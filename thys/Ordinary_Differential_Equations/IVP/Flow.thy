section \<open>Flow\<close>
theory Flow
imports
  Picard_Lindeloef_Qualitative
  "~~/src/HOL/Library/Diagonal_Subsequence"
  "../Library/Bounded_Linear_Operator"
  "../Library/Multivariate_Taylor"
begin

subsection \<open>simp rules for integrability (TODO: move)\<close>

named_theorems integrable_on_simps

lemma integrable_on_refl_ivl[intro, simp]: "g integrable_on {b .. (b::'b::ordered_euclidean_space)}"
  and integrable_on_refl_closed_segment[intro, simp]: "h integrable_on closed_segment a a"
  using integrable_on_refl[of g b]
  by (auto simp: cbox_sing)

lemma integrable_const_ivl_closed_segment[intro, simp]: "(\<lambda>x. c) integrable_on closed_segment a (b::real)"
  by (auto simp: closed_segment_real)

lemma integrable_ident_ivl[intro, simp]: "(\<lambda>x. x) integrable_on closed_segment a (b::real)"
  and integrable_ident_cbox[intro, simp]: "(\<lambda>x. x) integrable_on cbox a (b::real)"
  by (auto simp: closed_segment_real ident_integrable_on)

lemma content_closed_segment_real:
  fixes a b::real
  shows "content (closed_segment a b) = abs (b - a)"
  by (auto simp: closed_segment_real)

lemma integral_const_closed_segment:
  fixes a b::real
  shows "integral (closed_segment a b) (\<lambda>x. c) = abs (b - a) *\<^sub>R c"
  by (auto simp: closed_segment_real content_closed_segment_real)

lemmas [integrable_on_simps] =
  integrable_on_empty \<comment>\<open>empty\<close>
  integrable_on_refl integrable_on_refl_ivl integrable_on_refl_closed_segment \<comment>\<open>singleton\<close>
  integrable_const integrable_const_ivl integrable_const_ivl_closed_segment \<comment>\<open>constant\<close>
  ident_integrable_on integrable_ident_ivl integrable_ident_cbox \<comment>\<open>identity\<close>

lemmas [integrable_on_simps] =
  integrable_0
  integrable_neg
  integrable_cmul
  integrable_mult
  integrable_on_cmult_left
  integrable_on_cmult_right
  integrable_on_cdivide
  integrable_on_cmult_iff
  integrable_on_cmult_left_iff
  integrable_on_cmult_right_iff
  integrable_on_cdivide_iff
  integrable_diff
  integrable_add
  integrable_setsum


subsection \<open>Nonautonomous IVP on maximal existence interval\<close>

locale ll_on_open =
  fixes f::"real \<Rightarrow> 'a::{banach, heine_borel} \<Rightarrow> 'a" and T X
  assumes local_lipschitz: "local_lipschitz T X f"
  assumes cont: "\<And>x. x \<in> X \<Longrightarrow> continuous_on T (\<lambda>t. f t x)"
  assumes open_domain[intro!, simp]: "open T" "open X"
begin

lemma continuous_on_Times_f: "continuous_on (T \<times> X) (\<lambda>(t, x). f t x)"
  by (rule continuous_on_TimesI[OF local_lipschitz cont])

lemma continuous_on_f[continuous_intros]:
  assumes "continuous_on S g"
  assumes "continuous_on S h"
  assumes "h ` S \<subseteq> X"
  assumes "g ` S \<subseteq> T"
  shows "continuous_on S (\<lambda>x. f (g x) (h x))"
  using assms
  by (intro continuous_on_compose2[OF continuous_on_Times_f , of S "\<lambda>x. (g x, h x)", simplified])
    (auto intro!: continuous_intros)

lemma
  lipschitz_on_compact:
  assumes "compact K" "K \<subseteq> T"
  assumes "compact Y" "Y \<subseteq> X"
  obtains L where "\<And>t. t \<in> K \<Longrightarrow> lipschitz Y (f t) L"
proof -
  have cont: "\<And>x. x \<in> Y \<Longrightarrow> continuous_on K (\<lambda>t. f t x)"
    using \<open>Y \<subseteq> X\<close> \<open>K \<subseteq> T\<close>
    by (auto intro!: continuous_on_f continuous_intros)
  from local_lipschitz
  have "local_lipschitz K Y f"
    by (rule local_lipschitz_on_subset[OF _ \<open>K \<subseteq> T\<close> \<open>Y \<subseteq> X\<close>])
  from local_lipschitz_on_compact_implies_lipschitz[OF this \<open>compact Y\<close> \<open>compact K\<close> cont] that
  show ?thesis by metis
qed

lemma ll_on_open_rev[intro, simp]: "ll_on_open (\<lambda>t. - f (2 * t0 - t)) ((\<lambda>t. 2 * t0 - t) ` T) X"
  using local_lipschitz
  by unfold_locales
    (auto intro!: continuous_intros cont intro: local_lipschitz_compose1
      simp: fun_Compl_def local_lipschitz_uminus local_lipschitz_on_subset open_neg_translation image_image)

context fixes t0::real and x0::'a \<comment>"initial value"
begin

definition "outer_ivp = \<lparr>
  ivp_f = (\<lambda>(t, x). f t x),
  ivp_t0 = t0,
  ivp_x0 = x0,
  ivp_T = T,
  ivp_X = X \<rparr>"

definition "maximal_existence_bounds =
  (SOME (a::ereal, b::ereal).
    if unique_on_open outer_ivp then
    unique_on_open.maximal_existence_interval outer_ivp (real_of_ereal ` {a <..< b}) else b < a)"

definition "inf_existence = fst maximal_existence_bounds"

definition "sup_existence = snd maximal_existence_bounds"

definition "existence_ivl = real_of_ereal ` {inf_existence <..< sup_existence}"

definition "existence_ivp = \<lparr>
  ivp_f = (\<lambda>(t, x). f t x),
  ivp_t0 = t0,
  ivp_x0 = x0,
  ivp_T = existence_ivl,
  ivp_X = X \<rparr>"

lemma existence_ivp_simps[simp]:
  "ivp_f existence_ivp = (\<lambda>(t, x). f t x)"
  "ivp_t0 existence_ivp = t0"
  "ivp_x0 existence_ivp = x0"
  "ivp_T existence_ivp = existence_ivl"
  "ivp_X existence_ivp = X"
  by (simp_all add: existence_ivp_def)

lemma open_existence_ivl[simp]: "open existence_ivl"
  by (simp add: existence_ivl_def open_real_image)

lemma is_interval_existence_ivl[simp]: "is_interval existence_ivl"
  by (auto simp: existence_ivl_def is_interval_real_ereal_oo)

definition "flow t = ivp.solution existence_ivp t"

context assumes iv_in: "t0 \<in> T" "x0 \<in> X" begin

interpretation outer_ivp: ivp outer_ivp
  by standard (auto simp: outer_ivp_def iv_in)

interpretation outer_ivp: ivp_open outer_ivp
  by standard (auto simp: outer_ivp_def)

interpretation outer_ivp: continuous_rhs "ivp_T outer_ivp" "ivp_X outer_ivp" "ivp_f outer_ivp"
  by standard
    (auto simp: outer_ivp_def split_beta intro!: continuous_intros)

interpretation outer_ivp: unique_on_open outer_ivp
  using local_lipschitz
  by unfold_locales (simp add: outer_ivp_def)

lemma maximal_existence_bounds_def':
  "maximal_existence_bounds =
    (SOME (a::ereal, b::ereal). outer_ivp.maximal_existence_interval (real_of_ereal ` {a <..< b}))"
proof -
  have "unique_on_open outer_ivp" ..
  thus ?thesis
    by (simp add: maximal_existence_bounds_def)
qed

lemma maximal_existence_bounds:
  "outer_ivp.maximal_existence_interval
    (real_of_ereal ` {fst (maximal_existence_bounds)<..<snd (maximal_existence_bounds)})"
proof -
  obtain a b::ereal where "outer_ivp.maximal_existence_interval (real_of_ereal ` {a <..< b})"
    by (metis outer_ivp.maximal_existence_intervalE)
  hence "\<exists>x. case x of (a::ereal, b::ereal) \<Rightarrow>
      outer_ivp.maximal_existence_interval (real_of_ereal ` {a <..< b})"
    by (auto intro!: exI[where x="(a, b)"])
  from someI_ex[OF this]
  show ?thesis
    by (auto simp: maximal_existence_bounds_def')
qed

lemma maximal_existence_interval:
  "outer_ivp.maximal_existence_interval existence_ivl"
  by (simp add: inf_existence_def sup_existence_def maximal_existence_bounds existence_ivl_def)

lemma existence_ivl_subset:
  "existence_ivl \<subseteq> T"
  using maximal_existence_interval
  unfolding outer_ivp.maximal_existence_interval_def
  by (auto simp: outer_ivp_def)

lemma mem_existence_ivl_subset:
  "\<And>x. x \<in> existence_ivl \<Longrightarrow> x \<in> T"
  using existence_ivl_subset by auto

interpretation existence_ivp: ivp "existence_ivp"
  using maximal_existence_interval[unfolded outer_ivp.maximal_existence_interval_def]
  by unfold_locales (auto simp: iv_in outer_ivp_def)

lemma existence_ivl_initial_time[intro, simp]: "t0 \<in> existence_ivl"
  using existence_ivp.iv_defined
  by (auto simp: existence_ivp_def existence_ivl_def)

lemma existence_ivp: "unique_solution (existence_ivp)"
  using maximal_existence_interval[unfolded outer_ivp.maximal_existence_interval_def]
  by (simp add: outer_ivp_def existence_ivp_def)

interpretation existence_ivp: unique_solution "existence_ivp"
  by (rule existence_ivp)

interpretation existence_ivp: unique_on_open "existence_ivp"
proof unfold_locales
  have "(existence_ivl \<times> X) \<subseteq> ivp_T (outer_ivp) \<times> ivp_X (outer_ivp)"
    by (auto simp: outer_ivp_def mem_existence_ivl_subset)
  from continuous_on_subset[OF outer_ivp.continuous this]
  show "continuous_on (ivp_T (existence_ivp) \<times> ivp_X (existence_ivp)) (ivp_f (existence_ivp))"
    by (simp add: outer_ivp_def)
qed (insert outer_ivp.local_lipschitz outer_ivp.openX,
  auto simp add: outer_ivp_def local_lipschitz_on_subset existence_ivl_subset)

lemma double_nonneg_le:
  fixes a::real
  shows "a * 2 \<le> b \<Longrightarrow> a \<ge> 0 \<Longrightarrow> a \<le> b"
  by arith

lemma
  local_unique_solutions:
  obtains t u L
  where
    "\<And>x. x \<in> cball x0 u \<Longrightarrow>
      unique_solution
        (existence_ivp \<lparr>ivp_x0 := x, ivp_T := cball t0 t, ivp_X := cball x u\<rparr>)"
    "\<And>x. x \<in> cball x0 u \<Longrightarrow> cball x u \<subseteq> X"
    "\<And>t'. t' \<in> cball t0 t \<Longrightarrow> lipschitz (cball x0 (2 * u)) (f t') L"
    "cball t0 t \<subseteq> T"
    "cball x0 (2 * u) \<subseteq> X"
    "0 < t" "0 < u"
proof -
  from existence_ivp.eventually_unique_solution
  obtain B L t where t: "0 < t"
  and ev:
    "eventually
      (\<lambda>e. 0 < e \<and>
        cball (existence_ivp.t0) (t * e) \<subseteq> existence_ivp.T \<and>
        cball (existence_ivp.x0) e \<subseteq> existence_ivp.X \<and>
        unique_on_cylinder (existence_ivp \<lparr>ivp_T := cball existence_ivp.t0 (t * e),
        ivp_X := cball existence_ivp.x0 e\<rparr>) (t * e) e B L (cball existence_ivp.x0 e))
      (at_right 0)" .
  from eventually_happens[OF ev] obtain e where e:
    "e > 0"
    "cball (existence_ivp.t0) (t * e) \<subseteq> existence_ivp.T"
    "cball (existence_ivp.x0) e \<subseteq> existence_ivp.X"
    "unique_on_cylinder (existence_ivp \<lparr>ivp_T := cball existence_ivp.t0 (t * e),
        ivp_X := cball existence_ivp.x0 e\<rparr>) (t * e) e B L (cball existence_ivp.x0 e)"
    by auto
  then interpret cyl:
    unique_on_cylinder "existence_ivp \<lparr>ivp_T := cball existence_ivp.t0 (t * e),
      ivp_X := cball existence_ivp.x0 e\<rparr>" "t * e" e B L "cball existence_ivp.x0 e"
    by-assumption
  define e' where "e' = e / 2"
  have lips: "\<And>t'. t' \<in> cball t0 (t * e') \<Longrightarrow> lipschitz (cball x0 (2 * e')) (f t') L" "cball x0 (2 * e') \<subseteq> X"
    using cyl.global_lipschitz.lipschitz(1) e t
    by (auto simp add: e'_def dist_real_def dest!: double_nonneg_le)
  from e t have e'_pos: "e' > 0" by (simp add: e'_def)
  with t have te_pos: "t * e' > 0" by simp
  from e existence_ivl_subset have "cball t0 (t * e') \<subseteq> T"
    by (force simp: e'_def dest!: double_nonneg_le)
  moreover
  {
    fix x0'::'a
    assume x0': "x0' \<in> cball x0 e'"
    let ?i' = "existence_ivp \<lparr>ivp_x0 := x0', ivp_T := cball t0 (t * e'),
      ivp_X := cball x0' e'\<rparr>"
    have triangle: "dist x0 b \<le> e" if d: "dist x0' b \<le> e'" for b
    proof -
      have "dist x0 b \<le> dist x0 x0' + dist x0' b"
        by (rule dist_triangle)
      also have "\<dots> \<le> e' + e'"
        using x0' d by simp
      also have "\<dots> \<le> e" by (simp add: e'_def)
      finally show ?thesis .
    qed
    have subs1: "cball t0 (t * e') \<subseteq> cball t0 (t * e)"
      and subs2: "cball x0' e' \<subseteq> cball x0 e"
      and subs: "cball t0 (t * e') \<times> cball x0' e' \<subseteq> cball t0 (t * e) \<times> cball x0 e"
      using e'_pos x0'
      by (auto simp: e'_def triangle dest!: double_nonneg_le)

    interpret cyl': cylinder ?i' "t * e'" e'
      using e'_pos t
      by unfold_locales (auto simp: dist_real_def)
    interpret cyl': solution_in_cylinder ?i' "t * e'"  e' B
      using cyl.norm_f cyl.e_bounded cyl.continuous subs
      by unfold_locales (force simp: e'_def intro: continuous_on_subset)+
    interpret cyl': unique_on_cylinder ?i' "t * e'" e' B L "(cball x0 e)"
      using cyl.global_lipschitz.lipschitz(1)[simplified] t
        cyl.global_lipschitz.lipschitz e'_pos x0' subs subs1
      by unfold_locales (auto simp: triangle)
    have un: "unique_solution ?i'"
      by unfold_locales
    from subs2 e have subs: "cball x0' e' \<subseteq> X" by simp
    note un this
  } ultimately show thesis using lips te_pos e'_pos
    by (metis that)
qed

lemma in_existence_between_zeroI:
  "t \<in> existence_ivl \<Longrightarrow> s \<in> {t .. t0} \<union> {t0 .. t} \<Longrightarrow> s \<in> existence_ivl"
  using existence_ivl_initial_time[simplified existence_ivl_def]
  by (cases "inf_existence"; cases "sup_existence")
    (auto simp: existence_ivl_def real_atLeastGreaterThan_eq)

lemma ivl2_subset_existence_ivl:
  assumes "s \<in> existence_ivl" "t \<in> existence_ivl"
  shows "{s .. t} \<subseteq> existence_ivl"
  apply (rule subsetI)
  subgoal for x
    using in_existence_between_zeroI[OF assms(1), of x] in_existence_between_zeroI[OF assms(2), of x]
    by (force )
  done

lemma flow_in_domain: "t \<in> existence_ivl \<Longrightarrow> flow t \<in> X"
  using existence_ivp.solution_in_D flow_def by auto

lemma maximal_existence_flow:
  assumes "ivp.is_solution i x"
  assumes "i = \<lparr> ivp_f = (\<lambda>(t, x). f t x), ivp_t0 = t0, ivp_x0 = x0, ivp_T = K, ivp_X = X \<rparr>"
  assumes "is_interval K"
  assumes "t0 \<in> K"
  assumes "K \<subseteq> T"
  shows "K \<subseteq> existence_ivl" "\<And>t. t \<in> K \<Longrightarrow> flow t = x t"
proof -
  from assms have sol: "ivp.is_solution \<lparr>ivp_f = \<lambda>(t, x). f t x, ivp_t0 = t0, ivp_x0 = x0, ivp_T = K, ivp_X = X\<rparr> x"
    by auto
  from maximal_existence_interval[unfolded outer_ivp.maximal_existence_interval_def]
  have m: "\<And>K x. K \<subseteq> T \<Longrightarrow>
         is_interval K \<Longrightarrow>
         t0 \<in> K \<Longrightarrow>
         ivp.is_solution \<lparr> ivp_f = (\<lambda>(t, x). f t x), ivp_t0 = t0, ivp_x0 = x0, ivp_T = K, ivp_X = X \<rparr> x \<Longrightarrow>
         K \<subseteq> existence_ivl \<and>
          (\<forall>t\<in>K. x t = ivp.solution \<lparr> ivp_f = (\<lambda>(t, x). f t x), ivp_t0 = t0, ivp_x0 = x0, ivp_T = existence_ivl, ivp_X = X \<rparr> t)"
    by (auto simp: outer_ivp_def)
  have "K \<subseteq> T" using assms existence_ivl_subset by auto
  from m[OF this \<open>is_interval K\<close> \<open>t0 \<in> K\<close> sol]
  show "K \<subseteq> existence_ivl" "\<And>t. t \<in> K \<Longrightarrow> flow t = x t" 
    by (auto simp add: outer_ivp_def flow_def existence_ivp_def)
qed

lemma maximal_existence_flowI:
  assumes "\<And>t. t \<in> K \<Longrightarrow> (x has_vector_derivative f t (x t)) (at t within K)"
  assumes "\<And>t. t \<in> K \<Longrightarrow> x t \<in> X"
  assumes "x t0 = x0"
  assumes K: "is_interval K" "t0 \<in> K" "K \<subseteq> T"
  shows "K \<subseteq> existence_ivl" "\<And>t. t \<in> K \<Longrightarrow> flow t = x t"
proof -
  have sol: "ivp.is_solution \<lparr>ivp_f = \<lambda>(t, x). f t x, ivp_t0 = t0, ivp_x0 = x0, ivp_T = K, ivp_X = X\<rparr> x"
    apply (rule ivp.is_solutionI)
    apply unfold_locales
    using assms iv_in
    by auto
  from maximal_existence_flow[OF sol refl K]
    show "K \<subseteq> existence_ivl" "\<And>t. t \<in> K \<Longrightarrow> flow t = x t"
    by auto
qed

lemma Picard_iterate_mem_existence_ivlI:
  assumes "t0 \<le> t" "{t0 .. t} \<subseteq> T"
  assumes "compact C" "x0 \<in> C" "C \<subseteq> X"
  assumes "\<And>y s. t0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> y t0 = x0 \<Longrightarrow> y \<in> {t0..s} \<rightarrow> C \<Longrightarrow> continuous_on {t0..s} y \<Longrightarrow>
      x0 + integral {t0..s} (\<lambda>t. f t (y t)) \<in> C"
  shows "t \<in> existence_ivl" "\<And>s. t0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> flow s \<in> C"
proof -
  let ?i = "\<lparr>ivp_f = \<lambda>(t, x). f t x, ivp_t0 = t0, ivp_x0 = x0, ivp_T = {t0 .. t}, ivp_X = C\<rparr>"
  interpret uc: ivp ?i
    using assms iv_in
    by unfold_locales auto
  from lipschitz_on_compact[OF compact_Icc \<open>{t0 .. t} \<subseteq> T\<close> \<open>compact C\<close> \<open>C \<subseteq> X\<close>]
  obtain L where L: "\<And>s. s \<in> {t0 .. t} \<Longrightarrow> lipschitz C (f s) L" by metis
  interpret uc: unique_on_closed ?i t L
    using assms
    by unfold_locales
      (auto intro!: L compact_imp_closed \<open>compact C\<close> continuous_on_f continuous_intros
        simp: split_beta)
  have "{t0 .. t} \<subseteq> existence_ivl"
    using assms
    apply (intro maximal_existence_flow(1)[OF uc.is_solution_on_superset_domain[OF uc.is_solution_solution]])
    apply (auto simp: is_interval_closed_interval)
    done
  thus "t \<in> existence_ivl"
    using assms by auto
  show "flow s \<in> C" if "t0 \<le> s" "s \<le> t" for s
  proof -
    have "flow s = uc.solution s" "uc.solution s \<in> C"
      using uc.is_solutionD[OF uc.is_solution_solution] that assms
      by (auto simp: is_interval_closed_interval intro!: maximal_existence_flowI(2)[where K="{t0 .. t}"])
    thus ?thesis by simp
  qed
qed

lemma unique_on_intersection:
  assumes "t \<in> ivp_T i \<inter> ivp_T j"
  assumes "has_solution i"
  assumes "has_solution j"
  assumes "ivp_X i = ivp_X (existence_ivp)"
  assumes "ivp_X j = ivp_X (existence_ivp)"
  assumes "ivp_f i = ivp_f (existence_ivp)"
  assumes "ivp_f j = ivp_f (existence_ivp)"
  assumes "ivp_T i \<subseteq> T"
  assumes "ivp_T j \<subseteq> T"
  assumes "is_interval (ivp_T i)"
  assumes "is_interval (ivp_T j)"
  assumes "ti \<in> ivp_T i \<inter> ivp_T j"
  assumes "ivp.solution i ti = x0"
  assumes "ivp.solution j ti = x0"
  shows "ivp.solution i t = ivp.solution j t"
proof -
  interpret i: has_solution i by fact
  let ?i = "i\<lparr>ivp_t0 := ti, ivp_x0 := x0\<rparr>"
  interpret i': ivp ?i
    apply standard
    using \<open>ti \<in> _\<close> \<open>x0 \<in> _\<close>
    by (auto simp: \<open>i.X = _\<close>)
  have i'_sol: "i'.is_solution i.solution"
    apply (rule i.shift_initial_value)
    using assms
    apply auto
    done
  interpret j: has_solution j by fact
  let ?j = "j\<lparr>ivp_t0 := ti, ivp_x0 := x0\<rparr>"
  interpret j': ivp ?j
    apply standard
    using \<open>ti \<in> _\<close> \<open>x0 \<in> _\<close>
    by (auto simp: \<open>j.X = _\<close>)
  have j'_sol: "j'.is_solution j.solution"
    apply (rule j.shift_initial_value)
    using assms
    apply auto
    done

  have "ll_on_open.flow f T X ti x0 t = ivp.solution i t"
    using assms
    apply (intro ll_on_open.maximal_existence_flow[where i="i\<lparr>ivp_t0 := ti, ivp_x0 := x0\<rparr>" and K=i.T])
    subgoal by unfold_locales
    subgoal using assms by force
    subgoal by (rule \<open>x0 \<in> X\<close>)
    subgoal by (rule i'_sol)
    subgoal by (rule ivp.equality; simp add: assms)
    subgoal by (rule \<open>is_interval i.T\<close>)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    done

  moreover have "ll_on_open.flow f T X ti x0 t = ivp.solution j t"
    using assms
    apply (intro ll_on_open.maximal_existence_flow[where i="j\<lparr>ivp_t0 := ti, ivp_x0 := x0\<rparr>" and K=j.T])
    subgoal by unfold_locales
    subgoal using assms by force
    subgoal by (rule \<open>x0 \<in> X\<close>)
    subgoal by (rule j'_sol)
    subgoal by (rule ivp.equality; simp add: assms)
    subgoal by (rule \<open>is_interval j.T\<close>)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    done

  ultimately show ?thesis by simp
qed

lemma flow_initial_time[simp]: "flow t0 = x0"
  using existence_ivp.solution_t0 flow_def by auto

lemma flow_has_derivative:
  assumes "t \<in> existence_ivl"
  shows "(flow has_derivative (\<lambda>i. i *\<^sub>R f t (flow t))) (at t)"
proof -
  have "(flow has_derivative (\<lambda>i. i *\<^sub>R f t (flow t))) (at t within existence_ivl)"
    using existence_ivp.solution_has_deriv[of t] assms
    unfolding flow_def[abs_def]
    by (auto simp: has_vector_derivative_def)
  thus ?thesis
    by (simp add: at_within_open[OF assms open_existence_ivl])
qed

lemma
  flow_eq_rev:
  defines "mirror \<equiv> \<lambda>t. 2 * t0 - t"
  assumes "t \<in> existence_ivl"
  shows "flow t = ll_on_open.flow (\<lambda>t. - f (mirror t)) (mirror ` T) X t0 x0 (2 * t0 - t)"
  "2 * t0 - t \<in> ll_on_open.existence_ivl (\<lambda>t. - f (mirror t)) (mirror ` T) X t0 x0"
proof -
  from iv_in have mt0: "t0 \<in> mirror ` T"
    by (auto simp: mirror_def)
  have subset: "mirror ` existence_ivl \<subseteq> mirror ` T"
    using existence_ivl_subset
    by (rule image_mono)
  have [simp]: "is_interval (mirror ` X) \<longleftrightarrow> is_interval X" for X
    by (auto simp: mirror_def)
  interpret rev: ll_on_open "\<lambda>t. - f (mirror t)" "mirror ` T"
    unfolding mirror_def ..
  have "ivp.solution (existence_ivp) \<circ> mirror = (\<lambda>t. flow (mirror t))"
    by (auto simp: flow_def)
  with existence_ivp.mirror_solution[OF existence_ivp.is_solution_solution, simplified]
  have *:
    "ivp.is_solution
      (existence_ivp \<lparr>ivp_f := \<lambda>(t, x). - f (mirror t) x, ivp_T := mirror ` existence_ivl\<rparr>)
      (\<lambda>t. flow (mirror t))"
    by (auto simp: mirror_def)
  have it: "t0 \<in> mirror ` existence_ivl"
    using existence_ivl_initial_time by (simp add: mirror_def)
  from rev.maximal_existence_flow[where K="mirror ` existence_ivl", OF mt0 iv_in(2) * _ _ it]
  have "mirror ` existence_ivl \<subseteq> ll_on_open.existence_ivl (\<lambda>t. - f (mirror t)) (mirror ` T) X t0 x0"
    "\<And>t. t \<in> mirror ` existence_ivl \<Longrightarrow> rev.flow t0 x0 t = flow (mirror t)"
    by (auto simp: existence_ivp_def subset)
  then show "2 * t0 - t \<in> rev.existence_ivl t0 x0" "flow t = rev.flow t0 x0 (2 * t0 - t)"
    using assms by auto
qed

lemma rev_flow_eq:
  defines "mirror \<equiv> \<lambda>t. 2 * t0 - t"
  shows "t \<in> ll_on_open.existence_ivl (\<lambda>t. - f (mirror t)) (mirror ` T) X t0 x0 \<Longrightarrow>
    ll_on_open.flow (\<lambda>t. - f (mirror t)) (mirror ` T) X t0 x0 t = flow (2 * t0 - t)"
  and rev_existence_ivl_eq:
  "t \<in> ll_on_open.existence_ivl (\<lambda>t. - f (mirror t)) (mirror ` T)  X t0 x0 \<longleftrightarrow> 2 * t0 - t \<in> existence_ivl"
proof -
  from iv_in have mt0: "t0 \<in> mirror ` T" by (auto simp: mirror_def)
  interpret rev: ll_on_open "(\<lambda>t. - f (mirror t))" "(mirror ` T)"
    unfolding mirror_def ..
  from rev.flow_eq_rev[OF mt0 iv_in(2), of t] flow_eq_rev[of "2 * t0 -t"]
  show "t \<in> rev.existence_ivl t0 x0 \<Longrightarrow> rev.flow t0 x0 t = flow (2 * t0 - t)"
    "(t \<in> rev.existence_ivl t0 x0) = (2 * t0 - t \<in> existence_ivl)"
    by (auto simp: mirror_def \<open>x0 \<in> X\<close> fun_Compl_def image_image)
qed

end \<comment>\<open>@{thm iv_in}\<close>

end \<comment>\<open>@{term x0}\<close>

lemma
  assumes s: "s \<in> existence_ivl t0 x0"
  assumes t: "t + s \<in> existence_ivl s (flow t0 x0 s)"
  assumes iv_in[simp]: "t0 \<in> T" "x0 \<in> X"
  shows flow_trans: "flow t0 x0 (s + t) = flow s (flow t0 x0 s) (s + t)"
    and existence_ivl_trans: "s + t \<in> existence_ivl t0 x0"
proof -
  have "s \<in> T"
    using existence_ivl_subset iv_in(1) iv_in(2) s by blast
  from existence_ivp[OF iv_in]
  interpret u0: unique_solution "existence_ivp t0 x0" .
  let ?u0r = "(existence_ivp t0 x0)\<lparr>ivp_T:=if s \<ge> t0 then {t0 .. s} else {s .. t0}\<rparr>"
  interpret u0r: ivp ?u0r
    by unfold_locales auto
  have "has_solution ?u0r"
    apply unfold_locales
    apply (rule exI)
    apply (rule u0.solution_on_subset[OF _ _ u0.is_solution_solution])
    by (auto intro!: in_existence_between_zeroI[OF iv_in s])
  then interpret u0r: has_solution ?u0r .

  have "u0r.T \<subseteq> existence_ivl t0 x0"
    by (auto intro!: in_existence_between_zeroI[OF iv_in s])
  then have "u0r.T \<subseteq> T"
    using existence_ivl_subset[OF iv_in]
    by auto

  note flow_in_domain[OF iv_in s, simp]
  from existence_ivp[OF \<open>s \<in> T\<close> this]
  interpret u1: unique_solution "existence_ivp s (flow t0 x0 s)" by simp
  let ?u1 = "(existence_ivp s (flow t0 x0 s))\<lparr>ivp_T:=if t \<ge> 0 then {s..t + s} else {t + s..s}\<rparr>"
  interpret u1r: ivp ?u1
    by unfold_locales auto
  interpret u1r: has_solution ?u1
    apply unfold_locales
    apply (rule exI)
    apply (rule u1.solution_on_subset[OF _ _ u1.is_solution_solution])
    by (auto intro!: in_existence_between_zeroI[OF \<open>s \<in> T\<close> \<open>(flow t0 x0 s) \<in> X\<close> t])

  have "u1r.T \<subseteq> existence_ivl s (flow t0 x0 s)"
    by (auto intro!: in_existence_between_zeroI[OF \<open>s \<in> T\<close> \<open>(flow t0 x0 s) \<in> X\<close> t])
  then have "u1r.T \<subseteq> T"
    using existence_ivl_subset[OF \<open>s \<in> T\<close> \<open>(flow t0 x0 s) \<in> X\<close>]
    by auto

  let ?c = "(existence_ivp t0 x0)\<lparr>ivp_T:=ivp_T ?u0r \<union> ivp_T ?u1\<rparr>"
  interpret conn: ivp ?c
    by unfold_locales (auto simp: iv_in)
  interpret conn: connected_solutions ?c ?u0r ?u1 u0r.solution
  proof unfold_locales
    show "u0r.is_solution u0r.solution" by simp
  next
    assume "conn.t0 \<notin> u0r.T"
    thus "u1r.solution conn.t0 = conn.x0"
      by (simp split: if_split_asm)
  next
    assume "conn.t0 \<in> u0r.T"
    thus "u0r.solution conn.t0 = conn.x0"
      using u0r.solution_t0
      by (simp split: )
  next
    fix t assume t: "t \<in> u0r.T \<inter> u1r.T"
    from \<open>u0r.T \<subseteq> T\<close> have fr: "flow t0 x0 s = u0r.solution s"
     by (intro maximal_existence_flow[where i="?u0r" and K="ivp_T ?u0r"])
       (auto simp: is_interval_closed_interval)
    hence fs: "flow t0 x0 s = u1r.solution s"
      using u1r.solution_t0
      by simp
    from t \<open>has_solution ?u0r\<close> \<open>has_solution ?u1\<close>
    show "u0r.solution t = u1r.solution t"
      apply (rule unique_on_intersection[OF \<open>s \<in> T\<close> \<open>flow t0 x0 s \<in> X\<close>])
      using fr[symmetric] fs[symmetric] \<open>u0r.T \<subseteq> T\<close> \<open>u1r.T \<subseteq> T\<close>
      by (auto simp: is_interval_closed_interval s)
  qed auto
  have "flow t0 x0 (s + t) = (conn.connection (s + t))"
    by (rule maximal_existence_flow[OF iv_in conn.is_solution_connection, where K="ivp_T ?c"])
      (insert \<open>u0r.T \<subseteq> T\<close> \<open>u1r.T \<subseteq> T\<close>, auto simp: is_interval_closed_interval is_real_interval_union)
  also have "conn.connection (s + t) = u1r.solution (s + t)"
    by (rule conn.connection_eq_solution2) simp
  also
  from u1r.is_solution_solution
  have "u1r.is_solution u1r.solution" by simp
  then have "flow s (flow t0 x0 s) (s + t) = u1r.solution (s + t)"
    by (rule maximal_existence_flow(2)[OF \<open>s \<in> T\<close> \<open>(flow t0 x0 s) \<in> X\<close>, where K="ivp_T ?u1"])
      (insert \<open>u1r.T \<subseteq> T\<close>, auto simp: is_interval_closed_interval is_real_interval_union)
  then have "u1r.solution (s + t) = flow s (flow t0 x0 s) (s + t)"
    by (simp add: algebra_simps)
  finally show "flow t0 x0 (s + t) = flow s (flow t0 x0 s) (s + t)" .
  have "s + t \<in> conn.T"
    by simp
  also have "\<dots> \<subseteq> existence_ivl t0 x0" using conn.is_solution_connection
    by (rule maximal_existence_flow[OF iv_in])
      (insert \<open>u0r.T \<subseteq> T\<close> \<open>u1r.T \<subseteq> T\<close>, auto simp: is_interval_closed_interval is_real_interval_union)
  finally show "s + t \<in> existence_ivl t0 x0" .
qed

lemma
  assumes t: "t \<in> existence_ivl t0 x0"
  assumes iv_in[simp]: "t0 \<in> T" "x0 \<in> X"
  shows flows_reverse: "flow t (flow t0 x0 t) t0 = x0"
    and existence_ivl_reverse: "t0 \<in> existence_ivl t (flow t0 x0 t)"
proof -
  have "flow t0 x0 t \<in> X"
    by (rule flow_in_domain; fact)
  interpret existence_ivp: unique_solution "existence_ivp t0 x0"
    by (rule existence_ivp; fact)
  have "t0 \<in> {t .. t0} \<union> {t0 .. t}" by force
  also
  have "\<dots> \<subseteq> existence_ivl t (flow t0 x0 t)"
    apply (rule maximal_existence_flow[OF _ _ _ refl, where x="existence_ivp.solution"])
    subgoal using t existence_ivl_subset[OF iv_in] by force
    subgoal by fact
    subgoal
      using in_existence_between_zeroI[OF iv_in t]
      by (auto simp: flow_def
        intro!: existence_ivp.shift_initial_value[OF existence_ivp.is_solution_solution])
    subgoal by (auto intro!: is_real_interval_union is_interval_closed_interval)
    subgoal by auto
    subgoal using in_existence_between_zeroI[OF iv_in t] existence_ivl_subset[OF iv_in] by auto
    done
  finally show "t0 \<in> existence_ivl t (flow t0 x0 t)" .
  with flow_trans[OF t _ _  \<open>x0 \<in> X\<close>, of "t0 - t", simplified]
  show "flow t (flow t0 x0 t) t0 = x0" by simp
qed

lemma flow_has_vector_derivative:
  assumes "t0 \<in> T" "x \<in> X" "t \<in> existence_ivl t0 x"
  shows "(flow t0 x has_vector_derivative f t (flow t0 x t)) (at t)"
  using flow_has_derivative[OF assms]
  by (simp add: has_vector_derivative_def)

lemma flow_has_vector_derivative_at_0:
  assumes "t0 \<in> T" "x \<in> X" "t \<in> existence_ivl t0 x"
  shows "((\<lambda>h. flow t0 x (t + h)) has_vector_derivative f t (flow t0 x t)) (at 0)"
proof -
  from flow_has_vector_derivative[OF assms]
  have
    "(op + t has_vector_derivative 1) (at 0)"
    "(flow t0 x has_vector_derivative f t (flow t0 x t)) (at (t + 0))"
    by (auto intro!: derivative_eq_intros)
  from vector_diff_chain_at[OF this]
  show ?thesis by (simp add: o_def)
qed

lemma
  assumes in_domain: "t0 \<in> T" "x \<in> X"
  assumes "t \<in> existence_ivl t0 x"
  shows ivl_subset_existence_ivl: "{t0 .. t} \<subseteq> existence_ivl t0 x"
    and ivl_subset_existence_ivl': "{t .. t0} \<subseteq> existence_ivl t0 x"
    and closed_segment_subset_existence_ivl: "closed_segment t0 t \<subseteq> existence_ivl t0 x"
  using assms in_existence_between_zeroI[OF in_domain]
  by (auto simp: closed_segment_real)

lemma flow_fixed_point:
  assumes t: "t0 \<le> t" "t \<in> existence_ivl t0 x"
  assumes iv_in: "t0 \<in> T" "x \<in> X"
  shows "flow t0 x t = x + integral {t0..t} (\<lambda>t. f t (flow t0 x t))"
proof -
  have "\<forall>s\<in>{t0 .. t}. (flow t0 x has_vector_derivative f s (flow t0 x s)) (at s within {t0 .. t})"
    using ivl_subset_existence_ivl[OF iv_in t(2)]
    by (auto intro!: flow_has_vector_derivative[OF iv_in]
      intro: has_vector_derivative_at_within)
  from fundamental_theorem_of_calculus[OF t(1) this]
  have "((\<lambda>t. f t (flow t0 x t)) has_integral flow t0 x t - x) {t0..t}"
    by (simp add: iv_in)
  from this[THEN integral_unique]
  show ?thesis by (simp add: \<open>x \<in> X\<close>)
qed

lemma flow_fixed_point':
  assumes t: "t \<le> t0" "t \<in> existence_ivl t0 x"
  assumes iv_in: "t0 \<in> T" "x \<in> X"
  shows "flow t0 x t = x - integral {t..t0} (\<lambda>t. f t (flow t0 x t))"
proof -
  have "\<forall>s\<in>{t .. t0}. (flow t0 x has_vector_derivative f s (flow t0 x s)) (at s within {t .. t0})"
    using ivl_subset_existence_ivl'[OF iv_in t(2)]
    by (auto intro!: flow_has_vector_derivative[OF iv_in]
      intro: has_vector_derivative_at_within)
  from fundamental_theorem_of_calculus[OF t(1) this]
  have "((\<lambda>t. f t (flow t0 x t)) has_integral x - flow t0 x t) {t .. t0}"
    by (simp add: iv_in)
  from this[THEN integral_unique]
  show ?thesis by (simp add: \<open>x \<in> X\<close> algebra_simps)
qed

lemma flow_fixed_point'':
  assumes t: "t \<in> existence_ivl t0 x"
  assumes "t0 \<in> T" "x \<in> X"
  shows "flow t0 x t =
    x + (if t0 \<le> t then 1 else -1) *\<^sub>R integral (closed_segment t0 t) (\<lambda>t. f t (flow t0 x t))"
  using assms
  by (auto simp add: closed_segment_real flow_fixed_point flow_fixed_point')

lemma flow_continuous: "t0 \<in> T \<Longrightarrow> x \<in> X \<Longrightarrow> t \<in> existence_ivl t0 x \<Longrightarrow> continuous (at t) (flow t0 x)"
  by (metis has_derivative_continuous flow_has_derivative)

lemma flow_tendsto: "t0 \<in> T \<Longrightarrow> x \<in> X \<Longrightarrow> t \<in> existence_ivl t0 x \<Longrightarrow> (ts \<longlongrightarrow> t) F \<Longrightarrow>
    ((\<lambda>s. flow t0 x (ts s)) \<longlongrightarrow> flow t0 x t) F"
  by (rule isCont_tendsto_compose[OF flow_continuous, of t0 x t ts F])

lemma flow_continuous_on: "t0 \<in> T \<Longrightarrow> x \<in> X \<Longrightarrow> continuous_on (existence_ivl t0 x) (flow t0 x)"
  by (auto intro!: flow_continuous continuous_at_imp_continuous_on)

lemma flow_continuous_on_intro:
  "t0 \<in> T \<Longrightarrow> x \<in> X \<Longrightarrow>
  continuous_on s g \<Longrightarrow>
  (\<And>xa. xa \<in> s \<Longrightarrow> g xa \<in> existence_ivl t0 x) \<Longrightarrow>
  continuous_on s (\<lambda>xa. flow t0 x (g xa))"
  by (auto intro!: continuous_on_compose2[OF flow_continuous_on])

lemma f_flow_continuous:
  assumes "t \<in> existence_ivl t0 x" "t0 \<in> T" "x \<in> X"
  shows "isCont (\<lambda>t. f t (flow t0 x t)) t"
  by (rule continuous_on_interior)
    (insert existence_ivl_subset assms,
      auto intro!: flow_in_domain flow_continuous_on continuous_intros
        simp: interior_open)

lemma exponential_initial_condition_nonneg:
  assumes "t \<ge> t0" "t0 \<in> T"
  assumes y0: "t \<in> existence_ivl t0 y0" and "y0 \<in> Y"
  assumes z0: "t \<in> existence_ivl t0 z0" and "z0 \<in> Y"
  assumes "Y \<subseteq> X"
  assumes remain: "\<And>s. s \<in> {t0 .. t} \<Longrightarrow> flow t0 y0 s \<in> Y"
    "\<And>s. s \<in> {t0 .. t} \<Longrightarrow> flow t0 z0 s \<in> Y"
  assumes lipschitz: "\<And>s. s \<in> {t0 .. t} \<Longrightarrow> lipschitz Y (f s) K"
  shows "norm (flow t0 y0 t - flow t0 z0 t) \<le> norm (y0 - z0) * exp ((K + 1) * (t - t0))"
proof cases
  assume "y0 = z0"
  thus ?thesis
    by simp
next
  assume ne: "y0 \<noteq> z0"
  define K' where "K' = K + 1"
  from lipschitz have "lipschitz Y (f s) K'" if "s \<in> {t0 .. t}" for s
    using that
    by (auto simp: lipschitz_def K'_def
      intro!: order_trans[OF _ mult_right_mono[of K "K + 1"]])
  from assms have inX: "y0 \<in> X" "z0 \<in> X" by auto
  define v where "v t = norm (flow t0 y0 t - flow t0 z0 t)" for t
  have le: "v s \<le> v t0 + K' *  integral {t0 .. s} (\<lambda>t. v t)" if s: "s \<in> {t0 .. t}" for s
  proof -
    from s have "s \<ge> t0" by auto
    with s
      ivl_subset_existence_ivl[OF \<open>t0 \<in> T\<close> \<open>y0 \<in> X\<close> y0]
      ivl_subset_existence_ivl[OF \<open>t0 \<in> T\<close>  \<open>z0 \<in> X\<close> z0]
    have
      y0': "s \<in> existence_ivl t0 y0" and
      z0': "s \<in> existence_ivl t0 z0"
      by auto
    have integrable:
      "(\<lambda>t. f t (ll_on_open.flow f T X t0 y0 t)) integrable_on {t0..s}"
      "(\<lambda>t. f t (ll_on_open.flow f T X t0 z0 t)) integrable_on {t0..s}"
      using ivl_subset_existence_ivl[OF \<open>t0 \<in> T\<close> \<open>y0 \<in> X\<close> y0']
        ivl_subset_existence_ivl[OF \<open>t0 \<in> T\<close> \<open>z0 \<in> X\<close> z0']
        \<open>y0 \<in> X\<close> \<open>z0 \<in> X\<close> \<open>t0 \<in> T\<close>
      by (auto intro!: continuous_at_imp_continuous_on f_flow_continuous)
    hence int: "flow t0 y0 s - flow t0 z0 s =
        y0 - z0 + integral {t0 .. s} (\<lambda>t. f t (flow t0 y0 t) - f t (flow t0 z0 t))"
      unfolding v_def
      by (auto simp: algebra_simps flow_fixed_point[OF \<open>s \<ge> t0\<close> y0' \<open>t0 \<in> T\<close> \<open>y0 \<in> X\<close>]
        flow_fixed_point[OF \<open>s \<ge> t0\<close> z0' \<open>t0 \<in> T\<close> \<open>z0 \<in> X\<close>] integral_diff)
    show ?thesis
      using ivl_subset_existence_ivl[OF \<open>t0 \<in> T\<close> \<open>y0 \<in> X\<close> y0']
        ivl_subset_existence_ivl[OF \<open>t0 \<in> T\<close> \<open>z0 \<in> X\<close> z0'] s
      by (subst integral_mult)
        (auto simp: integral_mult v_def [abs_def] int inX \<open>t0 \<in> T\<close> simp del: integral_mult_right
          intro!: norm_triangle_le integral_norm_bound_integral
            integrable_continuous_real continuous_intros
            continuous_at_imp_continuous_on flow_continuous f_flow_continuous
            lipschitz_norm_leI[OF \<open>_ \<Longrightarrow> lipschitz _ _ K'\<close>] remain)
  qed
  have cont: "continuous_on {t0..t} v"
    using ivl_subset_existence_ivl[OF \<open>t0 \<in> T\<close> \<open>y0 \<in> X\<close> y0]
      ivl_subset_existence_ivl[OF \<open>t0 \<in> T\<close> \<open>z0 \<in> X\<close> z0] inX
    by (auto simp: v_def \<open>t0 \<in> T\<close>
      intro!: continuous_at_imp_continuous_on continuous_intros flow_continuous)
  have nonneg: "\<And>t. v t \<ge> 0"
    by (auto simp: v_def)
  from ne have pos: "v t0 > 0"
    by (auto simp: v_def \<open>t0 \<in> T\<close> inX)
  have lippos: "K' > 0"
  proof -
    have "0 \<le> dist (f t0 y0) (f t0 z0)" by simp
    also from lipschitzD[OF lipschitz \<open>y0 \<in> Y\<close> \<open>z0 \<in> Y\<close>, of t0] \<open>t0 \<le> t\<close> ne
    have "\<dots> \<le> K * dist y0 z0"
      by simp
    finally have "0 \<le> K"
      by (metis dist_le_zero_iff ne zero_le_mult_iff)
    thus ?thesis by (simp add: K'_def)
  qed
  have "v t \<le> v t0 * exp (K' * (t - t0))"
    apply (rule gronwall_general[OF le cont nonneg pos lippos])
    using \<open>t0 \<le> t\<close> by simp_all
  thus ?thesis
    by (simp add: v_def K'_def \<open>t0 \<in> T\<close> inX)
qed

lemma exponential_initial_condition:
  assumes "t0 \<in> T"
  assumes y0: "t \<in> existence_ivl t0 y0" and "y0 \<in> Y"
  assumes z0: "t \<in> existence_ivl t0 z0" and "z0 \<in> Y"
  assumes "Y \<subseteq> X"
  assumes remain: "\<And>s. s \<in> closed_segment t0 t \<Longrightarrow> flow t0 y0 s \<in> Y"
    "\<And>s. s \<in> closed_segment t0 t \<Longrightarrow> flow t0 z0 s \<in> Y"
  assumes lipschitz: "\<And>s. s \<in> closed_segment t0 t \<Longrightarrow> lipschitz Y (f s) K"
  shows "norm (flow t0 y0 t - flow t0 z0 t) \<le> norm (y0 - z0) * exp ((K + 1) * abs (t - t0))"
  using assms
proof cases
  assume "t0 \<le> t"
  with assms remain lipschitz
  have "norm (flow t0 y0 t - flow t0 z0 t) \<le> norm (y0 - z0) * exp ((K + 1) * (t - t0))"
    by (intro exponential_initial_condition_nonneg)
      (auto simp: closed_segment_real)
  thus ?thesis
    using \<open>t0 \<le> t\<close> by simp
next
  have "y0 \<in> X" "z0 \<in> X" using assms by auto
  let ?m = "\<lambda>t. 2 * t0 - t"
  have remain_rev: "ll_on_open.flow (\<lambda>t. - f (2 * t0 - t)) (?m ` T) X t0 y0 s \<in> Y"
    if "y0 \<in> X"
    and remain: "\<And>s. s \<in> closed_segment t0 t \<Longrightarrow> flow t0 y0 s \<in> Y"
    and y0: "t \<in> existence_ivl t0 y0"
    and s: "s \<in> {t0 .. 2 * t0 - t}"
    for s y0 Y
  proof -
    have "ll_on_open.flow (\<lambda>t. - f (2 * t0 - t)) (?m ` T) X t0 y0 s =
      ll_on_open.flow (\<lambda>t. - f (2 * t0 - t)) (?m ` T) X t0 y0 (2 * t0 - (2 * t0 - s))"
      by simp
    also have "\<dots> = flow t0 y0 (2 * t0 - s)"
    proof (rule flow_eq_rev(1)[symmetric])
      have "2 * t0 + - 1 * s \<in> {t..t0} \<union> {t0..t}"
        using s by force
      then have "2 * t0 + - 1 * s \<in> existence_ivl t0 y0"
        using \<open>t0 \<in> T\<close> \<open>y0 \<in> X\<close> ll_on_open.in_existence_between_zeroI ll_on_open_axioms y0 by blast
      then show "2 * t0 - s \<in> existence_ivl t0 y0"
        by auto
    qed fact+
    also have "\<dots> \<in> Y"
      using s by (simp add: closed_segment_real remain)
    finally show ?thesis  .
  qed
  interpret rev: ll_on_open "(\<lambda>t. - f (2 * t0 - t))" "?m ` T" ..
  assume "\<not> t \<ge> t0"
  then have "norm (rev.flow t0 y0 (2 * t0 - t) - rev.flow t0 z0 (2 * t0 - t)) \<le>
    norm (y0 - z0) * exp ((K + 1) * (2 * t0 - t - t0))"
    using lipschitz \<open>t0 \<in> T\<close> \<open>y0 \<in> Y\<close> \<open>z0 \<in> Y\<close> \<open>Y \<subseteq> X\<close>
    by (intro rev.exponential_initial_condition_nonneg)
      (auto intro!: flow_eq_rev[OF  \<open>t0 \<in> T\<close> \<open>z0 \<in> X\<close> z0] flow_eq_rev[OF  \<open>t0 \<in> T\<close> \<open>y0 \<in> X\<close> y0]
        remain_rev remain y0 z0 lipschitz
        simp: lipschitz_uminus' closed_segment_real)
  thus ?thesis
    using \<open>\<not> t \<ge> t0\<close>
    by (simp add: flow_eq_rev[OF  \<open>t0 \<in> T\<close> \<open>y0 \<in> X\<close> y0] flow_eq_rev[OF \<open>t0 \<in> T\<close> \<open>z0 \<in> X\<close> z0])
qed

lemma
  existence_ivl_cballs:
  assumes iv_in: "t0 \<in> T" "x0 \<in> X"
  obtains t u L
  where
    "\<And>y. y \<in> cball x0 u \<Longrightarrow> cball t0 t \<subseteq> existence_ivl t0 y"
    "\<And>s y. y \<in> cball x0 u \<Longrightarrow> s \<in> cball t0 t \<Longrightarrow> flow t0 y s \<in> cball y u"
    "lipschitz (cball t0 t\<times>cball x0 u) (\<lambda>(t, x). flow t0 x t) L"
    "\<And>y. y \<in> cball x0 u \<Longrightarrow> cball y u \<subseteq> X"
    "0 < t" "0 < u"
proof -
  from local_unique_solutions[OF iv_in]
  obtain t u L where usol: "\<And>y. y \<in> cball x0 u \<Longrightarrow>
    unique_solution (ll_on_open.existence_ivp f T X t0 x0 \<lparr>ivp_x0 := y, ivp_T := cball t0 t, ivp_X := cball y u\<rparr>)"
    and subs: "\<And>y. y \<in> cball x0 u \<Longrightarrow> cball y u \<subseteq> X"
    and lipschitz: "\<And>s. s \<in> cball t0 t \<Longrightarrow> lipschitz (cball x0 (2*u)) (f s) L"
    and subsT: "cball t0 t \<subseteq> T"
    and subs': "cball x0 (2 * u) \<subseteq> X"
    and tu: "0 < t" "0 < u"
    by metis
  {
    fix y assume y: "y \<in> cball x0 u"
    from subs[OF y] \<open>0 < u\<close> have "y \<in> X" by auto
    from usol[OF y] interpret unique_solution
      "(ll_on_open.existence_ivp f T X t0 x0 \<lparr>ivp_x0 := y, ivp_T := cball t0 t, ivp_X := cball y u\<rparr>)"
      .
    note * = maximal_existence_flow[OF \<open>t0 \<in> T\<close> \<open>y \<in> X\<close> is_solution_on_superset_domain[OF is_solution_solution],
      where K = "cball t0 t", simplified existence_ivp_def, simplified, OF subs,
        OF y refl less_imp_le[OF \<open>0 < t\<close>] subsT]
    from * have eivl: "cball t0 t \<subseteq> existence_ivl t0 y"
      by simp
    {
      fix s::real assume s: "s \<in> cball t0 t"
      from *(2)[of s] this have "flow t0 y s = solution s"
        by (auto simp: existence_ivp_def)
      also
      from s is_solutionD(3)[OF is_solution_solution]
      have "\<dots> \<in> cball y u"
        by (auto simp del: mem_cball)
      finally have "flow t0 y s \<in> cball y u" .
    }
    note eivl this
  } note * = this
  note *
  moreover
  have cont_on_f_flow:
    "\<And>x1 S. S \<subseteq> cball t0 t \<Longrightarrow> x1 \<in> cball x0 u \<Longrightarrow> continuous_on S (\<lambda>t. f t (flow t0 x1 t))"
    using subs[of x0] \<open>u > 0\<close> *(1) \<open>t0 \<in> T\<close>
    by (auto intro!: continuous_at_imp_continuous_on f_flow_continuous)
  thm compact_Times[OF compact_cball compact_cball]
  have "bounded ((\<lambda>(t, x). f t x) ` (cball t0 t \<times> cball x0 (2 * u)))"
    using mem_cball subs' subsT
    by (auto intro!: compact_imp_bounded compact_continuous_image compact_Times
      continuous_intros
      simp: split_beta')
  then obtain B where B: "\<And>s y. s \<in> cball t0 t \<Longrightarrow> y \<in> cball x0 (2 * u) \<Longrightarrow> norm (f s y) \<le> B" "B > 0"
    by (auto simp: bounded_pos cball_def)
  have flow_in_cball: "flow t0 x1 s \<in> cball x0 (2 * u)"
    if s: "s \<in> cball t0 t" and x1: "x1 \<in> cball x0 u"
    for s::real and x1
  proof -
    from *(2)[OF x1 s] have "flow t0 x1 s \<in> cball x1 u" .
    also have "\<dots> \<subseteq> cball x0 (2 * u)"
      using x1
      by (auto intro!: dist_triangle_le[OF add_mono, of _ x1 u _ u, simplified]
        simp: dist_commute)
    finally show ?thesis .
  qed
  have "lipschitz (cball t0 t\<times>cball x0 u) (\<lambda>(t, x). flow t0 x t) (B + exp ((L + 1) * \<bar>t\<bar>))"
  proof (rule lipschitzI, safe)
    fix t1 t2 :: real and x1 x2
    assume t1: "t1 \<in> cball t0 t" and t2: "t2 \<in> cball t0 t"
      and x1: "x1 \<in> cball x0 u" and x2: "x2 \<in> cball x0 u"
    have t1_ex: "t1 \<in> existence_ivl t0 x1"
      and t2_ex: "t2 \<in> existence_ivl t0 x1" "t2 \<in> existence_ivl t0 x2"
      and "x1 \<in> cball x0 (2*u)" "x2 \<in> cball x0 (2*u)"
      using *(1)[OF x1] *(1)[OF x2] t1 t2 x1 x2 tu by auto
    have "dist (flow t0 x1 t1) (flow t0 x2 t2) \<le>
      dist (flow t0 x1 t1) (flow t0 x1 t2) + dist (flow t0 x1 t2) (flow t0 x2 t2)"
      by (rule dist_triangle)
    also have "dist (flow t0 x1 t2) (flow t0 x2 t2) \<le> dist x1 x2 * exp ((L + 1) * \<bar>t2 - t0\<bar>)"
      unfolding dist_norm
    proof (rule exponential_initial_condition[of t0 t2 x1 "cball x0 (2 * u)" x2])
      fix s assume "s \<in> closed_segment t0 t2" hence s: "s \<in> cball t0 t"
        using t2
        by (auto simp: dist_real_def closed_segment_real split: if_split_asm)
      show "flow t0 x1 s \<in> cball x0 (2 * u)"
        by (rule flow_in_cball[OF s x1])
      show "flow t0 x2 s \<in> cball x0 (2 * u)"
        by (rule flow_in_cball[OF s x2])
      show "lipschitz (cball x0 (2 * u)) (f s) L" if "s \<in> closed_segment t0 t2" for s
        using that centre_in_cball convex_contains_segment less_imp_le t2 tu(1)
        by (blast intro!: lipschitz)
    qed fact+
    also have "\<dots> \<le> dist x1 x2 * exp ((L + 1) * \<bar>t\<bar>)"
      using \<open>u > 0\<close> t2
      by (auto
        intro!: mult_left_mono add_nonneg_nonneg lipschitz[THEN lipschitz_nonneg]
        simp: cball_eq_empty cball_eq_sing' dist_real_def)
    also
    have "x1 \<in> X"
      using x1 subs[of x0] \<open>u > 0\<close>
      by auto
    have integrable:
      "(\<lambda>t. f t (flow t0 x1 t)) integrable_on {t0..max t1 t2}"
      "(\<lambda>t. f t (flow t0 x1 t)) integrable_on {t2..t1}"
      "(\<lambda>t. f t (flow t0 x1 t)) integrable_on {t1..t2}"
      "(\<lambda>t. f t (flow t0 x1 t)) integrable_on {min t2 t1..t0}"
      using t1 t2 t1_ex x1 flow_in_cball[OF _ x1]
      by (auto intro!: order_trans[OF integral_bound[where B=B]] cont_on_f_flow B
        integrable_continuous_real
        simp: dist_real_def integral_minus_sets')
    note [simp] = t1_ex t2_ex \<open>x1 \<in> X\<close> integrable
    have "dist (flow t0 x1 t1) (flow t0 x1 t2) \<le> dist t1 t2 * B"
      using t1 t2 x1 flow_in_cball[OF _ x1] \<open>t0 \<in> T\<close>
        integral_combine[of t2 t0 t1 "\<lambda>t. f t (flow t0 x1 t)"]
        integral_combine[of t1 t0 t2 "\<lambda>t. f t (flow t0 x1 t)"]
      by (auto simp: flow_fixed_point'' closed_segment_real dist_norm add.commute
          norm_minus_commute integral_minus_sets' integral_minus_sets
        intro!: order_trans[OF integral_bound[where B=B]] cont_on_f_flow B)
    finally
    have "dist (flow t0 x1 t1) (flow t0 x2 t2) \<le>
        dist t1 t2 * B + dist x1 x2 * exp ((L + 1) * \<bar>t\<bar>)"
      by arith
    also have "\<dots> \<le> dist (t1, x1) (t2, x2) * B + dist (t1, x1) (t2, x2) * exp ((L + 1) * \<bar>t\<bar>)"
      using \<open>B > 0\<close>
      by (auto intro!: add_mono mult_right_mono simp: dist_prod_def)
    finally show "dist (flow t0 x1 t1) (flow t0 x2 t2)
       \<le> (B + exp ((L + 1) * \<bar>t\<bar>)) * dist (t1, x1) (t2, x2)"
      by (simp add: algebra_simps)
  qed (simp add: \<open>0 < B\<close> less_imp_le)
  ultimately
  show thesis using subs tu ..
qed

lemma filterlim_real_at_infinity_sequentially[tendsto_intros]:
     "filterlim real at_infinity sequentially"
  by (simp add: filterlim_at_top_imp_at_infinity filterlim_real_sequentially)

lemma existence_ivl_ninfty:
  assumes iv_in: "t0 \<in> T" "x0 \<in> X"
  shows inf_existence_ninfty[intro,simp]: "inf_existence t0 x0 \<noteq> \<infinity>"
    and sup_existence_ninfty[intro,simp]: "sup_existence t0 x0 \<noteq> -\<infinity>"
  using existence_ivl_initial_time[OF iv_in]
  by (auto simp: existence_ivl_def)

lemma
  flow_leaves_compact_ivl: \<comment>\<open>explosion if the solution exists for only finite time\<close>
  assumes iv_in: "t0 \<in> T" "x0 \<in> X"
  assumes "sup_existence t0 x0 < \<infinity>"
  assumes "real_of_ereal (sup_existence t0 x0) \<in> T"
  assumes "compact K"
  assumes "K \<subseteq> X"
  obtains t where "t \<ge> t0" "t \<in> existence_ivl t0 x0" "flow t0 x0 t \<notin> K"
proof (atomize_elim, rule ccontr, auto)
  assume "\<forall>t. t \<in> ll_on_open.existence_ivl f T X t0 x0 \<longrightarrow> t0 \<le> t \<longrightarrow> flow t0 x0 t \<in> K"
  note flow_in_K = this[rule_format]
  with assms obtain b where b: "sup_existence t0 x0 = ereal b"
    by (cases "sup_existence t0 x0") auto
  from b have b_gtI: "b > s" if "s \<in> existence_ivl t0 x0" for s
    using that
    by (auto simp add: existence_ivl_def ereal_less_ereal_Ex)

  from assms b have "b \<in> T" by simp
  from b have "b > t0"
    by (auto intro!: b_gtI iv_in)
  from b have "b > inf_existence t0 x0"
    using existence_ivl_initial_time[OF iv_in]
    by (auto simp add: existence_ivl_def assms)
  note b_gt = \<open>b > inf_existence t0 x0\<close> \<open>b > t0\<close>

  have in_existence_ivlI: "\<And>t. t0 \<le> t \<Longrightarrow> t < b \<Longrightarrow> t \<in> existence_ivl t0 x0"
    using b existence_ivl_ninfty[OF iv_in] existence_ivl_initial_time[OF iv_in]
    by (auto simp: existence_ivl_def assms real_image_ereal_ivl
      split: if_split_asm)

  have ev1: "eventually (\<lambda>n. b -  1 / n > inf_existence t0 x0) sequentially"
    using _ b_gt(1)
    by (rule order_tendstoD) (auto intro: tendsto_eq_intros seq_harmonic')
  have ev2: "eventually (\<lambda>n. n > 0) sequentially"
    by (metis eventually_at_top_dense)
  have ev3: "eventually (\<lambda>n. t0 + 1 / n < b) sequentially"
    by (rule order_tendstoD) (auto intro!: tendsto_intros tendsto_divide_0 \<open>t0 < b\<close>)
  let ?f = "\<lambda>n::nat. flow t0 x0 (b - 1/n)"
  from eventually_conj[OF ev1 eventually_conj[OF ev2 ev3]]
  obtain N::nat where N: "N > 0" "inf_existence t0 x0 < (b - 1 / N)" "t0 + 1 / N < b"
    by (auto dest!: eventually_happens)
  let ?fN = "?f o (op + N)"

  have "{t0 .. b} \<subseteq> T"
  proof
    fix x assume "x \<in> {t0 .. b}"
    then show "x \<in> T"
      by (cases "x = b") (auto simp: \<open>b \<in> T\<close> intro!: mem_existence_ivl_subset[OF iv_in] in_existence_ivlI)
  qed
  then have "bounded ((\<lambda>(t, x). f t x) ` ({t0 .. b} \<times> K))"
    using \<open>K \<subseteq> X\<close> \<open>compact K\<close> iv_in
    by (auto intro!: compact_imp_bounded compact_continuous_image
      continuous_intros compact_Times
      simp: split_beta subset_iff)
  then obtain M where M: "\<And>t x. t \<in> {t0 .. b} \<Longrightarrow> x \<in> K \<Longrightarrow> norm (f t x) \<le> M" "M > 0"
    by (force simp: bounded_pos)
  have dist_flow_le: "dist (flow t0 x0 t1) (flow t0 x0 t2) \<le> M * abs (t2 - t1)"
    if H: "t1 \<in> existence_ivl t0 x0" "t2 \<in> existence_ivl t0 x0" "t0 \<le> t1" "t0 \<le> t2"
    for t1 t2
  proof -
    {
      fix t1 t2
      assume t1: "t1 \<in> existence_ivl t0 x0"
        and t2: "t2 \<in> existence_ivl t0 x0"
      assume "t0 \<le> t1"
      assume "t1 < t2"
      let ?I = "\<lambda>ivl. (\<lambda>t. f t (flow t0 x0 t)) integrable_on ivl"
      have I[simp]: "?I {t0 .. t1}" "?I {t0 .. t2}" "?I {t1 .. t2}" "?I {t1 .. t0}"
        using closed_segment_subset_existence_ivl[OF iv_in t1]
           closed_segment_subset_existence_ivl[OF iv_in t2] \<open>t1 < t2\<close> \<open>t0 \<in> T\<close>
        by (force intro!: integrable_continuous_real continuous_at_imp_continuous_on
          f_flow_continuous \<open>x0 \<in> X\<close> simp: closed_segment_real split: if_split_asm)+
      hence "flow t0 x0 t2 - flow t0 x0 t1 = integral {t1..t2} (\<lambda>t. f t (flow t0 x0 t))"
        unfolding flow_fixed_point''[OF \<open>t1 \<in> existence_ivl t0 x0\<close> iv_in]
          flow_fixed_point''[OF \<open>t2 \<in> existence_ivl t0 x0\<close> iv_in]
        using \<open>t1 < t2\<close> integral_combine[of t1 t0 t2 "\<lambda>t. f t (flow t0 x0 t)"]
        by (auto simp: closed_segment_real algebra_simps integral_combine)
      also have "norm \<dots> \<le> M * (t2 - t1)"
        using closed_segment_subset_existence_ivl[OF iv_in t1]
           closed_segment_subset_existence_ivl[OF iv_in t2] \<open>t0 \<le> t1\<close> \<open>t1 < t2\<close>
           b_gtI[OF t2]
        by (intro integral_bound)
          (auto intro!: flow_in_K M continuous_at_imp_continuous_on
            f_flow_continuous iv_in
            simp: closed_segment_real)
      finally have "dist (flow t0 x0 t2) (flow t0 x0 t1) \<le> M * (t2 - t1)"
        by (simp add: dist_norm)
    } from this[of t1 t2] this[of t2 t1] H
    show ?thesis
      by (auto simp: abs_real_def dist_commute not_less less_eq_real_def)
  qed
    \<comment> "TODO: Cauchy really needed in the following?"

  have "Cauchy ?f"
  proof (rule metric_CauchyI)
    fix e::real assume "0 < e"
    have "(\<lambda>n. M / n) \<longlonglongrightarrow> 0"
      by (auto intro!: tendsto_divide_0 tendsto_eq_intros
        simp: filterlim_at_top_imp_at_infinity filterlim_real_sequentially)
    hence "eventually (\<lambda>n. M / n < e/2) sequentially"
      by (metis (poly_guards_query) \<open>0 < e\<close> half_gt_zero_iff order_tendsto_iff)
    from eventually_conj[OF this eventually_conj[OF ev1 eventually_conj[OF ev2 ev3]]]
    obtain N::nat
    where N: "N > 0" "M / N < e / 2" "inf_existence t0 x0 < (b - 1 / N)" "t0 + 1 / N < b"
      by (auto dest!: eventually_happens)
    {
      fix n m assume "n \<ge> N" "m \<ge> N"
      with N have nm: "n > 0" "m > 0" "b - 1 / N \<le> b - 1 / n"
        "b - 1 / N \<le> b - 1 / m" "t0 +  1/ n \<le> t0 + 1 / N"
        by (auto intro!: divide_left_mono)
      from le_less_trans[OF \<open>t0 + 1 / n \<le> t0 + 1/N\<close> \<open>t0 + 1/N < b\<close>] have "t0 + 1/n < b" .
      with nm have "dist (flow t0 x0 (b - 1 / n)) (flow t0 x0 (b - 1 / m)) \<le>
          M * abs (b - 1 / m - (b - 1 / n))"
        using b N existence_ivl_ninfty[OF iv_in] b_gt(1) less_ereal.simps(1)
        by (intro dist_flow_le;
          cases "inf_existence t0 x0";
          simp add: existence_ivl_def real_image_ereal_ivl)
      also have "\<dots> \<le> M * (1 / m + 1 / n)"
        using \<open>M > 0\<close> by (auto intro!: mult_left_mono order_trans[OF abs_triangle_ineq4])
      also have "\<dots> \<le> M / m + M / n" by (simp add: algebra_simps)
      also have "\<dots> \<le> M / N + M / N" using nm \<open>n \<ge> N\<close> \<open>m \<ge> N\<close> \<open>M>0\<close> \<open>0 < N\<close>
        by (intro add_mono) (auto intro!: divide_left_mono mult_pos_pos)
      also have "\<dots> < e / 2 + e / 2" using N by (intro add_strict_mono) simp
      also have "\<dots> = e" by simp
      finally have "dist (flow t0 x0 (b - 1 / n)) (flow t0 x0 (b - 1 / m)) < e" .
    }
    thus "\<exists>M::nat. \<forall>m\<ge>M. \<forall>n\<ge>M.
      dist (flow t0 x0 (b - 1 / real m)) (flow t0 x0 (b - 1 / real n)) < e"
      by blast
  qed
  hence "Cauchy ?fN"
    by (rule Cauchy_subseq_Cauchy) (metis nat_add_left_cancel_less subseq_def)
  moreover
  {
    {
      fix n::nat
      have "inf_existence t0 x0 < (b - 1 / N)" by fact
      also have "\<dots> \<le> (b - 1 / (N + n))"
        using \<open>0 < N\<close>
        by (auto intro!: divide_left_mono mult_pos_pos add_pos_nonneg)
      finally have "inf_existence t0 x0 < (b - 1 / (N + n))" .
    } moreover {
      fix n::nat
      have "t0 + 1 / (real N + real n) \<le> t0 + 1 / N"
        by (auto intro!: divide_left_mono mult_pos_pos add_pos_nonneg \<open>0 < N\<close>)
      also note \<open>\<dots> < b\<close>
      finally have "t0 < b - 1 / (N + n)" by simp
    } ultimately
    have "(\<forall>n. ?fN n \<in> K)"
      using existence_ivl_ninfty[OF iv_in] b_gt \<open>0 < N\<close> N
      by (cases "inf_existence t0 x0")
        (auto intro!: add_pos_nonneg flow_in_K less_imp_le
          simp: existence_ivl_def \<open>x0 \<in> X\<close> real_image_ereal_ivl b)
  }
  ultimately
  have "\<exists>l\<in>K. ?fN \<longlonglongrightarrow> l"
    using \<open>compact K\<close>
    by (auto simp: compact_eq_bounded_closed complete_eq_closed[symmetric] complete_def)
  then obtain x1 where x1: "x1 \<in> K" "?fN \<longlonglongrightarrow> x1" by metis
  hence "x1 \<in> X" using assms by auto

  have flow_at_b: "(flow t0 x0 \<longlongrightarrow> x1) (at b within {t0 .. b})"
  proof (rule tendstoI)
    fix e::real assume "0 < e" hence "0 < e / 2" by auto
    from x1(2)[THEN tendstoD, OF this]
    have ev3: "eventually (\<lambda>n. dist ((?fN) n) x1 < e/2) sequentially" .
    have "eventually (\<lambda>n. 1 / n < e / (2 * M)) sequentially"
      by (rule order_tendstoD[where y = 0])
        (auto intro!: tendsto_divide_0 tendsto_intros divide_pos_pos
          \<open>0 < e\<close> \<open>0 < M\<close>)
    hence ev4: "eventually (\<lambda>n. 1 / (N + n) < e / (2 * M)) sequentially"
      using ev2
    proof eventually_elim
      case (elim n)
      hence "1 / real (N + n) < 1 / n"
        by (auto intro!: divide_strict_left_mono \<open>0 < N\<close>)
      also have "\<dots> < e / (2 * M)"  by fact
      finally show ?case .
    qed
    from eventually_conj[OF ev3 eventually_conj [OF ev4 ev2]]
    obtain N'
    where N': "dist (?fN N') x1 < e / 2" "N' > 0" "1 / (N + N') < e / (2 * M)"
      by (auto dest!: eventually_happens)

    have "eventually (\<lambda>x. x < b) (at b within {t0 .. b})"
      by (auto simp: eventually_at_filter)
    moreover
    have "eventually (\<lambda>x. x > b - 1 / (real N' + real N)) (at b within {t0 .. b})"
      using N' by (auto intro!: order_tendstoD)
    moreover
    have "eventually (\<lambda>x. x < b - (1 / real (N + N') - e / 2 / M)) (at b within {t0 .. b})"
      using N' by (auto intro!: order_tendstoD)
    hence "eventually (\<lambda>x. x - (b - 1 / real (N + N')) < e / 2 / M) (at b within {t0 .. b})"
      by (simp add: algebra_simps)
    moreover
    have "eventually (\<lambda>x. x > t0) (at b within {t0 .. b})" "eventually (\<lambda>x. x < b) (at b within {t0 .. b})"
      using b_gt
      by (intro order_tendstoD)
        (auto simp: eventually_at_filter intro!: tendsto_intros)
    moreover
    hence "eventually (\<lambda>x. x \<in> existence_ivl t0 x0) (at b within {t0 .. b})"
      by eventually_elim (auto simp: in_existence_ivlI)
    ultimately have "eventually (\<lambda>x. dist (flow t0 x0 x) (?fN N') < e / 2) (at b within {t0 .. b})"
    proof eventually_elim
      case (elim x)
      have "dist (flow t0 x0 x) (flow t0 x0 (b - 1 / real (N + N'))) \<le>
          M * \<bar>b - 1 / real (N + N') - x\<bar>"
      proof (rule dist_flow_le)
        have "t0 + 1 / real (N + N') \<le> t0 + 1 / N"
          by (auto intro!: divide_left_mono mult_pos_pos add_pos_nonneg \<open>0 < N\<close>)
        also have "\<dots> < b" by fact
        finally
        show "t0 \<le> b - 1 / real (N + N')" by simp
        then show "b - 1 / real (N + N') \<in> existence_ivl t0 x0"
          using elim \<open>0 < N'\<close>
          by (auto intro!: in_existence_ivlI)
      qed (intro elim less_imp_le)+
      also have "\<bar>b - 1 / real (N + N') - x\<bar> = x - (b - 1 / real (N + N'))"
        using \<open>N > 0\<close> \<open>N' > 0\<close> elim
        by (auto simp: abs_real_def algebra_simps)
      also have "M * \<dots> < M * (e / 2 / M)"
        by (rule mult_strict_left_mono) fact+
      also have "\<dots> = e / 2"
        using \<open>0 < M\<close> by simp
      finally show ?case by (simp add: o_def)
    qed
    thus "eventually (\<lambda>x. dist (flow t0 x0 x) x1 < e) (at b within {t0 .. b})"
    proof eventually_elim
      case (elim x)
      have "dist (flow t0 x0 x) x1 \<le> dist (flow t0 x0 x) (?fN N') + dist (?fN N') x1"
        by (rule dist_triangle)
      also note elim
      also note N'(1)
      finally show ?case by simp
    qed
  qed

  define u where "u t = (if t < b then flow t0 x0 t else x1)" for t
  have u_below_b: "(u \<longlongrightarrow> u s) (at s within {t0..b})"
    if s: "t0 < s" "s < b" for s
  proof -
    from s have "s \<in> interior {t0 .. b}"
      by (simp add: interior_atLeastAtMost)
    hence "at s within {t0 .. b} = at s"
      by (subst at_within_interior) auto
    also
    have "at s = at s within {t0 <..< b}"
      using s by (subst (2) at_within_open) auto
    also
    have "\<forall>\<^sub>F x in at s within {t0<..<b}. flow t0 x0 x = (if x < b then flow t0 x0 x else x1)"
      by (auto simp: eventually_at_filter \<open>x0 \<in> X\<close> intro!: in_existence_ivlI)
    hence "((\<lambda>t. u t) \<longlongrightarrow> u s) \<dots>"
      using s
      by (intro filterlim_mono_eventually[OF tendsto_eq_rhs[OF flow_tendsto] order.refl])
        (auto simp add: iv_in in_existence_ivlI u_def)
    finally show ?thesis .
  qed
  have "((\<lambda>t. u t) \<longlongrightarrow> u b) (at b within {t0 .. b})"
    by (rule filterlim_mono_eventually[OF tendsto_eq_rhs[OF flow_at_b] order.refl])
      (auto simp: eventually_at_filter u_def)
  hence u_at_b: "((\<lambda>t. u t) \<longlongrightarrow> u b) (at b within {t0 .. b})"
    by (rule tendsto_within_subset) auto
  have "eventually (\<lambda>x. x < b) (at t0 within {t0 .. b})"
    using \<open>t0 < b\<close>
    by (auto intro!: order_tendstoD)
  hence "\<forall>\<^sub>F x in at t0 within {t0..b}. flow t0 x0 x = (if x < b then flow t0 x0 x else x1)"
    by eventually_elim auto
  then have u_at_t0: "((\<lambda>t. u t) \<longlongrightarrow> u t0) (at t0 within {t0 .. b})"
    using \<open>t0 < b\<close>
    by (intro filterlim_mono_eventually[OF tendsto_eq_rhs[OF flow_tendsto[where ts="\<lambda>x. x"]]])
      (auto simp add: iv_in u_def)

  {
    fix s assume "t0 \<le> s" "s \<le> b"
    with u_at_b u_below_b u_at_t0 have "(u \<longlongrightarrow> u s) (at s within {t0 .. b})"
      by (cases "s = b"; cases "s = t0"; simp)
  }
  hence u_cont: "continuous_on {t0 .. b} u"
    by (auto simp: continuous_on)
  moreover
  have u_fixed_point: "u t = x0 + integral {t0 .. t} (\<lambda>s. f s (u s))"
    if "t0 \<le> t" "t < b" for t
    using that
    by (subst integral_spike[where s="{b}" and g = "\<lambda>s. f s (flow t0 x0 s)"])
      (auto simp: u_def flow_fixed_point iv_in not_less in_existence_ivlI)
  have cont: "continuous_on {t0 .. b} (\<lambda>s. f s (u s))"
    using \<open>{t0 .. b} \<subseteq> T\<close>
    by (safe intro!: continuous_intros u_cont)
        (auto simp: u_def intro!: flow_in_domain iv_in \<open>x1 \<in> X\<close> in_existence_ivlI)

  have fixed_point_tendsto:
    "((\<lambda>t. x0 + integral {t0 .. t} (\<lambda>s. f s (u s))) \<longlongrightarrow>
      x0 + integral {t0 .. b} (\<lambda>s. f s (u s))) (at b within {t0 .. b})"
    using \<open>t0 < b\<close>
    by (auto intro!: integrable_continuous_real cont tendsto_intros
      indefinite_integral_continuous[unfolded continuous_on, rule_format])
  have "\<forall>\<^sub>F x in at b within {t0..b}. x0 + integral {t0..x} (\<lambda>s. f s (u s)) = u x"
    by (auto simp: eventually_at_filter u_fixed_point)
  with fixed_point_tendsto order.refl order.refl
  have u_tendsto: "(u \<longlongrightarrow> x0 + integral {t0 .. b} (\<lambda>s. f s (u s))) (at b within {t0 .. b})"
    by (rule filterlim_mono_eventually)
  have "{t0..b} - {b} = {t0..<b}" by auto
  then have "at b within {t0..b} \<noteq> bot" using \<open>b > t0\<close>
    unfolding trivial_limit_within
    by (simp add: islimpt_in_closure)
  then have "u b = x0 + integral {t0..b} (\<lambda>s. f s (u s))"
    using u_at_b u_tendsto
    by (rule tendsto_unique)
  with u_fixed_point have "\<And>s. t0 \<le> s \<Longrightarrow> s \<le> b \<Longrightarrow> x0 + integral {t0..s} (\<lambda>s. f s (u s)) = u s"
    by (case_tac "s = b") auto
  with _ have u_vderiv:
    "\<And>s. t0 \<le> s \<Longrightarrow> s \<le> b \<Longrightarrow> (u has_vector_derivative f s (u s)) (at s within {t0 .. b})"
    by (rule has_vector_derivative_imp)
      (auto intro!: derivative_eq_intros cont integral_has_vector_derivative)

  interpret i:
    ivp "\<lparr>ivp_f = \<lambda>(t, x). f t x, ivp_t0 = t0, ivp_x0 = x0, ivp_T = {t0..b}, ivp_X = X\<rparr>"
    by unfold_locales (auto simp: \<open>t0 < b\<close> less_imp_le \<open>x0 \<in> X\<close>)
  have "i.is_solution u"
    by (rule i.is_solutionI; clarsimp simp add: u_vderiv)
      (auto simp: u_def \<open>x0 \<in> X\<close> \<open>x1 \<in> X\<close> \<open>t0 < b\<close> iv_in
        intro!: flow_in_domain in_existence_ivlI)
  with iv_in \<open>{t0 .. b} \<subseteq> T\<close> \<open>t0 < b\<close> iv_in
  have "{t0 .. b} \<subseteq> existence_ivl t0 x0"
    by (intro maximal_existence_flow(1)[OF iv_in])
      (auto simp: is_interval_closed_interval)
  hence "b \<in> existence_ivl t0 x0" using \<open>t0 < b\<close>
    by auto
  thus False
    using b_gtI real_less_ereal_iff
    by (auto simp: existence_ivl_def \<open>x0 \<in> X\<close> b)
qed

lemma
  sup_existence_maximal:
  assumes "t0 \<in> T" "x0 \<in> X"
  assumes "\<And>t. t0 \<le> t \<Longrightarrow> t \<in> existence_ivl t0 x0 \<Longrightarrow> flow t0 x0 t \<in> K"
  assumes "compact K" "K \<subseteq> X"
  assumes "sup_existence t0 x0 \<noteq> \<infinity>"
  shows "real_of_ereal (sup_existence t0 x0) \<notin> T"
  using flow_leaves_compact_ivl[of t0 x0 K] assms by force

lemma fixes a b c::ereal
  shows not_inftyI: "a < b \<Longrightarrow> b < c \<Longrightarrow> abs b \<noteq> \<infinity>"
  by force

lemma
  interval_neqs:
  fixes r s t::real
  shows "{r<..<s} \<noteq> {t<..}"
    and "{r<..<s} \<noteq> {..<t}"
    and "{r<..<ra} \<noteq> UNIV"
    and "{r<..} \<noteq> {..<s}"
    and "{r<..} \<noteq> UNIV"
    and "{..<r} \<noteq> UNIV"
    and "{} \<noteq> {r<..}"
    and "{} \<noteq> {..<r}"
  subgoal by (metis dual_order.strict_trans greaterThanLessThan_iff greaterThan_iff gt_ex not_le order_refl)
  subgoal by (metis (no_types, hide_lams) greaterThanLessThan_empty_iff greaterThanLessThan_iff gt_ex lessThan_iff minus_minus neg_less_iff_less not_less order_less_irrefl)
  subgoal by force
  subgoal by (metis greaterThanLessThan_empty_iff greaterThanLessThan_eq greaterThan_iff inf.idem lessThan_iff lessThan_non_empty less_irrefl not_le)
  subgoal by force
  subgoal by force
  subgoal using greaterThan_non_empty by blast
  subgoal using lessThan_non_empty by blast
  done

lemma greaterThanLessThan_eq_iff:
  fixes r s t u::real
  shows "({r<..<s} = {t<..<u}) = (r \<ge> s \<and> u \<le> t \<or> r = t \<and> s = u)"
  by (metis cInf_greaterThanLessThan cSup_greaterThanLessThan greaterThanLessThan_empty_iff not_le)

lemma real_of_ereal_image_greaterThanLessThan_iff:
  "real_of_ereal ` {a <..< b} = real_of_ereal ` {c <..< d} \<longleftrightarrow> (a \<ge> b \<and> c \<ge> d \<or> a = c \<and> b = d)"
  unfolding real_atLeastGreaterThan_eq
  by (cases a; cases b; cases c; cases d;
    simp add: greaterThanLessThan_eq_iff interval_neqs interval_neqs[symmetric])

lemma uminus_image_real_of_ereal_image_greaterThanLessThan:
  "uminus ` real_of_ereal ` {l <..< u} = real_of_ereal ` {-u <..< -l}"
  by (force simp: algebra_simps ereal_less_uminus_reorder
    ereal_uminus_less_reorder intro: image_eqI[where x="-x" for x])

lemma add_image_real_of_ereal_image_greaterThanLessThan:
  "op + c ` real_of_ereal ` {l <..< u} = real_of_ereal ` {c + l <..< c + u}"
  apply safe
  subgoal for x
    using ereal_less_add[of c]
    by (force simp: real_of_ereal_add add.commute)
  subgoal for _ x
    by (force simp: add.commute real_of_ereal_minus ereal_minus_less ereal_less_minus
      intro: image_eqI[where x="x - c"])
  done

lemma add2_image_real_of_ereal_image_greaterThanLessThan:
  "(\<lambda>x. x + c) ` real_of_ereal ` {l <..< u} = real_of_ereal ` {l + c <..< u + c}"
  using add_image_real_of_ereal_image_greaterThanLessThan[of c l u]
  by (metis add.commute image_cong)

lemma minus_image_real_of_ereal_image_greaterThanLessThan:
  "op - c ` real_of_ereal ` {l <..< u} = real_of_ereal ` {c - u <..< c - l}"
  (is "?l = ?r")
proof -
  have "?l = op + c ` uminus ` real_of_ereal ` {l <..< u}" by auto
  also note uminus_image_real_of_ereal_image_greaterThanLessThan
  also note add_image_real_of_ereal_image_greaterThanLessThan
  finally show ?thesis by (simp add: minus_ereal_def)
qed

lemma
  inf_existence_minimal:
  assumes iv_in: "t0 \<in> T" "x0 \<in> X"
  assumes mem_compact: "\<And>t. t \<le> t0 \<Longrightarrow> t \<in> existence_ivl t0 x0 \<Longrightarrow> flow t0 x0 t \<in> K"
  assumes K: "compact K" "K \<subseteq> X"
  assumes inf: "inf_existence t0 x0 \<noteq> - \<infinity>"
  shows "real_of_ereal (inf_existence t0 x0) \<notin> T"
proof -
  let ?mirror  = "\<lambda>t. 2 * t0 - t"
  interpret rev: ll_on_open "\<lambda>t. - f (?mirror t)" "?mirror ` T" ..
  have rev_iv_in: "?mirror t0 \<in> ?mirror ` T" "x0 \<in> X" using iv_in by auto

  from rev_existence_ivl_eq[OF iv_in, unfolded rev.existence_ivl_def existence_ivl_def]
  have "real_of_ereal ` {rev.inf_existence t0 x0<..<rev.sup_existence t0 x0} =
    ?mirror ` real_of_ereal ` {inf_existence t0 x0<..<sup_existence t0 x0}"
    by (force intro!: image_eqI[where x="?mirror (real_of_ereal x)" for x])
  also have "\<dots> = real_of_ereal ` {2 * ereal t0 - sup_existence t0 x0<..<2 * ereal t0 - inf_existence t0 x0}"
    unfolding minus_image_real_of_ereal_image_greaterThanLessThan
    by simp
  finally have rev_bnds: "rev.inf_existence t0 x0 = 2 * t0 - (sup_existence t0 x0)"
    "rev.sup_existence t0 x0 = 2 * t0 - (inf_existence t0 x0)"
    unfolding real_of_ereal_image_greaterThanLessThan_iff
    using flow_eq_rev(2) iv_in(1) rev.existence_ivl_def rev_iv_in(2)
    by force+

  have rev_mem_compact: "2 * t0 - t0 \<le> t \<Longrightarrow> t \<in> rev.existence_ivl (2 * t0 - t0) x0 \<Longrightarrow> rev.flow (2 * t0 - t0) x0 t \<in> K" for t
    using mem_compact[of "?mirror t"] flow_eq_rev[OF iv_in, of "?mirror t"] rev_existence_ivl_eq[OF iv_in, of t]
    by auto
  have "real_of_ereal (rev.sup_existence (2 * t0 - t0) x0) \<notin> op - (2 * t0) ` T"
    using inf
    by (intro rev.sup_existence_maximal[OF rev_iv_in rev_mem_compact K])
      (auto simp: rev_bnds ereal_minus_eq_PInfty_iff)
  then show "real_of_ereal (inf_existence t0 x0) \<notin> T"
    using inf existence_ivl_def iv_in(1) rev_iv_in(2)
    by (cases "inf_existence t0 x0") (fastforce simp: rev_bnds)+
qed

lemma real_ereal_bound_lemma_up:
  assumes "s \<in> real_of_ereal ` {a<..<b}"
  assumes "t \<notin> real_of_ereal ` {a<..<b}"
  assumes "s \<le> t"
  shows "b \<noteq> \<infinity>"
  using assms
  apply (cases b)
  subgoal by force
  subgoal by (metis PInfty_neq_ereal(2) assms dual_order.strict_trans1 ereal_infty_less(1)
    ereal_less_ereal_Ex greaterThanLessThan_empty_iff greaterThanLessThan_iff greaterThan_iff
    image_eqI less_imp_le linordered_field_no_ub not_less order_trans
    real_greaterThanLessThan_infinity_eq real_image_ereal_ivl real_of_ereal.simps(1))
  subgoal by force
  done
lemma real_ereal_bound_lemma_down:
  assumes "s \<in> real_of_ereal ` {a<..<b}"
  assumes "t \<notin> real_of_ereal ` {a<..<b}"
  assumes "t \<le> s"
  shows "a \<noteq> - \<infinity>"
  using assms
  apply (cases b)
  apply (auto simp: real_greaterThanLessThan_infinity_eq)
  using assms(1) real_greaterThanLessThan_minus_infinity_eq
  apply auto
  done

lemma mem_is_intervalI:
  fixes a b c::real
  assumes "is_interval S"
  assumes "a \<in> S" "c \<in> S"
  assumes "a \<le> b" "b \<le> c"
  shows "b \<in> S"
  using assms is_interval_1 by blast

lemma
  initial_time_bounds:
  assumes iv_in: "t0 \<in> T" "x0 \<in> X"
  shows "inf_existence t0 x0 < t0" "t0 < sup_existence t0 x0"
  using existence_ivl_initial_time[OF iv_in]
  by (auto simp: existence_ivl_def ereal_real)

lemma
  mem_compact_implies_subset_existence_interval:
  assumes iv_in: "t0 \<in> T" "x0 \<in> X"
  assumes mem_compact: "\<And>t. t \<in> T \<Longrightarrow> flow t0 x0 t \<in> K"
  assumes K: "compact K" "K \<subseteq> X"
  assumes ivl: "is_interval T"
  shows "T \<subseteq> existence_ivl t0 x0"
proof
  fix t assume "t \<in> T"
  have "t0 \<in> existence_ivl t0 x0"
    by (rule existence_ivl_initial_time[OF iv_in])
  have "t < sup_existence t0 x0"
  proof (cases "sup_existence t0 x0")
    fix s
    assume s: "sup_existence t0 x0 = ereal s"
    with sup_existence_maximal[OF assms(1-5)] mem_existence_ivl_subset[OF iv_in]
    have "s \<notin> T"
      by auto
    from initial_time_bounds[OF iv_in] s
    have "t0 < s"
      by simp
    then have "t < s"
      using \<open>s \<notin> T\<close> iv_in \<open>t \<in> T\<close> ivl
      by (meson leI local.mem_is_intervalI not_less_iff_gr_or_eq)
    then show ?thesis using s by simp
  qed (auto simp: existence_ivl_ninfty[OF iv_in])
  moreover
  have "inf_existence t0 x0 < t"
  proof (cases "inf_existence t0 x0")
    fix i
    assume i: "inf_existence t0 x0 = ereal i"
    with inf_existence_minimal[OF assms(1-5)] mem_existence_ivl_subset[OF iv_in]
    have "i \<notin> T"
      by auto
    from initial_time_bounds[OF iv_in] i
    have "i < t0" by simp
    then have "i < t"
      using \<open>i \<notin> T\<close> iv_in \<open>t \<in> T\<close> ivl
      by (meson is_interval_1 less_imp_le not_le)
    then show ?thesis using i by simp
  qed (auto simp: existence_ivl_ninfty[OF iv_in])
  ultimately show "t \<in> existence_ivl t0 x0"
    by (simp add: rev_image_eqI existence_ivl_def)
qed

lemma
  subset_mem_compact_implies_subset_existence_interval:
  assumes ivl: "t0 \<in> T'" "is_interval T'" "T' \<subseteq> T"
  assumes iv_in: "x0 \<in> X"
  assumes mem_compact: "\<And>t. t \<in> T' \<Longrightarrow> t \<in> existence_ivl t0 x0 \<Longrightarrow> flow t0 x0 t \<in> K"
  assumes K: "compact K" "K \<subseteq> X"
  shows "T' \<subseteq> existence_ivl t0 x0"
proof (rule ccontr)
  assume "\<not> T' \<subseteq> existence_ivl t0 x0"
  then obtain t' where t': "t' \<in> T'" "t' \<notin> existence_ivl t0 x0"
    by auto
  then have "t' \<le> inf_existence t0 x0 \<or> t' \<ge> sup_existence t0 x0"
    by (cases "sup_existence t0 x0"; cases "inf_existence t0 x0")
       (auto simp: existence_ivl_def real_image_ereal_ivl split: if_split_asm)
  then show False
  proof
    assume t'_le: "ereal t' \<le> inf_existence t0 x0"
    then have ni: "inf_existence t0 x0 \<noteq> - \<infinity>" by auto
    then obtain i where i: "inf_existence t0 x0 = ereal i"
      using initial_time_bounds(1) iv_in ivl(1) ivl(3)
      by (cases "inf_existence t0 x0"; force)
    from assms have "t0 \<in> T" by auto
    have "i \<in> T'"
      using t'_le i initial_time_bounds[OF \<open>t0 \<in> T\<close> iv_in]
      by (intro mem_is_intervalI[OF ivl(2) t'(1) ivl(1)]) auto
    have *: "t \<in> T'" if "t \<le> t0" "t \<in> existence_ivl t0 x0" for t
      using that(2)
      by (intro mem_is_intervalI[OF ivl(2) \<open>i \<in> T'\<close> \<open>t0 \<in> T'\<close> _ that(1)])
        (auto simp add: existence_ivl_def i less_imp_le less_eq_ereal_def not_inftyI
          real_of_ereal_ord_simps)
    from inf_existence_minimal[OF \<open>t0 \<in> T\<close> iv_in mem_compact K ni, OF *]
    show False using \<open>i \<in> T'\<close> ivl by (auto simp: i)
  next
    assume t'_le: "sup_existence t0 x0 \<le> ereal t'"
    then have ns: "sup_existence t0 x0 \<noteq> \<infinity>" by auto
    then obtain s where s: "sup_existence t0 x0 = ereal s"
      using initial_time_bounds(2) iv_in ivl(1) ivl(3)
      by (cases "sup_existence t0 x0"; force)
    from assms have "t0 \<in> T" by auto
    have "s \<in> T'"
      using t'_le s initial_time_bounds[OF \<open>t0 \<in> T\<close> iv_in]
      by (intro mem_is_intervalI[OF ivl(2) ivl(1) t'(1)]) auto

    have *: "t \<in> T'" if "t0 \<le> t" "t \<in> existence_ivl t0 x0" for t
      using that(2)
      by (intro mem_is_intervalI[OF ivl(2) \<open>t0 \<in> T'\<close> \<open>s \<in> T'\<close> that(1)])
        (auto simp add: existence_ivl_def s real_of_ereal_ord_simps)
    from sup_existence_maximal[OF \<open>t0 \<in> T\<close> iv_in mem_compact K ns, OF *] \<open>s \<in> T'\<close> ivl
    show False by (auto simp: s)
  qed
qed

lemma
  global_right_existence_interval:
  assumes "b \<ge> t0"
  assumes b: "b \<in> existence_ivl t0 x0"
  assumes iv_in: "t0 \<in> T" "x0 \<in> X"
  obtains d K where "d > 0" "K > 0"
    "ball x0 d \<subseteq> X"
    "\<And>y. y \<in> ball x0 d \<Longrightarrow> b \<in> existence_ivl t0 y"
    "\<And>t y. y \<in> ball x0 d \<Longrightarrow> t \<in> {t0 .. b} \<Longrightarrow>
      dist (flow t0 x0 t) (flow t0 y t) \<le> dist x0 y * exp (K * abs (t - t0))"
    "\<And>e. e > 0 \<Longrightarrow>
      eventually (\<lambda>y. \<forall>t \<in> {t0 .. b}. dist (flow t0 x0 t) (flow t0 y t) < e) (at x0)"
proof -
  define seg where "seg = (\<lambda>t. flow t0 x0 t) ` (closed_segment t0 b)"
  have [simp]: "x0 \<in> seg"
    by (auto simp: seg_def intro!: image_eqI[where x=t0] simp: closed_segment_real iv_in)
  have "seg \<noteq> {}" by (auto simp: seg_def closed_segment_real)
  moreover
  have "compact seg"
    using iv_in b
    by (auto simp: seg_def closed_segment_real
        intro!: compact_continuous_image continuous_at_imp_continuous_on flow_continuous;
      metis (erased, hide_lams) atLeastAtMost_iff closed_segment_real
        closed_segment_subset_existence_ivl contra_subsetD order.trans)
  moreover note open_domain(2)
  moreover have "seg \<subseteq> X"
    using closed_segment_subset_existence_ivl b
    by (auto simp: seg_def intro!: flow_in_domain iv_in)
  ultimately
  obtain e where e: "0 < e" "{x. infdist x seg \<le> e} \<subseteq> X"
    thm compact_in_open_separated
    by (rule compact_in_open_separated)
  define A where "A = {x. infdist x seg \<le> e}"

  have "A \<subseteq> X" using e by (simp add: A_def)

  have mem_existence_ivlI: "\<And>s. t0 \<le> s \<Longrightarrow> s \<le> b \<Longrightarrow> s \<in> existence_ivl t0 x0"
    by (rule in_existence_between_zeroI[OF iv_in b]) auto

  have "compact A"
    unfolding A_def
    by (rule compact_infdist_le) fact+
  have "compact {t0 .. b}" "{t0 .. b} \<subseteq> T"
    using mem_existence_ivlI mem_existence_ivl_subset[OF iv_in]
    by (auto simp add: compact_Times \<open>compact A\<close>)
  from lipschitz_on_compact[OF this \<open>compact A\<close> \<open>A \<subseteq> X\<close>]
  obtain K' where "\<And>t. t \<in> {t0 .. b} \<Longrightarrow> lipschitz A (f t) K'"
    by metis
  hence K': "\<And>t. t \<in> {t0 .. b} \<Longrightarrow> lipschitz A (f t) (abs K')"
    by (rule nonneg_lipschitz)
  define K where "K = abs K' + 1"
  have "0 < K" "0 \<le> K"
    by (auto simp: K_def)
  have K: "\<And>t. t \<in> {t0 .. b} \<Longrightarrow> lipschitz A (f t) K"
    unfolding K_def
    using \<open>_ \<Longrightarrow> lipschitz A _ K'\<close>
    by (rule pos_lipschitz)

  have [simp]: "x0 \<in> A" using \<open>0 < e\<close> by (auto simp: A_def)


  define d where "d = min e (e * exp (-K * (b - t0)))"
  hence d: "0 < d" "d \<le> e" "d \<le> e * exp (-K * (b - t0))"
    using e by auto

  have d_times_exp_le: "d * exp (K * (t - t0)) \<le> e" if "t0 \<le> t" "t \<le> b" for t
  proof -
    from that have "d * exp (K * (t - t0)) \<le> d * exp (K * (b - t0))"
      using \<open>0 \<le> K\<close> \<open>0 < d\<close>
      by (auto intro!: mult_left_mono)
    also have "d * exp (K * (b - t0)) \<le> e"
      using d by (auto simp: exp_minus divide_simps)
    finally show ?thesis .
  qed
  have "ball x0 d \<subseteq> X" using d \<open>A \<subseteq> X\<close>
    by (auto simp: A_def dist_commute intro!: infdist_le2[where a=x0])
  {
    fix y
    assume y: "y \<in> ball x0 d"
    hence "y \<in> A" using d
      by (auto simp: A_def dist_commute intro!: infdist_le2[where a=x0])
    hence "y \<in> X" using \<open>A \<subseteq> X\<close> by auto
    {
      fix t::real assume t: "t0 \<le> t" "t \<in> existence_ivl t0 y" "t \<le> b"
      have "flow t0 y t \<in> A"
      proof (rule ccontr)
        assume flow_out: "flow t0 y t \<notin> A"
        obtain t' where t':
          "t0 \<le> t'"
          "t' \<le> t"
          "\<And>t. t \<in> {t0 .. t'} \<Longrightarrow> flow t0 x0 t \<in> A"
          "infdist (flow t0 y t') seg \<ge> e"
          "\<And>t. t \<in> {t0 .. t'} \<Longrightarrow> flow t0 y t \<in> A"
        proof -
          let ?out = "((\<lambda>t. infdist (flow t0 y t) seg) -` {e..}) \<inter> {t0..t}"
          have "compact ?out"
            unfolding compact_eq_bounded_closed
          proof safe
            show "bounded ?out" by (auto intro!: bounded_closed_interval)
            have "continuous_on {t0 .. t} ((\<lambda>t. infdist (flow t0 y t) seg))"
              using ivl_subset_existence_ivl t iv_in
              by (auto intro!: continuous_at_imp_continuous_on
                continuous_intros flow_continuous \<open>y \<in> X\<close>)
            thus "closed ?out"
              by (simp add: continuous_on_closed_vimage)
          qed
          moreover
          have "t \<in> (\<lambda>t. infdist (flow t0 y t) seg) -` {e..} \<inter> {t0..t}"
            using flow_out \<open>t0 \<le> t\<close>
            by (auto simp: A_def)
          hence "?out \<noteq> {}"
            by blast
          ultimately have "\<exists>s\<in>?out. \<forall>t\<in>?out. s \<le> t"
            by (rule compact_attains_inf)
          then obtain t' where t':
            "\<And>s. e \<le> infdist (flow t0 y s) seg \<Longrightarrow> t0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> t' \<le> s"
            "e \<le> infdist (flow t0 y t') seg"
            "t0 \<le> t'" "t' \<le> t"
            by (auto simp: vimage_def Ball_def) metis
          have flow_in: "flow t0 x0 s \<in> A" if s: "s \<in> {t0 .. t'}" for s
          proof -
            from s have "s \<in> closed_segment t0 b"
              using \<open>t \<le> b\<close> t' by (auto simp: closed_segment_real)
            then show ?thesis using s \<open>e > 0\<close> by (auto simp: seg_def A_def)
          qed
          have "flow t0 y t' \<in> A" if "t' = t0"
            using y d iv_in that
            by (auto simp:  A_def \<open>y \<in> X\<close> infdist_le2[where a=x0] dist_commute)
          moreover
          have left_of_in: "flow t0 y s \<in> A" if s: "s \<in> {t0 ..< t'}" for s
          proof -
            from s have "s \<in> closed_segment t0 b"
              using \<open>t \<le> b\<close> t' by (auto simp: closed_segment_real)
            from t'(1)[of s]
            have "t' > s \<Longrightarrow> t0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> e > infdist (flow t0 y s) seg"
              by force
            then show ?thesis
              using s t' \<open>e > 0\<close> by (auto simp: seg_def A_def)
          qed
          moreover
          have "closed A" using \<open>compact A\<close> by (auto simp: compact_eq_bounded_closed)
          have "((\<lambda>s. flow t0 y s) \<longlongrightarrow> flow t0 y t') (at_left t')"
            using ivl_subset_existence_ivl[OF \<open>t0 \<in> T\<close> \<open>y \<in> X\<close> t(2)] t' \<open>y \<in> X\<close> iv_in
            by (intro flow_tendsto) (auto intro!: tendsto_intros)
          with \<open>closed A\<close> _ _ have "t' \<noteq> t0 \<Longrightarrow> flow t0 y t' \<in> A"
          proof (rule Lim_in_closed_set)
            assume "t' \<noteq> t0"
            hence "t' > t0" using t' by auto
            hence "eventually (\<lambda>x. x \<ge> t0) (at_left t')"
              by (metis eventually_at_left less_imp_le)
            thus "eventually (\<lambda>x. flow t0 y x \<in> A) (at_left t')"
              unfolding eventually_at_filter
              by eventually_elim (auto intro!: left_of_in)
          qed simp
          ultimately have flow_y_in: "s \<in> {t0 .. t'} \<Longrightarrow> flow t0 y s \<in> A" for s
            by (cases "s = t'") auto
          have
            "t0 \<le> t'"
            "t' \<le> t"
            "\<And>t. t \<in> {t0 .. t'} \<Longrightarrow> flow t0 x0 t \<in> A"
            "infdist (flow t0 y t') seg \<ge> e"
            "\<And>t. t \<in> {t0 .. t'} \<Longrightarrow> flow t0 y t \<in> A"
            by (auto intro!: flow_in flow_y_in) fact+
          thus ?thesis ..
        qed
        {
          fix s assume s: "s \<in> {t0 .. t'}"
          hence "t0 \<le> s" by simp
          have "s \<le> b"
            using  t t' s b
            using ivl_subset_existence_ivl
            by auto
          hence sx0: "s \<in> existence_ivl t0 x0"
            by (simp add: \<open>t0 \<le> s\<close> mem_existence_ivlI)
          have sy: "s \<in> existence_ivl t0 y"
            by (meson \<open>y \<in> X\<close> atLeastAtMost_iff contra_subsetD iv_in(1) ivl_subset_existence_ivl
              order_trans s t'(2) t(2))
          have int: "flow t0 y s - flow t0 x0 s =
              y - x0 + (integral {t0 .. s} (\<lambda>t. f t (flow t0 y t)) -
                integral {t0 .. s} (\<lambda>t. f t (flow t0 x0 t)))"
            using iv_in
            unfolding flow_fixed_point[OF \<open>t0 \<le> s\<close> sx0 iv_in]
              flow_fixed_point[OF \<open>t0 \<le> s\<close> sy \<open>t0 \<in> T\<close> \<open>y \<in> X\<close>]
            by (simp add: algebra_simps)
          have "norm (flow t0 y s - flow t0 x0 s) \<le> norm (y - x0) +
            norm (integral {t0 .. s} (\<lambda>t. f t (flow t0 y t)) -
              integral {t0 .. s} (\<lambda>t. f t (flow t0 x0 t)))"
            unfolding int
            by (rule norm_triangle_ineq)
          also
          have "norm (integral {t0 .. s} (\<lambda>t. f t (flow t0 y t)) -
              integral {t0 .. s} (\<lambda>t. f t (flow t0 x0 t))) =
            norm (integral {t0 .. s} (\<lambda>t. f t (flow t0 y t) - f t (flow t0 x0 t)))"
            using ivl_subset_existence_ivl[of t0 x0 s] sx0 ivl_subset_existence_ivl[of t0 y s] sy
            by (subst integral_diff)
               (auto intro!: integrable_continuous_real continuous_at_imp_continuous_on
                f_flow_continuous \<open>y \<in> X\<close> iv_in)
          also have "\<dots> \<le> (integral {t0 .. s} (\<lambda>t. norm (f t (flow t0 y t) - f t (flow t0 x0 t))))"
            using ivl_subset_existence_ivl[OF _ _ sx0] ivl_subset_existence_ivl[OF _ _ sy]
            by (intro integral_norm_bound_integral)
               (auto intro!: integrable_continuous_real continuous_at_imp_continuous_on
                continuous_intros f_flow_continuous \<open>y \<in> X\<close> iv_in)
          also have "\<dots> \<le> (integral {t0 .. s} (\<lambda>t. K * norm ((flow t0 y t) - (flow t0 x0 t))))"
            using ivl_subset_existence_ivl[OF _ _ sx0] ivl_subset_existence_ivl[OF _ _ sy]
            s t'(3,5) \<open>s \<le> b\<close>
            by (auto simp del: integral_mult_right intro!: integral_le integrable_continuous_real
              continuous_at_imp_continuous_on lipschitz_norm_leI[OF K]
              continuous_intros f_flow_continuous flow_continuous \<open>y \<in> X\<close> iv_in)
          also have "\<dots> = K * integral {t0 .. s} (\<lambda>t. norm (flow t0 y t - flow t0 x0 t))"
            using ivl_subset_existence_ivl[OF _ _ sx0] ivl_subset_existence_ivl[OF _ _ sy]
            by (subst integral_mult)
               (auto intro!: integrable_continuous_real continuous_at_imp_continuous_on
                 lipschitz_norm_leI[OF K] continuous_intros f_flow_continuous
                 flow_continuous \<open>y \<in> X\<close> iv_in)
          finally
          have norm: "norm (flow t0 y s - flow t0 x0 s) \<le>
            norm (y - x0) + K * integral {t0 .. s} (\<lambda>t. norm (flow t0 y t - flow t0 x0 t))"
            by arith
          note norm \<open>s \<le> b\<close> sx0 sy
        } note norm_le = this
        from norm_le(2) t' have "t' \<in> closed_segment t0 b"
          by (auto simp: closed_segment_real)
        hence "infdist (flow t0 y t') seg \<le> dist (flow t0 y t') (flow t0 x0 t')"
          by (auto simp: seg_def infdist_le)
        also have "\<dots> \<le> norm (flow t0 y t' - flow t0 x0 t')"
          by (simp add: dist_norm)
        also have "\<dots> \<le> norm (y - x0) * exp (K * \<bar>t' - t0\<bar>)"
          unfolding K_def
          apply (rule exponential_initial_condition[OF \<open>t0 \<in> T\<close> _ _ _ _ _ _ _ K'])
          subgoal by (metis atLeastAtMost_iff local.norm_le(4) order_refl t'(1))
          subgoal by (metis \<open>y \<in> A\<close>)
          subgoal by (metis atLeastAtMost_iff local.norm_le(3) order_refl t'(1))
          subgoal using e by (simp add: A_def)
          subgoal by fact
          subgoal by (metis closed_segment_real t'(1,5))
          subgoal by (metis closed_segment_real t'(1,3))
          subgoal by (simp add: closed_segment_real local.norm_le(2) t'(1))
          done
        also have "\<dots> < d * exp (K * (t - t0))"
          using y d t' t
          by (intro mult_less_le_imp_less)
             (auto simp: dist_norm[symmetric] dist_commute intro!: mult_mono \<open>0 \<le> K\<close>)
        also have "\<dots> \<le> e"
          by (rule d_times_exp_le; fact)
        finally
        have "infdist (flow t0 y t') seg < e" .
        with \<open>infdist (flow t0 y t') seg \<ge> e\<close> show False
          by (auto simp: frontier_def)
      qed
    } note in_A = this

    have b_in: "b \<in> existence_ivl t0 y"
    proof (rule ccontr)
      assume "b \<notin> existence_ivl t0 y"
      hence disj: "b \<le> inf_existence t0 y \<or> sup_existence t0 y \<le> b"
        by (auto simp: existence_ivl_def ereal_infinity_cases
            ereal_less_real_iff not_le real_less_ereal_iff real_image_ereal_ivl
          split: if_split_asm)
      from existence_ivl_initial_time[OF \<open>t0 \<in> T\<close> \<open>y \<in> X\<close>]
      have "t0 \<le> sup_existence t0 y"
        using ereal_le_real_iff
        by (force simp add: real_image_ereal_ivl existence_ivl_def
          split: if_split_asm)
      with existence_ivl_initial_time[OF \<open>t0 \<in> T\<close> \<open>y \<in> X\<close>] \<open>t0 \<le> b\<close> disj
      have sup_le: "sup_existence t0 y \<le> b"
        by (meson \<open>y \<in> X\<close> ereal_less_eq(3) initial_time_bounds(1) iv_in(1) not_le order_trans)
      {
        fix t::real assume t: "t0 \<le> t" "t \<in> existence_ivl t0 y"
        hence "t < b"
          using sup_le
          by (auto simp: existence_ivl_def real_less_ereal_iff)
            (metis less_ereal.simps(1) less_le_trans)
        note in_A[OF t less_imp_le[OF this]]
      } note in_A = this
      have "sup_existence t0 y < \<infinity>" "real_of_ereal (sup_existence t0 y) \<in> T"
        subgoal
          using \<open>ereal t0 \<le> sup_existence t0 y\<close> ereal_le_real_iff sup_le
          by (force intro!: mem_existence_ivl_subset[OF iv_in] intro: mem_existence_ivlI)
        subgoal
          using \<open>ereal t0 \<le> sup_existence t0 y\<close> \<open>{t0..b} \<subseteq> T\<close> ereal_le_real_iff real_le_ereal_iff sup_le
          by fastforce
        done
      from flow_leaves_compact_ivl[OF \<open>t0 \<in> T\<close> \<open>y \<in> X\<close> this \<open>compact A\<close> \<open>A \<subseteq> X\<close>]
      obtain t where t: "t0 \<le> t" "t \<in> existence_ivl t0 y" "flow t0 y t \<notin> A" by auto
      from in_A[OF t(1,2)] t(3)
      show False
        by simp
    qed
    {
      fix t assume t: "t \<in> {t0 .. b}"
      also note ivl_subset_existence_ivl[OF \<open>t0 \<in> T\<close> \<open>y \<in> X\<close> b_in]
      finally have t_in: "t \<in> existence_ivl t0 y" .

      note t
      also note ivl_subset_existence_ivl[OF iv_in assms(2)]
      finally have t_in': "t \<in> existence_ivl t0 x0" .
      have "norm (flow t0 y t - flow t0 x0 t) \<le> norm (y - x0) * exp (K * \<bar>t - t0\<bar>)"
        unfolding K_def
        using t ivl_subset_existence_ivl[OF \<open>t0 \<in> T\<close> \<open>y \<in> X\<close> b_in] \<open>0 < e\<close>
        by (intro in_A exponential_initial_condition[OF \<open>t0 \<in> T\<close> t_in \<open>y \<in> A\<close> t_in' \<open>x0 \<in> A\<close> \<open>A \<subseteq> X\<close> _ _ K'])
          (auto simp: closed_segment_real A_def seg_def)
      hence "dist (flow t0 x0 t) (flow t0 y t) \<le> dist x0 y * exp (K * \<bar>t - t0\<bar>)"
        by (auto simp: dist_norm[symmetric] dist_commute)
    }
    note b_in this
  } note * = \<open>d > 0\<close> \<open>K > 0\<close> \<open>ball x0 d \<subseteq> X\<close> this
  moreover
  {
    fix e::real assume "0 < e"
    have "eventually (\<lambda>y. y \<in> ball x0 d) (at x0)"
      using \<open>d > 0\<close>
      by (rule eventually_at_in_ball)
    hence "eventually (\<lambda>y. \<forall>t\<in>{t0..b}. dist (flow t0 x0 t) (flow t0 y t) \<le> dist x0 y * exp (K * \<bar>t - t0\<bar>)) (at x0)"
      by eventually_elim (safe intro!: *)
    moreover
    have "eventually (\<lambda>y. \<forall>t\<in>{t0..b}. dist x0 y * exp (K * \<bar>t - t0\<bar>) \<le> dist x0 y * exp (K * (b - t0))) (at x0)"
      using \<open>t0 \<le> b\<close> \<open>0 < K\<close>
      by (auto intro!: mult_left_mono always_eventually)
    moreover
    have "eventually (\<lambda>y. dist x0 y * exp (K * (b - t0)) < e) (at x0)"
      using \<open>0 < e\<close> by (auto intro!: order_tendstoD tendsto_eq_intros)
    ultimately
    have "eventually (\<lambda>y. \<forall>t\<in>{t0..b}. dist (flow t0 x0 t) (flow t0 y t) < e) (at x0)"
      by eventually_elim force
  }
  ultimately show ?thesis ..
qed

lemma
  global_left_existence_interval:
  assumes "b \<le> t0"
  assumes b: "b \<in> existence_ivl t0 x0"
  assumes iv_in: "t0 \<in> T" "x0 \<in> X"
  obtains d K where "d > 0" "K > 0"
    "ball x0 d \<subseteq> X"
    "\<And>y. y \<in> ball x0 d \<Longrightarrow> b \<in> existence_ivl t0 y"
    "\<And>t y. y \<in> ball x0 d \<Longrightarrow> t \<in> {b .. t0} \<Longrightarrow> dist (flow t0 x0 t) (flow t0 y t) \<le> dist x0 y * exp (K * abs (t - t0))"
    "\<And>e. e > 0 \<Longrightarrow> eventually (\<lambda>y. \<forall>t \<in> {b .. t0}. dist (flow t0 x0 t) (flow t0 y t) < e) (at x0)"
proof -
  let ?mirror = "\<lambda>t. 2 * t0 - t"
  have t0': "t0 \<in> ?mirror ` T" using iv_in by auto
  interpret rev: ll_on_open "(\<lambda>t. - f (?mirror t))" "?mirror ` T" ..
  from assms have "2 * t0 - b \<ge> t0" "2 * t0 - b \<in> rev.existence_ivl t0 x0"
    by (auto simp: flow_eq_rev)
  from rev.global_right_existence_interval[OF this t0' \<open>x0 \<in> X\<close>]
  obtain d K where dK: "d > 0" "K > 0"
    "ball x0 d \<subseteq> X"
    "\<And>y. y \<in> ball x0 d \<Longrightarrow> 2 * t0 - b \<in> rev.existence_ivl t0 y"
    "\<And>t y. y \<in> ball x0 d \<Longrightarrow> t \<in> {t0 .. 2 * t0 - b} \<Longrightarrow> dist (rev.flow t0 x0 t) (rev.flow t0 y t) \<le> dist x0 y * exp (K * abs (t - t0))"
    "\<And>e. e > 0 \<Longrightarrow> eventually (\<lambda>y. \<forall>t \<in> {t0 .. 2 * t0 - b}. dist (rev.flow t0 x0 t) (rev.flow t0 y t) < e) (at x0)"
    by (auto simp: rev_flow_eq \<open>x0 \<in> X\<close>)
  from dK(3,4) have "\<And>y. y \<in> ball x0 d \<Longrightarrow> ?mirror (?mirror b) \<in> existence_ivl t0 y"
    by (subst rev_existence_ivl_eq[symmetric]) (auto simp: iv_in)
  then have 4: "\<And>y. y \<in> ball x0 d \<Longrightarrow> b \<in> existence_ivl t0 y" by simp
  have 5: "dist (flow t0 x0 t) (flow t0 y t) \<le> dist x0 y * exp (K * abs (t - t0))"
    if yt: "y \<in> ball x0 d" "t \<in> {b .. t0}" for t y
  proof -
    from dK(3) yt have yx0: "y \<in> X" "x0 \<in> ball x0 d" using \<open>d > 0\<close> by auto
    from yt yx0 rev.closed_segment_subset_existence_ivl[OF t0' _ dK(4)[OF yt(1)]]
    have "2 * t0 - t \<in> rev.existence_ivl t0 y"
      by (auto simp: closed_segment_real)
    moreover
    from yt \<open>x0 \<in> X\<close> rev.closed_segment_subset_existence_ivl[OF t0' _ dK(4)[OF \<open>x0 \<in> ball x0 d\<close>]]
    have "2 * t0 - t \<in> rev.existence_ivl t0 x0"
      by (auto simp: closed_segment_real)
    ultimately
    show ?thesis
      using yt dK(5)[of y "2 * t0 - t"] rev_flow_eq[OF iv_in, of "2 * t0 - t"]
        rev_flow_eq[OF \<open>t0 \<in> T\<close> \<open>y \<in> X\<close>, of "2 * t0 - t"]
      by (auto simp: dist_commute closed_segment_real)
  qed
  have 6: "eventually (\<lambda>y. \<forall>t\<in>{b .. t0}. dist (flow t0 x0 t) (flow t0 y t) < e) (at x0)"
    if "0 < e" for e :: real
  proof -
    have "eventually (\<lambda>y. y \<in> ball x0 d) (at x0)"
      using \<open>d > 0\<close> by (rule eventually_at_in_ball)
    hence "eventually (\<lambda>y. \<forall>t\<in>{t0..2 * t0 - b}. dist (rev.flow t0 x0 t) (rev.flow t0 y t)
        = dist (flow t0 x0 (2 * t0 - t)) (flow t0 y (2 * t0 - t))) (at x0)"
    proof eventually_elim
      case (elim y)
      hence "y \<in> X" "2 * t0 -b \<in> rev.existence_ivl t0 y" using dK by auto
      from rev.closed_segment_subset_existence_ivl[OF t0' this]
        rev.closed_segment_subset_existence_ivl[OF t0' \<open>x0 \<in> X\<close> \<open>2 * t0 - b \<in> rev.existence_ivl t0 x0\<close>]
      show ?case
        by (force simp: iv_in \<open>y \<in> X\<close> closed_segment_real rev_flow_eq)
    qed
    moreover
    note dK(6)[OF \<open>0 < e\<close>]
    ultimately
    show ?thesis
      by eventually_elim (auto simp: dest: bspec[where x="2 * t0 - t" for t])
  qed
  from dK(1-3) 4 5 6 show ?thesis ..
qed

lemma
  global_existence_interval:
  assumes a: "a \<in> existence_ivl t0 x0"
  assumes b: "b \<in> existence_ivl t0 x0"
  assumes le: "a \<le> b"
  assumes iv_in: "t0 \<in> T" "x0 \<in> X"
  obtains d K where "d > 0" "K > 0"
    "ball x0 d \<subseteq> X"
    "\<And>y. y \<in> ball x0 d \<Longrightarrow> a \<in> existence_ivl t0 y"
    "\<And>y. y \<in> ball x0 d \<Longrightarrow> b \<in> existence_ivl t0 y"
    "\<And>t y. y \<in> ball x0 d \<Longrightarrow> t \<in> {a .. b} \<Longrightarrow>
      dist (flow t0 x0 t) (flow t0 y t) \<le> dist x0 y * exp (K * abs (t - t0))"
    "\<And>e. e > 0 \<Longrightarrow>
      eventually (\<lambda>y. \<forall>t \<in> {a .. b}. dist (flow t0 x0 t) (flow t0 y t) < e) (at x0)"
proof -
  define r where "r = Max {t0, a, b}"
  define l where "l = Min {t0, a, b}"
  have r: "r \<ge> t0" "r \<in> existence_ivl t0 x0"
    using a b by (auto simp: max_def iv_in r_def)
  obtain dr Kr where right:
    "0 < dr" "0 < Kr" "ball x0 dr \<subseteq> X"
    "\<And>y. y \<in> ball x0 dr \<Longrightarrow> r \<in> existence_ivl t0 y"
    "\<And>y t. y \<in> ball x0 dr \<Longrightarrow> t \<in> {t0..r} \<Longrightarrow> dist (flow t0 x0 t) (flow t0 y t) \<le> dist x0 y * exp (Kr * \<bar>t - t0\<bar>)"
    "\<And>e. 0 < e \<Longrightarrow> \<forall>\<^sub>F y in at x0. \<forall>t\<in>{t0..r}. dist (flow t0 x0 t) (flow t0 y t) < e"
    by (rule global_right_existence_interval[OF r iv_in]) blast

  have l: "l \<le> t0" "l \<in> existence_ivl t0 x0"
    using a b by (auto simp: min_def iv_in l_def)
  obtain dl Kl where left:
    "0 < dl" "0 < Kl" "ball x0 dl \<subseteq> X"
    "\<And>y. y \<in> ball x0 dl \<Longrightarrow> l \<in> existence_ivl t0 y"
    "\<And>y t. y \<in> ball x0 dl \<Longrightarrow> t \<in> {l .. t0} \<Longrightarrow> dist (flow t0 x0 t) (flow t0 y t) \<le> dist x0 y * exp (Kl * \<bar>t - t0\<bar>)"
    "\<And>e. 0 < e \<Longrightarrow> \<forall>\<^sub>F y in at x0. \<forall>t\<in>{l .. t0}. dist (flow t0 x0 t) (flow t0 y t) < e"
    by (rule global_left_existence_interval[OF l iv_in]) blast

  define d where "d = min dr dl"
  define K where "K = max Kr Kl"

  have "0 < d" "0 < K" "ball x0 d \<subseteq> X"
    using left right by (auto simp: d_def K_def)
  moreover
  {
    fix y assume y: "y \<in> ball x0 d"
    hence "y \<in> X" using \<open>ball x0 d \<subseteq> X\<close> by auto
    from y
      ivl_subset_existence_ivl'[OF \<open>t0 \<in> T\<close> this left(4)]
      ivl_subset_existence_ivl[OF \<open>t0 \<in> T\<close> this right(4)]
    have "a \<in> existence_ivl t0 y" "b \<in> existence_ivl t0 y"
      by (auto simp: d_def l_def r_def min_def max_def split: if_split_asm)
  }
  moreover
  {
    fix t y
    assume y: "y \<in> ball x0 d"
      and t: "t \<in> {a .. b}"
    from y have "y \<in> X" using \<open>ball x0 d \<subseteq> X\<close> by auto
    have "dist (flow t0 x0 t) (flow t0 y t) \<le> dist x0 y * exp (K * abs (t - t0))"
    proof cases
      assume "t \<ge> t0"
      hence "dist (flow t0 x0 t) (flow t0 y t) \<le> dist x0 y * exp (Kr * abs (t - t0))"
        using y t
        by (intro right) (auto simp: d_def r_def)
      also have "exp (Kr * abs (t - t0)) \<le> exp (K * abs (t - t0))"
        by (auto simp: mult_left_mono K_def max_def mult_right_mono)
      finally show ?thesis by (simp add: mult_left_mono)
    next
      assume "\<not>t \<ge> t0"
      hence "dist (flow t0 x0 t) (flow t0 y t) \<le> dist x0 y * exp (Kl * abs (t - t0))"
        using y t
        by (intro left) (auto simp: d_def l_def)
      also have "exp (Kl * abs (t - t0)) \<le> exp (K * abs (t - t0))"
        by (auto simp: mult_left_mono K_def max_def mult_right_mono)
      finally show ?thesis by (simp add: mult_left_mono)
    qed
  } moreover {
    fix e::real assume "0 < e"
    from left(6)[OF \<open>0 < e\<close>] right(6)[OF \<open>0 < e\<close>]
    have "eventually (\<lambda>y. \<forall>t \<in> {a .. b}. dist (flow t0 x0 t) (flow t0 y t) < e) (at x0)"
      by eventually_elim (auto simp: l_def r_def min_def max_def)
  } ultimately show ?thesis ..
qed

lemma
  assumes t0: "t0 \<in> T"
  shows open_state_space: "open (Sigma X (existence_ivl t0))"
  and flow_continuous_on_state_space:
    "continuous_on (Sigma X (existence_ivl t0)) (\<lambda>(x, t). flow t0 x t)"
proof (safe intro!: topological_space_class.openI continuous_at_imp_continuous_on)
  fix t x assume "x \<in> X" and t: "t \<in> existence_ivl t0 x"
  with open_existence_ivl
  obtain e where e: "e > 0" "cball t e \<subseteq> existence_ivl t0 x"
    by (metis open_contains_cball)
  hence ivl: "t - e \<in> existence_ivl t0 x" "t + e \<in> existence_ivl t0 x" "t - e \<le> t + e"
    by (auto simp: cball_def dist_real_def)
  obtain d K where dK:
    "0 < d" "0 < K" "ball x d \<subseteq> X"
    "\<And>y. y \<in> ball x d \<Longrightarrow> t - e \<in> existence_ivl t0 y"
    "\<And>y. y \<in> ball x d \<Longrightarrow> t + e \<in> existence_ivl t0 y"
    "\<And>y s. y \<in> ball x d \<Longrightarrow> s \<in> {t - e..t + e} \<Longrightarrow>
      dist (flow t0 x s) (flow t0 y s) \<le> dist x y * exp (K * \<bar>s - t0\<bar>)"
    "\<And>eps. 0 < eps \<Longrightarrow>
      \<forall>\<^sub>F y in at x. \<forall>t\<in>{t - e..t + e}. dist (flow t0 x t) (flow t0 y t) < eps"
    by (rule global_existence_interval[OF ivl t0 \<open>x \<in> X\<close>]) blast
  let ?T = "ball x d \<times> ball t e"
  have "open ?T" by (auto intro!: open_Times)
  moreover have "(x, t) \<in> ?T" by (auto simp: dK \<open>0 < e\<close>)
  moreover have "?T \<subseteq> Sigma X (existence_ivl t0)"
  proof safe
    fix s y assume y: "y \<in> ball x d" and s: "s \<in> ball t e"
    with \<open>ball x d \<subseteq> X\<close> show "y \<in> X" by auto
    have "ball t e \<subseteq> closed_segment t0 (t - e) \<union> closed_segment t0 (t + e)"
      by (auto simp: closed_segment_real dist_real_def)
    with \<open>y \<in> X\<close> s closed_segment_subset_existence_ivl[OF t0 _ dK(4)[OF y]]
      closed_segment_subset_existence_ivl[OF t0 _ dK(5)[OF y]]
    show "s \<in> existence_ivl t0 y"
      by auto
  qed
  ultimately show "\<exists>T. open T \<and> (x, t) \<in> T \<and> T \<subseteq> Sigma X (existence_ivl t0)"
    by blast
  have **: "\<forall>\<^sub>F s in at 0. norm (flow t0 (x + fst s) (t + snd s) - flow t0 x t) < 2 * eps"
    if "eps > 0" for eps :: real
  proof -
    have " \<forall>\<^sub>F s in at 0. norm (flow t0 (x + fst s) (t + snd s) - flow t0 x t) =
      norm (flow t0 (x + fst s) (t + snd s) - flow t0 x (t + snd s) +
        (flow t0 x (t + snd s) - flow t0 x t))"
      by auto
    moreover
    have "\<forall>\<^sub>F s in at 0.
        norm (flow t0 (x + fst s) (t + snd s) - flow t0 x (t + snd s) +
          (flow t0 x (t + snd s) - flow t0 x t)) \<le>
        norm (flow t0 (x + fst s) (t + snd s) - flow t0 x (t + snd s)) +
          norm (flow t0 x (t + snd s) - flow t0 x t)"
      by eventually_elim (rule norm_triangle_ineq)
    moreover
    have "\<forall>\<^sub>F s in at 0. t + snd s \<in> ball t e"
      by (auto simp: dist_real_def intro!: order_tendstoD[OF _ \<open>0 < e\<close>]
        intro!: tendsto_eq_intros)
    moreover from dK(7)[OF \<open>eps > 0\<close>]
    have "\<forall>\<^sub>F h in at (fst (0::'a*real)).
        \<forall>t\<in>{t - e..t + e}. dist (flow t0 x t) (flow t0 (x + h) t) < eps"
      by (subst (asm) eventually_at_shift_zero[symmetric]) simp
    hence "\<forall>\<^sub>F (h::(_ * real)) in at 0.
      \<forall>t\<in>{t - e..t + e}. dist (flow t0 x t) (flow t0 (x + fst h) t) < eps"
      by (rule eventually_at_fst) (simp add: \<open>eps > 0\<close>)
    moreover
    have "\<forall>\<^sub>F h in at (snd (0::'a * _)). norm (flow t0 x (t + h) - flow t0 x t) < eps"
      using flow_continuous[OF t0 \<open>x \<in> X\<close> t, unfolded isCont_def, THEN tendstoD, OF \<open>eps > 0\<close>]
      by (subst (asm) eventually_at_shift_zero[symmetric]) (auto simp: dist_norm)
    hence "\<forall>\<^sub>F h::('a * _) in at 0. norm (flow t0 x (t + snd h) - flow t0 x t) < eps"
      by (rule eventually_at_snd) (simp add: \<open>eps > 0\<close>)
    ultimately
    show ?thesis
    proof eventually_elim
      case (elim s)
      note elim(1)
      also note elim(2)
      also note elim(5)
      also
      from elim(3) have "t + snd s \<in> {t - e..t + e}"
        by (auto simp: dist_real_def algebra_simps)
      from elim(4)[rule_format, OF this]
      have "norm (flow t0 (x + fst s) (t + snd s) - flow t0 x (t + snd s)) < eps"
        by (auto simp: dist_commute dist_norm[symmetric])
      finally
      show ?case by simp
    qed
  qed
  have *: "\<forall>\<^sub>F s in at 0. norm (flow t0 (x + fst s) (t + snd s) - flow t0 x t) < eps"
    if "eps > 0" for eps::real
  proof -
    from that have "eps / 2 > 0" by simp
    from **[OF this] show ?thesis by auto
  qed
  show "isCont (\<lambda>(x, y). flow t0 x y) (x, t)"
    unfolding isCont_iff
    by (rule LIM_zero_cancel)
      (auto simp: split_beta' norm_conv_dist[symmetric] intro!: tendstoI *)
qed

lemma flow_isCont_state_space: "t0 \<in> T \<Longrightarrow> x \<in> X \<Longrightarrow> t \<in> existence_ivl t0 x \<Longrightarrow> isCont (\<lambda>(x, t). flow t0 x t) (x, t)"
  using flow_continuous_on_state_space
  by (auto simp: continuous_on_eq_continuous_within at_within_open[OF _ open_state_space])

lemma
  flow_absolutely_integrable_on[integrable_on_simps]:
  assumes "t0 \<in> T" "x0 \<in> X"
  assumes "s \<in> existence_ivl t0 x0"
  shows "(\<lambda>x. norm (flow t0 x0 x)) integrable_on closed_segment t0 s"
  using assms
  by (auto simp: closed_segment_real intro!: integrable_continuous_real continuous_intros
    flow_continuous_on_intro
    intro: in_existence_between_zeroI)

lemma existence_ivl_eq_domain:
  assumes iv_in: "t0 \<in> T" "x0 \<in> X"
  assumes bnd: "\<And>tm tM t x. tm \<in> T \<Longrightarrow> tM \<in> T \<Longrightarrow> \<exists>M. \<exists>L. \<forall>t \<in> {tm .. tM}. \<forall>x \<in> X. norm (f t x) \<le> M + L * norm x"
  assumes "is_interval T" "X = UNIV"
  shows "existence_ivl t0 x0 = T"
proof -
  from assms have XI: "x \<in> X" for x by auto
  {
    fix tm tM assume tm: "tm \<in> T" and tM: "tM \<in> T" and tmtM: "tm \<le> t0" "t0 \<le> tM"
    from bnd[OF tm tM] obtain M' L'
    where bnd': "\<And>x t. x \<in> X \<Longrightarrow> tm \<le> t \<Longrightarrow> t \<le> tM \<Longrightarrow> norm (f t x) \<le> M' + L' * norm x"
      by force
    define M where "M = norm M' + 1"
    define L where "L = norm L' + 1"
    have bnd: "\<And>x t. x \<in> X \<Longrightarrow> tm \<le> t \<Longrightarrow> t \<le> tM \<Longrightarrow> norm (f t x) \<le> M + L * norm x"
      by (auto simp: M_def L_def intro!: bnd'[THEN order_trans] add_mono mult_mono)
    have "M > 0" "L > 0" by (auto simp: L_def M_def)

    let ?r = "(norm x0 + \<bar>tm - tM\<bar> * M + 1) * exp (L * \<bar>tm - tM\<bar>)"
    define K where "K = cball (0::'a) ?r"
    have K: "compact K" "K \<subseteq> X"
      by (auto simp: K_def \<open>X = UNIV\<close>)
    have flow_compact: "flow t0 x0 t \<in> K"
      if t: "t \<in> existence_ivl t0 x0"  and le: "tm \<le> t" "t \<le> tM" for t
    proof -
      have "norm (flow t0 x0 s) \<le> norm x0 + norm (t0 - t) * M + 1 +
            L * integral (closed_segment t0 s) (\<lambda>t. norm (flow t0 x0 t))"
        if sc: "s \<in> closed_segment t0 t" for s
      proof -
        from sc have s: "s \<in> existence_ivl t0 x0" and le: "tm \<le> s" "s \<le> tM"
          using t le sc
          using closed_segment_subset_existence_ivl iv_in(1) iv_in(2)
          apply -
          subgoal by force
          subgoal by (metis (full_types) atLeastAtMost_iff closed_segment_eq_real_ivl order_trans tmtM(1))
          subgoal by (metis (full_types) atLeastAtMost_iff closed_segment_eq_real_ivl order_trans tmtM(2))
          done
        from sc have nle: "norm (t0 - s) \<le> norm (t0 - t)" by (auto simp: closed_segment_real split: if_split_asm)
        from flow_fixed_point''[OF s iv_in]
        have "norm (flow t0 x0 s) \<le> norm x0 + integral (closed_segment t0 s) (\<lambda>t. M + L * norm (flow t0 x0 t))"
          using tmtM
          using closed_segment_subset_existence_ivl[OF iv_in s] le
          by (auto simp: closed_segment_real
            intro!: norm_triangle_le norm_triangle_ineq4[THEN order.trans]
              integral_norm_bound_integral bnd
              integrable_continuous_closed_segment
              integrable_continuous_real
              continuous_intros
              continuous_on_subset[OF flow_continuous_on]
              iv_in flow_in_domain
              mem_existence_ivl_subset[OF iv_in(1) XI])
        also have "\<dots> = norm x0 + norm (t0 - s) * M + L * integral (closed_segment t0 s) (\<lambda>t. norm (flow t0 x0 t))"
          by (simp add: integral_add integrable_on_simps iv_in \<open>s \<in> existence_ivl _ _\<close>
            integral_const_closed_segment abs_minus_commute)
        also have "norm (t0 - s) * M \<le> norm (t0 - t) * M "
          using nle \<open>M > 0\<close> by auto
        also have "\<dots> \<le> \<dots> + 1" by simp
        finally show ?thesis by simp
      qed
      then have "norm (flow t0 x0 t) \<le> (norm x0 + norm (t0 - t) * M + 1) * exp (L * \<bar>t - t0\<bar>)"
        using closed_segment_subset_existence_ivl[OF iv_in t]
        by (intro gronwall_more_general_segment[where a=t0 and b = t and t = t])
          (auto simp: \<open>0 < L\<close> \<open>0 < M\<close> less_imp_le
            intro!: add_nonneg_pos mult_nonneg_nonneg add_nonneg_nonneg continuous_intros
              flow_continuous_on_intro iv_in)
      also have "\<dots> \<le> ?r"
        using le tmtM
        by (auto simp: less_imp_le \<open>0 < M\<close> \<open>0 < L\<close> abs_minus_commute intro!: mult_mono)
      finally show ?thesis
       by (simp add: dist_norm K_def)
    qed

    have "{tm..tM} \<subseteq> existence_ivl t0 x0"
      using tmtM tm \<open>x0 \<in> X\<close> \<open>compact K\<close> \<open>K \<subseteq> X\<close> mem_is_intervalI[OF \<open>is_interval T\<close> \<open>tm \<in> T\<close> \<open>tM \<in> T\<close>]
      by (intro subset_mem_compact_implies_subset_existence_interval[OF _ _ _ _flow_compact])
         (auto simp: tmtM is_interval_closed_interval)
    then have "inf_existence t0 x0 < tm \<and> tM < sup_existence t0 x0"
      using tmtM
      by (cases "inf_existence t0 x0"; cases "sup_existence t0 x0")
        (auto simp: existence_ivl_def real_image_ereal_ivl subset_iff split: if_split_asm)
  } note bnds = this[THEN conjunct2] this[THEN conjunct1]

  show "existence_ivl t0 x0 = T"
  proof safe
    fix x assume x: "x \<in> T"
    have "inf_existence t0 x0 < x"
      apply (cases "x \<le> t0")
      subgoal by (rule bnds[OF x iv_in(1)]) simp_all
      subgoal by (meson XI ereal_less_eq(3) initial_time_bounds(1) iv_in(1) le_cases not_less order_trans) 
      done
    moreover have "x < sup_existence t0 x0"
      apply (cases "x \<ge> t0")
      subgoal by (rule bnds[OF iv_in(1) x]) simp_all
      subgoal by (meson XI dual_order.strict_trans ereal_less_eq(3) initial_time_bounds(2) iv_in(1) not_less)
      done
    ultimately show "x \<in> existence_ivl t0 x0"
      by (cases "inf_existence t0 x0"; cases "sup_existence t0 x0")
        (auto simp: existence_ivl_def real_atLeastGreaterThan_eq)
  qed (insert existence_ivl_subset[OF iv_in], fastforce)
qed

lemma flow_unique:
  assumes iv_in: "t0 \<in> T" "x0 \<in> X"
  assumes "t \<in> existence_ivl t0 x0"
  assumes "phi t0 = x0"
  assumes "\<And>t. t \<in> existence_ivl t0 x0 \<Longrightarrow> (phi has_vector_derivative f t (phi t)) (at t)"
  assumes "\<And>t. t \<in> existence_ivl t0 x0 \<Longrightarrow> phi t \<in> X"
  shows "flow t0 x0 t = phi t"
proof -
  interpret u: unique_solution "existence_ivp t0 x0"
    using iv_in by (rule existence_ivp)
  have "t \<in> u.T" using assms by auto
  show ?thesis
    unfolding flow_def
    apply (rule u.unique_solution[OF _ \<open>t \<in> u.T\<close>, symmetric])
    apply (rule u.is_solutionI)
    subgoal by (force simp add: assms)
    subgoal by (subst at_within_open) (simp_all add: assms)
    subgoal by (simp add: assms)
    done
qed

end \<comment>\<open>@{thm local_lipschitz}\<close>

locale two_ll_on_open =
  F: ll_on_open F T1 X + G: ll_on_open G T2 X
  for F T1 G T2 X J +
  fixes x0 and e::real and K
  assumes x0_in_X: "x0 \<in> X"
  assumes t0_in_T1: "0 \<in> T1"
  assumes t0_in_T2: "0 \<in> T2"
  assumes t0_in_J: "0 \<in> J"
  assumes J_subset: "J \<subseteq> F.existence_ivl 0 x0"
  assumes J_ivl: "is_interval J"
  assumes F_lipschitz: "\<And>t. t \<in> J \<Longrightarrow> lipschitz X (F t) K"
  assumes K_pos: "0 < K"
  assumes F_G_norm_ineq: "\<And>t x. t \<in> J \<Longrightarrow> x \<in> X \<Longrightarrow> norm (F t x - G t x) < e"
begin

lemma e_pos: "0 < e"
  using le_less_trans[OF norm_ge_zero F_G_norm_ineq[OF t0_in_J x0_in_X]]
  by assumption

definition "XX t = F.flow 0 x0 t"
definition "Y t = G.flow 0 x0 t"

lemma norm_X_Y_bound:
shows "\<forall>t \<in> J \<inter> G.existence_ivl 0 x0. norm (XX t - Y t) \<le> e / K * (exp(K * \<bar>t\<bar>) - 1)"
proof(safe)
  fix t assume "t \<in> J"
  assume tG: "t \<in> G.existence_ivl 0 x0"
  have "0 \<in> J" by (simp add: t0_in_J)

  let ?u="\<lambda>t. norm (XX t - Y t)"
  show "norm (XX t - Y t) \<le> e / K * (exp (K * \<bar>t\<bar>) - 1)"
  proof(cases "0 \<le> t")
    assume "0 \<le> t"
    hence [simp]: "\<bar>t\<bar> = t" by simp

    have t0_t_in_J: "{0..t} \<subseteq> J"
      using \<open>t \<in> J\<close> \<open>0 \<in> J\<close> J_ivl
      using G.mem_is_intervalI atLeastAtMost_iff subsetI by blast

    note F_G_flow_cont[continuous_intros] =
      continuous_on_subset[OF F.flow_continuous_on[OF t0_in_T1 x0_in_X]]
      continuous_on_subset[OF G.flow_continuous_on[OF t0_in_T2 x0_in_X]]

    have "?u t + e/K \<le> e/K * exp(K * t)"
    proof(rule gronwall[where g="\<lambda>t. ?u t + e/K", OF _ _ _ _ K_pos \<open>0 \<le> t\<close> order.refl])
      fix s assume "0 \<le> s" "s \<le> t"
      hence "{0..s} \<subseteq> J" using t0_t_in_J by auto

      hence t0_s_in_existence:
        "{0..s} \<subseteq> F.existence_ivl 0 x0"
        "{0..s} \<subseteq> G.existence_ivl 0 x0"
        using J_subset tG \<open>0 \<le> s\<close> \<open>s \<le> t\<close> G.ivl_subset_existence_ivl[OF t0_in_T2 x0_in_X tG]
        by auto

      hence s_in_existence:
        "s \<in> F.existence_ivl 0 x0"
        "s \<in> G.existence_ivl 0 x0"
          using \<open>0 \<le> s\<close> by auto

      note cont_statements[continuous_intros] =
        x0_in_X
        t0_in_T1 t0_in_T2
        F.flow_in_domain[OF t0_in_T1 x0_in_X]
        G.flow_in_domain[OF t0_in_T2 x0_in_X]
        F.mem_existence_ivl_subset[OF t0_in_T1 x0_in_X]
        G.mem_existence_ivl_subset[OF t0_in_T2 x0_in_X]

      have [integrable_on_simps]:
        "continuous_on {0..s} (\<lambda>s. F s (F.flow 0 x0 s))"
        "continuous_on {0..s} (\<lambda>s. G s (G.flow 0 x0 s))"
        "continuous_on {0..s} (\<lambda>s. F s (G.flow 0 x0 s))"
        "continuous_on {0..s} (\<lambda>s. G s (F.flow 0 x0 s))"
        using t0_s_in_existence
        by (auto intro!: continuous_intros integrable_continuous_real)

      have "XX s - Y s = integral {0..s} (\<lambda>s. F s (XX s) - G s (Y s))"
        by (simp add: XX_def Y_def integral_diff integrable_on_simps
               F.flow_fixed_point[OF \<open>0 \<le> s\<close> s_in_existence(1) t0_in_T1 x0_in_X]
               G.flow_fixed_point[OF \<open>0 \<le> s\<close> s_in_existence(2) t0_in_T2 x0_in_X])
      also have "... = integral {0..s} (\<lambda>s. (F s (XX s) - F s (Y s)) + (F s (Y s) - G s (Y s)))"
        by simp
      also have "... = integral {0..s} (\<lambda>s. F s (XX s) - F s (Y s)) + integral {0..s} (\<lambda>s. F s (Y s) - G s (Y s))"
        by (simp add: integral_diff integral_add XX_def Y_def integrable_on_simps)
      finally have "?u s \<le> norm (integral {0..s} (\<lambda>s. F s (XX s) - F s (Y s))) + norm (integral {0..s} (\<lambda>s. F s (Y s) - G s (Y s)))"
        by (simp add: norm_triangle_ineq)
      also have "... \<le> integral {0..s} (\<lambda>s. norm (F s (XX s) - F s (Y s))) + integral {0..s} (\<lambda>s. norm (F s (Y s) - G s (Y s)))"
        using t0_s_in_existence
        by (auto simp add: XX_def Y_def
          intro!: add_mono continuous_intros continuous_on_imp_absolutely_integrable_on)
      also have "... \<le> integral {0..s} (\<lambda>s. K * ?u s) + integral {0..s} (\<lambda>s. e)"
      proof (rule add_mono[OF integral_le integral_le])
        show "\<forall>x\<in>{0..s}. norm (F x (XX x) - F x (Y x)) \<le> K * norm (XX x - Y x)"
          using F_lipschitz[unfolded lipschitz_def, THEN conjunct2]
            cont_statements(1,2,4)
            t0_s_in_existence
          by (metis F_lipschitz XX_def Y_def \<open>{0..s} \<subseteq> J\<close> lipschitz_norm_leI ll_on_open.flow_in_domain subsetCE t0_in_T2 two_ll_on_open_axioms two_ll_on_open_def)
        show "\<forall>x\<in>{0..s}. norm (F x (Y x) - G x (Y x)) \<le> e"
          using F_G_norm_ineq cont_statements(2,3) t0_s_in_existence
          using Y_def \<open>{0..s} \<subseteq> J\<close> cont_statements(5) subset_iff by fastforce
      qed (simp_all add: t0_s_in_existence continuous_intros integrable_on_simps XX_def Y_def)
      also have "... = K * integral {0..s} (\<lambda>s. ?u s + e / K)"
        using K_pos t0_s_in_existence
        by (simp_all add: algebra_simps integral_add XX_def Y_def continuous_intros
          continuous_on_imp_absolutely_integrable_on)
      finally show "?u s + e / K \<le> e / K + K * integral {0..s} (\<lambda>s. ?u s + e / K)"
        by simp
    next
      show "continuous_on {0..t} (\<lambda>t. norm (XX t - Y t) + e / K)"
        using t0_t_in_J J_subset G.ivl_subset_existence_ivl[OF t0_in_T2 x0_in_X tG]
        by (auto simp add: XX_def Y_def intro!: continuous_intros)
    next
      fix s assume "0 \<le> s" "s \<le> t"
      show "0 \<le> norm (XX s - Y s) + e / K"
        using e_pos K_pos by simp
    next
      show "0 < e / K" using e_pos K_pos by simp
    qed
    thus ?thesis by (simp add: algebra_simps)
  next
    assume "\<not>0 \<le> t"
    hence "t \<le> 0" by simp
    hence [simp]: "\<bar>t\<bar> = -t" by simp

    have t0_t_in_J: "{t..0} \<subseteq> J"
      using \<open>t \<in> J\<close> \<open>0 \<in> J\<close> J_ivl \<open>\<not> 0 \<le> t\<close> atMostAtLeast_subset_convex is_interval_convex_1
      by auto

    note F_G_flow_cont[continuous_intros] =
      continuous_on_subset[OF F.flow_continuous_on[OF t0_in_T1 x0_in_X]]
      continuous_on_subset[OF G.flow_continuous_on[OF t0_in_T2 x0_in_X]]

    have "?u t + e/K \<le> e/K * exp(- K * t)"
    proof(rule gronwall_left[where g="\<lambda>t. ?u t + e/K", OF _ _ _ _ K_pos order.refl \<open>t \<le> 0\<close>])
      fix s assume "t \<le> s" "s \<le> 0"
      hence "{s..0} \<subseteq> J" using t0_t_in_J by auto

      hence t0_s_in_existence:
        "{s..0} \<subseteq> F.existence_ivl 0 x0"
        "{s..0} \<subseteq> G.existence_ivl 0 x0"
        using J_subset G.ivl_subset_existence_ivl'[OF t0_in_T2 x0_in_X tG] \<open>s \<le> 0\<close> \<open>t \<le> s\<close>
        by auto

      hence s_in_existence:
        "s \<in> F.existence_ivl 0 x0"
        "s \<in> G.existence_ivl 0 x0"
          using \<open>s \<le> 0\<close> by auto

      note cont_statements[continuous_intros] =
        x0_in_X
        t0_in_T1 t0_in_T2
        F.flow_in_domain[OF t0_in_T1 x0_in_X]
        G.flow_in_domain[OF t0_in_T2 x0_in_X]
        F.mem_existence_ivl_subset[OF t0_in_T1 x0_in_X]
        G.mem_existence_ivl_subset[OF t0_in_T2 x0_in_X]
      then have [continuous_intros]:
        "{s..0} \<subseteq> T1"
        "{s..0} \<subseteq> T2"
        "F.flow 0 x0 ` {s..0} \<subseteq> X"
        "G.flow 0 x0 ` {s..0} \<subseteq> X"
        "s \<le> x \<Longrightarrow> x \<le> 0 \<Longrightarrow> x \<in> F.existence_ivl 0 x0"
        "s \<le> x \<Longrightarrow> x \<le> 0 \<Longrightarrow> x \<in> G.existence_ivl 0 x0" for x
        using t0_s_in_existence
        by (auto simp: )
      have "XX s - Y s = - integral {s..0} (\<lambda>s. F s (XX s) - G s (Y s))"
        using t0_s_in_existence
        by (simp add: XX_def Y_def
               F.flow_fixed_point'[OF \<open>s \<le> 0\<close> s_in_existence(1) t0_in_T1 x0_in_X]
               G.flow_fixed_point'[OF \<open>s \<le> 0\<close> s_in_existence(2) t0_in_T2 x0_in_X]
               continuous_intros integrable_on_simps integral_diff)
      also have "... = - integral {s..0} (\<lambda>s. (F s (XX s) - F s (Y s)) + (F s (Y s) - G s (Y s)))"
        by simp
      also have "... = - (integral {s..0} (\<lambda>s. F s (XX s) - F s (Y s)) + integral {s..0} (\<lambda>s. F s (Y s) - G s (Y s)))"
        using t0_s_in_existence
        by (subst integral_add) (simp_all add: integral_add XX_def Y_def continuous_intros integrable_on_simps)
      finally have "?u s \<le> norm (integral {s..0} (\<lambda>s. F s (XX s) - F s (Y s))) + norm (integral {s..0} (\<lambda>s. F s (Y s) - G s (Y s)))"
        by (metis (no_types, lifting) norm_minus_cancel norm_triangle_ineq)
      also have "... \<le> integral {s..0} (\<lambda>s. norm (F s (XX s) - F s (Y s))) + integral {s..0} (\<lambda>s. norm (F s (Y s) - G s (Y s)))"
        using t0_s_in_existence
        by (auto simp add: XX_def Y_def intro!: continuous_intros continuous_on_imp_absolutely_integrable_on add_mono)
      also have "... \<le> integral {s..0} (\<lambda>s. K * ?u s) + integral {s..0} (\<lambda>s. e)"
      proof (rule add_mono[OF integral_le integral_le])
        show "\<forall>x\<in>{s..0}. norm (F x (XX x) - F x (Y x)) \<le> K * norm (XX x - Y x)"
          by (metis F_lipschitz XX_def Y_def \<open>{s..0} \<subseteq> J\<close> cont_statements(4) cont_statements(5)
            lipschitz_norm_leI subset_iff t0_s_in_existence(1) t0_s_in_existence(2))
        show "\<forall>x\<in>{s..0}. norm (F x (Y x) - G x (Y x)) \<le> e"
          using F_G_norm_ineq Y_def \<open>{s..0} \<subseteq> J\<close> cont_statements(5) subset_iff t0_s_in_existence(2)
          by fastforce
      qed (simp_all add: t0_s_in_existence continuous_intros integrable_on_simps XX_def Y_def)
      also have "... = K * integral {s..0} (\<lambda>s. ?u s + e / K)"
        using K_pos t0_s_in_existence
        by (simp_all add: algebra_simps integral_add t0_s_in_existence continuous_intros integrable_on_simps XX_def Y_def)
      finally show "?u s + e / K \<le> e / K + K * integral {s..0} (\<lambda>s. ?u s + e / K)"
        by simp
    next
      show "continuous_on {t..0} (\<lambda>t. norm (XX t - Y t) + e / K)"
        using t0_t_in_J J_subset G.ivl_subset_existence_ivl'[OF t0_in_T2 x0_in_X tG]
        by (auto simp add: XX_def Y_def intro!: continuous_intros)
    next
      fix s assume "t \<le> s" "s \<le> 0"
      show "0 \<le> norm (XX s - Y s) + e / K"
        using e_pos K_pos by simp
    next
      show "0 < e / K" using e_pos K_pos by simp
    qed
    thus ?thesis by (simp add: algebra_simps)
  qed
qed

end

locale auto_ll_on_open = \<comment>\<open>TODO: how to guarantee that this theory is always complete?!\<close>
  fixes f::"'a::{banach, heine_borel} \<Rightarrow> 'a" and X
  assumes local_lipschitz: "local_lipschitz UNIV X (\<lambda>_::real. f)"
  assumes open_domain[intro!, simp]: "open X"
begin

sublocale na: ll_on_open "\<lambda>_. f" UNIV X
  by standard (auto simp: intro!: continuous_on_const local_lipschitz)

lemma continuous_on_f[continuous_intros]:
  assumes "continuous_on S h"
  assumes "h ` S \<subseteq> X"
  shows "continuous_on S (\<lambda>x. f (h x))"
  by (rule na.continuous_on_f[OF continuous_on_const assms]) simp

lemma auto_ll_on_open_rev[intro, simp]: "auto_ll_on_open (-f) X"
proof standard
  have "range uminus = (UNIV::real set)" by (auto intro!: image_eqI[where x="- x" for x])
  with na.ll_on_open_rev[of 0] interpret rev: ll_on_open "\<lambda>t. - f" UNIV X
    by auto
  from rev.local_lipschitz show "local_lipschitz UNIV X (\<lambda>_::real. - f)" .
qed simp

context fixes x0::'a \<comment>"initial value"
begin

definition "inf_existence = na.inf_existence 0 x0"

definition "sup_existence = na.sup_existence 0 x0"

definition "existence_ivl = na.existence_ivl 0 x0"

lemma open_existence_ivl[simp]: "open (existence_ivl)"
  by (simp add: existence_ivl_def)

lemma is_interval_existence_ivl[simp]: "is_interval existence_ivl"
  by (simp add: existence_ivl_def)

definition "flow t = na.flow 0 x0 t"

lemma Picard_iterate_mem_existence_ivlI:
  assumes "0 \<le> t"
  assumes "compact C" "x0 \<in> C" "C \<subseteq> X"
  assumes "\<And>y s. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> y 0 = x0 \<Longrightarrow> y \<in> {0 .. s} \<rightarrow> C \<Longrightarrow> continuous_on {0 .. s} y \<Longrightarrow>
      x0 + integral {0 .. s} (\<lambda>t. f (y t)) \<in> C"
  shows "t \<in> existence_ivl" "\<And>s. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> flow s \<in> C"
  unfolding existence_ivl_def flow_def
  by (blast intro!: na.Picard_iterate_mem_existence_ivlI[OF
    UNIV_I set_mp[OF \<open>C \<subseteq> X\<close> \<open>x0 \<in> C\<close>] assms(1) subset_UNIV assms(2-5)])+

context assumes iv_in: "x0 \<in> X" begin

lemma existence_ivl_zero[intro, simp]: "0 \<in> existence_ivl"
  unfolding existence_ivl_def
  by (rule na.existence_ivl_initial_time[OF UNIV_I iv_in])

lemma in_existence_between_zeroI:
  "t \<in> existence_ivl \<Longrightarrow> s \<in> {t .. 0} \<union> {0 .. t} \<Longrightarrow> s \<in> existence_ivl"
  unfolding existence_ivl_def
  by (rule na.in_existence_between_zeroI[OF UNIV_I iv_in])

lemma ivl2_subset_existence_ivl:
  "s \<in> existence_ivl \<Longrightarrow> t \<in> existence_ivl \<Longrightarrow> {s .. t} \<subseteq> existence_ivl"
  unfolding existence_ivl_def
  by (rule na.ivl2_subset_existence_ivl[OF UNIV_I iv_in])

lemma flow_in_domain: "t \<in> existence_ivl \<Longrightarrow> flow t \<in> X"
  by (simp add: existence_ivl_def flow_def iv_in na.flow_in_domain)

lemma flow_zero[simp]: "flow 0 = x0"
  by (simp add: flow_def iv_in)

lemma flow_has_derivative:
  assumes "t \<in> existence_ivl"
  shows "(flow has_derivative (\<lambda>i. i *\<^sub>R f (flow t))) (at t)"
  using assms
  by (auto simp add: existence_ivl_def flow_def[abs_def] iv_in intro!: na.flow_has_derivative)

end \<comment>\<open>@{thm iv_in}\<close>

end \<comment>\<open>@{term x0}\<close>

lemma
  assumes "t \<in> na.existence_ivl s x"
  assumes "x \<in> X"
  shows mem_existence_ivl_shift_autonomous1: "t - s \<in> existence_ivl x"
    and flow_shift_autonomous1: "na.flow s x t = flow x (t - s)"
proof -
  from na.existence_ivp[OF UNIV_I \<open>x \<in> X\<close>]
  interpret s: unique_solution "na.existence_ivp s x" .

  let ?T = "(op + (- s) ` na.existence_ivl s x)"
  have shifted: "is_interval ?T" "0 \<in> ?T"
    using na.existence_ivl_initial_time[OF UNIV_I \<open>x \<in> X\<close>]
    by (auto)

  define i where "i = \<lparr>ivp_f = \<lambda>(t, y). f y, ivp_t0 = 0, ivp_x0 = x, ivp_T = ?T, ivp_X = X\<rparr>"
  interpret i: ivp i
    by unfold_locales (auto simp: i_def \<open>x \<in> X\<close>)

  from s.shift_autonomous_solution[OF s.is_solution_solution refl, where j=i]
  have "i.is_solution (\<lambda>x. s.solution (x + s))" by (simp add: i_def o_def)

  from na.maximal_existence_flow[OF UNIV_I \<open>x \<in> X\<close> this, unfolded i_def, OF refl shifted]
  have *: "?T \<subseteq> existence_ivl x"
    and **: "\<And>t. t \<in> op + (- s) ` na.existence_ivl s x \<Longrightarrow> flow x t = s.solution (t + s)"
    by (auto simp: existence_ivl_def flow_def)

  have "t - s \<in> ?T"
    using \<open>t \<in> _\<close>
    by auto
  also note *
  finally show "t - s \<in> existence_ivl x" .

  have "flow x (t - s) = s.solution t"
    using \<open>t \<in> _\<close>
    by (auto simp: ** existence_ivl_def)
  also have "\<dots> = na.flow s x t"
    unfolding na.flow_def ..
  finally show "na.flow s x t = flow x (t - s)" ..
qed

lemma
  assumes "t - s \<in> existence_ivl x"
  assumes "x \<in> X"
  shows mem_existence_ivl_shift_autonomous2: "t \<in> na.existence_ivl s x"
    and flow_shift_autonomous2: "na.flow s x t = flow x (t - s)"
proof -
  from na.existence_ivp[OF UNIV_I \<open>x \<in> X\<close>]
  interpret s: unique_solution "na.existence_ivp 0 x" .

  let ?T = "(op + s ` na.existence_ivl 0 x)"
  have shifted: "is_interval ?T" "s \<in> ?T"
    using na.existence_ivl_initial_time[OF UNIV_I \<open>x \<in> X\<close>]
    by auto

  define i where "i = \<lparr>ivp_f = \<lambda>(t, y). f y, ivp_t0 = s, ivp_x0 = x, ivp_T = ?T, ivp_X = X\<rparr>"
  interpret i: ivp i
    by unfold_locales (auto simp: i_def \<open>x \<in> X\<close>)

  from s.shift_autonomous_solution[OF s.is_solution_solution refl, where j=i]
  have "i.is_solution (\<lambda>x. s.solution (x - s))" by (simp add: i_def o_def)

  from na.maximal_existence_flow[OF UNIV_I \<open>x \<in> X\<close> this, unfolded i_def, OF refl shifted]
  have *: "?T \<subseteq> na.existence_ivl s x"
    and **: "\<And>t. t \<in> op + s ` existence_ivl x \<Longrightarrow> na.flow s x t = s.solution (t - s)"
    by (auto simp: existence_ivl_def flow_def)

  have "t \<in> ?T"
    using \<open>t - s \<in> _\<close>
    by (force simp: existence_ivl_def)
  also note *
  finally show "t \<in> na.existence_ivl s x" .

  have "na.flow s x t = s.solution (t - s)"
    using \<open>t - s \<in> _\<close>
    by (subst **; force)
  also have "\<dots> = flow x (t - s)"
    unfolding flow_def na.flow_def ..
  finally show "na.flow s x t = flow x (t - s)" .
qed

lemma
  assumes s: "s \<in> existence_ivl x0"
  assumes t: "t \<in> existence_ivl (flow x0 s)"
  assumes iv_in[simp]: "x0 \<in> X"
  shows flow_trans: "flow x0 (s + t) = flow (flow x0 s) t"
    and existence_ivl_trans: "s + t \<in> existence_ivl x0"
proof -
  from na.flow_trans[OF s[unfolded existence_ivl_def] _ UNIV_I iv_in, OF mem_existence_ivl_shift_autonomous2, of t]
  have "flow x0 (s + t) = na.flow s (flow x0 s) (s + t)"
    using t na.flow_in_domain[OF UNIV_I iv_in s[unfolded existence_ivl_def]]
    by (auto simp: flow_def existence_ivl_def)
  also have "\<dots> = flow (flow x0 s) t"
    by (subst flow_shift_autonomous2) (auto intro!: flow_in_domain s t)
  finally show "flow x0 (s + t) = flow (flow x0 s) t" .

  from na.existence_ivl_trans[OF s[unfolded existence_ivl_def] _ UNIV_I iv_in, OF mem_existence_ivl_shift_autonomous2, of t]
  show "s + t \<in> existence_ivl x0"
    using assms flow_in_domain
    by (auto simp: flow_def existence_ivl_def)
qed

lemma
  assumes t: "t \<in> existence_ivl x0"
  assumes [simp]: "x0 \<in> X"
  shows flows_reverse: "flow (flow x0 t) (- t) = x0"
    and existence_ivl_reverse: "-t \<in> existence_ivl (flow x0 t)"
proof -
  from na.existence_ivl_reverse[OF t[unfolded existence_ivl_def] UNIV_I \<open>x0 \<in> X\<close>, THEN mem_existence_ivl_shift_autonomous1]
    flow_in_domain[OF \<open>x0 \<in> X\<close>] t
  show "-t \<in> existence_ivl (flow x0 t)"
    by (auto simp: existence_ivl_def flow_def)
  with na.flows_reverse[OF t[unfolded existence_ivl_def] UNIV_I \<open>x0 \<in> X\<close>] flow_in_domain[OF \<open>x0 \<in> X\<close>]
  show "flow (flow x0 t) (- t) = x0"
    by (subst (asm) flow_shift_autonomous2) (auto simp: flow_def t)
qed

lemma flow_has_vector_derivative:
  assumes "x \<in> X" "t \<in> existence_ivl x"
  shows "(flow x has_vector_derivative f (flow x t)) (at t)"
  using na.flow_has_vector_derivative[of 0 x t] assms
  by (simp add: flow_def[abs_def] existence_ivl_def)

lemma flow_has_vector_derivative_at_0:
  assumes "x \<in> X" "t \<in> existence_ivl x"
  shows "((\<lambda>h. flow x (t + h)) has_vector_derivative f (flow x t)) (at 0)"
  using na.flow_has_vector_derivative_at_0[of 0 x t] assms
  by (simp add: flow_def[abs_def] existence_ivl_def)

lemma
  assumes in_domain: "x \<in> X"
  assumes "t \<in> existence_ivl x"
  shows ivl_subset_existence_ivl: "{0 .. t} \<subseteq> existence_ivl x"
    and ivl_subset_existence_ivl': "{t .. 0} \<subseteq> existence_ivl x"
    and closed_segment_subset_existence_ivl: "closed_segment 0 t \<subseteq> existence_ivl x"
  using assms
  by (auto simp: closed_segment_real
    intro!: in_existence_between_zeroI[OF \<open>x \<in> X\<close> \<open>t \<in> _\<close>])

lemma flow_fixed_point:
  assumes t: "0 \<le> t" "t \<in> existence_ivl x"
  assumes "x \<in> X"
  shows "flow x t = x + integral {0..t} (\<lambda>t. f (flow x t))"
  using assms
  unfolding flow_def existence_ivl_def
  by (intro na.flow_fixed_point; simp)

lemma flow_fixed_point':
  assumes t: "t \<le> 0" "t \<in> existence_ivl x"
  assumes "x \<in> X"
  shows "flow x t = x - integral {t..0} (\<lambda>t. f (flow x t))"
  using assms
  unfolding flow_def existence_ivl_def
  by (intro na.flow_fixed_point'; simp)

lemma flow_fixed_point'':
  assumes t: "t \<in> existence_ivl x"
  assumes "x \<in> X"
  shows "flow x t =
    x + (if 0 \<le> t then 1 else -1) *\<^sub>R integral (closed_segment 0 t) (\<lambda>t. f (flow x t))"
  using assms
  unfolding flow_def existence_ivl_def
  by (intro na.flow_fixed_point''; simp)

lemma flow_continuous: "x \<in> X \<Longrightarrow> t \<in> existence_ivl x \<Longrightarrow> continuous (at t) (flow x)"
  by (metis has_derivative_continuous flow_has_derivative)

lemma flow_tendsto: "x \<in> X \<Longrightarrow> t \<in> existence_ivl x \<Longrightarrow> (ts \<longlongrightarrow> t) F \<Longrightarrow>
    ((\<lambda>s. flow x (ts s)) \<longlongrightarrow> flow x t) F"
  unfolding existence_ivl_def flow_def
  by (metis na.flow_tendsto UNIV_I)

lemma flow_continuous_on: "x \<in> X \<Longrightarrow> continuous_on (existence_ivl x) (flow x)"
  unfolding existence_ivl_def flow_def[abs_def]
  by (metis na.flow_continuous_on UNIV_I)

lemma flow_continuous_on_intro:
  "x \<in> X \<Longrightarrow>
  continuous_on s g \<Longrightarrow>
  (\<And>xa. xa \<in> s \<Longrightarrow> g xa \<in> existence_ivl x) \<Longrightarrow>
  continuous_on s (\<lambda>xa. flow x (g xa))"
  unfolding existence_ivl_def flow_def[abs_def]
  by (metis na.flow_continuous_on_intro UNIV_I)

lemma f_flow_continuous:
  assumes "t \<in> existence_ivl x" "x \<in> X"
  shows "isCont (\<lambda>t. f (flow x t)) t"
  using assms
  unfolding flow_def existence_ivl_def
  by (intro na.f_flow_continuous; simp)

lemma exponential_initial_condition:
  assumes y0: "t \<in> existence_ivl y0" and "y0 \<in> Y"
  assumes z0: "t \<in> existence_ivl z0" and "z0 \<in> Y"
  assumes "Y \<subseteq> X"
  assumes remain: "\<And>s. s \<in> closed_segment 0 t \<Longrightarrow> flow y0 s \<in> Y"
    "\<And>s. s \<in> closed_segment 0 t \<Longrightarrow> flow z0 s \<in> Y"
  assumes lipschitz: "\<And>s. s \<in> closed_segment 0 t \<Longrightarrow> lipschitz Y f K"
  shows "norm (flow y0 t - flow z0 t) \<le> norm (y0 - z0) * exp ((K + 1) * abs t)"
  using assms
  unfolding flow_def existence_ivl_def
  by (intro order_trans[OF na.exponential_initial_condition]) auto

lemma
  existence_ivl_cballs:
  fixes x assumes "x \<in> X"
  obtains t u L
  where
    "\<And>y. y \<in> cball x u \<Longrightarrow> cball 0 t \<subseteq> existence_ivl y"
    "\<And>s y. y \<in> cball x u \<Longrightarrow> s \<in> cball 0 t \<Longrightarrow> flow y s \<in> cball y u"
    "lipschitz (cball 0 t\<times>cball x u) (\<lambda>(t, x). flow x t) L"
    "\<And>y. y \<in> cball x u \<Longrightarrow> cball y u \<subseteq> X"
    "0 < t" "0 < u"
  unfolding flow_def existence_ivl_def
  using na.existence_ivl_cballs[OF UNIV_I assms]
  by metis

lemma
  flow_leaves_compact_ivl:
  assumes "x0 \<in> X"
  assumes "sup_existence x0 < \<infinity>"
  assumes "compact K"
  assumes "K \<subseteq> X"
  obtains t where "t \<ge> 0" "t \<in> existence_ivl x0" "flow x0 t \<notin> K"
  unfolding flow_def existence_ivl_def
  using na.flow_leaves_compact_ivl[OF UNIV_I assms(1) assms(2)[unfolded sup_existence_def]
    UNIV_I assms(3-4)]
  by metis

lemma
  global_existence_interval:
  assumes a: "a \<in> existence_ivl x0"
  assumes b: "b \<in> existence_ivl x0"
  assumes le: "a \<le> b"
  assumes x0: "x0 \<in> X"
  obtains d K where "d > 0" "K > 0"
    "ball x0 d \<subseteq> X"
    "\<And>y. y \<in> ball x0 d \<Longrightarrow> a \<in> existence_ivl y"
    "\<And>y. y \<in> ball x0 d \<Longrightarrow> b \<in> existence_ivl y"
    "\<And>t y. y \<in> ball x0 d \<Longrightarrow> t \<in> {a .. b} \<Longrightarrow>
      dist (flow x0 t) (flow y t) \<le> dist x0 y * exp (K * abs t)"
    "\<And>e. e > 0 \<Longrightarrow>
      eventually (\<lambda>y. \<forall>t \<in> {a .. b}. dist (flow x0 t) (flow y t) < e) (at x0)"
  unfolding flow_def existence_ivl_def
  using na.global_existence_interval[OF assms(1-3)[unfolded flow_def existence_ivl_def]
    UNIV_I x0]
  by auto

lemma open_state_space: "open (Sigma X existence_ivl)"
  and flow_continuous_on_state_space:
    "continuous_on (Sigma X existence_ivl) (\<lambda>(x, t). flow x t)"
  using na.open_state_space na.flow_continuous_on_state_space
  by (auto simp: existence_ivl_def flow_def)

lemma flow_isCont_state_space: "x \<in> X \<Longrightarrow> t \<in> existence_ivl x \<Longrightarrow> isCont (\<lambda>(x, t). flow x t) (x, t)"
  using na.flow_isCont_state_space
  by (auto simp: existence_ivl_def flow_def)

lemma flow_continuous_on_state_space_comp[continuous_intros]:
  assumes "continuous_on Y h" "continuous_on Y g"
  assumes "\<And>y. y \<in> Y \<Longrightarrow> h y \<in> X"
  assumes "\<And>y. y \<in> Y \<Longrightarrow> g y \<in> existence_ivl (h y)"
  shows "continuous_on Y (\<lambda>y. flow (h y) (g y))"
  using assms continuous_on_compose2[where f="\<lambda>y. (h y, g y)" and s = Y, OF flow_continuous_on_state_space]
  by (auto intro!: continuous_intros)

end \<comment>"@{thm local_lipschitz}"

locale compact_continuously_diff =
  derivative_on_prod T X f "\<lambda>(t, x). f' x o\<^sub>L snd_blinfun"
    for T X and f::"(real \<times> 'a::{banach,perfect_space,heine_borel}) \<Rightarrow> 'a"
    and f'::"'a \<Rightarrow> ('a, 'a) blinfun" +
  assumes compact_domain: "compact X"
  assumes convex: "convex X"
  assumes nonempty_domains: "T \<noteq> {}" "X \<noteq> {}"
  assumes continuous_derivative: "continuous_on X f'"
begin

lemma
  f_comp_derivative[derivative_intros]:
  assumes "t \<in> T" "x \<in> X"
  shows "((\<lambda>a. f (t, a)) has_derivative blinfun_apply (f' x)) (at x within X)"
proof -
  have "(f o (\<lambda>a. (t, a)) has_derivative blinfun_apply (f' x)) (at x within X)"
    by (auto intro!: derivative_eq_intros refl has_derivative_within_subset[OF f'] assms simp: split_beta')
  thus ?thesis by (simp add: o_def)
qed

lemma ex_onorm_bound:
  "\<exists>B. \<forall>x \<in> X. norm (f' x) \<le> B"
proof -
  from _ compact_domain have "compact (f' ` X)"
    by (intro compact_continuous_image continuous_derivative)
  hence "bounded (f' ` X)" by (rule compact_imp_bounded)
  thus ?thesis
    by (auto simp add: bounded_iff cball_def norm_blinfun.rep_eq)
qed

definition "onorm_bound = (SOME B. \<forall>x \<in> X. norm (f' x) \<le> B)"

lemma onorm_bound: assumes "x \<in> X" shows "norm (f' x) \<le> onorm_bound"
  unfolding onorm_bound_def
  using someI_ex[OF ex_onorm_bound] assms
  by blast

sublocale closed_domain X
  using compact_domain by unfold_locales (rule compact_imp_closed)

sublocale global_lipschitz T X f onorm_bound
proof (unfold_locales, rule lipschitzI)
  fix t z y
  assume "t \<in> T" "y \<in> X" "z \<in> X"
  then have "norm (f (t, y) - f (t, z)) \<le> onorm_bound * norm (y - z)"
    using onorm_bound
    by (intro differentiable_bound[where f'=f', OF convex])
       (auto intro!: derivative_eq_intros simp: norm_blinfun.rep_eq)
  thus "dist (f (t, y)) (f (t, z)) \<le> onorm_bound * dist y z"
    by (auto simp: dist_norm norm_Pair)
next
  from nonempty_domains obtain x where x: "x \<in> X" by auto
  show "0 \<le> onorm_bound"
    using dual_order.trans local.onorm_bound norm_ge_zero x by blast
qed

end \<comment>\<open>@{thm compact_domain}\<close>

locale unique_on_compact_continuously_diff = self_mapping i +
  compact_continuously_diff T X f
  for i::"'a::{banach,perfect_space,heine_borel} ivp"
begin

sublocale unique_on_closed i t1 onorm_bound
  by unfold_locales (auto intro!: f' has_derivative_continuous_on)

end

locale c1_on_open =
  fixes f::"'a::{banach, perfect_space, heine_borel} \<Rightarrow> 'a" and f' X
  assumes open_dom[simp]: "open X"
  assumes derivative_rhs:
    "\<And>x. x \<in> X \<Longrightarrow> (f has_derivative blinfun_apply (f' x)) (at x)"
  assumes continuous_derivative: "continuous_on X f'"
begin

lemmas continuous_derivative_comp[continuous_intros] =
  continuous_on_compose2[OF continuous_derivative]

lemma derivative_tendsto[tendsto_intros]:
  assumes [tendsto_intros]: "(g \<longlongrightarrow> l) F"
    and "l \<in> X"
  shows "((\<lambda>x. f' (g x)) \<longlongrightarrow> f' l) F"
  using continuous_derivative[simplified continuous_on] assms
  by (auto simp: at_within_open[OF _ open_dom]
    intro!: tendsto_eq_intros
    intro: tendsto_compose)

lemma c1_on_open_rev[intro, simp]: "c1_on_open (-f) (-f') X"
  using derivative_rhs continuous_derivative
  by unfold_locales
    (auto intro!: continuous_intros derivative_eq_intros
    simp: fun_Compl_def blinfun.bilinear_simps)

lemma derivative_rhs_compose[derivative_intros]:
  "((g has_derivative g') (at x within s)) \<Longrightarrow> g x \<in> X \<Longrightarrow>
    ((\<lambda>x. f (g x)) has_derivative
      (\<lambda>xa. blinfun_apply (f' (g x)) (g' xa)))
    (at x within s)"
  by (metis has_derivative_compose[of g g' x s f "f' (g x)"] derivative_rhs)

sublocale auto_ll_on_open
proof (standard, rule local_lipschitzI)
  fix x and t::real
  assume "x \<in> X"
  with open_contains_cball[of "UNIV::real set"] open_UNIV
    open_contains_cball[of X] open_dom
  obtain u v where uv: "cball t u \<subseteq> UNIV" "cball x v \<subseteq> X" "u > 0" "v > 0"
    by blast
  let ?T = "cball t u" and ?X = "cball x v"
  have "bounded ?X" by simp
  have "compact (cball x v)"
    by simp
  interpret compact_continuously_diff ?T ?X "\<lambda>(t, x). f x" f'
    using uv
    by unfold_locales
      (auto simp: convex_cball cball_eq_empty split_beta'
        intro!: derivative_eq_intros continuous_on_compose2[OF continuous_derivative]
          continuous_intros)
  have "lipschitz ?X f onorm_bound"
    using lipschitz[of t] uv
    by auto
  thus "\<exists>u>0. \<exists>L. \<forall>t \<in> cball t u \<inter> UNIV. lipschitz (cball x u \<inter> X) f L"
    by (intro exI[where x=v])
      (auto intro!: exI[where x=onorm_bound] \<open>0 < v\<close> simp: Int_absorb2 uv)
qed (auto intro!: continuous_intros)

end \<comment>\<open>@{thm derivative_rhs}\<close>

locale c1_on_open_euclidean = c1_on_open f f' X
  for f::"'a::euclidean_space \<Rightarrow> _" and f' X
begin
lemma c1_on_open_euclidean_anchor: True ..

definition "XX x0 = flow x0"
definition "A x0 t = f' (XX x0 t)"

lemma continuous_on_A[continuous_intros]:
  assumes "continuous_on S a"
  assumes "continuous_on S b"
  assumes "\<And>s. s \<in> S \<Longrightarrow> a s \<in> X"
  assumes "\<And>s. s \<in> S \<Longrightarrow> b s \<in> existence_ivl (a s)"
  shows "continuous_on S (\<lambda>s. A (a s) (b s))"
proof -
  have "continuous_on S (\<lambda>x. f' (flow (a x) (b x)))"
    by (auto intro!: continuous_intros assms flow_in_domain)
  then show ?thesis
    by (rule continuous_on_eq) (auto simp: assms A_def XX_def)
qed

context
  fixes x0::'a
  assumes x0_def[continuous_intros]: "x0 \<in> X"
begin

lemma XX_defined: "xa \<in> existence_ivl x0 \<Longrightarrow> XX x0 xa \<in> X"
  by (auto simp: XX_def flow_in_domain x0_def)

lemma continuous_on_XX: "continuous_on (existence_ivl x0) (XX x0)"
  by (auto simp: XX_def intro!: continuous_intros )

lemmas continuous_on_XX_comp[continuous_intros] = continuous_on_compose2[OF continuous_on_XX]

interpretation var: ll_on_open "A x0" "existence_ivl x0" UNIV
  by standard
    (auto intro!: c1_implies_local_lipschitz[where f' = "\<lambda>(t, x). A x0 t"] continuous_intros
      derivative_eq_intros
      simp: split_beta' blinfun.bilinear_simps)

lemma varexivl_eq_exivl:
  assumes "t \<in> existence_ivl x0"
  shows "var.existence_ivl t a = existence_ivl x0"
proof (rule var.existence_ivl_eq_domain)
  fix s t x
  assume s: "s \<in> existence_ivl x0" and t: "t \<in> existence_ivl x0"
  then have "{s .. t} \<subseteq> existence_ivl x0"
    by (intro ivl2_subset_existence_ivl[OF x0_def])
  then have "continuous_on {s .. t} (A x0)"
    by (auto simp: closed_segment_real intro!: continuous_intros)
  then have "compact ((A x0) ` {s .. t})"
    using compact_Icc
    by (rule compact_continuous_image)
  then obtain B where B: "\<And>u. u \<in> {s .. t} \<Longrightarrow> norm (A x0 u) \<le> B"
    by (force dest!: compact_imp_bounded simp: bounded_iff)
  show "\<exists>M L. \<forall>t\<in>{s .. t}. \<forall>x\<in>UNIV. norm (blinfun_apply (A x0 t) x) \<le> M + L * norm x"
    by (rule exI[where x=0], rule exI[where x=B])
      (auto intro!: order_trans[OF norm_blinfun] mult_right_mono B)
qed (auto intro: assms)

definition "U u0 t = var.flow 0 u0 t"

definition "Y z t = flow (x0 + z) t"

text \<open>Linearity of the solution to the variational equation.
  TODO: generalize for arbitrary linear ODEs\<close>
lemma U_linear:
assumes "t \<in> existence_ivl x0"
shows "U (\<alpha> *\<^sub>R a + \<beta> *\<^sub>R b) t = \<alpha> *\<^sub>R U a t + \<beta> *\<^sub>R U b t"
  unfolding U_def
proof (rule var.maximal_existence_flow[OF _ _ _ refl is_interval_existence_ivl[of x0]])
  note x0_def[intro, simp]
  interpret c: ivp
    "\<lparr>ivp_f = \<lambda>(t, x). blinfun_apply (A x0 t) x,
      ivp_t0 = 0,
      ivp_x0 = \<alpha> *\<^sub>R a + \<beta> *\<^sub>R b,
      ivp_T = existence_ivl x0,
      ivp_X = UNIV\<rparr>"
    by unfold_locales auto
  show "c.is_solution (\<lambda>c. \<alpha> *\<^sub>R var.flow 0 a c + \<beta> *\<^sub>R var.flow 0 b c)"
  proof (rule c.is_solutionI)
    show "\<alpha> *\<^sub>R var.flow 0 a c.t0 + \<beta> *\<^sub>R var.flow 0 b c.t0 = c.x0"
      by simp
  next
    fix t assume "t \<in> c.T"
    hence "t \<in> existence_ivl x0" by simp
    with at_within_open[OF this open_existence_ivl]
    show "((\<lambda>c. \<alpha> *\<^sub>R var.flow 0 a c + \<beta> *\<^sub>R var.flow 0 b c) has_vector_derivative
          c.f (t, \<alpha> *\<^sub>R var.flow 0 a t + \<beta> *\<^sub>R var.flow 0 b t))
          (at t within c.T)"
      by (auto intro!: derivative_eq_intros var.flow_has_vector_derivative
        simp: blinfun.bilinear_simps varexivl_eq_exivl)
    show "\<alpha> *\<^sub>R var.flow 0 a t + \<beta> *\<^sub>R var.flow 0 b t \<in> c.X"
      by simp
  qed
qed (auto intro!: x0_def assms)

lemma linear_U:
assumes "t \<in> existence_ivl x0"
shows "linear (\<lambda>z. U z t)"
using U_linear[OF assms, of 1 _ 1] U_linear[OF assms, of _ _ 0]
by (auto intro!: linearI)

lemma bounded_linear_U:
assumes "t \<in> existence_ivl x0"
shows "bounded_linear (\<lambda>z. U z t)"
by (simp add: linear_linear linear_U assms)

lemma U_continuous_on_time: "continuous_on (existence_ivl x0) (\<lambda>t. U z t)"
unfolding U_def
using var.flow_continuous_on[of 0 z]
by (auto simp: x0_def varexivl_eq_exivl)

lemma proposition_17_6_weak:
  \<comment>\<open>from "Differential Equations, Dynamical Systems, and an Introduction to Chaos",
    Hirsch/Smale/Devaney\<close>
assumes "t \<in> existence_ivl x0"
shows "(\<lambda>y. (Y (y - x0) t - XX x0 t - U (y - x0) t) /\<^sub>R norm (y - x0)) \<midarrow> x0 \<rightarrow> 0"
proof-
  have "0 \<in> existence_ivl x0"
    by (simp add: x0_def)

  text \<open>Find some \<open>J \<subseteq> existence_ivl x0\<close> with \<open>0 \<in> J\<close> and \<open>t \<in> J\<close>.\<close>
  define t0 where "t0 = min 0 t"
  define t1 where "t1 = max 0 t"
  define J where "J = {t0..t1}"

  have "t0 \<le> 0" "0 \<le> t1" "0 \<in> J" "J \<noteq> {}" "t \<in> J" "compact J"
  and J_in_existence: "J \<subseteq> existence_ivl x0"
    using ivl_subset_existence_ivl ivl_subset_existence_ivl' x0_def assms
    by (auto simp add: J_def t0_def t1_def min_def max_def)

  {
    fix z S
    assume assms: "x0 + z \<in> X" "S \<subseteq> existence_ivl (x0 + z)"
    have "continuous_on S (Y z)"
      using flow_continuous_on assms(1)
      by (intro continuous_on_subset[OF _ assms(2)]) (simp add: Y_def)
  }
  note [continuous_intros] = this integrable_continuous_real blinfun.continuous_on

  have U_continuous[continuous_intros]: "\<And>z. continuous_on J (U z)"
    by(rule continuous_on_subset[OF U_continuous_on_time J_in_existence])

  from \<open>t \<in> J\<close>
  have "t0 \<le> t"
  and "t \<le> t1"
  and "t0 \<le> t1"
  and "t0 \<in> existence_ivl x0"
  and "t \<in> existence_ivl x0"
  and "t1 \<in> existence_ivl x0"
    using J_def J_in_existence by auto
  from global_existence_interval[OF \<open>t0 \<in> existence_ivl x0\<close> \<open>t1 \<in> existence_ivl x0\<close> \<open>t0 \<le> t1\<close> x0_def]
  obtain u K where uK_def:
    "0 < u"
    "0 < K"
    "ball x0 u \<subseteq> X"
    "\<And>y. y \<in> ball x0 u \<Longrightarrow> t0 \<in> existence_ivl y"
    "\<And>y. y \<in> ball x0 u \<Longrightarrow> t1 \<in> existence_ivl y"
    "\<And>t y. y \<in> ball x0 u \<Longrightarrow> t \<in> J \<Longrightarrow> dist (XX x0 t) (Y (y - x0) t) \<le> dist x0 y * exp (K * \<bar>t\<bar>)"
    "\<And>e. 0 < e \<Longrightarrow> \<forall>\<^sub>F y in at x0. \<forall>t\<in>J. dist (XX x0 t) (Y (y - x0) t) < e"
      by (auto simp add: J_def XX_def Y_def)

  have J_in_existence_ivl: "\<And>y. y \<in> ball x0 u \<Longrightarrow> J \<subseteq> existence_ivl y"
    unfolding J_def
    using uK_def
    by (intro ivl2_subset_existence_ivl) auto
  have ball_in_X: "\<And>z. z \<in> ball 0 u \<Longrightarrow> x0 + z \<in> X"
    using uK_def(3)
    by (auto simp: dist_norm)

  have XX_J_props: "XX x0 ` J \<noteq> {}" "compact (XX x0 ` J)" "XX x0` J \<subseteq> X"
    using \<open>t0 \<le> t1\<close>
    using J_def(1) J_in_existence
    by (auto simp add: J_def XX_def intro!:
      compact_continuous_image continuous_intros flow_in_domain)

  have [continuous_intros]: "continuous_on J (\<lambda>s. f' (XX x0 s))"
    using J_in_existence
    by (auto intro!: continuous_intros flow_in_domain simp: XX_def)

  text \<open> Show the thesis via cases \<open>t = 0\<close>, \<open>0 < t\<close> and \<open>t < 0\<close>. \<close>
  show ?thesis
  proof(cases "t = 0")
    assume "t = 0"
    show ?thesis
    unfolding \<open>t = 0\<close> Lim_at
    proof(simp add: dist_norm[of _ 0] del: zero_less_dist_iff, safe, rule exI, rule conjI[OF \<open>0 < u\<close>], safe)
      fix e::real and x assume "0 < e" "0 < dist x x0" "dist x x0 < u"
      hence "x \<in> X"
        using uK_def(3)
        by (auto simp: dist_commute)
      hence "inverse (norm (x - x0)) * norm (Y (x - x0) 0 - XX x0 0 - U (x - x0) 0) = 0"
        using x0_def
        by (simp add: XX_def Y_def U_def)
      thus "inverse (norm (x - x0)) * norm (Y (x - x0) 0 - XX x0 0 - U (x - x0) 0) < e"
        using \<open>0 < e\<close> by auto
    qed
  next
    assume "t \<noteq> 0"
    show ?thesis
    proof(unfold Lim_at, safe)
      fix e::real assume "0 < e"
      then obtain e' where "0 < e'" "e' < e"
        using dense by auto

      obtain N
        where N_ge_SupS: "Sup { norm (f' (XX x0 s)) |s. s \<in> J } \<le> N" (is "Sup ?S \<le> N")
          and N_gr_0: "0 < N"
        \<comment>\<open> We need N to be an upper bound of @{term ?S}, but also larger than zero. \<close>
        by (meson le_cases less_le_trans linordered_field_no_ub)
      have N_ineq: "\<And>s. s \<in> J \<Longrightarrow> norm (f' (XX x0 s)) \<le> N"
        proof-
          fix s assume "s \<in> J"
          have "?S = (norm o f' o XX x0) ` J" by auto
          moreover have "continuous_on J (norm o f' o XX x0)"
            using J_in_existence
            by (auto intro!: continuous_intros)
          ultimately have  "\<exists>a b. ?S = {a..b} \<and> a \<le> b"
            using continuous_image_closed_interval[OF \<open>t0 \<le> t1\<close>]
            by (simp add: J_def)
          then obtain a b where "?S = {a..b}" and "a \<le> b" by auto
          hence "bdd_above ?S" by simp
          from \<open>s \<in> J\<close>  cSup_upper[OF _ this]
          have "norm (f' (XX x0 s)) \<le> Sup ?S"
            by auto
          thus "norm (f' (XX x0 s)) \<le> N"
            using N_ge_SupS by simp
        qed

      text \<open> Define a small region around \<open>XX ` J\<close>, that is a subset of the domain \<open>X\<close>. \<close>
      from compact_in_open_separated[OF XX_J_props(1,2) open_domain XX_J_props(3)]
        obtain e_domain where e_domain_def: "0 < e_domain" "{x. infdist x (XX x0 ` J) \<le> e_domain} \<subseteq> X"
        by auto
      define G where "G = {x\<in>X. infdist x (XX x0 ` J) < e_domain}"
      have G_vimage: "G = ((\<lambda>x. infdist x (XX x0 ` J)) -` {..<e_domain}) \<inter> X"
        by (auto simp: G_def)
      have "open G" "G \<subseteq> X"
        unfolding G_vimage
        by (auto intro!: open_Int open_vimage continuous_intros continuous_at_imp_continuous_on)

      text \<open>Define a compact subset H of G. Inside H, we can guarantee
         an upper bound on the Taylor remainder.\<close>
      define e_domain2 where "e_domain2 = e_domain / 2"
      have "e_domain2 > 0" "e_domain2 < e_domain" using \<open>e_domain > 0\<close>
        by (simp_all add: e_domain2_def)
      define H where "H = {x. infdist x (XX x0 ` J) \<le> e_domain2}"
      have H_props: "H \<noteq> {}" "compact H" "H \<subseteq> G"
        proof-
          have "x0 \<in> XX x0 ` J"
            unfolding image_iff
            using XX_def \<open>0 \<in> J\<close>  x0_def
            by force

          hence "x0 \<in> H"
            using \<open>0 < e_domain2\<close>
            by (simp add: H_def x0_def)
          thus "H \<noteq> {}"
            by auto
        next
          show "compact H"
            unfolding H_def
            using \<open>0 < e_domain2\<close> XX_J_props
            by (intro compact_infdist_le) simp_all
        next
          show "H \<subseteq> G"
          proof
            fix x assume "x \<in> H"

            from \<open>x \<in> H\<close>
            have "infdist x (XX x0 ` J) < e_domain"
              using \<open>0 < e_domain\<close>
              by (simp add: H_def e_domain2_def)
            moreover from this have "x \<in> X"
              using e_domain_def(2)
              by auto
            ultimately show "x \<in> G"
              unfolding G_def
              by auto
          qed
        qed

      have f'_cont_on_G: "(\<And>x. x \<in> G \<Longrightarrow> isCont f' x)"
        using continuous_on_interior[OF continuous_on_subset[OF continuous_derivative \<open>G \<subseteq> X\<close>]]
        by (simp add: interior_open[OF \<open>open G\<close>])

      define e1 where "e1 = e' / (\<bar>t\<bar> * exp (K * \<bar>t\<bar>) * exp (N * \<bar>t\<bar>))"
        \<comment> \<open> @{term e1} is the bounding term for the Taylor remainder. \<close>
      have "0 < \<bar>t\<bar>"
        using \<open>t \<noteq> 0\<close>
        by simp
      hence "0 < e1"
        using \<open>0 < e'\<close>
        by (simp add: e1_def) 

      text \<open> Taylor expansion of f on set G. \<close>
      from uniform_explicit_remainder_taylor_1[where f=f and f'=f',
        OF derivative_rhs[OF subsetD[OF \<open>G \<subseteq> X\<close>]] f'_cont_on_G \<open>open G\<close> H_props \<open>0 < e1\<close>]
      obtain d_taylor R
      where taylor_expansion:
        "0 < d_taylor"
        "\<And>x z. f z = f x + (f' x) (z - x) + R x z"
        "\<And>x y. x \<in> H \<Longrightarrow> y \<in> H \<Longrightarrow> dist x y < d_taylor \<Longrightarrow> norm (R x y) \<le> e1 * dist x y"
        "continuous_on (G \<times> G) (\<lambda>(a, b). R a b)"
          by auto

      text \<open> Find d, such that solutions are always at least \<open>min (e_domain/2) d_taylor\<close> apart,
         i.e. always in H. This later gives us the bound on the remainder. \<close>
      have "0 < min (e_domain/2) d_taylor"
        using \<open>0 < d_taylor\<close> \<open>0 < e_domain\<close>
        by auto
      from uK_def(7)[OF this, unfolded eventually_at]
      obtain d_ivl where d_ivl_def:
        "0 < d_ivl"
        "\<And>x. 0 < dist x x0 \<Longrightarrow> dist x x0 < d_ivl \<Longrightarrow>
          (\<forall>t\<in>J. dist (XX x0 t) (Y (x - x0) t) < min (e_domain / 2) d_taylor)"
        by (auto simp: dist_norm)

      define d where "d = min u d_ivl"
      have "0 < d" using \<open>0 < u\<close> \<open>0 < d_ivl\<close>
        by (simp add: d_def)
      hence "d \<le> u" "d \<le> d_ivl"
        by (auto simp: d_def)

      text \<open> Therefore, any flow starting in \<open>ball x0 d\<close> will be in G. \<close>
      have Y_in_G: "\<And>y. y \<in> ball x0 d \<Longrightarrow> (\<lambda>s. Y (y - x0) s) ` J \<subseteq> G"
        proof
          fix x y assume assms: "y \<in> ball x0 d" "x \<in> (\<lambda>s. Y (y - x0) s) ` J"
          show "x \<in> G"
          proof(cases)
            assume "y = x0"
            from assms(2)
            have "x \<in> XX x0 ` J"
              by (simp add: XX_def Y_def \<open>y = x0\<close>)
            thus "x \<in> G"
              using \<open>0 < e_domain\<close> \<open>XX x0 ` J \<subseteq> X\<close>
              by (auto simp: G_def)
          next
            assume "y \<noteq> x0"
            hence "0 < dist y x0"
              by (simp add: dist_norm)
            from d_ivl_def(2)[OF this] \<open>d \<le> d_ivl\<close>  \<open>0 < e_domain\<close> assms(1)
            have dist_XX_Y: "\<And>t. t \<in> J \<Longrightarrow> dist (XX x0 t) (Y (y - x0) t) < e_domain"
              by (auto simp: XX_def Y_def dist_commute)

            from assms(2)
            obtain t where t_def: "t \<in> J" "x = Y (y - x0) t"
              by auto
            have "x \<in> X"
              unfolding t_def(2) Y_def
              using uK_def(3) assms(1) \<open>d \<le> u\<close> subsetD[OF J_in_existence_ivl t_def(1)]
              by (auto simp: intro!: flow_in_domain)

            have "XX x0 t \<in> XX x0 ` J" using t_def by auto
            from dist_XX_Y[OF t_def(1)]
            have "dist x (XX x0 t) < e_domain"
              by (simp add: t_def(2) dist_commute)
            from le_less_trans[OF infdist_le[OF \<open>XX x0 t \<in> XX x0 ` J\<close>] this] \<open>x \<in> X\<close>
            show "x \<in> G"
              by (auto simp: G_def)
          qed
        qed
      from this[of x0] \<open>0 < d\<close>
      have X_in_G: "XX x0 ` J \<subseteq> G"
        by (simp add: XX_def Y_def)

      show "\<exists>d>0. \<forall>x. 0 < dist x x0 \<and> dist x x0 < d \<longrightarrow>
                     dist ((Y (x - x0) t - XX x0 t - U (x - x0) t) /\<^sub>R norm (x - x0)) 0 < e"
      proof(rule exI, rule conjI[OF \<open>0 < d\<close>], safe, unfold norm_conv_dist[symmetric])
        fix x assume x_x0_dist: "0 < dist x x0" "dist x x0 < d"
        hence x_in_ball': "x \<in> ball x0 d"
          by (simp add: dist_commute)
        hence x_in_ball: "x \<in> ball x0 u"
          using \<open>d \<le> u\<close>
          by simp

        text \<open> First, some prerequisites. \<close>
        from x_in_ball
        have z_in_ball: "x - x0 \<in> ball 0 u"
          using \<open>0 < u\<close>
          by (simp add: dist_norm)
        hence [continuous_intros]: "dist x0 x < u"
          by (auto simp: dist_norm)

        from J_in_existence_ivl[OF x_in_ball]
        have J_in_existence_ivl_x: "J \<subseteq> existence_ivl x" .
        from ball_in_X[OF z_in_ball]
        have x_in_X[continuous_intros]: "x \<in> X"
          by simp

        text \<open> On all of \<open>J\<close>, we can find upper bounds for the distance of \<open>XX\<close> and \<open>Y\<close>. \<close>
        have dist_XX_Y: "\<And>s. s \<in> J \<Longrightarrow> dist (XX x0 s) (Y (x - x0) s) \<le> dist x0 x * exp (K * \<bar>t\<bar>)"
          using t0_def t1_def uK_def(2)
          by (intro order_trans[OF uK_def(6)[OF x_in_ball] mult_left_mono])
             (auto simp add: XX_def Y_def J_def intro!: mult_mono)
        from d_ivl_def x_x0_dist \<open>d \<le> d_ivl\<close>
        have dist_XX_Y2: "\<And>t. t \<in> J \<Longrightarrow> dist (XX x0 t) (Y (x - x0) t) < min (e_domain2) d_taylor"
          by (auto simp: XX_def Y_def e_domain2_def)

        let ?g = "\<lambda>t. norm (Y (x - x0) t - XX x0 t - U (x - x0) t)"
        let ?C = "\<bar>t\<bar> * dist x0 x * exp (K * \<bar>t\<bar>) * e1"
        text \<open> Find an upper bound to \<open>?g\<close>, i.e. show that
             \<open>?g s \<le> ?C + N * integral {a..b} ?g\<close>
           for \<open>{a..b} = {0..s}\<close> or \<open>{a..b} = {s..0}\<close> for some \<open>s \<in> J\<close>.
           We can then apply Grönwall's inequality to obtain a true bound for \<open>?g\<close>. \<close>
        have g_bound: "?g s \<le> ?C + N * integral {a..b} ?g"
          if s_def: "s \<in> {a..b}"
          and J'_def: "{a..b} \<subseteq> J"
          and ab_cases: "(a = 0 \<and> b = s) \<or> (a = s \<and> b = 0)"
          for s a b
        proof -
          from that have "s \<in> J" by auto

          have s_in_existence_ivl_x0: "s \<in> existence_ivl x0"
            using J_in_existence \<open>s \<in> J\<close> by auto
          have s_in_existence_ivl: "\<And>y. y \<in> ball x0 u \<Longrightarrow> s \<in> existence_ivl y"
            using J_in_existence_ivl \<open>s \<in> J\<close> by auto
          have s_in_existence_ivl2: "\<And>z. z \<in> ball 0 u \<Longrightarrow> s \<in> existence_ivl (x0 + z)"
            using s_in_existence_ivl
            by (simp add: dist_norm)

          text \<open>Prove continuities beforehand.\<close>
          note continuous_on_0_s[continuous_intros] = continuous_on_subset[OF _ \<open>{a..b} \<subseteq> J\<close>]

          have [continuous_intros]: "continuous_on J (XX x0)"
            apply(rule continuous_on_subset[OF _ J_in_existence])
            using flow_continuous_on[OF x0_def]
            by (simp add: XX_def)

          have [continuous_intros]: "continuous_on S (\<lambda>s. f (Y z s))"
            if "x0 + z \<in> X" "S \<subseteq> existence_ivl (x0 + z)" for z S
          proof (rule continuous_on_subset[OF _ that(2)])
            show "continuous_on (existence_ivl (x0 + z)) (\<lambda>s. f (Y z s))"
              using that
              by (auto intro!: continuous_intros flow_in_domain flow_continuous_on simp: Y_def)
          qed

          have [continuous_intros]: "continuous_on J (\<lambda>s. f (XX x0 s))"
            by(rule continuous_on_subset[OF _ J_in_existence])
              (auto intro!: continuous_intros flow_continuous_on flow_in_domain simp: XX_def x0_def)

          have [continuous_intros]: "\<And>z. continuous_on J (\<lambda>s. f' (XX x0 s) (U z s))"
          proof-
            fix z
            have a1: "continuous_on J (XX x0)"
              unfolding XX_def
              by (rule continuous_on_subset[OF flow_continuous_on[OF x0_def] J_in_existence])

            have a2: "(\<lambda>s. (XX x0 s, U z s)) ` J \<subseteq> (XX x0 ` J) \<times> ((\<lambda>s. U z s) ` J)"
              by auto
            have a3: "continuous_on ((\<lambda>s. (XX x0 s, U z s)) ` J) (\<lambda>(x, u). f' x u)"
              using assms
              by (intro continuous_on_subset[OF _ a2])
                (auto intro!: tendsto_eq_intros blinfun.tendsto
                  simp: split_beta' flow_in_domain[OF x0_def J_in_existence[THEN subsetD]] XX_def
                    continuous_on_def)
            from continuous_on_compose[OF continuous_on_Pair[OF a1 U_continuous] a3]
            show "continuous_on J (\<lambda>s. f' (XX x0 s) (U z s))"
              by simp
          qed

          have [continuous_intros]: "continuous_on J (\<lambda>s. R (XX x0 s) (Y (x - x0) s))"
            using J_in_existence J_in_existence_ivl[OF x_in_ball] X_in_G \<open>{a..b} \<subseteq> J\<close> Y_in_G
              x_x0_dist
            by (intro continuous_on_compose_Pair[OF taylor_expansion(4)])
              (auto intro!: continuous_intros simp: dist_commute)
          hence [continuous_intros]:
            "(\<lambda>s. R (XX x0 s) (Y (x - x0) s)) integrable_on J"
            unfolding J_def
            by (rule integrable_continuous_real)

          have i1: "integral {a..b} (\<lambda>s. f (Y (x - x0) s)) - integral {a..b} (\<lambda>s. f (XX x0 s)) =
              integral {a..b} (\<lambda>s. f (Y (x - x0) s) - f (XX x0 s))"
            using J_in_existence_ivl[OF x_in_ball]
            by (intro integral_diff[symmetric]) (auto intro!: continuous_intros)

          have i2:
            "integral {a..b} (\<lambda>s. f (Y (x - x0) s) - f (XX x0 s) - (f' (XX x0 s)) (U (x - x0) s)) =
              integral {a..b} (\<lambda>s. f (Y (x - x0) s) - f (XX x0 s)) -
              integral {a..b} (\<lambda>s. f' (XX x0 s) (U (x - x0) s))"
            using J_in_existence_ivl[OF x_in_ball]
            by (intro integral_diff[OF integrable_diff]) (auto intro!: continuous_intros)

          from ab_cases
          have "?g s = norm (integral {a..b} (\<lambda>s'. f (Y (x - x0) s')) - integral {a..b} (\<lambda>s'. f (XX x0 s')) - integral {a..b} (\<lambda>s'. (f' (XX x0 s')) (U (x - x0) s')))"
          proof(safe)
            assume "a = 0" "b = s"
            hence "0 \<le> s" using \<open>s \<in> {a..b}\<close> by simp

            text\<open> Integral equations for XX, Y and U. \<close>
            have XX_integral_eq: "XX x0 s = x0 + integral {0..s} (\<lambda>s. f (XX x0 s))"
              unfolding XX_def
              by (rule flow_fixed_point[OF \<open>0 \<le> s\<close> s_in_existence_ivl_x0 x0_def])
            have Y_integral_eq: "Y (x - x0) s = x0 + (x - x0) + integral {0..s} (\<lambda>s. f (Y (x - x0) s))"
              using flow_fixed_point \<open>0 \<le> s\<close> s_in_existence_ivl2[OF z_in_ball] ball_in_X[OF z_in_ball]
              by (simp add: Y_def)
            have U_integral_eq: "U (x - x0) s = (x - x0) + integral {0..s} (\<lambda>s. f' (XX x0 s) (U (x - x0) s))"
              unfolding U_def A_def[symmetric]
              by (rule var.flow_fixed_point)
                (auto simp: \<open>0 \<le> s\<close> x0_def varexivl_eq_exivl s_in_existence_ivl_x0)
            show "?g s = norm (integral {0..s} (\<lambda>s'. f (Y (x - x0) s')) - integral {0..s} (\<lambda>s'. f (XX x0 s')) -
                integral {0..s} (\<lambda>s'. blinfun_apply (f' (XX x0 s')) (U (x - x0) s')))"
              by (simp add: XX_integral_eq Y_integral_eq U_integral_eq)
          next
            assume "a = s" "b = 0"
            hence "s \<le> 0" using \<open>s \<in> {a..b}\<close> by simp

            have XX_integral_eq_left: "XX x0 s = x0 - integral {s..0} (\<lambda>s. f (XX x0 s))"
              unfolding XX_def
              by (rule flow_fixed_point'[OF \<open>s \<le> 0\<close> s_in_existence_ivl_x0 x0_def])
            have Y_integral_eq_left: "Y (x - x0) s = x0 + (x - x0) - integral {s..0} (\<lambda>s. f (Y (x - x0) s))"
              using flow_fixed_point' \<open>s \<le> 0\<close> s_in_existence_ivl2[OF z_in_ball] ball_in_X[OF z_in_ball]
              by (simp add: Y_def)
            have U_integral_eq_left: "U (x - x0) s = (x - x0) - integral {s..0} (\<lambda>s. f' (XX x0 s) (U (x - x0) s))"
              unfolding U_def A_def[symmetric]
              by (rule var.flow_fixed_point')
                (auto simp: \<open>s \<le> 0\<close> x0_def varexivl_eq_exivl s_in_existence_ivl_x0)

            have "?g s =
              norm (- integral {s..0} (\<lambda>s'. f (Y (x - x0) s')) +
                integral {s..0} (\<lambda>s'. f (XX x0 s')) +
                integral {s..0} (\<lambda>s'. (f' (XX x0 s')) (U (x - x0) s')))"
              unfolding XX_integral_eq_left Y_integral_eq_left U_integral_eq_left
              by simp
            also have "... = norm (integral {s..0} (\<lambda>s'. f (Y (x - x0) s')) -
                integral {s..0} (\<lambda>s'. f (XX x0 s')) -
                integral {s..0} (\<lambda>s'. (f' (XX x0 s')) (U (x - x0) s')))"
              by (subst norm_minus_cancel[symmetric], simp)
            finally show "?g s =
              norm (integral {s..0} (\<lambda>s'. f (Y (x - x0) s')) -
                integral {s..0} (\<lambda>s'. f (XX x0 s')) -
                integral {s..0} (\<lambda>s'. blinfun_apply (f' (XX x0 s')) (U (x - x0) s')))"
              .
          qed
          also have "... =
            norm (integral {a..b} (\<lambda>s. f (Y (x - x0) s) - f (XX x0 s) - (f' (XX x0 s)) (U (x - x0) s)))"
            by (simp add: i1 i2)
          also have "... \<le>
            integral {a..b} (\<lambda>s. norm (f (Y (x - x0) s) - f (XX x0 s) - f' (XX x0 s) (U (x - x0) s)))"
            using x_in_X J_in_existence_ivl_x J_in_existence \<open>{a..b} \<subseteq> J\<close>
            by (auto intro!: continuous_intros continuous_on_imp_absolutely_integrable_on)
          also have "... = integral {a..b}
              (\<lambda>s. norm (f' (XX x0 s) (Y (x - x0) s - XX x0 s - U (x - x0) s) + R (XX x0 s) (Y (x - x0) s)))"
          proof (safe intro!: integral_spike[OF negligible_empty, simplified] arg_cong[where f=norm])
            fix s' assume "s' \<in> {a..b}"
            show "f' (XX x0 s') (Y (x - x0) s' - XX x0 s' - U (x - x0) s') + R (XX x0 s') (Y (x - x0) s') =
              f (Y (x - x0) s') - f (XX x0 s') - f' (XX x0 s') (U (x - x0) s')"
              by (simp add: blinfun.diff_right taylor_expansion(2)[of "Y (x - x0) s'" "XX x0 s'"])
          qed
          also have "... \<le> integral {a..b}
            (\<lambda>s. norm (f' (XX x0 s) (Y (x - x0) s - XX x0 s - U (x - x0) s)) +
              norm (R (XX x0 s) (Y (x - x0) s)))"
            using J_in_existence_ivl[OF x_in_ball] norm_triangle_ineq
            by (auto intro!: continuous_intros integral_le)
          also have "... =
            integral {a..b} (\<lambda>s. norm (f' (XX x0 s) (Y (x - x0) s - XX x0 s - U (x - x0) s))) +
            integral {a..b} (\<lambda>s. norm (R (XX x0 s) (Y (x - x0) s)))"
            using J_in_existence_ivl[OF x_in_ball]
            by (auto intro!: continuous_intros integral_add)
          also have "... \<le> N * integral {a..b} ?g + ?C" (is "?l1 + ?r1 \<le> _")
          proof(rule add_mono)
            have "?l1 \<le> integral {a..b} (\<lambda>s. norm (f' (XX x0 s)) * norm (Y (x - x0) s - XX x0 s - U (x - x0) s))"
              using norm_blinfun J_in_existence_ivl[OF x_in_ball]
              by (auto intro!: continuous_intros integral_le)

            also have "... \<le> integral {a..b} (\<lambda>s. N * norm (Y (x - x0) s - XX x0 s - U (x - x0) s))"
              using J_in_existence_ivl[OF x_in_ball]
              by (intro integral_le)
                (auto intro!: continuous_intros mult_right_mono
                  dest!: N_ineq[OF \<open>{a..b} \<subseteq> J\<close>[THEN subsetD]])
            also have "... = N * integral {a..b} (\<lambda>s. norm ((Y (x - x0) s - XX x0 s - U (x - x0) s)))"
              unfolding real_scaleR_def[symmetric]
              by(rule integral_cmul)
            finally show "?l1 \<le> N * integral {a..b} ?g" .
          next
            have "?r1 \<le> integral {a..b} (\<lambda>s. e1 * dist (XX x0 s) (Y (x - x0) s))"
              using J_in_existence_ivl[OF x_in_ball] \<open>0 < e_domain\<close> dist_XX_Y2 \<open>0 < e_domain2\<close>
              by (intro integral_le)
                (force
                  intro!: continuous_intros taylor_expansion(3) order_trans[OF infdist_le]
                   dest!: \<open>{a..b} \<subseteq> J\<close>[THEN subsetD]
                   intro: less_imp_le
                   simp: dist_commute H_def)+
            also have "... \<le> integral {a..b} (\<lambda>s. e1 * (dist x0 x * exp (K * \<bar>t\<bar>)))"
              apply(rule integral_le)
              subgoal using J_in_existence_ivl[OF x_in_ball] by (force intro!: continuous_intros)
              subgoal by force
              subgoal by (force dest!: \<open>{a..b} \<subseteq> J\<close>[THEN subsetD]
                intro!: less_imp_le[OF \<open>0 < e1\<close>] mult_left_mono[OF dist_XX_Y])
              done
            also have "... \<le> ?C"
              using \<open>s \<in> J\<close> x_x0_dist \<open>0 < e1\<close> \<open>{a..b} \<subseteq> J\<close> \<open>0 < \<bar>t\<bar>\<close> t0_def t1_def
              by (auto simp: integral_const_real J_def(1))
            finally show "?r1 \<le> ?C" .
          qed
          finally show ?thesis
            by simp
        qed
        have g_continuous: "continuous_on J ?g"
          using J_in_existence_ivl[OF x_in_ball] J_in_existence
          using J_def(1) U_continuous
          by (auto simp: J_def intro!: continuous_intros)
        note [continuous_intros] = continuous_on_subset[OF g_continuous]
        have C_gr_zero: "0 < ?C"
          using \<open>0 < \<bar>t\<bar>\<close> \<open>0 < e1\<close> x_x0_dist(1)
          by (simp add: dist_commute)
        have "0 \<le> t \<or> t \<le> 0" by auto
        then have "?g t \<le> ?C * exp (N * \<bar>t\<bar>)"
        proof
          assume "0 \<le> t"
          moreover
          have "norm (Y (x - x0) t - XX x0 t - U (x - x0) t) \<le>
            \<bar>t\<bar> * dist x0 x * exp (K * \<bar>t\<bar>) * e1 * exp (N * t)"
            using \<open>t \<in> J\<close> J_def \<open>t0 \<le> 0\<close>
            by (intro gronwall[OF g_bound _ _ C_gr_zero \<open>0 < N\<close> \<open>0 \<le> t\<close> order.refl])
              (auto intro!: continuous_intros simp: )
          ultimately show ?thesis by simp
        next
          assume "t \<le> 0"
          moreover
          have "norm (Y (x - x0) t - XX x0 t - U (x - x0) t) \<le>
            \<bar>t\<bar> * dist x0 x * exp (K * \<bar>t\<bar>) * e1 * exp (- N * t)"
            using \<open>t \<in> J\<close> J_def \<open>0 \<le> t1\<close>
            by (intro gronwall_left[OF g_bound _ _ C_gr_zero \<open>0 < N\<close> order.refl \<open>t \<le> 0\<close>])
              (auto intro!: continuous_intros)
          ultimately show ?thesis
            by simp
        qed
        also have "... = dist x x0 * (\<bar>t\<bar> * exp (K * \<bar>t\<bar>) * e1 * exp (N * \<bar>t\<bar>))"
          by (auto simp: dist_commute)
        also have "... < norm (x - x0) * e"
          unfolding e1_def
          using \<open>e' < e\<close> \<open>0 < \<bar>t\<bar>\<close> \<open>0 < e1\<close> x_x0_dist(1)
          by (simp add: dist_norm)
        finally show "norm ((Y (x - x0) t - XX x0 t - U (x - x0) t) /\<^sub>R norm (x - x0)) < e"
          by (simp, metis x_x0_dist(1) dist_norm divide_inverse mult.commute pos_divide_less_eq)
      qed
    qed
  qed
qed

lemma local_lipschitz_A:
  "OT \<subseteq> existence_ivl x0 \<Longrightarrow> local_lipschitz OT (OS::('a \<Rightarrow>\<^sub>L 'a) set) (\<lambda>t. op o\<^sub>L (A x0 t))"
  by (rule local_lipschitz_on_subset[OF _ _ subset_UNIV, where T="existence_ivl x0"])
     (auto simp: split_beta' A_def XX_def
      intro!: c1_implies_local_lipschitz[where f'="\<lambda>(t, x). comp3 (f' (flow x0 t))"]
        derivative_eq_intros blinfun_eqI ext
        continuous_intros flow_in_domain)

lemma total_derivative_ll_on_open:
  "ll_on_open (\<lambda>t. blinfun_compose (A x0 t)) (existence_ivl x0) (UNIV::('a \<Rightarrow>\<^sub>L 'a) set)"
  by standard (auto intro!: continuous_intros local_lipschitz_A[OF order_refl])

interpretation mvar: ll_on_open "\<lambda>t. blinfun_compose (A x0 t)" "existence_ivl x0" "UNIV::('a \<Rightarrow>\<^sub>L 'a) set"
  by (rule total_derivative_ll_on_open)

lemma wholevar_existence_ivl_eq_existence_ivl:\<comment>\<open>TODO: unify with @{thm varexivl_eq_exivl}\<close>
  assumes "t \<in> existence_ivl x0"
  shows "mvar.existence_ivl t = (\<lambda>_. existence_ivl x0)"
proof (rule ext, rule mvar.existence_ivl_eq_domain)
  fix s t x
  assume s: "s \<in> existence_ivl x0" and t: "t \<in> existence_ivl x0"
  then have "{s .. t} \<subseteq> existence_ivl x0"
    by (intro ivl2_subset_existence_ivl[OF x0_def])
  then have "continuous_on {s .. t} (A x0)"
    by (auto intro!: continuous_intros)
  then have "compact (A x0 ` {s .. t})"
    using compact_Icc
    by (rule compact_continuous_image)
  then obtain B where B: "\<And>u. u \<in> {s .. t} \<Longrightarrow> norm (A x0 u) \<le> B"
    by (force dest!: compact_imp_bounded simp: bounded_iff)
  show "\<exists>M L. \<forall>t\<in>{s .. t}. \<forall>x\<in>UNIV. norm (A x0 t o\<^sub>L x) \<le> M + L * norm x"
    unfolding o_def
    by (rule exI[where x=0], rule exI[where x=B])
      (auto intro!: order_trans[OF norm_blinfun_compose] mult_right_mono B)
qed (auto intro: assms)

lemma
  assumes "t \<in> existence_ivl x0"
  shows "continuous_on (UNIV \<times> existence_ivl x0) (\<lambda>(x, ta). mvar.flow t x ta)"
proof -
  from mvar.flow_continuous_on_state_space[OF assms,
    unfolded wholevar_existence_ivl_eq_existence_ivl[OF assms]]
  show "continuous_on (UNIV \<times> existence_ivl x0) (\<lambda>(x, ta). mvar.flow t x ta)" .
qed

definition "W = mvar.flow 0 id_blinfun"

lemma var_eq_mvar:
  assumes "t0 \<in> existence_ivl x0"
  assumes "t \<in> existence_ivl x0"
  shows "var.flow t0 i t = mvar.flow t0 id_blinfun t i"
  by (rule var.flow_unique)
     (auto intro!: assms derivative_eq_intros mvar.flow_has_derivative
       simp: varexivl_eq_exivl assms has_vector_derivative_def blinfun.bilinear_simps
        wholevar_existence_ivl_eq_existence_ivl)

end

subsection \<open>Differentiability of the flow\<close>

text \<open> \<open>U t\<close>, i.e. the solution of the variational equation, is the space derivative at the initial
  value \<open>x0\<close>. \<close>
lemma flow_dx_derivative:
assumes "x0 \<in> X"
assumes "t \<in> existence_ivl x0"
shows "((\<lambda>x0. flow x0 t) has_derivative (\<lambda>z. U x0 z t)) (at x0)"
  unfolding has_derivative_at
  apply(rule conjI[OF bounded_linear_U[OF \<open>x0 \<in> X\<close>]])
  subgoal using assms by force
  subgoal using assms(1,2)
    by (intro iffD1[OF LIM_equal proposition_17_6_weak[OF assms]])
      (simp add: diff_diff_add XX_def Y_def U_def inverse_eq_divide)
  done

lemma flow_dx_derivative_blinfun:
assumes "x0 \<in> X"
assumes "t \<in> existence_ivl x0"
shows "((\<lambda>x. flow x t) has_derivative Blinfun (\<lambda>z. U x0 z t)) (at x0)"
by (rule has_derivative_Blinfun[OF flow_dx_derivative[OF assms]])

definition "flowderiv x0 t = comp12 (W x0 t) (blinfun_scaleR_left (f (flow x0 t)))"

lemma flowderiv_eq: "flowderiv x0 t (\<xi>\<^sub>1, \<xi>\<^sub>2) = (W x0 t) \<xi>\<^sub>1 + \<xi>\<^sub>2 *\<^sub>R f (flow x0 t)"
  by (auto simp: flowderiv_def)

lemma W_continuous_on: "continuous_on (Sigma X existence_ivl) (\<lambda>(x0, t). W x0 t)"
  \<comment>\<open>TODO: somewhere here is hidden continuity wrt rhs of ODE, extract it!\<close>
  unfolding continuous_on split_beta'
proof (safe intro!: tendstoI)
  fix e'::real and t x assume x: "x \<in> X" and tx: "t \<in> existence_ivl x" and e': "e' > 0"
  let ?S = "Sigma X existence_ivl"

  have "(x, t) \<in> ?S" using x tx by auto
  from open_prod_elim[OF open_state_space this]
  obtain OX OT where OXOT: "open OX" "open OT" "(x, t) \<in> OX \<times> OT" "OX \<times> OT \<subseteq> ?S"
    by blast
  then obtain dx dt
  where dx: "dx > 0" "cball x dx \<subseteq> OX"
    and dt: "dt > 0" "cball t dt \<subseteq> OT"
    by (force simp: open_contains_cball)

  from OXOT dt dx have "cball t dt \<subseteq> existence_ivl x" "cball x dx \<subseteq> X" by auto

  interpret one: ll_on_open "(\<lambda>t. op o\<^sub>L (A x t))" "existence_ivl x" "UNIV::('a\<Rightarrow>\<^sub>L'a) set"
    by (rule total_derivative_ll_on_open) fact

  have one_exivl: "one.existence_ivl 0 = (\<lambda>_. existence_ivl x)"
    by (rule wholevar_existence_ivl_eq_existence_ivl[OF \<open>x \<in> X\<close> existence_ivl_zero[OF \<open>x \<in> X\<close>]])

  have *: "closed ({t .. 0} \<union> {0 .. t})" "{t .. 0} \<union> {0 .. t} \<noteq> {}"
    by auto
  let ?T = "{t .. 0} \<union> {0 .. t} \<union> cball t dt"
  have "compact ?T"
    by (auto intro!: compact_Un)
  have "?T \<subseteq> existence_ivl x"
    by (intro Un_least ivl_subset_existence_ivl' ivl_subset_existence_ivl \<open>x \<in> X\<close>
      \<open>t \<in> existence_ivl x\<close> \<open>cball t dt \<subseteq> existence_ivl x\<close>)

  have "compact (one.flow 0 id_blinfun ` ?T)" 
    using \<open>?T \<subseteq> _\<close> \<open>x \<in> X\<close>
      wholevar_existence_ivl_eq_existence_ivl[OF \<open>x \<in> X\<close> existence_ivl_zero[OF \<open>x \<in> X\<close>]]
    by (auto intro!: \<open>0 < dx\<close> compact_continuous_image \<open>compact ?T\<close>
      continuous_on_subset[OF one.flow_continuous_on])

  let ?line = "one.flow 0 id_blinfun ` ?T"
  let ?X = "{x. infdist x ?line \<le> dx}"
  have "compact ?X"
    using \<open>?T \<subseteq> _\<close> \<open>x \<in> X\<close>
      wholevar_existence_ivl_eq_existence_ivl[OF \<open>x \<in> X\<close> existence_ivl_zero[OF \<open>x \<in> X\<close>]]
    by (auto intro!: compact_infdist_le \<open>0 < dx\<close> compact_continuous_image compact_Un
      continuous_on_subset[OF one.flow_continuous_on ])

  from one.local_lipschitz \<open>?T \<subseteq> _\<close>
  have llc: "local_lipschitz ?T ?X (\<lambda>t. op o\<^sub>L (A x t))"
    by (rule local_lipschitz_on_subset) auto

  have cont: "\<And>xa. xa \<in> ?X \<Longrightarrow> continuous_on ?T (\<lambda>t. A x t o\<^sub>L xa)"
    using \<open>?T \<subseteq> _\<close>
    by (auto intro!: continuous_intros \<open>x \<in> X\<close>)

  from local_lipschitz_on_compact_implies_lipschitz[OF llc \<open>compact ?X\<close> \<open>compact ?T\<close> cont]
  obtain K' where K': "\<And>ta. ta \<in> ?T \<Longrightarrow> lipschitz ?X (op o\<^sub>L (A x ta)) K'"
    by blast
  define K where "K = abs K' + 1"
  have "K > 0"
    by (simp add: K_def)
  have K: "\<And>ta. ta \<in> ?T \<Longrightarrow> lipschitz ?X (op o\<^sub>L (A x ta)) K"
    by (auto intro!: lipschitzI mult_right_mono order_trans[OF lipschitzD[OF K']] simp: K_def)

  have ex_ivlI: "\<And>y. y \<in> cball x dx \<Longrightarrow> ?T \<subseteq> existence_ivl y"
    using dx dt OXOT
    by (intro Un_least ivl_subset_existence_ivl' ivl_subset_existence_ivl; force)

  have cont: "continuous_on ((?T \<times> ?X) \<times> cball x dx) (\<lambda>((ta, xa), y). (A y ta o\<^sub>L xa))"
    using \<open>cball x dx \<subseteq> X\<close> ex_ivlI
    by (force intro!: continuous_intros simp: split_beta' )

  have "one.flow 0 id_blinfun t \<in> one.flow 0 id_blinfun ` ({t..0} \<union> {0..t} \<union> cball t dt)"
    by auto
  then have mem: "(t, one.flow 0 id_blinfun t, x) \<in> ?T \<times> ?X \<times> cball x dx"
    by (auto simp: \<open>0 < dx\<close> less_imp_le)

  define e where "e = min e' (dx / 2) / 2"
  have "e > 0" using \<open>e' > 0\<close> by (auto simp: e_def \<open>0 < dx\<close>)
  define d where "d = e * K / (exp (K * (abs t + abs dt + 1)) - 1)"
  have "d > 0" by (auto simp: d_def intro!: mult_pos_pos divide_pos_pos \<open>0 < e\<close> \<open>K > 0\<close>)

  have cmpct: "compact (?T \<times> ?X \<times> cball x dx)" "compact (?T \<times> ?X)"
    using \<open>compact ?T\<close> \<open>compact ?X\<close>
    by (auto intro!: compact_cball compact_Times)

  have compact_line: "compact ?line"
    using \<open>{t..0} \<union> {0..t} \<union> cball t dt \<subseteq> existence_ivl x\<close> one_exivl
    by (force intro!: compact_continuous_image \<open>compact ?T\<close> continuous_on_subset[OF one.flow_continuous_on] simp: \<open>x \<in> X\<close>)

  from continuous_on_compact_product_lemma[OF cont cmpct(2) compact_cball \<open>0 < d\<close>]
  obtain d' where d': "d' > 0"
    "\<And>ta xa xa' y. ta \<in> ?T \<Longrightarrow> xa \<in> ?X \<Longrightarrow> xa'\<in>cball x dx \<Longrightarrow> y\<in>cball x dx \<Longrightarrow> dist xa' y < d' \<Longrightarrow>
      dist (A xa' ta o\<^sub>L xa) (A y ta o\<^sub>L xa) < d"
    by auto

  {
    fix y
    assume dxy: "dist x y < d'"
    assume "y \<in> cball x dx"
    then have "y \<in> X"
      using dx dt OXOT by force+

    interpret two: ll_on_open "(\<lambda>t. op o\<^sub>L (A y t))" "existence_ivl y" "UNIV::('a\<Rightarrow>\<^sub>L'a) set"
      by (rule total_derivative_ll_on_open) fact
    have two_exivl: "two.existence_ivl 0 = (\<lambda>_. existence_ivl y)"
      by (rule wholevar_existence_ivl_eq_existence_ivl[OF \<open>y \<in> X\<close> existence_ivl_zero[OF \<open>y \<in> X\<close>]])

    let ?X' = "\<Union>x \<in> ?line. ball x dx"
    have "open ?X'" by auto
    have "?X' \<subseteq> ?X"
      by (auto intro!: infdist_le2 simp: dist_commute)

    interpret oneR: ll_on_open "(\<lambda>t. op o\<^sub>L (A x t))" "existence_ivl x" ?X'
      by standard (auto intro!: \<open>x \<in> X\<close> continuous_intros local_lipschitz_A[OF \<open>x \<in> X\<close> order_refl])
    interpret twoR: ll_on_open "(\<lambda>t. op o\<^sub>L (A y t))" "existence_ivl y" ?X'
      by standard (auto intro!: \<open>y \<in> X\<close> continuous_intros local_lipschitz_A[OF \<open>y \<in> X\<close> order_refl])
    interpret both:
      two_ll_on_open "(\<lambda>t. op o\<^sub>L (A x t))" "existence_ivl x" "(\<lambda>t. op o\<^sub>L (A y t))" "existence_ivl y" ?X' ?T "id_blinfun" d K
    proof unfold_locales
      show mem_codom: "id_blinfun \<in> ?X'"
        using \<open>0 < dx\<close> \<open>x \<in> X\<close>
        by (auto intro!: bexI[where x=0])
      show zero_x: "0 \<in> existence_ivl x" and zero_y: "0 \<in> existence_ivl y" and "0 < K"
        by (auto simp:  \<open>x \<in> X\<close> \<open>0 < dx\<close> \<open>0 < K\<close>
          intro!: existence_ivl_zero \<open>x \<in> X\<close> \<open>y \<in> X\<close> bexI[where x=0])
      show iv_in: "0 \<in> {t..0} \<union> {0..t} \<union> cball t dt"
        by auto
      show "is_interval ({t..0} \<union> {0..t} \<union> cball t dt)"
        by (auto simp: is_interval_def dist_real_def)
      show "{t..0} \<union> {0..t} \<union> cball t dt \<subseteq> oneR.existence_ivl 0 id_blinfun"
        apply (rule oneR.maximal_existence_flow[OF _ _ _ refl, where x="one.flow 0 id_blinfun"])
        subgoal by (simp add: \<open>x \<in> X\<close>)
        subgoal by fact
        subgoal apply (rule ivp.is_solutionI)
          subgoal using iv_in mem_codom by unfold_locales auto
          subgoal using \<open>x \<in> X\<close> by simp
          subgoal
            using \<open>x \<in> X\<close> \<open>?T \<subseteq> _\<close>
            by (auto simp: one_exivl
              intro!: has_vector_derivative_at_within[OF one.flow_has_vector_derivative])
          subgoal using \<open>x \<in> X\<close> \<open>dx > 0\<close> by simp force
          done
        subgoal by fact
        subgoal by fact
        subgoal by fact
        done
      fix s assume s: "s \<in> ?T"
      then show "lipschitz ?X' (op o\<^sub>L (A x s)) K"
        by (intro lipschitz_subset[OF K \<open>?X' \<subseteq> ?X\<close>]) auto
      fix j assume j: "j \<in> ?X'"
      show "norm ((A x s o\<^sub>L j) - (A y s o\<^sub>L j)) < d"
        unfolding dist_norm[symmetric]
        apply (rule d')
        subgoal by (rule s)
        subgoal using \<open>?X' \<subseteq> ?X\<close> j ..
        subgoal using \<open>dx > 0\<close> by simp
        subgoal using \<open>y \<in> cball x dx\<close> by simp
        subgoal using dxy by simp
        done
    qed
    have less_e: "norm (W x s - both.Y s) < e"
      if s: "s \<in> ?T \<inter> twoR.existence_ivl 0 id_blinfun" for s
    proof -
      from s have s_less: "\<bar>s\<bar> < \<bar>t\<bar> + \<bar>dt\<bar> + 1"
        by (auto simp: dist_real_def)
      note both.norm_X_Y_bound[rule_format, OF s]
      also have "d / K * (exp (K * \<bar>s\<bar>) - 1) =
          e * ((exp (K * \<bar>s\<bar>) - 1) / (exp (K * (\<bar>t\<bar> + \<bar>dt\<bar> + 1)) - 1))"
        by (simp add: d_def)
      also have "\<dots> < e * 1"
        by (rule mult_strict_left_mono[OF _ \<open>0 < e\<close>])
           (simp add: add_nonneg_pos \<open>0 < K\<close> \<open>0 < e\<close> s_less)
      also have "\<dots> = e" by simp
      also
      from s have s: "s \<in> ?T" by simp
      have "both.XX s = W x s"
        unfolding both.XX_def W_def[OF \<open>x \<in> X\<close>]
        apply (rule oneR.maximal_existence_flow[OF _ _ _ refl, where K="?T"])
        subgoal by (rule both.t0_in_T1)
        subgoal using \<open>0 < dx\<close> by (force simp: \<open>x \<in> X\<close> intro!: bexI[where x=0])
        subgoal
          apply (rule ivp.is_solutionI)
          subgoal using \<open>0 \<in> ?T\<close>
            by unfold_locales (auto intro!: bexI[where x=0] simp: \<open>x \<in> X\<close> \<open>0 < dx\<close>)
          subgoal by (simp add: \<open>x \<in> X\<close>)
          subgoal
            apply simp
            using \<open>cball t dt \<subseteq> existence_ivl x\<close>  one_exivl tx \<open>x \<in> X\<close> x
              \<open>?T \<subseteq> existence_ivl x\<close>
            by (auto intro!: has_vector_derivative_at_within[OF one.flow_has_vector_derivative])
          subgoal using \<open>0 < dx\<close> by simp force
          done
        subgoal by (rule both.J_ivl)
        subgoal by (rule both.t0_in_J)
        subgoal using \<open>?T \<subseteq> existence_ivl x\<close> by blast
        subgoal by (rule s)
        done
      finally show ?thesis .
    qed

    have "e < dx" using \<open>dx > 0\<close> by (auto simp: e_def)

    let ?i = "{x. infdist x (one.flow 0 id_blinfun ` ?T) \<le> e}"
    have 1: "?i \<subseteq> (\<Union>x\<in>one.flow 0 id_blinfun ` ?T. ball x dx)"
    proof -
      have cl: "closed ?line" "?line \<noteq> {}" using compact_line
        by (auto simp: compact_imp_closed)
      have "?i \<subseteq> (\<Union>x\<in>one.flow 0 id_blinfun ` ?T. cball x e)"
      proof safe
        fix x
        assume H: "infdist x ?line \<le> e"
        from infdist_attains_inf[OF cl, of x]
        obtain y where "y \<in> ?line" "infdist x ?line = dist x y" by auto
        then show "x \<in> (\<Union>x\<in>?line. cball x e)"
          using H
          by (auto simp: dist_commute)
      qed
      also have "\<dots> \<subseteq> (\<Union>x\<in>?line. ball x dx)"
        using \<open>e < dx\<close>
        by auto
      finally show ?thesis .
    qed
    have 2: "twoR.flow 0 id_blinfun s \<in> ?i"
      if "s \<in> ?T" "s \<in> twoR.existence_ivl 0 id_blinfun" for s
    proof -
      from that have sT: "s \<in> ?T \<inter> twoR.existence_ivl 0 id_blinfun"
        by force
      from less_e[OF this]
      have "dist (twoR.flow 0 id_blinfun s) (one.flow 0 id_blinfun s) \<le> e"
        unfolding W_def[OF \<open>x \<in> X\<close>] both.Y_def dist_commute dist_norm by simp
      then show ?thesis
        using sT by (force intro: infdist_le2)
    qed
    have T_subset: "?T \<subseteq> twoR.existence_ivl 0 id_blinfun"
      apply (rule twoR.subset_mem_compact_implies_subset_existence_interval[
          where K="{x. infdist x ?line \<le> e}"])
      subgoal using \<open>0 < dt\<close> by force
      subgoal by (rule both.J_ivl)
      subgoal using \<open>y \<in> cball x dx\<close> ex_ivlI by blast
      subgoal by (rule both.x0_in_X)
      defer
      subgoal using \<open>dt > 0\<close> by (intro compact_infdist_le) (auto intro!: compact_line \<open>0 < e\<close>)
      subgoal by (rule 1)
      subgoal by (rule 2)
      done
    also have "twoR.existence_ivl 0 id_blinfun \<subseteq> existence_ivl y"
      apply (rule twoR.existence_ivl_subset)
      subgoal by (rule both.t0_in_T2)
      subgoal
        using \<open>0 < dx\<close>
        by (force simp: \<open>x \<in> X\<close> intro!: bexI[where x=0])
      done
    finally have "?T \<subseteq> existence_ivl y" .
    have "norm (W x s - W y s) < e" if s: "s \<in> ?T" for s
    proof -
      from s have "s \<in> ?T \<inter> twoR.existence_ivl 0 id_blinfun" using T_subset by force
      from less_e[OF this] have "norm (W x s - both.Y s) < e" .
      also have "two.flow 0 id_blinfun s = twoR.flow 0 id_blinfun s"
        apply (rule two.maximal_existence_flow[OF _ _ _ refl, where K="?T"])
        subgoal by (rule both.t0_in_T2)
        subgoal by simp
        subgoal
          apply (rule ivp.is_solutionI)
          unfolding ivp.simps
          subgoal using \<open>0 \<in> ?T\<close> by unfold_locales auto
          subgoal unfolding ivp.simps
            by (rule twoR.flow_initial_time)
              (auto intro!: bexI[where x=0] simp: \<open>x \<in> X\<close> \<open>0 < dx\<close> \<open>y \<in> X\<close>)
          subgoal
            apply (rule has_vector_derivative_at_within)
            apply (rule twoR.flow_has_vector_derivative[THEN has_vector_derivative_eq_rhs])
            subgoal by (simp add: \<open>y \<in> X\<close>)
            subgoal by (force intro!: bexI[where x=0] simp: \<open>x \<in> X\<close> \<open>0 < dx\<close>)
            subgoal using \<open>?T \<subseteq> twoR.existence_ivl _ _\<close> by force
            subgoal by simp
            done
          subgoal by simp
          done
        subgoal by fact
        subgoal by fact
        subgoal by fact
        subgoal by fact
        done
      then have "both.Y s = W y s"
        unfolding both.Y_def W_def[OF \<open>y \<in> X\<close>]
        by simp
      finally show ?thesis .
    qed
  } note cont_data = this
  have "\<forall>\<^sub>F (y, s) in at (x, t) within ?S. dist x y < d'"
    unfolding at_within_open[OF \<open>(x, t) \<in> ?S\<close> open_state_space] UNIV_Times_UNIV[symmetric]
    using \<open>d' > 0\<close>
    by (intro eventually_at_Pair_within_TimesI1)
      (auto simp: eventually_at less_imp_le dist_commute)
  moreover
  have "\<forall>\<^sub>F (y, s) in at (x, t) within ?S. y \<in> cball x dx"
    unfolding at_within_open[OF \<open>(x, t) \<in> ?S\<close> open_state_space] UNIV_Times_UNIV[symmetric]
    using \<open>dx > 0\<close>
    by (intro eventually_at_Pair_within_TimesI1)
      (auto simp: eventually_at less_imp_le dist_commute)
  moreover
  have "\<forall>\<^sub>F (y, s) in at (x, t) within ?S. s \<in> ?T"
    unfolding at_within_open[OF \<open>(x, t) \<in> ?S\<close> open_state_space] UNIV_Times_UNIV[symmetric]
    using \<open>dt > 0\<close>
    by (intro eventually_at_Pair_within_TimesI2)
      (auto simp: eventually_at less_imp_le dist_commute)
  moreover
  have "0 \<in> existence_ivl x" by (simp add: \<open>x \<in> X\<close>)
  have "\<forall>\<^sub>F x in at t within existence_ivl x. dist (one.flow 0 id_blinfun x) (one.flow 0 id_blinfun t) < e"
    using one.flow_continuous_on[OF \<open>0 \<in> existence_ivl x\<close>]
    using \<open>0 < e\<close> tx
    by (auto simp add: continuous_on one_exivl dest!: tendstoD)
  then have "\<forall>\<^sub>F (y, s) in at (x, t) within ?S. dist (W x s) (W x t) < e"
    using \<open>0 < e\<close>
    unfolding at_within_open[OF \<open>(x, t) \<in> ?S\<close> open_state_space] UNIV_Times_UNIV[symmetric] W_def[OF \<open>x \<in> X\<close>]
    by (intro eventually_at_Pair_within_TimesI2)
      (auto simp: at_within_open[OF tx open_existence_ivl])
  ultimately
  have "\<forall>\<^sub>F (y, s) in at (x, t) within ?S. dist (W y s) (W x t) < e'"
    apply eventually_elim
  proof (safe del: UnE, goal_cases)
    case (1 y s)
    have "dist (W y s) (W x t) \<le> dist (W y s) (W x s) + dist (W x s) (W x t)"
      by (rule dist_triangle)
    also
    have "dist (W x s) (W x t) < e"
      by (rule 1)
    also have "dist (W y s) (W x s) < e"
      unfolding dist_norm norm_minus_commute
      using 1
      by (intro cont_data)
    also have "e + e \<le> e'" by (simp add: e_def)
    finally show "dist (W y s) (W x t) < e'" by arith
  qed
  then show "\<forall>\<^sub>F ys in at (x, t) within ?S. dist (W (fst ys) (snd ys)) (W (fst (x, t)) (snd (x, t))) < e'"
    by (simp add: split_beta')
qed

lemma W_continuous_on_comp[continuous_intros]:
  assumes h: "continuous_on S h" and g: "continuous_on S g"
  shows "(\<And>s. s \<in> S \<Longrightarrow> h s \<in> X) \<Longrightarrow> (\<And>s. s \<in> S \<Longrightarrow> g s \<in> existence_ivl (h s)) \<Longrightarrow>
    continuous_on S (\<lambda>s. W (h s) (g s))"
  using continuous_on_compose[OF continuous_on_Pair[OF h g] continuous_on_subset[OF W_continuous_on]]
  by auto

lemma f_flow_continuous_on: "continuous_on (Sigma X existence_ivl) (\<lambda>(x0, t). f (flow x0 t))"
  using flow_continuous_on_state_space
  by (auto intro!: continuous_on_f flow_in_domain simp: split_beta')

lemma
  flow_has_space_derivative:
  assumes "t \<in> existence_ivl x0" "x0 \<in> X"
  shows "((\<lambda>x0. flow x0 t) has_derivative W x0 t) (at x0)"
  by (rule flow_dx_derivative_blinfun[THEN has_derivative_eq_rhs])
    (simp_all add: var_eq_mvar assms U_def blinfun.blinfun_apply_inverse W_def)

lemma
  flow_has_flowderiv:
  assumes "t \<in> existence_ivl x0" "x0 \<in> X"
  shows "((\<lambda>(x0, t). flow x0 t) has_derivative flowderiv x0 t) (at (x0, t) within Sigma X existence_ivl)"
proof -
  from open_state_space assms obtain e' where e': "e' > 0" "ball (x0, t) e' \<subseteq> Sigma X existence_ivl"
    by (force simp: open_contains_ball)
  define e where "e = e' / sqrt 2"
  have "0 < e" using e' by (auto simp: e_def)
  have "ball x0 e \<times> ball t e \<subseteq> ball (x0, t) e'"
    by (auto simp: dist_prod_def real_sqrt_sum_squares_less e_def)
  also note e'(2)
  finally have subs: "ball x0 e \<times> ball t e \<subseteq> Sigma X existence_ivl" .


  have d1: "((\<lambda>x0. flow x0 s) has_derivative blinfun_apply (W y s)) (at y within ball x0 e)"
    if "y \<in> ball x0 e" "s \<in> ball t e" for y s
    using subs that
    by (subst at_within_open; force intro!: flow_has_space_derivative)
  have d2: "(flow y has_derivative blinfun_apply (blinfun_scaleR_left (f (flow y s)))) (at s within ball t e)"
    if "y \<in> ball x0 e" "s \<in> ball t e" for y s
    using subs that
    unfolding has_vector_derivative_eq_has_derivative_blinfun[symmetric]
    by (subst at_within_open; force intro!: flow_has_vector_derivative)
  have "((\<lambda>(x0, t). flow x0 t) has_derivative flowderiv x0 t) (at (x0, t) within ball x0 e \<times> ball t e)"
    using subs
    unfolding UNIV_Times_UNIV[symmetric]
    by (intro has_derivative_partialsI[OF d1 d2, THEN has_derivative_eq_rhs])
      (auto intro!: \<open>0 < e\<close> continuous_intros flow_in_domain flow_continuous_on_state_space_comp
        simp: flowderiv_def split_beta')
  then show ?thesis
    by (auto simp: at_within_open[OF _ open_state_space] at_within_open[OF _ open_Times] assms \<open>0 < e\<close>)
qed

lemma flowderiv_continuous_on: "continuous_on (Sigma X existence_ivl) (\<lambda>(x0, t). flowderiv x0 t)"
  apply (auto simp: flowderiv_def split_beta' intro!: )
  apply (subst blinfun_of_matrix_works[where f="comp12 (W (fst x) (snd x))
            (blinfun_scaleR_left (f (flow (fst x) (snd x))))" for x, symmetric])
  apply (auto intro!: continuous_intros flow_in_domain)
  done

end \<comment>\<open>@{thm c1_on_open_euclidean_anchor}\<close>

end