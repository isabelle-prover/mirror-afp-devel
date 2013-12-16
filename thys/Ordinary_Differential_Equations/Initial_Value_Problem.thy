header{* Initial Value Problems *}
theory Initial_Value_Problem
imports Bounded_Continuous_Function
begin

subsection {* Lipschitz continuity *}
text{*\label{sec:lipschitz}*}

definition lipschitz
  where "lipschitz t f L \<longleftrightarrow> (\<forall>x \<in> t. \<forall>y\<in>t. dist (f x) (f y) \<le> L * dist x y)"

lemma lipschitzI:
  assumes "\<And>x y. x \<in> t \<Longrightarrow> y \<in> t \<Longrightarrow> dist (f x) (f y) \<le> L * dist x y"
  shows "lipschitz t f L"
using assms unfolding lipschitz_def by auto

lemma lipschitzD:
  assumes "lipschitz t f L"
  assumes "x \<in> t" "y \<in> t"
  shows "dist (f x) (f y) \<le> L * dist x y"
using assms unfolding lipschitz_def by simp

lemma lipschitz_subset:
  assumes "lipschitz D f L"
  assumes "D' \<subseteq> D"
  shows "lipschitz D' f L"
  using assms by (auto intro: lipschitzI dest: lipschitzD)

subsection {* Solutions of IVPs *}
text{*\label{sec:solutions}*}

record 'a ivp =
  ivp_f :: "real \<times> 'a \<Rightarrow> 'a"
  ivp_t0 :: "real"
  ivp_x0 :: "'a"
  ivp_I :: "real set"
  ivp_D :: "'a set"

locale ivp =
  fixes i::"('a::ordered_euclidean_space) ivp"
  assumes iv_defined: "ivp_t0 i \<in> ivp_I i" "ivp_x0 i \<in> ivp_D i"
begin

abbreviation "t0 \<equiv> ivp_t0 i"
abbreviation "x0 \<equiv> ivp_x0 i"
abbreviation "I \<equiv> ivp_I i"
abbreviation "D \<equiv> ivp_D i"
abbreviation "f \<equiv> ivp_f i"

definition is_solution where "is_solution x \<longleftrightarrow>
  x t0 = x0\<and>
  (\<forall>t\<in>I.
    (x has_vector_derivative f (t, x t))
      (at t within I) \<and>
     x t \<in> D)"

definition "solution = (SOME x. is_solution x)"

lemma is_solutionD:
  assumes "is_solution x"
  shows
  "x t0 = x0"
  "\<And>t. t \<in> I \<Longrightarrow> (x has_vector_derivative f (t, x t)) (at t within I)"
  "\<And>t. t \<in> I \<Longrightarrow> x t \<in> D"
  using assms
  by (auto simp: is_solution_def)

lemma solution_continuous_on:
  assumes "is_solution x"
  shows "continuous_on I x"
using is_solutionD[OF assms]
by (auto intro!: differentiable_imp_continuous_on
  simp add: differentiable_on_def differentiable_def has_vector_derivative_def)
  blast

lemma is_solutionI[intro]:
  assumes "x t0 = x0"
  assumes "\<And>t. t \<in> I \<Longrightarrow>
    (x has_vector_derivative f (t, x t)) (at t within I)"
  assumes "\<And>t. t \<in> I \<Longrightarrow> x t \<in> D"
  shows "is_solution x"
  using assms
  unfolding is_solution_def by simp

lemma is_solution_solution_eq:
  assumes "\<And>t. t \<in> I \<Longrightarrow> x t = y t"
  shows "is_solution x = is_solution y"
proof -
  { fix t assume "t \<in> I"
    hence "(y has_vector_derivative f (t, y t)) (at t within I) =
      (x has_vector_derivative f (t, y t)) (at t within I)"
      using assms
      by (subst has_vector_derivative_cong) auto }
  thus ?thesis using assms iv_defined by (auto simp: is_solution_def)
qed

lemma solution_on_subset:
  assumes "I' \<subseteq> I"
  assumes "t0 \<in> I'"
  assumes "is_solution x"
  shows "ivp.is_solution (i\<lparr>ivp_I := I'\<rparr>) x"
proof -
  interpret ivp': ivp "i\<lparr>ivp_I := I'\<rparr>" using assms iv_defined
    by unfold_locales simp_all
  show ?thesis
  using assms is_solutionD[OF `is_solution x`]
  by (intro ivp'.is_solutionI) (auto intro:
    has_vector_derivative_within_subset[where s="I"])
qed

lemma is_solution_on_superset_domain:
  assumes "is_solution y"
  assumes "D \<subseteq> D'"
  shows "ivp.is_solution (i \<lparr>ivp_D := D'\<rparr>) y"
proof -
  interpret ivp': ivp "i\<lparr>ivp_D:=D'\<rparr>" using assms iv_defined
    by unfold_locales auto
  show ?thesis
  using assms
  by (auto simp: is_solution_def ivp'.is_solution_def)
qed

lemma restriction_of_solution:
  assumes "t1 \<in> I'"
  assumes "x t1 \<in> D"
  assumes "I' \<subseteq> I"
  assumes x_sol: "is_solution x"
  shows "ivp.is_solution (i\<lparr>ivp_t0:=t1, ivp_x0:=x t1, ivp_I:=I'\<rparr>) x"
proof -
  interpret ivp': ivp "i\<lparr>ivp_t0:=t1, ivp_x0:=x t1, ivp_I:=I'\<rparr>"
    using assms iv_defined interval is_solutionD[OF x_sol]
    by unfold_locales simp_all
  show ?thesis
    using is_solutionD[OF x_sol] assms
    by (intro ivp'.is_solutionI) (auto intro:
    has_vector_derivative_within_subset[where t=I' and s=I]
      simp: interval)
qed

end

locale has_solution = ivp +
  assumes exists_solution: "\<exists>x. is_solution x"
begin

lemma is_solution_solution:
  shows "is_solution solution"
  using exists_solution unfolding solution_def by (rule someI_ex)

lemma solution:
  shows solution_t0: "solution t0 = x0"
    and solution_has_deriv: "\<And>t. t \<in> I \<Longrightarrow> (solution has_vector_derivative f (t, solution t)) (at t within I)"
    and solution_in_D: "\<And>t. t \<in> I \<Longrightarrow> solution t \<in> D"
  using is_solution_solution unfolding is_solution_def by auto

end

locale unique_solution = has_solution +
  assumes unique_solution: "\<And>y t. is_solution y \<Longrightarrow> t \<in> I \<Longrightarrow> y t = solution t"

lemma (in ivp) unique_solutionI:
  assumes "is_solution x"
  assumes "\<And>y t. is_solution y \<Longrightarrow> t \<in> I \<Longrightarrow> y t = x t"
  shows "unique_solution i"
proof
  show "\<exists>x. is_solution x" using assms by blast
  then interpret has_solution by unfold_locales
  fix y t
  assume "is_solution y" "t\<in>I"
  from assms(2)[OF this] assms(2)[OF is_solution_solution `t \<in> I`]
  show "y t = solution t" by simp
qed

locale interval = fixes a b assumes interval_notempty: "a \<le> b"

locale ivp_on_interval = ivp + interval t0 T for T +
  assumes interval: "I = {t0..T}"
begin

lemma is_solution_ext_cont:
  assumes "continuous_on I x"
  shows "is_solution (ext_cont x t0 T) = is_solution x"
  using assms iv_defined interval by (intro is_solution_solution_eq) simp_all

end

sublocale ivp_on_interval \<subseteq> interval t0 T by unfold_locales

subsubsection{* Connecting solutions *}
text{*\label{sec:combining-solutions}*}

locale connected_solutions =
  i1: ivp_on_interval i1 T1 + i2: ivp_on_interval i2 T2 + i: ivp_on_interval i T
  + i1: has_solution i1 + i2: has_solution i2
  for i::"('a::ordered_euclidean_space) ivp" and i1::"'a ivp"
  and i2::"'a ivp" and T and T1 and T2 +
  fixes y
  assumes conn_t: "i2.t0 = T1"
  assumes sol1: "i1.is_solution y"
  assumes conn_x: "i2.x0 = y T1"
  assumes conn_f: "i1.f (T1, y T1) =
    i2.f (T1, y T1)"
  assumes initial_value: "t0 = i1.t0" "x0 = i1.x0"
  assumes f: "f = (\<lambda>(t, x). if t \<le> T1 then i1.f (t, x) else i2.f (t, x))"
  assumes interval: "I = {t0..T2}"
  assumes dom:"D = i1.D" "D = i2.D" "T = T2"
begin

lemma I_subsets:
  shows I1_subset: "i1.I \<subseteq> I"
  and I2_subset: "i2.I \<subseteq> I"
  using i1.iv_defined i2.iv_defined
  by (simp_all add: conn_t interval i1.interval i2.interval initial_value)

definition connection where
  "connection t = (if t \<le> T1 then y t else i2.solution t)"

lemma is_solution_connection: "is_solution connection"
proof -
  {
    fix t
    assume "t0 \<le> t" "t \<le> T2"
    hence "(connection
      has_vector_derivative
      (if t \<le> T1 then
        i1.f (t, y t) else i2.f (t, i2.solution t)))
      (at t within {t0..T2})"
      using initial_value interval dom conn_t conn_x conn_f
        i1.is_solutionD[OF sol1] i2.solution
      i1.iv_defined i2.iv_defined
      unfolding i1.interval i2.interval connection_def[abs_def]
      by (intro linear_continuation) auto
  } note D = this
  {
    fix t
    assume "t0 \<le> t" "t \<le> T1"
    moreover
    hence "t0 \<le> t" "t \<le> T2" using i2.interval i2.iv_defined conn_t
      by auto
    note D[OF this]
    ultimately
    have "((\<lambda>t. if t \<le> T1 then y t else i2.solution t)
      has_vector_derivative f (t, connection t))
      (at t within {t0..T2})"
      by (simp add: f connection_def[abs_def])
  } moreover {
    fix t
    assume "t \<le> T2" "\<not> t \<le> T1"
    moreover
    hence "t0 \<le> t" "t \<le> T2" using i1.interval i1.iv_defined initial_value
      by auto
    moreover
    note D[OF this]
    ultimately
    have "((\<lambda>t. if t \<le> T1 then y t else i2.solution t)
      has_vector_derivative f (t, connection t))
            (at t within {t0..T2})"
      by (simp add: f connection_def[abs_def])
  } ultimately
  show "is_solution connection" using
    i1.interval i2.interval i1.iv_defined i2.iv_defined
    i1.is_solutionD[OF sol1] i2.solution conn_f conn_t conn_x
    initial_value f interval dom
    by (intro is_solutionI) (auto simp: connection_def[abs_def])
qed

end

sublocale connected_solutions \<subseteq> has_solution using is_solution_connection
  by unfold_locales auto

locale connected_unique_solutions =
  i1: unique_solution i1 + i2: unique_solution i2 +
  connected_solutions i i1 i2 T T1 T2 "i1.solution"
  for i::"('a::ordered_euclidean_space) ivp" and i1::"'a ivp"
  and i2::"'a ivp" and T and T1 and T2

sublocale connected_unique_solutions \<subseteq> unique_solution
proof (intro unique_solutionI)
  show "is_solution connection" using is_solution_connection .
  fix y t
  assume "is_solution y" "t \<in> I"
  have "i1.is_solution y"
  proof (intro i1.is_solutionI)
    show "y (i1.t0) = i1.x0"
      using is_solutionD(1)[OF `is_solution y`] initial_value by simp
  next
    fix ta
    assume "ta \<in> i1.I"
    hence "ta \<in> I" using I1_subset by auto
    from is_solutionD(2)[OF `is_solution y` this]
    have "(y has_vector_derivative i1.f (ta, y ta)) (at ta within I)"
      using `ta \<in> i1.I` by (simp add: f i1.interval)
    thus "(y has_vector_derivative i1.f (ta, y ta)) (at ta within i1.I)"
      using I1_subset
      by (rule has_vector_derivative_within_subset)
    show "y ta \<in> i1.D" using is_solutionD(3)[OF `is_solution y` `ta \<in> I`]
      by (simp add: dom)
  qed
  have "i2.is_solution y"
  proof (intro i2.is_solutionI)
    have "i1.solution T1 = y T1"
      using i1.unique_solution[OF `i1.is_solution y`] i1.interval i1.iv_defined
      by simp
    thus "y (i2.t0) = i2.x0"
      by (simp add: conn_t conn_x)
    fix ta
    assume "ta \<in> i2.I"
    hence "ta \<in> I" using I2_subset by auto
    from is_solutionD(2)[OF `is_solution y` this]
    have "(y has_vector_derivative i2.f (ta, y ta)) (at ta within I)"
      using `ta \<in> i2.I` conn_t conn_f `i1.solution T1 = y T1`
      by (cases "ta = T1") (simp_all add: f i2.interval)
    thus "(y has_vector_derivative i2.f (ta, y ta)) (at ta within i2.I)"
      using I2_subset
      by (rule has_vector_derivative_within_subset)
    show "y ta \<in> i2.D" using is_solutionD(3)[OF `is_solution y` `ta \<in> I`]
      using dom by simp
  qed
  from i1.unique_solution[OF `i1.is_solution y`, of t]
    i2.unique_solution[OF `i2.is_solution y`, of t]
  show "y t = connection t"
    using `t \<in> I`
    by (simp add: interval i1.interval i2.interval initial_value conn_t
      connection_def)
qed

subsection {* Picard-Lindeloef on bounded interval for @{term "D=UNIV"} *}
text{*\label{sec:pl-bi}*}
locale continuous = fixes I D f
  assumes continuous: "continuous_on (I\<times>D) f"

locale global_lipschitz =
  fixes I D f and L::real
  assumes lipschitz: "\<And>t. t\<in>I \<Longrightarrow> lipschitz D (\<lambda>x. f (t, x)) L" "0 \<le> L"

locale unique_on_bounded_strip = ivp_on_interval + continuous I D f +
  global_lipschitz I D f L for L +
  assumes lipschitz_bound: "(T - t0) * L < 1"
  assumes strip: "D = UNIV"

begin

text {* Picard Iteration *}

definition P_inner
  where
  "P_inner x t = x0 + integral {t0..t} (\<lambda>t. f (t, x t))"

definition P::"(real, 'a) bcontfun \<Rightarrow> (real, 'a) bcontfun" where
  "P x = ext_cont (P_inner x) t0 T"

lemma P_inner_bcontfun:
  assumes y_cont: "continuous_on I y"
  shows "(\<lambda>x. P_inner y (clamp t0 T x)) \<in> bcontfun"
proof -
  have "continuous_on {t0..T} (\<lambda>t. f (t, y t))"
    using continuous
    by (intro continuous_xy) (auto simp: strip interval
      intro: y_cont continuous_on_subset)
  thus ?thesis using interval iv_defined
    by (auto intro!: clamp_bcontfun continuous_on_intros
      indefinite_integral_continuous
      simp add: P_def P_inner_def)
qed

lemma lipschitz_P:
  shows "lipschitz UNIV P ((T - t0) * L)"
proof (rule lipschitzI)
  fix y z
  {
    fix y z::"real\<Rightarrow>'a"
    assume "y \<in> bcontfun"
    assume "z \<in> bcontfun"
    from bcontfunE[OF this] guess zb . note zb=this
    from bcontfunE[OF `y \<in> bcontfun`] guess yb . note yb=this
    {
      fix t
      assume t_bounds: "t0 \<le> t" "t \<le> T"
        --{* Instances of @{text continuous_on_subset} *}
      have y_cont: "continuous_on {t0..t} (\<lambda>t. y t)" using yb
        by (auto intro:continuous_on_subset)
      have "continuous_on {t0..T} (\<lambda>t. f (t, y t))"
        using continuous interval yb strip
        by (auto intro:continuous_xy continuous_on_subset)
      hence fy_cont[intro, simp]:
        "continuous_on {t0..t} (\<lambda>t. f (t, y t))"
        by (rule continuous_on_subset) (simp add: t_bounds)
      have z_cont: "continuous_on {t0..t} (\<lambda>t. z t)" using zb
        by (auto intro:continuous_on_subset)
      have "continuous_on {t0..T} (\<lambda>t. f (t, z t))" using zb
        continuous strip interval
        by (auto intro:continuous_xy continuous_on_subset)
      hence fz_cont[intro, simp]:
        "continuous_on {t0..t} (\<lambda>t. f (t, z t))"
        by (rule continuous_on_subset) (simp add: t_bounds)

      have "norm (P_inner y t - P_inner z t) =
        norm (integral {t0..t} (\<lambda>t. f (t, y t) - f (t, z t)))"
        using yb
        by (auto simp add: integral_sub P_inner_def)
      also have "... \<le> integral {t0..t} (\<lambda>t. norm (f (t, y t) - f (t, z t)))"
        by (auto intro!: integral_norm_bound_integral continuous_on_intros)
      also have "... \<le> integral {t0..t} (\<lambda>t. L * norm (y t - z t))"
        using y_cont z_cont lipschitz t_bounds strip interval
        by (auto intro!: integral_le continuous_on_intros
          simp add: dist_norm lipschitz_def)
      also have "... \<le> integral {t0..t} (\<lambda>t. L *
        norm (Abs_bcontfun y - Abs_bcontfun  z))"
        using norm_bounded[of "Abs_bcontfun y - Abs_bcontfun z"]
          y_cont z_cont lipschitz
        by (intro integral_le) (auto intro!: continuous_on_intros mult_left_mono
          simp add: Abs_bcontfun_inverse[OF `y \<in> bcontfun`]
          Abs_bcontfun_inverse[OF `z \<in> bcontfun`])
      also have "... =
        L * (t - t0) * norm (Abs_bcontfun y - Abs_bcontfun z)"
        using t_bounds by simp
      also have "... \<le> L * (T - t0) * norm (Abs_bcontfun y - Abs_bcontfun z)"
        using t_bounds zero_le_dist lipschitz
        by (auto intro!: mult_right_mono mult_left_mono)
      finally
      have "norm (P_inner y t - P_inner z t)
        \<le> L * (T - t0) * norm (Abs_bcontfun y - Abs_bcontfun z)" .
    }
    hence "dist (P (Abs_bcontfun y)) (P (Abs_bcontfun z)) \<le>
      L * (T - t0) * dist (Abs_bcontfun y) (Abs_bcontfun z)"
      using continuous `y \<in> bcontfun` `z \<in> bcontfun` interval iv_defined
      unfolding P_def dist_norm
      apply (intro norm_bound)
      apply (auto simp: Abs_bcontfun_inverse)
      unfolding ext_cont_def
      apply (subst Abs_bcontfun_inverse) defer
      apply (subst Abs_bcontfun_inverse) defer
      apply (simp add: clamp_def)
      unfolding Basis_real_def
      apply (auto intro!: P_inner_bcontfun elim!: bcontfunE intro: continuous_on_subset)
      done
  }
  from this[OF Rep_bcontfun Rep_bcontfun]
  show "dist (P y) (P z) \<le> (T - t0) * L * dist y z"
    unfolding Rep_bcontfun_inverse by (simp add: field_simps)
qed

definition fixed_point where
  "fixed_point = (THE x. P x = x)"

lemma fixed_point_unique: "\<exists>!x. P x = x"
  using lipschitz lipschitz_bound lipschitz_P interval
      complete_UNIV iv_defined
  by (intro banach_fix_type[where c="(T - t0)*L"])
     (auto intro: split_mult_pos_le simp: lipschitz_def)

lemma fixed_point:
  "P fixed_point =  fixed_point"
  unfolding fixed_point_def using fixed_point_unique by (rule theI')

lemma fixed_point_equality:
  assumes "P x = x"
  shows "fixed_point = x"
  unfolding fixed_point_def using fixed_point_unique assms by (rule the1_equality)

lemma fixed_point_continuous: "\<And>t. continuous_on I fixed_point"
  using bcontfunE[OF Rep_bcontfun[of fixed_point]]
  by (auto intro: continuous_on_subset)

lemma fixed_point_solution:
  shows "is_solution fixed_point"
proof
  have "fixed_point t0 = P fixed_point t0"
    unfolding fixed_point ..
  also have "... = x0"
    using interval iv_defined continuous fixed_point_continuous
    unfolding P_def P_inner_def[abs_def]
    by (subst ext_cont_cancel) (auto simp add: strip
  intro!: continuous_on_intros indefinite_integral_continuous integrable_continuous continuous_xy intro: continuous_on_subset)
  finally show "fixed_point t0 = x0" .
next
  fix t
  have U: "\<forall>t \<in> I. fixed_point t \<in> UNIV" by simp
  assume "t \<in> I" hence t_range: "t \<in> {t0..T}" by (simp add: interval)
  from has_vector_derivative_const
    integral_has_vector_derivative[
    OF continuous_xy[OF U continuous[simplified strip] fixed_point_continuous,
    simplified interval] t_range]
  have "((\<lambda>u. x0 + integral {t0..u}
         (\<lambda>x. f (x, fixed_point x))) has_vector_derivative
   0 + f (t, fixed_point t))
   (at t within {t0..T})"
    by (rule has_vector_derivative_add)
  hence "((P fixed_point) has_vector_derivative
    f (t, fixed_point t)) (at t within {t0..T})"
    unfolding P_def P_inner_def[abs_def]
    using t_range
    apply (subst has_vector_derivative_cong)
    apply (simp_all)
    using fixed_point_continuous continuous interval
    by (subst ext_cont_cancel) (auto simp add: strip
      intro!: continuous_on_intros indefinite_integral_continuous continuous_xy
      intro: continuous_on_subset)
  moreover
  have "fixed_point t \<in> D" unfolding strip by simp
  ultimately 
  show "(fixed_point has_vector_derivative
      f (t, fixed_point t)) (at t within I)"
    "fixed_point t \<in> D" unfolding fixed_point interval
    by simp_all
qed

end

subsubsection {* Existence of solution *}

sublocale unique_on_bounded_strip \<subseteq> has_solution
proof
  from fixed_point_solution
  show "\<exists>x. is_solution x" by blast
qed

lemma ext_cont_cong[cong]:
  assumes "t0 = s0"
  assumes "T = S"
  assumes "\<And>t. t \<in> {t0..T} \<Longrightarrow> f t = g t"
  assumes "continuous_on {t0..T} f"
  assumes "continuous_on {s0..S} g"
  assumes "t0 \<le> T"
  shows "ext_cont f t0 T = ext_cont g s0 S"
  unfolding assms ext_cont_def
  using assms clamp_in_interval[OF `t0 \<le> T`]
  by (subst Rep_bcontfun_inject[symmetric]) simp

lemma (in unique_on_bounded_strip) solution_fixed_point:
  "P (ext_cont solution t0 T) = ext_cont solution t0 T"
unfolding P_def
apply (rule ext_cont_cong)
using solution_continuous_on[OF is_solution_solution] interval interval_notempty
unfolding P_inner_def
apply simp_all
proof -
  fix t
  assume t_bounds: "t0 \<le> t \<and> t \<le> T"
  hence "\<And>t. t\<in>{t0..T} \<Longrightarrow>
    (ext_cont solution t0 T has_vector_derivative
      f (t, ext_cont solution t0 T t)) (at t within {t0..T})"
    using solution(2) unfolding interval using interval iv_defined
      solution_continuous_on[OF is_solution_solution]
    by (subst has_vector_derivative_cong) auto
  hence "\<forall>ta\<in>{t0..t}. (ext_cont solution t0 T has_vector_derivative
    f (ta, ext_cont solution t0 T ta)) (at ta within {t0..t})"
    using t_bounds interval iv_defined
    by (auto intro!:
      has_vector_derivative_within_subset[where t="{t0..t}" and s="{t0..T}"])
  hence "((\<lambda>t. f (t, ext_cont solution t0 T t)) has_integral
    ext_cont solution t0 T t - ext_cont solution t0 T t0) {t0..t}"
    using t_bounds by (intro fundamental_theorem_of_calculus) simp
  from this[THEN integral_unique]
  have "ext_cont solution t0 T t =
    ext_cont solution t0 T t0 +
    integral {t0..t} (\<lambda>t. f (t, ext_cont solution t0 T t))"
    using t_bounds by simp
  thus "x0 +
           integral {t0..t}
            (\<lambda>t. f (t, ext_cont solution t0 T t)) =
           solution t"
    using t_bounds solution_continuous_on[OF is_solution_solution]
      interval solution_t0
    by simp
next
  show "continuous_on {t0..T} (P_inner (ext_cont solution t0 T))"
    unfolding P_inner_def[abs_def] interval
    using continuous
    apply (intro continuous_on_intros integrable_continuous indefinite_integral_continuous continuous_xy[where U = UNIV])
    apply (auto simp: strip interval)
    unfolding ext_cont_def
    apply (subst Abs_bcontfun_inverse[OF clamp_bcontfun])
    using interval interval_notempty solution_continuous_on[OF is_solution_solution] clamp_continuous_on
    apply (auto)
    apply (rule continuous_on_subset)
    apply force
    apply simp
    done
qed

subsubsection {* Unique solution *}
text{*\label{sec:ivp-ubs}*}
sublocale unique_on_bounded_strip \<subseteq> unique_solution
proof
    --{* Every solution equals the fixed point *}
  fix z t
  assume "t \<in> I"
  assume "is_solution z"
  hence "continuous_on I z" using solution_continuous_on by simp
  hence is_solution_ext_cont_z: "is_solution (ext_cont z t0 T)"
    using is_solution_ext_cont interval `is_solution z` by simp
  hence z_sol:
    "ext_cont z t0 T t0 = x0"
    "(\<forall>t\<in>{t0..T}.
    (ext_cont z t0 T has_vector_derivative f (t, ext_cont z t0 T t)) (at t within {t0..T}))"
    by (auto simp add: is_solution_def interval)
  have "continuous_on I (ext_cont z t0 T)"
    using solution_continuous_on[OF is_solution_ext_cont_z] .
  {
    fix t
    assume t_bounds: "t \<in> {t0..T}"
    have "\<forall>ta\<in>{t0..t}.
      (ext_cont z t0 T has_vector_derivative f (ta, ext_cont z t0 T ta)) (at ta within {t0..t})"
      using t_bounds z_sol(2)        
      by (auto intro: has_vector_derivative_within_subset[where s="{t0..T}"])
    hence "((\<lambda>t. f (t, ext_cont z t0 T t)) has_integral
      ext_cont z t0 T t - ext_cont z t0 T t0) {t0..t}"
      using t_bounds
      by (intro fundamental_theorem_of_calculus) simp
    from this[THEN integral_unique]
    have "ext_cont z t0 T t = ext_cont z t0 T t0 + integral {t0..t} (\<lambda>t. f (t, ext_cont z t0 T t))"
      using t_bounds by simp
    hence "z t = x0 + integral {t0..t} (\<lambda>t. f (t, ext_cont z t0 T t))"
      using t_bounds `continuous_on I z` interval interval_notempty
        is_solutionD[OF `is_solution z`]
      by simp_all
  }
  note integral_rewrite = this
  have z_fix: "P (ext_cont z t0 T) = ext_cont z t0 T"
    unfolding P_def P_inner_def[abs_def]
    apply (rule ext_cont_cong)
    apply simp
    apply simp
    apply (subst integral_rewrite)
    apply simp apply simp
    apply (intro continuous_on_intros integrable_continuous indefinite_integral_continuous continuous_xy[where U = UNIV])
    using continuous strip interval `continuous_on I (ext_cont z t0 T)`
    `continuous_on I z` interval_notempty
    by simp_all 
      --{* z is bounded and continuous *}
  with fixed_point_equality have "fixed_point = ext_cont z t0 T"
    by simp
  hence "ext_cont z t0 T = ext_cont solution t0 T"
    using solution_fixed_point fixed_point_equality by simp
  hence "ext_cont z t0 T t = ext_cont solution t0 T t"
    by simp
  thus "z t = solution t" using `t \<in> I`
    `continuous_on I z` solution_continuous_on[OF is_solution_solution]
    using interval by simp
qed

subsection {* Picard-Lindeloef for @{term "D=UNIV"} *}
text{*\label{sec:pl-us}*}

locale unique_on_strip = ivp_on_interval + continuous I D f +
  global_lipschitz I D f L for L +
  assumes strip: "D = UNIV"

sublocale unique_on_strip \<subseteq> unique_solution
proof (cases "T = t0")
  assume "T = t0"
  then interpret has_solution
    using is_solution_def interval iv_defined
    by unfold_locales (auto intro!: exI[where x="(\<lambda>t. x0)"]
      simp add: has_vector_derivative_def
      has_derivative_within_alt bounded_linear_scaleR_left)
  show "unique_solution i"
    using `T=t0` interval solution_t0
    by unfold_locales (simp add: is_solution_def)
next
  assume "T \<noteq> t0" with interval iv_defined have interval: "I = {t0..T}" "t0 < T"
    by auto
  obtain n::nat and b where b: "b = (T - t0) / (Suc n)" and bL: "L * b < 1"
    by (rule, rule) (auto intro: order_le_less_trans real_natceiling_ge
    simp: natceiling_def)
  then interpret i': ivp_on_interval i "t0 + (Suc n) * b"
    using interval by unfold_locales simp_all
  from b have "b > 0" using interval iv_defined
    by (auto intro: divide_pos_pos)
  hence "b \<ge> 0" by simp
  from interval have "t0 * (real (Suc n) - 1) \<le> T * (real (Suc n) - 1)" by (cases n) auto
  hence ble: "t0 + b \<le> T" unfolding b by (auto simp add: field_simps)
  have subsetbase: "t0 + (Suc n) * b \<le> T" using i'.interval interval by auto

  interpret i': unique_solution "i\<lparr>ivp_I := {t0..t0 + real (Suc n) * b}\<rparr>"
    using subsetbase
  proof (induct n)
    case 0
    then interpret sol: unique_on_bounded_strip "i\<lparr>ivp_I:={t0..t0+b}\<rparr>" "t0 + b"
      using strip interval `b > 0` using bL continuous lipschitz
      by unfold_locales (auto intro: continuous_on_subset simp: ac_simps)
    show ?case by simp unfold_locales
  next
    case (Suc n)
    def nb \<equiv> "real (Suc n) * b"
    def snb \<equiv> "real (Suc (Suc n)) * b"
    note Suc = Suc[simplified nb_def[symmetric] snb_def[symmetric]]
    from `b > 0` nb_def snb_def have nbs_nonneg: "0 < snb" "0 < nb"
      by (simp_all add: zero_less_mult_iff)
    with `b>0` have nb_le_snb: "nb < snb" using nb_def snb_def
      by auto
    have [simp]: "snb + - nb = b"
    proof -
      have "snb + - (nb) = b * real (Suc (Suc n)) + - (b * real (Suc n))"
        by (simp add: ac_simps snb_def nb_def)
      thus ?thesis by (simp add: field_simps real_of_nat_Suc)
    qed
    def i1 \<equiv> "i\<lparr>ivp_I := {t0..t0 + nb}\<rparr>"
    def T1 \<equiv> "t0 + nb"
    interpret ivp1: ivp_on_interval i1 T1
      using iv_defined `nb > 0` by unfold_locales (auto simp: i1_def T1_def)
    interpret ivp1: unique_solution i1
      using nb_le_snb nbs_nonneg Suc continuous lipschitz by (simp add: i1_def)

    def i2 \<equiv> "i\<lparr>ivp_t0:=t0+nb, ivp_I:={t0 + nb..t0+snb},
      ivp_x0:=ivp1.solution (t0 + nb)\<rparr>"
    def T2 \<equiv> "t0 + snb"
    interpret ivp2: unique_on_bounded_strip i2 T2
      using bL Suc(2) nbs_nonneg strip `nb < snb` interval continuous lipschitz
      by unfold_locales (auto intro: continuous_on_subset
        simp: ac_simps i2_def T2_def, metis `snb + - nb = b` minus_real_def)
    def i \<equiv> "i\<lparr>ivp_I := {t0..t0 + real (Suc (Suc n)) * b}\<rparr>"
    def T \<equiv> "t0 + real (Suc (Suc n)) * b"
    interpret ivp_c: connected_unique_solutions i i1 i2 T T1 T2
      using `b > 0` iv_defined ivp1.is_solution_solution
      by unfold_locales (auto intro: mult_nonneg_nonneg
        simp: i1_def i2_def i_def T1_def T2_def T_def snb_def)
    show ?case unfolding i_def[symmetric] by unfold_locales
  qed
  show "unique_solution i"
    using i'.solution i'.unique_solution interval(1)[symmetric] i'.interval[symmetric]
    by unfold_locales auto
qed

subsection {* Picard-Lindeloef on rectangular domain *}
text{*\label{sec:pl-rect}*}
locale rectangle = ivp_on_interval +
  fixes b
  assumes b_nonneg: "b \<ge> 0"
  assumes rectangle: "D = {x0 - (\<Sum>i\<in>Basis. b *\<^sub>R i)..x0 + (\<Sum>i\<in>Basis. b *\<^sub>R i)}"

locale solution_in_rectangle = rectangle + continuous I D f +
  fixes B
  assumes f_bounded: "\<And>x t. t \<in> I \<Longrightarrow> x \<in> D \<Longrightarrow> norm (f (t, x)) \<le> B"
  assumes T_bounded: "T \<le> t0 + b / B"
begin

lemma B_nonneg: "B \<ge> 0"
proof -
  have "0 \<le> norm (f (t0, x0))" by simp
  also from iv_defined f_bounded have "... \<le> B" by simp
  finally show ?thesis by simp
qed

lemma solution_in_bounds:
  assumes x_sol: "ivp.is_solution (i\<lparr>ivp_f:=f', ivp_D:=D'\<rparr>) x"
  assumes "t \<in> {t0..T}" "D \<subseteq> D'"
  assumes f_eq: "\<And>t x. t\<in>{t0..T} \<Longrightarrow> x \<in> D \<Longrightarrow> f (t, x) = f' (t, x)"
  shows "x t \<in> D"
proof -
  interpret x_sol: ivp "i\<lparr>ivp_f:=f', ivp_D:=D'\<rparr>"
    using iv_defined assms by unfold_locales auto
  show ?thesis
  proof cases
    assume "b = 0 \<or> B = 0" with assms T_bounded interval_notempty have "t = t0"
      by auto
    thus ?thesis using iv_defined x_sol.is_solutionD[OF x_sol] by simp
  next
    assume "\<not>(b = 0 \<or> B = 0)"
    hence "b > 0" "B > 0" using B_nonneg b_nonneg by auto
    show ?thesis
    proof -
      from x_sol.solution_continuous_on[OF x_sol]
      have "continuous_on {t0..T} x" using interval by simp
      hence closed: "closed {t \<in> {t0..T}. norm (x t - x t0) \<in> {b..}}"
        by (intro continuous_closed_preimage continuous_on_intros) auto
          --{* No argument within @{term "{t0..T}"} makes @{term y} exceed @{term B} *}
      have exceeding: "{t \<in> {t0..T}. norm (x t - x t0) \<in> {b..}} \<subseteq> {T}"
      proof (rule ccontr)
        assume "\<not>{t \<in> {t0..T}. norm (x t - x t0) \<in> {b..}} \<subseteq> {T}"
        hence notempty: "{t \<in> {t0..T}. norm (x t - x t0) \<in> {b..}} \<noteq> {}"
          and not_max: "{t \<in> {t0..T}. norm (x t - x t0) \<in> {b..}} \<noteq> {T}" by auto
        from distance_attains_inf[OF closed this(1), of t0]
        obtain t where t_bound: "t \<in> {t0..T}" and exceeds: "norm (x t - x t0) \<in> {b..}"
          and min:
          "\<forall>t2\<in>{t0..T}. norm (x t2 - x t0) \<in> {b..} \<longrightarrow> dist t0 t \<le> dist t0 t2"
          by blast
        have lt: "t0 < t"
          using t_bound exceeds min
            eucl_le[of x0] eucl_le[where y=x0] diff_self `b>0`
          by (auto simp add: less_le) 
        have deriv:
          "\<forall>t\<in>{t0<..<t}. (x has_derivative (\<lambda>h. h *\<^sub>R f' (t, x t))) (at t)"
        proof
          fix s
          assume int:"s \<in> {t0<..<t}"
          hence "s \<in> {t0..T}" using assms t_bound by simp
          from x_sol.is_solutionD[OF x_sol] this t_bound
          show "(x has_derivative (\<lambda>h. h *\<^sub>R f' (s, x s))) (at s)"
            unfolding has_vector_derivative_def
            by (subst has_derivative_within_open[OF int, symmetric]) (auto intro!:
              has_derivative_within_subset[where t="{t0<..<t}"] simp add: interval)
        qed
        have der_x: "\<And>s. s \<in> {t0..t} \<Longrightarrow> (x has_vector_derivative f' (s, x s)) (at s within {t0..t})"
        proof -
          fix s
          assume "s \<in> {t0..t}"
          hence "s \<in> {t0..T}" using assms t_bound by simp
          from x_sol.is_solutionD[OF x_sol] this t_bound
          show "(x has_vector_derivative f' (s, x s)) (at s within {t0..t})"
            by (auto intro!: has_vector_derivative_within_subset[where t="{t0..t}"]
              simp add: interval)
        qed
        hence cont: "continuous_on {t0..t} x"
          by (auto intro!: differentiable_imp_continuous_on has_derivative_within_subset[where t="{t0..t}"]
            simp add: differentiable_on_def differentiable_def has_vector_derivative_def) blast
        from mvt_general[OF lt cont deriv] guess \<xi> .. note \<xi> = this
        have "norm (x t - x t0) < b"
        proof cases
          assume "f' (\<xi>, x \<xi>) = 0"
          with \<xi>(2) have "norm (x t - x t0) \<le> 0" by simp
          with `b > 0` show ?thesis by simp
        next
          assume f'_nonzero: "f' (\<xi>, x \<xi>) \<noteq> 0"
          note \<xi>(2)
          also
          have "t \<noteq> T"
            using t_bound exceeds min not_max by (auto simp: dist_norm)
          hence "norm ((t - t0) *\<^sub>R f' (\<xi>, x \<xi>)) < \<bar>T - t0\<bar> * norm (f' (\<xi>, x \<xi>))"
            using t_bound f'_nonzero by simp
          also
          have "\<xi> \<notin> {t \<in> {t0..T}. norm (x t - x t0) \<in> {b..}}"
          proof
            assume "\<xi> \<in> {t \<in> {t0..T}. norm (x t - x t0) \<in> {b..}}"
            with min have "dist t0 t \<le> dist t0 \<xi>" by simp
            thus "False" using t_bound \<xi> by (simp add: dist_real_def)
          qed
          with \<xi> t_bound have norm_lt: "norm (x \<xi> - x t0) < b" by auto
          have "x \<xi> \<ge> x0 - (\<Sum>i\<in>Basis. b *\<^sub>R i) \<and> x \<xi> \<le> x0 + (\<Sum>i\<in>Basis. b *\<^sub>R i)"
          proof (rule ccontr)
            assume "\<not> (x0 - (\<Sum>i\<in>Basis. b *\<^sub>R i) \<le> x \<xi> \<and> x \<xi> \<le> x0 + (\<Sum>i\<in>Basis. b *\<^sub>R i))"
            hence "\<exists>i\<in>Basis. \<not> x \<xi> \<bullet> i \<le> x0 \<bullet> i + b \<or> \<not> x0 \<bullet> i - b \<le> x \<xi> \<bullet> i"
              by (auto simp add: eucl_le[where x = "x \<xi>"] eucl_le[where y = "x \<xi>"] inner_simps)
            then guess i .. note i = this
            then have "i \<in> Basis" "b < norm ((x \<xi> - x t0) \<bullet> i)"
              using x_sol.is_solutionD[OF x_sol]
              by (auto simp: inner_simps)
            moreover have "... \<le> norm (x \<xi> - x t0)" using norm_nth_le[of i "x \<xi> - x t0"] i
              by simp
            ultimately
            show False using norm_lt by simp
          qed
          with \<xi> f_eq have "\<bar>T - t0\<bar> * norm (f' (\<xi>, x \<xi>)) \<le> \<bar>T - t0\<bar> * B"
            using f_bounded rectangle interval t_bound by auto
          also
          have "... \<le> b" using `b>0` f_bounded T_bounded interval iv_defined `B>0`
            by (simp add: field_simps abs_real_def)
          finally
          show "norm (x t - x t0) < b" .
        qed
        moreover
        from exceeds have "norm (x t - x t0) \<ge> b" by simp
        ultimately show False by simp
      qed
      show "x t \<in> D"
      proof cases
        assume "t = T"
        have "x t0 = x0" using x_sol.is_solutionD[OF x_sol] by simp
        have "x T \<ge> x0 - (\<Sum>i\<in>Basis. b *\<^sub>R i) \<and> x T \<le> x0 + (\<Sum>i\<in>Basis. b *\<^sub>R i)"
        proof (rule ccontr)
          assume not_le: "\<not> (x0 - (\<Sum>i\<in>Basis. b *\<^sub>R i) \<le> x T \<and> x T \<le> x0 + (\<Sum>i\<in>Basis. b *\<^sub>R i))"
          hence "\<exists>i\<in>Basis. \<not> x T \<bullet> i \<le> x0 \<bullet> i + b \<or> \<not> x0 \<bullet> i - b \<le> x T \<bullet> i"
            by (auto simp add: eucl_le[where x = "x T"] eucl_le[where y = "x T"] inner_simps)
          then guess i .. note i = this
          from i(2)
          show False
          proof safe
            assume H: "\<not> x T \<bullet> i \<le> x0 \<bullet> i + b"
            hence "\<exists>s\<in>{t0..T}. x s \<bullet> i = x0 \<bullet> i + b"
              using interval_notempty x_sol.solution_continuous_on[OF x_sol]
                `x t0 = x0` b_nonneg
              by (auto intro: ivt_increasing_component_on_1 simp: interval)
            then guess s .. note s = this
            have "s \<in> {t \<in> {t0..T}. norm (x t - x t0) \<in> {b..}}"
            proof safe
              have "b \<le> norm ((x s - x t0)\<bullet>i)"
                using s by (simp add: `x t0 = x0` inner_simps)
              also have "... \<le> norm (x s - x t0)"
                using i(1)
                by (rule norm_nth_le)
              finally show "b \<le> norm (x s - x t0)" .
            qed (insert s, simp)
            with exceeding have "s = T" by auto
            with s H show False by simp
          next
            assume H: "\<not> x0 \<bullet> i - b \<le> x T \<bullet> i"
            hence "\<exists>s\<in>{t0..T}. x s \<bullet> i = x0 \<bullet> i - b"
              using interval_notempty x_sol.solution_continuous_on[OF x_sol]
                `x t0 = x0` b_nonneg
              by (auto intro: ivt_decreasing_component_on_1 simp: interval)
            then guess s .. note s = this
            have "s \<in> {t \<in> {t0..T}. norm (x t - x t0) \<in> {b..}}"
            proof safe
              have "b \<le> norm ((x s - x t0)\<bullet>i)"
                using s by (simp add: `x t0 = x0` inner_simps)
              also have "... \<le> norm (x s - x t0)"
                using i(1)
                by (rule norm_nth_le)
              finally show "b \<le> norm (x s - x t0)" .
            qed (insert s, simp)
            with exceeding have "s = T" by auto
            with s H show False by simp
          qed
        qed
        with `t = T` show "x t \<in> D" by (simp add: rectangle)
      next
        assume "t \<noteq> T"
        have "x t \<ge> x0 - (\<Sum>i\<in>Basis. b *\<^sub>R i) \<and> x t \<le> x0 + (\<Sum>i\<in>Basis. b *\<^sub>R i)"
        proof (rule ccontr)
          assume not_le: "\<not> (x0 - (\<Sum>i\<in>Basis. b *\<^sub>R i) \<le> x t \<and> x t \<le> x0 + (\<Sum>i\<in>Basis. b *\<^sub>R i))"
          hence "\<exists>i\<in>Basis. \<not> x t \<bullet> i \<le> x0 \<bullet> i + b \<or> \<not> x0 \<bullet> i - b \<le> x t \<bullet> i"
            by (auto simp add: eucl_le[where x = "x t"] eucl_le[where y = "x t"] inner_simps)
          then guess i .. note i = this
          then have "i \<in> Basis" "b < norm ((x t - x t0) \<bullet> i)"
            using x_sol.is_solutionD[OF x_sol]
            by (auto simp add: inner_simps)
          moreover have "... \<le> norm (x t - x t0)"
            using norm_nth_le[of i "x t - x t0"] i by simp
          ultimately have b_lt: "b < norm (x t - x t0)" by simp
          with exceeding assms `t \<noteq> T` show False by auto
        qed
        thus "x t \<in> D" by (simp add: rectangle)
      qed
    qed
  qed
qed

lemma is_solution_eq_is_solution_on_supersetdomain:
  assumes "D \<subseteq> D'"
  shows "is_solution = ivp.is_solution (i\<lparr>ivp_D:=D'\<rparr>)"
proof -
  interpret ivp': ivp "i\<lparr>ivp_D:=D'\<rparr>" using iv_defined assms by unfold_locales auto
  show ?thesis using assms
  proof (safe intro!: ext)
    fix x assume "ivp'.is_solution x"
    moreover hence "\<And>t. t \<in> I \<Longrightarrow> x t \<in> D" using assms
      by (intro solution_in_bounds) (simp_all add: interval)
    ultimately show "is_solution x"
      by (auto intro!: is_solutionI dest: ivp'.is_solutionD simp add: interval)
  qed (intro is_solution_on_superset_domain)
qed

end

text {* For the numerical approximation, it is necessary that f is
lipschitz-continuous outside the actual domain - therefore D'. *}

locale unique_on_rectangle =
  solution_in_rectangle + glob: global_lipschitz I D' f L for L D' +
  assumes lipschitz_on_domain: "D \<subseteq> D'"
begin

lemma lipschitz: "t \<in> I \<Longrightarrow> lipschitz D (\<lambda>x. f (t, x)) L" "0 \<le> L"
  using lipschitz lipschitz_on_domain
  by (auto intro: lipschitz_subset)

end

sublocale unique_on_rectangle \<subseteq> unique_solution
proof -
  have "D \<noteq> {}" using rectangle b_nonneg
    by (auto simp: algebra_simps intro!: add_nonneg_nonneg setsum_nonneg scaleR_nonneg_nonneg)
  hence not_empty: "{t0..T}\<times>D \<noteq> {}" using interval iv_defined by simp
  hence rect_le: "(t0, x0 - (\<Sum>i\<in>Basis. b *\<^sub>R i)) \<le> (T, x0 + (\<Sum>i\<in>Basis. b *\<^sub>R i))"
    by (auto simp: rectangle)
  {
    fix t::real and x y
    let ?fc = "ext_cont f (t0,x0 - (\<Sum>i\<in>Basis. b *\<^sub>R i)) (T,x0 + (\<Sum>i\<in>Basis. b *\<^sub>R i))"
    let ?ca_x = "clamp (t0, x0 - (\<Sum>i\<in>Basis. b *\<^sub>R i)) (T, x0 + (\<Sum>i\<in>Basis. b *\<^sub>R i)) (t, x)"
    let ?ca_y = "clamp (t0, x0 - (\<Sum>i\<in>Basis. b *\<^sub>R i)) (T, x0 + (\<Sum>i\<in>Basis. b *\<^sub>R i)) (t, y)"
    assume "t \<in> {t0..T}"
    hence fst_x: "fst (?ca_x) = t" "fst (?ca_y) = t"
      by (simp_all add: clamp_def fst_eq_Basis)
    have "?ca_x \<in> {t0..T}\<times>D" "?ca_y \<in> {t0..T}\<times>D"
      thm clamp_in_interval
      using clamp_in_interval[OF rect_le]
      unfolding rectangle pair_interval_iff by auto
    hence "(fst (?ca_x), snd (?ca_x)) \<in> {t0..T}\<times>D" "(fst (?ca_y), snd (?ca_y)) \<in> {t0..T}\<times>D"
      by auto
    hence "(t, snd (?ca_x)) \<in> {t0..T}\<times>D"
      "(t, snd (?ca_y)) \<in> {t0..T}\<times>D"
      unfolding fst_x .
    with lipschitz
    have "dist (f (t, snd (?ca_x))) (f (t, snd (?ca_y))) \<le>
      L * dist (snd (?ca_x)) (snd (?ca_y))"
      by (simp add: lipschitz_def interval)
    hence "dist (f (fst (?ca_x), snd (?ca_x))) (f (fst (?ca_y), snd (?ca_y))) \<le>
      L * dist (snd (?ca_x)) (snd (?ca_y))" unfolding fst_x .
    hence "dist (?fc (t, x)) (?fc (t, y)) \<le> L * dist (snd (?ca_x)) (snd (?ca_y))"
      unfolding ext_cont_def apply simp
      apply (subst Abs_bcontfun_inverse[OF clamp_bcontfun])
      using `D \<noteq> {}` rectangle interval_notempty apply simp
      using continuous interval rectangle apply simp
      apply (subst Abs_bcontfun_inverse[OF clamp_bcontfun])
      using `D \<noteq> {}` rectangle interval_notempty apply simp
      using continuous interval rectangle apply simp apply simp done
    moreover have "... \<le> L * dist (?ca_x) (?ca_y)"
      using `0 \<le> L` by (auto intro: mult_left_mono dist_snd_le)
    moreover have "... \<le> L * dist (t, x) (t, y)"
      using lipschitz`{t0..T}\<times>D\<noteq>{}` rectangle
      by (auto intro!: mult_left_mono dist_snd_le dist_clamps_le_dist_args)
    ultimately
    have "dist (?fc (t, x)) (?fc (t, y)) \<le> L * dist x y"
      by (simp add: dist_Pair_Pair)
  }
  then interpret ivp_c: unique_on_strip
    "i\<lparr>ivp_f:=ext_cont f (t0,x0 - (\<Sum>i\<in>Basis. b *\<^sub>R i)) (T,x0 + (\<Sum>i\<in>Basis. b *\<^sub>R i)), ivp_D:=UNIV\<rparr>"
    using interval continuous rectangle lipschitz iv_defined
    apply unfold_locales
    apply (auto intro!:
      continuous_on_subset[where t = "{t0..T} \<times> UNIV" and s = UNIV]
      simp add: `D\<noteq>{}` lipschitz_def)
    unfolding ext_cont_def
      apply (subst Abs_bcontfun_inverse[OF clamp_bcontfun])
      using `D \<noteq> {}` rectangle interval_notempty apply simp
      using continuous interval rectangle apply simp
      apply (rule clamp_continuous_on) using `D \<noteq> {}` by auto
  show "unique_solution i"
  proof (rule unique_solutionI)
    show "is_solution ivp_c.solution"
    proof
      fix t assume "t \<in> I"
      moreover
      hence "(ivp_c.solution has_vector_derivative
        ext_cont f (t0, x0 - (\<Sum>i\<in>Basis. b *\<^sub>R i)) (T, x0 + (\<Sum>i\<in>Basis. b *\<^sub>R i)) (t, ivp_c.solution t))
        (at t within {t0..T})"
        using ivp_c.solution_has_deriv interval by auto
      moreover
      from solution_in_bounds[OF ivp_c.is_solution_solution
        `t\<in>I`[simplified interval]]
      show "ivp_c.solution t \<in> D" apply rule
        using interval rectangle continuous
        by simp_all
      ultimately
      show "(ivp_c.solution has_vector_derivative f (t, ivp_c.solution t))
        (at t within I)"
        using interval rectangle continuous
        by simp_all
    next
    qed (insert ivp_c.solution_t0, simp)
  next
    fix z t
    assume z_sol: "is_solution z" and "t \<in> I"
    hence "t\<in>{t0..T}" by (simp add: interval)
    have "i\<lparr>ivp_f := f,
            ivp_D := D\<rparr> = i" by simp
    from solution_in_bounds[where f'=f and D'=D, simplified this,
      OF z_sol `t\<in>{t0..T}`]
    have "z t \<in> D" by simp
    hence "ivp_c.is_solution z"
      using is_solutionD[OF z_sol] rectangle iv_defined interval continuous
      by (intro ivp_c.is_solutionI) auto
    thus "z t = ivp_c.solution t" using `t \<in> I`
      using ivp_c.unique_solution by simp
  qed
qed

end
