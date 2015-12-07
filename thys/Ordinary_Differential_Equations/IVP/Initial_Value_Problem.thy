section{* Initial Value Problems *}
theory Initial_Value_Problem
imports "../ODE_Auxiliarities"
begin

subsection {* Lipschitz continuity *}
text{*\label{sec:lipschitz}*}

context metric_space begin

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

end

subsection {* Solutions of IVPs *}
text{*\label{sec:solutions}*}

record 'a ivp =
  ivp_f :: "real \<times> 'a \<Rightarrow> 'a"
  ivp_t0 :: "real"
  ivp_x0 :: "'a"
  ivp_T :: "real set"
  ivp_X :: "'a set"

locale ivp =
  fixes i::"('a::ordered_euclidean_space) ivp"
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

lemma is_solution_solution_eq:
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
  using assms is_solutionD[OF `is_solution x`]
  by (intro ivp'.is_solutionI) (auto intro:
    has_vector_derivative_within_subset[where s="T"])
qed

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
    by (intro ivp'.is_solutionI) (auto intro: has_vector_derivative_within_subset[where t=T' and s=T])
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
    and solution_has_deriv: "\<And>t. t \<in> T \<Longrightarrow> (solution has_vector_derivative f (t, solution t)) (at t within T)"
    and solution_in_D: "\<And>t. t \<in> T \<Longrightarrow> solution t \<in> X"
  using is_solution_solution unfolding is_solution_def by auto

end

lemma (in ivp) singleton_has_solutionI:
  assumes "T = {t0}"
  shows "has_solution i"
  by unfold_locales (auto simp: has_vector_derivative_def assms
    intro!: has_derivative_singletonI bounded_linear_scaleR_left iv_defined exI[where x="\<lambda>x. x0"])

locale unique_solution = has_solution +
  assumes unique_solution: "\<And>y t. is_solution y \<Longrightarrow> t \<in> T \<Longrightarrow> y t = solution t"

lemma (in ivp) unique_solutionI:
  assumes "is_solution x"
  assumes "\<And>y t. is_solution y \<Longrightarrow> t \<in> T \<Longrightarrow> y t = x t"
  shows "unique_solution i"
proof
  show "\<exists>x. is_solution x" using assms by blast
  then interpret has_solution by unfold_locales
  fix y t
  assume "is_solution y" "t\<in>T"
  from assms(2)[OF this] assms(2)[OF is_solution_solution `t \<in> T`]
  show "y t = solution t" by simp
qed

lemma (in ivp) singleton_unique_solutionI:
  assumes "T = {t0}"
  shows "unique_solution i"
proof -
  interpret singsol: has_solution i
    using assms
    by (rule singleton_has_solutionI)
  show ?thesis
    by unfold_locales (auto dest!: is_solutionD(1) simp: assms singsol.solution_t0)
qed

locale interval = fixes a b assumes interval_notempty: "a \<le> b"

locale ivp_on_interval = ivp + interval t0 t1 for t1 +
  assumes interval: "T = {t0..t1}"
begin

lemma is_solution_ext_cont:
  assumes "continuous_on T x"
  shows "is_solution (ext_cont x t0 t1) = is_solution x"
  using assms iv_defined interval by (intro is_solution_solution_eq) simp_all

lemma solution_fixed_point:
  assumes x: "is_solution x"
  assumes t: "t \<in> T"
  shows "x0 + integral {t0..t} (\<lambda>t. f (t, x t)) = x t"
proof -
  from is_solutionD(2)[OF x] t
  have "\<forall>ta\<in>{t0..t}. (x has_vector_derivative f (ta, x ta)) (at ta within {t0..t})"
    by (auto intro!: has_vector_derivative_within_subset[where t="{t0..t}" and s="{t0..t1}"]
      simp: interval)
  hence "((\<lambda>t. f (t, x t)) has_integral x t - x t0) {t0..t}"
    using t by (intro fundamental_theorem_of_calculus) (simp add: interval)
  from this[THEN integral_unique]
  have "x t = x t0 + integral {t0..t} (\<lambda>t. f (t, x t))" by simp
  thus "x0 + integral {t0..t} (\<lambda>t. f (t, x t)) = x t"
    using solution_continuous_on[OF x] is_solutionD[OF x] by simp
qed

end

sublocale ivp_on_interval \<subseteq> interval t0 t1 by unfold_locales

subsubsection{* Connecting solutions *}
text{*\label{sec:combining-solutions}*}

locale connected_solutions =
  i1?: ivp_on_interval i1 t1 + i2?: ivp_on_interval i2 t2 + i?: ivp_on_interval i t2
  + i1?: has_solution i1 + i2?: has_solution i2
  for i::"('a::ordered_euclidean_space) ivp" and i1::"'a ivp"
  and i2::"'a ivp" and t1 and t2 +
  fixes y
  assumes conn_t: "i2.t0 = t1"
  assumes sol1: "i1.is_solution y"
  assumes conn_x: "i2.x0 = y t1"
  assumes conn_f: "i1.f (t1, y t1) =
    i2.f (t1, y t1)"
  assumes initial_value: "t0 = i1.t0" "x0 = i1.x0"
  assumes f: "f = (\<lambda>(t, x). if t \<le> t1 then i1.f (t, x) else i2.f (t, x))"
  assumes interval: "T = {t0..t2}"
  assumes dom:"X = i1.X" "X = i2.X"
begin

lemma T_subsets:
  shows T1_subset: "i1.T \<subseteq> T"
  and T2_subset: "i2.T \<subseteq> T"
  using i1.iv_defined i2.iv_defined
  by (simp_all add: conn_t interval i1.interval i2.interval initial_value)

definition connection where
  "connection t = (if t \<le> t1 then y t else i2.solution t)"

lemma is_solution_connection: "is_solution connection"
proof -
  {
    fix t
    assume "t0 \<le> t" "t \<le> t2"
    hence "(connection has_vector_derivative (if t \<le> t1 then
        i1.f (t, y t) else i2.f (t, i2.solution t))) (at t within {t0..t2})"
      using initial_value interval dom conn_t conn_x conn_f
        i1.is_solutionD[OF sol1] i2.solution
      i1.iv_defined i2.iv_defined
      unfolding i1.interval i2.interval connection_def[abs_def]
      by (intro linear_continuation) auto
  } note D = this
  {
    fix t
    assume "t0 \<le> t" "t \<le> t1"
    moreover
    hence "t0 \<le> t" "t \<le> t2" using i2.interval i2.iv_defined conn_t
      by auto
    note D[OF this]
    ultimately
    have "((\<lambda>t. if t \<le> t1 then y t else i2.solution t)
      has_vector_derivative f (t, connection t))
      (at t within {t0..t2})"
      by (simp add: f connection_def[abs_def])
  } moreover {
    fix t
    assume "t \<le> t2" "\<not> t \<le> t1"
    moreover
    hence "t0 \<le> t" "t \<le> t2" using i1.interval i1.iv_defined initial_value
      by auto
    moreover
    note D[OF this]
    ultimately
    have "((\<lambda>t. if t \<le> t1 then y t else i2.solution t)
      has_vector_derivative f (t, connection t))
            (at t within {t0..t2})"
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
  i1?: unique_solution i1 + i2?: unique_solution i2 +
  connected_solutions i i1 i2 t1 t2 "i1.solution"
  for i::"('a::ordered_euclidean_space) ivp" and i1::"'a ivp"
  and i2::"'a ivp" and t1 and t2
begin

sublocale unique_solution
proof (intro unique_solutionI)
  show "is_solution connection" using is_solution_connection .
  fix y t
  assume "is_solution y" "t \<in> T"
  have "i1.is_solution y"
  proof (intro i1.is_solutionI)
    show "y (i1.t0) = i1.x0"
      using is_solutionD(1)[OF `is_solution y`] initial_value by simp
  next
    fix ta
    assume "ta \<in> i1.T"
    hence "ta \<in> T" using T1_subset by auto
    from is_solutionD(2)[OF `is_solution y` this]
    have "(y has_vector_derivative i1.f (ta, y ta)) (at ta within T)"
      using `ta \<in> i1.T` by (simp add: f i1.interval)
    thus "(y has_vector_derivative i1.f (ta, y ta)) (at ta within i1.T)"
      using T1_subset
      by (rule has_vector_derivative_within_subset)
    show "y ta \<in> i1.X" using is_solutionD(3)[OF `is_solution y` `ta \<in> T`]
      by (simp add: dom)
  qed
  have "i2.is_solution y"
  proof (intro i2.is_solutionI)
    have "i1.solution t1 = y t1"
      using i1.unique_solution[OF `i1.is_solution y`] i1.interval i1.iv_defined
      by simp
    thus "y (i2.t0) = i2.x0"
      by (simp add: conn_t conn_x)
    fix ta
    assume "ta \<in> i2.T"
    hence "ta \<in> T" using T2_subset by auto
    from is_solutionD(2)[OF `is_solution y` this]
    have "(y has_vector_derivative i2.f (ta, y ta)) (at ta within T)"
      using `ta \<in> i2.T` conn_t conn_f `i1.solution t1 = y t1`
      by (cases "ta = t1") (simp_all add: f i2.interval)
    thus "(y has_vector_derivative i2.f (ta, y ta)) (at ta within i2.T)"
      using T2_subset
      by (rule has_vector_derivative_within_subset)
    show "y ta \<in> i2.X" using is_solutionD(3)[OF `is_solution y` `ta \<in> T`]
      using dom by simp
  qed
  from i1.unique_solution[OF `i1.is_solution y`, of t]
    i2.unique_solution[OF `i2.is_solution y`, of t]
  show "y t = connection t"
    using `t \<in> T`
    by (simp add: interval i1.interval i2.interval initial_value conn_t
      connection_def)
qed

lemma connection_eq_solution: "\<And>t. t \<in> T \<Longrightarrow> connection t = solution t"
  by (rule unique_solution is_solution_connection)+

lemma solution1_eq_solution:
  assumes "t \<in> i1.T"
  shows "i1.solution t = solution t"
proof -
  from T1_subset assms have "t \<in> T" by auto
  from connection_eq_solution[OF `t \<in> T`] i1.interval assms
  show ?thesis
    by (simp add: connection_def split: split_if_asm)
qed

lemma solution2_eq_solution:
  assumes "t \<in> i2.T"
  shows "i2.solution t = solution t"
proof -
  from T2_subset assms have "t \<in> T" by auto
  from connection_eq_solution[OF `t \<in> T`] i2.interval assms conn_t conn_x i2.solution_t0
  show ?thesis
    by (simp add: connection_def split: split_if_asm)
qed

end

subsection {* Picard-Lindeloef on set of functions into closed set *}
text{*\label{sec:plclosed}*}
locale continuous = fixes T X f
  assumes continuous: "continuous_on (T \<times> X) f"

locale global_lipschitz =
  fixes T X f and L::real
  assumes lipschitz: "\<And>t. t\<in>T \<Longrightarrow> lipschitz X (\<lambda>x. f (t, x)) L" "0 \<le> L"

locale closed_domain =
  fixes X assumes closed: "closed X"

locale self_mapping = ivp_on_interval +
  assumes self_mapping:
    "\<And>x t. t \<in> T \<Longrightarrow> x t0 = x0 \<Longrightarrow> x \<in> {t0..t} \<rightarrow> X \<Longrightarrow> continuous_on {t0..t} x \<Longrightarrow>
      x0 + integral {t0..t} (\<lambda>t. f (t, x t)) \<in> X"

locale unique_on_closed = self_mapping + continuous T X f +
  closed_domain X +
  global_lipschitz T X f L for L
begin

text {* Picard Iteration *}

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
  using `y \<in> {t0..t} \<rightarrow> X` assms interval_notempty
  by (intro continuous_Sigma[of _ _ "\<lambda>_. X"])
    (auto simp: interval intro: assms continuous_on_subset continuous)

lemma P_inner_bcontfun:
  assumes "y \<in> T \<rightarrow> X"
  assumes y_cont: "continuous_on T y"
  shows "(\<lambda>x. P_inner y (clamp t0 t1 x)) \<in> bcontfun"
proof -
  show ?thesis using interval iv_defined assms
    by (auto intro!: clamp_bcontfun continuous_intros continuous_f indefinite_integral_continuous
                     integrable_continuous_real
             simp add: P_def P_inner_def)
qed

definition "iter_space = (Abs_bcontfun ` ((T \<rightarrow> X) \<inter> bcontfun \<inter> {x. x t0 = x0}))"

lemma iter_spaceI:
  "(\<And>x. x \<in> T \<Longrightarrow> Rep_bcontfun g x \<in> X) \<Longrightarrow> g t0 = x0 \<Longrightarrow> g \<in> iter_space"
  by (force simp add: assms iter_space_def Rep_bcontfun Rep_bcontfun_inverse intro!: Rep_bcontfun)

lemma const_in_subspace: "(\<lambda>_. x0) \<in> (T \<rightarrow> X) \<inter> bcontfun \<inter> {x. x t0 = x0}"
  by (auto intro: const_bcontfun iv_defined)

lemma closed_iter_space: "closed iter_space"
proof -
  have "(T \<rightarrow> X) \<inter> bcontfun \<inter> {x. x t0 = x0} = Pi T (\<lambda>i. if i = t0 then {x0} else X) \<inter> bcontfun"
    using iv_defined by (auto simp: Pi_iff split: split_if_asm)
  thus ?thesis using closed by (auto simp add: iter_space_def intro!: closed_Pi_bcontfun)
qed

lemma iter_space_notempty: "iter_space \<noteq> {}"
  using const_in_subspace by (auto simp: iter_space_def)

lemma P_self_mapping:
  assumes in_space: "g \<in> iter_space"
  shows "P g \<in> iter_space"
proof (rule iter_spaceI)
  have cont: "continuous_on (cbox t0 t1) (P_inner (Rep_bcontfun g))"
    using assms Rep_bcontfun[of g, simplified bcontfun_def]
    by (auto simp: interval iter_space_def Abs_bcontfun_inverse P_inner_def interval_notempty
      intro!: continuous_intros indefinite_integral_continuous integrable_continuous_real continuous_f)
  from ext_cont_cancel[OF _ cont] assms
  show "Rep_bcontfun (P g) t0 = x0"
     "\<And>t. t \<in> T \<Longrightarrow> Rep_bcontfun (P g) t \<in> X"
    using assms Rep_bcontfun[of g, simplified bcontfun_def]
    by (auto intro!: self_mapping simp: interval interval_notempty P_inner_def P_def iter_space_def
      Abs_bcontfun_inverse)
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
  auto simp: interval P_inner_def continuous_intros indefinite_integral_continuous continuous_f)

lemma
  solution_in_iter_space:
  assumes "is_solution z"
  shows "ext_cont z t0 t1 \<in> iter_space"
proof -
  let ?z = "ext_cont z t0 t1"
  have "is_solution ?z"
    using is_solution_ext_cont interval `is_solution z` solution_continuous_on by simp
  hence "\<And>t. t \<in> T \<Longrightarrow> ext_cont z t0 t1 t \<in> X" by (auto simp add: is_solution_def)
  thus "?z \<in> iter_space" using is_solutionD[OF `is_solution z`]
    solution_continuous_on[OF `is_solution z`]
    by (auto simp: interval interval_notempty intro!: iter_spaceI)
qed

end

locale unique_on_bounded_closed = unique_on_closed +
  assumes lipschitz_bound: "(t1 - t0) * L < 1"
begin

lemma lipschitz_P:
  shows "lipschitz iter_space P ((t1 - t0) * L)"
proof (rule lipschitzI)
  fix y z
  assume "y \<in> iter_space" and "z \<in> iter_space"
  hence y_defined: "Rep_bcontfun y \<in> (T \<rightarrow> X)" and z_defined: "Rep_bcontfun z \<in> (T \<rightarrow> X)"
    by (auto simp: Abs_bcontfun_inverse iter_space_def)
  {
    fix y z::"real\<Rightarrow>'a"
    assume "y \<in> bcontfun" and y_defined: "y \<in> (T \<rightarrow> X)"
    assume "z \<in> bcontfun" and z_defined: "z \<in> (T \<rightarrow> X)"
    from bcontfunE[OF `y \<in> bcontfun`] have y: "continuous_on UNIV y" by auto
    from bcontfunE[OF `z \<in> bcontfun`] have z: "continuous_on UNIV z" by auto
    {
      fix t
      assume t_bounds: "t0 \<le> t" "t \<le> t1"
        --{* Instances of @{text continuous_on_subset} *}
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
        by (auto intro!: integral_le continuous_intros
          simp add: dist_norm lipschitz_def Pi_iff)
      also have "... \<le> integral {t0..t} (\<lambda>t. L *
        norm (Abs_bcontfun y - Abs_bcontfun  z))"
        using norm_bounded[of "Abs_bcontfun y - Abs_bcontfun z"]
          y_cont z_cont lipschitz
        by (intro integral_le) (auto intro!: continuous_intros mult_left_mono
          simp add: Abs_bcontfun_inverse[OF `y \<in> bcontfun`]
          Abs_bcontfun_inverse[OF `z \<in> bcontfun`])
      also have "... =
        L * (t - t0) * norm (Abs_bcontfun y - Abs_bcontfun z)"
        using t_bounds by simp
      also have "... \<le> L * (t1 - t0) * norm (Abs_bcontfun y - Abs_bcontfun z)"
        using t_bounds zero_le_dist lipschitz
        by (auto intro!: mult_right_mono mult_left_mono)
      finally
      have "norm (P_inner y t - P_inner z t)
        \<le> L * (t1 - t0) * norm (Abs_bcontfun y - Abs_bcontfun z)" .
    } note * = this
    have "dist (P (Abs_bcontfun y)) (P (Abs_bcontfun z)) \<le>
      L * (t1 - t0) * dist (Abs_bcontfun y) (Abs_bcontfun z)"
      unfolding P_def dist_norm ext_cont_def Abs_bcontfun_inverse[OF `y \<in> bcontfun`]
        Abs_bcontfun_inverse[OF `z \<in> bcontfun`]
      using interval iv_defined `y \<in> bcontfun` `z \<in> bcontfun` y_defined z_defined
        clamp_in_interval[of t0 t1] interval_notempty
      apply (intro norm_bound)
      unfolding Rep_bcontfun_minus
      apply (subst Abs_bcontfun_inverse)
       defer
       apply (subst Abs_bcontfun_inverse)
        defer
        apply (auto intro!: P_inner_bcontfun * elim!: bcontfunE intro: continuous_on_subset)
      done
  }
  from this[OF Rep_bcontfun y_defined Rep_bcontfun z_defined]
  show "dist (P y) (P z) \<le> (t1 - t0) * L * dist y z"
    unfolding Rep_bcontfun_inverse by (simp add: field_simps)
qed


lemma fixed_point_unique: "\<exists>!x\<in>iter_space. P x = x"
  using lipschitz lipschitz_bound lipschitz_P interval
      complete_UNIV iv_defined
  by (intro banach_fix) (auto intro: P_self_mapping split_mult_pos_le
    intro!: closed_iter_space iter_space_notempty simp: lipschitz_def complete_eq_closed)

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
  unfolding fixed_point_def using fixed_point_unique assms by (rule the1_equality)

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
    by (subst ext_cont_cancel) (auto simp add: iter_space_def Abs_bcontfun_inverse
      intro!: continuous_intros indefinite_integral_continuous integrable_continuous_real
      continuous_f intro: continuous_on_subset)
  finally show "fixed_point t0 = x0" .
next
  fix t
  have U: "Rep_bcontfun fixed_point \<in> Pi T (\<lambda>_. X)"
    using fixed_point by (auto simp add: iter_space_def Abs_bcontfun_inverse)
  assume "t \<in> T" hence t_range: "t \<in> {t0..t1}" by (simp add: interval)
  from has_vector_derivative_const
    integral_has_vector_derivative[
    OF continuous_Sigma[OF U continuous fixed_point_continuous, simplified interval] t_range]
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
    by (subst ext_cont_cancel) (auto simp add: iter_space_def Abs_bcontfun_inverse
      intro!: continuous_intros indefinite_integral_continuous integrable_continuous_real
      continuous_f intro: continuous_on_subset)
  moreover
  have "fixed_point t \<in> X"
    using fixed_point `t \<in> T` by (auto simp add: iter_space_def Abs_bcontfun_inverse)
  ultimately
  show "(fixed_point has_vector_derivative
      f (t, fixed_point t)) (at t within T)"
    "fixed_point t \<in> X" unfolding fixed_point interval
    by simp_all
qed

end

subsubsection {* Existence of solution *}

sublocale unique_on_bounded_closed \<subseteq> has_solution
proof
  from fixed_point_solution
  show "\<exists>x. is_solution x" by blast
qed

subsubsection {* Unique solution *}
text{*\label{sec:ivp-ubs}*}

sublocale unique_on_bounded_closed \<subseteq> unique_solution
proof
  fix z t
  assume "is_solution z"
  with ext_cont_solution_fixed_point `is_solution z` is_solution_solution
    solution_in_iter_space fixed_point_equality
  have "ext_cont solution t0 t1 t = ext_cont z t0 t1 t" by metis
  moreover assume "t \<in> T"
  ultimately
  show "z t = solution t"
    using solution_continuous_on[OF `is_solution z`] solution_continuous_on[OF is_solution_solution]
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
    using `t1=t0` interval solution_t0
    by unfold_locales (simp add: is_solution_def)
next
  assume "t1 \<noteq> t0" with interval iv_defined have interval: "T = {t0..t1}" "t0 < t1"
    by auto
  obtain n::nat and b where b: "b = (t1 - t0) / (Suc n)" and bL: "L * b < 1"
    by (rule, rule) (auto intro: order_le_less_trans real_nat_ceiling_ge simp del: of_nat_Suc)
  then interpret i': ivp_on_interval i "t0 + (Suc n) * b"
    using interval by unfold_locales simp_all
  from b have "b > 0" using interval iv_defined
    by auto
  hence "b \<ge> 0" by simp
  from interval have "t0 * (real (Suc n) - 1) \<le> t1 * (real (Suc n) - 1)" by (cases n) auto
  hence ble: "t0 + b \<le> t1" unfolding b by (auto simp add: field_simps)
  have subsetbase: "t0 + (Suc n) * b \<le> t1" using i'.interval interval by auto

  interpret i': unique_solution "i\<lparr>ivp_T := {t0..t0 + real (Suc n) * b}\<rparr>"
    using subsetbase
  proof (induct n)
    case 0
    then interpret sol: unique_on_bounded_closed "i\<lparr>ivp_T:={t0..t0+b}\<rparr>" "t0 + b"
      using interval iv_defined `b > 0` bL continuous lipschitz closed self_mapping
      by unfold_locales (auto intro: continuous_on_subset simp: ac_simps Pi_iff)
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
    have [simp]: "snb - nb = b"
    proof -
      have "snb + - (nb) = b * real (Suc (Suc n)) + - (b * real (Suc n))"
        by (simp add: ac_simps snb_def nb_def)
      thus ?thesis by (simp add: field_simps of_nat_Suc)
    qed
    def i1 \<equiv> "i\<lparr>ivp_T := {t0..t0 + nb}\<rparr>"
    def T1 \<equiv> "t0 + nb"
    interpret ivp1: ivp_on_interval i1 T1
      using iv_defined `nb > 0` by unfold_locales (auto simp: i1_def T1_def)
    interpret ivp1: unique_solution i1
      using nb_le_snb nbs_nonneg Suc continuous lipschitz by (simp add: i1_def)
    interpret ivp1_cl: unique_on_closed i1 "t0 + nb"
      using nb_le_snb nbs_nonneg Suc continuous lipschitz closed self_mapping
      by unfold_locales (auto simp: i1_def interval intro: continuous_on_subset)
    def i2 \<equiv> "i\<lparr>ivp_t0:=t0+nb, ivp_T:={t0 + nb..t0+snb},
      ivp_x0:=ivp1.solution (t0 + nb)\<rparr>"
    def T2 \<equiv> "t0 + snb"
    interpret ivp2: ivp_on_interval i2 T2
      using nbs_nonneg `nb < snb` ivp1.solution_in_D
      by unfold_locales (auto simp: i1_def i2_def T2_def)
    interpret ivp2: self_mapping i2 T2
    proof unfold_locales
      fix x t assume t: "t \<in> ivp2.T" and x: "x ivp2.t0 = ivp2.x0" "x \<in> {ivp2.t0 .. t} \<rightarrow> ivp2.X"
        and cont: "continuous_on {ivp2.t0 .. t} x"
      hence "t \<in> T"
        using Suc(2) nbs_nonneg interval
        by (simp add: i2_def)
      let ?un = "(\<lambda>t. if t \<le> nb + t0 then ivp1.solution t else x t)"
      let ?fun = "(\<lambda>t. f (t, ?un t))"
      have decomp: "{t0..t} = {t0..nb + t0} \<union> {nb + t0..t}" using interval_notempty t nbs_nonneg
        by (auto simp: i2_def)
      have un_space: "?un \<in> {t0..t} \<rightarrow> X"
        using x ivp1.solution_in_D
        by (auto simp: i1_def i2_def Pi_iff)
      have cont_un: "continuous_on {t0..t} ?un"
        using x cont ivp1.solution_continuous_on[OF ivp1.is_solution_solution, simplified i1_def]
        unfolding decomp
        by (intro continuous_on_If) (auto intro: continuous_on_subset simp: i1_def i2_def ac_simps)
      have cont_fun: "continuous_on {t0..t} ?fun"
        using un_space cont_un `t \<in> T` by (rule continuous_f)
      have "ivp.solution i1 (nb + t0) + integral {nb + t0..t} (\<lambda>xa. f (xa, x xa)) =
        x0 + (integral {t0..nb + t0} (\<lambda>t. f (t, ivp1.solution t)) + integral {nb + t0..t} (\<lambda>xa. f (xa, x xa)))"
        using ivp1_cl.solution_fixed_point[OF ivp1.is_solution_solution] nbs_nonneg
          ivp1_cl.P_inner_def
        by (auto simp: i1_def ac_simps)
      also have "integral {t0..nb + t0} (\<lambda>t. f (t, ivp1.solution t)) = integral {t0..nb + t0} ?fun"
        by (rule integral_spike[OF negligible_empty]) auto
      also have fun2: "integral {nb + t0..t} (\<lambda>t. f (t, x t)) = integral {nb + t0..t} ?fun"
        using x
        by (intro integral_spike[OF negligible_empty]) (auto simp: i1_def i2_def ac_simps)
      also have "integral {t0..nb + t0} ?fun + integral {nb + t0..t} ?fun = integral {t0..t} ?fun"
        using t nbs_nonneg
        by (intro integral_combine) (auto simp: i2_def less_imp_le intro!: cont_fun)
      also have "x0 + \<dots> \<in> X"
        using `t \<in> T` `nb > 0` ivp1.is_solutionD[OF ivp1.is_solution_solution]
        by (intro self_mapping[OF _ _ un_space cont_un]) (auto simp: ivp1.iv_defined i1_def)
      also note fun2[symmetric]
      finally show "ivp2.x0 + integral {ivp2.t0 .. t} (\<lambda>t. ivp2.f (t, x t)) \<in> ivp2.X"
        by (simp add: i1_def i2_def ac_simps)
    qed
    interpret ivp2: unique_on_bounded_closed i2 T2
      using bL Suc(2) nbs_nonneg interval continuous lipschitz closed
      by unfold_locales (auto intro: continuous_on_subset simp:ac_simps i1_def i2_def T2_def)
    def i \<equiv> "i\<lparr>ivp_T := {t0..t0 + real (Suc (Suc n)) * b}\<rparr>"
    def T \<equiv> "t0 + real (Suc (Suc n)) * b"
    interpret ivp_c: connected_unique_solutions i i1 i2 T1 T2
      using `b > 0` iv_defined ivp1.is_solution_solution
      by unfold_locales (auto simp: i1_def i2_def i_def T1_def T2_def T_def snb_def)
    show ?case unfolding i_def[symmetric] by unfold_locales
  qed
  show "unique_solution i"
    using i'.solution i'.unique_solution interval(1)[symmetric] i'.interval[symmetric]
    by unfold_locales (auto simp del: of_nat_Suc)
qed

subsection {* Picard-Lindeloef for @{term "X=(\<lambda>_. UNIV)"} *}
text{*\label{sec:pl-us}*}

locale unique_on_strip = ivp_on_interval + continuous T X f +
  global_lipschitz T X f L for L +
  assumes strip: "X = UNIV"

sublocale unique_on_strip < unique_on_closed
  using strip by unfold_locales auto

subsection {* Picard-Lindeloef on rectangular domain *}
text{*\label{sec:pl-rect}*}
locale rectangle = ivp_on_interval +
  fixes b
  assumes b_pos: "b > 0"
  assumes rectangle: "X = {x0 - b *\<^sub>R One..x0 + b *\<^sub>R One}"

lemma dist_component_le:
  fixes x y::"'a::euclidean_space"
  assumes "i \<in> Basis"
  shows "dist (x \<bullet> i) (y \<bullet> i) \<le> dist x y"
  using assms
  by (auto simp: euclidean_dist_l2[of x y] intro: member_le_setL2)

lemma setsum_inner_Basis_one: "i \<in> Basis \<Longrightarrow> (\<Sum>x\<in>Basis. x \<bullet> i) = 1"
  by (subst setsum.mono_neutral_right [of _ "{i}"]) (auto simp: inner_not_same_Basis)

lemma cball_in_cube:
  fixes y::"'a::ordered_euclidean_space"
  shows "cball y r \<subseteq> {y - r *\<^sub>R One..y + r *\<^sub>R One}"
  unfolding scaleR_setsum_right interval_cbox cbox_def
proof safe
  fix x i::'a assume "i \<in> Basis" "x \<in> cball y r"
  with dist_component_le[OF `i \<in> Basis`, of y x]
  have "dist (y \<bullet> i) (x \<bullet> i) \<le> r" by simp
  thus "(y - setsum (op *\<^sub>R r) Basis) \<bullet> i \<le> x \<bullet> i" "x \<bullet> i \<le> (y + setsum (op *\<^sub>R r) Basis) \<bullet> i"
    by (auto simp add: inner_diff_left inner_add_left inner_setsum_left setsum_right_distrib[symmetric]
      setsum_inner_Basis_one `i\<in>Basis` dist_real_def)
qed

lemma centered_cube_in_cball:
  shows "{- r *\<^sub>R One..r *\<^sub>R One::'a::ordered_euclidean_space} \<subseteq> cball 0 (sqrt(DIM('a)) * r)"
proof
  fix x::'a
  have "norm x \<le> sqrt(DIM('a)) * infnorm x"
  by (rule norm_le_infnorm)
  also
  assume "x \<in> {- r *\<^sub>R One..r *\<^sub>R One}"
  hence "infnorm x \<le> r"
    using assms
    by (auto simp: infnorm_def eucl_le[where 'a='a] intro!: cSup_least)
      (simp add: abs_real_def minus_le_iff)
  finally show "x \<in> cball 0 (sqrt(DIM('a)) * r)"
    by (auto simp: dist_norm mult_left_mono)
qed

locale solution_in_rectangle = rectangle + continuous T X f +
  fixes B
  assumes norm_f: "\<And>x t. t \<in> T \<Longrightarrow> x \<in> X \<Longrightarrow> norm (f (t, x)) \<le> B"
  assumes t1_bounded: "t1 \<le> t0 + b / B"
begin

lemma B_nonneg: "B \<ge> 0"
proof -
  have "0 \<le> norm (f (t0, x0))" by simp
  also from iv_defined norm_f have "... \<le> B" by simp
  finally show ?thesis by simp
qed

lemma in_bounds_derivativeI:
  assumes "t \<in> T"
  assumes init: "x t0 = x0"
  assumes cont: "continuous_on {t0..t} x"
  assumes solves: "\<And>s. s \<in> {t0..t} \<Longrightarrow> (x has_vector_derivative f (s, y s)) (at s within {t0..t})"
  assumes y_bounded: "\<And>\<xi>. \<xi>\<in>{t0..t} \<Longrightarrow> x \<xi> \<in> X \<Longrightarrow> y \<xi> \<in> X"
  shows "x t \<in> X"
proof cases
  assume "b = 0 \<or> B = 0" with assms t1_bounded interval interval_notempty have "t = t0"
    by auto
  thus ?thesis using iv_defined init by simp
next
  assume "\<not>(b = 0 \<or> B = 0)"
  hence "b > 0" "B > 0" using B_nonneg b_pos by auto
  show ?thesis
  proof -
    from cont have closed: "closed {s \<in> {t0..t}. norm (x s - x t0) \<in> {b..}}"
      by (intro continuous_closed_preimage continuous_intros) auto
    have exceeding: "{s \<in> {t0..t}. norm (x s - x t0) \<in> {b..}} \<subseteq> {t}"
    proof (rule ccontr)
      assume "\<not>{s \<in> {t0..t}. norm (x s - x t0) \<in> {b..}} \<subseteq> {t}"
      hence notempty: "{s \<in> {t0..t}. norm (x s - x t0) \<in> {b..}} \<noteq> {}"
        and not_max: "{s \<in> {t0..t}. norm (x s - x t0) \<in> {b..}} \<noteq> {t}" by auto
      from distance_attains_inf[OF closed notempty, of t0]
      obtain s where s_bound: "s \<in> {t0..t}" and exceeds: "norm (x s - x t0) \<in> {b..}"
        and min: "\<forall>t2\<in>{t0..t}. norm (x t2 - x t0) \<in> {b..} \<longrightarrow> dist t0 s \<le> dist t0 t2"
        by blast
      hence "s \<le> t" by simp
      have lt: "t0 < s"
        using s_bound exceeds min
          eucl_le[of x0] eucl_le[where y=x0] diff_self `b>0`
        by (auto simp add: less_le)
      have deriv:
        "\<forall>t\<in>{t0<..<s}. (x has_derivative (\<lambda>h. h *\<^sub>R f (t, y t))) (at t)"
      proof
        fix ss
        assume int:"ss \<in> {t0<..<s}"
        hence "{t0..t} \<supseteq> {t0<..<s}" "t0 \<le> ss" "ss \<le> t" using s_bound by auto
        with solves[of ss]
        show "(x has_derivative (\<lambda>h. h *\<^sub>R f (ss, y ss))) (at ss)"
          unfolding has_vector_derivative_def
          by (subst has_derivative_within_open[OF int, symmetric])
            (auto intro!: has_derivative_within_subset[where s="{t0..t}" and t = "{t0<..<s}"]
             simp add: interval)
      qed
      from cont have cont: "continuous_on {t0..s} x"
        by (rule continuous_on_subset) (simp add: `s \<le> t`)
      from mvt_general[OF lt cont deriv] obtain \<xi> where \<xi>: "\<xi> \<in> {t0<..<s}"
        "norm (x s - x t0) \<le> norm ((s - t0) *\<^sub>R f (\<xi>, y \<xi>))" by auto
      have "\<xi> \<in> {t0..t}" using \<xi> `s \<le> t` by auto
      hence "\<xi> \<in> {t0..t1}" using assms by (auto simp: interval)
      have "norm (x s - x t0) < b"
      proof cases
        assume "f (\<xi>, y \<xi>) = 0"
        with \<xi>(2) have "norm (x s - x t0) \<le> 0" by simp
        with `b > 0` show ?thesis by simp
      next
        assume f'_nonzero: "f (\<xi>, y \<xi>) \<noteq> 0"
        note \<xi>(2)
        also
        have "s \<noteq> t"
          using s_bound exceeds min not_max by (auto simp: dist_norm)
        hence "norm ((s - t0) *\<^sub>R f (\<xi>, y \<xi>)) < \<bar>t1 - t0\<bar> * norm (f (\<xi>, y \<xi>))"
          using s_bound f'_nonzero `t \<in> T` by (simp add: interval less_le)
        also
        have "\<xi> \<notin> {s \<in> {t0..t}. norm (x s - x t0) \<in> {b..}}"
        proof
          assume "\<xi> \<in> {s \<in> {t0..t}. norm (x s - x t0) \<in> {b..}}"
          with min have "dist t0 s \<le> dist t0 \<xi>" by simp
          thus "False" using s_bound \<xi> by (simp add: dist_real_def)
        qed
        with `\<xi> \<in> {t0..t}` have norm_lt: "norm (x \<xi> - x t0) < b"
          by auto
        hence "x \<xi> \<in> cball x0 b" by (auto simp: dist_norm[symmetric] dist_commute init)
        with cball_in_cube[of "x0" b]
        have "x \<xi> \<in> X" unfolding rectangle[symmetric] by (auto simp: scaleR_setsum_left)
        with \<xi> have "\<bar>t1 - t0\<bar> * norm (f (\<xi>, y \<xi>)) \<le> \<bar>t1 - t0\<bar> * B"
          using `\<xi> \<in> {t0..t1}`
          using norm_f y_bounded interval s_bound by (auto simp: interval)
        also
        have "... \<le> b" using `b>0` norm_f t1_bounded interval iv_defined `B>0`
          by (simp add: field_simps abs_real_def)
        finally
        show "norm (x s - x t0) < b" .
      qed
      moreover
      from exceeds have "norm (x s - x t0) \<ge> b" by simp
      ultimately show False by simp
    qed note mvt_result = this
    from cont assms have cont_diff: "continuous_on {t0..t} (\<lambda>xa. x xa - x t0)"
      by (auto intro!: continuous_intros continuous_on_subset[where t="{t0..t}"] simp: interval)
    have "norm (x t - x t0) \<le> b"
    proof (rule ccontr)
      assume H: "\<not> norm (x t - x t0) \<le> b"
      hence "norm (x t - x t0) \<ge> b" "t0 \<le> t" using assms interval by simp_all
      from IVT'[of "\<lambda>t. norm (x t - x t0)" t0 b t, OF _ this continuous_on_norm[OF cont_diff]]
      obtain s where s: "s\<ge>t0" "s \<le> t" "norm (x s - x t0) = b"
        using b_pos by auto
      have "s \<in> {s \<in> {t0..t}. norm (x s - x t0) \<in> {b..}}"
        using s `t \<in> T` by (auto simp: interval)
      with mvt_result have "s = t" by blast
      hence "s = t" using s `t \<in> T` by (auto simp: interval)
      with s H show False by simp
    qed
    hence "x t \<in> cball x0 b" using init
      by (auto simp: dist_commute dist_norm[symmetric])
    also note cball_in_cube
    finally show "x t \<in> X" unfolding rectangle .
  qed
qed

lemma integral_in_bounds:
  assumes "t \<in> T" "x t0 = x0" "x \<in> {t0..t} \<rightarrow> X"
  assumes cont: "continuous_on {t0..t} x"
  shows "x0 + integral {t0..t} (\<lambda>t. f (t, x t)) \<in> X" (is "x0 + ?ix t \<in> X")
proof -
  have cont_f:"continuous_on {t0..t} (\<lambda>t. f (t, x t))"
    using assms
    by (intro continuous_Sigma)
      (auto intro: cont continuous_on_subset[OF continuous] simp: interval)
  show ?thesis
    using assms
    by (intro in_bounds_derivativeI[where y=x and x="\<lambda>t. x0 + ?ix t"])
      (auto simp: interval intro!: cont_f integral_has_vector_derivative
      has_vector_derivative_const has_vector_derivative_add[THEN vector_derivative_eq_rhs]
      continuous_intros indefinite_integral_continuous)
qed

lemma solution_in_bounds:
  assumes "t \<in> T"
  assumes init: "x t0 = x0"
  assumes cont: "continuous_on {t0..t} x"
  assumes solves: "\<And>s. s \<in> {t0..t} \<Longrightarrow> (x has_vector_derivative f (s, x s)) (at s within {t0..t})"
  shows "x t \<in> X"
  using assms by (rule in_bounds_derivativeI)

lemma is_solution_eq_is_solution_on_supersetdomain:
  assumes "X \<subseteq> X'"
  shows "is_solution = ivp.is_solution (i\<lparr>ivp_X:=X'\<rparr>)"
proof -
  interpret ivp': ivp "i\<lparr>ivp_X:=X'\<rparr>" using iv_defined assms by unfold_locales auto
  show ?thesis using assms
  proof (safe intro!: ext)
   fix x assume "ivp'.is_solution x"
    moreover
    from ivp'.is_solutionD[OF this] ivp'.solution_continuous_on[OF this]
    have "\<And>t. t \<in> T \<Longrightarrow> x t \<in> X" using assms
      by (intro solution_in_bounds) (force simp: interval
        intro: continuous_on_subset has_vector_derivative_within_subset)+
    ultimately show "is_solution x"
      by (auto intro!: is_solutionI dest: ivp'.is_solutionD simp add: interval)
  qed (intro is_solution_on_superset_domain)
qed

end

text {* For the numerical approximation, it is necessary that f is
lipschitz-continuous outside the actual domain - therefore D'. *}

locale unique_on_rectangle =
  solution_in_rectangle + global_lipschitz: global_lipschitz T X' f L for L X' +
  assumes lipschitz_on_domain: "X \<subseteq> X'"
begin

lemma lipschitz': "t \<in> T \<Longrightarrow> lipschitz X (\<lambda>x. f (t, x)) L" "0 \<le> L"
  using global_lipschitz.lipschitz lipschitz_on_domain
  by (auto intro: lipschitz_subset)

end

sublocale unique_on_rectangle \<subseteq> unique_on_closed
proof
  show "0 \<le> L" "closed X" using lipschitz' by (simp_all add: rectangle)
  fix t assume "t \<in> T" with lipschitz' show "lipschitz X (\<lambda>x. f (t, x)) L" by simp
qed (rule integral_in_bounds)

lemma (in unique_on_rectangle) unique_on_rectangle_subset:
  assumes "t0 \<le> t1'" "t1' \<le> t1"
  shows "unique_on_rectangle (i\<lparr>ivp_T:={t0..t1'}\<rparr>) t1' b B L X'"
  using iv_defined rectangle interval assms b_pos
    continuous_on_subset[OF continuous, of "{t0..t1'} \<times> X"]
    norm_f t1_bounded global_lipschitz.lipschitz lipschitz_on_domain
  by unfold_locales  --{*slow*}
     (fastforce simp: Times_subset_cancel2 order.trans[OF assms] simp del: of_nat_Suc)+

locale unique_on_rectangle_superset = subset?: unique_on_rectangle + fixes X'' assumes superset: "X' \<subseteq> X''"
begin

sublocale superset_domain?: has_solution "i\<lparr>ivp_X:=X''\<rparr>"
  using iv_defined lipschitz_on_domain superset
  by unfold_locales (auto intro!: exI[where x=solution] is_solution_on_superset_domain)

lemma sup_solution_is_solution: "is_solution x \<Longrightarrow> subset.is_solution x"
  using assms lipschitz_on_domain superset
  by (subst is_solution_eq_is_solution_on_supersetdomain[of X'']) auto

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
  note solutions_eq[OF `t \<in> T`, symmetric]
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

locale derivative_on_convex =
  fixes T X and f::"(real \<times> 'a::ordered_euclidean_space) \<Rightarrow> 'a" and f'
  assumes convex: "convex T" "convex X"
  assumes nonempty: "T \<noteq> {}" "X \<noteq> {}"
  assumes f': "\<And>t x. t \<in> T \<Longrightarrow> x \<in> X \<Longrightarrow> (f has_derivative f' (t, x)) (at (t, x) within (T \<times> X))"

locale compact_domain =
  fixes X assumes compact: "compact X"

lemma norm_scale_inverse_self: "norm (x /\<^sub>R norm x) \<le> 1"
  by (auto simp: inverse_eq_divide)

locale continuously_diff =
  fixes f'::"(real \<times> 'a::ordered_euclidean_space) \<Rightarrow> (real \<times> 'a::ordered_euclidean_space) \<Rightarrow> 'a"
  assumes cont_diff: "continuous_on ((T\<times>X)\<times>cball 0 1) (\<lambda>(tx, dtdx). f' tx dtdx)"

locale compact_continuously_diff =
  compact_domain X +
  derivative_on_convex T X f f' +
  continuously_diff f' for T X f f' +
  assumes compact_domain1: "compact T"
  assumes nonempty_domains: "T \<noteq> {}" "X \<noteq> {}"
begin

lemma ex_onorm_bound:
  "\<exists>B. \<forall>t x. t \<in> T \<longrightarrow> x \<in> X \<longrightarrow> onorm (f' (t, x)) \<le> B"
proof -
  have "compact ((\<lambda>(tx, dtdx). f' tx dtdx) ` ((T \<times> X) \<times> cball 0 1))" (is "compact ?F'")
    by (rule compact_continuous_image[OF cont_diff])
      (auto intro!: compact_Times compact_domain1 compact)
  hence "bounded ?F'"
    by (rule compact_imp_bounded)
  then obtain B where B: "\<And>x. x\<in>?F' \<Longrightarrow> norm x \<le> B" unfolding bounded_iff by blast
  show ?thesis
  proof (rule exI[where x= B], safe)
    fix t x assume "t \<in> T" "x \<in> X"
    interpret bounded_linear "f' (t, x)"
      by (auto simp: algebra_simps intro!: has_derivative_bounded_linear[OF f'[OF `t \<in> T` `x \<in> X`]])
    show "onorm (f' (t, x)) \<le> B"
    proof (rule onorm_le, safe)
      fix a b
      from scaleR[of "inverse (norm (a, b))" "(a, b)"]
      have "norm (f' (t, x) (a, b)) =
          norm (f' (t, x) (inverse (norm (a, b)) *\<^sub>R (a, b))) * norm (a, b)" (is "_ = ?f * _")
        by (auto simp: field_simps) (simp add: zero_prod_def)
      also
      have uball: "(a, b) /\<^sub>R norm (a, b) \<in> cball 0 1"
        unfolding cball_def
        apply rule
        apply (subst dist_commute)
        apply (subst norm_conv_dist[symmetric])
        apply (rule norm_scale_inverse_self)
        done
      hence "?f \<le> B"
        using `t \<in> T` `x \<in> X` by (safe intro!: pair_imageI B)
      finally show "norm (f' (t, x) (a, b)) \<le> B * norm (a, b)" by (auto simp: mult_right_mono)
    qed
  qed
qed

definition "onorm_bound = (SOME B. \<forall>t x. t \<in> T \<longrightarrow> x \<in> X \<longrightarrow> onorm (f' (t, x)) \<le> B)"

lemma onorm_bound: assumes "t \<in> T" "x \<in> X" shows "onorm (f' (t, x)) \<le> onorm_bound"
  unfolding onorm_bound_def
  using someI_ex[OF ex_onorm_bound] assms
  by blast

sublocale closed_domain X
  using compact by (unfold_locales) (rule compact_imp_closed)

sublocale global_lipschitz T X f onorm_bound
proof (unfold_locales, rule lipschitzI)
  fix t x y
  assume txy: "t \<in> T" "x \<in> X" "y \<in> X"
  from onorm_bound have "norm (f (t, x) - f (t, y)) \<le> onorm_bound * norm ((t, x) - (t, y))"
    using txy
    by (intro differentiable_bound) (auto intro!: f' convex_Times[OF convex])
  thus "dist (f (t, x)) (f (t, y)) \<le> onorm_bound * dist x y"
    by (auto simp: dist_norm norm_Pair)
next
  from nonempty_domains obtain t x where t: "t \<in> T" and x: "x \<in> X" by auto
  show "0 \<le> onorm_bound"
    apply (rule order_trans)
    apply (rule onorm_pos_le)
    apply (rule has_derivative_bounded_linear[OF f'[OF t x]])
    apply (rule onorm_bound[OF t x])
    done
qed

end

locale unique_on_closed_cont_diff =
  self_mapping +
  continuous T X f +
  compact_domain X +
  derivative_on_convex T X f +
  continuously_diff f'
begin

sublocale compact_continuously_diff T X f f'
  using iv_defined
  by unfold_locales (auto simp: interval)

sublocale unique_on_closed i t1 onorm_bound
  by unfold_locales

end

end
