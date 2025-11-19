(*
  File: Path_Automation_Library.thy
  Author: Manuel Eberl, University of Innsbruck

  Auxiliary material, mostly about paths. Some of it about real functions, fractional part, etc.
  TODO: Most or all of it should be moved to the distribution.
*)
section \<open>Auxiliary material\<close>
theory Path_Automation_Library
  imports "HOL-Complex_Analysis.Complex_Analysis"
begin

subsection \<open>Miscellaneous\<close>

(* TODO: Move? *)
lemma cis_multiple_2pi':
  "n \<in> \<int> \<Longrightarrow> cis (2 * n * pi) = 1"
  "n \<in> \<int> \<Longrightarrow> cis (2 * (n * pi)) = 1"
  "n \<in> \<int> \<Longrightarrow> cis (pi * (2 * n)) = 1"
  "n \<in> \<int> \<Longrightarrow> cis (pi * (n * 2)) = 1"
  using cis_multiple_2pi[of n] by (simp_all only: mult_ac)

lemma dist_linepath1: "dist (linepath a b x) a = \<bar>x\<bar> * dist a b"
proof -
  have "dist (linepath a b x) a = norm (x *\<^sub>R (b - a))"
    unfolding scaleR_diff_right
    by (simp add: linepath_def dist_norm algebra_simps)
  also have "\<dots> = \<bar>x\<bar> * dist a b"
    by (subst norm_scaleR) (auto simp: dist_norm norm_minus_commute)
  finally show ?thesis .
qed

lemma dist_linepath2: "dist (linepath a b x) b = \<bar>1 - x\<bar> * dist a b"
proof -
  have "dist (linepath a b x) b = norm ((x - 1) *\<^sub>R (b - a))"
    unfolding scaleR_diff_right
    by (simp add: linepath_def dist_norm algebra_simps)
  also have "\<dots> = \<bar>x - 1\<bar> * dist a b"
    by (subst norm_scaleR) (auto simp: dist_norm norm_minus_commute)
  finally show ?thesis
    by (simp add: abs_minus_commute)
qed


subsection \<open>Some facts about strict monotonicity\<close>

(* TODO: Move? *)
lemma strict_mono_on_atLeastAtMost_combine:
  fixes f :: "'a :: linorder \<Rightarrow> 'b :: linorder"
  assumes "strict_mono_on {a..b} f" "strict_mono_on {b..c} f"
  shows   "strict_mono_on {a..c} f"
proof (rule strict_mono_onI)
  fix r s
  assume rs: "r \<in> {a..c}" "s \<in> {a..c}" "r < s"
  consider "r \<in> {a..b}" "s \<in> {a..b}" | "r \<in> {a..b}" "s \<in> {b<..c}" | "r \<in> {b..c}" "s \<in> {b..c}"
    using rs by force
  thus "f r < f s"
  proof cases
    assume rs: "r \<in> {a..b}" "s \<in> {b<..c}"
    have "f r \<le> f b"
      using rs by (intro strict_mono_on_leD[OF assms(1)]) auto
    also have "f b < f s"
      using rs by (intro strict_mono_onD[OF assms(2)]) auto
    finally show "f r < f s" .
  qed (use assms \<open>r < s\<close> in \<open>auto simp: strict_mono_on_def\<close>)
qed

(* TODO: Move to HOL.Fun *)
lemma mono_on_compose:
  assumes "mono_on A f" "mono_on B g" "f ` A \<subseteq> B"
  shows   "mono_on A (g \<circ> f)"
  unfolding o_def
  by (intro mono_onI mono_onD[OF assms(1)] mono_onD[OF assms(2)]) (use assms(3) in auto)

(* TODO: Move to HOL.Fun *)
lemma strict_mono_on_compose:
  assumes "strict_mono_on B g" "strict_mono_on A f" "f ` A \<subseteq> B"
  shows   "strict_mono_on A (g \<circ> f)"
  unfolding strict_mono_on_def using assms(3)
  by (auto simp: strict_mono_on_def intro!: assms(1,2)[THEN strict_mono_onD])

(* TODO: delete; already in isabelle-dev *)
lemma strict_mono_on_less:
  assumes "strict_mono_on S (f::'a :: linorder \<Rightarrow> 'b::preorder)"
  assumes "x \<in> S" "y \<in> S"
  shows "f x < f y \<longleftrightarrow> x < y"
  using strict_mono_onD[OF assms(1,2,3)] strict_mono_onD[OF assms(1,3,2)]
        order_less_imp_not_less[of "f x" "f y"]
  by (cases x y rule: linorder_cases) auto

(* TODO: Move to HOL.Fun *)
lemma strict_mono_on_imp_strict_mono_on_inv:
  fixes f :: "'a :: linorder \<Rightarrow> 'b :: preorder"
  assumes "strict_mono_on {a..b} f"
  assumes "\<And>x. x \<in> {a..b} \<Longrightarrow> g (f x) = x"
  shows   "strict_mono_on (f ` {a..b}) g"
proof (rule strict_mono_onI, safe)
  fix r s assume rs: "r \<in> {a..b}" "s \<in> {a..b}" "f r < f s"
  thus "g (f r) < g (f s)"
    using strict_mono_on_less[OF assms(1)] rs by (auto simp: assms(2))
qed

(* TODO: Move to HOL.Fun *)
lemma strict_mono_on_imp_strict_mono_on_inv_into:
  fixes f :: "'a :: linorder \<Rightarrow> 'b :: preorder"
  assumes "strict_mono_on {a..b} f"
  shows   "strict_mono_on (f ` {a..b}) (inv_into {a..b} f)"
  using strict_mono_on_imp_strict_mono_on_inv[OF
          assms inv_into_f_f[OF strict_mono_on_imp_inj_on[OF assms]]]
  by blast

text \<open>
  Nice lemma taken from
    Austin, A. K. (1985). 69.8 Two Curiosities. The Mathematical Gazette,
    69(447), 42–44. \<^url>\<open>https://doi.org/10.2307/3616452\<close>.

  A strictly monotonic function \<open>f\<close> on some closed real interval has a
  continuous (and strictly monotonic) inverse function \<open>g\<close> -- even if \<open>f\<close> itself
  is not continuous.
\<close>
(* TODO Move. Not sure where. It uses one theorem from HOL-Analysis, @{thm "continuous_onI"}.
   That dependency could be removed. But probably easiest to move it to HOL-Analysis.
*)
lemma strict_mono_on_imp_continuous_on_inv:
  fixes f :: "real \<Rightarrow> real"
  assumes "strict_mono_on {a..b} f"
  assumes "\<And>x. x \<in> {a..b} \<Longrightarrow> g (f x) = x"
  shows   "continuous_on (f ` {a..b}) g"
proof (cases "a < b")
  case False
  thus ?thesis
    by (cases "a = b") auto
next
  case ab: True
  show ?thesis
  proof (rule continuous_onI, safe)
    fix x \<epsilon> :: real
    assume \<epsilon>: "\<epsilon> > 0" and x: "x \<in> {a..b}"
  
    consider "x = a" | "x = b" | "x \<in> {a<..<b}"
      using x by force
    thus "\<exists>d>0. \<forall>x'\<in>f ` {a..b}. dist x' (f x) < d \<longrightarrow> dist (g x') (g (f x)) \<le> \<epsilon>"
    proof cases
      assume [simp]: "x = a"
      define \<epsilon>' where "\<epsilon>' = min \<epsilon> ((b - a) / 2)"
      have \<epsilon>': "\<epsilon>' > 0" "\<epsilon>' \<le> \<epsilon>" "\<epsilon>' < b - a"
        using \<epsilon> \<open>a < b\<close> by (auto simp: \<epsilon>'_def min_less_iff_disj)
      define \<delta> where "\<delta> = f (a + \<epsilon>') - f a"
      show ?thesis
      proof (rule exI[of _ \<delta>], safe)
        show "\<delta> > 0"
          using \<open>a < b\<close> \<epsilon>' by (auto simp: \<delta>_def intro!: strict_mono_onD[OF assms(1)])
      next
        fix t assume t: "t \<in> {a..b}" "dist (f t) (f x) < \<delta>"
        have "f t \<ge> f a"
          using \<open>a < b\<close> t by (intro strict_mono_on_leD[OF assms(1)]) auto
        with t have "f t - f a < \<delta>"
          by (simp add: dist_norm)
        hence "f t < f (a + \<epsilon>')"
          unfolding \<delta>_def by linarith
        hence "t < a + \<epsilon>'"
          using t \<epsilon>' by (subst (asm) strict_mono_on_less[OF assms(1)]) auto
        thus "dist (g (f t)) (g (f x)) \<le> \<epsilon>"
          using \<open>a < b\<close> t \<open>f t \<ge> f a\<close> \<epsilon>' by (simp add: assms dist_norm)
      qed

    next

      assume [simp]: "x = b"
      define \<epsilon>' where "\<epsilon>' = min \<epsilon> ((b - a) / 2)"
      have \<epsilon>': "\<epsilon>' > 0" "\<epsilon>' \<le> \<epsilon>" "\<epsilon>' < b - a"
        using \<epsilon> \<open>a < b\<close> by (auto simp: \<epsilon>'_def min_less_iff_disj)
      define \<delta> where "\<delta> = f b - f (b - \<epsilon>')"
      show ?thesis
      proof (rule exI[of _ \<delta>], safe)
        show "\<delta> > 0"
          using \<open>a < b\<close> \<epsilon>' by (auto simp: \<delta>_def intro!: strict_mono_onD[OF assms(1)])
      next
        fix t assume t: "t \<in> {a..b}" "dist (f t) (f x) < \<delta>"
        have "f t \<le> f b"
          using \<open>a < b\<close> t by (intro strict_mono_on_leD[OF assms(1)]) auto
        with t have "f b - f t < \<delta>"
          by (simp add: dist_norm)
        hence "f t > f (b - \<epsilon>')"
          unfolding \<delta>_def by linarith
        hence "t > b - \<epsilon>'"
          using t \<epsilon>' by (subst (asm) strict_mono_on_less[OF assms(1)]) auto
        thus "dist (g (f t)) (g (f x)) \<le> \<epsilon>"
          using \<open>a < b\<close> t \<open>f t \<le> f b\<close> \<epsilon>' by (simp add: assms dist_norm)
      qed

    next

      assume x: "x \<in> {a<..<b}"
      define \<epsilon>' where "\<epsilon>' = min \<epsilon> (min (x - a) (b - x) / 2)"
      have \<epsilon>': "\<epsilon>' > 0" "\<epsilon>' \<le> \<epsilon>" "\<epsilon>' < x - a" "\<epsilon>' < b - x"
        using \<epsilon> x by (auto simp: \<epsilon>'_def min_less_iff_disj)
      define \<delta> where "\<delta> = min (f x - f (x - \<epsilon>')) (f (x + \<epsilon>') - f x)"
      have *: "f (x - \<epsilon>') < f x" "f x < f (x + \<epsilon>')" 
        using \<epsilon>' by (intro strict_mono_onD[OF assms(1)]; simp)+
      show ?thesis
      proof (rule exI[of _ \<delta>], safe)
        show "\<delta> > 0"
          using * \<epsilon>' by (auto simp add: \<delta>_def)
      next
        fix t assume t: "t \<in> {a..b}" "dist (f t) (f x) < \<delta>"
        have "dist (g (f t)) (g (f x)) \<le> \<epsilon>'"
        proof (cases "t \<ge> x")
          case True
          hence "f t \<ge> f x"
            by (intro strict_mono_on_leD[OF assms(1)]) (use x t in auto)
          with t have "f t - f x < \<delta>"
            by (simp add: dist_norm)
          hence "f t < f (x + \<epsilon>')"
            unfolding \<delta>_def by linarith
          hence "t < x + \<epsilon>'"
            by (subst (asm) strict_mono_on_less[OF assms(1)]) (use x t \<epsilon>' in auto)
          thus ?thesis
            using x t True by (simp add: assms dist_norm)
        next
          case False
          hence "f t \<le> f x"
            by (intro strict_mono_on_leD[OF assms(1)]) (use x t in auto)
          with t have "f x - f t < \<delta>"
            by (simp add: dist_norm)
          hence "f t > f (x - \<epsilon>')"
            unfolding \<delta>_def by linarith
          hence "t > x - \<epsilon>'"
            by (subst (asm) strict_mono_on_less[OF assms(1)]) (use x t \<epsilon>' in auto)
          thus ?thesis
            using x t False by (simp add: assms dist_norm)
        qed
        also have "\<dots> \<le> \<epsilon>"
          by fact
        finally show "dist (g (f t)) (g (f x)) \<le> \<epsilon>" .
      qed
    qed
  qed
qed

lemma strict_mono_on_imp_continuous_on_inv_into:
  fixes f :: "real \<Rightarrow> real"
  assumes "strict_mono_on {a..b} f"
  shows   "continuous_on (f ` {a..b}) (inv_into {a..b} f)"
proof (rule strict_mono_on_imp_continuous_on_inv)
  show "inv_into {a..b} f (f x) = x" if "x \<in> {a..b}" for x
    using inv_into_f_f[OF strict_mono_on_imp_inj_on[OF assms] that] .
qed fact+


subsection \<open>General lemmas about topology\<close>

(* TODO: Move to HOL.Topological_Spaces (e.g. near the continuous_def *)
lemma continuous_cong:
  assumes "eventually (\<lambda>x. f x = g x) F" "f (netlimit F) = g (netlimit F)"
  shows   "continuous F f \<longleftrightarrow> continuous F g"
  unfolding continuous_def using assms by (intro filterlim_cong) simp_all

(* TODO: Move to HOL-Analysis.Elementary_Topology *)
lemma at_within_atLeastAtMost_eq_bot_iff_real:
  "at x within {a..b} = bot \<longleftrightarrow> x \<notin> {a..b::real} \<or> a = b"
  by (cases a b rule: linorder_cases) (auto simp: trivial_limit_within islimpt_finite)

(* TODO: Move to HOL.Topological_Spaces *)
lemma eventually_in_pointed_at: "eventually (\<lambda>x. x \<in> A - {y}) (at y within A)"
  by (simp add: eventually_at_filter)


(* 
  TODO: I suggest putting all of the following ones near their dependencies, 
  e.g. at_within_Icc_at_right in HOL.Topological_Spaces*)

lemma (in order_topology) at_within_Icc_Icc_right:
  assumes "a \<le> x" "x < b" "b \<le> c"
  shows   "at x within {a..c} = at x within {a..b}"
  by (cases "x = a") (use assms in \<open>simp_all add: at_within_Icc_at_right at_within_Icc_at\<close>)

lemma (in order_topology) at_within_Icc_Icc_left:
  assumes "a \<le> b" "b < x" "x \<le> c"
  shows   "at x within {a..c} = at x within {b..c}"
  by (cases "x = c") (use assms in \<open>simp_all add: at_within_Icc_at_left at_within_Icc_at\<close>)

lemma (in order_topology)
  assumes "a < b"
  shows at_within_Ico_at_right: "at a within {a..<b} = at_right a"
    and at_within_Ico_at_left:  "at b within {a..<b} = at_left b"
  using order_tendstoD(2)[OF tendsto_ident_at assms, of "{a<..}"]
  using order_tendstoD(1)[OF tendsto_ident_at assms, of "{..<b}"]
  by (auto intro!: order_class.order_antisym filter_leI
      simp: eventually_at_filter less_le
      elim: eventually_elim2)

lemma (in order_topology)
  assumes "a < b"
  shows at_within_Ioc_at_right: "at a within {a<..b} = at_right a"
    and at_within_Ioc_at_left:  "at b within {a<..b} = at_left b"
  using order_tendstoD(2)[OF tendsto_ident_at assms, of "{a<..}"]
  using order_tendstoD(1)[OF tendsto_ident_at assms, of "{..<b}"]
  by (auto intro!: order_class.order_antisym filter_leI
      simp: eventually_at_filter less_le
      elim: eventually_elim2)

lemma (in order_topology) at_within_Ico_at: "a < x \<Longrightarrow> x < b \<Longrightarrow> at x within {a..<b} = at x"
  by (rule at_within_open_subset[where S="{a<..<b}"]) auto

lemma (in order_topology) at_within_Ioc_at: "a < x \<Longrightarrow> x < b \<Longrightarrow> at x within {a<..b} = at x"
  by (rule at_within_open_subset[where S="{a<..<b}"]) auto

lemma (in order_topology) at_within_Ioo_at: "a < x \<Longrightarrow> x < b \<Longrightarrow> at x within {a<..<b} = at x"
  by (rule at_within_open_subset[where S="{a<..<b}"]) auto

lemma (in order_topology) at_within_Icc_Ico:
  assumes "a \<le> x" "x < b"
  shows   "at x within {a..b} = at x within {a..<b}"
  by (cases "x = a")
     (use assms in \<open>simp_all add: at_within_Icc_at_right at_within_Ico_at_right
                                  at_within_Ico_at at_within_Icc_at\<close>)

lemma (in order_topology) at_within_Icc_Ioc:
  assumes "a < x" "x \<le> b"
  shows   "at x within {a..b} = at x within {a<..b}"
  by (cases "x = b")
     (use assms in \<open>simp_all add: at_within_Icc_at_left at_within_Ioc_at_left
                                  at_within_Ioc_at at_within_Icc_at\<close>)


subsection \<open>General lemmas about real functions\<close>

(* TODO: move to HOL.Topological_Spaces? *)
lemma isCont_real_If_combine:
  fixes x :: real
  assumes [simp]: "f x = h x" "g x = h x"
  assumes contf: "continuous (at_left x) f"
  assumes contg: "continuous (at_right x) g"
  assumes f: "eventually (\<lambda>y. h y = f y) (at_left x)"
  assumes g: "eventually (\<lambda>y. h y = g y) (at_right x)"
  shows   "continuous (at x) h"
  unfolding continuous_at_split
proof
  have "continuous (at_left x) f \<longleftrightarrow> continuous (at_left x) h"
    by (intro continuous_cong eventually_mono[OF f]) (auto simp: Lim_ident_at)
  with contf show "continuous (at_left x) h" by blast
next
  have "continuous (at_right x) g \<longleftrightarrow> continuous (at_right x) h"
    by (intro continuous_cong eventually_mono[OF g]) (auto simp: Lim_ident_at)
  with contg show "continuous (at_right x) h" by blast
qed

(* TODO: move to HOL.Topological_Spaces? *)
lemma continuous_on_real_If_combine:
  fixes f g :: "real \<Rightarrow> 'a :: topological_space"
  assumes "continuous_on {a..b} f"
  assumes "continuous_on {b..c} g"
  assumes "f b = g b" "a \<le> b" "b \<le> c"
  defines "h \<equiv> (\<lambda>x. if x \<le> b then f x else g x)"
  shows   "continuous_on {a..c} h"
proof (cases "a = b \<or> b = c")
  case True
  thus ?thesis
  proof
    assume [simp]: "a = b"
    have "continuous_on {a..c} g"
      using assms by (simp add: continuous_on_imp_continuous_within)
    also have "?this \<longleftrightarrow> continuous_on {a..c} h"
      by (intro continuous_on_cong) (auto simp: assms)
    finally show ?thesis .
  next
    assume [simp]: "b = c"
    have "continuous_on {a..c} f"
      using assms by (simp add: continuous_on_imp_continuous_within)
    also have "?this \<longleftrightarrow> continuous_on {a..c} h"
      by (intro continuous_on_cong) (auto simp: assms)
    finally show ?thesis .
  qed
next
  case False
  hence abc: "a < b" "b < c"
    using assms by auto
  note [simp] = at_within_atLeastAtMost_eq_bot_iff_real Lim_ident_at
  have "continuous (at x within {a..c}) h" if x: "x \<in> {a..c}" for x
  proof (cases x b rule: linorder_cases)
    case [simp]: equal
    have "continuous (at b) h"
      unfolding continuous_at_split
    proof
      have "continuous (at b within {a..b}) f"
        using assms x by (simp add: continuous_on_imp_continuous_within)
      also have "at b within {a..b} = at_left b"
        using abc by (simp add: at_within_Icc_at_left)
      also have ev: "eventually (\<lambda>x. x < b) (at_left b)"
        using eventually_at_topological by blast
      have "continuous (at_left b) f \<longleftrightarrow> continuous (at_left b) h"
        using assms by (intro continuous_cong eventually_mono[OF ev]) (auto simp: h_def)
      finally show "continuous (at_left b) h" .
    next
      have "continuous (at b within {b..c}) g"
        using assms x by (simp add: continuous_on_imp_continuous_within)
      also have "at b within {b..c} = at_right b"
        using abc by (simp add: at_within_Icc_at_right)
      also have ev: "eventually (\<lambda>x. x > b) (at_right b)"
        using eventually_at_topological by blast
      have "continuous (at_right b) g \<longleftrightarrow> continuous (at_right b) h"
        using assms by (intro continuous_cong eventually_mono[OF ev]) (auto simp: h_def)
      finally show "continuous (at_right b) h" .
    qed
    thus ?thesis
      using continuous_at_imp_continuous_at_within local.equal by blast
  next
    case less
    have "continuous (at x within {a..b}) f"
      using assms less x by (simp add: continuous_on_imp_continuous_within)
    also have "eventually (\<lambda>y. y \<in> {a..b} - {x}) (at x within {a..b})"
      by (rule eventually_in_pointed_at)
    hence "eventually (\<lambda>y. f y = h y) (at x within {a..b})"
      by eventually_elim (auto simp: h_def)
    hence "continuous (at x within {a..b}) f \<longleftrightarrow> continuous (at x within {a..b}) h"
      using assms less x by (intro continuous_cong) simp_all
    also have "at x within {a..b} = at x within {a..c}"
      by (rule sym, rule at_within_Icc_Icc_right) (use x less assms in auto)
    finally show ?thesis .
  next
    case greater
    have "continuous (at x within {b..c}) g"
      using assms greater x by (simp add: continuous_on_imp_continuous_within)
    also {
      have "eventually (\<lambda>y. y \<in> {b<..c} - {x}) (at x within {b<..c})"
        by (rule eventually_in_pointed_at)
      also have "at x within {b<..c} = at x within {b..c}"
        using greater assms x by (metis atLeastAtMost_iff at_within_Icc_Ioc)
      finally have "eventually (\<lambda>y. g y = h y) (at x within {b..c})"
        by eventually_elim (use greater in \<open>auto simp: h_def\<close>)
    }
    hence "continuous (at x within {b..c}) g \<longleftrightarrow> continuous (at x within {b..c}) h"
      using assms greater x by (intro continuous_cong) simp_all
    also have "at x within {b..c} = at x within {a..c}"
      by (rule sym, rule at_within_Icc_Icc_left) (use x greater assms in auto)
    finally show ?thesis .
  qed
  thus ?thesis
    using continuous_on_eq_continuous_within by blast
qed

(* TODO: move to HOL.Topological_Spaces? *)
lemma continuous_on_real_If_combine':
  fixes f g :: "real \<Rightarrow> 'a :: topological_space"
  assumes "continuous_on {a..b} f"
  assumes "continuous_on {b..c} g"
  assumes "f b = g b" "a \<le> b" "b \<le> c"
  defines "h \<equiv> (\<lambda>x. if x < b then f x else g x)"
  shows   "continuous_on {a..c} h"
proof -
  have "continuous_on {-c..-a} ((\<lambda>x. if x \<le> -b then (g \<circ> uminus) x else (f \<circ> uminus) x))"
    (is "continuous_on _ ?h'")
    using assms
    by (intro continuous_on_real_If_combine continuous_on_compose continuous_intros) auto
  hence "continuous_on {a..c} (?h' \<circ> uminus)"
    by (intro continuous_on_compose continuous_intros) auto
  also have "?h' \<circ> uminus = h"
    by (auto simp: h_def fun_eq_iff)
  finally show ?thesis .
qed

(* TODO: move to HOL-Analysis.Path_Connected *)
lemma continuous_on_linepath [continuous_intros]:
  assumes "continuous_on A f" "continuous_on A g" "continuous_on A h"
  shows   "continuous_on A (\<lambda>x. linepath (f x) (g x) (h x))"
  unfolding linepath_def by (intro continuous_intros assms)


subsection \<open>Rounding and fractional part\<close>

(* general properties of floor, ceiling, frac for any type *)

(* TODO: Move to HOL.Archimedean_Field *)
lemma frac_of_Int [simp]: "x \<in> \<int> \<Longrightarrow> frac x = 0"
  by (subst frac_eq_0_iff)

(* TODO: Move to HOL.Archimedean_Field *)
lemma floor_less_not_int: "x \<notin> \<int> \<Longrightarrow> of_int (floor x) < x"
  by (metis Ints_of_int floor_correct order_less_le)

(* TODO: Move to HOL.Archimedean_Field *)
lemma less_ceiling_not_int: "x \<notin> \<int> \<Longrightarrow> of_int (ceiling x) > x"
  by (meson floor_less_iff floor_less_not_int less_ceiling_iff)

(* TODO: Move to HOL.Archimedean_Field *)
lemma image_frac_atLeastLessThan:
  assumes "y \<ge> x + (1 :: 'a :: floor_ceiling)"
  shows   "frac ` {x..<y} = {0..<1}"
proof safe
  fix t :: 'a assume t: "t \<in> {0..<1}"
  define u where "u = (if t \<ge> frac x then t + of_int \<lfloor>x\<rfloor> else t + of_int \<lfloor>x\<rfloor> + 1)"
  have "frac u = t"
    using t by (auto simp: u_def frac_def floor_unique)
  moreover {
    have "x \<le> t + of_int \<lfloor>x\<rfloor> + 1"
      using assms t unfolding atLeastLessThan_iff by linarith
    moreover have "t + of_int \<lfloor>x\<rfloor> < y"
      using assms t unfolding atLeastLessThan_iff by linarith
    ultimately have "u \<in> {x..<y}"
      using assms by (auto simp: u_def frac_def)
  }
  ultimately show "t \<in> frac ` {x..<y}"
    by blast
qed (auto simp: frac_lt_1)

(* TODO: Move to HOL.Archimedean_Field *)
lemma image_frac_atLeastAtMost:
  assumes "y \<ge> x + 1"
  shows   "frac ` {x..y} = {0..<1}"
proof 
  have "{0..<1} = frac ` {x..<y}"
    by (rule sym, intro image_frac_atLeastLessThan assms)
  also have "\<dots> \<subseteq> frac ` {x..y}"
    by (intro image_mono) auto
  finally show "{0..<1} \<subseteq> frac ` {x..y}" .
qed (auto simp: frac_lt_1)


(* 
  TODO: Move the remaining ones from this section.
  They are specific to the type real: topological properties of frac (i.e. limits)
  Obvious place to put them would be where "continuous_frac" also lives, namely in HOL.Deriv.  
*)

lemma tendsto_frac_real [tendsto_intros]:
  assumes "(x :: real) \<notin> \<int>"
  shows   "(frac \<longlongrightarrow> frac x) (at x within A)"
  using assms continuous_at_imp_continuous_at_within continuous_frac continuous_within by blast

lemma tendsto_frac_at_left_int_real:
  assumes "(x :: real) \<in> \<int>"
  shows   "(frac \<longlongrightarrow> 1) (at_left x)"
proof -
  have "((\<lambda>y. y - real_of_int \<lfloor>x\<rfloor> + 1) \<longlongrightarrow> 1) (at_left x)"
    by (rule tendsto_eq_intros refl)+ (use assms in \<open>auto elim!: Ints_cases\<close>)
  moreover have "eventually (\<lambda>y. y \<in> {x-1<..<x}) (at_left x)"
    using eventually_at_left_real by force
  hence "eventually (\<lambda>y. frac y = y - real_of_int \<lfloor>x\<rfloor> + 1) (at_left x)"
  proof eventually_elim
    case (elim y)
    show "frac y = y - real_of_int \<lfloor>x\<rfloor> + 1"
      using assms elim by (subst frac_unique_iff) (auto elim!: Ints_cases)
  qed
  ultimately show ?thesis
    by (simp add: filterlim_cong)
qed

lemma filterlim_at_frac_at_left_int_real:
  assumes "(x :: real) \<in> \<int>"
  shows   "filterlim frac (at_left 1) (at_left x)"
  unfolding filterlim_at
proof
  show "\<forall>\<^sub>F y in at_left x. frac y \<in> {..<1} \<and> frac y \<noteq> 1"
  proof (intro always_eventually allI)
    fix y :: real
    show "frac y \<in> {..<1} \<and> frac y \<noteq> 1"
      using frac_lt_1[of y] by auto
  qed
qed (auto intro!: tendsto_frac_at_left_int_real assms)

lemma tendsto_frac_at_right_int_real:
  assumes "(x :: real) \<in> \<int>"
  shows   "(frac \<longlongrightarrow> 0) (at_right x)"
proof -
  have "((\<lambda>y. y - real_of_int \<lfloor>x\<rfloor>) \<longlongrightarrow> 0) (at_right x)"
    by (rule tendsto_eq_intros refl)+ (use assms in \<open>auto elim!: Ints_cases\<close>)
  moreover have "eventually (\<lambda>y. y \<in> {x<..<x+1}) (at_right x)"
    using eventually_at_right_real by force
  hence "eventually (\<lambda>y. frac y = y - real_of_int \<lfloor>x\<rfloor>) (at_right x)"
  proof eventually_elim
    case (elim y)
    show "frac y = y - real_of_int \<lfloor>x\<rfloor>"
      using assms elim by (subst frac_unique_iff) (auto elim!: Ints_cases)
  qed
  ultimately show ?thesis
    by (simp add: filterlim_cong)
qed

lemma filterlim_at_frac_at_right_int_real [tendsto_intros]:
  assumes "(x :: real) \<in> \<int>"
  shows   "filterlim frac (at_right 0) (at_right x)"
  unfolding filterlim_at
proof
  have "eventually (\<lambda>y. y \<in> {x<..<x+1}) (at_right x)"
    using eventually_at_right_real by force
  thus "\<forall>\<^sub>F x in at_right x. frac x \<in> {0<..} \<and> frac x \<noteq> 0"
  proof eventually_elim
    case (elim y)
    hence "y \<notin> \<int>"
      using assms by (auto elim!: Ints_cases)
    thus "frac y \<in> {0<..} \<and> frac y \<noteq> 0"
      using frac_ge_0[of x] by auto
  qed
qed (auto intro!:  tendsto_frac_at_right_int_real assms)

(* TODO: version for continuous? *)
lemma continuous_on_frac_real:
  assumes "continuous_on {0..1} f" "f 0 = f 1"
  shows   "continuous_on A (\<lambda>x::real. f (frac x))"
proof -
  have isCont_f: "isCont f x" if "x \<in> {0<..<1}" for x
    by (rule continuous_on_interior[OF assms(1)]) (use that in auto)
  note [continuous_intros] = continuous_at_compose[OF _ isCont_f, unfolded o_def]

  have contfl: "(f \<longlongrightarrow> f 0) (at_right 0)"
    using assms(1) by (simp add: continuous_on_Icc_at_rightD)
  have contfr: "(f \<longlongrightarrow> f 1) (at_left 1)"
    using assms(1) by (simp add: continuous_on_Icc_at_leftD)
  note tendsto_intros = filterlim_compose[OF contfr] filterlim_compose[OF contfl]

  have "continuous (at x) (\<lambda>x. f (frac x))" for x
  proof (cases "x \<in> \<int>")
    case True
    have "((\<lambda>x. f (frac x)) \<longlongrightarrow> f 1) (at_left x)"
      by (rule tendsto_intros filterlim_at_frac_at_left_int_real True)+
    moreover have "((\<lambda>x. f (frac x)) \<longlongrightarrow> f 0) (at_right x)"
      by (rule tendsto_intros filterlim_at_frac_at_right_int_real True)+
    ultimately show ?thesis
      using assms(2) True unfolding continuous_at_split unfolding continuous_def
      by (auto simp: Lim_ident_at elim!: Ints_cases)
  next
    case False
    have "x < 1 + real_of_int \<lfloor>x\<rfloor>"
      by linarith
    hence "continuous (at x) (\<lambda>y. f (y - \<lfloor>x\<rfloor>))"
      using floor_less_not_int[of x] False
      by (intro continuous_intros) (auto simp: algebra_simps)
    also have "eventually (\<lambda>y. y \<in> {floor x<..<ceiling x}) (nhds x)"
      using eventually_floor_less[OF filterlim_ident False]
            eventually_less_ceiling[OF filterlim_ident False]
      by eventually_elim auto
    hence "eventually (\<lambda>y. frac y = y - \<lfloor>x\<rfloor>) (nhds x)"
    proof eventually_elim
      case (elim y)
      hence "y - real_of_int \<lfloor>x\<rfloor> < 1"
        unfolding greaterThanLessThan_iff using ceiling_diff_floor_le_1[of x] by linarith
      thus ?case using elim
        by (subst frac_unique_iff) auto
    qed
    hence "eventually (\<lambda>y. f (y - \<lfloor>x\<rfloor>) = f (frac y)) (at x)"
      unfolding eventually_at_filter by eventually_elim (auto simp: frac_def)
    hence "isCont (\<lambda>y. f (y - \<lfloor>x\<rfloor>)) x = isCont (\<lambda>y. f (frac y)) x"
      by (intro continuous_cong) (auto simp: frac_def)
    finally show ?thesis .
  qed
  thus ?thesis
    using continuous_at_imp_continuous_on by blast
qed

lemma continuous_on_frac_real':
  assumes "continuous_on {0..1} f" "continuous_on A g" "f 0 = f 1"
  shows   "continuous_on A (\<lambda>x. f (frac (g x :: real)))"
  using continuous_on_compose2[OF continuous_on_frac_real[OF assms(1,3)] assms(2)] by blast


subsection \<open>General lemmas about paths\<close>

(* TODO: move to HOL-Analysis.Path_Connected *)
lemma linepath_scaleR: "(*\<^sub>R) c \<circ> linepath a b = linepath (c *\<^sub>R a) (c *\<^sub>R b)"
  by (simp add: linepath_def fun_eq_iff algebra_simps)

(* TODO: move to HOL-Analysis.Path_Connected *)
lemma linepath_mult_complex: "(*) c \<circ> linepath a b = linepath (c * a) (c * b :: complex)"
  by (simp add: linepath_def fun_eq_iff algebra_simps)

(* TODO: move to HOL-Analysis.Path_Connected *)
lemma linepath_translate: "(+) c \<circ> linepath a b = linepath (c + a) (c + b)"
  by (simp add: linepath_def fun_eq_iff algebra_simps)

(* TODO: move to HOL-Complex_Analysis.Contour_Integration *)
lemma part_circlepath_translate:
  "(+) c \<circ> part_circlepath x r a b = part_circlepath (c + x) r a b"
  by (simp add: part_circlepath_def fun_eq_iff algebra_simps)

(* TODO: move to HOL-Complex_Analysis.Contour_Integration *)
lemma circlepath_translate:
  "(+) c \<circ> circlepath x r = circlepath (c + x) r"
  by (simp add: circlepath_def part_circlepath_translate)

(* TODO: move to HOL-Analysis.Path_Connected *)
lemma rectpath_translate:
  "(+) c \<circ> rectpath a b = rectpath (c + a) (c + b)"
  by (simp add: rectpath_def linepath_translate Let_def path_compose_join plus_complex.ctr)

(* TODO: move to HOL-Analysis.Path_Connected *)
lemma path_image_cong: "(\<And>x. x \<in> {0..1} \<Longrightarrow> p x = q x) \<Longrightarrow> path_image p = path_image q"
  by (auto simp: path_image_def)

(* TODO: move to HOL-Analysis.Path_Connected *)
lemma path_cong: "(\<And>x. x \<in> {0..1} \<Longrightarrow> p x = q x) \<Longrightarrow> path p = path q"
  unfolding path_def by (intro continuous_on_cong) auto

(* TODO: move to HOL-Analysis.Path_Connected *)
lemma simple_path_cong:
  shows "(\<And>x. x \<in> {0..1} \<Longrightarrow> f x = g x) \<Longrightarrow> simple_path f \<longleftrightarrow> simple_path g"
  unfolding simple_path_def loop_free_def
  by (intro arg_cong2[of _ _ _ _ "(\<and>)"] path_cong) auto

(* TODO: move to HOL-Analysis.Path_Connected *)
lemma simple_path_reversepath_iff: "simple_path (reversepath g) \<longleftrightarrow> simple_path g"
  using simple_path_reversepath[of g] simple_path_reversepath[of "reversepath g"]
  by auto

(* TODO: move to HOL-Analysis.Path_Connected *)
lemma path_image_loop:
  assumes "pathstart p = pathfinish p"
  shows   "path_image p = p ` {0..<1}"
  unfolding path_image_def
proof safe
  fix x :: real assume x: "x \<in> {0..1}"
  have "(if x = 1 then 0 else x) \<in> {0..<1}" "p x = p (if x = 1 then 0 else x)"
    using assms x by (auto simp: pathstart_def pathfinish_def)
  thus "p x \<in> p ` {0..<1}"
    by blast
qed auto

(* TODO: move to HOL-Analysis.Path_Connected *)
lemma simple_pathD:
  assumes "simple_path p" "x \<in> {0..1}" "y \<in> {0..1}" "x \<noteq> y" "p x = p y"
  shows   "{x, y} = {0, 1}"
  using assms unfolding simple_path_def loop_free_def by blast

(* 
  TODO: add [trans] attribute to original theorem where it is proven
  The closely related homotopic_paths_trans already has it.
 *)
lemmas [trans] = homotopic_loops_trans

(* TODO: Move to HOL-Analysis.Homotopy *)
proposition homotopic_loops_reparametrize:
  assumes "path p" "pathstart p = pathfinish p"
      and pips: "path_image p \<subseteq> s"
      and contf: "continuous_on {0..1} f"
      and q: "\<And>t. t \<in> {0..1} \<Longrightarrow> q t = p (frac (f t))"
      and closed: "f 1 = f 0 + 1"
    shows "homotopic_loops s p q"
proof -
  note [continuous_intros] = continuous_on_frac_real'[OF continuous_on_path[OF \<open>path p\<close>]]
  note [continuous_intros] = continuous_on_compose2[OF contf]
  define h :: "real \<times> real \<Rightarrow> 'a" where "h = (\<lambda>(u,v). p (frac (linepath v (f v) u)))"

  have [simp]: "p (frac t) = p t" if "t \<in> {0..1}" for t
    using that assms(2) frac_eq[of t]
    by (cases "t = 1") (auto simp: pathstart_def pathfinish_def)

  show ?thesis
    unfolding homotopic_loops
  proof (rule exI[of _ h]; safe)
    fix v :: real assume v: "v \<in> {0..1}"
    show "h (0, v) = p v" and "h (1, v) = q v"
      using q v by (simp_all add: h_def linepath_def)
  next
    fix u v :: real assume uv: "u \<in> {0..1}" "v \<in> {0..1}"
    have "h (u, v) \<in> path_image p"
      by (auto simp: h_def path_image_def intro!: imageI less_imp_le[OF frac_lt_1])
    also have "\<dots> \<subseteq> s"
      by fact
    finally show "h (u, v) \<in> s" .
  next
    fix t :: real assume t: "t \<in> {0..1}"
    show "pathfinish (h \<circ> Pair t) = pathstart (h \<circ> Pair t)"
      using t by (auto simp: h_def pathfinish_def pathstart_def linepath_def 
                             closed algebra_simps frac_def)
  next
    show "continuous_on ({0..1}\<times>{0..1}) h"
      unfolding h_def case_prod_unfold using \<open>pathstart p = pathfinish p\<close>
      by (auto intro!: continuous_intros order.refl continuous_on_fst less_imp_le[OF frac_lt_1]
               simp: pathstart_def pathfinish_def)
  qed
qed



subsection \<open>Some facts about betweenness\<close>

(*
  TODO: Not sure where to put these. Somewhere in HOL-Analysis. Needs both "linepath" and "between"
  to be defined, but I don't know the import graph well enough to know the earliest descendent
  of both of those theories.
*)

lemma between_conv_linepath:
  fixes a b c :: "'a :: euclidean_space"
  assumes "between (a, c) b"
  shows   "b = linepath a c (dist a b / dist a c)" (is "_ = ?b'")
proof (cases "a = c")
  case False
  from assms obtain u where u: "u \<in> {0..1}" "b = (1 - u) *\<^sub>R a + u *\<^sub>R c"
    using assms by (auto simp: between_def closed_segment_def)
  have "dist a b = norm (u *\<^sub>R (a - c))"
    unfolding scaleR_diff_right by (simp add: u dist_norm algebra_simps)
  hence ab: "dist a b = u * dist a c"
    using u(1) by (simp add: dist_norm norm_minus_commute)
  define t where "t = dist a b / dist a c"
  have "linepath a c t =
          (1 - dist a b / dist a c) *\<^sub>R a + (dist a b / dist a c) *\<^sub>R c"
    by (simp add: ab linepath_def t_def)
  also have "(1 - dist a b / dist a c) = 1 - u"
    using False by (simp add: ab)
  also have "dist a b / dist a c = u"
    using False by (simp add: ab)
  also have "(1 - u) *\<^sub>R a + u *\<^sub>R c = b"
    by (simp add: u)
  finally show ?thesis
    by (simp add: u t_def)
qed (use assms in auto)

lemma between_trans1:
  assumes "between (a, c) b" "between (b, d) c" "b \<noteq> c" "a \<noteq> d"
  shows   "between (a, d) b"
proof (cases "distinct [a, b, c, d]")
  case False
  with assms show ?thesis
    by (auto simp: between_def)
next
  case True
  from assms(1) obtain u where u: "u \<in> {0..1}" "b = (1 - u) *\<^sub>R a + u *\<^sub>R c"
    by (auto simp: between_def closed_segment_def)
  from assms(2) obtain v where v: "v \<in> {0..1}" "c = (1 - v) *\<^sub>R b + v *\<^sub>R d"
    by (auto simp: between_def closed_segment_def)

  have "u \<noteq> 0" "u \<noteq> 1" "v \<noteq> 0" "v \<noteq> 1"
    using u v True by auto
  with u(1) v(1) have uv: "u \<in> {0<..<1}" "v \<in> {0<..<1}"
    by auto

  define z where "z = 1 - u * (1 - v)"
  define t where "t = (u * v) / z"
  have "u * (1 - v) < 1 * 1"
    using uv by (intro mult_strict_mono) auto
  hence *: "z > 0"
    unfolding z_def by auto

  have "b = (1 - u) *\<^sub>R a + (u * (1 - v)) *\<^sub>R b + (u * v) *\<^sub>R d"
    by (subst u, subst v) (simp add: algebra_simps)
  hence "z *\<^sub>R b = (1 - u) *\<^sub>R a + (u * v) *\<^sub>R d"
    by (simp add: algebra_simps z_def)
  hence "inverse z *\<^sub>R z *\<^sub>R b = inverse z *\<^sub>R ((1 - u) *\<^sub>R a + (u * v) *\<^sub>R d)"
    by (simp only: )
  also have "inverse z *\<^sub>R z *\<^sub>R b = b"
    using * by (simp add: field_simps)
  also have "inverse z *\<^sub>R ((1 - u) *\<^sub>R a + (u * v) *\<^sub>R d) =
             ((1 - u) / z) *\<^sub>R a + ((u * v) / z) *\<^sub>R d"
    using * by (simp add: algebra_simps divide_inverse)
  also have "(1 - u) / z = 1 - t"
    using * by (simp add: field_simps t_def z_def)
  also have "(u * v) / z = t"
    by (simp add: t_def)
  finally have "b = (1 - t) *\<^sub>R a + t *\<^sub>R d" .

  moreover have "t \<ge> 0"
    unfolding t_def using u(1) v(1) *
    by (intro divide_nonneg_pos mult_nonneg_nonneg) auto
  moreover have "(1 - u) / z \<ge> 0"
    using u(1) * by (intro divide_nonneg_pos) auto
  with \<open>(1 - u) / z = 1 - t\<close> have "t \<le> 1"
    by simp
  ultimately show ?thesis
    unfolding between_def prod.case closed_segment_def by blast
qed

lemma between_trans2:
  "between (a, c) b \<Longrightarrow> between (b, d) c \<Longrightarrow> b \<noteq> c \<Longrightarrow> a \<noteq> d \<Longrightarrow> between (a, d) c"
  using between_trans1[of d b c a] by (simp add: between_commute)

lemma between_trans1':
  assumes "between (a :: 'a :: euclidean_space, c) b" "between (b, d) c" "b \<noteq> c"
  shows   "between (a, d) b"
proof (cases "a = d")
  case True
  with assms show ?thesis
    using between_antisym between_commute by metis
qed (use between_trans1[OF assms] in simp)

lemma between_trans2':
  assumes "between (a :: 'a :: euclidean_space, c) b" "between (b, d) c" "b \<noteq> c"
  shows   "between (a, d) c"
proof (cases "a = d")
  case True
  with assms show ?thesis
    using between_antisym between_commute by metis
qed (use between_trans2[OF assms] in simp)

text \<open>
  The following expresses successive betweenness: e.g. \<open>betweens [a,b,c,d]\<close> means that the
  points \<open>a\<close>, \<open>b\<close>, \<open>c\<close>, \<open>d\<close> all lie on the same line in that order.
  Note that we do not have strict betweenness, i.e.\ some of the points might be identical.
\<close>
fun betweens :: "'a :: euclidean_space list \<Rightarrow> bool" where
  "betweens (x # y # z # xs) \<longleftrightarrow> between (x, z) y \<and> betweens (y # z # xs)"
| "betweens _ \<longleftrightarrow> True"


subsection \<open>Simple loops and orientation\<close>

(* TODO: Move all of this. Probably belongs to HOL-Complex_Analysis.Winding_Numbers. *)

text \<open>
  A simple loop is a continuous path whose start and end point coincide and which never intersects
  itself. In e.g.\ the complex plane, such a simple loop partitions the full complex plane into
  an inner and outer part by the Jordan Curve Theorem.
\<close>
definition simple_loop :: "(real \<Rightarrow> 'a :: topological_space) \<Rightarrow> bool"
  where "simple_loop p \<longleftrightarrow> simple_path p \<and> pathstart p = pathfinish p"

lemma simple_loop_reversepath [simp]: "simple_loop (reversepath p) \<longleftrightarrow> simple_loop p"
  by (auto simp: simple_loop_def simple_path_reversepath_iff)

text \<open>
  The winding number of a simple loop is either $1$ for any point inside the loop or $-1$ for any
  point inside the loop (and of course $0$ for all the points outside, and undefined for all the
  points on it).

  We refer to the winding number of the points inside a simple loop as their \<^emph>\<open>orientation\<close>,
  and we call simple loops with orientation $1$ \<^emph>\<open>counter-clockwise\<close> and those with orientation
  $-1$ \<^emph>\<open>clockwise\<close>.
\<close>
definition simple_loop_ccw :: "(real \<Rightarrow> complex) \<Rightarrow> bool" where
  "simple_loop_ccw p \<longleftrightarrow> simple_loop p \<and> (\<exists>z. z \<notin> path_image p \<and> winding_number p z = 1)"

definition simple_loop_cw :: "(real \<Rightarrow> complex) \<Rightarrow> bool" where
  "simple_loop_cw p \<longleftrightarrow> simple_loop p \<and> (\<exists>z. z \<notin> path_image p \<and> winding_number p z = -1)"

definition simple_loop_orientation :: "(real \<Rightarrow> complex) \<Rightarrow> int" where
  "simple_loop_orientation p =
     (if simple_loop_ccw p then 1 else if simple_loop_cw p then -1 else 0)"

lemma simple_loop_ccwI:
  "simple_loop p \<Longrightarrow> z \<notin> path_image p \<Longrightarrow> winding_number p z = 1 \<Longrightarrow> simple_loop_ccw p"
  unfolding simple_loop_ccw_def by auto

lemma simple_loop_cwI:
  "simple_loop p \<Longrightarrow> z \<notin> path_image p \<Longrightarrow> winding_number p z = -1 \<Longrightarrow> simple_loop_cw p"
  unfolding simple_loop_cw_def by auto

lemma simple_path_not_cw_and_ccw: "\<not>simple_loop_cw p \<or> \<not>simple_loop_ccw p"
  unfolding simple_loop_cw_def simple_loop_ccw_def simple_loop_def
  by (metis ComplI UnE inside_Un_outside one_neq_neg_one simple_closed_path_winding_number_inside
            simple_path_def winding_number_zero_in_outside zero_neq_neg_one zero_neq_one)

lemma simple_loop_cw_or_ccw:
  assumes "simple_loop p"
  shows   "simple_loop_cw p \<or> simple_loop_ccw p"
  using assms unfolding simple_loop_cw_def simple_loop_ccw_def simple_loop_def
  by (metis Compl_iff UnCI inside_Un_outside simple_closed_path_winding_number_inside
        simple_closed_path_wn3)

lemma simple_loop_ccw_conv_cw:
  assumes "simple_loop p"
  shows   "simple_loop_ccw p \<longleftrightarrow> \<not>simple_loop_cw p"
  using assms simple_path_not_cw_and_ccw simple_loop_cw_or_ccw by blast

lemma simple_loop_orientation_eqI:
  assumes "simple_loop p" "z \<notin> path_image p"
  assumes "winding_number p z \<in> {-1, 1}"
  shows   "simple_loop_orientation p = winding_number p z"
  unfolding simple_loop_orientation_def
  using assms simple_loop_ccwI simple_loop_ccw_conv_cw simple_loop_cwI by force

lemma simple_loop_winding_number_cases:
  assumes "simple_loop p" "z \<notin> path_image p"
  shows   "winding_number p z = (if z \<in> inside (path_image p) then simple_loop_orientation p else 0)"
proof (cases "z \<in> inside (path_image p)")
  case True
  hence "winding_number p z \<in> {-1, 1}"
    using simple_closed_path_winding_number_inside[of p] assms
    unfolding simple_loop_def by fast
  hence "simple_loop_orientation p = winding_number p z"
    by (intro simple_loop_orientation_eqI) (use assms in auto)
  thus ?thesis
    using True by simp
next
  case False
  hence "winding_number p z = 0"
    using assms unfolding simple_loop_def
    by (simp add: inside_outside simple_path_imp_path winding_number_zero_in_outside)
  thus ?thesis
    using False by auto
qed

lemma simple_loop_orientation_eq_0_iff [simp]:
  "simple_loop_orientation p = 0 \<longleftrightarrow> \<not>simple_loop p"
  using simple_loop_cw_or_ccw[of p]
  by (auto simp: simple_loop_orientation_def simple_loop_cw_def simple_loop_ccw_def)

lemma simple_loop_ccw_reversepath_aux:
  assumes "simple_loop_ccw p"
  shows   "simple_loop_cw (reversepath p)"
proof -
  from assms obtain z where *: "simple_loop p" "z \<notin> path_image p" "winding_number p z = 1"
    by (auto simp: simple_loop_ccw_def)
  moreover from * have "winding_number (reversepath p) z = -winding_number p z"
    by (subst winding_number_reversepath) (auto simp: simple_path_imp_path simple_loop_def)
  ultimately show ?thesis using *
    by (auto simp: simple_loop_cw_def simple_loop_def simple_path_reversepath)
qed

lemma simple_loop_cw_reversepath_aux:
  assumes "simple_loop_cw p"
  shows   "simple_loop_ccw (reversepath p)"
proof -
  from assms obtain z where *: "simple_loop p" "z \<notin> path_image p" "winding_number p z = -1"
    by (auto simp: simple_loop_cw_def)
  moreover from * have "winding_number (reversepath p) z = -winding_number p z"
    by (subst winding_number_reversepath) (auto simp: simple_path_imp_path simple_loop_def)
  ultimately show ?thesis using *
    by (auto simp: simple_loop_ccw_def simple_loop_def simple_path_reversepath)
qed

lemma simple_loop_cases: "simple_loop_ccw p \<or> simple_loop_cw p \<or> \<not>simple_loop p"
  using simple_loop_cw_or_ccw[of p] by blast

lemma simple_loop_cw_reversepath [simp]: "simple_loop_cw (reversepath p) \<longleftrightarrow> simple_loop_ccw p"
  using simple_loop_ccw_reversepath_aux reversepath_reversepath simple_loop_cw_reversepath_aux
  by metis

lemma simple_loop_ccw_reversepath [simp]: "simple_loop_ccw (reversepath p) \<longleftrightarrow> simple_loop_cw p"
  using simple_loop_ccw_reversepath_aux reversepath_reversepath simple_loop_cw_reversepath_aux
  by metis
  
lemma simple_loop_orientation_reversepath [simp]:
  "simple_loop_orientation (reversepath p) = -simple_loop_orientation p"
  using simple_path_not_cw_and_ccw[of p] by (auto simp: simple_loop_orientation_def)

lemma simple_loop_orientation_cases:
  assumes "simple_loop p"
  shows   "simple_loop_orientation p \<in> {-1, 1}"
  using simple_loop_cases[of p] assms by (auto simp: simple_loop_orientation_def)

lemma inside_simple_loop_iff:
  assumes "simple_loop p"
  shows   "z \<in> inside (path_image p) \<longleftrightarrow> z \<notin> path_image p \<and> winding_number p z \<noteq> 0"
  using assms
  by (smt (verit, best) disjoint_iff_not_equal inside_no_overlap norm_zero of_int_0
     simple_closed_path_norm_winding_number_inside simple_loop_def simple_loop_winding_number_cases)

lemma outside_simple_loop_iff:
  assumes "simple_loop p"
  shows   "z \<in> outside (path_image p) \<longleftrightarrow> z \<notin> path_image p \<and> winding_number p z = 0"
  using assms by (metis Compl_iff Un_iff inside_Un_outside inside_outside inside_simple_loop_iff)



subsection \<open>More about circular arcs\<close>

(*
  TODO: Move some or all of this. Probably belongs to HOL-Complex_Analysis.Contour_Integration.
*)

lemma part_circlepath_altdef:
  "part_circlepath z r a b = (\<lambda>t. z + rcis r (linepath a b t))"
  unfolding part_circlepath_def rcis_def cis_conv_exp ..

lemma part_circlepath_cong:
  assumes "x = x'" "r = r'" "cis a' = cis a" "b' = a' + b - a"
  shows   "part_circlepath x r a b = part_circlepath x' r' a' b'"
  by (simp add: part_circlepath_altdef rcis_def linepath_def algebra_simps assms
           flip: cis_mult cis_divide)

lemma part_circlepath_empty: "part_circlepath x r a a = linepath (x + rcis r a) (x + rcis r a)"
  by (auto simp: part_circlepath_altdef linepath_def algebra_simps fun_eq_iff)

lemma part_circlepath_radius_0 [simp]: "part_circlepath x 0 a b = linepath x x"
  by (simp add: part_circlepath_altdef linepath_def)

lemma part_circlepath_scaleR:
  "(*\<^sub>R) c \<circ> part_circlepath x r a b = part_circlepath (c *\<^sub>R x) (c * r) a b"
proof (cases "c = 0")
  assume "c \<noteq> 0"
  thus ?thesis
    by (simp add: part_circlepath_altdef fun_eq_iff algebra_simps linepath_def rcis_def cis_Arg 
                  complex_sgn_def scaleR_conv_of_real flip: cis_divide cis_mult)
qed (auto simp: fun_eq_iff part_circlepath_altdef)

lemma part_circlepath_mult_complex:
  "(*) c \<circ> part_circlepath x r a b = part_circlepath (c * x :: complex) (norm c * r) (a + Arg c) (b + Arg c)"
proof (cases "c = 0")
  assume "c \<noteq> 0"
  thus ?thesis
    by (simp add: part_circlepath_altdef fun_eq_iff algebra_simps linepath_def rcis_def cis_Arg 
                  complex_sgn_def scaleR_conv_of_real flip: cis_divide cis_mult)
qed (auto simp: fun_eq_iff part_circlepath_altdef)  

lemma part_circlepath_mult_complex':
  assumes "cis a' = cis (a + Arg c)" "b' = a' + b - a"
  shows   "(*) c \<circ> part_circlepath x r a b = part_circlepath (c * x :: complex) (norm c * r) a' b'"
  unfolding part_circlepath_mult_complex by (rule part_circlepath_cong) (use assms in auto)

lemma circlepath_altdef: "circlepath x r t = x + rcis r (2 * pi * t)"
  by (simp add: circlepath_def part_circlepath_altdef mult_ac)  

lemma reversepath_circlepath: "reversepath (circlepath x r) = part_circlepath x r (2 * pi) 0"
  by (simp add: circlepath_def)

lemma pathstart_part_circlepath': "pathstart (part_circlepath z r a b) = z + rcis r a"
  and pathfinish_part_circlepath': "pathfinish (part_circlepath z r a b) = z + rcis r b"
  unfolding part_circlepath_altdef by (simp_all add: pathstart_def pathfinish_def linepath_def)



subsection \<open>Reparametrisation of loops by shifting\<close>

(* TODO: Move to HOL-Analysis.Path_Connected *)
lemma shiftpath_loop_altdef:
  assumes "pathstart p = pathfinish p" "x \<in> {0..1}" "a \<in> {0..1}"
  shows   "shiftpath a p x = p (frac (x + a))"
proof -
  consider "x + a < 1" | "x + a = 1" | "x + a > 1" "x + a < 2" | "x + a = 2"
    using assms(2,3) by fastforce
  thus ?thesis
  proof cases
    case 3
    hence [simp]: "frac (a + x) = x + a - 1"
      using assms unfolding atLeastAtMost_iff by (subst frac_unique_iff) auto
    show ?thesis using assms 3
      by (auto simp: shiftpath_def pathstart_def pathfinish_def algebra_simps)
  qed (use assms frac_eq[of "a + x"]
       in  \<open>auto simp: shiftpath_def algebra_simps pathstart_def pathfinish_def\<close>)
qed

lemma homotopic_loops_shiftpath_left:
  assumes "path p" "path_image p \<subseteq> A" "pathstart p = pathfinish p" "x \<in> {0..1}"
  shows   "homotopic_loops A (shiftpath x p) p"
proof (rule homotopic_loops_sym, rule homotopic_loops_reparametrize)
  show "continuous_on {0..1} ((+) x)"
    by (intro continuous_intros)
  show "shiftpath x p t = p (frac (x + t))" if "t \<in> {0..1}" for t
    using that assms by (simp add: shiftpath_loop_altdef add_ac)
qed (use assms in auto)

lemma homotopic_loops_shiftpath_right:
  assumes "path p" "path_image p \<subseteq> A" "pathstart p = pathfinish p" "x \<in> {0..1}"
  shows   "homotopic_loops A p (shiftpath x p)"
  using homotopic_loops_shiftpath_left[OF assms] by (simp add: homotopic_loops_sym)

lemma shiftpath_full_part_circlepath:
  "shiftpath c (part_circlepath x r a (a + 2 * of_int n * pi)) =
   part_circlepath x r (a + 2 * n * pi * c) (a + 2 * n * pi * (c + 1))"
  unfolding shiftpath_def
  by (simp add: shiftpath_def part_circlepath_altdef fun_eq_iff rcis_def linepath_def
                field_simps cis_multiple_2pi' flip: cis_mult cis_divide)

lemma shiftpath_circlepath:
  "shiftpath c (circlepath x r) = part_circlepath x r (c * 2 * pi) ((c + 1) * 2 * pi)"
  unfolding circlepath_def using shiftpath_full_part_circlepath[of c x r 0 1]
  by (simp add: algebra_simps)


text \<open>
  The following variant of \<^const>\<open>shiftpath\<close> is more convenient for loops.
\<close>
definition shiftpath' :: "real \<Rightarrow> (real \<Rightarrow> 'a) \<Rightarrow> (real \<Rightarrow> 'a)"
  where "shiftpath' a p = (\<lambda>x. p (frac (x + a)))"

lemma shiftpath'_0 [simp]: "pathfinish p = pathstart p \<Longrightarrow> t \<in> {0..1} \<Longrightarrow> shiftpath' 0 p t = p t"
  using frac_eq[of t] by (cases "t = 1") (auto simp: pathfinish_def pathstart_def shiftpath'_def)

lemma path_image_shiftpath':
  assumes "path p" "pathstart p = pathfinish p"
  shows   "path_image (shiftpath' c p) = path_image p"
proof -
  have "path_image (shiftpath' c p) = (\<lambda>x. p (frac (x + c))) ` {0..1}"
    unfolding path_image_def shiftpath'_def ..
  also have "{0..1} = {0..<1 - frac c} \<union> {1 - frac c..1}"
    using frac_lt_1[of c] frac_ge_0[of c] by (auto simp del: frac_ge_0)
  also have "(\<lambda>x. p (frac (x + c))) ` \<dots> = 
             (\<lambda>x. p (frac (x + c))) ` {0..<1 - frac c} \<union> (\<lambda>x. p (frac (x + c))) ` {1 - frac c..1}"
    by (rule image_Un)

  also have "(\<lambda>x. p (frac (x + c))) ` {0..<1 - frac c} = (\<lambda>x. p (x + frac c)) ` {0..<1 - frac c}"
  proof (intro image_cong refl)
    show "p (frac (x + c)) = p (x + frac c)" if "x \<in> {0..<1-frac c}" for x
    proof -
      have "frac x = x"
        using frac_eq[of x] that frac_ge_0[of c] by (auto simp del: frac_ge_0)
      thus ?thesis
        using frac_lt_1[of c] frac_ge_0[of c] that
        by (auto simp: frac_add field_simps simp del: frac_ge_0)
    qed
  qed
  also have "{0..<1 - frac c} = (+) (-frac c) ` {frac c..<1}"
    by (subst image_add_atLeastLessThan) simp_all
  also have "(\<lambda>x. p (x + frac c)) ` \<dots> = p ` {frac c..<1}"
    by (subst image_image) simp

  also have "(\<lambda>x. p (frac (x + c))) ` {1 - frac c..1} = (\<lambda>x. p (x + frac c - 1)) ` {1 - frac c..1}"
  proof (intro image_cong refl)
    fix x assume x: "x \<in> {1 - frac c..1}"
    have "frac (x + c) = x + frac c - 1"
    proof (cases "x = 1")
      case False
      with x have "x \<in> {0..<1}"
        using frac_lt_1[of c] by auto
      hence "frac x = x"
        by (subst frac_eq) auto
      thus ?thesis using x by (auto simp: algebra_simps frac_add)
    qed (auto simp: frac_def)
    thus "p (frac (x + c)) = p (x + frac c - 1)"
      by simp
  qed
  also have "{1 - frac c..1} = (+) (1 - frac c) ` {0..frac c}"
    by (subst image_add_atLeastAtMost) simp_all
  also have "(\<lambda>x. p (x + frac c - 1)) ` \<dots> = p ` {0..frac c}"
    by (subst image_image) simp

  also have "p ` {frac c..<1} \<union> p ` {0..frac c} = p ` ({frac c..<1} \<union> {0..frac c})"
    by (rule image_Un [symmetric])
  also have "{frac c..<1} \<union> {0..frac c} = {0..<1}"
    using frac_lt_1[of c] frac_ge_0[of c] by (auto simp del: frac_ge_0)
  also have "p ` {0..<1} = path_image p"
    by (rule path_image_loop [symmetric]) fact+
  finally show ?thesis .
qed

lemma path_shiftpath_0_iff [simp]: "path (shiftpath 0 p) \<longleftrightarrow> path p"
  unfolding path_def by (intro continuous_on_cong) (auto simp: shiftpath_def)

lemma path_shiftpath'_int_iff [simp]:
  assumes "pathstart p = pathfinish p" "c \<in> \<int>"
  shows   "path (shiftpath' c p) \<longleftrightarrow> path p"
  unfolding path_def 
proof (intro continuous_on_cong)
  show "shiftpath' c p x = p x" if "x \<in> {0..1}" for x
  proof (cases "x = 1")
    case False
    hence "x \<in> {0..<1}"
      using that by auto
    moreover from this have "frac x = x"
      by (subst frac_eq) auto
    moreover have "frac (x + c) = frac x"
      using assms by (auto elim!: Ints_cases simp: frac_def)
    ultimately show ?thesis
      using assms that
      by (auto simp: shiftpath'_def pathstart_def pathfinish_def)
  qed (use assms in \<open>auto simp: shiftpath'_def frac_def pathfinish_def pathstart_def\<close>)
qed auto

lemma shiftpath'_eq_shiftpath:
  assumes "pathstart p = pathfinish p" "c \<in> {0..1}" "t \<in> {0..1}"
  shows   "shiftpath' c p t = shiftpath c p t"
proof -
  consider "t + c < 1" | "t + c = 1" | "t + c > 1" "t + c < 2" | "t + c \<ge> 2"
    by linarith
  thus ?thesis
  proof cases
    case 1
    hence "frac (t + c) = t + c"
      using assms by (subst frac_unique_iff) auto
    thus ?thesis
      using assms 1 by (simp add: shiftpath'_def shiftpath_def add_ac)
  next
    case 3
    hence "frac (t + c) = t + c - 1"
      using assms by (subst frac_unique_iff) (auto simp: algebra_simps)
    thus ?thesis
      using assms 3 by (simp add: shiftpath'_def shiftpath_def add_ac)
  next
    case 4
    with assms have "t + c = 2"
      by auto
    thus ?thesis using assms
      by (simp add: shiftpath'_def shiftpath_def pathstart_def pathfinish_def add_ac)
  qed (use assms in \<open>auto simp: shiftpath'_def shiftpath_def add_ac pathstart_def pathfinish_def\<close>)
qed

lemma shiftpath'_frac: "shiftpath' (frac c) p = shiftpath' c p"
  unfolding shiftpath'_def by (simp add: frac_def algebra_simps)

lemma path_shiftpath' [intro]:
  "pathstart p = pathfinish p \<Longrightarrow> path p \<Longrightarrow> path (shiftpath' c p)"
  unfolding shiftpath'_def path_def
  by (rule continuous_on_frac_real')
     (auto intro!: continuous_intros simp: pathfinish_def pathstart_def)

lemma pathfinish_shiftpath':
  "pathfinish (shiftpath' c p) = pathstart (shiftpath' c p)"
  by (simp add: pathstart_def pathfinish_def shiftpath'_def frac_def)

lemma shiftpath'_shiftpath': "shiftpath' c (shiftpath' d p) = shiftpath' (c + d) p"
proof
  fix x :: real
  have "shiftpath' c (shiftpath' d p) x = p (frac (frac (x + c) + d))"
    by (simp_all add: shiftpath'_def)
  also have "frac (frac (x + c) + d) =
               x + c - real_of_int \<lfloor>x + c\<rfloor> + d - real_of_int \<lfloor>x + c - real_of_int \<lfloor>x + c\<rfloor> + d\<rfloor>"
    by (simp add: frac_def)
  also have "x + c - real_of_int \<lfloor>x + c\<rfloor> + d = x + c + d - real_of_int \<lfloor>x + c\<rfloor>"
    by Groebner_Basis.algebra
  also have "floor \<dots> = \<lfloor>x + c + d\<rfloor> - \<lfloor>x + c\<rfloor>"
    by (subst floor_diff_of_int) auto
  also have "x + c + d - real_of_int \<lfloor>x + c\<rfloor> - real_of_int (\<lfloor>x + c + d\<rfloor> - \<lfloor>x + c\<rfloor>) =
               frac (x + c + d)"
    by (simp add: frac_def)
  also have "p \<dots> = shiftpath' (c + d) p x"
    by (simp add: shiftpath'_def add_ac)
  finally show "shiftpath' c (shiftpath' d p) x = shiftpath' (c + d) p x" .
qed

lemma simple_path_shiftpath':
  assumes "simple_path p" "pathfinish p = pathstart p"
  shows   "simple_path (shiftpath' c p)"
proof -
  have "simple_path (shiftpath (frac c) p)"
    by (intro simple_path_shiftpath frac_ge_0 less_imp_le[OF frac_lt_1] assms)
  also have "?this \<longleftrightarrow> simple_path (shiftpath' (frac c) p)"
    by (intro simple_path_cong) (auto simp: assms shiftpath'_eq_shiftpath less_imp_le[OF frac_lt_1])
  also have "shiftpath' (frac c) p = shiftpath' c p"
    by (simp only: shiftpath'_frac)
  finally show ?thesis .
qed

lemma simple_path_shiftpath'_iff [simp]:
  assumes "pathfinish p = pathstart p"
  shows   "simple_path (shiftpath' c p) \<longleftrightarrow> simple_path p"
proof
  assume "simple_path (shiftpath' c p)"
  hence "simple_path (shiftpath' (-c) (shiftpath' c p))"
    by (rule simple_path_shiftpath') (use assms in \<open>auto simp: pathfinish_shiftpath'\<close>)
  also have "shiftpath' (-c) (shiftpath' c p) = shiftpath' 0 p"
    by (simp add: shiftpath'_shiftpath')
  also have "simple_path \<dots> \<longleftrightarrow> simple_path p"
    by (intro simple_path_cong) (use assms in auto)
  finally show "simple_path p" .
qed (use assms in \<open>auto intro!: simple_path_shiftpath'\<close>)

lemma homotopic_loops_shiftpath'_left:
  assumes "path p" "path_image p \<subseteq> A" "pathstart p = pathfinish p"
  shows   "homotopic_loops A (shiftpath' x p) p"
proof (rule homotopic_loops_sym, rule homotopic_loops_reparametrize)
  show "continuous_on {0..1} ((+) x)"
    by (intro continuous_intros)
  show "shiftpath' x p t = p (frac (x + t))" if "t \<in> {0..1}" for t
    using that assms by (simp add: shiftpath'_def add_ac)
qed (use assms in auto)

lemma homotopic_loops_shiftpath'_right:
  assumes "path p" "path_image p \<subseteq> A" "pathstart p = pathfinish p"
  shows   "homotopic_loops A p (shiftpath' x p)"
  using homotopic_loops_shiftpath'_left[OF assms] by (simp add: homotopic_loops_sym)


lemma shiftpath'_full_part_circlepath:
  "shiftpath' c (part_circlepath x r a (a + 2 * of_int n * pi)) =
   part_circlepath x r (a + 2 * n * pi * c) (a + 2 * n * pi * (c + 1))" (is "?lhs = ?rhs")
proof
  fix t
  have "shiftpath' c (part_circlepath x r a (a + 2 * of_int n * pi)) t = 
           x + rcis r a * cis (2 * pi * (c + t) * of_int n) * 
           cis ((2 * pi) * (-of_int (n * \<lfloor>c + t\<rfloor>)))"
    by (simp add: shiftpath'_def fun_eq_iff part_circlepath_altdef rcis_def
             linepath_def algebra_simps frac_def divide_conv_cnj cis_cnj 
             del: cis_multiple_2pi flip: cis_mult cis_divide)
  also have "cis ((2 * pi) * (-of_int (n * \<lfloor>c + t\<rfloor>))) = 1"
    by (rule cis_multiple_2pi) auto
  also have "x + rcis r a * cis (2 * pi * (c + t) * of_int n) * 1 = 
               part_circlepath x r (a + 2 * n * pi * c) (a + 2 * n * pi * (c + 1)) t"
    by (simp add: part_circlepath_def algebra_simps cis_conv_exp exp_add linepath_def rcis_def)
  finally show "?lhs t = ?rhs t"
    by simp
qed  

lemma shiftpath'_circlepath:
  "shiftpath' c (circlepath x r) = part_circlepath x r (c * 2 * pi) ((c + 1) * 2 * pi)"
  unfolding circlepath_def using shiftpath'_full_part_circlepath[of c x r 0 1]
  by (simp add: algebra_simps)

end