(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)

section \<open>Additions to the library\<close>

theory Library_Complements
  imports "HOL-Analysis.Analysis" "HOL-Cardinals.Cardinal_Order_Relation"
begin

subsection \<open>Mono intros\<close>

text \<open>We have a lot of (large) inequalities to prove. It is very convenient to have a set of
introduction rules for this purpose (a lot should be added to it, I have put here all the ones
I needed).

The typical use case is when one wants to prove some inequality, say
$ \exp (x*x) \leq y + \exp(1 + z * z + y)$, assuming $y \geq 0$ and $0 \leq x \leq z$.
One would write it has
\begin{verbatim}
have "0 + \exp(0 + x * x + 0) < = y + \exp(1 + z * z + y)"
using `y > = 0` `x < = z` by (intro mono_intros)
\end{verbatim}
When the left and right hand terms are written in completely analogous ways as above, then the
introduction rules (that contain monotonicity of addition, of the exponential, and so on) reduce
this to comparison of elementary terms in the formula. This is a very naive strategy, that fails
in many situations, but that is very efficient when used correctly.
\<close>

named_theorems mono_intros "structural introduction rules to prove inequalities"
declare le_imp_neg_le [mono_intros]
declare add_left_mono [mono_intros]
declare add_right_mono [mono_intros]
declare add_strict_left_mono [mono_intros]
declare add_strict_right_mono [mono_intros]
declare add_mono [mono_intros]
declare add_strict_mono [mono_intros]
declare diff_mono [mono_intros]
declare mult_left_mono [mono_intros]
declare mult_right_mono [mono_intros]
declare mult_mono [mono_intros]
declare max.mono [mono_intros]
declare min.mono [mono_intros]
declare power_mono [mono_intros]
declare ln_ge_zero [mono_intros]
declare ln_le_minus_one [mono_intros]
declare ennreal_minus_mono [mono_intros]
declare ennreal_leI [mono_intros]
declare e2ennreal_mono [mono_intros]
declare enn2ereal_nonneg [mono_intros]
declare zero_le [mono_intros]
declare top_greatest [mono_intros]
declare bot_least [mono_intros]
declare dist_triangle [mono_intros]
declare dist_triangle2 [mono_intros]
declare dist_triangle3 [mono_intros]
declare exp_ge_add_one_self_aux [mono_intros]
declare exp_gt_one [mono_intros]
declare exp_less_mono [mono_intros]
declare dist_triangle [mono_intros]

lemma ln_le_cancelI [mono_intros]:
  assumes "(0::real) < x" "x \<le> y"
  shows "ln x \<le> ln y"
using assms by auto

lemma exp_le_cancelI [mono_intros]:
  assumes "x \<le> (y::real)"
  shows "exp x \<le> exp y"
using assms by simp

lemma mult_ge1_mono [mono_intros]:
  assumes "a \<ge> (0::'a::linordered_idom)" "b \<ge> 1"
  shows "a \<le> a * b" "a \<le> b * a"
using assms mult_le_cancel_left1 mult_le_cancel_right1 by force+

text \<open>A few convexity inequalities we will need later on.\<close>

lemma xy_le_uxx_vyy [mono_intros]:
  assumes "u > 0" "u * v = (1::real)"
  shows "x * y \<le> u * x^2/2 + v * y^2/2"
proof -
  have "v > 0" using assms
    by (metis (full_types) dual_order.strict_implies_order le_less_linear mult_nonneg_nonpos not_one_le_zero)
  then have *: "sqrt u * sqrt v = 1"
    using assms by (metis real_sqrt_mult_distrib2 real_sqrt_one)
  have "(sqrt u * x - sqrt v * y)^2 \<ge> 0" by auto
  then have "u * x^2 + v * y^2 - 2 * 1 * x * y \<ge> 0"
    unfolding power2_eq_square *[symmetric] using \<open>u>0\<close> \<open>v > 0\<close> by (auto simp add: algebra_simps)
  then show ?thesis by (auto simp add: algebra_simps divide_simps)
qed

lemma xy_le_xx_yy [mono_intros]:
  "x * y \<le> x^2/2 + y^2/2" for x y::real
using xy_le_uxx_vyy[of 1 1] by auto

lemma ln_squared_bound [mono_intros]:
  "(ln x)^2 \<le> 2 * x - 2" if "x \<ge> 1" for x::real
proof -
  define f where "f = (\<lambda>x::real. 2 * x - 2 - ln x * ln x)"
  have *: "DERIV f x :> 2 - 2 * ln x / x" if "x > 0" for x::real
    unfolding f_def using that by (auto intro!: derivative_eq_intros)
  have "f 1 \<le> f x" if "x \<ge> 1" for x
  proof (rule DERIV_nonneg_imp_nondecreasing[OF that], safe)
    fix t::real assume "t \<ge> 1"
    show "\<exists>y. (f has_real_derivative y) (at t) \<and> 0 \<le> y"
      apply (rule exI[of _ "2 - 2 * ln t / t"])
      using *[of t] \<open>t \<ge> 1\<close> by (auto simp add: divide_simps ln_bound)
  qed
  then show ?thesis unfolding f_def power2_eq_square using that by auto
qed

text \<open>In the next lemma, the assumptions are too strong (negative numbers
less than $-1$ also work well to have a square larger than $1$), but in practice one proves
inequalities with nonnegative numbers, so this version is really the useful one for
\verb+mono_intros+.\<close>

lemma mult_ge1_powers [mono_intros]:
  assumes "a \<ge> (1::'a::linordered_idom)"
  shows "1 \<le> a * a" "1 \<le> a * a * a" "1 \<le> a * a * a * a"
using assms by (meson assms dual_order.trans mult_ge1_mono(1) zero_le_one)+

lemmas [mono_intros] = ln_bound

lemma mono_cSup:
  fixes f :: "'a::conditionally_complete_lattice \<Rightarrow> 'b::conditionally_complete_lattice"
  assumes "bdd_above A" "A \<noteq> {}" "mono f"
  shows "Sup (f`A) \<le> f (Sup A)"
by (metis assms(1) assms(2) assms(3) cSUP_least cSup_upper mono_def)

lemma mono_cSup_bij:
  fixes f :: "'a::conditionally_complete_linorder \<Rightarrow> 'b::conditionally_complete_linorder"
  assumes "bdd_above A" "A \<noteq> {}" "mono f" "bij f"
  shows "Sup (f`A) = f(Sup A)"
proof -
  have "Sup ((inv f)`(f`A)) \<le> (inv f) (Sup (f`A))"
    apply (rule mono_cSup)
    using mono_inv[OF assms(3) assms(4)] assms(2) bdd_above_image_mono[OF assms(3) assms(1)] by auto
  then have "f (Sup ((inv f)`(f`A))) \<le> Sup (f`A)"
    using assms mono_def by (metis (no_types, hide_lams) bij_betw_imp_surj_on surj_f_inv_f)
  moreover have "f (Sup ((inv f)`(f`A))) = f(Sup A)"
    using assms by (simp add: bij_is_inj)
  ultimately show ?thesis using mono_cSup[OF assms(1) assms(2) assms(3)] by auto
qed

subsection \<open>More topology\<close>

text \<open>In situations of interest to us later on, convergence is well controlled only for sequences
living in some dense subset of the space (but the limit can be anywhere). This is enough to
establish continuity of the function, if the target space is well enough separated.

The statement we give below is very general,
as we do not assume that the function is continuous inside the original set $S$, it will typically
only be continuous at a set $T$ contained in the closure of $S$. In many applications, $T$ will
be the closure of $S$, but we are also thinking of the case where one constructs an extension
of a function inside a space, to its boundary, and the behaviour at the boundary is better than
inside the space. The example we have in mind is the extension of a quasi-isometry to the boundary
of a Gromov hyperbolic space.

In the following criterion, we assume that if $u_n$ inside $S$ converges to a point at the boundary
$T$, then $f(u_n)$ converges (where $f$ is some function inside). Then, we can extend the function $f$ at
the boundary, by picking the limit value of $f(u_n)$ for some sequence converging to $u_n$. Then
the lemma asserts that $f$ is continuous at every point $b$ on the boundary.

The proof is done in two steps:
\begin{enumerate}
\item First, if $v_n$ is another inside sequence tending to
the same point $b$ on the boundary, then $f(v_n)$ converges to the same value as $f(u_n)$: this is
proved by considering the sequence $w$ equal to $u$ at even times and to $v$ at odd times, and
saying that $f(w_n)$ converges. Its limit is equal to the limit of $f(u_n)$ and of $f(v_n)$, so they
have to coincide.
\item Now, consider a general sequence $v$ (in the space or the boundary) converging to $b$. We want
to show that $f(v_n)$ tends to $f(b)$. If $v_n$ is inside $S$, we have already done it in the first
step. If it is on the boundary, on the other hand, we can approximate it by an inside point $w_n$
for which $f(w_n)$ is very close to $f(v_n)$. Then $w_n$ is an inside sequence converging to $b$,
hence $f(w_n)$ converges to $f(b)$ by the first step, and then $f(v_n)$ also converges to $f(b)$.
The precise argument is more conveniently written by contradiction. It requires good separation
properties of the target space.
\end{enumerate}\<close>

text \<open>First, we introduce the material to interpolate between two sequences, one at even times
and the other one at odd times.\<close>

definition even_odd_interpolate::"(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)"
  where "even_odd_interpolate u v n = (if even n then u (n div 2) else v (n div 2))"

lemma even_odd_interpolate_compose:
  "even_odd_interpolate (f o u) (f o v) = f o (even_odd_interpolate u v)"
  unfolding even_odd_interpolate_def comp_def by auto

lemma even_odd_interpolate_filterlim:
  "filterlim u F sequentially \<and> filterlim v F sequentially \<longleftrightarrow> filterlim (even_odd_interpolate u v) F sequentially"
proof (auto)
  assume H: "filterlim (even_odd_interpolate u v) F sequentially"
  define r::"nat \<Rightarrow> nat" where "r = (\<lambda>n. 2 * n)"
  have "strict_mono r" unfolding r_def strict_mono_def by auto
  then have "filterlim r sequentially sequentially"
    by (simp add: filterlim_subseq)
  have "filterlim (\<lambda>n. (even_odd_interpolate u v) (r n)) F sequentially"
    by (rule filterlim_compose[OF H filterlim_subseq[OF \<open>strict_mono r\<close>]])
  moreover have "even_odd_interpolate u v (r n) = u n" for n
    unfolding r_def even_odd_interpolate_def by auto
  ultimately show "filterlim u F sequentially" by auto
  define r::"nat \<Rightarrow> nat" where "r = (\<lambda>n. 2 * n + 1)"
  have "strict_mono r" unfolding r_def strict_mono_def by auto
  then have "filterlim r sequentially sequentially"
    by (simp add: filterlim_subseq)
  have "filterlim (\<lambda>n. (even_odd_interpolate u v) (r n)) F sequentially"
    by (rule filterlim_compose[OF H filterlim_subseq[OF \<open>strict_mono r\<close>]])
  moreover have "even_odd_interpolate u v (r n) = v n" for n
    unfolding r_def even_odd_interpolate_def by auto
  ultimately show "filterlim v F sequentially" by auto
next
  assume H: "filterlim u F sequentially" "filterlim v F sequentially"
  show "filterlim (even_odd_interpolate u v) F sequentially"
  unfolding filterlim_iff eventually_sequentially proof (auto)
    fix P assume *: "eventually P F"
    obtain N1 where N1: "\<And>n. n \<ge> N1 \<Longrightarrow> P (u n)"
      using H(1) unfolding filterlim_iff eventually_sequentially using * by auto
    obtain N2 where N2: "\<And>n. n \<ge> N2 \<Longrightarrow> P (v n)"
      using H(2) unfolding filterlim_iff eventually_sequentially using * by auto
    have "P (even_odd_interpolate u v n)" if "n \<ge> 2 * N1 + 2 * N2" for n
    proof (cases "even n")
      case True
      have "n div 2 \<ge> N1" using that by auto
      then show ?thesis unfolding even_odd_interpolate_def using True N1 by auto
    next
      case False
      have "n div 2 \<ge> N2" using that by auto
      then show ?thesis unfolding even_odd_interpolate_def using False N2 by auto
    qed
    then show "\<exists>N. \<forall>n\<ge>N. P (even_odd_interpolate u v n)" by auto
  qed
qed

text \<open>Then, we prove the continuity criterion for extensions of functions to the boundary $T$ of a set
$S$. The first assumption is that $f(u_n)$ converges when $f$ converges to the boundary, and the
second one that the extension of $f$ to the boundary has been defined using the limit along some
sequence tending to the point under consideration. The following criterion is the most general one,
but this is not the version that is most commonly applied so we use a prime in its name.\<close>

lemma continuous_at_extension_sequentially':
  fixes f :: "'a::{first_countable_topology, t2_space} \<Rightarrow> 'b::t3_space"
  assumes "b \<in> T"
          "\<And>u b. (\<forall>n. u n \<in> S) \<Longrightarrow> b \<in> T \<Longrightarrow> u \<longlonglongrightarrow> b \<Longrightarrow> convergent (\<lambda>n. f (u n))"
          "\<And>b. b \<in> T \<Longrightarrow> \<exists>u. (\<forall>n. u n \<in> S) \<and> u \<longlonglongrightarrow> b \<and> ((\<lambda>n. f (u n)) \<longlonglongrightarrow> f b)"
  shows "continuous (at b within (S \<union> T)) f"
proof -
  have first_step: "(\<lambda>n. f (u n)) \<longlonglongrightarrow> f c" if "\<And>n. u n \<in> S" "u \<longlonglongrightarrow> c" "c \<in> T" for u c
  proof -
    obtain v where v: "\<And>n. v n \<in> S" "v \<longlonglongrightarrow> c" "(\<lambda>n. f (v n)) \<longlonglongrightarrow> f c"
      using assms(3)[OF \<open>c \<in> T\<close>] by blast
    then have A: "even_odd_interpolate u v \<longlonglongrightarrow> c"
      unfolding even_odd_interpolate_filterlim[symmetric] using \<open>u \<longlonglongrightarrow> c\<close> by auto
    moreover have B: "\<forall>n. even_odd_interpolate u v n \<in> S"
      using \<open>\<And>n. u n \<in> S\<close> \<open>\<And>n. v n \<in> S\<close> unfolding even_odd_interpolate_def by auto
    have "convergent (\<lambda>n. f (even_odd_interpolate u v n))"
      by (rule assms(2)[OF B \<open>c \<in> T\<close> A])
    then obtain m where "(\<lambda>n. f (even_odd_interpolate u v n)) \<longlonglongrightarrow> m"
      unfolding convergent_def by auto
    then have "even_odd_interpolate (f o u) (f o v) \<longlonglongrightarrow> m"
      unfolding even_odd_interpolate_compose unfolding comp_def by auto
    then have "(f o u) \<longlonglongrightarrow> m" "(f o v) \<longlonglongrightarrow> m"
      unfolding even_odd_interpolate_filterlim[symmetric] by auto
    then have "m = f c" using v(3) unfolding comp_def using LIMSEQ_unique by auto
    then show ?thesis using \<open>(f o u) \<longlonglongrightarrow> m\<close> unfolding comp_def by auto
  qed
  show "continuous (at b within (S \<union> T)) f"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain U where U: "open U" "f b \<in> U" "\<not>(\<forall>\<^sub>F x in at b within S \<union> T. f x \<in> U)"
      unfolding continuous_within tendsto_def[where l = "f b"] using sequentially_imp_eventually_nhds_within by auto
    have "\<exists>V W. open V \<and> open W \<and> f b \<in> V \<and> (UNIV - U) \<subseteq> W \<and> V \<inter> W = {}"
      apply (rule t3_space) using U by auto
    then obtain V W where VW: "open V" "open W" "f b \<in> V" "UNIV - U \<subseteq> W" "V \<inter> W = {}"
      by auto

    obtain A :: "nat \<Rightarrow> 'a set" where *:
      "\<And>i. open (A i)"
      "\<And>i. b \<in> A i"
      "\<And>F. \<forall>n. F n \<in> A n \<Longrightarrow> F \<longlonglongrightarrow> b"
      by (rule first_countable_topology_class.countable_basis) blast
    with * U(3) have "\<exists>F. \<forall>n. F n \<in> S \<union> T \<and> F n \<in> A n \<and> \<not> (f(F n) \<in> U)"
      unfolding at_within_def eventually_inf_principal eventually_nhds
      by (intro choice) (meson DiffE)
    then obtain F where F: "\<And>n. F n \<in> S \<union> T" "\<And>n. F n \<in> A n" "\<And>n. f(F n) \<notin> U"
      by auto

    have "\<exists>y. y \<in> S \<and> y \<in> A n \<and> f y \<in> W" for n
    proof (cases "F n \<in> S")
      case True
      show ?thesis apply (rule exI[of _ "F n"]) using F VW True by auto
    next
      case False
      then have "F n \<in> T" using \<open>F n \<in> S \<union> T\<close> by auto
      obtain u where u: "\<And>p. u p \<in> S" "u \<longlonglongrightarrow> F n" "(\<lambda>p. f (u p)) \<longlonglongrightarrow> f(F n)"
        using assms(3)[OF \<open>F n \<in> T\<close>] by auto
      moreover have "f(F n) \<in> W" using F VW by auto
      ultimately have "eventually (\<lambda>p. f (u p) \<in> W) sequentially"
        using \<open>open W\<close> by (simp add: tendsto_def)
      moreover have "eventually (\<lambda>p. u p \<in> A n) sequentially"
        using \<open>F n \<in> A n\<close> u \<open>open (A n)\<close> by (simp add: tendsto_def)
      ultimately have "\<exists>p. f(u p) \<in> W \<and> u p \<in> A n"
        using eventually_False_sequentially eventually_elim2 by blast
      then show ?thesis using u(1) by auto
    qed
    then have "\<exists>u. \<forall>n. u n \<in> S \<and> u n \<in> A n \<and> f (u n) \<in> W"
      by (auto intro: choice)
    then obtain u where u: "\<And>n. u n \<in> S" "\<And>n. u n \<in> A n" "\<And>n. f (u n) \<in> W"
      by blast
    then have "u \<longlonglongrightarrow> b" using *(3) by auto
    then have "(\<lambda>n. f (u n)) \<longlonglongrightarrow> f b" using first_step assms u by auto
    then have "eventually (\<lambda>n. f (u n) \<in> V) sequentially"
      using VW by (simp add: tendsto_def)
    then have "\<exists>n. f (u n) \<in> V"
      using eventually_False_sequentially eventually_elim2 by blast
    then show False
      using u(3) \<open>V \<inter> W = {}\<close> by auto
  qed
qed

text \<open>We can specialize the previous statement to the common case where one already knows the
sequential continuity of $f$ along sequences in $S$ converging to a point in $T$. This will be the
case in most --but not all-- applications. This is a straightforward application of the above
criterion.\<close>

proposition continuous_at_extension_sequentially:
  fixes f :: "'a::{first_countable_topology, t2_space} \<Rightarrow> 'b::t3_space"
  assumes "a \<in> T"
          "T \<subseteq> closure S"
          "\<And>u b. (\<forall>n. u n \<in> S) \<Longrightarrow> b \<in> T \<Longrightarrow> u \<longlonglongrightarrow> b \<Longrightarrow> (\<lambda>n. f (u n)) \<longlonglongrightarrow> f b"
  shows "continuous (at a within (S \<union> T)) f"
apply (rule continuous_at_extension_sequentially'[OF \<open>a \<in> T\<close>])
using assms(3) convergent_def apply blast
by (metis assms(2) assms(3) closure_sequential subset_iff)

text \<open>We also give global versions. We can only express the continuity on $T$, so
this is slightly weaker than the previous statements since we are not saying anything on inside
sequences tending to $T$ -- but in cases where $T$ contains $S$ these statements contain all the
information.\<close>

lemma continuous_on_extension_sequentially':
  fixes f :: "'a::{first_countable_topology, t2_space} \<Rightarrow> 'b::t3_space"
  assumes "\<And>u b. (\<forall>n. u n \<in> S) \<Longrightarrow> b \<in> T \<Longrightarrow> u \<longlonglongrightarrow> b \<Longrightarrow> convergent (\<lambda>n. f (u n))"
          "\<And>b. b \<in> T \<Longrightarrow> \<exists>u. (\<forall>n. u n \<in> S) \<and> u \<longlonglongrightarrow> b \<and> ((\<lambda>n. f (u n)) \<longlonglongrightarrow> f b)"
  shows "continuous_on T f"
unfolding continuous_on_eq_continuous_within apply (auto intro!: continuous_within_subset[of _ "S \<union> T" f T])
by (intro continuous_at_extension_sequentially'[OF _ assms], auto)

lemma continuous_on_extension_sequentially:
  fixes f :: "'a::{first_countable_topology, t2_space} \<Rightarrow> 'b::t3_space"
  assumes "T \<subseteq> closure S"
          "\<And>u b. (\<forall>n. u n \<in> S) \<Longrightarrow> b \<in> T \<Longrightarrow> u \<longlonglongrightarrow> b \<Longrightarrow> (\<lambda>n. f (u n)) \<longlonglongrightarrow> f b"
  shows "continuous_on T f"
unfolding continuous_on_eq_continuous_within apply (auto intro!: continuous_within_subset[of _ "S \<union> T" f T])
by (intro continuous_at_extension_sequentially[OF _ assms], auto)


subsubsection \<open>Homeomorphisms\<close>

text \<open>A variant around the notion of homeomorphism, which is only expressed in terms of the
function and not of its inverse.\<close>

definition homeomorphism_on::"'a set \<Rightarrow> ('a::topological_space \<Rightarrow> 'b::topological_space) \<Rightarrow> bool"
  where "homeomorphism_on S f = (\<exists>g. homeomorphism S (f`S) f g)"

lemma homeomorphism_on_continuous:
  assumes "homeomorphism_on S f"
  shows "continuous_on S f"
using assms unfolding homeomorphism_on_def homeomorphism_def by auto

lemma homeomorphism_on_bij:
  assumes "homeomorphism_on S f"
  shows "bij_betw f S (f`S)"
using assms unfolding homeomorphism_on_def homeomorphism_def by auto (metis inj_on_def inj_on_imp_bij_betw)

lemma homeomorphism_on_homeomorphic:
  assumes "homeomorphism_on S f"
  shows "S homeomorphic (f`S)"
using assms unfolding homeomorphism_on_def homeomorphic_def by auto

lemma homeomorphism_on_compact:
  fixes f::"'a::topological_space \<Rightarrow> 'b::t2_space"
  assumes "continuous_on S f"
          "compact S"
          "inj_on f S"
  shows "homeomorphism_on S f"
unfolding homeomorphism_on_def using homeomorphism_compact[OF assms(2) assms(1) _ assms(3)] by auto

lemma homeomorphism_on_subset:
  assumes "homeomorphism_on S f"
          "T \<subseteq> S"
  shows "homeomorphism_on T f"
using assms homeomorphism_of_subsets unfolding homeomorphism_on_def by blast

text \<open>Characterization of homeomorphisms in terms of sequences: a map is a homeomorphism if and
only if it respects convergent sequences.\<close>

lemma homeomorphism_on_sequentially:
  fixes f::"'a::{first_countable_topology, t2_space} \<Rightarrow> 'b::{first_countable_topology, t2_space}"
  assumes "\<And>x u. x \<in> S \<Longrightarrow> (\<forall>n. u n \<in> S) \<Longrightarrow> u \<longlonglongrightarrow> x \<longleftrightarrow> (\<lambda>n. f (u n)) \<longlonglongrightarrow> f x"
  shows "homeomorphism_on S f"
proof -
  have "x = y" if "f x = f y" "x \<in> S" "y \<in> S" for x y
  proof -
    have "(\<lambda>n. f x) \<longlonglongrightarrow> f y" using that by auto
    then have "(\<lambda>n. x) \<longlonglongrightarrow> y" using assms(1) that by auto
    then show "x = y" using LIMSEQ_unique by auto
  qed
  then have "inj_on f S" by (simp add: inj_on_def)

  have Cf: "continuous_on S f"
    apply (rule continuous_on_sequentiallyI) using assms by auto
  define g where "g = inv_into S f"
  have Cg: "continuous_on (f`S) g"
  proof (rule continuous_on_sequentiallyI)
    fix v b assume H: "\<forall>n. v n \<in> f ` S" "b \<in> f ` S" "v \<longlonglongrightarrow> b"
    define u where "u = (\<lambda>n. g (v n))"
    define a where "a = g b"
    have "u n \<in> S" "f (u n) = v n" for n
      unfolding u_def g_def using H(1) by (auto simp add: inv_into_into f_inv_into_f)
    have "a \<in> S" "f a = b"
      unfolding a_def g_def using H(2) by (auto simp add: inv_into_into f_inv_into_f)
    show "(\<lambda>n. g(v n)) \<longlonglongrightarrow> g b"
      unfolding u_def[symmetric] a_def[symmetric] apply (rule iffD2[OF assms])
      using \<open>\<And>n. u n \<in> S\<close> \<open>a \<in> S\<close> \<open>v \<longlonglongrightarrow> b\<close>
      unfolding \<open>\<And>n. f (u n) = v n\<close> \<open>f a = b\<close> by auto
  qed
  have "homeomorphism S (f`S) f g"
    apply (rule homeomorphismI[OF Cf Cg]) unfolding g_def using \<open>inj_on f S\<close> by auto
  then show ?thesis
    unfolding homeomorphism_on_def by auto
qed

lemma homeomorphism_on_UNIV_sequentially:
  fixes f::"'a::{first_countable_topology, t2_space} \<Rightarrow> 'b::{first_countable_topology, t2_space}"
  assumes "\<And>x u. u \<longlonglongrightarrow> x \<longleftrightarrow> (\<lambda>n. f (u n)) \<longlonglongrightarrow> f x"
  shows "homeomorphism_on UNIV f"
using assms by (auto intro!: homeomorphism_on_sequentially)

text \<open>Now, we give similar characterizations in terms of sequences living in a dense subset. As
in the sequential continuity criteria above, we first give a very general criterion, where the map
does not have to be continuous on the approximating set $S$, only on the limit set $T$, without
any a priori identification of the limit. Then, we specialize this statement to a less general
but often more usable version.\<close>

lemma homeomorphism_on_extension_sequentially':
  fixes f::"'a::{first_countable_topology, t3_space} \<Rightarrow> 'b::{first_countable_topology, t3_space}"
  assumes "\<And>u b. (\<forall>n. u n \<in> S) \<Longrightarrow> b \<in> T \<Longrightarrow> u \<longlonglongrightarrow> b \<Longrightarrow> convergent (\<lambda>n. f (u n))"
          "\<And>u c. (\<forall>n. u n \<in> S) \<Longrightarrow> c \<in> f`T \<Longrightarrow> (\<lambda>n. f (u n)) \<longlonglongrightarrow> c \<Longrightarrow> convergent u"
          "\<And>b. b \<in> T \<Longrightarrow> \<exists>u. (\<forall>n. u n \<in> S) \<and> u \<longlonglongrightarrow> b \<and> ((\<lambda>n. f (u n)) \<longlonglongrightarrow> f b)"
  shows "homeomorphism_on T f"
proof -
  have "x = y" if "f x = f y" "x \<in> T" "y \<in> T" for x y
  proof -
    obtain u::"nat \<Rightarrow> 'a" where u: "\<And>n. u n \<in> S" "u \<longlonglongrightarrow> x" "(\<lambda>n. f (u n)) \<longlonglongrightarrow> f x"
      using assms(3)[OF \<open>x \<in> T\<close>] by auto
    obtain v::"nat \<Rightarrow> 'a" where v: "\<And>n. v n \<in> S" "v \<longlonglongrightarrow> y" "(\<lambda>n. f (v n)) \<longlonglongrightarrow> f y"
      using assms(3)[OF \<open>y \<in> T\<close>] by auto
    have "even_odd_interpolate (f o u) (f o v) \<longlonglongrightarrow> f x"
      unfolding even_odd_interpolate_filterlim[symmetric] comp_def using u v \<open>f x = f y\<close> by auto
    then have *: "(\<lambda>n. f (even_odd_interpolate u v n)) \<longlonglongrightarrow> f x"
      unfolding even_odd_interpolate_compose unfolding comp_def by auto
    have "convergent (even_odd_interpolate u v)"
      apply (rule assms(2)[OF _ _ *])
      unfolding even_odd_interpolate_def using u(1) v(1) \<open>x \<in> T\<close> by auto
    then obtain z where "even_odd_interpolate u v \<longlonglongrightarrow> z"
      unfolding convergent_def by auto
    then have "u \<longlonglongrightarrow> z" "v \<longlonglongrightarrow> z" unfolding even_odd_interpolate_filterlim[symmetric] by auto
    then have "z = x" "z = y" using u(2) v(2) LIMSEQ_unique by auto
    then show "x = y" by auto
  qed
  then have "inj_on f T" by (simp add: inj_on_def)

  have Cf: "continuous_on T f"
    apply (rule continuous_on_extension_sequentially'[OF assms(1) assms(3)]) by auto
  define g where "g = inv_into T f"
  text \<open>To prove the continuity of the inverse $g$ of $f$, we would like to use the same sequential
  criterion. However, this inverse is only well defined on the image of $T$, not on the image of
  $S \cup T$ (as $f$ does not have to be injective on $S$), which creates a lot of problems to
  apply the criterion. Instead, we prove the continuity by hand, essentially following the proof
  of the criterion but tweaking it here or there.\<close>
  have "continuous (at y within f`T) g" if "y \<in> f`T" for y
  proof (rule ccontr)
    define x where "x = g y"
    have "x \<in> T" "f x = y"
      unfolding x_def g_def using \<open>y \<in> f`T\<close> by (auto simp add: inv_into_into f_inv_into_f)
    assume "\<not> ?thesis"
    then obtain U where U: "open U" "g y \<in> U" "\<not>(\<forall>\<^sub>F z in at y within f`T. g z \<in> U)"
      unfolding continuous_within tendsto_def[where l = "g y"] using sequentially_imp_eventually_nhds_within by auto
    have "\<exists>V W. open V \<and> open W \<and> g y \<in> V \<and> (UNIV - U) \<subseteq> W \<and> V \<inter> W = {}"
      apply (rule t3_space) using U by auto
    then obtain V W where VW: "open V" "open W" "x \<in> V" "UNIV - U \<subseteq> W" "V \<inter> W = {}"
      unfolding \<open>x = g y\<close> by auto

    obtain A :: "nat \<Rightarrow> 'b set" where *:
      "\<And>i. open (A i)"
      "\<And>i. y \<in> A i"
      "\<And>F. \<forall>n. F n \<in> A n \<Longrightarrow> F \<longlonglongrightarrow> y"
      by (rule first_countable_topology_class.countable_basis) blast
    with * U(3) have "\<exists>F. \<forall>n. F n \<in> f`T \<and> F n \<in> A n \<and> \<not> (g(F n) \<in> U)"
      unfolding at_within_def eventually_inf_principal eventually_nhds
      by (intro choice) (meson DiffE)
    then obtain F where F: "\<And>n. F n \<in> f`T" "\<And>n. F n \<in> A n" "\<And>n. g(F n) \<notin> U"
      by auto
    have "\<exists>z. z \<in> S \<and> f z \<in> A n \<and> z \<in> W" for n
    proof -
      define z where "z = g (F n)"
      have "f z = F n"
        unfolding z_def g_def using \<open>F n \<in> f`T\<close> by (simp add: f_inv_into_f)
      then have "f z \<in> A n" using F(2) by auto
      have "z \<in> T" "z \<notin> U"
        unfolding z_def using F by (auto simp add: g_def inv_into_into)
      then have "z \<in> W" using VW by auto
      obtain u::"nat \<Rightarrow> 'a" where u: "\<And>p. u p \<in> S" "u \<longlonglongrightarrow> z" "(\<lambda>p. f (u p)) \<longlonglongrightarrow> f z"
        using assms(3)[OF \<open>z \<in> T\<close>] by auto
      then have "eventually (\<lambda>p. f (u p) \<in> A n) sequentially"
        using \<open>open (A n)\<close> \<open>f z \<in> A n\<close> unfolding tendsto_def by simp
      moreover have "eventually (\<lambda>p. u p \<in> W) sequentially"
        using \<open>open W\<close> \<open>z \<in> W\<close> u unfolding tendsto_def by simp
      ultimately have "\<exists>p. u p \<in> W \<and> f (u p) \<in> A n"
        using eventually_False_sequentially eventually_elim2 by blast
      then show ?thesis using u(1) by auto
    qed
    then have "\<exists>u. \<forall>n. u n \<in> S \<and> f (u n) \<in> A n \<and> u n \<in> W"
      by (auto intro: choice)
    then obtain u where u: "\<And>n. u n \<in> S" "\<And>n. f (u n) \<in> A n" "\<And>n. u n \<in> W"
      by blast
    then have I: "(\<lambda>n. f (u n)) \<longlonglongrightarrow> y" using *(3) by auto

    obtain v where v: "\<And>n. v n \<in> S" "v \<longlonglongrightarrow> x" "((\<lambda>n. f (v n)) \<longlonglongrightarrow> f x)"
      using assms(3)[OF \<open>x \<in> T\<close>] by auto
    have "even_odd_interpolate (f o u) (f o v) \<longlonglongrightarrow> y"
      unfolding even_odd_interpolate_filterlim[symmetric] comp_def using u v I \<open>f x = y\<close> by auto
    then have *: "(\<lambda>n. f (even_odd_interpolate u v n)) \<longlonglongrightarrow> y"
      unfolding even_odd_interpolate_compose unfolding comp_def by auto
    have "convergent (even_odd_interpolate u v)"
      apply (rule assms(2)[OF _ _ *])
      unfolding even_odd_interpolate_def using u(1) v(1) \<open>y \<in> f`T\<close> by auto
    then obtain z where "even_odd_interpolate u v \<longlonglongrightarrow> z"
      unfolding convergent_def by auto
    then have *: "u \<longlonglongrightarrow> z" "v \<longlonglongrightarrow> z" unfolding even_odd_interpolate_filterlim[symmetric] by auto
    then have "z = x" using u(2) v(2) LIMSEQ_unique by auto
    then have "u \<longlonglongrightarrow> x" using * by simp
    then have "eventually (\<lambda>n. u n \<in> V) sequentially"
      using VW by (simp add: tendsto_def)
    then have "\<exists>n. u n \<in> V"
      using eventually_False_sequentially eventually_elim2 by blast
    then show False
      using u(3) \<open>V \<inter> W = {}\<close> by auto
  qed
  then have Cg: "continuous_on (f`T) g"
    by (simp add: continuous_on_eq_continuous_within)
  have "homeomorphism T (f`T) f g"
    apply (rule homeomorphismI[OF Cf Cg]) unfolding g_def using \<open>inj_on f T\<close> by auto
  then show ?thesis
    unfolding homeomorphism_on_def by auto
qed

proposition homeomorphism_on_extension_sequentially:
  fixes f::"'a::{first_countable_topology, t3_space} \<Rightarrow> 'b::{first_countable_topology, t3_space}"
  assumes "\<And>u b. (\<forall>n. u n \<in> S) \<Longrightarrow> u \<longlonglongrightarrow> b \<longleftrightarrow> (\<lambda>n. f (u n)) \<longlonglongrightarrow> f b"
          "T \<subseteq> closure S"
  shows "homeomorphism_on T f"
apply (rule homeomorphism_on_extension_sequentially'[of S])
using assms(1) convergent_def apply fastforce
using assms(1) convergent_def apply blast
by (metis assms(1) assms(2) closure_sequential subsetCE)

lemma homeomorphism_on_UNIV_extension_sequentially:
  fixes f::"'a::{first_countable_topology, t3_space} \<Rightarrow> 'b::{first_countable_topology, t3_space}"
  assumes "\<And>u b. (\<forall>n. u n \<in> S) \<Longrightarrow> u \<longlonglongrightarrow> b \<longleftrightarrow> (\<lambda>n. f (u n)) \<longlonglongrightarrow> f b"
          "closure S = UNIV"
  shows "homeomorphism_on UNIV f"
apply (rule homeomorphism_on_extension_sequentially[of S]) using assms by auto

subsubsection \<open>Proper spaces\<close>

text \<open>Proper spaces, i.e., spaces in which every closed ball is compact -- or, equivalently,
any closed bounded set is compact.\<close>

definition proper::"('a::metric_space) set \<Rightarrow> bool"
  where "proper S \<equiv> (\<forall> x r. compact (cball x r \<inter> S))"

lemma proper_compact_cball:
  assumes "proper (UNIV::'a::metric_space set)"
  shows "compact (cball (x::'a) r)"
using assms unfolding proper_def by auto

lemma proper_compact_bounded_closed:
  assumes "proper (UNIV::'a::metric_space set)" "closed (S::'a set)" "bounded S"
  shows "compact S"
proof -
  obtain x r where "S \<subseteq> cball x r"
    using \<open>bounded S\<close> bounded_subset_cball by blast
  then have *: "S = S \<inter> cball x r"
    by auto
  show ?thesis
    apply (subst *, rule closed_Int_compact) using assms unfolding proper_def by auto
qed

lemma proper_real [simp]:
  "proper (UNIV::real set)"
unfolding proper_def by auto

lemma proper_imp_complete:
  assumes "proper S"
  shows "complete S"
proof -
  have "\<exists>l\<in>S. u \<longlonglongrightarrow> l" if "Cauchy u" "\<And>n. u n \<in> S" for u
  proof -
    have "bounded (range u)"
      using \<open>Cauchy u\<close> cauchy_imp_bounded by auto
    then obtain x r where *: "\<And>n. dist x (u n) \<le> r"
      unfolding bounded_def by auto
    then have "u n \<in> (cball x r) \<inter> S" for n using \<open>u n \<in> S\<close> by auto
    moreover have "complete ((cball x r) \<inter> S)"
      apply (rule compact_imp_complete) using assms unfolding proper_def by auto
    ultimately show ?thesis
      unfolding complete_def using \<open>Cauchy u\<close> by auto
  qed
  then show ?thesis
    unfolding complete_def by auto
qed


subsubsection \<open>Measure of balls\<close>

text \<open>The image of a ball by an affine map is still a ball, with explicit center and radius.\<close>

lemma affine_image_ball [simp]:
  "(\<lambda>y. R *\<^sub>R y + x) ` cball 0 1 = cball (x::('a::real_normed_vector)) \<bar>R\<bar>"
proof
  have "dist x (R *\<^sub>R y + x) \<le> \<bar>R\<bar>" if "dist 0 y \<le> 1" for y
  proof -
    have "dist x (R *\<^sub>R y + x) = norm ((R *\<^sub>R y + x) - x)" by (simp add: dist_norm)
    also have "... = \<bar>R\<bar> * norm y" by auto
    finally show ?thesis using that by (simp add: mult_left_le)
  qed
  then show "(\<lambda>y. R *\<^sub>R y + x) ` cball 0 1 \<subseteq> cball x \<bar>R\<bar>" by auto

  show "cball x \<bar>R\<bar> \<subseteq> (\<lambda>y. R *\<^sub>R y + x) ` cball 0 1"
  proof (cases "\<bar>R\<bar> = 0")
    case True
    then have "cball x \<bar>R\<bar> = {x}" by auto
    moreover have "x = R *\<^sub>R 0 + x \<and> 0 \<in> cball 0 1" by auto
    ultimately show ?thesis by auto
  next
    case False
    have "z \<in> (\<lambda>y. R *\<^sub>R y + x) ` cball 0 1" if "z \<in> cball x \<bar>R\<bar>" for z
    proof -
      define y where "y = (z - x) /\<^sub>R R"
      have "R *\<^sub>R y + x = z" unfolding y_def using False by auto
      moreover have "y \<in> cball 0 1"
        using \<open>z \<in> cball x \<bar>R\<bar>\<close> False unfolding y_def by (auto simp add: dist_norm[symmetric] divide_simps dist_commute)
      ultimately show ?thesis by auto
    qed
    then show ?thesis by auto
  qed
qed

text \<open>From the rescaling properties of Lebesgue measure in a euclidean space, it follows that
the measure of any ball can be expressed in terms of the measure of the unit ball.\<close>

lemma lebesgue_measure_ball:
  assumes "R\<ge>0"
  shows "measure lborel (cball (x::('a::euclidean_space)) R) = R^(DIM('a)) * measure lborel (cball (0::'a) 1)"
        "emeasure lborel (cball (x::('a::euclidean_space)) R) = R^(DIM('a)) * emeasure lborel (cball (0::'a) 1)"
using measure_lebesgue_affine[of R x "cball 0 1"] emeasure_lebesgue_affine[of R x "cball 0 1"] assms
unfolding affine_image_ball by (auto simp add: ennreal_power)

text \<open>We show that the unit ball has positive measure -- this is obvious, but useful. We could
show it by arguing that it contains a box, whose measure can be computed, but instead we say
that if the measure vanished then the measure of any ball would also vanish, contradicting the
fact that the space has infinite measure. This avoids all computations.\<close>

lemma lebesgue_measure_ball_pos:
  "emeasure lborel (cball (0::'a::euclidean_space) 1) > 0"
  "measure lborel (cball (0::'a::euclidean_space) 1) > 0"
proof -
  show "emeasure lborel (cball (0::'a::euclidean_space) 1) > 0"
  proof (rule ccontr)
    assume "\<not>(emeasure lborel (cball (0::'a::euclidean_space) 1) > 0)"
    then have "emeasure lborel (cball (0::'a) 1) = 0" by auto
    then have "emeasure lborel (cball (0::'a) n) = 0" for n::nat
      using lebesgue_measure_ball(2)[of "real n" 0] by (metis mult_zero_right of_nat_0_le_iff)
    then have "emeasure lborel (\<Union>n. cball (0::'a) (real n)) = 0"
      by (metis (mono_tags, lifting) borel_closed closed_cball emeasure_UN_eq_0 imageE sets_lborel subsetI)
    moreover have "(\<Union>n. cball (0::'a) (real n)) = UNIV" by (auto simp add: real_arch_simple)
    ultimately show False
      by (simp add: emeasure_lborel_UNIV)
  qed
  moreover have "emeasure lborel (cball (0::'a::euclidean_space) 1) < \<infinity>"
    by (rule emeasure_bounded_finite, auto)
  ultimately show "measure lborel (cball (0::'a::euclidean_space) 1) > 0"
    by (metis borel_closed closed_cball ennreal_0 has_integral_iff_emeasure_lborel has_integral_measure_lborel less_irrefl order_refl zero_less_measure_iff)
qed

subsubsection \<open>Miscellaneous topology\<close>

text \<open>When manipulating the triangle inequality, it is very frequent to deal with 4 points
(and automation has trouble doing it automatically). Even sometimes with 5 points...\<close>

lemma dist_triangle4 [mono_intros]:
  "dist x t \<le> dist x y + dist y z + dist z t"
using dist_triangle[of x z y] dist_triangle[of x t z] by auto

lemma dist_triangle5 [mono_intros]:
  "dist x u \<le> dist x y + dist y z + dist z t + dist t u"
using dist_triangle4[of x u y z] dist_triangle[of z u t] by auto

text \<open>A thickening of a compact set is closed.\<close>

lemma compact_has_closed_thickening:
  assumes "compact C"
          "continuous_on C f"
  shows "closed (\<Union>x\<in>C. cball x (f x))"
proof (auto simp add: closed_sequential_limits)
  fix u l assume *: "\<forall>n::nat. \<exists>x\<in>C. dist x (u n) \<le> f x" "u \<longlonglongrightarrow> l"
  have "\<exists>x::nat\<Rightarrow>'a. \<forall>n. x n \<in> C \<and> dist (x n) (u n) \<le> f (x n)"
    apply (rule choice) using * by auto
  then obtain x::"nat \<Rightarrow> 'a" where x: "\<And>n. x n \<in> C" "\<And>n. dist (x n) (u n) \<le> f (x n)"
    by blast
  obtain r c where "strict_mono r" "c \<in> C" "(x o r) \<longlonglongrightarrow> c"
    using x(1) \<open>compact C\<close> by (meson compact_eq_seq_compact_metric seq_compact_def)
  then have "c \<in> C" using x(1) \<open>compact C\<close> by auto
  have lim: "(\<lambda>n. f (x (r n)) - dist (x (r n)) (u (r n))) \<longlonglongrightarrow> f c - dist c l"
    apply (intro tendsto_intros, rule continuous_on_tendsto_compose[of C f])
    using *(2) x(1) \<open>(x o r) \<longlonglongrightarrow> c\<close> \<open>continuous_on C f\<close> \<open>c \<in> C\<close> \<open>strict_mono r\<close> LIMSEQ_subseq_LIMSEQ
    unfolding comp_def by auto
  have "f c - dist c l \<ge> 0" apply (rule LIMSEQ_le_const[OF lim]) using x(2) by auto
  then show "\<exists>x\<in>C. dist x l \<le> f x" using \<open>c \<in> C\<close> by auto
qed

subsection \<open>Material on ereal and ennreal\<close>

text \<open>More additions to \verb+tendsto_intros+.\<close>

lemma ereal_leq_imp_neg_leq [mono_intros]:
  fixes x y::ereal
  assumes "x \<le> y"
  shows "-y \<le> -x"
  using assms by auto

lemma ereal_le_imp_neg_le [mono_intros]:
  fixes x y::ereal
  assumes "x < y"
  shows "-y < -x"
  using assms by auto

text \<open>Monotonicity of basic inclusions.\<close>

lemma ennreal_mono':
  "mono ennreal"
by (simp add: ennreal_leI monoI)

lemma enn2ereal_mono':
  "mono enn2ereal"
by (simp add: less_eq_ennreal.rep_eq mono_def)

lemma e2ennreal_mono':
  "mono e2ennreal"
by (simp add: e2ennreal_mono mono_def)

lemma enn2ereal_mono [mono_intros]:
  assumes "x \<le> y"
  shows "enn2ereal x \<le> enn2ereal y"
  using assms less_eq_ennreal.rep_eq by auto

lemma ereal_mono [mono_intros]:
  assumes "x \<le> y"
  shows "ereal x \<le> ereal y"
by (simp add: assms)

lemma enn2ereal_a_minus_b_plus_b [mono_intros]:
  "enn2ereal a \<le> enn2ereal (a - b) + enn2ereal b"
by (metis diff_add_self_ennreal less_eq_ennreal.rep_eq linear plus_ennreal.rep_eq)

text \<open>The next lemma follows from the same assertion in ereals.\<close>

lemma enn2ereal_strict_mono [mono_intros]:
  assumes "x < y"
  shows "enn2ereal x < enn2ereal y"
  using assms less_ennreal.rep_eq by auto

declare ennreal_mult_strict_left_mono [mono_intros]

lemma ennreal_ge_0 [mono_intros]:
  assumes "0 < x"
  shows "0 < ennreal x"
by (simp add: assms)


text \<open>The next lemma is true and useful in ereal, note that variants such as $a + b \leq c + d$
implies $a-d \leq c -b$ are not true -- take $a = c = \infty$ and $b = d = 0$...\<close>

lemma ereal_minus_le_minus_plus [mono_intros]:
  fixes a b c::ereal
  assumes "a \<le> b + c"
  shows "-b \<le> -a + c"
  using assms apply (cases a, cases b, cases c, auto)
  using ereal_infty_less_eq2(2) ereal_plus_1(4) by fastforce

lemma tendsto_ennreal_0 [tendsto_intros]:
  assumes "(u \<longlongrightarrow> 0) F"
  shows "((\<lambda>n. ennreal(u n)) \<longlongrightarrow> 0) F"
unfolding ennreal_0[symmetric] by (intro tendsto_intros assms)

lemma tendsto_ennreal_1 [tendsto_intros]:
  assumes "(u \<longlongrightarrow> 1) F"
  shows "((\<lambda>n. ennreal(u n)) \<longlongrightarrow> 1) F"
unfolding ennreal_1[symmetric] by (intro tendsto_intros assms)

subsection \<open>Miscellaneous\<close>

lemma power4_eq_xxxx:
  fixes x::"'a::monoid_mult"
  shows "x^4 = x * x * x * x"
by (simp add: mult.assoc power_numeral_even)

subsubsection \<open>Liminfs and Limsups\<close>

text \<open>More facts on liminfs and limsups\<close>

lemma Limsup_obtain':
  fixes u::"'a \<Rightarrow> 'b::complete_linorder"
  assumes "Limsup F u > c" "eventually P F"
  shows "\<exists>n. P n \<and> u n > c"
proof -
  have *: "(INF P:{P. eventually P F}. SUP x:{x. P x}. u x) > c" using assms by (simp add: Limsup_def)
  have **: "c < (SUP x:{x. P x}. u x)" using less_INF_D[OF *, of P] assms by auto
  then show ?thesis by (simp add: less_SUP_iff)
qed

lemma limsup_obtain:
  fixes u::"nat \<Rightarrow> 'a :: complete_linorder"
  assumes "limsup u > c"
  shows "\<exists>n \<ge> N. u n > c"
using Limsup_obtain'[OF assms, of "\<lambda>n. n \<ge> N"] unfolding eventually_sequentially by auto

lemma Liminf_obtain':
  fixes u::"'a \<Rightarrow> 'b::complete_linorder"
  assumes "Liminf F u < c" "eventually P F"
  shows "\<exists>n. P n \<and> u n < c"
proof -
  have *: "(SUP P:{P. eventually P F}. INF x:{x. P x}. u x) < c" using assms by (simp add: Liminf_def)
  have **: "(INF x:{x. P x}. u x) < c" using SUP_lessD[OF *, of P] assms by auto
  then show ?thesis by (simp add: INF_less_iff)
qed

lemma liminf_obtain:
  fixes u::"nat \<Rightarrow> 'a :: complete_linorder"
  assumes "liminf u < c"
  shows "\<exists>n \<ge> N. u n < c"
using Liminf_obtain'[OF assms, of "\<lambda>n. n \<ge> N"] unfolding eventually_sequentially by auto

text \<open>The Liminf of a minimum is the minimum of the Liminfs.\<close>

lemma Liminf_min_eq_min_Liminf:
  fixes u v::"nat \<Rightarrow> 'a::complete_linorder"
  shows "Liminf F (\<lambda>n. min (u n) (v n)) = min (Liminf F u) (Liminf F v)"
proof (rule order_antisym)
  show "Liminf F (\<lambda>n. min (u n) (v n)) \<le> min (Liminf F u) (Liminf F v)"
    by (auto simp add: Liminf_mono)

  have "Liminf F (\<lambda>n. min (u n) (v n)) > w" if H: "min (Liminf F u) (Liminf F v) > w" for w
  proof (cases "{w<..<min (Liminf F u) (Liminf F v)} = {}")
    case True
    have "eventually (\<lambda>n. u n > w) F" "eventually (\<lambda>n. v n > w) F"
      using H le_Liminf_iff by fastforce+
    then have "eventually (\<lambda>n. min (u n) (v n) > w) F"
      apply auto using eventually_elim2 by fastforce
    moreover have "z > w \<Longrightarrow> z \<ge> min (Liminf F u) (Liminf F v)" for z
      using H True not_le_imp_less by fastforce
    ultimately have "eventually (\<lambda>n. min (u n) (v n) \<ge> min (Liminf F u) (Liminf F v)) F"
      by (simp add: eventually_mono)
    then have "min (Liminf F u) (Liminf F v) \<le> Liminf F (\<lambda>n. min (u n) (v n))"
      by (metis Liminf_bounded)
    then show ?thesis using H less_le_trans by blast
  next
    case False
    then obtain z where "z \<in> {w<..<min (Liminf F u) (Liminf F v)}"
      by blast
    then have H: "w < z" "z < min (Liminf F u) (Liminf F v)"
      by auto
    then have "eventually (\<lambda>n. u n > z) F" "eventually (\<lambda>n. v n > z) F"
      using le_Liminf_iff by fastforce+
    then have "eventually (\<lambda>n. min (u n) (v n) > z) F"
      apply auto using eventually_elim2 by fastforce
    then have "Liminf F (\<lambda>n. min (u n) (v n)) \<ge> z"
      by (simp add: Liminf_bounded eventually_mono less_imp_le)
    then show ?thesis using H(1)
      by auto
  qed
  then show "min (Liminf F u) (Liminf F v) \<le> Liminf F (\<lambda>n. min (u n) (v n))"
    using not_le_imp_less by blast
qed

subsubsection \<open>Bounding the cardinality of a finite set\<close>

text \<open>A variation with real bounds.\<close>

lemma finite_finite_subset_caract':
  fixes C::real
  assumes "\<And>G. G \<subseteq> F \<Longrightarrow> finite G \<Longrightarrow> card G \<le> C"
  shows "finite F \<and> card F \<le> C"
by (meson assms finite_if_finite_subsets_card_bdd le_nat_floor order_refl)

text \<open>To show that a set has cardinality at most one, it suffices to show that any two of its
elements coincide.\<close>

lemma finite_at_most_singleton:
  assumes "\<And>x y. x \<in> F \<Longrightarrow> y \<in> F \<Longrightarrow> x = y"
  shows "finite F \<and> card F \<le> 1"
proof (cases "F = {}")
  case True
  then show ?thesis by auto
next
  case False
  then obtain x where "x \<in> F" by auto
  then have "F = {x}" using assms by auto
  then show ?thesis by auto
qed

text \<open>Bounded sets of integers are finite.\<close>

lemma finite_real_int_interval [simp]:
  "finite (range real_of_int \<inter> {a..b})"
proof -
  have "range real_of_int \<inter> {a..b} \<subseteq> real_of_int`{floor a..ceiling b}"
    by (auto, metis atLeastAtMost_iff ceiling_mono ceiling_of_int floor_mono floor_of_int image_eqI)
  then show ?thesis using finite_subset by blast
qed

text \<open>Well separated sets of real numbers are finite, with controlled cardinality.\<close>

lemma separated_in_real_card_bound:
  assumes "T \<subseteq> {a..(b::real)}" "d > 0" "\<And>x y. x \<in> T \<Longrightarrow> y \<in> T \<Longrightarrow> y > x \<Longrightarrow> y \<ge> x + d"
  shows "finite T" "card T \<le> nat (floor ((b-a)/d) + 1)"
proof -
  define f where "f = (\<lambda>x. floor ((x-a) / d))"
  have "f`{a..b} \<subseteq> {0..floor ((b-a)/d)}"
    unfolding f_def using \<open>d > 0\<close> by (auto simp add: floor_mono frac_le)
  then have *: "f`T \<subseteq> {0..floor ((b-a)/d)}" using \<open>T \<subseteq> {a..b}\<close> by auto
  then have "finite (f`T)" by (rule finite_subset, auto)
  have "card (f`T) \<le> card {0..floor ((b-a)/d)}" apply (rule card_mono) using * by auto
  then have card_le: "card (f`T) \<le> nat (floor ((b-a)/d) + 1)" using card_atLeastAtMost_int by auto

  have *: "f x \<noteq> f y" if "y \<ge> x + d" for x y
  proof -
    have "(y-a)/d \<ge> (x-a)/d + 1" using \<open>d>0\<close> that by (auto simp add: divide_simps)
    then show ?thesis unfolding f_def by linarith
  qed
  have "inj_on f T"
    unfolding inj_on_def using * assms(3) by (auto, metis not_less_iff_gr_or_eq)
  show "finite T"
    using \<open>finite (f`T)\<close> \<open>inj_on f T\<close> finite_image_iff by blast
  have "card T = card (f`T)"
    using \<open>inj_on f T\<close> by (simp add: card_image)
  then show "card T \<le> nat (floor ((b-a)/d) + 1)"
    using card_le by auto
qed


subsection \<open>Manipulating finite ordered sets\<close>

text \<open>We will need below to contruct finite sets of real numbers with good properties expressed
in terms of consecutive elements of the set. We introduce tools to manipulate such sets,
expressing in particular the next and the previous element of the set and controlling how they
evolve when one inserts a new element in the set. It works in fact in any linorder, and could
also prove useful to construct sets of integer numbers.

Manipulating the next and previous elements work well, except at the top (respectively bottom).
In our constructions, these will be fixed and called $b$ and $a$.\<close>

text \<open>Notations for the next and the previous elements.\<close>

definition next_in::"'a set \<Rightarrow> 'a \<Rightarrow> ('a::linorder)"
  where "next_in A u = Min (A \<inter> {u<..})"

definition prev_in::"'a set \<Rightarrow> 'a \<Rightarrow> ('a::linorder)"
  where "prev_in A u = Max (A \<inter> {..<u})"

context
  fixes A::"('a::linorder) set" and a b::'a
  assumes A: "finite A" "A \<subseteq> {a..b}" "a \<in> A" "b \<in> A" "a < b"
begin

text \<open>Basic properties of the next element, when one starts from an element different from top.\<close>

lemma next_in_basics:
  assumes "u \<in> {a..<b}"
  shows "next_in A u \<in> A"
        "next_in A u > u"
        "A \<inter> {u<..<next_in A u} = {}"
proof -
  have next_in_A: "next_in A u \<in> A \<inter> {u<..}"
    unfolding next_in_def apply (rule Min_in)
    using assms \<open>finite A\<close> \<open>b \<in> A\<close> by auto
  then show "next_in A u \<in> A" "next_in A u > u" by auto
  show "A \<inter> {u<..<next_in A u} = {}"
    unfolding next_in_def using A by (auto simp add: leD)
qed

lemma next_inI:
  assumes "u \<in> {a..<b}"
          "v \<in> A"
          "v > u"
          "{u<..<v} \<inter> A = {}"
  shows "next_in A u = v"
using assms next_in_basics[OF \<open>u \<in> {a..<b}\<close>] by fastforce

text \<open>Basic properties of the previous element, when one starts from an element different from
bottom.\<close>

lemma prev_in_basics:
  assumes "u \<in> {a<..b}"
  shows "prev_in A u \<in> A"
        "prev_in A u < u"
        "A \<inter> {prev_in A u<..<u} = {}"
proof -
  have prev_in_A: "prev_in A u \<in> A \<inter> {..<u}"
    unfolding prev_in_def apply (rule Max_in)
    using assms \<open>finite A\<close> \<open>a \<in> A\<close> by auto
  then show "prev_in A u \<in> A" "prev_in A u < u" by auto
  show "A \<inter> {prev_in A u<..<u} = {}"
    unfolding prev_in_def using A by (auto simp add: leD)
qed

lemma prev_inI:
  assumes "u \<in> {a<..b}"
          "v \<in> A"
          "v < u"
          "{v<..<u} \<inter> A = {}"
  shows "prev_in A u = v"
using assms prev_in_basics[OF \<open>u \<in> {a<..b}\<close>]
by (meson disjoint_iff_not_equal greaterThanLessThan_iff less_linear)

text \<open>The interval $[a,b]$ is covered by the intervals between the consecutive elements of $A$.\<close>

lemma intervals_decomposition:
  "(\<Union> U \<in> {{u..next_in A u} | u. u \<in> A - {b}}. U) = {a..b}"
proof
  show "(\<Union>U\<in>{{u..next_in A u} |u. u \<in> A - {b}}. U) \<subseteq> {a..b}"
    using \<open>A \<subseteq> {a..b}\<close> next_in_basics(1) apply auto apply fastforce
    by (metis \<open>A \<subseteq> {a..b}\<close> atLeastAtMost_iff eq_iff le_less_trans less_eq_real_def not_less subset_eq subset_iff_psubset_eq)

  have "x \<in> (\<Union>U\<in>{{u..next_in A u} |u. u \<in> A - {b}}. U)" if "x \<in> {a..b}" for x
  proof -
    consider "x = b" | "x \<in> A - {b}" | "x \<notin> A" by blast
    then show ?thesis
    proof(cases)
      case 1
      define u where "u = prev_in A b"
      have "b \<in> {a<..b}" using \<open>a < b\<close> by simp
      have "u \<in> A - {b}" unfolding u_def using prev_in_basics[OF \<open>b \<in> {a<..b}\<close>] by simp
      then have "u \<in> {a..<b}" using \<open>A \<subseteq> {a..b}\<close> \<open>a < b\<close> by fastforce
      have "next_in A u = b"
        using prev_in_basics[OF \<open>b \<in> {a<..b}\<close>] next_in_basics[OF \<open>u \<in> {a..<b}\<close>] \<open>A \<subseteq> {a..b}\<close> unfolding u_def by force
      then have "x \<in> {u..next_in A u}" unfolding 1 using prev_in_basics[OF \<open>b \<in> {a<..b}\<close>] u_def by auto
      then show ?thesis using \<open>u \<in> A - {b}\<close> by auto
    next
      case 2
      then have "x \<in> {a..<b}" using \<open>A \<subseteq> {a..b}\<close> \<open>a < b\<close> by fastforce
      have "x \<in> {x.. next_in A x}" using next_in_basics[OF \<open>x \<in> {a..<b}\<close>] by auto
      then show ?thesis using 2 by auto
    next
      case 3
      then have "x \<in> {a<..b}" using that \<open>a \<in> A\<close> leI by fastforce
      define u where "u = prev_in A x"
      have "u \<in> A - {b}" unfolding u_def using prev_in_basics[OF \<open>x \<in> {a<..b}\<close>] that by auto
      then have "u \<in> {a..<b}" using \<open>A \<subseteq> {a..b}\<close> \<open>a < b\<close> by fastforce
      have "x \<in> {u..next_in A u}"
        using prev_in_basics[OF \<open>x \<in> {a<..b}\<close>] next_in_basics[OF \<open>u \<in> {a..<b}\<close>] unfolding u_def by auto
      then show ?thesis using \<open>u \<in> A - {b}\<close> by auto
    qed
  qed
  then show "{a..b} \<subseteq> (\<Union>U\<in>{{u..next_in A u} |u. u \<in> A - {b}}. U)" by auto
qed
end

text \<open>If one inserts an additional element, then next and previous elements are not modified,
except at the location of the insertion.\<close>

lemma next_in_insert:
  assumes A: "finite A" "A \<subseteq> {a..b}" "a \<in> A" "b \<in> A" "a < b"
      and "x \<in> {a..b} - A"
  shows "\<And>u. u \<in> A - {b, prev_in A x} \<Longrightarrow> next_in (insert x A) u = next_in A u"
        "next_in (insert x A) x = next_in A x"
        "next_in (insert x A) (prev_in A x) = x"
proof -
  define B where "B = insert x A"
  have B: "finite B" "B \<subseteq> {a..b}" "a \<in> B" "b \<in> B" "a < b"
    using assms unfolding B_def by auto
  have x: "x \<in> {a..<b}" "x \<in> {a<..b}" using assms leI by fastforce+
  show "next_in B x = next_in A x"
    unfolding B_def by (auto simp add: next_in_def)

  show "next_in B (prev_in A x) = x"
    apply (rule next_inI[OF B])
    unfolding B_def using prev_in_basics[OF A \<open>x \<in> {a<..b}\<close>] \<open>A \<subseteq> {a..b}\<close> x by auto

  fix u assume "u \<in> A - {b, prev_in A x}"
  then have "u \<in> {a..<b}" using assms by fastforce
  have "x \<notin> {u<..<next_in A u}"
  proof (rule ccontr)
    assume "\<not>(x \<notin> {u<..<next_in A u})"
    then have *: "x \<in> {u<..<next_in A u}" by auto
    have "prev_in A x = u"
      apply (rule prev_inI[OF A \<open>x \<in> {a<..b}\<close>])
      using \<open>u \<in> A - {b, prev_in A x}\<close> * next_in_basics[OF A \<open>u \<in> {a..<b}\<close>] apply auto
      by (meson disjoint_iff_not_equal greaterThanLessThan_iff less_trans)
    then show False using \<open>u \<in> A - {b, prev_in A x}\<close> by auto
  qed
  show "next_in B u = next_in A u"
    apply (rule next_inI[OF B \<open>u \<in> {a..<b}\<close>]) unfolding B_def
    using next_in_basics[OF A \<open>u \<in> {a..<b}\<close>] \<open>x \<notin> {u<..<next_in A u}\<close> by auto
qed

text \<open>If consecutive elements are enough separated, this implies a simple bound on the
cardinality of the set.\<close>

lemma separated_in_real_card_bound2:
  fixes A::"real set"
  assumes A: "finite A" "A \<subseteq> {a..b}" "a \<in> A" "b \<in> A" "a < b"
      and B: "\<And>u. u \<in> A - {b} \<Longrightarrow> next_in A u \<ge> u + d" "d > 0"
  shows "card A \<le> nat (floor ((b-a)/d) + 1)"
proof (rule separated_in_real_card_bound[OF \<open>A \<subseteq> {a..b}\<close> \<open>d > 0\<close>])
  fix x y assume "x \<in> A" "y \<in> A" "y > x"
  then have "x \<in> A - {b}" "x \<in> {a..<b}" using \<open>A \<subseteq> {a..b}\<close> by auto
  have "y \<ge> next_in A x"
    using next_in_basics[OF A \<open>x \<in> {a..<b}\<close>] \<open>y \<in> A\<close> \<open>y > x\<close> by auto
  then show "y \<ge> x + d" using B(1)[OF \<open>x \<in> A - {b}\<close>] by auto
qed


subsection \<open>Well-orders\<close>

text \<open>In this subsection, we give additional lemmas on well-orders or cardinals or whatever,
that would well belong to the library, and will be needed below.\<close>

lemma (in wo_rel) max2_underS [simp]:
  assumes "x \<in> underS z" "y \<in> underS z"
  shows "max2 x y \<in> underS z"
using assms max2_def by auto

lemma (in wo_rel) max2_underS' [simp]:
  assumes "x \<in> underS y"
  shows "max2 x y = y" "max2 y x = y"
apply (simp add: underS_E assms max2_def)
using assms max2_def ANTISYM antisym_def underS_E by fastforce

lemma (in wo_rel) max2_xx [simp]:
  "max2 x x = x"
using max2_def by auto

declare underS_notIn [simp]

text \<open>The abbrevation $=o$ is used both in \verb+Set_Algebras+ and Cardinals.
We disable the one from \verb+Set_Algebras+.\<close>

no_notation elt_set_eq (infix "=o" 50)

lemma regularCard_ordIso:
  assumes "Card_order r" "regularCard r" "s =o r"
  shows "regularCard s"
unfolding regularCard_def
proof (auto)
  fix K assume K: "K \<subseteq> Field s" "cofinal K s"
  obtain f where f: "bij_betw f (Field s) (Field r)" "embed s r f" using \<open>s =o r\<close> unfolding ordIso_def iso_def by auto
  have "f`K \<subseteq> Field r" using K(1) f(1) bij_betw_imp_surj_on by blast
  have "cofinal (f`K) r" unfolding cofinal_def
  proof
    fix a assume "a \<in> Field r"
    then obtain a' where a: "a' \<in> Field s" "f a' = a" using f
      by (metis bij_betw_imp_surj_on imageE)
    then obtain b' where b: "b' \<in> K" "a' \<noteq> b' \<and> (a', b') \<in> s"
      using \<open>cofinal K s\<close> unfolding cofinal_def by auto
    have P1: "f b' \<in> f`K" using b(1) by auto
    have "a' \<noteq> b'" "a' \<in> Field s" "b' \<in> Field s" using a(1) b K(1) by auto
    then have P2: "a \<noteq> f b'" unfolding a(2)[symmetric] using f(1) unfolding bij_betw_def inj_on_def by auto
    have "(a', b') \<in> s" using b by auto
    then have P3: "(a, f b') \<in> r" unfolding a(2)[symmetric] using f
      by (meson FieldI1 FieldI2 Card_order_ordIso[OF assms(1) assms(3)] card_order_on_def iso_defs(1) iso_iff2)
    show "\<exists>b\<in>f ` K. a \<noteq> b \<and> (a, b) \<in> r"
      using P1 P2 P3 by blast
  qed
  then have "|f`K| =o r"
    using \<open>regularCard r\<close> \<open>f`K \<subseteq> Field r\<close> unfolding regularCard_def by auto
  moreover have "|f`K| =o |K|" using f(1) K(1)
    by (meson bij_betw_subset card_of_ordIsoI ordIso_symmetric)
  ultimately show "|K| =o s"
    using \<open>s =o r\<close> by (meson ordIso_symmetric ordIso_transitive)
qed

lemma AboveS_not_empty_in_regularCard:
  assumes "|S| <o r" "S \<subseteq> Field r"
  assumes r: "Card_order r" "regularCard r" "\<not>finite (Field r)"
  shows "AboveS r S \<noteq> {}"
proof -
  have "\<not>(cofinal S r)"
    using assms not_ordLess_ordIso unfolding regularCard_def by auto
  then obtain a where a: "a \<in> Field r" "\<forall>b\<in>S. \<not>(a \<noteq> b \<and> (a,b) \<in> r)"
    unfolding cofinal_def by auto
  have *: "a = b \<or> (b, a) \<in> r" if "b \<in> S" for b
  proof -
    have "a = b \<or> (a,b) \<notin> r" using a that by auto
    then show ?thesis
      using \<open>Card_order r\<close> \<open>a \<in> Field r\<close> \<open>b \<in> S\<close> \<open>S \<subseteq> Field r\<close> unfolding card_order_on_def well_order_on_def linear_order_on_def total_on_def
      by auto
  qed
  obtain c where "c \<in> Field r" "c \<noteq> a" "(a, c) \<in> r"
    using a(1) r infinite_Card_order_limit by fastforce
  then have "c \<in> AboveS r S"
    unfolding AboveS_def apply simp using Card_order_trans[OF r(1)] by (metis *)
  then show ?thesis by auto
qed

lemma AboveS_not_empty_in_regularCard':
  assumes "|S| <o r" "f`S \<subseteq> Field r" "T \<subseteq> S"
  assumes r: "Card_order r" "regularCard r" "\<not>finite (Field r)"
  shows "AboveS r (f`T) \<noteq> {}"
proof -
  have "|f`T| \<le>o |T|" by simp
  moreover have "|T| \<le>o |S|" using \<open>T \<subseteq> S\<close> by simp
  ultimately have *: "|f`T| <o r" using \<open>|S| <o r\<close> by (meson ordLeq_ordLess_trans)
  show ?thesis using AboveS_not_empty_in_regularCard[OF * _ r] \<open>T \<subseteq> S\<close> \<open>f`S \<subseteq> Field r\<close> by auto
qed

lemma Well_order_extend:
assumes WELL: "well_order_on A r" and SUB: "A \<subseteq> B"
shows "\<exists>r'. well_order_on B r' \<and> r \<subseteq> r'"
proof-
  have r: "Well_order r \<and> Field r = A" using WELL well_order_on_Well_order by blast
  let ?C = "B - A"
  obtain r'' where "well_order_on ?C r''" using well_order_on by blast
  then have r'': "Well_order r'' \<and> Field r'' = ?C"
    using well_order_on_Well_order by blast
  let ?r' = "r Osum r''"
  have "Field r Int Field r'' = {}" using r r'' by auto
  then have "r \<le>o ?r'" using Osum_ordLeq[of r r''] r r'' by blast
  then have "Well_order ?r'" unfolding ordLeq_def by auto
  moreover have "Field ?r' = B" using r r'' SUB by (auto simp add: Field_Osum)
  ultimately have "well_order_on B ?r'" by auto
  moreover have "r \<subseteq> ?r'" by (simp add: Osum_def subrelI)
  ultimately show ?thesis by blast
qed

text \<open>The next lemma shows that, if the range of a function is endowed with a wellorder,
then one can pull back this wellorder by the function, and then extend it in the fibers
of the function in order to keep the wellorder property.

The proof is done by taking an arbitrary family of wellorders on each of the fibers, and using
the lexicographic order: one has $x < y$ if $f x < f y$, or if $f x = f y$ and, in the corresponding
fiber of $f$, one has $x < y$.

To formalize it, it is however more efficient to use one single wellorder, and restrict it
to each fiber.\<close>

lemma Well_order_pullback:
  assumes "Well_order r"
  shows "\<exists>s. Well_order s \<and> Field s = UNIV \<and> (\<forall>x y. (f x, f y) \<in> (r-Id) \<longrightarrow> (x, y) \<in> s)"
proof -
  obtain r2 where r2: "Well_order r2" "Field r2 = UNIV" "r \<subseteq> r2"
    using Well_order_extend[OF assms, of UNIV] well_order_on_Well_order by auto
  obtain s2 where s2: "Well_order s2" "Field s2 = (UNIV::'b set)"
    by (meson well_ordering)

  have r2s2:
    "\<And>x y z. (x, y) \<in> s2 \<Longrightarrow> (y, z) \<in> s2 \<Longrightarrow> (x, z) \<in> s2"
    "\<And>x. (x, x) \<in> s2"
    "\<And>x y. (x, y) \<in> s2 \<or> (y, x) \<in> s2"
    "\<And>x y. (x, y) \<in> s2 \<Longrightarrow> (y, x) \<in> s2 \<Longrightarrow> x = y"
    "\<And>x y z. (x, y) \<in> r2 \<Longrightarrow> (y, z) \<in> r2 \<Longrightarrow> (x, z) \<in> r2"
    "\<And>x. (x, x) \<in> r2"
    "\<And>x y. (x, y) \<in> r2 \<or> (y, x) \<in> r2"
    "\<And>x y. (x, y) \<in> r2 \<Longrightarrow> (y, x) \<in> r2 \<Longrightarrow> x = y"
    using r2 s2 unfolding well_order_on_def linear_order_on_def partial_order_on_def total_on_def preorder_on_def antisym_def refl_on_def trans_def
    by (metis UNIV_I)+

  define s where "s = {(x,y). (f x, f y) \<in> r2 \<and> (f x = f y \<longrightarrow> (x, y) \<in> s2)}"
  have "linear_order s"
  unfolding linear_order_on_def partial_order_on_def preorder_on_def
  proof (auto)
    show "total_on UNIV s"
      unfolding s_def apply (rule total_onI, auto) using r2s2 by metis+
    show "refl_on UNIV s"
      unfolding s_def apply (rule refl_onI, auto) using r2s2 by blast+
    show "trans s"
      unfolding s_def apply (rule transI, auto) using r2s2 by metis+
    show "antisym s"
      unfolding s_def apply (rule antisymI, auto) using r2s2 by metis+
  qed
  moreover have "wf (s - Id)"
  proof (rule wfI_min)
    fix x::'b and Q assume "x \<in> Q"
    obtain z' where z': "z' \<in> f`Q" "\<And>y. (y, z') \<in> r2 - Id \<longrightarrow> y \<notin> f`Q"
    proof (rule wfE_min[of "r2-Id" "f x" "f`Q"], auto)
      show "wf(r2-Id)" using \<open>Well_order r2\<close> unfolding well_order_on_def by auto
      show "f x \<in> f`Q" using \<open>x \<in> Q\<close> by auto
    qed
    define Q2 where "Q2 = Q \<inter> f-`{z'}"
    obtain z where z: "z \<in> Q2" "\<And>y. (y, z) \<in> s2 - Id \<longrightarrow> y \<notin> Q2"
    proof (rule wfE_min'[of "s2-Id" "Q2"], auto)
      show "wf(s2-Id)" using \<open>Well_order s2\<close> unfolding well_order_on_def by auto
      assume "Q2 = {}"
      then show False unfolding Q2_def using \<open>z' \<in> f`Q\<close> by blast
    qed
    have "(y, z) \<in> (s-Id) \<Longrightarrow> y \<notin> Q" for y
      unfolding s_def using z' z Q2_def by auto
    then show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> s - Id \<longrightarrow> y \<notin> Q"
      using \<open>z \<in> Q2\<close> Q2_def by auto
  qed
  ultimately have "well_order_on UNIV s" unfolding well_order_on_def by simp
  moreover have "(f x, f y) \<in> (r-Id) \<longrightarrow> (x, y) \<in> s" for x y
    unfolding s_def using \<open>r \<subseteq> r2\<close> by auto
  ultimately show ?thesis using well_order_on_Well_order by metis
qed

end (*of theory Library_Complements*)
