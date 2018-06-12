(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)

section \<open>Gromov hyperbolic spaces\<close>

theory Gromov_Hyperbolicity
  imports "HOL-Decision_Procs.Approximation" Isometries Hausdorff_Distance Metric_Completion
begin

hide_const (open) Approximation.Min
hide_const (open) Approximation.Max

subsection \<open>Definition, basic properties\<close>

text \<open>Although we will mainly work with type classes later on, we introduce the definition
of hyperbolicity on subsets of a metric space.

A set is $\delta$-hyperbolic if it satisfies the following inequality. It is very obscure at first sight,
but we will see several equivalent characterizations later on. For instance, a space is hyperbolic
(maybe for a different constant $\delta$) if all geodesic triangles are thin, i.e., every side is
close to the union of the two other sides. This definition captures the main features of negative
curvature at a large scale, and has proved extremely fruitful and influential.

Two important references on this topic are~\cite{ghys_hyperbolique} and~\cite{bridson_haefliger}.
We will sometimes follow them, sometimes depart from them.\<close>

definition Gromov_hyperbolic_subset::"real \<Rightarrow> ('a::metric_space) set \<Rightarrow> bool"
  where "Gromov_hyperbolic_subset delta A = (\<forall>x\<in>A. \<forall>y\<in>A. \<forall>z\<in>A. \<forall>t\<in>A. dist x y + dist z t \<le> max (dist x z + dist y t) (dist x t + dist y z) + 2 * delta)"

lemma Gromov_hyperbolic_subsetI [intro]:
  assumes "\<And>x y z t. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z \<in> A \<Longrightarrow> t \<in> A \<Longrightarrow> dist x y + dist z t \<le> max (dist x z + dist y t) (dist x t + dist y z) + 2 * delta"
  shows "Gromov_hyperbolic_subset delta A"
using assms unfolding Gromov_hyperbolic_subset_def by auto

text \<open>When the four points are not all distinct, the above inequality is always satisfied for
$\delta = 0$.\<close>

lemma Gromov_hyperbolic_ineq_not_distinct:
  assumes "x = y \<or> x = z \<or> x = t \<or> y = z \<or> y = t \<or> z = (t::'a::metric_space)"
  shows "dist x y + dist z t \<le> max (dist x z + dist y t) (dist x t + dist y z)"
using assms by (auto simp add: dist_commute, simp add: dist_triangle add.commute, simp add: dist_triangle3)

text \<open>It readily follows from the definition that hyperbolicity passes to the closure of the set.\<close>

lemma Gromov_hyperbolic_closure:
  assumes "Gromov_hyperbolic_subset delta A"
  shows "Gromov_hyperbolic_subset delta (closure A)"
unfolding Gromov_hyperbolic_subset_def proof (auto)
  fix x y z t assume H: "x \<in> closure A" "y \<in> closure A" "z \<in> closure A" "t \<in> closure A"
  obtain X::"nat \<Rightarrow> 'a" where X: "\<And>n. X n \<in> A" "X \<longlonglongrightarrow> x"
    using H closure_sequential by blast
  obtain Y::"nat \<Rightarrow> 'a" where Y: "\<And>n. Y n \<in> A" "Y \<longlonglongrightarrow> y"
    using H closure_sequential by blast
  obtain Z::"nat \<Rightarrow> 'a" where Z: "\<And>n. Z n \<in> A" "Z \<longlonglongrightarrow> z"
    using H closure_sequential by blast
  obtain T::"nat \<Rightarrow> 'a" where T: "\<And>n. T n \<in> A" "T \<longlonglongrightarrow> t"
    using H closure_sequential by blast
  have *: "max (dist (X n) (Z n) + dist (Y n) (T n)) (dist (X n) (T n) + dist (Y n) (Z n)) + 2 * delta - dist (X n) (Y n) - dist (Z n) (T n) \<ge> 0" for n
    using assms X(1)[of n] Y(1)[of n] Z(1)[of n] T(1)[of n] unfolding Gromov_hyperbolic_subset_def
    by (auto simp add: algebra_simps)
  have **: "(\<lambda>n. max (dist (X n) (Z n) + dist (Y n) (T n)) (dist (X n) (T n) + dist (Y n) (Z n)) + 2 * delta - dist (X n) (Y n) - dist (Z n) (T n))
    \<longlonglongrightarrow> max (dist x z + dist y t) (dist x t + dist y z) + 2 * delta - dist x y - dist z t"
    apply (auto intro!: tendsto_intros) using X Y Z T by auto
  have "max (dist x z + dist y t) (dist x t + dist y z) + 2 * delta - dist x y - dist z t \<ge> 0"
    apply (rule LIMSEQ_le_const[OF **]) using * by auto
  then show "dist x y + dist z t \<le> max (dist x z + dist y t) (dist x t + dist y z) + 2 * delta"
    by auto
qed

text \<open>A good formulation of hyperbolicity is in terms of Gromov products. Intuitively, the
Gromov product of $x$ and $y$ based at $e$ is the distance between $e$ and the geodesic between
$x$ and $y$. It is also the time after which the geodesics from $e$ to $x$ and from $e$ to $y$
stop travelling together.\<close>

definition Gromov_product_at::"('a::metric_space) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> real"
  where "Gromov_product_at e x y = (dist e x + dist e y - dist x y) / 2"

lemma Gromov_hyperbolic_subsetI2:
  fixes delta::real
  assumes "\<And>e x y z. e \<in> A \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> z \<in> A \<Longrightarrow> Gromov_product_at (e::'a::metric_space) x z \<ge> min (Gromov_product_at e x y) (Gromov_product_at e y z) - delta"
  shows "Gromov_hyperbolic_subset delta A"
proof (rule Gromov_hyperbolic_subsetI)
  fix x y z t assume H: "x \<in> A" "z \<in> A" "y \<in> A" "t \<in> A"
  show "dist x y + dist z t \<le> max (dist x z + dist y t) (dist x t + dist y z) + 2 * delta"
    using assms[OF H] unfolding Gromov_product_at_def min_def max_def
    by (auto simp add: divide_simps algebra_simps dist_commute)
qed

lemma Gromov_product_nonneg [simp, mono_intros]:
  "Gromov_product_at e x y \<ge> 0"
unfolding Gromov_product_at_def by (simp add: dist_triangle3)

lemma Gromov_product_commute:
  "Gromov_product_at e x y = Gromov_product_at e y x"
unfolding Gromov_product_at_def by (auto simp add: dist_commute)

lemma Gromov_product_le_dist [simp, mono_intros]:
  "Gromov_product_at e x y \<le> dist e x"
  "Gromov_product_at e x y \<le> dist e y"
unfolding Gromov_product_at_def by (auto simp add: diff_le_eq dist_triangle dist_triangle2)

lemma Gromov_product_le_infdist [mono_intros]:
  assumes "geodesic_segment_between G x y"
  shows "Gromov_product_at e x y \<le> infdist e G"
proof -
  have [simp]: "G \<noteq> {}" using assms by auto
  have "Gromov_product_at e x y \<le> dist e z" if "z \<in> G" for z
  proof -
    have "dist e x + dist e y \<le> (dist e z + dist z x) + (dist e z + dist z y)"
      by (intro add_mono dist_triangle)
    also have "... = 2 * dist e z + dist x y"
      apply (auto simp add: dist_commute) using \<open>z \<in> G\<close> assms by (metis dist_commute geodesic_segment_dist)
    finally show ?thesis unfolding Gromov_product_at_def by auto
  qed
  then show ?thesis
    apply (subst infdist_notempty) by (auto intro: cINF_greatest)
qed

lemma Gromov_product_add:
  "Gromov_product_at e x y + Gromov_product_at x e y = dist e x"
unfolding Gromov_product_at_def by (auto simp add: algebra_simps divide_simps dist_commute)

lemma Gromov_product_geodesic_segment:
  assumes "geodesic_segment_between G x y" "t \<in> {0..dist x y}"
  shows "Gromov_product_at x y (geodesic_segment_param G x t) = t"
proof -
  have "dist x (geodesic_segment_param G x t) = t"
    using assms(1) assms(2) geodesic_segment_param(6) by auto
  moreover have "dist y (geodesic_segment_param G x t) = dist x y - t"
    by (metis \<open>dist x (geodesic_segment_param G x t) = t\<close> add_diff_cancel_left' assms(1) assms(2) dist_commute geodesic_segment_dist geodesic_segment_param(3))
  ultimately show ?thesis unfolding Gromov_product_at_def by auto
qed

lemma Gromov_product_e_x_x [simp]:
  "Gromov_product_at e x x = dist e x"
unfolding Gromov_product_at_def by auto

lemma Gromov_product_at_diff:
  "\<bar>Gromov_product_at x y z - Gromov_product_at a b c\<bar> \<le> dist x a + dist y b + dist z c"
unfolding Gromov_product_at_def abs_le_iff apply (auto simp add: divide_simps)
by (smt dist_commute dist_triangle4)+

lemma Gromov_product_at_diff1:
  "\<bar>Gromov_product_at a x y - Gromov_product_at b x y\<bar> \<le> dist a b"
using Gromov_product_at_diff[of a x y b x y] by auto

lemma Gromov_product_at_diff2:
  "\<bar>Gromov_product_at e x z - Gromov_product_at e y z\<bar> \<le> dist x y"
using Gromov_product_at_diff[of e x z e y z] by auto

lemma Gromov_product_at_diff3:
  "\<bar>Gromov_product_at e x y - Gromov_product_at e x z\<bar> \<le> dist y z"
using Gromov_product_at_diff[of e x y e x z] by auto

text \<open>The Gromov product is continuous in its three variables. We formulate it in terms of sequences,
as it is the way it will be used below (and moreover continuity for functions of several variables
is very poor in the library).\<close>

lemma Gromov_product_at_continuous:
  assumes "(u \<longlongrightarrow> x) F" "(v \<longlongrightarrow> y) F" "(w \<longlongrightarrow> z) F"
  shows "((\<lambda>n. Gromov_product_at (u n) (v n) (w n)) \<longlongrightarrow> Gromov_product_at x y z) F"
proof -
  have "((\<lambda>n. abs(Gromov_product_at (u n) (v n) (w n) - Gromov_product_at x y z)) \<longlongrightarrow> 0 + 0 + 0) F"
    apply (rule tendsto_sandwich[of "\<lambda>n. 0" _ _ "\<lambda>n. dist (u n) x + dist (v n) y + dist (w n) z", OF always_eventually always_eventually])
    apply (simp, simp add: Gromov_product_at_diff, simp, intro tendsto_intros)
    using assms tendsto_dist_iff by auto
  then show ?thesis
    apply (subst tendsto_dist_iff) unfolding dist_real_def by auto
qed


subsection \<open>Typeclass for Gromov hyperbolic spaces\<close>

text \<open>We could (should?) just derive \verb+Gromov_hyperbolic_space+ from \verb+metric_space+.
However, in this case, properties of metric spaces are not available when working in the locale!
It is more efficient to ensure that we have a metric space by putting a type class restriction
in the definition. The $\delta$ in Gromov-hyperbolicity type class is called \verb+deltaG+ to
avoid name clashes.
\<close>

class metric_space_with_deltaG = metric_space +
  fixes deltaG::"('a::metric_space) itself \<Rightarrow> real"

class Gromov_hyperbolic_space = metric_space_with_deltaG +
  assumes hyperb_quad_ineq0: "Gromov_hyperbolic_subset (deltaG(TYPE('a::metric_space))) (UNIV::'a set)"

lemma (in Gromov_hyperbolic_space) hyperb_quad_ineq [mono_intros]:
  shows "dist x y + dist z t \<le> max (dist x z + dist y t) (dist x t + dist y z) + 2 * deltaG(TYPE('a))"
using hyperb_quad_ineq0 unfolding Gromov_hyperbolic_subset_def by auto

text \<open>It readily follows from the definition that the completion of a $\delta$-hyperbolic
space is still $\delta$-hyperbolic.\<close>

instantiation metric_completion :: (Gromov_hyperbolic_space) Gromov_hyperbolic_space
begin
definition deltaG_metric_completion::"('a metric_completion) itself \<Rightarrow> real" where
  "deltaG_metric_completion _ = deltaG(TYPE('a))"

instance proof (standard, rule Gromov_hyperbolic_subsetI)
  have "Gromov_hyperbolic_subset (deltaG(TYPE('a))) (range (to_metric_completion::'a \<Rightarrow> _))"
    unfolding Gromov_hyperbolic_subset_def
    apply (auto simp add: isometry_onD[OF to_metric_completion_isometry])
    by (metis hyperb_quad_ineq)
  then have "Gromov_hyperbolic_subset (deltaG TYPE('a metric_completion)) (UNIV::'a metric_completion set)"
    unfolding deltaG_metric_completion_def to_metric_completion_dense'[symmetric]
    using Gromov_hyperbolic_closure by auto
  then show "dist x y + dist z t \<le> max (dist x z + dist y t) (dist x t + dist y z) + 2 * deltaG TYPE('a metric_completion)"
      for x y z t::"'a metric_completion"
    unfolding Gromov_hyperbolic_subset_def by auto
qed
end (*of instantiation metric_completion (of Gromov_hyperbolic_space) is Gromov_hyperbolic*)


context Gromov_hyperbolic_space
begin

lemma delta_nonneg [simp, mono_intros]:
  "deltaG(TYPE('a)) \<ge> 0"
proof -
  obtain x::'a where True by auto
  show ?thesis using hyperb_quad_ineq[of x x x x] by auto
qed

lemma hyperb_ineq [mono_intros]:
  "Gromov_product_at (e::'a) x z \<ge> min (Gromov_product_at e x y) (Gromov_product_at e y z) - deltaG(TYPE('a))"
using hyperb_quad_ineq[of e y x z] unfolding Gromov_product_at_def min_def max_def
by (auto simp add: divide_simps algebra_simps metric_space_class.dist_commute)

lemma hyperb_ineq' [mono_intros]:
  "Gromov_product_at (e::'a) x z + deltaG(TYPE('a)) \<ge> min (Gromov_product_at e x y) (Gromov_product_at e y z)"
using hyperb_ineq[of e x y z] by auto

lemma hyperb_ineq_4_points [mono_intros]:
  "Min {Gromov_product_at (e::'a) x y, Gromov_product_at e y z, Gromov_product_at e z t} - 2 * deltaG(TYPE('a)) \<le> Gromov_product_at e x t"
using hyperb_ineq[of e x y z] hyperb_ineq[of e x z t] apply auto using delta_nonneg by linarith

lemma hyperb_ineq_4_points' [mono_intros]:
  "Min {Gromov_product_at (e::'a) x y, Gromov_product_at e y z, Gromov_product_at e z t} \<le> Gromov_product_at e x t + 2 * deltaG(TYPE('a))"
using hyperb_ineq_4_points[of e x y z t] by auto

text \<open>In Gromov-hyperbolic spaces, geodesic triangles are thin, i.e., a point on one side of a
geodesic triangle is close to the union of the two other sides (where the constant in "close"
is $4\delta$, independent of the size of the triangle). We prove this basic property
(which, in fact, is a characterization of Gromov-hyperbolic spaces: a geodesic space in which
triangles are thin is hyperbolic).\<close>

lemma thin_triangles1:
  assumes "geodesic_segment_between G x y" "geodesic_segment_between H x (z::'a)"
          "t \<in> {0..Gromov_product_at x y z}"
  shows "dist (geodesic_segment_param G x t) (geodesic_segment_param H x t) \<le> 4 * deltaG(TYPE('a))"
proof -
  have *: "Gromov_product_at x z (geodesic_segment_param H x t) = t"
    apply (rule Gromov_product_geodesic_segment[OF assms(2)]) using assms(3) Gromov_product_le_dist(2)
    by (metis atLeastatMost_subset_iff subset_iff)
  have "Gromov_product_at x y (geodesic_segment_param H x t)
        \<ge> min (Gromov_product_at x y z) (Gromov_product_at x z (geodesic_segment_param H x t)) - deltaG(TYPE('a))"
    by (rule hyperb_ineq)
  then have I: "Gromov_product_at x y (geodesic_segment_param H x t) \<ge> t - deltaG(TYPE('a))"
    using assms(3) unfolding * by auto

  have *: "Gromov_product_at x (geodesic_segment_param G x t) y = t"
    apply (subst Gromov_product_commute)
    apply (rule Gromov_product_geodesic_segment[OF assms(1)]) using assms(3) Gromov_product_le_dist(1)
    by (metis atLeastatMost_subset_iff subset_iff)
  have "t - 2 * deltaG(TYPE('a)) = min t (t- deltaG(TYPE('a))) - deltaG(TYPE('a))"
    unfolding min_def using antisym by fastforce
  also have "... \<le> min (Gromov_product_at x (geodesic_segment_param G x t) y) (Gromov_product_at x y (geodesic_segment_param H x t)) - deltaG(TYPE('a))"
    using I * by auto
  also have "... \<le> Gromov_product_at x (geodesic_segment_param G x t) (geodesic_segment_param H x t)"
    by (rule hyperb_ineq)
  finally have I: "Gromov_product_at x (geodesic_segment_param G x t) (geodesic_segment_param H x t) \<ge> t - 2 * deltaG(TYPE('a))"
    by simp

  have A: "dist x (geodesic_segment_param G x t) = t"
    by (meson assms(1) assms(3) atLeastatMost_subset_iff geodesic_segment_param(6) Gromov_product_le_dist(1) subset_eq)
  have B: "dist x (geodesic_segment_param H x t) = t"
    by (meson assms(2) assms(3) atLeastatMost_subset_iff geodesic_segment_param(6) Gromov_product_le_dist(2) subset_eq)
  show ?thesis
    using I unfolding Gromov_product_at_def A B by auto
qed

theorem thin_triangles:
  assumes "geodesic_segment_between Gxy x y"
          "geodesic_segment_between Gxz x z"
          "geodesic_segment_between Gyz y z"
          "(w::'a) \<in> Gyz"
  shows "infdist w (Gxy \<union> Gxz) \<le> 4 * deltaG(TYPE('a))"
proof -
  obtain t where w: "t \<in> {0..dist y z}" "w = geodesic_segment_param Gyz y t"
    using geodesic_segment_param[OF assms(3)] assms(4) by (metis imageE)
  show ?thesis
  proof (cases "t \<le> Gromov_product_at y x z")
    case True
    have *: "dist w (geodesic_segment_param Gxy y t) \<le> 4 * deltaG(TYPE('a))" unfolding w(2)
      apply (rule thin_triangles1[of _ _ z _ x])
      using True assms(1) assms(3) w(1) by (auto simp add: geodesic_segment_commute Gromov_product_commute)
    show ?thesis
      apply (rule infdist_le2[OF _ *])
      by (metis True assms(1) box_real(2) geodesic_segment_commute geodesic_segment_param(3) Gromov_product_le_dist(1) mem_box_real(2) order_trans subset_eq sup.cobounded1 w(1))
  next
    case False
    define s where "s = dist y z - t"
    have s: "s \<in> {0..Gromov_product_at z y x}"
      unfolding s_def using Gromov_product_add[of y z x] w(1) False by (auto simp add: Gromov_product_commute)
    have w2: "w = geodesic_segment_param Gyz z s"
      unfolding s_def w(2) apply (rule geodesic_segment_reverse_param[symmetric]) using assms(3) w(1) by auto
    have *: "dist w (geodesic_segment_param Gxz z s) \<le> 4 * deltaG(TYPE('a))" unfolding w2
      apply (rule thin_triangles1[of _ _ y _ x])
      using s assms by (auto simp add: geodesic_segment_commute)
    show ?thesis
      apply (rule infdist_le2[OF _ *])
      by (metis Un_iff assms(2) atLeastAtMost_iff geodesic_segment_commute geodesic_segment_param(3) Gromov_product_commute Gromov_product_le_dist(1) order_trans s)
  qed
qed

text \<open>A consequence of the thin triangles property is that, although the geodesic between
two points is in general not unique in a Gromov-hyperbolic space, two such geodesics are
within $O(\delta)$ of each other.\<close>

lemma geodesics_nearby:
  assumes "geodesic_segment_between G x y" "geodesic_segment_between H x y"
          "(z::'a) \<in> G"
  shows "infdist z H \<le> 4 * deltaG(TYPE('a))"
using thin_triangles[OF geodesic_segment_between_x_x(1) assms(2) assms(1) assms(3)]
geodesic_segment_endpoints(1)[OF assms(2)] insert_absorb by fastforce

text \<open>A small variant of the property of thin triangles is that triangles are slim, i.e., there is
a point which is close to the three sides of the triangle (a "center" of the triangle, but
only defined up to $O(\delta)$).\<close>

lemma slim_triangle:
  assumes "geodesic_segment_between Gxy x y"
          "geodesic_segment_between Gxz x z"
          "geodesic_segment_between Gyz y (z::'a)"
  shows "\<exists>w. infdist w Gxy \<le> 4 * deltaG(TYPE('a)) \<and>
             infdist w Gxz \<le> 4 * deltaG(TYPE('a)) \<and>
             infdist w Gyz \<le> 4 * deltaG(TYPE('a)) \<and>
             dist w x = (Gromov_product_at x y z)"
proof -
  define w where "w = geodesic_segment_param Gxy x (Gromov_product_at x y z)"
  have "w \<in> Gxy" unfolding w_def
    by (rule geodesic_segment_param(3)[OF assms(1)], auto)
  then have xy: "infdist w Gxy \<le> 4 * deltaG(TYPE('a))" by simp
  have *: "dist w x = (Gromov_product_at x y z)"
    unfolding w_def using assms(1)
    by (metis Gromov_product_le_dist(1) Gromov_product_nonneg atLeastAtMost_iff geodesic_segment_param(6) metric_space_class.dist_commute)

  define w2 where "w2 = geodesic_segment_param Gxz x (Gromov_product_at x y z)"
  have "w2 \<in> Gxz" unfolding w2_def
    by (rule geodesic_segment_param(3)[OF assms(2)], auto)
  moreover have "dist w w2 \<le> 4 * deltaG(TYPE('a))"
    unfolding w_def w2_def by (rule thin_triangles1[OF assms(1) assms(2)], auto)
  ultimately have xz: "infdist w Gxz \<le> 4 * deltaG(TYPE('a))"
    using infdist_le2 by blast

  have "w = geodesic_segment_param Gxy y (dist x y - Gromov_product_at x y z)"
    unfolding w_def by (rule geodesic_segment_reverse_param[OF assms(1), symmetric], auto)
  then have w: "w = geodesic_segment_param Gxy y (Gromov_product_at y x z)"
    using Gromov_product_add[of x y z] by (metis add_diff_cancel_left')

  define w3 where "w3 = geodesic_segment_param Gyz y (Gromov_product_at y x z)"
  have "w3 \<in> Gyz" unfolding w3_def
    by (rule geodesic_segment_param(3)[OF assms(3)], auto)
  moreover have "dist w w3 \<le> 4 * deltaG(TYPE('a))"
    unfolding w w3_def by (rule thin_triangles1[OF geodesic_segment_commute[OF assms(1)] assms(3)], auto)
  ultimately have yz: "infdist w Gyz \<le> 4 * deltaG(TYPE('a))"
    using infdist_le2 by blast

  show ?thesis using xy xz yz * by auto
qed

end (* of locale Gromov_hyperbolic_space *)

text \<open>There are converses to the above statements: if triangles are thin, or slim, then the space
is Gromov-hyperbolic, for some $\delta$. We prove these criteria here, following the proofs in
Ghys (with a simplification in the case of slim triangles.\<close>

text \<open>The basic result we will use twice below is the following: if points on sides of triangles
at the same distance of the basepoint are close to each other up to the Gromov product, then the
space is hyperbolic. The proof goes as follows. One wants to show that $(x,z)_e \geq
\min((x,y)_e, (y,z)_e) - \delta = t-\delta$. On $[ex]$, $[ey]$ and $[ez]$, consider points
$wx$, $wy$ and $wz$ at distance $t$ of $e$. Then $wx$ and $wy$ are $\delta$-close by assumption,
and so are $wy$ and $wz$. Then $wx$ and $wz$ are $2\delta$-close. One can use these two points
to express $(x,z)_e$, and the result follows readily.\<close>

lemma (in geodesic_space) controlled_thin_triangles_implies_hyperbolic:
  assumes "\<And>(x::'a) y z t Gxy Gxz. geodesic_segment_between Gxy x y \<Longrightarrow> geodesic_segment_between Gxz x z \<Longrightarrow> t \<in> {0..Gromov_product_at x y z}
      \<Longrightarrow> dist (geodesic_segment_param Gxy x t) (geodesic_segment_param Gxz x t) \<le> delta"
  shows "Gromov_hyperbolic_subset delta (UNIV::'a set)"
proof (rule Gromov_hyperbolic_subsetI2)
  fix e x y z::'a
  define t where "t = min (Gromov_product_at e x y) (Gromov_product_at e y z)"
  define wx where "wx = geodesic_segment_param {e--x} e t"
  define wy where "wy = geodesic_segment_param {e--y} e t"
  define wz where "wz = geodesic_segment_param {e--z} e t"
  have "dist wx wy \<le> delta"
    unfolding wx_def wy_def t_def by (rule assms[of _ _ x _ y], auto)
  have "dist wy wz \<le> delta"
    unfolding wy_def wz_def t_def by (rule assms[of _ _ y _ z], auto)

  have "t + dist wy x = dist e wx + dist wy x"
    unfolding wx_def apply (auto intro!: geodesic_segment_param_in_geodesic_spaces(6)[symmetric])
    unfolding t_def by (auto, meson Gromov_product_le_dist(1) min.absorb_iff2 min.left_idem order.trans)
  also have "... \<le> dist e wx + (dist wy wx + dist wx x)"
    by (intro mono_intros)
  also have "... \<le> dist e wx + (delta + dist wx x)"
    using \<open>dist wx wy \<le> delta\<close> by (auto simp add: metric_space_class.dist_commute)
  also have "... = delta + dist e x"
    apply auto apply (rule geodesic_segment_dist[of "{e--x}"])
    unfolding wx_def t_def by (auto simp add: geodesic_segment_param_in_segment)
  finally have *: "t + dist wy x - delta \<le> dist e x" by simp

  have "t + dist wy z = dist e wz + dist wy z"
    unfolding wz_def apply (auto intro!: geodesic_segment_param_in_geodesic_spaces(6)[symmetric])
    unfolding t_def by (auto, meson Gromov_product_le_dist(2) min.absorb_iff1 min.right_idem order.trans)
  also have "... \<le> dist e wz + (dist wy wz + dist wz z)"
    by (intro mono_intros)
  also have "... \<le> dist e wz + (delta + dist wz z)"
    using \<open>dist wy wz \<le> delta\<close> by (auto simp add: metric_space_class.dist_commute)
  also have "... = delta + dist e z"
    apply auto apply (rule geodesic_segment_dist[of "{e--z}"])
    unfolding wz_def t_def by (auto simp add: geodesic_segment_param_in_segment)
  finally have "t + dist wy z - delta \<le> dist e z" by simp

  then have "(t + dist wy x - delta) + (t + dist wy z - delta) \<le> dist e x + dist e z"
    using * by simp
  also have "... = dist x z + 2 * Gromov_product_at e x z"
    unfolding Gromov_product_at_def by (auto simp add: algebra_simps divide_simps)
  also have "... \<le> dist wy x + dist wy z + 2 * Gromov_product_at e x z"
    using metric_space_class.dist_triangle[of x z wy] by (auto simp add: metric_space_class.dist_commute)
  finally have "2 * t - 2 * delta \<le> 2 * Gromov_product_at e x z"
    by auto
  then show "min (Gromov_product_at e x y) (Gromov_product_at e y z) - delta \<le> Gromov_product_at e x z"
    unfolding t_def by auto
qed

text \<open>We prove that if triangles are thin, i.e., they satisfy the Rips condition, i.e., every side
of a triangle is included in the $\delta$-neighborhood of the union of the other triangles, then
the space is hyperbolic. If a point $w$ on $[xy]$ satisfies $d(x,w) < (y,z)_x - \delta$, then its
friend on $[xz] \cup [yz]$ has to be on $[xz]$, and roughly at the same distance of the origin.
Then it follows that the point on $[xz]$ with $d(x,w') = d(x,w)$ is close to $w$, as desired.
If $d(x,w) \in [(y,z)_x - \delta, (y,z)_x)$, we argue in the same way but for the point which
is closer to $x$ by an amount $\delta$. Finally, the last case $d(x,w) = (y,z)_x$ follows by
continuity.\<close>

proposition (in geodesic_space) thin_triangles_implies_hyperbolic:
  assumes "\<And>(x::'a) y z w Gxy Gyz Gxz. geodesic_segment_between Gxy x y \<Longrightarrow> geodesic_segment_between Gxz x z \<Longrightarrow> geodesic_segment_between Gyz y z
        \<Longrightarrow> w \<in> Gxy \<Longrightarrow> infdist w (Gxz \<union> Gyz) \<le> delta"
  shows "Gromov_hyperbolic_subset (4 * delta) (UNIV::'a set)"
proof -
  obtain x0::'a where True by auto
  have "infdist x0 ({x0} \<union> {x0}) \<le> delta"
    by (rule assms[of "{x0}" x0 x0 "{x0}" x0 "{x0}" x0], auto)
  then have [simp]: "delta \<ge> 0"
    using infdist_nonneg by auto

  have "dist (geodesic_segment_param Gxy x t) (geodesic_segment_param Gxz x t) \<le> 4 * delta"
    if H: "geodesic_segment_between Gxy x y" "geodesic_segment_between Gxz x z" "t \<in> {0..Gromov_product_at x y z}"
    for x y z t Gxy Gxz
  proof -
    have Main: "dist (geodesic_segment_param Gxy x u) (geodesic_segment_param Gxz x u) \<le> 4 * delta"
      if "u \<in> {delta..<Gromov_product_at x y z}" for u
    proof -
      define wy where "wy = geodesic_segment_param Gxy x (u-delta)"
      have "dist wy (geodesic_segment_param Gxy x u) = abs((u-delta) - u)"
        unfolding wy_def apply (rule geodesic_segment_param(7)[OF H(1)]) using that apply auto
        using Gromov_product_le_dist(1)[of x y z] \<open>delta \<ge> 0\<close> by linarith+
      then have I1: "dist wy (geodesic_segment_param Gxy x u) = delta" by auto

      have "infdist wy (Gxz \<union> {y--z}) \<le> delta"
        unfolding wy_def apply (rule assms[of Gxy x y _ z]) using H by (auto simp add: geodesic_segment_param_in_segment)
      moreover have "\<exists>wz \<in> Gxz \<union> {y--z}. infdist wy (Gxz \<union> {y--z}) = dist wy wz"
        apply (rule infdist_compact_attained, intro compact_Un)
        using H(2) by (auto simp add: geodesic_segment_topology(1))
      ultimately obtain wz where wz: "wz \<in> Gxz \<union> {y--z}" "dist wy wz \<le> delta"
        by force

      have "dist wz x \<le> dist wz wy + dist wy x"
        by (rule metric_space_class.dist_triangle)
      also have "... \<le> delta + (u-delta)"
        apply (intro add_mono) using wz(2) unfolding wy_def apply (auto simp add: metric_space_class.dist_commute)
        apply (intro eq_refl geodesic_segment_param(6)[OF H(1)])
        using that apply auto
        by (metis diff_0_right diff_mono dual_order.trans Gromov_product_le_dist(1) less_eq_real_def metric_space_class.dist_commute metric_space_class.zero_le_dist wy_def)
      finally have "dist wz x \<le> u" by auto
      also have "... < Gromov_product_at x y z"
        using that by auto
      also have "... \<le> infdist x {y--z}"
        by (rule Gromov_product_le_infdist, auto)
      finally have "dist x wz < infdist x {y--z}"
        by (simp add: metric_space_class.dist_commute)
      then have "wz \<notin> {y--z}"
        by (metis add.left_neutral infdist_triangle infdist_zero leD)
      then have "wz \<in> Gxz"
        using wz by auto

      have "u - delta = dist x wy"
        unfolding wy_def apply (rule geodesic_segment_param(6)[symmetric, OF H(1)])
        using that apply auto
        using Gromov_product_le_dist(1)[of x y z] \<open>delta \<ge> 0\<close> by linarith
      also have "... \<le> dist x wz + dist wz wy"
        by (rule metric_space_class.dist_triangle)
      also have "... \<le> dist x wz + delta"
        using wz(2) by (simp add: metric_space_class.dist_commute)
      finally have "dist x wz \<ge> u - 2 * delta" by auto

      define dz where "dz = dist x wz"
      have *: "wz = geodesic_segment_param Gxz x dz"
        unfolding dz_def using \<open>wz \<in> Gxz\<close> H(2) by auto
      have "dist wz (geodesic_segment_param Gxz x u) = abs(dz - u)"
        unfolding * apply (rule geodesic_segment_param(7)[OF H(2)])
        unfolding dz_def using \<open>dist wz x \<le> u\<close> that apply (auto simp add: metric_space_class.dist_commute)
        using Gromov_product_le_dist(2)[of x y z] \<open>delta \<ge> 0\<close> by linarith+
      also have "... \<le> 2 * delta"
        unfolding dz_def using \<open>dist wz x \<le> u\<close> \<open>dist x wz \<ge> u - 2 * delta\<close>
        by (auto simp add: metric_space_class.dist_commute)
      finally have I3: "dist wz (geodesic_segment_param Gxz x u) \<le> 2 * delta"
        by simp

      have "dist (geodesic_segment_param Gxy x u) (geodesic_segment_param Gxz x u)
              \<le> dist (geodesic_segment_param Gxy x u) wy + dist wy wz + dist wz (geodesic_segment_param Gxz x u)"
        by (rule dist_triangle4)
      also have "... \<le> delta + delta + (2 * delta)"
        using I1 wz(2) I3 by (auto simp add: metric_space_class.dist_commute)
      finally show ?thesis by simp
    qed
    have "t \<in> {0..dist x y}" "t \<in> {0..dist x z}" "t \<ge> 0"
      using \<open>t \<in> {0..Gromov_product_at x y z}\<close> apply auto
      using Gromov_product_le_dist[of x y z] by linarith+
    consider "t \<le> delta" | "t \<in> {delta..<Gromov_product_at x y z}" | "t = Gromov_product_at x y z \<and> t > delta"
      using \<open>t \<in> {0..Gromov_product_at x y z}\<close> by (auto, linarith)
    then show ?thesis
    proof (cases)
      case 1
      have "dist (geodesic_segment_param Gxy x t) (geodesic_segment_param Gxz x t) \<le> dist x (geodesic_segment_param Gxy x t) + dist x (geodesic_segment_param Gxz x t)"
        by (rule metric_space_class.dist_triangle3)
      also have "... = t + t"
        using geodesic_segment_param(6)[OF H(1) \<open>t \<in> {0..dist x y}\<close>] geodesic_segment_param(6)[OF H(2) \<open>t \<in> {0..dist x z}\<close>]
        by auto
      also have "... \<le> 4 * delta" using 1 \<open>delta \<ge> 0\<close> by linarith
      finally show ?thesis by simp
    next
      case 2
      show ?thesis using Main[OF 2] by simp
    next
      case 3
      text \<open>In this case, we argue by approximating $t$ by a slightly smaller parameter, for which
      the result has already been proved above. We need to argue that all functions are continuous
      on the sets we are considering, which is straightforward but tedious.\<close>
      define u::"nat \<Rightarrow> real" where "u = (\<lambda>n. t-1/n)"
      have "u \<longlonglongrightarrow> t - 0"
        unfolding u_def by (intro tendsto_intros)
      then have "u \<longlonglongrightarrow> t" by simp
      then have *: "eventually (\<lambda>n. u n > delta) sequentially"
        using 3 by (auto simp add: order_tendsto_iff)
      have **: "eventually (\<lambda>n. u n \<ge> 0) sequentially"
        apply (rule eventually_elim2[OF *, of "(\<lambda>n. delta \<ge> 0)"]) apply auto
        using \<open>delta \<ge> 0\<close> by linarith
      have ***: "u n \<le> t" for n unfolding u_def by auto
      have A: "eventually (\<lambda>n. u n \<in> {delta..<Gromov_product_at x y z}) sequentially"
        apply (auto intro!: eventually_conj)
        apply (rule eventually_mono[OF *], simp)
        unfolding u_def using 3 by auto
      have B: "eventually (\<lambda>n. dist (geodesic_segment_param Gxy x (u n)) (geodesic_segment_param Gxz x (u n)) \<le> 4 * delta) sequentially"
        by (rule eventually_mono[OF A Main], simp)
      have C: "(\<lambda>n. dist (geodesic_segment_param Gxy x (u n)) (geodesic_segment_param Gxz x (u n)))
            \<longlonglongrightarrow> dist (geodesic_segment_param Gxy x t) (geodesic_segment_param Gxz x t)"
        apply (intro tendsto_intros)
        apply (rule continuous_on_tendsto_compose[OF _ \<open>u \<longlonglongrightarrow> t\<close> \<open>t \<in> {0..dist x y}\<close>])
        apply (simp add: isometry_on_continuous H(1))
        using ** *** \<open>t \<in> {0..dist x y}\<close> apply (simp, intro eventually_conj, simp, meson dual_order.trans eventually_mono)
        apply (rule continuous_on_tendsto_compose[OF _ \<open>u \<longlonglongrightarrow> t\<close> \<open>t \<in> {0..dist x z}\<close>])
        apply (simp add: isometry_on_continuous H(2))
        using ** *** \<open>t \<in> {0..dist x z}\<close> apply (simp, intro eventually_conj, simp, meson dual_order.trans eventually_mono)
        done
      show ?thesis
        using B unfolding eventually_sequentially using LIMSEQ_le_const2[OF C] by simp
    qed
  qed
  with controlled_thin_triangles_implies_hyperbolic[OF this]
  show ?thesis by auto
qed

text \<open>Then, we prove that if triangles are slim (i.e., there is a point that is $\delta$-close to
all sides), then the space is hyperbolic. Using the previous statement, we should show that points
on $[xy]$ and $[xz]$ at the same distance $t$ of the origin are close, if $t \leq (y,z)_x$.
There are two steps:
- for $t = (y,z)_x$, then the two points are in fact close to the middle of the triangle
(as this point satisfies $d(x,y) = d(x,w) + d(w,y) + O(\delta)$, and similarly for the other sides,
one gets readily $d(x,w) = (y,z)_w + O(\delta)$ by expanding the formula for the Gromov product).
Hence, they are close together.
- For $t < (y,z)_x$, we argue that there are points $y' \in [xy]$ and $z' \in [xz]$ for which
$t = (y',z')_x$, by a continuity argument and the intermediate value theorem.
Then the result follows from the first step in the triangle $xy'z'$.

The proof we give is simpler than the one in~\cite{ghys_hyperbolique}, and gives better constants.\<close>

proposition (in geodesic_space) slim_triangles_implies_hyperbolic:
  assumes "\<And>(x::'a) y z Gxy Gyz Gxz. geodesic_segment_between Gxy x y \<Longrightarrow> geodesic_segment_between Gxz x z \<Longrightarrow> geodesic_segment_between Gyz y z
        \<Longrightarrow> \<exists>w. infdist w Gxy \<le> delta \<and> infdist w Gxz \<le> delta \<and> infdist w Gyz \<le> delta"
  shows "Gromov_hyperbolic_subset (6 * delta) (UNIV::'a set)"
proof -
  text \<open>First step: the result is true for $t = (y,z)_x$.\<close>
  have Main: "dist (geodesic_segment_param Gxy x (Gromov_product_at x y z)) (geodesic_segment_param Gxz x (Gromov_product_at x y z)) \<le> 6 * delta"
    if H: "geodesic_segment_between Gxy x y" "geodesic_segment_between Gxz x z"
    for x y z Gxy Gxz
  proof -
    obtain w where w: "infdist w Gxy \<le> delta" "infdist w Gxz \<le> delta" "infdist w {y--z} \<le> delta"
      using assms[OF H, of "{y--z}"] by auto
    have "\<exists>wxy \<in> Gxy. infdist w Gxy = dist w wxy"
      apply (rule infdist_compact_attained) using H(1) by (auto simp add: geodesic_segment_topology(1))
    then obtain wxy where wxy: "wxy \<in> Gxy" "dist w wxy \<le> delta"
      using w by auto
    have "\<exists>wxz \<in> Gxz. infdist w Gxz = dist w wxz"
      apply (rule infdist_compact_attained) using H(2) by (auto simp add: geodesic_segment_topology(1))
    then obtain wxz where wxz: "wxz \<in> Gxz" "dist w wxz \<le> delta"
      using w by auto
    have "\<exists>wyz \<in> {y--z}. infdist w {y--z} = dist w wyz"
      apply (rule infdist_compact_attained) by (auto simp add: geodesic_segment_topology(1))
    then obtain wyz where wyz: "wyz \<in> {y--z}" "dist w wyz \<le> delta"
      using w by auto

    have I: "dist wxy wxz \<le> 2 * delta" "dist wxy wyz \<le> 2 * delta" "dist wxz wyz \<le> 2 * delta"
      using metric_space_class.dist_triangle[of wxy wxz w] metric_space_class.dist_triangle[of wxy wyz w] metric_space_class.dist_triangle[of wxz wyz w]
            wxy(2) wyz(2) wxz(2) by (auto simp add: metric_space_class.dist_commute)

    text \<open>We show that $d(x, wxy)$ is close to the Gromov product of $y$ and $z$ seen from $x$.
    This follows from the fact that $w$ is essentially on all geodesics, so that everything simplifies
    when one writes down the Gromov products, leaving only $d(x, w)$ up to $O(\delta)$.
    To get the right $O(\delta)$, one has to be a little bit careful, using the triangular inequality
    when possible. This means that the computations for the upper and lower bounds are different,
    making them a little bit tedious, although straightforward.\<close>
    have "dist y wxy -4 * delta + dist wxy z \<le> dist y wxy - dist wxy wyz + dist wxy z - dist wxy wyz"
      using I by simp
    also have "... \<le> dist wyz y + dist wyz z"
      using metric_space_class.dist_triangle[of y wxy wyz] metric_space_class.dist_triangle[of wxy z wyz]
      by (auto simp add: metric_space_class.dist_commute)
    also have "... = dist y z"
      using wyz(1) by (metis geodesic_segment_dist local.some_geodesic_is_geodesic_segment(1) metric_space_class.dist_commute)
    finally have *: "dist y wxy + dist wxy z - 4 * delta \<le> dist y z" by simp
    have "2 * Gromov_product_at x y z = dist x y + dist x z - dist y z"
      unfolding Gromov_product_at_def by simp
    also have "... \<le> dist x wxy + dist wxy y + dist x wxy + dist wxy z - (dist y wxy + dist wxy z - 4 * delta)"
      using metric_space_class.dist_triangle[of x y wxy] metric_space_class.dist_triangle[of x z wxy] *
      by (auto simp add: metric_space_class.dist_commute)
    also have "... = 2 * dist x wxy + 4 * delta"
      by (auto simp add: metric_space_class.dist_commute)
    finally have A: "Gromov_product_at x y z \<le> dist x wxy + 2 * delta" by simp

    have "dist x wxy -4 * delta + dist wxy z \<le> dist x wxy - dist wxy wxz + dist wxy z - dist wxy wxz"
      using I by simp
    also have "... \<le> dist wxz x + dist wxz z"
      using metric_space_class.dist_triangle[of x wxy wxz] metric_space_class.dist_triangle[of wxy z wxz]
      by (auto simp add: metric_space_class.dist_commute)
    also have "... = dist x z"
      using wxz(1) H(2) by (metis geodesic_segment_dist metric_space_class.dist_commute)
    finally have *: "dist x wxy + dist wxy z - 4 * delta \<le> dist x z" by simp
    have "2 * dist x wxy - 4 * delta = (dist x wxy + dist wxy y) + (dist x wxy + dist wxy z - 4 * delta) - (dist y wxy + dist wxy z)"
      by (auto simp add: metric_space_class.dist_commute)
    also have "... \<le> dist x y + dist x z - dist y z"
      using * metric_space_class.dist_triangle[of y z wxy] geodesic_segment_dist[OF H(1) wxy(1)] by auto
    also have "... = 2 * Gromov_product_at x y z"
      unfolding Gromov_product_at_def by simp
    finally have B: "Gromov_product_at x y z \<ge> dist x wxy - 2 * delta" by simp

    define dy where "dy = dist x wxy"
    have *: "wxy = geodesic_segment_param Gxy x dy"
      unfolding dy_def using \<open>wxy \<in> Gxy\<close> H(1) by auto
    have "dist wxy (geodesic_segment_param Gxy x (Gromov_product_at x y z)) = abs(dy - Gromov_product_at x y z)"
      unfolding * apply (rule geodesic_segment_param(7)[OF H(1)])
      unfolding dy_def using that geodesic_segment_dist_le[OF H(1) wxy(1), of x] by (auto simp add: metric_space_class.dist_commute)
    also have "... \<le> 2 * delta"
      using A B unfolding dy_def by auto
    finally have Iy: "dist wxy (geodesic_segment_param Gxy x (Gromov_product_at x y z)) \<le> 2 * delta"
      by simp

    text \<open>We need the same estimate for $wxz$. The proof is exactly the same, copied and pasted.
    It would be better to have a separate statement, but since its assumptions would be rather
    cumbersome I decided to keep the two proofs.\<close>
    have "dist z wxz -4 * delta + dist wxz y \<le> dist z wxz - dist wxz wyz + dist wxz y - dist wxz wyz"
      using I by simp
    also have "... \<le> dist wyz z + dist wyz y"
      using metric_space_class.dist_triangle[of z wxz wyz] metric_space_class.dist_triangle[of wxz y wyz]
      by (auto simp add: metric_space_class.dist_commute)
    also have "... = dist z y"
      using \<open>dist wyz y + dist wyz z = dist y z\<close> by (auto simp add: metric_space_class.dist_commute)
    finally have *: "dist z wxz + dist wxz y - 4 * delta \<le> dist z y" by simp
    have "2 * Gromov_product_at x y z = dist x z + dist x y - dist z y"
      unfolding Gromov_product_at_def by (simp add: metric_space_class.dist_commute)
    also have "... \<le> dist x wxz + dist wxz z + dist x wxz + dist wxz y - (dist z wxz + dist wxz y - 4 * delta)"
      using metric_space_class.dist_triangle[of x z wxz] metric_space_class.dist_triangle[of x y wxz] *
      by (auto simp add: metric_space_class.dist_commute)
    also have "... = 2 * dist x wxz + 4 * delta"
      by (auto simp add: metric_space_class.dist_commute)
    finally have A: "Gromov_product_at x y z \<le> dist x wxz + 2 * delta" by simp

    have "dist x wxz -4 * delta + dist wxz y \<le> dist x wxz - dist wxz wxy + dist wxz y - dist wxz wxy"
      using I by (simp add: metric_space_class.dist_commute)
    also have "... \<le> dist wxy x + dist wxy y"
      using metric_space_class.dist_triangle[of x wxz wxy] metric_space_class.dist_triangle[of wxz y wxy]
      by (auto simp add: metric_space_class.dist_commute)
    also have "... = dist x y"
      using wxy(1) H(1) by (metis geodesic_segment_dist metric_space_class.dist_commute)
    finally have *: "dist x wxz + dist wxz y - 4 * delta \<le> dist x y" by simp
    have "2 * dist x wxz - 4 * delta = (dist x wxz + dist wxz z) + (dist x wxz + dist wxz y - 4 * delta) - (dist z wxz + dist wxz y)"
      by (auto simp add: metric_space_class.dist_commute)
    also have "... \<le> dist x z + dist x y - dist z y"
      using * metric_space_class.dist_triangle[of z y wxz] geodesic_segment_dist[OF H(2) wxz(1)] by auto
    also have "... = 2 * Gromov_product_at x y z"
      unfolding Gromov_product_at_def by (simp add: metric_space_class.dist_commute)
    finally have B: "Gromov_product_at x y z \<ge> dist x wxz - 2 * delta" by simp

    define dz where "dz = dist x wxz"
    have *: "wxz = geodesic_segment_param Gxz x dz"
      unfolding dz_def using \<open>wxz \<in> Gxz\<close> H(2) by auto
    have "dist wxz (geodesic_segment_param Gxz x (Gromov_product_at x y z)) = abs(dz - Gromov_product_at x y z)"
      unfolding * apply (rule geodesic_segment_param(7)[OF H(2)])
      unfolding dz_def using that geodesic_segment_dist_le[OF H(2) wxz(1), of x] by (auto simp add: metric_space_class.dist_commute)
    also have "... \<le> 2 * delta"
      using A B unfolding dz_def by auto
    finally have Iz: "dist wxz (geodesic_segment_param Gxz x (Gromov_product_at x y z)) \<le> 2 * delta"
      by simp

    have "dist (geodesic_segment_param Gxy x (Gromov_product_at x y z)) (geodesic_segment_param Gxz x (Gromov_product_at x y z))
      \<le> dist (geodesic_segment_param Gxy x (Gromov_product_at x y z)) wxy + dist wxy wxz + dist wxz (geodesic_segment_param Gxz x (Gromov_product_at x y z))"
      by (rule dist_triangle4)
    also have "... \<le> 2 * delta + 2 * delta + 2 * delta"
      using Iy Iz I by (auto simp add: metric_space_class.dist_commute)
    finally show ?thesis by simp
  qed

  text \<open>Second step: the result is true for $t \leq (y,z)_x$, by a continuity argument and a
  reduction to the first step.\<close>
  have "dist (geodesic_segment_param Gxy x t) (geodesic_segment_param Gxz x t) \<le> 6 * delta"
    if H: "geodesic_segment_between Gxy x y" "geodesic_segment_between Gxz x z" "t \<in> {0..Gromov_product_at x y z}"
    for x y z t Gxy Gxz
  proof -
    define ys where "ys = (\<lambda>s. geodesic_segment_param Gxy x (s * dist x y))"
    define zs where "zs = (\<lambda>s. geodesic_segment_param Gxz x (s * dist x z))"
    define F where "F = (\<lambda>s. Gromov_product_at x (ys s) (zs s))"
    have "\<exists>s. 0 \<le> s \<and> s \<le> 1 \<and> F s = t"
    proof (rule IVT')
      show "F 0 \<le> t" "t \<le> F 1"
        unfolding F_def using that unfolding ys_def zs_def by (auto simp add: Gromov_product_e_x_x)
      show "continuous_on {0..1} F"
        unfolding F_def Gromov_product_at_def ys_def zs_def
        apply (intro continuous_intros continuous_on_compose2[of "{0..dist x y}" _ _ "\<lambda>t. t * dist x y"] continuous_on_compose2[of "{0..dist x z}" _ _ "\<lambda>t. t * dist x z"])
        apply (auto intro!: isometry_on_continuous geodesic_segment_param(4) that)
        using metric_space_class.zero_le_dist mult_left_le_one_le by blast+
    qed (simp)
    then obtain s where s: "s \<in> {0..1}" "t = Gromov_product_at x (ys s) (zs s)"
      unfolding F_def by auto

    have a: "x = geodesic_segment_param Gxy x 0" using H(1) by auto
    have b: "x = geodesic_segment_param Gxz x 0" using H(2) by auto
    have dy: "dist x (ys s) = s * dist x y"
      unfolding ys_def apply (rule geodesic_segment_param[OF H(1)]) using s(1) by (auto simp add: mult_left_le_one_le)
    have dz: "dist x (zs s) = s * dist x z"
      unfolding zs_def apply (rule geodesic_segment_param[OF H(2)]) using s(1) by (auto simp add: mult_left_le_one_le)

    define Gxy2 where "Gxy2 = geodesic_subsegment Gxy x 0 (s * dist x y)"
    define Gxz2 where "Gxz2 = geodesic_subsegment Gxz x 0 (s * dist x z)"

    have "dist (geodesic_segment_param Gxy2 x t) (geodesic_segment_param Gxz2 x t) \<le> 6 * delta"
    unfolding s(2) proof (rule Main)
      show "geodesic_segment_between Gxy2 x (ys s)"
        apply (subst a) unfolding Gxy2_def ys_def apply (rule geodesic_subsegment[OF H(1)])
        using s(1) by (auto simp add: mult_left_le_one_le)
      show "geodesic_segment_between Gxz2 x (zs s)"
        apply (subst b) unfolding Gxz2_def zs_def apply (rule geodesic_subsegment[OF H(2)])
        using s(1) by (auto simp add: mult_left_le_one_le)
    qed
    moreover have "geodesic_segment_param Gxy2 x (t-0) = geodesic_segment_param Gxy x t"
      apply (subst a) unfolding Gxy2_def apply (rule geodesic_subsegment(3)[OF H(1)])
      using s(1) H(3) unfolding s(2) apply (auto simp add: mult_left_le_one_le)
      unfolding dy[symmetric] by (rule Gromov_product_le_dist)
    moreover have "geodesic_segment_param Gxz2 x (t-0) = geodesic_segment_param Gxz x t"
      apply (subst b) unfolding Gxz2_def apply (rule geodesic_subsegment(3)[OF H(2)])
      using s(1) H(3) unfolding s(2) apply (auto simp add: mult_left_le_one_le)
      unfolding dz[symmetric] by (rule Gromov_product_le_dist)
    ultimately show ?thesis by simp
  qed
  with controlled_thin_triangles_implies_hyperbolic[OF this]
  show ?thesis by auto
qed


subsection \<open>Morse Lemma\<close>

text \<open>A central feature of hyperbolic spaces is that a path from $x$ to $y$ can not deviate
too much from a geodesic from $x$ to $y$ unless it is extremely long (exponentially long in
terms of the distance from $x$ to $y$). This is useful both to ensure that short paths (for instance
quasi-geodesics) stay close to geodesics, see the Morse lemme below, and to ensure that paths
that avoid a given large ball of radius $R$ have to be exponentially long in terms of $R$ (this
is extremely useful for random walks). This proposition is the first non-trivial result
on hyperbolic spaces in~\cite{bridson_haefliger} (Proposition III.H.1.6). We follow their proof.

The proof is geometric, and uses the existence of geodesics and the fact that geodesic
triangles are thin. In fact, the result still holds if the space is not geodesic, as
it can be deduced by embedding the hyperbolic space in a geodesic hyperbolic space and using
the result there.\<close>

class Gromov_hyperbolic_space_geodesic = Gromov_hyperbolic_space + geodesic_space

proposition (in Gromov_hyperbolic_space_geodesic) lipschitz_path_close_to_geodesic:
  fixes c::"real \<Rightarrow> 'a"
  assumes "M-lipschitz_on {A..B} c"
          "geodesic_segment_between G (c A) (c B)"
          "x \<in> G"
  shows "infdist x (c`{A..B}) \<le> (4/ln 2) * deltaG(TYPE('a)) * max 0 (ln (B-A)) + M"
proof -
  have "M \<ge> 0" by (rule lipschitz_on_nonneg[OF assms(1)])
  have Main: "a \<in> {A..B} \<Longrightarrow> b \<in> {A..B} \<Longrightarrow> a \<le> b \<Longrightarrow> b-a \<le> 2^(n+1) \<Longrightarrow> geodesic_segment_between H (c a) (c b)
        \<Longrightarrow> y \<in> H \<Longrightarrow> infdist y (c`{A..B}) \<le> 4 * deltaG(TYPE('a)) * n + M" for a b H y n
  proof (induction n arbitrary: a b H y)
    case 0
    have "infdist y (c ` {A..B}) \<le> dist y (c b)"
      apply (rule infdist_le) using \<open>b \<in> {A..B}\<close> by auto
    moreover have "infdist y (c ` {A..B}) \<le> dist y (c a)"
      apply (rule infdist_le) using \<open>a \<in> {A..B}\<close> by auto
    ultimately have "2 * infdist y (c ` {A..B}) \<le> dist (c a) y + dist y (c b)"
      by (auto simp add: metric_space_class.dist_commute)
    also have "... = dist (c a) (c b)"
      by (rule geodesic_segment_dist[OF \<open>geodesic_segment_between H (c a) (c b)\<close> \<open>y \<in> H\<close>])
    also have "... \<le> M * abs(b - a)"
      using lipschitz_onD(1)[OF assms(1) \<open>a \<in> {A..B}\<close> \<open>b \<in> {A..B}\<close>] unfolding dist_real_def
      by (simp add: abs_minus_commute)
    also have "... \<le> M * 2"
      using \<open>a \<le> b\<close> \<open>b - a \<le> 2^(0 + 1)\<close> \<open>M \<ge> 0\<close> mult_left_mono by auto
    finally show ?case by simp
  next
    case (Suc n)
    define m where "m = (a + b)/2"
    have "m \<in> {A..B}" using \<open>a \<in> {A..B}\<close> \<open>b \<in> {A..B}\<close> unfolding m_def by auto
    define Ha where "Ha = {c m--c a}"
    define Hb where "Hb = {c m--c b}"
    have I: "geodesic_segment_between Ha (c m) (c a)" "geodesic_segment_between Hb (c m) (c b)"
      unfolding Ha_def Hb_def by auto
    then have "Ha \<noteq> {}" "Hb \<noteq> {}" "compact Ha" "compact Hb"
      by (auto intro: geodesic_segment_topology)

    have *: "infdist y (Ha \<union> Hb) \<le> 4 * deltaG(TYPE('a))"
      by (rule thin_triangles[OF I \<open>geodesic_segment_between H (c a) (c b)\<close> \<open>y \<in> H\<close>])
    then have "infdist y Ha \<le> 4 * deltaG(TYPE('a)) \<or> infdist y Hb \<le> 4 * deltaG(TYPE('a))"
      unfolding infdist_union_min[OF \<open>Ha \<noteq> {}\<close> \<open>Hb \<noteq> {}\<close>] by auto
    then show ?case
    proof
      assume H: "infdist y Ha \<le> 4 * deltaG TYPE('a)"
      obtain z where z: "z \<in> Ha" "infdist y Ha = dist y z"
        using infdist_compact_attained[OF \<open>compact Ha\<close> \<open>Ha \<noteq> {}\<close>] by auto
      have Iz: "infdist z (c`{A..B}) \<le> 4 * deltaG(TYPE('a)) * n + M"
      proof (rule Suc.IH[OF \<open>a \<in> {A..B}\<close> \<open>m \<in> {A..B}\<close>, of Ha])
        show "a \<le> m" unfolding m_def using \<open>a \<le> b\<close> by auto
        show "m - a \<le> 2^(n+1)" using \<open>b - a \<le> 2^(Suc n + 1)\<close> \<open>a \<le> b\<close> unfolding m_def by auto
        show "geodesic_segment_between Ha (c a) (c m)" by (simp add: I(1) geodesic_segment_commute)
        show "z \<in> Ha" using z by auto
      qed
      have "infdist y (c`{A..B}) \<le> dist y z + infdist z (c`{A..B})"
        by (metis add.commute infdist_triangle)
      also have "... \<le> 4 * deltaG TYPE('a) + (4 * deltaG(TYPE('a)) * n + M)"
        using H z Iz by (auto intro: add_mono)
      finally show "infdist y (c ` {A..B}) \<le> 4 * deltaG TYPE('a) * real (Suc n) + M"
        by (auto simp add: algebra_simps)
    next
      assume H: "infdist y Hb \<le> 4 * deltaG TYPE('a)"
      obtain z where z: "z \<in> Hb" "infdist y Hb = dist y z"
        using infdist_compact_attained[OF \<open>compact Hb\<close> \<open>Hb \<noteq> {}\<close>] by auto
      have Iz: "infdist z (c`{A..B}) \<le> 4 * deltaG(TYPE('a)) * n + M"
      proof (rule Suc.IH[OF \<open>m \<in> {A..B}\<close> \<open>b \<in> {A..B}\<close>, of Hb])
        show "m \<le> b" unfolding m_def using \<open>a \<le> b\<close> by auto
        show "b - m \<le> 2^(n+1)" using \<open>b - a \<le> 2^(Suc n + 1)\<close> \<open>a \<le> b\<close>
          unfolding m_def by (auto simp add: divide_simps)
        show "geodesic_segment_between Hb (c m) (c b)" by (simp add: I(2))
        show "z \<in> Hb" using z by auto
      qed
      have "infdist y (c`{A..B}) \<le> dist y z + infdist z (c`{A..B})"
        by (metis add.commute infdist_triangle)
      also have "... \<le> 4 * deltaG TYPE('a) + (4 * deltaG(TYPE('a)) * n + M)"
        using H z Iz by (auto intro: add_mono)
      finally show "infdist y (c ` {A..B}) \<le> 4 * deltaG TYPE('a) * real (Suc n) + M"
        by (auto simp add: algebra_simps)
    qed
  qed
  consider "B-A <0" | "B-A \<ge> 0 \<and> B-A \<le> 2" | "B-A > 2" by linarith
  then show ?thesis
  proof (cases)
    case 1
    then have "c`{A..B} = {}" by auto
    then show ?thesis unfolding infdist_def using \<open>M \<ge> 0\<close> by auto
  next
    case 2
    have "infdist x (c`{A..B}) \<le> 4 * deltaG(TYPE('a)) * real 0 + M"
      apply (rule Main[OF _ _ _ _ \<open>geodesic_segment_between G (c A) (c B)\<close> \<open>x \<in> G\<close>])
      using 2 by auto
    also have "... \<le> (4/ln 2) * deltaG(TYPE('a)) * max 0 (ln (B-A)) + M"
      using delta_nonneg by auto
    finally show ?thesis by auto
  next
    case 3
    define n::nat where "n = nat(floor (log 2 (B-A)))"
    have "log 2 (B-A) > 0" using 3 by auto
    then have n: "n \<le> log 2 (B-A)" "log 2 (B-A) < n+1"
      unfolding n_def by (auto simp add: floor_less_cancel)
    then have *: "B-A \<le> 2^(n+1)"
      by (meson le_log_of_power linear not_less one_less_numeral_iff semiring_norm(76))
    have "n \<le> ln (B-A) * (1/ln 2)" using n unfolding log_def by auto
    then have "n \<le> (1/ln 2) * max 0 (ln (B-A))"
      using 3 by (auto simp add: algebra_simps divide_simps)
    have "infdist x (c`{A..B}) \<le> 4 * deltaG(TYPE('a)) * n + M"
      apply (rule Main[OF _ _ _ _ \<open>geodesic_segment_between G (c A) (c B)\<close> \<open>x \<in> G\<close>])
      using * 3 by auto
    also have "... \<le> 4 * deltaG(TYPE('a)) * ((1/ln 2) * max 0 (ln (B-A))) + M"
      apply (intro mono_intros) using \<open>n \<le> (1/ln 2) * max 0 (ln (B-A))\<close> delta_nonneg by auto
    finally show ?thesis by auto
  qed
qed

text \<open>By rescaling coordinates at the origin, one obtains a variation around the previous
statement.\<close>

proposition (in Gromov_hyperbolic_space_geodesic) lipschitz_path_close_to_geodesic':
  fixes c::"real \<Rightarrow> 'a"
  assumes "M-lipschitz_on {A..B} c"
          "geodesic_segment_between G (c A) (c B)"
          "x \<in> G"
          "a > 0"
  shows "infdist x (c`{A..B}) \<le> (4/ln 2) * deltaG(TYPE('a)) * max 0 (ln (a * (B-A))) + M/a"
proof -
  define d where "d = c o (\<lambda>t. (1/a) * t)"
  have *: "(M * ((1/a)* 1))-lipschitz_on {a * A..a * B} d"
    unfolding d_def apply (rule lipschitz_on_compose, intro lipschitz_intros) using assms by auto
  have "d`{a * A..a * B} = c`{A..B}"
    unfolding d_def image_comp[symmetric]
    apply (rule arg_cong[where ?f = "image c"]) using \<open>a > 0\<close> by auto
  then have "infdist x (c`{A..B}) = infdist x (d`{a * A..a * B})" by auto
  also have "... \<le> (4/ln 2) * deltaG(TYPE('a)) * max 0 (ln ((a * B)- (a * A))) + M/a"
    apply (rule lipschitz_path_close_to_geodesic[OF _ _ \<open>x \<in> G\<close>])
    using * assms unfolding d_def by auto
  finally show ?thesis by (auto simp add: algebra_simps)
qed

text \<open>The next theorem is often called simply the Morse Lemma, but it is really
a theorem, and we add the name Gromov the avoid the confusion with the other Morse lemma
on the existence of good coordinates for $C^2$ functions with non-vanishing hessian.

It states that a quasi-geodesic remains within bounded distance of a geodesic with the same
endpoints, the error depending only on $\delta$ and on the parameters $(\lambda, C)$ of the
quasi-geodesic, but not on its length.

Contrary to usual practice, we try to get an explicit constant for the upper bound,
although we do not try to get something particularly good. What the proof really
gives is a bound of the form $K \lambda^2 (C + \delta \ln (\lambda (1+C)))$ for some explicit
constant $K$. However, for convenience of use, we bound this from above by
$K'\lambda^2 (C+\lambda+\delta^2)$ for some $K'$ -- we get $K' = 81$.

We follow the proof in~\cite{bridson_haefliger}.\<close>

theorem (in Gromov_hyperbolic_space_geodesic) Morse_Gromov_theorem:
  fixes c::"real \<Rightarrow> 'a"
  assumes "lambda C-quasi_isometry_on {A..B} c"
  shows "hausdorff_distance (c`{A..B}) {c A--c B} \<le> 81 * lambda^2 * (C + lambda + deltaG(TYPE('a))^2)"
proof -
  have C: "C \<ge> 0" "lambda \<ge> 1" using quasi_isometry_onD[OF assms] by auto
  consider "B-A < 0" | "B-A \<ge> 0 \<and> dist (c A) (c B) \<le> 2 * C" | "B-A \<ge> 0 \<and> dist (c A) (c B) > 2 * C" by linarith
  then show ?thesis
  proof (cases)
    case 1
    then have "c`{A..B} = {}" by auto
    then show ?thesis unfolding hausdorff_distance_def using delta_nonneg C by auto
  next
    case 2
    have "(1/lambda) * dist A B - C \<le> dist (c A) (c B)"
      apply (rule quasi_isometry_onD[OF assms]) using 2 by auto
    also have "... \<le> 2 * C" using 2 by auto
    finally have "dist A B \<le> 3 * lambda * C"
      using C by (auto simp add: algebra_simps divide_simps)
    then have *: "B - A \<le> 3 * lambda * C" using 2 unfolding dist_real_def by auto
    show ?thesis
    proof (rule hausdorff_distanceI2)
      show "0 \<le> 81 * lambda^2 * (C + lambda + deltaG(TYPE('a))^2)" using C by auto
      fix x assume "x \<in> c`{A..B}"
      then obtain t where t: "x = c t" "t \<in> {A..B}" by auto
      have "dist x (c A) \<le> lambda * dist t A + C"
        unfolding t(1) using quasi_isometry_onD(1)[OF assms t(2), of A] 2 by auto
      also have "... \<le>lambda * (B-A) + C" using t(2) 2 C unfolding dist_real_def by auto
      also have "... \<le> 3 * lambda * lambda * C + 1 * 1 * C" using * C by auto
      also have "... \<le> 3 * lambda * lambda * C + lambda * lambda * C"
        apply (intro mono_intros) using C by auto
      also have "... = 4 * lambda * lambda * (C + 0 + 0^2)"
        by auto
      also have "... \<le> 81 * lambda * lambda * (C + lambda + deltaG(TYPE('a))^2)"
        apply (intro mono_intros) using C delta_nonneg by auto
      finally have *: "dist x (c A) \<le> 81 * lambda^2 * (C + lambda + deltaG(TYPE('a))^2)"
        unfolding power2_eq_square by simp
      show "\<exists>y\<in>{c A--c B}. dist x y \<le> 81 * lambda^2 * (C + lambda + deltaG(TYPE('a))^2)"
        apply (rule bexI[of _ "c A"]) using * by auto
    next
      fix x assume "x \<in> {c A-- c B}"
      then have "dist x (c A) \<le> dist (c A) (c B)"
        by (meson geodesic_segment_dist_le geodesic_segment_endpoints(1) local.some_geodesic_is_geodesic_segment(1))
      also have "... \<le> 2 * C"
        using 2 by auto
      also have "... \<le> 2 * 1 * 1 * (C + lambda + 0)" using 2 C unfolding dist_real_def by auto
      also have "... \<le> 81 * lambda * lambda * (C + lambda + deltaG(TYPE('a)) * deltaG(TYPE('a)))"
        apply (intro mono_intros) using C delta_nonneg by auto
      finally have *: "dist x (c A) \<le> 81 * lambda * lambda * (C + lambda + deltaG(TYPE('a)) * deltaG(TYPE('a)))"
        by simp
      show "\<exists>y\<in>c`{A..B}. dist x y \<le> 81 * lambda^2 * (C + lambda + deltaG(TYPE('a))^2)"
        apply (rule bexI[of _ "c A"]) unfolding power2_eq_square using * 2 by auto
    qed
  next
    case 3
    then obtain d where d: "continuous_on {A..B} d" "d A = c A" "d B = c B"
              "\<And>x. x \<in> {A..B} \<Longrightarrow> dist (c x) (d x) \<le> 5*C"
              "lambda (10 * C)-quasi_isometry_on {A..B} d"
              "(9 * lambda)-lipschitz_on {A..B} d"
      using quasi_geodesic_made_lipschitz[OF assms] by auto
    have "hausdorff_distance (c`{A..B}) (d`{A..B}) \<le> 5*C"
      apply (rule hausdorff_distance_vimage) using d C by auto

    have "A \<in> {A..B}" "B \<in> {A..B}" using 3 by auto

    text \<open>We show that the distance of any point in the geodesic from $c(A)$ to $c(B)$ is a bounded
    distance away from the quasi-geodesic $d$, by considering a point $x$ where the distance $D$ is
    maximal and arguing around this point.

    Consider the point $x_m$ on the geodesic $[c(A), c(B)]$ at distance $2D$ from $x$, and the closest
    point $y_m$ on the image of $d$. Then the distance between $x_m$ and $y_m$ is at most $D$. Hence
    a point on $[x_m,y_m]$ is at distance at least $2D - D = D$ of $x$. In the same way, define $x_M$
    and $y_M$ on the other side of $x$. Then the excursion from $x_m$ to $y_m$, then to $y_M$ along
    $d$, then to $x_M$, has length at most $D + (\lambda \cdot 6D + C) + D$ and is always at distance
    at least $D$ from $x$. It follows from the previous lemma that $D \leq \log(length)$, which
    implies a bound on $D$.

    This argument has to be amended if $x$ is at distance $<2D$ from $c(A)$ or $c(B)$. In this case,
    simply use $x_m = y_m = c(A)$ or $x_M = y_M = c(B)$, then everything goes through.\<close>

    have "\<exists>x \<in> {c A--c B}. \<forall>y \<in> {c A--c B}. infdist y (d`{A..B}) \<le> infdist x (d`{A..B})"
      by (rule continuous_attains_sup, auto intro: continuous_intros)
    then obtain x where x: "x \<in> {c A--c B}" "\<And>y. y \<in> {c A--c B} \<Longrightarrow> infdist y (d`{A..B}) \<le> infdist x (d`{A..B})"
      by auto
    define D where "D = infdist x (d`{A..B})"
    have "D \<ge> 0" unfolding D_def by (rule infdist_nonneg)
    have D_bound: "D \<le> 27 * lambda + 14 * C + 27 * deltaG(TYPE('a))^2"
    proof (cases "D \<le> 1")
      case True
      have "1 * 1 + 1 * 0 + 0 * 0 \<le> 27 * lambda + 14 * C + 27 * deltaG(TYPE('a))^2"
        apply (intro mono_intros) using C delta_nonneg by auto
      then show ?thesis using True by auto
    next
      case False
      then have "D \<ge> 1" by auto
      have ln2mult: "2 * ln t = ln (t * t)" if "t > 0" for t::real by (simp add: that ln_mult)
      have "infdist (c A) (d`{A..B}) = 0" using \<open>d A = c A\<close> by (metis \<open>A \<in> {A..B}\<close> image_eqI infdist_zero)
      then have "x \<noteq> c A" using \<open>D \<ge> 1\<close> D_def by auto

      define tx where "tx = dist (c A) x"
      then have "tx \<in> {0..dist (c A) (c B)}"
        using \<open>x \<in> {c A--c B}\<close>
        by (meson atLeastAtMost_iff geodesic_segment_dist_le some_geodesic_is_geodesic_segment(1) metric_space_class.zero_le_dist some_geodesic_endpoints(1))
      have "tx > 0" using \<open>x \<noteq> c A\<close> tx_def by auto
      have x_param: "x = geodesic_segment_param {c A--c B} (c A) tx"
        using \<open>x \<in> {c A--c B}\<close> geodesic_segment_param[OF some_geodesic_is_geodesic_segment(1)] tx_def by auto

      define tm where "tm = max (tx - 2 * D) 0"
      have "tm \<in> {0..dist (c A) (c B)}" unfolding tm_def using \<open>tx \<in> {0..dist (c A) (c B)}\<close> \<open>D \<ge> 0\<close> by auto
      define xm where "xm = geodesic_segment_param {c A--c B} (c A) tm"
      have "xm \<in> {c A--c B}" using \<open>tm \<in> {0..dist (c A) (c B)}\<close>
        by (metis geodesic_segment_param(3) local.some_geodesic_is_geodesic_segment(1) xm_def)
      have "dist xm x = abs((max (tx - 2 * D) 0) - tx)"
        unfolding xm_def tm_def x_param apply (rule geodesic_segment_param[of _ _ "c B"], auto)
        using \<open>tx \<in> {0..dist (c A) (c B)}\<close> \<open>D \<ge> 0\<close> by auto
      also have "... \<le> 2 * D" by (simp add: \<open>0 \<le> D\<close> tx_def)
      finally have "dist xm x \<le> 2 * D" by auto
      have "\<exists>ym\<in>d`{A..B}. infdist xm (d`{A..B}) = dist xm ym"
        apply (rule infdist_compact_attained) using 3 d(1) compact_continuous_image by auto
      then obtain ym where ym: "ym \<in> d`{A..B}" "dist xm ym = infdist xm (d`{A..B})"
        by metis
      then obtain um where um: "um \<in> {A..B}" "ym = d um" by auto
      have "dist xm ym \<le> D"
        unfolding D_def using x ym by (simp add: \<open>xm \<in> {c A--c B}\<close>)
      have D1: "dist x z \<ge> D" if "z \<in> {xm--ym}" for z
      proof (cases "tx - 2 * D < 0")
        case True
        then have "tm = 0" unfolding tm_def by auto
        then have "xm = c A" unfolding xm_def
          by (meson geodesic_segment_param(1) local.some_geodesic_is_geodesic_segment(1))
        then have "infdist xm (d`{A..B}) = 0"
          using \<open>d A = c A\<close> \<open>A \<in> {A..B}\<close> by (metis image_eqI infdist_zero)
        then have "ym = xm" using ym(2) by auto
        then have "z = xm" using \<open>z \<in> {xm--ym}\<close> geodesic_segment_between_x_x(3)
          by (metis empty_iff insert_iff some_geodesic_is_geodesic_segment(1))
        then have "z \<in> d`{A..B}" using \<open>ym = xm\<close> ym(1) by blast
        then show "dist x z \<ge> D" unfolding D_def by (simp add: infdist_le)
      next
        case False
        then have *: "tm = tx - 2 * D" unfolding tm_def by auto
        have "dist xm x = abs((tx - 2 * D) - tx)"
          unfolding xm_def x_param * apply (rule geodesic_segment_param[of _ _ "c B"], auto)
          using False \<open>tx \<in> {0..dist (c A) (c B)}\<close> \<open>D \<ge> 0\<close> by auto
        then have "2 * D = dist xm x" using \<open>D \<ge> 0\<close> by auto
        also have "... \<le> dist xm z + dist x z" using metric_space_class.dist_triangle2 by auto
        also have "... \<le> dist xm ym + dist x z"
          using \<open>z \<in> {xm--ym}\<close> by (auto, meson geodesic_segment_dist_le some_geodesic_is_geodesic_segment(1) some_geodesic_endpoints(1))
        also have "... \<le> D + dist x z"
          using \<open>dist xm ym \<le> D\<close> by simp
        finally show "dist x z \<ge> D" by auto
      qed

      define tM where "tM = min (tx + 2 * D) (dist (c A) (c B))"
      have "tM \<in> {0..dist (c A) (c B)}" unfolding tM_def using \<open>tx \<in> {0..dist (c A) (c B)}\<close> \<open>D \<ge> 0\<close> by auto
      have "tm \<le> tM"
        unfolding tM_def using \<open>D \<ge> 0\<close> \<open>tm \<in> {0..dist (c A) (c B)}\<close> \<open>tx \<equiv> dist (c A) x\<close> tm_def by auto
      define xM where "xM = geodesic_segment_param {c A--c B} (c A) tM"
      have "xM \<in> {c A--c B}" using \<open>tM \<in> {0..dist (c A) (c B)}\<close>
        by (metis geodesic_segment_param(3) local.some_geodesic_is_geodesic_segment(1) xM_def)
      have "dist xM x = abs((min (tx + 2 * D) (dist (c A) (c B))) - tx)"
        unfolding xM_def tM_def x_param apply (rule geodesic_segment_param[of _ _ "c B"], auto)
        using \<open>tx \<in> {0..dist (c A) (c B)}\<close> \<open>D \<ge> 0\<close> by auto
      also have "... \<le> 2 * D" using \<open>0 \<le> D\<close> \<open>tx \<in> {0..dist (c A) (c B)}\<close> by auto
      finally have "dist xM x \<le> 2 * D" by auto
      have "\<exists>yM\<in>d`{A..B}. infdist xM (d`{A..B}) = dist xM yM"
        apply (rule infdist_compact_attained) using 3 d(1) compact_continuous_image by auto
      then obtain yM where yM: "yM \<in> d`{A..B}" "dist xM yM = infdist xM (d`{A..B})"
        by metis
      then obtain uM where uM: "uM \<in> {A..B}" "yM = d uM" by auto
      have "dist xM yM \<le> D"
        unfolding D_def using x yM by (simp add: \<open>xM \<in> {c A--c B}\<close>)
      have D3: "dist x z \<ge> D" if "z \<in> {xM--yM}" for z
      proof (cases "tx + 2 * D > dist (c A) (c B)")
        case True
        then have "tM = dist (c A) (c B)" unfolding tM_def by auto
        then have "xM = c B" unfolding xM_def
          by (meson geodesic_segment_param(2) local.some_geodesic_is_geodesic_segment(1))
        then have "infdist xM (d`{A..B}) = 0"
          using \<open>d B = c B\<close> \<open>B \<in> {A..B}\<close> by (metis image_eqI infdist_zero)
        then have "yM = xM" using yM(2) by auto
        then have "z = xM" using \<open>z \<in> {xM--yM}\<close> geodesic_segment_between_x_x(3)
          by (metis empty_iff insert_iff some_geodesic_is_geodesic_segment(1))
        then have "z \<in> d`{A..B}" using \<open>yM = xM\<close> yM(1) by blast
        then show "dist x z \<ge> D" unfolding D_def by (simp add: infdist_le)
      next
        case False
        then have *: "tM = tx + 2 * D" unfolding tM_def by auto
        have "dist xM x = abs((tx + 2 * D) - tx)"
          unfolding xM_def x_param * apply (rule geodesic_segment_param[of _ _ "c B"], auto)
          using False \<open>tx \<in> {0..dist (c A) (c B)}\<close> \<open>D \<ge> 0\<close> by auto
        then have "2 * D = dist xM x" using \<open>D \<ge> 0\<close> by auto
        also have "... \<le> dist xM z + dist x z" using metric_space_class.dist_triangle2 by auto
        also have "... \<le> dist xM yM + dist x z"
          using \<open>z \<in> {xM--yM}\<close> by (auto, meson geodesic_segment_dist_le local.some_geodesic_is_geodesic_segment(1) some_geodesic_endpoints(1))
        also have "... \<le> D + dist x z"
          using \<open>dist xM yM \<le> D\<close> by simp
        finally show "dist x z \<ge> D" by auto
      qed

      define excursion:: "real\<Rightarrow>'a" where "excursion = (\<lambda>t.
        if t \<in> {0..dist xm ym} then (geodesic_segment_param {xm--ym} xm t)
        else if t \<in> {dist xm ym..dist xm ym + abs(uM - um)} then d (um + sgn(uM-um) * (t - dist xm ym))
        else geodesic_segment_param {yM--xM} yM (t - dist xm ym - abs (uM -um)))"
      define L where "L = dist xm ym + abs(uM - um) + dist yM xM"
      have E1: "excursion t = geodesic_segment_param {xm--ym} xm t" if "t \<in> {0..dist xm ym}" for t
        unfolding excursion_def using that by auto
      have E2: "excursion t = d (um + sgn(uM-um) * (t - dist xm ym))" if "t \<in> {dist xm ym..dist xm ym + abs(uM - um)}" for t
        unfolding excursion_def using that by (auto simp add: \<open>ym = d um\<close>)
      have E3: "excursion t = geodesic_segment_param {yM--xM} yM (t - dist xm ym - abs (uM -um))"
        if "t \<in> {dist xm ym + \<bar>uM - um\<bar>..dist xm ym + \<bar>uM - um\<bar> + dist yM xM}" for t
        unfolding excursion_def using that \<open>yM = d uM\<close> \<open>ym = d um\<close> by (auto simp add: sgn_mult_abs)
      have E0: "excursion 0 = xm"
        unfolding excursion_def by auto
      have EL: "excursion L = xM"
        unfolding excursion_def L_def apply (auto simp add: uM(2) um(2) sgn_mult_abs)
        by (metis (mono_tags, hide_lams) add.left_neutral add_increasing2 add_le_same_cancel1 dist_real_def
              Gromov_product_e_x_x Gromov_product_nonneg metric_space_class.dist_le_zero_iff)
      have [simp]: "L \<ge> 0" unfolding L_def by auto
      have "L > 0"
      proof (rule ccontr)
        assume "\<not>(L>0)"
        then have "L = 0" using \<open>L \<ge> 0\<close> by simp
        then have "xm = xM" using E0 EL by auto
        then have "tM = tm" unfolding xm_def xM_def
          using \<open>tM \<in> {0..dist (c A) (c B)}\<close> \<open>tm \<in> {0..dist (c A) (c B)}\<close> local.geodesic_segment_param_in_geodesic_spaces(6) by fastforce
        also have "... < tx" unfolding tm_def using \<open>tx > 0\<close> \<open>D \<ge> 1\<close> by auto
        also have "... \<le> tM" unfolding tM_def using \<open>D \<ge> 0\<close> \<open>tx \<in> {0..dist (c A) (c B)}\<close> by auto
        finally show False by simp
      qed

      have "(1/lambda) * dist um uM - (10 * C) \<le> dist (d um) (d uM)"
        by (rule quasi_isometry_onD(2)[OF \<open>lambda (10 * C)-quasi_isometry_on {A..B} d\<close> \<open>um \<in> {A..B}\<close> \<open>uM \<in> {A..B}\<close>])
      also have "... \<le> dist ym xm + dist xm x + dist x xM + dist xM yM"
        unfolding um(2)[symmetric] uM(2)[symmetric] by (rule dist_triangle5)
      also have "... \<le> D + (2*D) + (2*D) + D"
        using \<open>dist xm ym \<le> D\<close> \<open>dist xm x \<le> 2*D\<close> \<open>dist xM x \<le> 2*D\<close> \<open>dist xM yM \<le> D\<close>
        by (auto simp add: metric_space_class.dist_commute intro: add_mono)
      finally have "(1/lambda) * dist um uM \<le> 6*D + 10*C" by auto
      then have "dist um uM \<le> 6*D*lambda + 10*C*lambda"
        using C by (auto simp add: divide_simps algebra_simps)
      then have "L \<le> D + (6*D*lambda + 10*C*lambda) + D"
        unfolding L_def dist_real_def using \<open>dist xm ym \<le> D\<close> \<open>dist xM yM \<le> D\<close>
        by (auto simp add: metric_space_class.dist_commute intro: add_mono)
      also have "... \<le> 8 * D * lambda + 10*C*lambda"
        using C \<open>D \<ge> 0\<close> by (auto intro: mono_intros)
      finally have L_bound: "L \<le> lambda * (8 * D + 10 * C)"
        by (auto simp add: algebra_simps)

      have "1 * (1 * 1 + 0) \<le> lambda * (8 * D + 10 * C)"
        using C \<open>D \<ge> 1\<close> by (intro mono_intros, auto)

      consider "um < uM" | "um = uM" | "um > uM" by linarith
      then have "((\<lambda>t. um + sgn (uM - um) * (t - dist xm ym)) ` {dist xm ym..dist xm ym + \<bar>uM - um\<bar>}) \<subseteq> {min um uM..max um uM}"
        by (cases, auto)
      also have "... \<subseteq> {A..B}" using \<open>um \<in> {A..B}\<close> \<open>uM \<in> {A..B}\<close> by auto
      finally have middle: "((\<lambda>t. um + sgn (uM - um) * (t - dist xm ym)) ` {dist xm ym..dist xm ym + \<bar>uM - um\<bar>}) \<subseteq> {A..B}"
        by simp

      have "(9 * lambda)-lipschitz_on {0..L} excursion"
      proof (unfold L_def, rule lipschitz_on_closed_Union[of "{{0..dist xm ym}, {dist xm ym..dist xm ym + abs(uM - um)}, {dist xm ym + abs(uM - um)..dist xm ym + abs(uM - um) + dist yM xM}}" _ "\<lambda> i. i"], auto)
        show "lambda \<ge> 0" using C by auto

        have *: "1-lipschitz_on {0..dist xm ym} (geodesic_segment_param {xm--ym} xm)"
          by (rule isometry_on_lipschitz, simp)
        have **: "1-lipschitz_on {0..dist xm ym} excursion"
          using lipschitz_on_transform[OF * E1] by simp
        show "(9 * lambda)-lipschitz_on {0..dist xm ym} excursion"
          apply (rule lipschitz_on_mono[OF **]) using C by auto

        have *: "(1*(1+0))-lipschitz_on {dist xm ym + \<bar>uM - um\<bar>..dist xm ym + \<bar>uM - um\<bar> + dist yM xM}
                ((geodesic_segment_param {yM--xM} yM) o (\<lambda>t. t - (dist xm ym + abs (uM -um))))"
          by (intro lipschitz_intros, rule isometry_on_lipschitz, auto)
        have **: "(1*(1+0))-lipschitz_on {dist xm ym + \<bar>uM - um\<bar>..dist xm ym + \<bar>uM - um\<bar> + dist yM xM} excursion"
          apply (rule lipschitz_on_transform[OF *]) using E3 unfolding comp_def by (auto simp add: algebra_simps)
        show "(9 * lambda)-lipschitz_on {dist xm ym + \<bar>uM - um\<bar>..dist xm ym + \<bar>uM - um\<bar> + dist yM xM} excursion"
          apply (rule lipschitz_on_mono[OF **]) using C by auto

        have **: "((9 * lambda) * (0 + abs(sgn (uM - um)) * (1 + 0)))-lipschitz_on {dist xm ym..dist xm ym + abs(uM - um)} (d o (\<lambda>t. um + sgn(uM-um) * (t - dist xm ym)))"
          apply (intro lipschitz_intros, rule lipschitz_on_subset[OF _ middle])
          using \<open>(9 * lambda)-lipschitz_on {A..B} d\<close> by simp
        have ***: "(9 * lambda)-lipschitz_on {dist xm ym..dist xm ym + abs(uM - um)} (d o (\<lambda>t. um + sgn(uM-um) * (t - dist xm ym)))"
          apply (rule lipschitz_on_mono[OF **]) using C by auto
        show "(9 * lambda)-lipschitz_on {dist xm ym..dist xm ym + abs(uM - um)} excursion"
          apply (rule lipschitz_on_transform[OF ***]) using E2 by auto
      qed

      have *: "dist x z \<ge> D" if z: "z \<in> excursion`{0..L}" for z
      proof -
        obtain tz where tz: "z = excursion tz" "tz \<in> {0..dist xm ym + abs(uM - um) + dist yM xM}"
          using z L_def by auto
        consider "tz \<in> {0..dist xm ym}" | "tz \<in> {dist xm ym<..dist xm ym + abs(uM - um)}" | "tz \<in> {dist xm ym + abs(uM - um)<..dist xm ym + abs(uM - um) + dist yM xM}"
          using tz by force
        then show ?thesis
        proof (cases)
          case 1
          then have "z \<in> {xm--ym}" unfolding tz(1) excursion_def by auto
          then show ?thesis using D1 by auto
        next
          case 3
          then have "z \<in> {yM--xM}" unfolding tz(1) excursion_def using tz(2) by auto
          then show ?thesis using D3 by (simp add: some_geodesic_commute)
        next
          case 2
          then have "z \<in> d`{A..B}" unfolding tz(1) excursion_def using middle by force
          then show ?thesis unfolding D_def by (simp add: infdist_le)
        qed
      qed

      text \<open>Now comes the main point: the excursion is always at distance at least $D$ of $x$,
      but this distance is also bounded by the log of its length, i.e., essentially $\log D$. To
      have an efficient estimate, we use a rescaled version, to get rid of one term on the right
      hand side.\<close>
      have "1 * 1 * 1 * (1 + 0/1) \<le> 720 * lambda * lambda * (1+C/D)"
        apply (intro mono_intros) using \<open>lambda \<ge> 1\<close> \<open>D \<ge> 1\<close> \<open>C \<ge> 0\<close> by auto
      then have "ln (720 * lambda * lambda * (1+C/D)) \<ge> 0"
        apply (subst ln_ge_zero_iff) by auto
      define a where "a = 72 * lambda/D"
      have "a > 0" unfolding a_def using \<open>D \<ge> 1\<close> \<open>lambda \<ge> 1\<close> by auto

      have "D \<le> infdist x (excursion`{0..L})"
        unfolding infdist_def apply auto apply (rule cInf_greatest) using * by auto
      also have "... \<le> (4/ln 2) * deltaG(TYPE('a)) * max 0 (ln (a * (L-0))) + (9 * lambda) / a"
      proof (rule lipschitz_path_close_to_geodesic'[of _ _ _ _ "geodesic_subsegment {c A--c B} (c A) tm tM"])
        show "(9 * lambda)-lipschitz_on {0..L} excursion" by fact
        have *: "geodesic_subsegment {c A--c B} (c A) tm tM = geodesic_segment_param {c A--c B} (c A) ` {tm..tM} "
          apply (rule geodesic_subsegment(1)[of _ _ "c B"])
          using \<open>tm \<in> {0..dist (c A) (c B)}\<close> \<open>tM \<in> {0..dist (c A) (c B)}\<close> \<open>tm \<le> tM\<close> by auto
        show "x \<in> geodesic_subsegment {c A--c B} (c A) tm tM"
          unfolding * unfolding x_param tm_def tM_def using \<open>tx \<in> {0..dist (c A) (c B)}\<close> \<open>0 \<le> D\<close> by simp
        show "geodesic_segment_between (geodesic_subsegment {c A--c B} (c A) tm tM) (excursion 0) (excursion L)"
          unfolding E0 EL xm_def xM_def apply (rule geodesic_subsegment[of _ _ "c B"])
          using \<open>tm \<in> {0..dist (c A) (c B)}\<close> \<open>tM \<in> {0..dist (c A) (c B)}\<close> \<open>tm \<le> tM\<close> by auto
      qed (fact)
      also have "... = (4/ln 2) * deltaG(TYPE('a)) * max 0 (ln (a *L)) + D/8"
        unfolding a_def using \<open>D \<ge> 1\<close> \<open>lambda \<ge> 1\<close> by (simp add: algebra_simps)
      finally have "(7 * ln 2 / 32) * D \<le> deltaG(TYPE('a)) * max 0 (ln (a * L))"
        by (auto simp add: algebra_simps divide_simps)
      also have "... \<le> deltaG(TYPE('a)) * max 0 (ln ((72 * lambda/D) * (lambda * (8 * D + 10 * C))))"
        unfolding a_def apply (intro mono_intros)
        using L_bound \<open>L > 0\<close> \<open>lambda \<ge> 1\<close> \<open>D \<ge> 1\<close> by auto
      also have "... \<le> deltaG(TYPE('a)) * max 0 (ln ((72 * lambda/D) * (lambda * (10 * D + 10 * C))))"
        apply (intro mono_intros)
        using L_bound \<open>L > 0\<close> \<open>lambda \<ge> 1\<close> \<open>D \<ge> 1\<close> by auto
      also have "... = deltaG(TYPE('a)) * max 0 (ln (720 * lambda * lambda * (1+C/D)))"
        using \<open>D \<ge> 1\<close> by (auto simp add: algebra_simps)
      also have "... = deltaG(TYPE('a)) * ln (720 * lambda * lambda * (1+C/D))"
        using \<open>ln (720 * lambda * lambda * (1+C/D)) \<ge> 0\<close> by auto
      also have "... \<le> deltaG(TYPE('a)) * ln (720 * lambda * lambda * (1+C/1))"
        apply (intro mono_intros) using \<open>lambda \<ge> 1\<close> \<open>C \<ge> 0\<close> \<open>D \<ge> 1\<close>
        by (auto simp add: divide_simps mult_ge1_mono(1))
      text \<open>We have obtained a bound on $D$, of the form $D \leq M \delta \ln(M \lambda^2(1+C))$.
      This is a nice bound, but we tweak it a little bit to obtain something more manageable,
      without the logarithm.\<close>
      also have "... = deltaG(TYPE('a)) * (ln 720 + 2 * ln lambda + ln (1+C))"
        apply (subst ln2mult) using \<open>C \<ge> 0\<close> \<open>lambda \<ge> 1\<close> apply simp
        apply (subst ln_mult[symmetric]) apply simp using \<open>C \<ge> 0\<close> \<open>lambda \<ge> 1\<close> apply simp
        apply (subst ln_mult[symmetric]) using \<open>C \<ge> 0\<close> \<open>lambda \<ge> 1\<close> by auto
      also have "... = (deltaG(TYPE('a)) * 1) * ln 720 + 2 * (deltaG(TYPE('a)) * ln lambda) + (deltaG(TYPE('a)) * ln (1+C))"
        by (auto simp add: algebra_simps)
      text \<open>For each term, of the form $\delta \ln c$, we bound it by $(\delta^2 + (\ln c)^2)/2$, and
      then bound $(\ln c)^2$ by $2c-2$. In fact, to get coefficients of the same order of
      magnitude on $\delta^2$ and $\lambda$, we tweak a little bit the inequality for the last two
      terms, using rather $uv \leq (u^2/2 + 2v^2)/2$. We also bound $\ln(720)$ by a good
      approximation $20/3$.\<close>
      also have "... \<le> (deltaG(TYPE('a))^2/2 + 1^2/2) * (20/3)
            + 2 * ((1/2) * deltaG(TYPE('a))^2/2 + 2 * (ln lambda)^2 / 2) + ((1/2) * deltaG(TYPE('a))^2/2 + 2 * (ln (1+C))^2 / 2)"
        by (intro mono_intros, auto, approximation 7)
      also have "... = (49/12) * deltaG(TYPE('a))^2 + 10/3 + 2 * (ln lambda)^2 + (ln (1+C))^2"
        by (auto simp add: algebra_simps)
      also have "... \<le> (49/12) * deltaG(TYPE('a))^2 + 10/3 + 2 * (2 * lambda - 2) + (2 * (1+C) - 2)"
        apply (intro mono_intros) using \<open>C \<ge> 0\<close> \<open>lambda \<ge> 1\<close> by auto
      also have "... \<le> 49/12 * deltaG(TYPE('a))^2 + 4 * lambda + 2 * C"
        by auto
      finally have "D \<le> (32/ (7 * ln 2)) * (49/12 * deltaG(TYPE('a))^2 + 4 * lambda + 2 * C)"
        by (auto simp add: divide_simps)
      also have "... \<le> (12 * 27/49) * (49/12 * deltaG(TYPE('a))^2 + 4 * lambda + 2 * C)"
        apply (intro mono_intros, approximation 10) using \<open>lambda \<ge> 1\<close> \<open>C \<ge> 0\<close> by auto
      also have "... \<le> 27 * deltaG(TYPE('a))^2 + 27 * lambda + 14 * C"
        using \<open>lambda \<ge> 1\<close> \<open>C \<ge> 0\<close> by auto
      finally show ?thesis by simp
    qed
    define D0 where "D0 = 27 * lambda + 14 * C + 27 * deltaG(TYPE('a))^2"
    have first_step: "infdist y (d`{A..B}) \<le> D0" if "y \<in> {c A--c B}" for y
      using x(2)[OF that] D_bound unfolding D0_def D_def by auto
    have "1 * 1 + 4 * 0 + 27 * 0 \<le> D0"
      unfolding D0_def apply (intro mono_intros) using C delta_nonneg by auto
    then have "D0 > 0" by simp
    text \<open>This is the end of the first step, i.e., showing that $[c(A), c(B)]$ is included in
    the neighborhood of size $D0$ of the quasi-geodesic.\<close>

    text \<open>Now, we start the second step: we show that the quasi-geodesic is included in the
    neighborhood of size $D1$ of the geodesic, where $D1 \geq D0$ is the constant defined below.
    The argument goes as follows. Assume that a point $y$ on the quasi-geodesic is at distance $>D0$
    of the geodesic. Consider the last point $y_m$ before $y$ which is at distance $D0$ of the
    geodesic, and the first point $y_M$ after $y$ likewise. On $(y_m, y_M)$, one is always at distance
    $>D0$ of the geodesic. However, by the first step, the geodesic is covered by the balls of radius
    $D0$ centered at points on the quasi-geodesic -- and only the points before $y_m$ or after $y_M$
    can be used. Let $K_m$ be the points on the geodesics that are at distance $\leq D0$ of a point
    on the quasi-geodesic before $y_m$, and likewise define $K_M$. These are two closed subsets of
    the geodesic. By connectedness, they have to intersect. This implies that some points before $y_m$
    and after $y_M$ are at distance at most $2D0$. Since we are dealing with a quasi-geodesic, this
    gives a bound on the distance between $y_m$ and $y_M$, and therefore a bound between $y$ and the
    geodesic, as desired.\<close>

    define D1 where "D1 = lambda * lambda * (81 * lambda + 62 * C + 81 * deltaG(TYPE('a))^2)"
    have "1 * 1 * (27 * lambda + 14 * C + 27 * deltaG(TYPE('a))^2)
            \<le> lambda * lambda * (81 * lambda + 62 * C + 81 * deltaG(TYPE('a))^2)"
      apply (intro mono_intros) using C by auto
    then have "D0 \<le> D1" unfolding D0_def D1_def by auto
    have second_step: "infdist y {c A--c B} \<le> D1" if "y \<in> d`{A..B}" for y
    proof (cases "infdist y {c A--c B} \<le> D0")
      case True
      then show ?thesis using \<open>D0 \<le> D1\<close> by auto
    next
      case False
      obtain ty where "ty \<in> {A..B}" "y = d ty" using \<open>y \<in> d`{A..B}\<close> by auto

      define tm where "tm = Sup ((\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {A..ty})"
      have tm: "tm \<in> (\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {A..ty}"
      unfolding tm_def proof (rule closed_contains_Sup)
        show "closed ((\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {A..ty})"
          apply (rule closed_vimage_Int, auto, intro continuous_intros)
          apply (rule continuous_on_subset[OF d(1)]) using \<open>ty \<in> {A..B}\<close> by auto
        have "A \<in> (\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {A..ty}"
          using \<open>D0 > 0\<close> \<open>ty \<in> {A..B}\<close> by (auto simp add: \<open>d A = c A\<close>)
        then show "(\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {A..ty} \<noteq> {}" by auto
        show "bdd_above ((\<lambda>t. infdist (d t) {c A--c B}) -` {..D0} \<inter> {A..ty})" by auto
      qed
      have *: "infdist (d t) {c A--c B} > D0" if "t \<in> {tm<..ty}" for t
      proof (rule ccontr)
        assume "\<not>(infdist (d t) {c A--c B} > D0)"
        then have *: "t \<in> (\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {A..ty}"
          using that tm by auto
        have "t \<le> tm" unfolding tm_def apply (rule cSup_upper) using * by auto
        then show False using that by auto
      qed

      define tM where "tM = Inf ((\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {ty..B})"
      have tM: "tM \<in> (\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {ty..B}"
      unfolding tM_def proof (rule closed_contains_Inf)
        show "closed ((\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {ty..B})"
          apply (rule closed_vimage_Int, auto, intro continuous_intros)
          apply (rule continuous_on_subset[OF d(1)]) using \<open>ty \<in> {A..B}\<close> by auto
        have "B \<in> (\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {ty..B}"
          using \<open>D0 > 0\<close> \<open>ty \<in> {A..B}\<close> by (auto simp add: \<open>d B = c B\<close>)
        then show "(\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {ty..B} \<noteq> {}" by auto
        show "bdd_below ((\<lambda>t. infdist (d t) {c A--c B}) -` {..D0} \<inter> {ty..B})" by auto
      qed
      have "infdist (d t) {c A--c B} > D0" if "t \<in> {ty..<tM}" for t
      proof (rule ccontr)
        assume "\<not>(infdist (d t) {c A--c B} > D0)"
        then have *: "t \<in> (\<lambda>t. infdist (d t) {c A--c B})-`{..D0} \<inter> {ty..B}"
          using that tM by auto
        have "t \<ge> tM" unfolding tM_def apply (rule cInf_lower) using * by auto
        then show False using that by auto
      qed
      then have lower_tm_tM: "infdist (d t) {c A--c B} > D0" if "t \<in> {tm<..<tM}" for t
        using * that by (cases "t \<ge> ty", auto)

      define Km where "Km = (\<Union>z \<in> d`{A..tm}. cball z D0)"
      define KM where "KM = (\<Union>z \<in> d`{tM..B}. cball z D0)"
      have "{c A--c B} \<subseteq> Km \<union> KM"
      proof
        fix x assume "x \<in> {c A--c B}"
        have "\<exists>z \<in> d`{A..B}. infdist x (d`{A..B}) = dist x z"
          apply (rule infdist_compact_attained, rule compact_continuous_image[OF \<open>continuous_on {A..B} d\<close>])
          using that by auto
        then obtain tx where "tx \<in> {A..B}" "infdist x (d`{A..B}) = dist x (d tx)" by blast
        then have "dist x (d tx) \<le> D0"
          using first_step[OF \<open>x \<in> {c A--c B}\<close>] by auto
        then have "x \<in> cball (d tx) D0" by (auto simp add: metric_space_class.dist_commute)
        consider "tx \<in> {A..tm}" | "tx \<in> {tm<..<tM}" | "tx \<in> {tM..B}"
          using \<open>tx \<in> {A..B}\<close> by fastforce
        then show "x \<in> Km \<union> KM"
        proof (cases)
          case 1
          then have "x \<in> Km" unfolding Km_def using \<open>x \<in> cball (d tx) D0\<close> by auto
          then show ?thesis by simp
        next
          case 3
          then have "x \<in> KM" unfolding KM_def using \<open>x \<in> cball (d tx) D0\<close> by auto
          then show ?thesis by simp
        next
          case 2
          have "infdist (d tx) {c A--c B} \<le> dist (d tx) x" using \<open>x \<in> {c A--c B}\<close> by (rule infdist_le)
          also have "... \<le> D0" using \<open>x \<in> cball (d tx) D0\<close> by auto
          finally have False using lower_tm_tM[OF 2] by simp
          then show ?thesis by simp
        qed
      qed
      then have *: "{c A--c B} = (Km \<inter> {c A--c B}) \<union> (KM \<inter> {c A--c B})" by auto
      have "(Km \<inter> {c A--c B}) \<inter> (KM \<inter> {c A--c B}) \<noteq> {}"
      proof (rule connected_as_closed_union[OF _ *])
        have "closed Km"
          unfolding Km_def apply (rule compact_has_closed_thickening)
          apply (rule compact_continuous_image)
          apply (rule continuous_on_subset[OF \<open>continuous_on {A..B} d\<close>])
          using tm \<open>ty \<in> {A..B}\<close> by auto
        then show "closed (Km \<inter> {c A--c B})" by (rule topological_space_class.closed_Int, auto)

        have "closed KM"
          unfolding KM_def apply (rule compact_has_closed_thickening)
          apply (rule compact_continuous_image)
          apply (rule continuous_on_subset[OF \<open>continuous_on {A..B} d\<close>])
          using tM \<open>ty \<in> {A..B}\<close> by auto
        then show "closed (KM \<inter> {c A--c B})" by (rule topological_space_class.closed_Int, auto)

        show "connected {c A--c B}" by simp
        have "c A \<in> Km \<inter> {c A--c B}" apply auto
          unfolding Km_def using tm \<open>d A = c A\<close> \<open>D0 > 0\<close> by (auto) (rule bexI[of _ A], auto)
        then show "Km \<inter> {c A--c B} \<noteq> {}" by auto
        have "c B \<in> KM \<inter> {c A--c B}" apply auto
          unfolding KM_def using tM \<open>d B = c B\<close> \<open>D0 > 0\<close> by (auto) (rule bexI[of _ B], auto)
        then show "KM \<inter> {c A--c B} \<noteq> {}" by auto
      qed
      then obtain w where "w \<in> {c A--c B}" "w \<in> Km" "w \<in> KM" by auto
      then obtain twm twM where tw: "twm \<in> {A..tm}" "w \<in> cball (d twm) D0" "twM \<in> {tM..B}" "w \<in> cball (d twM) D0"
        unfolding Km_def KM_def by auto
      have "(1/lambda) * dist twm twM - (10*C) \<le> dist (d twm) (d twM)"
        apply (rule quasi_isometry_onD(2)[OF d(5)]) using tw tm tM by auto
      also have "... \<le> dist (d twm) w + dist w (d twM)"
        by (rule metric_space_class.dist_triangle)
      also have "... \<le> 2 * D0" using tw by (auto simp add: metric_space_class.dist_commute)
      finally have "dist twm twM \<le> lambda * (10*C + 2*D0)"
        using C by (auto simp add: divide_simps algebra_simps)
      then have *: "dist twm ty \<le> lambda * (10*C + 2*D0)"
        using tw tm tM dist_real_def by auto

      have "dist (d ty) w \<le> dist (d ty) (d twm) + dist (d twm) w"
        by (rule metric_space_class.dist_triangle)
      also have "... \<le> (lambda * dist ty twm + (10*C)) + D0"
        apply (intro add_mono, rule quasi_isometry_onD(1)[OF d(5)]) using tw tm tM by auto
      also have "... \<le> (lambda * (lambda * (10*C + 2*D0))) + (10*C) + D0"
        apply (intro mono_intros) using C * by (auto simp add: metric_space_class.dist_commute)
      also have "... = lambda * lambda * (10*C + 2*D0) + 1 * 1 * (10 * C) + 1 * 1 * D0"
        by simp
      also have "... \<le> lambda * lambda * (10*C + 2*D0) + lambda * lambda * (10 * C) + lambda * lambda * D0"
        apply (intro mono_intros) using C * \<open>D0 > 0\<close> by auto
      also have "... = lambda * lambda * (20 * C + 3 * D0)"
        by (auto simp add: algebra_simps)
      also have "... = lambda * lambda * (62 * C + 81 * lambda + 81 * deltaG(TYPE('a))^2)"
        unfolding D0_def by auto
      finally have "dist y w \<le> D1" unfolding D1_def \<open>y = d ty\<close> by (auto simp add: algebra_simps)
      then show "infdist y {c A--c B} \<le> D1" using infdist_le[OF \<open>w \<in> {c A--c B}\<close>, of y] by auto
    qed
    text \<open>This concludes the second step.\<close>

    text \<open>Putting the two steps together, we deduce that the Hausdorff distance between the
    geodesic and the quasi-geodesic is bounded by $D1$. A bound between the geodesic and
    the original (untamed) quasi-geodesic follows.\<close>

    have a: "hausdorff_distance (d`{A..B}) {c A--c B} \<le> D1"
    proof (rule hausdorff_distanceI)
      show "D1 \<ge> 0" unfolding D1_def using C delta_nonneg by auto
      fix x assume "x \<in> d ` {A..B}"
      then show "infdist x {c A--c B} \<le> D1" using second_step by auto
    next
      fix x assume "x \<in> {c A--c B}"
      then show "infdist x (d`{A..B}) \<le> D1" using first_step \<open>D0 \<le> D1\<close> by force
    qed
    have b: "hausdorff_distance (c`{A..B}) (d`{A..B}) \<le> 5 * C"
      apply (rule hausdorff_distance_vimage) using d(4) C by auto

    have "hausdorff_distance (c`{A..B}) {c A--c B} \<le>
        hausdorff_distance (c`{A..B}) (d`{A..B}) + hausdorff_distance (d`{A..B}) {c A--c B}"
      apply (rule hausdorff_distance_triangle)
      using \<open>A \<in> {A..B}\<close> apply blast
      by (rule quasi_isometry_on_bounded[OF d(5)], auto)
    also have "... \<le> D1 + 5*C" using a b by auto
    also have "... = lambda * lambda * (81 * lambda + 62 * C + 81 * deltaG(TYPE('a))^2) + 1 * 1 * (5 * C)"
      unfolding D1_def by auto
    also have "... \<le> lambda * lambda * (81 * lambda + 62 * C + 81 * deltaG(TYPE('a))^2)
                      + lambda * lambda * (19 * C)"
      apply (intro mono_intros) using C delta_nonneg by auto
    also have "... = 81 * lambda^2 * (lambda + C + deltaG(TYPE('a))^2)"
      by (auto simp add: algebra_simps power2_eq_square)
    finally show ?thesis by (auto simp add: algebra_simps)
  qed
qed

theorem (in Gromov_hyperbolic_space_geodesic) Morse_Gromov_theorem2:
  fixes c d::"real \<Rightarrow> 'a"
  assumes "lambda C-quasi_isometry_on {A..B} c"
          "lambda C-quasi_isometry_on {A..B} d"
          "c A = d A" "c B = d B"
  shows "hausdorff_distance (c`{A..B}) (d`{A..B}) \<le> 162 * lambda^2 * (C + lambda + deltaG(TYPE('a))^2)"
proof (cases "A \<le> B")
  case False
  then have "hausdorff_distance (c`{A..B}) (d`{A..B}) = 0" by auto
  then show ?thesis using quasi_isometry_onD[OF assms(1)] delta_nonneg by auto
next
  case True
  have "hausdorff_distance (c`{A..B}) {c A--c B} \<le> 81 * lambda^2 * (C + lambda + deltaG(TYPE('a))^2)"
    by (rule Morse_Gromov_theorem[OF assms(1)])
  moreover have "hausdorff_distance {c A--c B} (d`{A..B}) \<le> 81 * lambda^2 * (C + lambda + deltaG(TYPE('a))^2)"
    unfolding \<open>c A = d A\<close> \<open>c B = d B\<close> apply (subst hausdorff_distance_sym)
    by (rule Morse_Gromov_theorem[OF assms(2)])
  moreover have "hausdorff_distance (c`{A..B}) (d`{A..B}) \<le> hausdorff_distance (c`{A..B}) {c A--c B} + hausdorff_distance {c A--c B} (d`{A..B})"
    apply (rule hausdorff_distance_triangle)
    using True compact_imp_bounded[OF some_geodesic_compact] by auto
  ultimately show ?thesis by auto
qed

text \<open>We deduce from the Morse lemma that hyperbolicity is invariant under quasi-isometry.\<close>

text \<open>First, we note that the image of a geodesic segment under a quasi-isometry is close to
a geodesic segment in Hausdorff distance, as it is a quasi-geodesic.\<close>

lemma geodesic_quasi_isometric_image:
  fixes f::"'a::metric_space \<Rightarrow> 'b::Gromov_hyperbolic_space_geodesic"
  assumes "lambda C-quasi_isometry_on UNIV f"
          "geodesic_segment_between G x y"
  shows "hausdorff_distance (f`G) {f x--f y} \<le> 81 * lambda^2 * (C + lambda + deltaG(TYPE('b))^2)"
proof -
  define c where "c = f o (geodesic_segment_param G x)"
  have *: "(1 * lambda) (0 * lambda + C)-quasi_isometry_on {0..dist x y} c"
    unfolding c_def by (rule quasi_isometry_on_compose[where Y = UNIV], auto intro!: isometry_quasi_isometry_on simp add: assms)
  have "hausdorff_distance (c`{0..dist x y}) {c 0--c (dist x y)} \<le> 81 * lambda^2 * (C + lambda + deltaG(TYPE('b))^2)"
    apply (rule Morse_Gromov_theorem) using * by auto
  moreover have "c`{0..dist x y} = f`G"
    unfolding c_def image_comp[symmetric] using assms(2) by auto
  moreover have "c 0 = f x" "c (dist x y) = f y"
    unfolding c_def using assms(2) by auto
  ultimately show ?thesis by auto
qed

text \<open>We deduce that hyperbolicity is invariant under quasi-isometry. The proof goes as follows:
we want to see that a geodesic triangle is delta-thin, i.e., a point on a side $Gxy$ is close to the
union of the two other sides $Gxz$ and $Gyz$. Pull everything back by the quasi-isometry: we obtain
three quasi-geodesic, each of which is close to the corresponding geodesic segment by the Morse lemma.
As the geodesic triangle is thin, it follows that the quasi-geodesic triangle is also thin, i.e.,
a point on $f^{-1}Gxy$ is close to $f^{-1}Gxz \cup f^{-1}Gyz$ (for some explicit, albeit large,
constant). Then push everything forward by $f$: as it is a quasi-isometry, it will again distort
distances by a bounded amount.\<close>

lemma Gromov_hyperbolic_invariant_under_quasi_isometry_explicit:
  fixes f::"'a::geodesic_space \<Rightarrow> 'b::Gromov_hyperbolic_space_geodesic"
  assumes "lambda C-quasi_isometry f"
  shows "Gromov_hyperbolic_subset (656 * lambda^3 * (lambda + C + deltaG(TYPE('b))^2)) (UNIV::('a set))"
proof -
  have C: "lambda \<ge> 1" "C \<ge> 0"
    using quasi_isometry_onD[OF assms] by auto

  text \<open>The Morse lemma gives a control bounded by $K$ below. Following the proof, we deduce
  a bound on the thinness of triangles by an ugly constant $L$. We bound it by a more tractable
  (albeit still ugly) constant $M$.\<close>
  define K where "K = 81 * lambda^2 * (C + lambda + deltaG(TYPE('b))^2)"
  have HD: "hausdorff_distance (f`G) {f a--f b} \<le> K" if "geodesic_segment_between G a b" for G a b
    unfolding K_def by (rule geodesic_quasi_isometric_image[OF assms that])
  define L where "L = lambda * (4 * (deltaG(TYPE('b)) * 1) + 2 * K) + C * lambda * 1"
  define M where "M = 164 * lambda^3 * (lambda + C + deltaG(TYPE('b))^2)"

  have "L \<le> lambda * (4 * 1 * (deltaG(TYPE('b))^2/2 + 1^2/2) + 2 * K) + C * lambda * lambda^2"
    unfolding L_def apply (intro mono_intros) using C by auto
  also have "... \<le> lambda * (4 * lambda^2 * (deltaG(TYPE('b))^2/2 + lambda/2) + 2 * K) + C * lambda * lambda^2"
    apply (intro mono_intros) using C by auto
  also have "... = lambda^3 * (163 * C + 164 * lambda + 164 * deltaG(TYPE('b))^2)"
    by (simp add: K_def algebra_simps divide_simps power2_eq_square power3_eq_cube)
  also have "... \<le> M"
    unfolding M_def using C by (auto simp add: algebra_simps)
  finally have "L \<le> M" by simp

  text \<open>After these preliminaries, we start the real argument per se, showing that triangles
  are thin in the type b.\<close>
  have Thin: "infdist w (Gxz \<union> Gyz) \<le> M" if
    H: "geodesic_segment_between Gxy x y" "geodesic_segment_between Gxz x z" "geodesic_segment_between Gyz y z" "w \<in> Gxy"
    for w x y z::'a and Gxy Gyz Gxz
  proof -
    obtain w2 where w2: "w2 \<in> {f x--f y}" "infdist (f w) {f x--f y} = dist (f w) w2"
      using infdist_compact_attained[of "{f x--f y}" "f w"] by auto
    have "dist (f w) w2 = infdist (f w) {f x-- f y}"
      using w2 by simp
    also have "... \<le> hausdorff_distance (f`Gxy) {f x-- f y}"
      using geodesic_segment_topology(4)[OF geodesic_segmentI] H
      by (auto intro!: quasi_isometry_on_bounded[OF quasi_isometry_on_subset[OF assms]] infdist_le_hausdorff_distance)
    also have "... \<le> K" using HD[OF H(1)] by simp
    finally have *: "dist (f w) w2 \<le> K" by simp

    have "infdist w2 (f`Gxz \<union> f`Gyz) \<le> infdist w2 ({f x--f z} \<union> {f y--f z})
                + hausdorff_distance ({f x--f z} \<union> {f y--f z}) (f`Gxz \<union> f`Gyz)"
      apply (rule hausdorff_distance_infdist_triangle)
      using geodesic_segment_topology(4)[OF geodesic_segmentI] H
      by (auto intro!: quasi_isometry_on_bounded[OF quasi_isometry_on_subset[OF assms]])
    also have "... \<le> 4 * deltaG(TYPE('b)) + hausdorff_distance ({f x--f z} \<union> {f y--f z}) (f`Gxz \<union> f`Gyz)"
      apply (simp, rule thin_triangles[of "{f x--f z}" "f z" "f x" "{f y--f z}" "f y" "{f x--f y}" w2])
      using w2 apply auto
      using geodesic_segment_commute some_geodesic_is_geodesic_segment(1) by blast+
    also have "... \<le> 4 * deltaG(TYPE('b)) + max (hausdorff_distance {f x--f z} (f`Gxz)) (hausdorff_distance {f y--f z} (f`Gyz))"
      apply (intro mono_intros) using H by auto
    also have "... \<le> 4 * deltaG(TYPE('b)) + K"
      using HD[OF H(2)] HD[OF H(3)] by (auto simp add: hausdorff_distance_sym)
    finally have **: "infdist w2 (f`Gxz \<union> f`Gyz) \<le> 4 * deltaG(TYPE('b)) + K" by simp

    have "infdist (f w) (f`Gxz \<union> f`Gyz) \<le> infdist w2 (f`Gxz \<union> f`Gyz) + dist (f w) w2"
      by (rule infdist_triangle)
    then have A: "infdist (f w) (f`(Gxz \<union> Gyz)) \<le> 4 * deltaG(TYPE('b)) + 2 * K"
      using * ** by (auto simp add: image_Un)

    have "infdist w (Gxz \<union> Gyz) \<le> L + epsilon" if "epsilon>0" for epsilon
    proof -
      have *: "epsilon/lambda > 0" using that C by auto
      have "\<exists>z \<in> f`(Gxz \<union> Gyz). dist (f w) z < 4 * deltaG(TYPE('b)) + 2 * K + epsilon/lambda"
        apply (rule infdist_almost_attained)
        using A * H(2) by auto
      then obtain z where z: "z \<in> Gxz \<union> Gyz" "dist (f w) (f z) < 4 * deltaG(TYPE('b)) + 2 * K + epsilon/lambda"
        by auto

      have "infdist w (Gxz \<union> Gyz) \<le> dist w z"
        by (auto intro!: infdist_le z(1))
      also have "... \<le> lambda * dist (f w) (f z) + C * lambda"
        using quasi_isometry_onD[OF assms] by (auto simp add: algebra_simps divide_simps)
      also have "... \<le> lambda * (4 * deltaG(TYPE('b)) + 2 * K + epsilon/lambda) + C * lambda"
        apply (intro mono_intros) using z(2) C by auto
      also have "... = L + epsilon"
        unfolding K_def L_def using C by (auto simp add: algebra_simps)
      finally show ?thesis by simp
    qed
    then have "infdist w (Gxz \<union> Gyz) \<le> L"
      using field_le_epsilon by blast
    then show ?thesis
      using \<open>L \<le> M\<close> by auto
  qed
  then have "Gromov_hyperbolic_subset (4 * M) (UNIV::'a set)"
    using thin_triangles_implies_hyperbolic[OF Thin] by auto
  then show ?thesis unfolding M_def by (auto simp add: algebra_simps)
qed

text \<open>Most often, the precise value of the constant in the previous theorem is irrelevant,
it is used in the following form.\<close>

theorem Gromov_hyperbolic_invariant_under_quasi_isometry:
  assumes "quasi_isometric (UNIV::('a::geodesic_space) set) (UNIV::('b::Gromov_hyperbolic_space_geodesic) set)"
  shows "\<exists>delta. Gromov_hyperbolic_subset delta (UNIV::'a set)"
proof -
  obtain C lambda f where f: "lambda C-quasi_isometry_between (UNIV::'a set) (UNIV::'b set) f"
    using assms unfolding quasi_isometric_def by auto
  show ?thesis
    using Gromov_hyperbolic_invariant_under_quasi_isometry_explicit[OF quasi_isometry_betweenD(1)[OF f]] by blast
qed


section \<open>Metric trees\<close>

text \<open>Metric trees have several equivalent definitions. The simplest one is probably that it
is a geodesic space in which the union of two geodesic segments intersecting only at one endpoint is
still a geodesic segment.

Metric trees are Gromov hyperbolic, with $\delta = 0$.\<close>

class metric_tree = geodesic_space +
  assumes geod_union: "geodesic_segment_between G x y \<Longrightarrow> geodesic_segment_between H y z \<Longrightarrow> G \<inter> H = {y} \<Longrightarrow> geodesic_segment_between (G \<union> H) x z"

text \<open>We will now show that the real line is a metric tree, by identifying its geodesic
segments, i.e., the compact intervals.\<close>

lemma geodesic_segment_between_real:
  assumes "x \<le> (y::real)"
  shows "geodesic_segment_between (G::real set) x y = (G = {x..y})"
proof
  assume H: "geodesic_segment_between G x y"
  then have "connected G" "x \<in> G" "y \<in> G"
    using geodesic_segment_topology(2) geodesic_segmentI geodesic_segment_endpoints by auto
  then have *: "{x..y} \<subseteq> G"
    by (simp add: connected_contains_Icc)
  moreover have "G \<subseteq> {x..y}"
  proof
    fix s assume "s \<in> G"
    have "abs(s-x) + abs(s-y) = abs(x-y)"
      using geodesic_segment_dist[OF H \<open>s \<in> G\<close>] unfolding dist_real_def by auto
    then show "s \<in> {x..y}" using \<open>x \<le> y\<close> by auto
  qed
  ultimately show "G = {x..y}" by auto
next
  assume H: "G = {x..y}"
  define g where "g = (\<lambda>t. t + x)"
  have "g 0 = x \<and> g (dist x y) = y \<and> isometry_on {0..dist x y} g \<and> G = g ` {0..dist x y}"
    unfolding g_def isometry_on_def H using \<open>x \<le> y\<close> by (auto simp add: dist_real_def)
  then have "\<exists>g. g 0 = x \<and> g (dist x y) = y \<and> isometry_on {0..dist x y} g \<and> G = g ` {0..dist x y}"
    by auto
  then show "geodesic_segment_between G x y" unfolding geodesic_segment_between_def by auto
qed

lemma geodesic_segment_between_real':
  "{x--y} = {min x y..max x (y::real)}"
by (metis geodesic_segment_between_real geodesic_segment_commute some_geodesic_is_geodesic_segment(1) max_def min.cobounded1 min_def)

lemma geodesic_segment_real:
  "geodesic_segment (G::real set) = (\<exists>x y. x \<le> y \<and> G = {x..y})"
proof
  assume "geodesic_segment G"
  then obtain x y where *: "geodesic_segment_between G x y" unfolding geodesic_segment_def by auto
  have "(x \<le> y \<and> G = {x..y}) \<or> (y \<le> x \<and> G = {y..x})"
    apply (rule le_cases[of x y])
    using geodesic_segment_between_real * geodesic_segment_commute apply simp
    using geodesic_segment_between_real * geodesic_segment_commute by metis
  then show "\<exists>x y. x \<le> y \<and> G = {x..y}" by auto
next
  assume "\<exists>x y. x \<le> y \<and> G = {x..y}"
  then show "geodesic_segment G"
    unfolding geodesic_segment_def using geodesic_segment_between_real by metis
qed

instance real::metric_tree
proof
  fix G H::"real set" and x y z::real assume GH: "geodesic_segment_between G x y" "geodesic_segment_between H y z" "G \<inter> H = {y}"
  have G: "G = {min x y..max x y}" using GH
    by (metis geodesic_segment_between_real geodesic_segment_commute inf_real_def inf_sup_ord(2) max.coboundedI2 max_def min_def)
  have H: "H = {min y z..max y z}" using GH
    by (metis geodesic_segment_between_real geodesic_segment_commute inf_real_def inf_sup_ord(2) max.coboundedI2 max_def min_def)
  have *: "(x \<le> y \<and> y \<le> z) \<or> (z \<le> y \<and> y \<le> x)"
    using G H \<open>G \<inter> H = {y}\<close> unfolding min_def max_def
    apply auto
    apply (metis (mono_tags, hide_lams) min_le_iff_disj order_refl)
    by (metis (full_types) less_eq_real_def max_def)
  show "geodesic_segment_between (G \<union> H) x z"
    using * apply rule
    using \<open>G \<inter> H = {y}\<close> unfolding G H apply (metis G GH(1) GH(2) H geodesic_segment_between_real ivl_disj_un_two_touch(4) order_trans)
    using \<open>G \<inter> H = {y}\<close> unfolding G H
    by (metis (full_types) Un_commute geodesic_segment_between_real geodesic_segment_commute ivl_disj_un_two_touch(4) le_max_iff_disj max.absorb_iff2 max.commute min_absorb2)
qed

context metric_tree begin

text \<open>We show that a metric tree is uniquely geodesic.\<close>

subclass uniquely_geodesic_space
proof
  fix x y G H assume H: "geodesic_segment_between G x y" "geodesic_segment_between H x (y::'a)"
  show "G = H"
  proof (rule uniquely_geodesic_spaceI[OF _ H])
    fix G H x y assume "geodesic_segment_between G x y" "geodesic_segment_between H x y" "G \<inter> H = {x, (y::'a)}"
    show "x = y"
    proof (rule ccontr)
      assume "x \<noteq> y"
      then have "dist x y > 0" by auto
      obtain g where g: "g 0 = x" "g (dist x y) = y" "isometry_on {0..dist x y} g" "G = g`{0..dist x y}"
        by (meson \<open>geodesic_segment_between G x y\<close> geodesic_segment_between_def)
      define G2 where "G2 = g`{0..dist x y/2}"
      have "G2 \<subseteq> G" unfolding G2_def g(4) by auto
      define z where "z = g(dist x y/2)"
      have "dist x z = dist x y/2"
        using isometry_onD[OF g(3), of 0 "dist x y/2"] g(1) z_def unfolding dist_real_def by auto
      have "dist y z = dist x y/2"
        using isometry_onD[OF g(3), of "dist x y" "dist x y/2"] g(2) z_def unfolding dist_real_def by auto

      have G2: "geodesic_segment_between G2 x z" unfolding \<open>g 0 = x\<close>[symmetric] z_def G2_def
        apply (rule geodesic_segmentI2) by (rule isometry_on_subset[OF g(3)], auto simp add: \<open>g 0 = x\<close>)
      have [simp]: "x \<in> G2" "z \<in> G2" using geodesic_segment_endpoints G2 by auto
      have "dist x a \<le> dist x z" if "a \<in> G2" for a
        apply (rule geodesic_segment_dist_le) using G2 that by auto
      also have "... < dist x y" unfolding \<open>dist x z = dist x y/2\<close> using \<open>dist x y > 0\<close> by auto
      finally have "y \<notin> G2" by auto

      then have "G2 \<inter> H = {x}"
        using \<open>G2 \<subseteq> G\<close> \<open>x \<in> G2\<close> \<open>G \<inter> H = {x, y}\<close> by auto
      have *: "geodesic_segment_between (G2 \<union> H) z y"
        apply (rule geod_union[of _ _ x])
        using \<open>G2 \<inter> H = {x}\<close> \<open>geodesic_segment_between H x y\<close> G2 by (auto simp add: geodesic_segment_commute)
      have "dist x y \<le> dist z x + dist x y" by auto
      also have "... = dist z y"
        apply (rule geodesic_segment_dist[OF *]) using \<open>G \<inter> H = {x, y}\<close> by auto
      also have "... = dist x y / 2"
        by (simp add: \<open>dist y z = dist x y / 2\<close> metric_space_class.dist_commute)
      finally show False using \<open>dist x y > 0\<close> by auto
    qed
  qed
qed

text \<open>An important property of metric trees is that any geodesic triangle is degenerate, i.e., the
three sides intersect at a unique point, the center of the triangle, that we introduce now.\<close>

definition center::"'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "center x y z = (SOME t. t \<in> {x--y} \<inter> {x--z} \<inter> {y--z})"

lemma center_as_intersection:
  "{x--y} \<inter> {x--z} \<inter> {y--z} = {center x y z}"
proof -
  obtain g where g: "g 0 = x" "g (dist x y) = y" "isometry_on {0..dist x y} g" "{x--y} = g`{0..dist x y}"
    by (meson geodesic_segment_between_def some_geodesic_is_geodesic_segment(1))
  obtain h where h: "h 0 = x" "h (dist x z) = z" "isometry_on {0..dist x z} h" "{x--z} = h`{0..dist x z}"
    by (meson geodesic_segment_between_def some_geodesic_is_geodesic_segment(1))

  define Z where "Z = {t \<in> {0..min (dist x y) (dist x z)}. g t = h t}"
  have "0 \<in> Z" unfolding Z_def using g(1) h(1) by auto
  have [simp]: "closed Z"
  proof -
    have *: "Z = (\<lambda>s. dist (g s) (h s))-`{0} \<inter> {0..min (dist x y) (dist x z)}"
      unfolding Z_def by auto
    show ?thesis
      unfolding * apply (rule closed_vimage_Int)
      using continuous_on_subset[OF isometry_on_continuous[OF g(3)], of "{0..min (dist x y) (dist x z)}"]
            continuous_on_subset[OF isometry_on_continuous[OF h(3)], of "{0..min (dist x y) (dist x z)}"]
            continuous_on_dist by auto
  qed
  define a where "a = Sup Z"
  have "a \<in> Z"
    unfolding a_def apply (rule closed_contains_Sup, auto) using \<open>0 \<in> Z\<close> Z_def by auto
  define c where "c = h a"
  then have a: "g a = c" "h a = c" "a \<ge> 0" "a \<le> dist x y" "a \<le> dist x z"
    using \<open>a \<in> Z\<close> unfolding Z_def c_def by auto

  define G2 where "G2 = g`{a..dist x y}"
  have G2: "geodesic_segment_between G2 (g a) (g (dist x y))"
    unfolding G2_def apply (rule geodesic_segmentI2)
    using isometry_on_subset[OF g(3)] \<open>a \<in> Z\<close> unfolding Z_def by auto
  define H2 where "H2 = h`{a..dist x z}"
  have H2: "geodesic_segment_between H2 (h a) (h (dist x z))"
    unfolding H2_def apply (rule geodesic_segmentI2)
    using isometry_on_subset[OF h(3)] \<open>a \<in> Z\<close> unfolding Z_def by auto
  have "G2 \<inter> H2 \<subseteq> {c}"
  proof
    fix w assume w: "w \<in> G2 \<inter> H2"
    obtain sg where sg: "w = g sg" "sg \<in> {a..dist x y}" using w unfolding G2_def by auto
    obtain sh where sh: "w = h sh" "sh \<in> {a..dist x z}" using w unfolding H2_def by auto
    have "dist w x = sg"
      unfolding g(1)[symmetric] sg(1) using isometry_onD[OF g(3), of 0 sg] sg(2)
      unfolding dist_real_def using a by (auto simp add: metric_space_class.dist_commute)
    moreover have "dist w x = sh"
      unfolding h(1)[symmetric] sh(1) using isometry_onD[OF h(3), of 0 sh] sh(2)
      unfolding dist_real_def using a by (auto simp add: metric_space_class.dist_commute)
    ultimately have "sg = sh" by simp
    have "sh \<in> Z" unfolding Z_def using sg sh \<open>a \<ge> 0\<close> unfolding \<open>sg = sh\<close> by auto
    then have "sh \<le> a"
      unfolding a_def apply (rule cSup_upper) unfolding Z_def by auto
    then have "sh = a" using sh(2) by auto
    then show "w \<in> {c}" unfolding sh(1) using a(2) by auto
  qed
  then have *: "G2 \<inter> H2 = {c}"
    unfolding G2_def H2_def using a by (auto simp add: image_iff, force)
  have "geodesic_segment_between (G2 \<union> H2) y z"
    apply (subst g(2)[symmetric], subst h(2)[symmetric]) apply(rule geod_union[of _ _ "h a"])
    using geodesic_segment_commute G2 H2 a * by force+
  then have "G2 \<union> H2 = {y--z}"
    using geodesic_segment_unique by auto
  then have "c \<in> {y--z}" using * by auto
  then have *: "c \<in> {x--y} \<inter> {x--z} \<inter> {y--z}"
    using g(4) h(4) c_def a by force
  have center: "center x y z \<in> {x--y} \<inter> {x--z} \<inter> {y--z}"
    unfolding center_def using someI[of "\<lambda>p. p \<in> {x--y} \<inter> {x--z} \<inter> {y--z}", OF *] by blast
  have *: "dist x d = Gromov_product_at x y z" if "d \<in> {x--y} \<inter> {x--z} \<inter> {y--z}" for d
  proof -
    have "dist x y = dist x d + dist d y"
         "dist x z = dist x d + dist d z"
         "dist y z = dist y d + dist d z"
      using that by (auto simp add: geodesic_segment_dist geodesic_segment_unique)
    then show ?thesis unfolding Gromov_product_at_def by (auto simp add: metric_space_class.dist_commute)
  qed
  have "d = center x y z" if "d \<in> {x--y} \<inter> {x--z} \<inter> {y--z}" for d
    apply (rule geodesic_segment_dist_unique[of "{x--y}" x y])
    using *[OF that] *[OF center] that center by auto
  then show "{x--y} \<inter> {x--z} \<inter> {y--z} = {center x y z}" using center by blast
qed

lemma center_on_geodesic [simp]:
  "center x y z \<in> {x--y}"
  "center x y z \<in> {x--z}"
  "center x y z \<in> {y--z}"
  "center x y z \<in> {y--x}"
  "center x y z \<in> {z--x}"
  "center x y z \<in> {z--y}"
using center_as_intersection by (auto simp add: some_geodesic_commute)

lemma center_commute:
  "center x y z = center x z y"
  "center x y z = center y x z"
  "center x y z = center y z x"
  "center x y z = center z x y"
  "center x y z = center z y x"
using center_as_intersection some_geodesic_commute by blast+

lemma center_dist:
  "dist x (center x y z) = Gromov_product_at x y z"
proof -
  have "dist x y = dist x (center x y z) + dist (center x y z) y"
       "dist x z = dist x (center x y z) + dist (center x y z) z"
       "dist y z = dist y (center x y z) + dist (center x y z) z"
    by (auto simp add: geodesic_segment_dist geodesic_segment_unique)
  then show ?thesis unfolding Gromov_product_at_def by (auto simp add: metric_space_class.dist_commute)
qed

lemma geodesic_intersection:
  "{x--y} \<inter> {x--z} = {x--center x y z}"
proof -
  have "{x--y} = {x--center x y z} \<union> {center x y z--y}"
    using center_as_intersection geodesic_segment_split by blast
  moreover have "{x--z} = {x--center x y z} \<union> {center x y z--z}"
    using center_as_intersection geodesic_segment_split by blast
  ultimately have "{x--y} \<inter> {x--z} = {x--center x y z} \<union> ({center x y z--y} \<inter> {x--center x y z}) \<union> ({center x y z--y} \<inter> {x--center x y z}) \<union> ({center x y z--y} \<inter> {center x y z--z})"
    by auto
  moreover have "{center x y z--y} \<inter> {x--center x y z} = {center x y z}"
    using geodesic_segment_split(2) center_as_intersection[of x y z] by auto
  moreover have "{center x y z--y} \<inter> {x--center x y z} = {center x y z}"
    using geodesic_segment_split(2) center_as_intersection[of x y z] by auto
  moreover have "{center x y z--y} \<inter> {center x y z--z} = {center x y z}"
    using geodesic_segment_split(2)[of "center x y z" y z] center_as_intersection[of x y z] by (auto simp add: some_geodesic_commute)
  ultimately show "{x--y} \<inter> {x--z} = {x--center x y z}" by auto
qed
end (*of context metric_tree*)

text \<open>We can now prove that a metric tree is Gromov hyperbolic, for $\delta = 0$. The simplest
proof goes through the slim triangles property: it suffices to show that, given a geodesic triangle,
there is a point at distance at most $0$ of each of its sides. This is the center we have
constructed above.\<close>

class metric_tree_with_delta = metric_tree + metric_space_with_deltaG +
  assumes delta0: "deltaG(TYPE('a::metric_space)) = 0"

class Gromov_hyperbolic_space_0 = Gromov_hyperbolic_space +
  assumes delta0 [simp]: "deltaG(TYPE('a::metric_space)) = 0"

class Gromov_hyperbolic_space_0_geodesic = Gromov_hyperbolic_space_0 + geodesic_space

text \<open>Isabelle does not accept cycles in the class graph. So, we will show that
\verb+metric_tree_with_delta+ is a subclass of \verb+Gromov_hyperbolic_space_0_geodesic+, and
conversely that \verb+Gromov_hyperbolic_space_0_geodesic+ is a subclass of \verb+metric_tree+.

In a tree, we have already proved that triangles are $0$-slim (the center is common to all sides
of the triangle). The $0$-hyperbolicity follows from one of the equivalent characterizations
of hyperbolicity (the other characterizations could be used as well, but the proofs would be
less immediate.)\<close>

subclass (in metric_tree_with_delta) Gromov_hyperbolic_space_0
proof (standard)
  show "deltaG TYPE('a) = 0" unfolding delta0 by auto
  have "Gromov_hyperbolic_subset (6 * 0) (UNIV::'a set)"
  proof (rule slim_triangles_implies_hyperbolic)
    fix x::'a and y z Gxy Gyz Gxz
    define w where "w = center x y z"
    assume "geodesic_segment_between Gxy x y"
        "geodesic_segment_between Gxz x z" "geodesic_segment_between Gyz y z"
    then have "Gxy = {x--y}" "Gyz = {y--z}" "Gxz = {x--z}"
      by (auto simp add: local.geodesic_segment_unique)
    then have "w \<in> Gxy" "w \<in> Gyz" "w \<in> Gxz"
      unfolding w_def by auto
    then have "infdist w Gxy \<le> 0 \<and> infdist w Gxz \<le> 0 \<and> infdist w Gyz \<le> 0"
      by auto
    then show "\<exists>w. infdist w Gxy \<le> 0 \<and> infdist w Gxz \<le> 0 \<and> infdist w Gyz \<le> 0"
      by blast
  qed
  then show "Gromov_hyperbolic_subset (deltaG TYPE('a)) (UNIV::'a set)" unfolding delta0 by auto
qed

text \<open>To use the fact that reals are Gromov hyperbolic, given that they are a metric tree,
we need to instantiate them as \verb+metric_tree_with_delta+.\<close>

instantiation real::metric_tree_with_delta
begin
definition deltaG_real::"real itself \<Rightarrow> real"
  where "deltaG_real _ = 0"
instance apply standard unfolding deltaG_real_def by auto
end

text \<open>Let us now prove the converse: a geodesic space which is $\delta$-hyperbolic for $\delta = 0$
is a metric tree. For the proof, we consider two geodesic segments $G = [x,y]$ and $H = [y,z]$ with a common
endpoint, and we have to show that their union is still a geodesic segment from $x$ to $z$. For
this, introduce a geodesic segment $L = [x,z]$. By the property of thin triangles, $G$ is included
in $H \cup L$. In particular, a point $Y$ close to $y$ but different from $y$ on $G$ is on $L$,
and therefore realizes the equality $d(x,z) = d(x, Y) + d(Y, z)$. Passing to the limit, $y$
also satisfies this equality. The conclusion readily follows thanks to Lemma
\verb+geodesic_segment_union+.
\<close>

subclass (in Gromov_hyperbolic_space_0_geodesic) metric_tree
proof
  fix G H x y z assume A: "geodesic_segment_between G x y" "geodesic_segment_between H y z" "G \<inter> H = {y::'a}"
  show "geodesic_segment_between (G \<union> H) x z"
  proof (cases "x = y")
    case True
    then show ?thesis
      by (metis A Un_commute geodesic_segment_between_x_x(3) inf.commute sup_inf_absorb)
  next
    case False
    define D::"nat \<Rightarrow> real" where "D = (\<lambda>n. dist x y - (dist x y) * (1/(real(n+1))))"
    have D: "D n \<in> {0..< dist x y}" "D n \<in> {0..dist x y}" for n
      unfolding D_def by (auto simp add: False divide_simps algebra_simps)
    have Dlim: "D \<longlonglongrightarrow> dist x y - dist x y * 0"
      unfolding D_def by (intro tendsto_intros LIMSEQ_ignore_initial_segment[OF lim_1_over_n, of 1])

    define Y::"nat \<Rightarrow> 'a" where "Y = (\<lambda>n. geodesic_segment_param G x (D n))"
    have *: "Y \<longlonglongrightarrow> y"
      unfolding Y_def apply (subst geodesic_segment_param(2)[OF A(1), symmetric])
      using isometry_on_continuous[OF geodesic_segment_param(4)[OF A(1)]]
      unfolding continuous_on_sequentially comp_def using D(2) Dlim by auto

    have "dist x z = dist x (Y n) + dist (Y n) z" for n
    proof -
      obtain L where L: "geodesic_segment_between L x z" using geodesic_subsetD[OF geodesic] by blast
      have "Y n \<in> G" unfolding Y_def
        apply (rule geodesic_segment_param(3)[OF A(1)]) using D[of n] by auto
      have "dist x (Y n) = D n"
        unfolding Y_def apply (rule geodesic_segment_param[OF A(1)]) using D[of n] by auto
      then have "Y n \<noteq> y"
        using D[of n] by auto
      then have "Y n \<notin> H" using A(3) \<open>Y n \<in> G\<close> by auto
      have "infdist (Y n) (H \<union> L) \<le> 4 * deltaG(TYPE('a))"
        apply (rule thin_triangles[OF geodesic_segment_commute[OF A(2)] geodesic_segment_commute[OF L] geodesic_segment_commute[OF A(1)]])
        using \<open>Y n \<in> G\<close> by simp
      then have "infdist (Y n) (H \<union> L) = 0"
        using infdist_nonneg[of "Y n" "H \<union> L"] unfolding delta0 by auto
      have "Y n \<in> H \<union> L"
      proof (subst in_closed_iff_infdist_zero)
        have "closed H"
          using A(2) geodesic_segment_topology geodesic_segment_def by fastforce
        moreover have "closed L"
          using L geodesic_segment_topology geodesic_segment_def by fastforce
        ultimately show "closed (H \<union> L)" by auto
        show "H \<union> L \<noteq> {}" using A(2) geodesic_segment_endpoints(1) by auto
      qed (fact)
      then have "Y n \<in> L" using \<open>Y n \<notin> H\<close> by simp
      show ?thesis using geodesic_segment_dist[OF L \<open>Y n \<in> L\<close>] by simp
    qed
    moreover have "(\<lambda>n. dist x (Y n) + dist (Y n) z) \<longlonglongrightarrow> dist x y + dist y z"
      by (intro tendsto_intros *)
    ultimately have "(\<lambda>n. dist x z) \<longlonglongrightarrow> dist x y + dist y z"
      using filterlim_cong eventually_sequentially by auto
    then have *: "dist x z = dist x y + dist y z"
      using LIMSEQ_unique by auto
    show "geodesic_segment_between (G \<union> H) x z"
      by (rule geodesic_segment_union[OF * A(1) A(2)])
  qed
qed

end (*of theory Gromov_Hyperbolic*)
