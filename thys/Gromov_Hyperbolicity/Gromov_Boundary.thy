(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)


theory Gromov_Boundary
  imports Gromov_Hyperbolicity Eexp_Eln
begin

section \<open>Constructing a distance from a quasi-distance\<close>

text \<open>Below, we will construct a distance on the Gromov completion of a hyperbolic space. The
geometrical object that arises naturally is almost a distance, but it does not satisfy the triangular
inequality. There is a general process to turn such a quasi-distance into a genuine distance, as
follows: define the new distance $\tilde d(x,y)$ to be the infimum of $d(x, u_1) + d(u_1,u_2) +
\dotsb + d(u_{n-1},x)$ over all sequences of points (of any length) connecting $x$ to $y$.
It is clear that it satisfies the triangular inequality, is symmetric, and $\tilde d(x,y) \leq
d(x,y)$. What is not clear, however, is if $\tilde d(x,y)$ can be zero if $x \neq y$, or more
generally how one can bound $\tilde d$ from below. The main point of this contruction is that,
if $d$ satisfies the inequality $d(x,z) \leq \sqrt{2} \max(d(x,y), d(y,z))$, then one
has $\tilde d(x,y) \geq d(x,y)/2$ (and in particular $\tilde d$ defines the same topology, the
same set of Lipschitz functions, and so on, as $d$).

This statement can be found in [Bourbaki, topologie generale, chapitre 10] or in
[Ghys-de la Harpe] for instance. We follow their proof.
\<close>

definition turn_into_distance::"('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> real)"
  where "turn_into_distance f x y = Inf {(\<Sum> i \<in> {0..<n}. f (u i) (u (Suc i)))| u (n::nat). u 0 = x \<and> u n = y}"

locale Turn_into_distance =
  fixes f::"'a \<Rightarrow> 'a \<Rightarrow> real"
  assumes nonneg: "f x y \<ge> 0"
      and sym: "f x y = f y x"
      and self_zero: "f x x = 0"
      and weak_triangle: "f x z \<le> sqrt 2 * max (f x y) (f y z)"
begin

text \<open>The two lemmas below are useful when dealing with Inf results, as they always require
the set under consideration to be non-empty and bounded from below.\<close>

lemma bdd_below [simp]:
  "bdd_below {(\<Sum> i = 0..<n. f (u i) (u (Suc i)))| u (n::nat). u 0 = x \<and> u n = y}"
  apply (rule bdd_belowI[of _ 0]) using nonneg by (auto simp add: sum_nonneg)

lemma nonempty:
  "{\<Sum>i = 0..<n. f (u i) (u (Suc i)) |u n. u 0 = x \<and> u n = y} \<noteq> {}"
proof -
  define u::"nat \<Rightarrow> 'a" where "u = (\<lambda>n. if n = 0 then x else y)"
  define n::nat where "n = 1"
  have "u 0 = x \<and> u n = y" unfolding u_def n_def by auto
  then have "(\<Sum>i = 0..<n. f (u i) (u (Suc i))) \<in> {\<Sum>i = 0..<n. f (u i) (u (Suc i)) |u n. u 0 = x \<and> u n = y}"
    by auto
  then show ?thesis by auto
qed

text \<open>We can now prove that \verb+turn_into_distance f+ satisfies all the properties of a distance.
First, it is nonnegative.\<close>

lemma TID_nonneg:
  "turn_into_distance f x y \<ge> 0"
unfolding turn_into_distance_def apply (rule cInf_greatest[OF nonempty])
using nonneg by (auto simp add: sum_nonneg)

text \<open>For the symmetry, we use the symmetry of $f$, and go backwards along a chain of points,
replacing a sequence from $x$ to $y$ with a sequence from $y$ to $x$.\<close>

lemma TID_sym:
  "turn_into_distance f x y = turn_into_distance f y x"
proof -
  have "turn_into_distance f x y \<le> Inf {(\<Sum> i \<in> {0..<n}. f (u i) (u (Suc i)))| u (n::nat). u 0 = y \<and> u n = x}" for x y
  proof (rule cInf_greatest[OF nonempty], auto)
    fix u::"nat \<Rightarrow> 'a" and n assume U: "y = u 0" "x = u n"
    define v::"nat \<Rightarrow>'a" where "v = (\<lambda>i. u (n-i))"
    have V: "v 0 = x" "v n = y" unfolding v_def using U by auto

    have "(\<Sum>i = 0..<n. f (u i) (u (Suc i))) = (\<Sum>i = 0..<n. (\<lambda>i. f (u i) (u (Suc i))) (n-1-i))"
      apply (rule sum.reindex_bij_betw[symmetric])
      by (rule bij_betw_byWitness[of _ "\<lambda>i. n-1-i"], auto)
    also have "... = (\<Sum> i = 0..<n. f (v (Suc i)) (v i))"
      apply (rule sum.cong) unfolding v_def by (auto simp add: Suc_diff_Suc)
    also have "... = (\<Sum> i = 0..<n. f (v i) (v (Suc i)))"
      using sym by auto
    finally have "(\<Sum>i = 0..<n. f (u i) (u (Suc i))) = (\<Sum> i = 0..<n. f (v i) (v (Suc i)))"
      by simp

    moreover have "turn_into_distance f x y \<le> (\<Sum> i = 0..<n. f (v i) (v (Suc i)))"
      unfolding turn_into_distance_def apply (rule cInf_lower)
      using V by auto
    finally show "turn_into_distance f (u n) (u 0) \<le> (\<Sum>i = 0..<n. f (u i) (u (Suc i)))"
      using U by auto
  qed
  then have *: "turn_into_distance f x y \<le> turn_into_distance f y x" for x y
    unfolding turn_into_distance_def by auto
  show ?thesis using *[of x y] *[of y x] by simp
qed

text \<open>There is a trivial upper bound by $f$, using the single chain $x, y$.\<close>

lemma upper:
  "turn_into_distance f x y \<le> f x y"
unfolding turn_into_distance_def proof (rule cInf_lower, auto)
  define u::"nat \<Rightarrow> 'a" where "u = (\<lambda>n. if n = 0 then x else y)"
  define n::nat where "n = 1"
  have "u 0 = x \<and> u n = y \<and> f x y = (\<Sum>i = 0..<n. f (u i) (u (Suc i)))" unfolding u_def n_def by auto
  then show "\<exists>u n. f x y = (\<Sum>i = 0..<n. f (u i) (u (Suc i))) \<and> u 0 = x \<and> u n = y"
    by auto
qed

text \<open>The new distance vanishes on a pair of equal points, as this is already the case for $f$.\<close>

lemma TID_self_zero:
  "turn_into_distance f x x = 0"
using upper[of x x] TID_nonneg[of x x] self_zero[of x] by auto

text \<open>For the triangular inequality, we concatenate a sequence from $x$ to $y$ almost realizing the
infimum, and a sequence from $y$ to $z$ almost realizing the infimum, to obtain a sequence from
$x$ to $z$ along which the sums of $f$ is almost bounded by
\verb|turn_into_distance f x y + turn_into_distance f y z|.
\<close>

lemma triangle:
  "turn_into_distance f x z \<le> turn_into_distance f x y + turn_into_distance f y z"
proof -
  have "turn_into_distance f x z \<le> turn_into_distance f x y + turn_into_distance f y z + e" if "e > 0" for e
  proof -
    have "Inf {(\<Sum> i \<in> {0..<n}. f (u i) (u (Suc i)))| u (n::nat). u 0 = x \<and> u n = y} < turn_into_distance f x y + e/2"
      unfolding turn_into_distance_def using \<open>e > 0\<close> by auto
    then have "\<exists>a \<in> {(\<Sum> i \<in> {0..<n}. f (u i) (u (Suc i)))| u (n::nat). u 0 = x \<and> u n = y}. a < turn_into_distance f x y + e/2"
      by (rule cInf_lessD[OF nonempty])
    then obtain u n where U: "u 0 = x" "u n = y" "(\<Sum> i \<in> {0..<n}. f (u i) (u (Suc i))) < turn_into_distance f x y + e/2"
      by auto

    have "Inf {(\<Sum> i \<in> {0..<m}. f (v i) (v (Suc i)))| v (m::nat). v 0 = y \<and> v m = z} < turn_into_distance f y z + e/2"
      unfolding turn_into_distance_def using \<open>e > 0\<close> by auto
    then have "\<exists>a \<in> {(\<Sum> i \<in> {0..<m}. f (v i) (v (Suc i)))| v (m::nat). v 0 = y \<and> v m = z}. a < turn_into_distance f y z + e/2"
      by (rule cInf_lessD[OF nonempty])
    then obtain v m where V: "v 0 = y" "v m = z" "(\<Sum> i \<in> {0..<m}. f (v i) (v (Suc i))) < turn_into_distance f y z + e/2"
      by auto

    define w where "w = (\<lambda>i. if i < n then u i else v (i-n))"
    have *: "w 0 = x" "w (n+m) = z"
      unfolding w_def using U V by auto
    have "turn_into_distance f x z \<le> (\<Sum>i = 0..<n+m. f (w i) (w (Suc i)))"
      unfolding turn_into_distance_def apply (rule cInf_lower) using * by auto
    also have "... = (\<Sum>i = 0..<n. f (w i) (w (Suc i))) + (\<Sum>i = n..<n+m. f (w i) (w (Suc i)))"
      by (simp add: sum.atLeastLessThan_concat)
    also have "... = (\<Sum>i = 0..<n. f (w i) (w (Suc i))) + (\<Sum>i = 0..<m. f (w (i+n)) (w (Suc (i+n))))"
      by (auto intro!: sum.reindex_bij_betw[symmetric] bij_betw_byWitness[of _ "\<lambda>i. i-n"])
    also have "... = (\<Sum>i = 0..<n. f (u i) (u (Suc i))) + (\<Sum>i = 0..<m. f (v i) (v (Suc i)))"
      unfolding w_def apply (auto intro!: sum.cong)
      using U(2) V(1) Suc_lessI by fastforce
    also have "... < turn_into_distance f x y + e/2 + turn_into_distance f y z + e/2"
      using U(3) V(3) by auto
    finally show ?thesis by auto
  qed
  then show ?thesis
    using field_le_epsilon by blast
qed

text \<open>Now comes the only nontrivial statement of the construction, the fact that the new
distance is bounded from below by $f/2$.

Here is the mathematical proof. We show by induction that all chains from $x$ to
$y$ satisfy this bound. Assume this is done for all chains of length $<n$, we do it for a
chain of length $n$. Write $S = \sum f(u_i, u_{i+1})$ for the sum along the chain. Introduce $p$
the last index where the sum is $\leq S/2$. Then the sum from $0$ to $p$ is $\leq S/2$, and the sum
from $p+1$ to $n$ is also $\leq S/2$ (by maximality of $p$). The induction assumption
gives that $f (x, u_p)$ is bounded by twice the sum from $0$ to $p$, which is at most $S$. Same
thing for $f(u_{p+1}, y)$. With the weird triangle inequality applied two times, we get
$f (x, y) \leq 2 \max(f(x,u_p), f(u_p, u_{p+1}), f(u_{p+1}, y)) \leq 2S$, as claimed.

The formalization presents no difficulty.
\<close>

lemma lower:
  "f x y \<le> 2 * turn_into_distance f x y"
proof -
  have I: "f (u 0) (u n) \<le> (\<Sum> i \<in> {0..<n}. f (u i) (u (Suc i))) * 2" for n u
  proof (induction n arbitrary: u rule: less_induct)
    case (less n)
    show "f (u 0) (u n) \<le> (\<Sum>i = 0..<n. f (u i) (u (Suc i))) * 2"
    proof (cases "n = 0")
      case True
      then have "f (u 0) (u n) = 0" using self_zero by auto
      then show ?thesis using True by auto
    next
      case False
      then have "n > 0" by auto
      define S where "S = (\<Sum>i = 0..<n. f (u i) (u (Suc i)))"
      have "S \<ge> 0" unfolding S_def using nonneg by (auto simp add: sum_nonneg)
      have "\<exists>p. p < n \<and> (\<Sum>i = 0..<p. f (u i) (u (Suc i))) \<le> S/2 \<and> (\<Sum>i = Suc p..<n. f (u i) (u (Suc i))) \<le> S/2"
      proof (cases "S = 0")
        case True
        have "(\<Sum>i = Suc 0..<n. f (u i) (u (Suc i))) = (\<Sum>i = 0..<n. f (u i) (u (Suc i))) - f(u 0) (u (Suc 0))"
          using sum_head_upt_Suc[OF \<open>n > 0\<close>, of "\<lambda>i. f (u i) (u (Suc i))"] by simp
        also have "... \<le> S/2" using True S_def nonneg by auto
        finally have "0 < n \<and> (\<Sum>i = 0..<0. f (u i) (u (Suc i))) \<le> S/2 \<and> (\<Sum>i = Suc 0..<n. f (u i) (u (Suc i))) \<le> S/2"
          using \<open>n > 0\<close> \<open>S = 0\<close> by auto
        then show ?thesis by auto
      next
        case False
        then have "S > 0" using \<open>S \<ge> 0\<close> by simp
        define A where "A = {q. q \<le> n \<and> (\<Sum>i = 0..<q. f (u i) (u (Suc i))) \<le> S/2}"
        have "0 \<in> A" unfolding A_def using \<open>S > 0\<close> \<open>n > 0\<close> by auto
        have "n \<notin> A" unfolding A_def using \<open>S > 0\<close> unfolding S_def by auto
        define p where "p = Max A"
        have "p \<in> A" unfolding p_def apply (rule Max_in) using \<open>0 \<in> A\<close> unfolding A_def by auto
        then have L: "p \<le> n" "(\<Sum>i = 0..<p. f (u i) (u (Suc i))) \<le> S/2" unfolding A_def by auto
        then have "p < n" using \<open>n \<notin> A\<close> \<open>p \<in> A\<close> le_neq_trans by blast
        have "Suc p \<notin> A" unfolding p_def
          by (metis (no_types, lifting) A_def Max_ge Suc_n_not_le_n infinite_nat_iff_unbounded mem_Collect_eq not_le p_def)
        then have *: "(\<Sum>i = 0..<Suc p. f (u i) (u (Suc i))) > S/2"
          unfolding A_def using \<open>p < n\<close> by auto
        have "(\<Sum> i = Suc p..<n. f (u i) (u (Suc i))) = S - (\<Sum>i = 0..<Suc p. f (u i) (u (Suc i)))"
          unfolding S_def using \<open>p < n\<close> by (metis (full_types) Suc_le_eq sum_diff_nat_ivl zero_le)
        also have "... \<le> S/2" using * by auto
        finally have "p < n \<and> (\<Sum>i = 0..<p. f (u i) (u (Suc i))) \<le> S/2 \<and> (\<Sum>i = Suc p..<n. f (u i) (u (Suc i))) \<le> S/2"
          using \<open>p < n\<close> L(2) by auto
        then show ?thesis by auto
      qed
      then obtain p where P: "p < n" "(\<Sum>i = 0..<p. f (u i) (u (Suc i))) \<le> S/2" "(\<Sum>i = Suc p..<n. f (u i) (u (Suc i))) \<le> S/2"
        by auto
      have "f (u 0) (u p) \<le> (\<Sum>i = 0..<p. f (u i) (u (Suc i))) * 2"
        apply (rule less.IH) using \<open>p < n\<close> by auto
      then have A: "f (u 0) (u p) \<le> S" using P(2) by auto
      have B: "f (u p) (u (Suc p)) \<le> S"
        apply (rule sum_nonneg_leq_bound[of "{0..<n}" "\<lambda>i. f (u i) (u (Suc i))"])
        using nonneg S_def \<open>p < n\<close> by auto
      have "f (u (0 + Suc p)) (u ((n-Suc p) + Suc p)) \<le> (\<Sum>i = 0..<n-Suc p. f (u (i + Suc p)) (u (Suc i + Suc p))) * 2"
        apply (rule less.IH) using \<open>n > 0\<close> by auto
      also have "... = 2 * (\<Sum>i = Suc p..<n. f (u i) (u (Suc i)))"
        by (auto intro!: sum.reindex_bij_betw bij_betw_byWitness[of _ "\<lambda>i. i - Suc p"])
      also have "... \<le> S" using P(3) by simp
      finally have C: "f (u (Suc p)) (u n) \<le> S"
        using \<open>p < n\<close> by auto

      have "f (u 0) (u n) \<le> sqrt 2 * max (f (u 0) (u p)) (f (u p) (u n))"
        using weak_triangle by simp
      also have "... \<le> sqrt 2* max (f (u 0) (u p)) (sqrt 2 * max (f (u p) (u (Suc p))) (f (u (Suc p)) (u n)))"
        using weak_triangle by simp (meson max.cobounded2 order_trans)
      also have "... \<le> sqrt 2 * max S (sqrt 2 * max S S)"
        using A B C by auto (simp add: le_max_iff_disj)
      also have "... \<le> sqrt 2 * max (sqrt 2 * S) (sqrt 2 * max S S)"
        apply (intro mult_left_mono max.mono) using \<open>S \<ge> 0\<close> less_eq_real_def by auto
      also have "... = 2 * S"
        by auto
      finally show ?thesis
        unfolding S_def by simp
    qed
  qed
  have "f x y/2 \<le> turn_into_distance f x y"
    unfolding turn_into_distance_def by (rule cInf_greatest[OF nonempty], auto simp add: I)
  then show ?thesis by simp
qed

end (*of locale Turn_into_distance*)


section \<open>The Gromov completion of a hyperbolic space\<close>

subsection \<open>The Gromov boundary as a set\<close>

text \<open>A sequence in a Gromov hyperbolic space converges to a point in the boundary if
the Gromov product $(u_n, u_m)_e$ tends to infinity when $m,n \to _infty$. The point at infinity
is defined as the equivalence class of such sequences, for the relation $u \sim v$ iff
$(u_n, v_n)_e \to \infty$ (or, equivalently, $(u_n, v_m)_e \to \infty$ when $m, n\to \infty$, or
one could also change basepoints). Hence, the Gromov boundary is naturally defined as a quotient
type. There is a difficulty: it can be empty in general, hence defining it as a type is not always
possible. One could introduce a new typeclass of Gromov hyperbolic spaces for which the boundary
is not empty (unboundedness is not enough, think of infinitely many segments $[0,n]$ all joined at
$0$), and then only define the boundary of such spaces. However, this is tedious. Rather, we
work with the Gromov completion (containing the space and its boundary), this is always not empty.
The price to pay is that, in the definition of the completion, we have to distinguish between
sequences converging to the boundary and sequences converging inside the space. This is more natural
to proceed in this way as the interesting features of the boundary come from the fact that its sits
at infinity of the initial space, so their relations (and the topology of $X \cup \partial X$) are
central.\<close>

definition Gromov_converging_at_boundary::"(nat \<Rightarrow> ('a::Gromov_hyperbolic_space)) \<Rightarrow> bool"
  where "Gromov_converging_at_boundary u = (\<forall>a. \<forall>(M::real). \<exists>N. \<forall>n \<ge> N. \<forall> m\<ge>N. Gromov_product_at a (u m) (u n) \<ge> M)"

lemma Gromov_converging_at_boundaryI:
  assumes "\<And>M. \<exists>N. \<forall>n \<ge> N. \<forall> m\<ge>N. Gromov_product_at a (u m) (u n) \<ge> M"
  shows "Gromov_converging_at_boundary u"
unfolding Gromov_converging_at_boundary_def proof (auto)
  fix b::'a and M::real
  obtain N where *: "\<And>m n. n\<ge>N \<Longrightarrow> m\<ge>N \<Longrightarrow> Gromov_product_at a (u m) (u n) \<ge> M + dist a b"
    using assms[of "M + dist a b"] by auto
  have "Gromov_product_at b (u m) (u n) \<ge> M" if "m \<ge> N" "n \<ge> N" for m n
    using *[OF that] Gromov_product_at_diff1[of a "u m" "u n" b] by (smt Gromov_product_commute)
  then show "\<exists>N. \<forall>n\<ge>N. \<forall>m\<ge>N. M \<le> Gromov_product_at b (u m) (u n)" by auto
qed

lemma Gromov_converging_at_boundary_imp_unbounded:
  assumes "Gromov_converging_at_boundary u"
  shows "(\<lambda>n. dist a (u n)) \<longlonglongrightarrow> \<infinity>"
proof -
  have "\<exists>N. \<forall>n \<ge> N. dist a (u n) \<ge> M" for M::real
    using assms unfolding Gromov_converging_at_boundary_def Gromov_product_e_x_x[symmetric] by meson
  then show ?thesis
    unfolding tendsto_PInfty eventually_sequentially by (meson dual_order.strict_trans1 gt_ex less_ereal.simps(1))
qed

lemma Gromov_converging_at_boundary_imp_not_constant:
  "\<not>(Gromov_converging_at_boundary (\<lambda>n. x))"
  using Gromov_converging_at_boundary_imp_unbounded[of "(\<lambda>n. x)" "x"] Lim_bounded_PInfty by auto

lemma Gromov_converging_at_boundary_imp_not_constant':
  assumes "Gromov_converging_at_boundary u"
  shows "\<not>(\<forall>m n. u m = u n)"
  using Gromov_converging_at_boundary_imp_not_constant
  by (metis (no_types) Gromov_converging_at_boundary_def assms order_refl)

text \<open>We introduce a partial equivalence relation, defined over the sequences that converge to
infinity, and the constant sequences. Quotienting the space of admissible sequences by this
equivalence relation will give rise to the Gromov completion.\<close>

definition Gromov_completion_rel::"(nat \<Rightarrow> 'a::Gromov_hyperbolic_space) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool"
  where "Gromov_completion_rel u v =
            (((Gromov_converging_at_boundary u \<and> Gromov_converging_at_boundary v \<and> (\<forall>a. (\<lambda>n. Gromov_product_at a (u n) (v n)) \<longlonglongrightarrow> \<infinity>)))
            \<or> (\<forall>n m. u n = v m \<and> u n = u m \<and> v n = v m))"

text \<open>We need some basic lemmas to work separately with sequences tending to the boundary
and with constant sequences, as follows.\<close>

lemma Gromov_completion_rel_const [simp]:
  "Gromov_completion_rel (\<lambda>n. x) (\<lambda>n. x)"
unfolding Gromov_completion_rel_def by auto

lemma Gromov_completion_rel_to_const:
  assumes "Gromov_completion_rel u (\<lambda>n. x)"
  shows "u n = x"
using assms unfolding Gromov_completion_rel_def using Gromov_converging_at_boundary_imp_not_constant[of x] by auto

lemma Gromov_completion_rel_to_const':
  assumes "Gromov_completion_rel (\<lambda>n. x) u"
  shows "u n = x"
using assms unfolding Gromov_completion_rel_def using Gromov_converging_at_boundary_imp_not_constant[of x] by auto

lemma Gromov_product_tendsto_PInf_a_b:
  assumes "(\<lambda>n. Gromov_product_at a (u n) (v n)) \<longlonglongrightarrow> \<infinity>"
  shows "(\<lambda>n. Gromov_product_at b (u n) (v n)) \<longlonglongrightarrow> \<infinity>"
proof (rule tendsto_sandwich[of "\<lambda>n. ereal(Gromov_product_at a (u n) (v n)) + (- dist a b)" _ _ "\<lambda>n. \<infinity>"])
  have "ereal(Gromov_product_at b (u n) (v n)) \<ge> ereal(Gromov_product_at a (u n) (v n)) + (- dist a b)" for n
    using Gromov_product_at_diff1[of a "u n" "v n" b] by auto
  then show "\<forall>\<^sub>F n in sequentially. ereal (Gromov_product_at a (u n) (v n)) + ereal (- dist a b) \<le> ereal (Gromov_product_at b (u n) (v n))"
    by auto
  have "(\<lambda>n. ereal(Gromov_product_at a (u n) (v n)) + (- dist a b)) \<longlonglongrightarrow> \<infinity> + (- dist a b)"
    apply (intro tendsto_intros) using assms by auto
  then show "(\<lambda>n. ereal (Gromov_product_at a (u n) (v n)) + ereal (- dist a b)) \<longlonglongrightarrow> \<infinity>" by simp
qed (auto)

lemma Gromov_converging_at_boundary_rel:
  assumes "Gromov_converging_at_boundary u"
  shows "Gromov_completion_rel u u"
unfolding Gromov_completion_rel_def using Gromov_converging_at_boundary_imp_unbounded[OF assms] assms by auto

text \<open>We can now prove that we indeed have an equivalence relation.\<close>

lemma part_equivp_Gromov_completion_rel:
  "part_equivp Gromov_completion_rel"
proof (rule part_equivpI)
  show "\<exists>x::(nat \<Rightarrow> 'a). Gromov_completion_rel x x"
    apply (rule exI[of _ "\<lambda>n. (SOME a::'a. True)"]) unfolding Gromov_completion_rel_def by (auto simp add: convergent_const)

  show "symp Gromov_completion_rel"
    unfolding symp_def Gromov_completion_rel_def by (auto simp add: Gromov_product_commute) metis+

  show "transp (Gromov_completion_rel::(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool)"
  unfolding transp_def proof (intro allI impI)
    fix u v w::"nat\<Rightarrow>'a"
    assume UV: "Gromov_completion_rel u v"
       and VW: "Gromov_completion_rel v w"
    show "Gromov_completion_rel u w"
    proof (cases "\<forall>n m. v n = v m")
      case True
      define a where "a = v 0"
      have *: "v = (\<lambda>n. a)" unfolding a_def using True by auto
      then have "u n = v 0" "w n = v 0" for n
        using Gromov_completion_rel_to_const' Gromov_completion_rel_to_const UV VW unfolding * by auto force
      then show ?thesis
        using UV VW unfolding Gromov_completion_rel_def by auto
    next
      case False
      have "(\<lambda>n. Gromov_product_at a (u n) (w n)) \<longlonglongrightarrow> \<infinity>" for a
      proof (rule tendsto_sandwich[of "\<lambda>n. min (ereal (Gromov_product_at a (u n) (v n))) (ereal (Gromov_product_at a (v n) (w n))) + (- deltaG(TYPE('a)))" _ _ "\<lambda>n. \<infinity>"])
        have "min (Gromov_product_at a (u n) (v n)) (Gromov_product_at a (v n) (w n)) - deltaG(TYPE('a)) \<le> Gromov_product_at a (u n) (w n)" for n
          by (rule hyperb_ineq)
        then have "min (ereal (Gromov_product_at a (u n) (v n))) (ereal (Gromov_product_at a (v n) (w n))) + ereal (- deltaG TYPE('a)) \<le> ereal (Gromov_product_at a (u n) (w n))" for n
          by (auto simp del: ereal_min simp add: ereal_min[symmetric])
        then show "\<forall>\<^sub>F n in sequentially. min (ereal (Gromov_product_at a (u n) (v n))) (ereal (Gromov_product_at a (v n) (w n)))
                    + ereal (- deltaG TYPE('a)) \<le> ereal (Gromov_product_at a (u n) (w n))"
          unfolding eventually_sequentially by auto

        have "(\<lambda>n. min (ereal (Gromov_product_at a (u n) (v n))) (ereal (Gromov_product_at a (v n) (w n))) + (- deltaG(TYPE('a)))) \<longlonglongrightarrow> min \<infinity> \<infinity> + (- deltaG(TYPE('a)))"
          apply (intro tendsto_intros) using UV VW False unfolding Gromov_completion_rel_def by auto
        then show "(\<lambda>n. min (ereal (Gromov_product_at a (u n) (v n))) (ereal (Gromov_product_at a (v n) (w n))) + (- deltaG(TYPE('a)))) \<longlonglongrightarrow> \<infinity>" by auto
      qed (auto)
      then show ?thesis
        using False UV VW unfolding Gromov_completion_rel_def by auto
    qed
  qed
qed

text \<open>We can now define the Gromov completion of a Gromov hyperbolic space, considering either
sequences converging to a point on the boundary, or sequences converging inside the space, and
quotienting by the natural equivalence relation.\<close>

quotient_type (overloaded) 'a Gromov_completion =
  "nat \<Rightarrow> ('a::Gromov_hyperbolic_space)"
  / partial: "Gromov_completion_rel"
by (rule part_equivp_Gromov_completion_rel)

text \<open>The Gromov completion contains is made of a copy of the original space, and new points
forming the Gromov boundary.\<close>

definition to_Gromov_completion::"('a::Gromov_hyperbolic_space) \<Rightarrow> 'a Gromov_completion"
  where "to_Gromov_completion x = abs_Gromov_completion (\<lambda>n. x)"

definition from_Gromov_completion::"('a::Gromov_hyperbolic_space) Gromov_completion \<Rightarrow> 'a"
  where "from_Gromov_completion = inv to_Gromov_completion"

definition Gromov_boundary::"('a::Gromov_hyperbolic_space) Gromov_completion set"
  where "Gromov_boundary = UNIV - range to_Gromov_completion"

lemma to_Gromov_completion_inj:
  "inj to_Gromov_completion"
proof (rule injI)
  fix x y::'a assume H: "to_Gromov_completion x = to_Gromov_completion y"
  have "Gromov_completion_rel (\<lambda>n. x) (\<lambda>n. y)"
    apply (subst Quotient3_rel[OF Quotient3_Gromov_completion, symmetric])
    using H unfolding to_Gromov_completion_def by auto
  then show "x = y"
    using Gromov_completion_rel_to_const by auto
qed

lemma from_to_Gromov_completion [simp]:
  "from_Gromov_completion (to_Gromov_completion x) = x"
unfolding from_Gromov_completion_def by (simp add: to_Gromov_completion_inj)

lemma to_from_Gromov_completion:
  assumes "x \<notin> Gromov_boundary"
  shows "to_Gromov_completion (from_Gromov_completion x) = x"
using assms to_Gromov_completion_inj unfolding Gromov_boundary_def from_Gromov_completion_def
by (simp add: f_inv_into_f)

lemma not_in_Gromov_boundary:
  assumes "x \<notin> Gromov_boundary"
  shows "\<exists>a. x = to_Gromov_completion a"
using assms unfolding Gromov_boundary_def by auto

lemma not_in_Gromov_boundary' [simp]:
  "to_Gromov_completion x \<notin> Gromov_boundary"
unfolding Gromov_boundary_def by auto

lemma abs_Gromov_completion_in_Gromov_boundary [simp]:
  assumes "Gromov_converging_at_boundary u"
  shows "abs_Gromov_completion u \<in> Gromov_boundary"
using Gromov_completion_rel_to_const Gromov_converging_at_boundary_imp_not_constant'
  Gromov_converging_at_boundary_rel[OF assms]
  Quotient3_rel[OF Quotient3_Gromov_completion] assms not_in_Gromov_boundary to_Gromov_completion_def
  by fastforce

lemma rep_Gromov_completion_to_Gromov_completion [simp]:
  "rep_Gromov_completion (to_Gromov_completion y) = (\<lambda>n. y)"
proof -
  have "Gromov_completion_rel (\<lambda>n. y) (rep_Gromov_completion (abs_Gromov_completion (\<lambda>n. y)))"
    by (metis Gromov_completion_rel_const Quotient3_Gromov_completion rep_abs_rsp)
  then show ?thesis
    unfolding to_Gromov_completion_def using Gromov_completion_rel_to_const' by blast
qed


subsection \<open>Extending the original distance and the original Gromov product to the completion\<close>

text \<open>In this subsection, we extend the Gromov product to the boundary, by taking limits along
sequences tending to the point in the boundary. This does not converge, but it does up to $\delta$,
so for definiteness we use a $\liminf$ over all sequences tending to the boundary point -- one
interest of this definition is that the extended Gromov product still satisfies the hyperbolicity
inequality. One difficulty is that this extended Gromov product can take infinite values (it does
so exactly on the pair $(x,x)$ where $x$ is in the boundary), so we should define this product
in extended nonnegative reals.

We also extend the original distance, by $+\infty$ on the boundary. This is not a really interesting
function, but it will be instrumental below. Again, this extended Gromov distance (not to be mistaken
for the genuine distance we will construct later on on the completion) takes values in extended
nonnegative reals.\<close>


text \<open>To define the extended Gromov product, one takes a limit of the Gromov product along any
sequence, as it does not depend up to $\delta$ on the chosen sequence. However, if one wants to
keep the exact inequality that defines hyperbolicity, but at all points, then using an infimum
is the best choice.\<close>

definition extended_Gromov_product_at::"('a::Gromov_hyperbolic_space) \<Rightarrow> 'a Gromov_completion \<Rightarrow> 'a Gromov_completion \<Rightarrow> ennreal"
  where "extended_Gromov_product_at e x y = Inf {liminf (\<lambda>n. ennreal(Gromov_product_at e (u n) (v n))) |u v. abs_Gromov_completion u = x \<and> abs_Gromov_completion v = y \<and> Gromov_completion_rel u u \<and> Gromov_completion_rel v v}"

definition extended_Gromov_distance::"('a::Gromov_hyperbolic_space) Gromov_completion \<Rightarrow> 'a Gromov_completion \<Rightarrow> ennreal"
  where "extended_Gromov_distance x y =
              (if x \<in> Gromov_boundary \<or> y \<in> Gromov_boundary then \<infinity>
              else ennreal (dist (inv to_Gromov_completion x) (inv to_Gromov_completion y)))"

text \<open>The extended distance and the extended Gromov product are invariant under exchange
of the points, readily from the definition.\<close>

lemma extended_Gromov_distance_commute:
  "extended_Gromov_distance x y = extended_Gromov_distance y x"
  unfolding extended_Gromov_distance_def by (simp add: dist_commute)

lemma extended_Gromov_product_at_commute:
  "extended_Gromov_product_at e x y = extended_Gromov_product_at e y x"
unfolding extended_Gromov_product_at_def
proof (rule arg_cong[of _ _ Inf])
  have "{liminf (\<lambda>n. ennreal (Gromov_product_at e (u n) (v n))) |u v.
          abs_Gromov_completion u = x \<and> abs_Gromov_completion v = y \<and> Gromov_completion_rel u u \<and> Gromov_completion_rel v v} =
        {liminf (\<lambda>n. ennreal (Gromov_product_at e (v n) (u n))) |u v.
          abs_Gromov_completion v = y \<and> abs_Gromov_completion u = x \<and> Gromov_completion_rel v v \<and> Gromov_completion_rel u u}"
    by (auto simp add: Gromov_product_commute)
  then show "{liminf (\<lambda>n. ennreal (Gromov_product_at e (u n) (v n))) |u v.
      abs_Gromov_completion u = x \<and> abs_Gromov_completion v = y \<and> Gromov_completion_rel u u \<and> Gromov_completion_rel v v} =
      {liminf (\<lambda>n. ennreal (Gromov_product_at e (u n) (v n))) |u v.
      abs_Gromov_completion u = y \<and> abs_Gromov_completion v = x \<and> Gromov_completion_rel u u \<and> Gromov_completion_rel v v}"
    by auto
qed

text \<open>Inside the space, the extended distance and the extended Gromov product coincide with the
original ones.\<close>

lemma extended_Gromov_distance_inside [simp]:
  "extended_Gromov_distance (to_Gromov_completion x) (to_Gromov_completion y) = dist x y"
unfolding extended_Gromov_distance_def Gromov_boundary_def by (auto simp add: to_Gromov_completion_inj)

lemma extended_Gromov_product_inside [simp] :
  "extended_Gromov_product_at e (to_Gromov_completion x) (to_Gromov_completion y) = Gromov_product_at e x y"
proof -
  have A: "u = (\<lambda>n. z)" if H: "abs_Gromov_completion u = abs_Gromov_completion (\<lambda>n. z)" "Gromov_completion_rel u u" for u and z::'a
  proof -
    have "Gromov_completion_rel u (\<lambda>n. z)"
      apply (subst Quotient3_rel[OF Quotient3_Gromov_completion, symmetric])
      using H uniformity_dist_class_def by auto
    then show ?thesis using Gromov_completion_rel_to_const by auto
  qed
  then have *: "{u. abs_Gromov_completion u = to_Gromov_completion z \<and> Gromov_completion_rel u u} = {(\<lambda>n. z)}" for z::'a
    unfolding to_Gromov_completion_def by auto
  have **: "{F u v |u v. abs_Gromov_completion u = to_Gromov_completion x \<and> abs_Gromov_completion v = to_Gromov_completion y \<and> Gromov_completion_rel u u \<and> Gromov_completion_rel v v}
      = {F (\<lambda>n. x) (\<lambda>n. y)}" for F::"(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> ennreal"
    using *[of x] *[of y] unfolding extended_Gromov_product_at_def by (auto, smt mem_Collect_eq singletonD)

  have "extended_Gromov_product_at e (to_Gromov_completion x) (to_Gromov_completion y) = Inf {liminf (\<lambda>n. ennreal(Gromov_product_at e ((\<lambda>n. x) n) ((\<lambda>n. y) n)))}"
    unfolding extended_Gromov_product_at_def ** by simp
  also have "... = ennreal(Gromov_product_at e x y)"
    by (auto simp add: Liminf_const)
  finally show "extended_Gromov_product_at e (to_Gromov_completion x) (to_Gromov_completion y) = Gromov_product_at e x y"
    by simp
qed

text \<open>A point in the boundary is at infinite extended distance of everyone, including itself:
the extended distance is obtained by taking the supremum along all sequences tending to this point,
so even for one single point one can take two sequences tending to it at different speeds, which
results in an infinite extended distance.\<close>

lemma extended_Gromov_distance_PInf_boundary [simp]:
  assumes "x \<in> Gromov_boundary"
  shows "extended_Gromov_distance x y = \<infinity>" "extended_Gromov_distance y x = \<infinity>"
unfolding extended_Gromov_distance_def using assms by auto

text \<open>By construction, the extended distance still satisfies the triangle inequality.\<close>

lemma extended_Gromov_distance_triangle [mono_intros]:
  "extended_Gromov_distance x z \<le> extended_Gromov_distance x y + extended_Gromov_distance y z"
proof (cases "x \<in> Gromov_boundary \<or> y \<in> Gromov_boundary \<or> z \<in> Gromov_boundary")
  case True
  then have *: "extended_Gromov_distance x y + extended_Gromov_distance y z = \<infinity>" by auto
  show ?thesis by (simp add: *)
next
  case False
  then obtain a b c where abc: "x = to_Gromov_completion a" "y = to_Gromov_completion b" "z = to_Gromov_completion c"
    unfolding Gromov_boundary_def by auto
  show ?thesis
    unfolding abc using dist_triangle[of a c b] ennreal_leI by fastforce
qed

text \<open>The extended Gromov product can be bounded by the extended distance, just like inside
the space.\<close>

lemma extended_Gromov_product_le_dist [mono_intros]:
  "extended_Gromov_product_at e x y \<le> extended_Gromov_distance (to_Gromov_completion e) x"
proof (cases "x \<in> Gromov_boundary")
  case True
  then show ?thesis by simp
next
  case False
  then obtain a where a: "x = to_Gromov_completion a"
    using not_in_Gromov_boundary by auto
  define v where "v = rep_Gromov_completion y"

  have *: "abs_Gromov_completion (\<lambda>n. a) = x \<and> abs_Gromov_completion v = y \<and> Gromov_completion_rel (\<lambda>n. a) (\<lambda>n. a) \<and> Gromov_completion_rel v v"
    unfolding v_def a to_Gromov_completion_def
    by (auto simp add: Quotient3_rep_reflp[OF Quotient3_Gromov_completion] Quotient3_abs_rep[OF Quotient3_Gromov_completion])
  have "extended_Gromov_product_at e x y \<le> liminf (\<lambda>n. ennreal(Gromov_product_at e a (v n)))"
    unfolding extended_Gromov_product_at_def apply (rule Inf_lower) using * by force
  also have "... \<le> liminf (\<lambda>n. ennreal(dist e a))"
    using Gromov_product_le_dist(1)[of e a] by (auto intro!: Liminf_mono)
  also have "... = ennreal(dist e a)"
    by (simp add: Liminf_const)
  also have "... = extended_Gromov_distance (to_Gromov_completion e) x"
    unfolding a by auto
  finally show ?thesis by auto
qed

lemma extended_Gromov_product_le_dist' [mono_intros]:
  "extended_Gromov_product_at e x y \<le> extended_Gromov_distance (to_Gromov_completion e) y"
using extended_Gromov_product_le_dist[of e y x] by (simp add: extended_Gromov_product_at_commute)

text \<open>The Gromov product inside the space varies by at most the distance when one varies one of
the points. We will need the same statement for the extended Gromov product. The proof is done
using this inequality inside the space, and passing to the limit.\<close>

lemma extended_Gromov_product_at_diff3 [mono_intros]:
  "extended_Gromov_product_at e x y \<le> extended_Gromov_product_at e x z + extended_Gromov_distance y z"
proof (cases "(extended_Gromov_distance y z = \<infinity>) \<or> (extended_Gromov_product_at e x z = \<infinity>)")
  case False
  then have "y \<notin> Gromov_boundary" "z \<notin> Gromov_boundary"
    using extended_Gromov_distance_PInf_boundary by auto
  then obtain b c where b: "y = to_Gromov_completion b" and c: "z = to_Gromov_completion c"
    unfolding Gromov_boundary_def by auto
  have "extended_Gromov_distance y z = ennreal(dist b c)"
    unfolding b c by auto
  have "extended_Gromov_product_at e x y \<le> (extended_Gromov_product_at e x z + extended_Gromov_distance y z) + h" if "h>0" for h
  proof -
    have "\<exists>t\<in>{liminf (\<lambda>n. ennreal(Gromov_product_at e (u n) (w n))) |u w. abs_Gromov_completion u = x
                  \<and> abs_Gromov_completion w = z \<and> Gromov_completion_rel u u \<and> Gromov_completion_rel w w}.
          t < extended_Gromov_product_at e x z + h"
      apply (subst Inf_less_iff[symmetric]) using False \<open>h > 0\<close> unfolding extended_Gromov_product_at_def[symmetric] by auto
    then obtain u w where H: "abs_Gromov_completion u = x" "abs_Gromov_completion w = z"
                          "Gromov_completion_rel u u" "Gromov_completion_rel w w"
                          "liminf (\<lambda>n. ennreal(Gromov_product_at e (u n) (w n))) < extended_Gromov_product_at e x z + h"
      by auto
    then have w: "w n = c" for n
      using c Gromov_completion_rel_to_const Quotient3_Gromov_completion Quotient3_rel to_Gromov_completion_def by fastforce
    define v where v: "v = (\<lambda>n::nat. b)"
    have "abs_Gromov_completion v = y" "Gromov_completion_rel v v"
      unfolding v by (auto simp add: b to_Gromov_completion_def)

    have "Gromov_product_at e (u n) (v n) \<le> Gromov_product_at e (u n) (w n) + dist b c" for n
      unfolding v w using Gromov_product_at_diff3[of e "u n" b c] by auto
    then have *: "ennreal(Gromov_product_at e (u n) (v n)) \<le> ennreal(Gromov_product_at e (u n) (w n)) + extended_Gromov_distance y z" for n
      unfolding \<open>extended_Gromov_distance y z = ennreal(dist b c)\<close> using ennreal_leI by fastforce
    have "extended_Gromov_product_at e x y \<le> liminf(\<lambda>n. ennreal(Gromov_product_at e (u n) (v n)))"
      unfolding extended_Gromov_product_at_def by (rule Inf_lower, auto, rule exI[of _ u], rule exI[of _ v], auto, fact+)
    also have "... \<le> liminf(\<lambda>n. ennreal(Gromov_product_at e (u n) (w n)) + extended_Gromov_distance y z)"
      apply (rule Liminf_mono) using * unfolding eventually_sequentially by auto
    also have "... = liminf(\<lambda>n. ennreal(Gromov_product_at e (u n) (w n))) + extended_Gromov_distance y z"
      by (rule Liminf_add_const, auto)
    also have "... \<le> extended_Gromov_product_at e x z + h + extended_Gromov_distance y z"
      using less_imp_le[OF H(5)] by auto
    finally show ?thesis
      by (simp add: ord_le_eq_trans)
  qed
  then show ?thesis
    using ennreal_le_epsilon ennreal_less_zero_iff by blast
next
  case True
  then show ?thesis
    by (metis ennreal_add_eq_top infinity_ennreal_def top_greatest)
qed

lemma extended_Gromov_product_at_diff2 [mono_intros]:
  "extended_Gromov_product_at e x y \<le> extended_Gromov_product_at e z y + extended_Gromov_distance x z"
using extended_Gromov_product_at_diff3[of e y x z] by (simp add: extended_Gromov_product_at_commute)

lemma extended_Gromov_product_at_diff1 [mono_intros]:
  "extended_Gromov_product_at e x y \<le> extended_Gromov_product_at f x y + dist e f"
proof (cases "extended_Gromov_product_at f x y = \<infinity>")
  case False
  have "extended_Gromov_product_at e x y \<le> (extended_Gromov_product_at f x y + dist e f) + h" if "h>0" for h
  proof -
    have "\<exists>t\<in>{liminf (\<lambda>n. ennreal(Gromov_product_at f (u n) (v n))) |u v. abs_Gromov_completion u = x
                \<and> abs_Gromov_completion v = y \<and> Gromov_completion_rel u u \<and> Gromov_completion_rel v v}.
          t < extended_Gromov_product_at f x y + h"
      apply (subst Inf_less_iff[symmetric]) using False \<open>h > 0\<close> unfolding extended_Gromov_product_at_def[symmetric] by auto
    then obtain u v where H: "abs_Gromov_completion u = x" "abs_Gromov_completion v = y"
                          "Gromov_completion_rel u u" "Gromov_completion_rel v v"
                          "liminf (\<lambda>n. ennreal(Gromov_product_at f (u n) (v n))) < extended_Gromov_product_at f x y + h"
      by auto

    have "Gromov_product_at e (u n) (v n) \<le> Gromov_product_at f (u n) (v n) + dist e f" for n
      using Gromov_product_at_diff1[of e "u n" "v n" f] by auto
    then have *: "ennreal(Gromov_product_at e (u n) (v n)) \<le> ennreal(Gromov_product_at f (u n) (v n)) + dist e f" for n
      using ennreal_leI by fastforce
    have "extended_Gromov_product_at e x y \<le> liminf(\<lambda>n. ennreal(Gromov_product_at e (u n) (v n)))"
      unfolding extended_Gromov_product_at_def by (rule Inf_lower, auto, rule exI[of _ u], rule exI[of _ v], auto, fact+)
    also have "... \<le> liminf(\<lambda>n. ennreal(Gromov_product_at f (u n) (v n)) + dist e f)"
      apply (rule Liminf_mono) using * unfolding eventually_sequentially by auto
    also have "... = liminf(\<lambda>n. ennreal(Gromov_product_at f (u n) (v n))) + dist e f"
      by (rule Liminf_add_const, auto)
    also have "... \<le> extended_Gromov_product_at f x y + h + dist e f"
      using less_imp_le[OF H(5)] by auto
    finally show ?thesis
      by (simp add: ord_le_eq_trans)
  qed
  then show ?thesis
    using ennreal_le_epsilon ennreal_less_zero_iff by blast
next
  case True
  then show ?thesis
    by (metis ennreal_add_eq_top infinity_ennreal_def top_greatest)
qed

text \<open>A point in the Gromov boundary is represented by a sequence tending to infinity and
converging in the Gromov boundary, essentially by definition.\<close>

lemma Gromov_boundary_abs_converging:
  assumes "x \<in> Gromov_boundary" "abs_Gromov_completion u = x" "Gromov_completion_rel u u"
  shows "Gromov_converging_at_boundary u"
proof -
  have "Gromov_converging_at_boundary u \<or> (\<forall>m n. u n = u m)"
    using assms unfolding Gromov_completion_rel_def by auto
  moreover have "\<not>(\<forall>m n. u n = u m)"
  proof (rule ccontr, simp)
    assume *: "\<forall>m n. u n = u m"
    define z where "z = u 0"
    then have z: "u = (\<lambda>n. z)"
      using * by auto
    then have "x = to_Gromov_completion z"
      using assms unfolding z to_Gromov_completion_def by auto
    then show False using \<open>x \<in> Gromov_boundary\<close> unfolding Gromov_boundary_def by auto
  qed
  ultimately show ?thesis by auto
qed

lemma Gromov_boundary_rep_converging:
  assumes "x \<in> Gromov_boundary"
  shows "Gromov_converging_at_boundary (rep_Gromov_completion x)"
apply (rule Gromov_boundary_abs_converging[OF assms])
using Quotient3_Gromov_completion Quotient3_abs_rep Quotient3_rep_reflp by fastforce+

text \<open>We can characterize the points for which the Gromov product is infinite: they have to be
the same point, at infinity. This is essentially equivalent to the definition of the Gromov
completion, but there is some boilerplate to get the proof working.\<close>

lemma Gromov_boundary_extended_product_PInf:
  "extended_Gromov_product_at e x y = \<infinity> \<longleftrightarrow> (x \<in> Gromov_boundary \<and> y = x)"
proof
  fix x y::"'a Gromov_completion" assume "x \<in> Gromov_boundary \<and> y = x"
  then have H: "y = x" "x \<in> Gromov_boundary" by auto
  have "liminf (\<lambda>n. ennreal (Gromov_product_at e (u n) (v n))) = \<infinity>" if
                  "abs_Gromov_completion u = x" "abs_Gromov_completion v = y"
                  "Gromov_completion_rel u u" "Gromov_completion_rel v v" for u v
  proof -
    have "Gromov_converging_at_boundary u" "Gromov_converging_at_boundary v"
      using Gromov_boundary_abs_converging that H by auto
    have "Gromov_completion_rel u v" using that \<open>y = x\<close>
      using Quotient3_rel[OF Quotient3_Gromov_completion] by fastforce
    then have "(\<lambda>n. Gromov_product_at e (u n) (v n)) \<longlonglongrightarrow> \<infinity>"
      unfolding Gromov_completion_rel_def using Gromov_converging_at_boundary_imp_not_constant'[OF \<open>Gromov_converging_at_boundary u\<close>] by auto
    then have "(\<lambda>n. e2ennreal (ereal (Gromov_product_at e (u n) (v n)))) \<longlonglongrightarrow> e2ennreal(\<infinity>)"
      by (intro tendsto_intros, simp)
    then have "(\<lambda>n. ennreal (Gromov_product_at e (u n) (v n))) \<longlonglongrightarrow> \<infinity>"
      by auto
    then show ?thesis
      by (simp add: tendsto_iff_Liminf_eq_Limsup)
  qed
  then show "extended_Gromov_product_at e x y = \<infinity>"
    unfolding extended_Gromov_product_at_def by auto
next
  fix x y::"'a Gromov_completion" assume H: "extended_Gromov_product_at e x y = \<infinity>"
  then have "extended_Gromov_distance (to_Gromov_completion e) x = \<infinity>"
    using extended_Gromov_product_le_dist[of e x y] neq_top_trans by auto
  then have "x \<in> Gromov_boundary"
    by (metis extended_Gromov_distance_def infinity_ennreal_def not_in_Gromov_boundary' top_neq_ennreal)
  have "extended_Gromov_distance (to_Gromov_completion e) y = \<infinity>"
    using extended_Gromov_product_le_dist[of e y x] neq_top_trans H by (auto simp add: extended_Gromov_product_at_commute)
  then have "y \<in> Gromov_boundary"
    by (metis extended_Gromov_distance_def infinity_ennreal_def not_in_Gromov_boundary' top_neq_ennreal)
  define u where "u = rep_Gromov_completion x"
  define v where "v = rep_Gromov_completion y"
  have A: "Gromov_converging_at_boundary u" "Gromov_converging_at_boundary v"
    unfolding u_def v_def using \<open>x \<in> Gromov_boundary\<close> \<open>y \<in> Gromov_boundary\<close>
    by (auto simp add: Gromov_boundary_rep_converging)

  have "abs_Gromov_completion u = x \<and> abs_Gromov_completion v = y \<and> Gromov_completion_rel u u \<and> Gromov_completion_rel v v"
    unfolding u_def v_def
    using Quotient3_abs_rep[OF Quotient3_Gromov_completion] Quotient3_rep_reflp[OF Quotient3_Gromov_completion] by auto
  then have "extended_Gromov_product_at e x y \<le> liminf (\<lambda>n. ennreal(Gromov_product_at e (u n) (v n)))"
    unfolding extended_Gromov_product_at_def by (auto intro!: Inf_lower)
  then have "(\<lambda>n. ennreal(Gromov_product_at e (u n) (v n))) \<longlonglongrightarrow> \<infinity>"
    by (metis (no_types, lifting) H Liminf_le_Limsup infinity_ennreal_def neq_top_trans sequentially_bot tendsto_iff_Liminf_eq_Limsup)
  then have "(\<lambda>n. enn2ereal(ennreal(Gromov_product_at e (u n) (v n)))) \<longlonglongrightarrow> enn2ereal(\<infinity>)"
    by (intro tendsto_intros, simp)
  then have "(\<lambda>n. ereal(Gromov_product_at e (u n) (v n))) \<longlonglongrightarrow> \<infinity>"
    unfolding enn2ereal_ennreal[OF Gromov_product_nonneg] by auto
  then have "(\<lambda>n. ereal(Gromov_product_at a (u n) (v n))) \<longlonglongrightarrow> \<infinity>" for a
    using Gromov_product_tendsto_PInf_a_b by auto

  then have "Gromov_completion_rel u v"
    unfolding Gromov_completion_rel_def using A by auto
  then have "abs_Gromov_completion u = abs_Gromov_completion v"
    using Quotient3_rel_abs[OF Quotient3_Gromov_completion] by auto
  then have "x = y"
    unfolding u_def v_def Quotient3_abs_rep[OF Quotient3_Gromov_completion] by auto
  then show "x \<in> Gromov_boundary \<and> y = x"
    using \<open>x \<in> Gromov_boundary\<close> by auto
qed

text \<open>As for points inside the space, we deduce that the extended Gromov product between $x$ and $x$
is just the extended distance to the basepoint.\<close>

lemma extended_Gromov_product_e_x_x [simp]:
  "extended_Gromov_product_at e x x = extended_Gromov_distance (to_Gromov_completion e) x"
proof (cases "x \<in> Gromov_boundary")
  case True
  then show ?thesis using Gromov_boundary_extended_product_PInf by auto
next
  case False
  then obtain a where a: "x = to_Gromov_completion a"
    unfolding Gromov_boundary_def by auto
  show ?thesis
    unfolding a by auto
qed

text \<open>The inequality in terms of Gromov products characterizing hyperbolicity extends in the
same form to the Gromov completion, by taking limits of this inequality in the space.\<close>

lemma extended_hyperb_ineq [mono_intros]:
  "extended_Gromov_product_at (e::'a::Gromov_hyperbolic_space) x z \<ge>
      min (extended_Gromov_product_at e x y) (extended_Gromov_product_at e y z) - deltaG(TYPE('a))"
proof -
  have "min (extended_Gromov_product_at e x y) (extended_Gromov_product_at e y z) - deltaG(TYPE('a)) \<le>
    Inf {liminf (\<lambda>n. ennreal (Gromov_product_at e (u n) (v n))) |u v.
            abs_Gromov_completion u = x \<and> abs_Gromov_completion v = z \<and> Gromov_completion_rel u u \<and> Gromov_completion_rel v v}"
  proof (rule cInf_greatest, auto)
    define u where "u = rep_Gromov_completion x"
    define w where "w = rep_Gromov_completion z"
    have "abs_Gromov_completion u = x \<and> abs_Gromov_completion w = z \<and> Gromov_completion_rel u u \<and> Gromov_completion_rel w w"
      unfolding u_def w_def
      using Quotient3_abs_rep[OF Quotient3_Gromov_completion] Quotient3_rep_reflp[OF Quotient3_Gromov_completion] by auto
    then show "\<exists>t u. Gromov_completion_rel u u \<and>
            (\<exists>v. abs_Gromov_completion v = z \<and> abs_Gromov_completion u = x \<and> t = liminf (\<lambda>n. ennreal (Gromov_product_at e (u n) (v n))) \<and> Gromov_completion_rel v v)"
      by auto
  next
    fix u w assume H: "x = abs_Gromov_completion u" "z = abs_Gromov_completion w"
                      "Gromov_completion_rel u u" "Gromov_completion_rel w w"
    define v where "v = rep_Gromov_completion y"
    have Y: "y = abs_Gromov_completion v" "Gromov_completion_rel v v"
      unfolding v_def
      by (auto simp add: Quotient3_abs_rep[OF Quotient3_Gromov_completion] Quotient3_rep_reflp[OF Quotient3_Gromov_completion])

    have *: "min (ennreal(Gromov_product_at e (u n) (v n))) (ennreal(Gromov_product_at e (v n) (w n))) \<le> ennreal(Gromov_product_at e (u n) (w n)) + deltaG(TYPE('a))" for n
      apply (subst min_ennreal, auto)
      apply (subst ennreal_plus[symmetric], simp, simp)
      apply (rule ennreal_leI)
      using hyperb_ineq[of e "u n" "v n" "w n"] by auto

    have "extended_Gromov_product_at e (abs_Gromov_completion u) y \<le> liminf (\<lambda>n. ennreal(Gromov_product_at e (u n) (v n)))"
      unfolding extended_Gromov_product_at_def using Y H by (auto intro!: Inf_lower)
    moreover have "extended_Gromov_product_at e y (abs_Gromov_completion w) \<le> liminf (\<lambda>n. ennreal(Gromov_product_at e (v n) (w n)))"
      unfolding extended_Gromov_product_at_def using Y H by (auto intro!: Inf_lower)
    ultimately have "min (extended_Gromov_product_at e (abs_Gromov_completion u) y) (extended_Gromov_product_at e y (abs_Gromov_completion w))
      \<le> min (liminf (\<lambda>n. ennreal(Gromov_product_at e (u n) (v n)))) (liminf (\<lambda>n. ennreal(Gromov_product_at e (v n) (w n))))"
      by (intro mono_intros, auto)
    also have "... = liminf (\<lambda>n. min (ennreal(Gromov_product_at e (u n) (v n))) (ennreal(Gromov_product_at e (v n) (w n))))"
      by (rule Liminf_min_eq_min_Liminf[symmetric])
    also have "... \<le> liminf (\<lambda>n. ennreal(Gromov_product_at e (u n) (w n)) + deltaG(TYPE('a)))"
      using * by (auto intro!: Liminf_mono)
    also have "... = liminf (\<lambda>n. ennreal(Gromov_product_at e (u n) (w n))) + deltaG(TYPE('a))"
      by (auto intro!: Liminf_add_const)
    finally show "min (extended_Gromov_product_at e (abs_Gromov_completion u) y) (extended_Gromov_product_at e y (abs_Gromov_completion w)) - ennreal (deltaG TYPE('a))
                  \<le> liminf (\<lambda>n. ennreal (Gromov_product_at e (u n) (w n)))"
      by (simp add: add.commute ennreal_minus_le_iff)
  qed
  then show ?thesis unfolding extended_Gromov_product_at_def by auto
qed

lemma extended_hyperb_ineq' [mono_intros]:
  "extended_Gromov_product_at (e::'a::Gromov_hyperbolic_space) x z + deltaG(TYPE('a))\<ge>
      min (extended_Gromov_product_at e x y) (extended_Gromov_product_at e y z)"
using extended_hyperb_ineq[of e x y z] unfolding ennreal_minus_le_iff by (simp add: add.commute)

lemma extended_hyperb_ineq_4_points' [mono_intros]:
  "Min {extended_Gromov_product_at (e::'a::Gromov_hyperbolic_space) x y, extended_Gromov_product_at e y z, extended_Gromov_product_at e z t} \<le> extended_Gromov_product_at e x t + 2 * deltaG(TYPE('a))"
proof -
  have *: "ennreal(2 * z) = ennreal z + ennreal z" for z
    by (metis (no_types, hide_lams) BitM_plus_one add.left_neutral add.right_neutral add_mono_thms_linordered_field(5) ennreal_eq_0_iff ennreal_plus less_eq_real_def linorder_not_le mult_2_right order_less_irrefl order_trans_rules(23) semiring_normalization_rules(7))
  have "min (extended_Gromov_product_at e x y + 0) (min (extended_Gromov_product_at e y z) (extended_Gromov_product_at e z t))
        \<le> min (extended_Gromov_product_at e x y + deltaG(TYPE('a))) (extended_Gromov_product_at e y t + deltaG(TYPE('a))) "
    by (intro mono_intros)
  also have "... = min (extended_Gromov_product_at e x y) (extended_Gromov_product_at e y t) + deltaG(TYPE('a))"
    by (simp add: min_def)
  also have "... \<le> (extended_Gromov_product_at e x t + deltaG(TYPE('a))) + deltaG(TYPE('a))"
    by (intro mono_intros)
  finally show ?thesis unfolding * by (auto simp add: algebra_simps)
qed

lemma extended_hyperb_ineq_4_points [mono_intros]:
  "Min {extended_Gromov_product_at (e::'a::Gromov_hyperbolic_space) x y, extended_Gromov_product_at e y z, extended_Gromov_product_at e z t} - 2 * deltaG(TYPE('a)) \<le> extended_Gromov_product_at e x t"
using extended_hyperb_ineq_4_points'[of e x y z] unfolding ennreal_minus_le_iff by (simp add: add.commute)


subsection \<open>Construction of the distance on the Gromov completion\<close>

text \<open>We want now to define the natural topology of the Gromov completion. Most textbooks
first define a topology on $\partial X$, or sometimes on
$X \cup \partial X$, and then much later a distance on $\partial X$ (but they never do the tedious
verification that the distance defines the same topology as the topology defined before). I have
not seen one textbook defining a distance on $X \cup \partial X$. It turns out that one can in fact
define a distance on $X \cup \partial X$, whose restriction to $\partial X$ is the usual distance
on the Gromov boundary, and define the topology of $X \cup \partial X$ using it. For formalization
purposes, this is very convenient as topologies defined with distances are automatically nice and
tractable (no need to check separation axioms, for instance). The price to pay is that, once
we have defined the distance, we have to check that it defines the right notion of convergence
one expects.

What we would like to take for the distance is
$d(x,y) = e^{-(x,y)_o}$, where $o$ is some fixed basepoint in the space. However, this
does not behave like a distance at small scales (but it is essentially the right thing at large
scales), and it does not really satisfy the triangle inequality. However, $e^{-\epsilon (x,y)_o}$
almost satisfies the triangle inequality if $\epsilon$ is small enough, i.e., it is equivalent
to a function satisfying the triangle inequality. This gives a genuine distance on the boundary,
but not inside the space as it does not vanish on pairs $(x,x)$.

A third try would be to take $d(x,y) = \min(\tilde d(x,y), e^{-\epsilon (x,y)_o})$ where
$\tilde d$ is the natural extension of $d$ to the Gromov completion (it is infinite if $x$ or $y$
belongs to the boundary). However, we can not prove that it is equivalent to a distance.

Finally, it works with $d(x,y) \asymp \min(\tilde d(x,y)^{1/2}, e^{-\epsilon (x,y)_o}$. This is
what we will prove below. To construct the distance, we use the results proved in
the locale \verb+Turn_into_distance+. For this, we need to check that our quasi-distance
satisfies a weird version of the triangular inequality.

All this construction depends on a basepoint, that we fix arbitrarily once and for all.
\<close>

definition epsilonG::"('a::Gromov_hyperbolic_space) itself \<Rightarrow> real"
  where "epsilonG _ = ln 2 / (2+2*deltaG(TYPE('a)))"

definition basepoint::"'a"
  where "basepoint = (SOME a. True)"

definition extended_predist::"('a::Gromov_hyperbolic_space) Gromov_completion \<Rightarrow> 'a Gromov_completion \<Rightarrow> real"
  where "extended_predist x y = enn2real(min (esqrt (extended_Gromov_distance x y))
          (eexp (- enn2ereal(epsilonG(TYPE('a)) * extended_Gromov_product_at basepoint x y))))"

lemma extended_predist_ennreal:
  "ennreal (extended_predist x (y::('a::Gromov_hyperbolic_space) Gromov_completion)) = min (esqrt (extended_Gromov_distance x y))
          (eexp (- enn2ereal(epsilonG(TYPE('a)) * extended_Gromov_product_at basepoint x y)))"
unfolding extended_predist_def apply (subst ennreal_enn2real, auto)
by (metis eexp_le1 enn2ereal_nonneg ennreal_1 ennreal_neq_top ereal_uminus_le_0_iff min.strict_coboundedI2 neq_top_trans top.not_eq_extremum)

lemma constant_in_extended_predist_pos [simp]:
  "epsilonG(TYPE('a::Gromov_hyperbolic_space)) > 0"
  "epsilonG(TYPE('a::Gromov_hyperbolic_space)) \<ge> 0"
  "ennreal (epsilonG(TYPE('a))) * top = top"
proof -
  have *: "2+2*deltaG(TYPE('a)) \<ge> 2 + 2 * 0"
    by (intro mono_intros, auto)
  show **: "epsilonG(TYPE('a)) > 0"
    unfolding epsilonG_def apply (auto simp add: divide_simps) using * by auto
  then show "ennreal (epsilonG(TYPE('a))) * top = top"
    using ennreal_mult_top by auto
  show "epsilonG(TYPE('a::Gromov_hyperbolic_space)) \<ge> 0"
    using ** by simp
qed

lemma extended_predist_nonneg [simp]:
  "extended_predist x y \<ge> 0"
unfolding extended_predist_def by auto

lemma extended_predist_commute:
  "extended_predist x y = extended_predist y x"
unfolding extended_predist_def by (simp add: extended_Gromov_distance_commute extended_Gromov_product_at_commute)

lemma extended_predist_self0 [simp]:
  "extended_predist x y = 0 \<longleftrightarrow> x = y"
proof (auto)
  show "extended_predist y y = 0"
  proof (cases "y \<in> Gromov_boundary")
    case True
    then have *: "extended_Gromov_product_at basepoint y y = \<infinity>"
      using Gromov_boundary_extended_product_PInf by auto
    show ?thesis unfolding extended_predist_def * by (auto simp add: min_def)
  next
    case False
    then obtain a where *: "y = to_Gromov_completion a"
      using not_in_Gromov_boundary by auto
    show ?thesis unfolding extended_predist_def * by (auto simp add: min_def)
  qed
  assume "extended_predist x y = 0"
  then have "esqrt (extended_Gromov_distance x y) = 0 \<or> eexp (- enn2ereal(epsilonG(TYPE('a)) * extended_Gromov_product_at basepoint x y)) = 0"
    unfolding extended_predist_def apply auto
    by (metis eexp_le1 eexp_special_values(1) enn2ereal_eq_top_iff enn2ereal_nonneg enn2real_eq_0_iff ennreal_1 ereal_uminus_eq_iff ereal_uminus_le_0_iff min_def neq_top_trans top_neq_ennreal)
  then show "x = y"
  proof
    assume "esqrt (extended_Gromov_distance x y) = 0"
    then have *: "extended_Gromov_distance x y = 0"
      using esqrt_strict_mono strict_mono_eq by fastforce
    then have "\<not>(x \<in> Gromov_boundary)" "\<not>(y \<in> Gromov_boundary)" by auto
    then obtain a b where ab: "x = to_Gromov_completion a" "y = to_Gromov_completion b"
      unfolding Gromov_boundary_def by auto
    have "a = b" using * unfolding ab by auto
    then show "x = y" using ab by auto
  next
    assume "eexp (- enn2ereal (epsilonG(TYPE('a)) * extended_Gromov_product_at basepoint x y)) = 0"
    then have "extended_Gromov_product_at basepoint x y = \<infinity>"
      by (auto simp add: ennreal_mult_eq_top_iff)
    then show "x = y"
      using Gromov_boundary_extended_product_PInf[of basepoint x y] by auto
  qed
qed

lemma extended_predist_le1 [simp]:
  "extended_predist x y \<le> 1"
unfolding extended_predist_def by (simp add: enn2real_leI min_le_iff_disj)

lemma extended_predist_weak_triangle:
  "extended_predist x z \<le> sqrt 2 * max (extended_predist x y) (extended_predist y z)"
proof -
  have "esqrt 2 = eexp (ereal(ln 2/2))"
    unfolding ennreal_sqrt2[symmetric] by auto (metis exp_ln_iff ln_sqrt real_sqrt_gt_0_iff zero_less_numeral)

  have A: "eexp(enn2ereal (ennreal(epsilonG TYPE('a)) * 1)) \<le> esqrt 2"
    apply (simp del:eexp.simps)
    unfolding epsilonG_def \<open>esqrt 2 = eexp (ereal(ln 2/2))\<close>
    apply (auto simp add: algebra_simps divide_simps intro!: mono_intros)
    using delta_nonneg[where ?'a = 'a] by auto

  text \<open>We have to show an inequality $d(x, z) \leq \sqrt{2} \max(d(x,y), d(y,z))$. Each of $d(x,y)$
  and $d(y,z)$ is either the extended distance, or the exponential of minus the Gromov product,
  depending on which is smaller. We split according to the four cases.\<close>

  have "(esqrt (extended_Gromov_distance x y) \<le> eexp (- enn2ereal(epsilonG(TYPE('a)) * extended_Gromov_product_at basepoint x y))
        \<or> esqrt (extended_Gromov_distance x y) \<ge> eexp (- enn2ereal(epsilonG(TYPE('a)) * extended_Gromov_product_at basepoint x y)))
        \<and>
      ((esqrt (extended_Gromov_distance y z) \<le> eexp (- enn2ereal(epsilonG(TYPE('a)) * extended_Gromov_product_at basepoint y z))
        \<or> esqrt (extended_Gromov_distance y z) \<ge> eexp (- enn2ereal(epsilonG(TYPE('a)) * extended_Gromov_product_at basepoint y z))))"
    by auto
  then have "ennreal(extended_predist x z) \<le> esqrt 2 * max (ennreal(extended_predist x y)) (ennreal (extended_predist y z))"
  proof (auto)

    text \<open>First, consider the case where the minimum is the extended distance for both cases.
    Then $ed(x,z) \leq ed(x,y) + ed(y,z) \leq 2 \max(ed(x,y), ed(y,z))$. Therefore, $ed(x,z)^{1/2}
    \leq \sqrt{2} \max(ed(x,y)^{1/2}, ed(y,z)^{1/2})$. As predist is defined using
    the square root of $ed$, this readily gives the result.\<close>
    assume H: "esqrt (extended_Gromov_distance x y) \<le> eexp (- enn2ereal (epsilonG(TYPE('a)) * extended_Gromov_product_at basepoint x y))"
              "esqrt (extended_Gromov_distance y z) \<le> eexp (- enn2ereal (epsilonG(TYPE('a)) * extended_Gromov_product_at basepoint y z))"
    have "extended_Gromov_distance x z \<le> extended_Gromov_distance x y + extended_Gromov_distance y z"
      by (rule extended_Gromov_distance_triangle)
    also have "... \<le> 2 * max (extended_Gromov_distance x y) (extended_Gromov_distance y z)"
      by (simp add: add_mono mult_2)
    finally have "esqrt (extended_Gromov_distance x z) \<le> esqrt (2 * max (extended_Gromov_distance x y) (extended_Gromov_distance y z))"
      by (intro mono_intros)
    also have "... = esqrt 2 * max (esqrt (extended_Gromov_distance x y)) (esqrt (extended_Gromov_distance y z))"
      by (auto simp add: esqrt_mult max_of_mono[OF esqrt_mono])
    finally show ?thesis unfolding extended_predist_ennreal min_def using H by auto

  next
    text \<open>Next, consider the case where the minimum comes from the Gromov product for both cases.
    Then, the conclusion will come for the hyperbolicity inequality (which is valid in the Gromov
    completion as well). There is an additive loss of $\delta$ in this inequality, which is converted
    to a multiplicative loss after taking the exponential to get the distance. Since, in the formula
    for the distance, the Gromov product is multiplied by a constant $\epsilon$ by design, the loss
    we get in the end is $\exp(\delta \epsilon)$. The precise value of $\epsilon$ we have taken is
    designed so that this is at most $\sqrt{2}$, giving the desired conclusion.\<close>
    assume H: "eexp (- enn2ereal (ennreal (epsilonG TYPE('a)) * extended_Gromov_product_at basepoint x y)) \<le> esqrt (extended_Gromov_distance x y)"
              "eexp (- enn2ereal (ennreal (epsilonG TYPE('a)) * extended_Gromov_product_at basepoint y z)) \<le> esqrt (extended_Gromov_distance y z)"

    text \<open>First, check that $\epsilon$ and $\delta$ satisfy the required inequality
    $\exp(\epsilon \delta) \leq \sqrt{2}$ (but in the extended reals as this is what we will use.\<close>
    have B: "eexp (epsilonG(TYPE('a)) * deltaG(TYPE('a))) \<le> esqrt 2"
      unfolding epsilonG_def \<open>esqrt 2 = eexp (ereal(ln 2/2))\<close>
      apply (auto simp add: algebra_simps divide_simps intro!: mono_intros)
      using delta_nonneg[where ?'a = 'a] by auto

    text \<open>We start the computation. First, use the hyperbolicity inequality.\<close>
    have "eexp (- enn2ereal (ennreal (epsilonG TYPE('a)) * extended_Gromov_product_at basepoint x z))
      \<le> eexp (- enn2ereal (ennreal (epsilonG TYPE('a)) * (min (extended_Gromov_product_at basepoint x y) (extended_Gromov_product_at basepoint y z) - deltaG(TYPE('a)))))"
      by (intro mono_intros, auto simp add: extended_hyperb_ineq)
    text \<open>Use distributivity to isolate the term $\epsilon \delta$.
    This is not so trivial as we are in ennreal, where $a-b+b$ is not always equal to $a$, so the
    justification requires some work.\<close>
    also have "... \<le> eexp (- enn2ereal (ennreal (epsilonG TYPE('a)) * min (extended_Gromov_product_at basepoint x y) (extended_Gromov_product_at basepoint y z))
            + enn2ereal(ennreal (epsilonG TYPE('a) * deltaG TYPE('a))))"
      apply (intro mono_intros)
      apply (subst ennreal_right_diff_distrib, simp)
      apply (subst ennreal_mult'[symmetric], simp)
      apply (intro mono_intros)
      done
    text \<open>Use multiplicativity of exponential to extract the multiplicative error factor.\<close>
    also have "... = eexp(- enn2ereal (ennreal (epsilonG TYPE('a)) * (min (extended_Gromov_product_at basepoint x y) (extended_Gromov_product_at basepoint y z))))
                    * eexp(epsilonG(TYPE('a))* deltaG(TYPE('a)))"
      apply (subst enn2ereal_ennreal, simp) by (rule eexp_add_mult, auto)
    text \<open>Extract the min outside of the exponential, using that all functions are monotonic.\<close>
    also have "... = eexp(epsilonG(TYPE('a))* deltaG(TYPE('a)))
                    * (max (eexp(- enn2ereal (ennreal (epsilonG TYPE('a)) * extended_Gromov_product_at basepoint x y)))
                           (eexp(- enn2ereal (ennreal (epsilonG TYPE('a)) * extended_Gromov_product_at basepoint y z))))"
      apply (subst min_of_mono[symmetric, of "\<lambda>t. enn2ereal(ennreal (epsilonG TYPE('a)) * t)"])
      apply (meson less_eq_ennreal.rep_eq mono_def mult_left_mono zero_le)
      apply (subst max_of_antimono[of "\<lambda> (t::ereal). -t", symmetric])
      apply (simp add: antimonoI)
      apply (subst max_of_mono[OF eexp_mono])
      apply (simp add: mult.commute)
      done
    text \<open>We recognize the distance of $x$ to $y$ and the distance from $y$ to $z$ on the right.\<close>
    also have "... = eexp(epsilonG(TYPE('a)) * deltaG(TYPE('a))) * (max (ennreal(extended_predist x y)) (ennreal(extended_predist y z)))"
      unfolding extended_predist_ennreal min_def using H by auto
    also have "... \<le> esqrt 2 * max (ennreal(extended_predist x y)) (ennreal(extended_predist y z))"
      by (intro mono_intros B, auto)
    finally show ?thesis unfolding extended_predist_ennreal min_def by auto

  next
    text \<open>Next consider the case where $d(x,y)$ comes from the exponential of minus the Gromov product,
    but $d(y,z)$ comes from their extended distance. Then $d(y,z) \leq 1$ (as $d(y,z)$ is smaller
    then the exponential of minus the Gromov distance, which is at most $1$), and this is all we use:
    the Gromov product between $x$ and $y$ or $x$ and $z$ differ by at most the distance from $y$ to $z$,
    i.e., $1$. Then the result follows directly as $\exp(\epsilon) \leq \sqrt{2}$, by the choice of
    $\epsilon$.\<close>
    assume H: "eexp (- enn2ereal (ennreal (epsilonG TYPE('a)) * extended_Gromov_product_at basepoint x y)) \<le> esqrt (extended_Gromov_distance x y)"
              "esqrt (extended_Gromov_distance y z) \<le> eexp (- enn2ereal (ennreal (epsilonG TYPE('a)) * extended_Gromov_product_at basepoint y z))"
    then have "esqrt(extended_Gromov_distance y z) \<le> 1"
      using eexp_le1 enn2ereal_nonneg ereal_uminus_le_0_iff order_trans by blast
    then have "extended_Gromov_distance y z \<le> 1"
      by (metis antisym esqrt_mono2 esqrt_simps(2) esqrt_strict_mono le_cases strict_mono_eq)

    have "ennreal(extended_predist x z) \<le> eexp(- enn2ereal (ennreal (epsilonG TYPE('a)) * extended_Gromov_product_at basepoint x z))"
      unfolding extended_predist_ennreal min_def by auto
    also have "... \<le> eexp(-enn2ereal (ennreal (epsilonG TYPE('a)) * extended_Gromov_product_at basepoint x y)
                          + enn2ereal (ennreal(epsilonG TYPE('a)) * extended_Gromov_distance y z))"
      apply (intro mono_intros, auto simp add: plus_ennreal.rep_eq[symmetric], intro mono_intros)
      using extended_Gromov_product_at_diff3[of basepoint x y z] unfolding distrib_left[symmetric]
      by (auto intro!: mono_intros)
    also have "... \<le> eexp(-enn2ereal (ennreal (epsilonG TYPE('a)) * extended_Gromov_product_at basepoint x y) + enn2ereal (ennreal(epsilonG TYPE('a)) * 1))"
      by (intro mono_intros, fact)
    also have "... = eexp(-enn2ereal (ennreal (epsilonG TYPE('a)) * extended_Gromov_product_at basepoint x y)) * eexp(enn2ereal (ennreal(epsilonG TYPE('a)) * 1))"
      by (rule eexp_add_mult, auto)
    also have "... \<le> eexp(-enn2ereal (ennreal (epsilonG TYPE('a)) * extended_Gromov_product_at basepoint x y)) * esqrt 2"
      by (intro mono_intros A, auto)
    also have "... = esqrt 2 * ennreal(extended_predist x y)"
      unfolding extended_predist_ennreal min_def using H by (auto simp add: mult.commute)
    also have "... \<le> esqrt 2 * max (ennreal(extended_predist x y)) (ennreal(extended_predist y z))"
      unfolding max_def by (auto intro!: mono_intros)
    finally show ?thesis by auto

  next
    text \<open>The last case is the symmetric of the previous one, and is proved similarly.\<close>
    assume H: "esqrt (extended_Gromov_distance x y) \<le> eexp (- enn2ereal (ennreal (epsilonG TYPE('a)) * extended_Gromov_product_at basepoint x y))"
              "eexp (- enn2ereal (ennreal (epsilonG TYPE('a)) * extended_Gromov_product_at basepoint y z)) \<le> esqrt (extended_Gromov_distance y z)"
    then have "esqrt(extended_Gromov_distance x y) \<le> 1"
      using eexp_le1 enn2ereal_nonneg ereal_uminus_le_0_iff order_trans by blast
    then have "extended_Gromov_distance x y \<le> 1"
      by (metis antisym esqrt_mono2 esqrt_simps(2) esqrt_strict_mono le_cases strict_mono_eq)

    have "ennreal(extended_predist x z) \<le> eexp(- enn2ereal (ennreal (epsilonG TYPE('a)) * extended_Gromov_product_at basepoint x z))"
      unfolding extended_predist_ennreal min_def by auto
    also have "... \<le> eexp(-enn2ereal (ennreal (epsilonG TYPE('a)) * extended_Gromov_product_at basepoint y z)
                          + enn2ereal (ennreal(epsilonG TYPE('a)) * extended_Gromov_distance x y))"
      apply (intro mono_intros, auto simp add: plus_ennreal.rep_eq[symmetric], intro mono_intros)
      using extended_Gromov_product_at_diff3[of basepoint z y x] unfolding distrib_left[symmetric]
      by (auto intro!: mono_intros simp add: extended_Gromov_distance_commute extended_Gromov_product_at_commute)
    also have "... \<le> eexp(-enn2ereal (ennreal (epsilonG TYPE('a)) * extended_Gromov_product_at basepoint y z) + enn2ereal (ennreal(epsilonG TYPE('a)) * 1))"
      by (intro mono_intros, fact)
    also have "... = eexp(-enn2ereal (ennreal (epsilonG TYPE('a)) * extended_Gromov_product_at basepoint y z)) * eexp(enn2ereal (ennreal(epsilonG TYPE('a)) * 1))"
      by (rule eexp_add_mult, auto)
    also have "... \<le> eexp(-enn2ereal (ennreal (epsilonG TYPE('a)) * extended_Gromov_product_at basepoint y z)) * esqrt 2"
      by (intro mono_intros A, auto)
    also have "... = esqrt 2 * ennreal(extended_predist y z)"
      unfolding extended_predist_ennreal min_def using H by (auto simp add: mult.commute)
    also have "... \<le> esqrt 2 * max (ennreal(extended_predist x y)) (ennreal(extended_predist y z))"
      unfolding max_def by (auto intro!: mono_intros)
    finally show ?thesis by auto
  qed

  then show "extended_predist x z \<le> sqrt 2 * max (extended_predist x y) (extended_predist y z)"
    unfolding ennreal_sqrt2[symmetric] max_of_mono[OF ennreal_mono']
    by (metis ennreal_le_iff ennreal_mult' extended_predist_nonneg le_max_iff_disj mult_eq_0_iff mult_left_mono real_sqrt_ge_0_iff zero_le_numeral)
qed

instantiation Gromov_completion :: (Gromov_hyperbolic_space) metric_space
begin

definition dist_Gromov_completion::"('a::Gromov_hyperbolic_space) Gromov_completion \<Rightarrow> 'a Gromov_completion \<Rightarrow> real"
  where "dist_Gromov_completion = turn_into_distance extended_predist"

text \<open>To define a metric space in the current library of Isabelle/HOL, one should also introduce
a uniformity structure and a topology, as follows (they are prescribed by the distance):\<close>

definition uniformity_Gromov_completion::"(('a Gromov_completion) \<times> ('a Gromov_completion)) filter"
  where "uniformity_Gromov_completion = (INF e:{0 <..}. principal {(x, y). dist x y < e})"

definition open_Gromov_completion :: "'a Gromov_completion set \<Rightarrow> bool"
  where "open_Gromov_completion U = (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity)"

instance proof
  interpret Turn_into_distance extended_predist
    by (standard, auto intro: extended_predist_weak_triangle extended_predist_commute)
  fix x y z::"'a Gromov_completion"
  show "(dist x y = 0) = (x = y)"
    using TID_nonneg[of x y] lower[of x y] TID_self_zero upper[of x y] extended_predist_self0[of x y] unfolding dist_Gromov_completion_def
    by (auto, linarith)
  show "dist x y \<le> dist x z + dist y z"
    unfolding dist_Gromov_completion_def using triangle by (simp add: TID_sym)
qed (auto simp add: uniformity_Gromov_completion_def open_Gromov_completion_def)
end

text \<open>The only relevant property of the distance on the Gromov completion is that it is comparable
to the minimum of (the square root of) the extended distance, and the exponential of minus the Gromov
product. The precise formula we use to define it is just an implementation detail, in a sense.
We summarize these properties in the next theorem.
From this point on, we will only use this, and never come back to the definition based on
\verb+extended_predist+ and \verb+turn_into_distance+.\<close>

theorem Gromov_completion_dist_comparison [mono_intros]:
  fixes x y::"('a::Gromov_hyperbolic_space) Gromov_completion"
  shows "ennreal(dist x y) \<le> esqrt(extended_Gromov_distance x y)"
        "ennreal(dist x y) \<le> eexp (- enn2ereal(epsilonG(TYPE('a)) * extended_Gromov_product_at basepoint x y))"
        "min (esqrt(extended_Gromov_distance x y)) (eexp (- enn2ereal(epsilonG(TYPE('a)) * extended_Gromov_product_at basepoint x y))) \<le> 2 * ennreal(dist x y)"
proof -
  interpret Turn_into_distance extended_predist
    by (standard, auto intro: extended_predist_weak_triangle extended_predist_commute)
  have "ennreal(dist x y) \<le> ennreal(extended_predist x y)"
    unfolding dist_Gromov_completion_def by (auto intro!: upper mono_intros)
  then show "ennreal(dist x y) \<le> esqrt(extended_Gromov_distance x y)"
            "ennreal(dist x y) \<le> eexp (- enn2ereal(epsilonG(TYPE('a)) * extended_Gromov_product_at basepoint x y))"
    unfolding extended_predist_ennreal by auto
  have "ennreal(extended_predist x y) \<le> ennreal(2 * dist x y)"
    unfolding dist_Gromov_completion_def by (auto intro!: lower mono_intros)
  also have "... = 2 * ennreal (dist x y)"
    by (simp add: ennreal_mult')
  finally show "min (esqrt(extended_Gromov_distance x y)) (eexp (- enn2ereal(epsilonG(TYPE('a)) * extended_Gromov_product_at basepoint x y))) \<le> 2 * ennreal(dist x y)"
    unfolding extended_predist_ennreal by auto
qed

lemma Gromov_completion_dist_le_1 [simp, mono_intros]:
  fixes x y::"('a::Gromov_hyperbolic_space) Gromov_completion"
  shows "dist x y \<le> 1"
proof -
  have "ennreal(dist x y) \<le> eexp (- enn2ereal(epsilonG(TYPE('a)) * extended_Gromov_product_at basepoint x y))"
    using Gromov_completion_dist_comparison(2)[of x y] by simp
  also have "... \<le> eexp(-0)"
    by (intro mono_intros)
  finally show ?thesis
    by auto
qed


text \<open>To avoid computations with exponentials, the following lemma is very convenient. It asserts
that if $x$ is close enough to infinity, and $y$ is close enough to $x$, then the Gromov product
between $x$ and $y$ is large.\<close>

lemma large_Gromov_product_approx:
  assumes "(M::ennreal) < \<infinity>"
  shows "\<exists>e D. e > 0 \<and> D < \<infinity> \<and> (\<forall>x y. dist x y \<le> e \<longrightarrow> extended_Gromov_distance x (to_Gromov_completion basepoint) \<ge> D \<longrightarrow> extended_Gromov_product_at basepoint x y \<ge> M)"
proof -
  obtain M0::real where "M = ennreal M0" using assms by (auto intro: ennreal_cases)
  define e::real where "e = exp(-epsilonG(TYPE('a)) * M0)/2"
  define D::ennreal where "D = ennreal M0 + 4"
  have "e > 0"
    unfolding e_def by auto
  moreover have "D < \<infinity>"
    unfolding D_def by auto
  moreover have "extended_Gromov_product_at basepoint x y \<ge> M0"
    if "dist x y \<le> e" "extended_Gromov_distance x (to_Gromov_completion basepoint) \<ge> D" for x y::"'a Gromov_completion"
  proof (cases "esqrt(extended_Gromov_distance x y) \<le> eexp (- enn2ereal(epsilonG(TYPE('a)) * extended_Gromov_product_at basepoint x y))")
    case False
    then have "eexp (- enn2ereal(epsilonG(TYPE('a)) * extended_Gromov_product_at basepoint x y)) \<le> 2 * ennreal(dist x y)"
      using Gromov_completion_dist_comparison(3)[of x y] unfolding min_def by auto
    also have "... \<le> exp(-epsilonG(TYPE('a)) * M0)"
      using \<open>dist x y \<le> e\<close> unfolding e_def by (auto simp add: numeral_mult_ennreal)
    finally have "-eln(exp(-epsilonG(TYPE('a)) * M0)) \<le> -eln(eexp (- enn2ereal(epsilonG(TYPE('a)) * extended_Gromov_product_at basepoint x y)))"
      by (intro mono_intros)
    then have "epsilonG((TYPE('a))) * M0 \<le> enn2ereal(epsilonG(TYPE('a))) * enn2ereal(extended_Gromov_product_at basepoint x y)"
      by (auto simp add: times_ennreal.rep_eq)
    then have "ereal M0 \<le> enn2ereal (extended_Gromov_product_at basepoint x y)"
      apply (auto simp del: times_ereal.simps(1) simp add: times_ereal.simps(1)[symmetric])
      by (metis ereal_mult_strict_left_mono not_less constant_in_extended_predist_pos(1) ereal_less(2) less_ereal.simps(4))
    then show "M0 \<le> extended_Gromov_product_at basepoint x y"
      by (metis (full_types) dual_order.trans enn2ereal_ennreal ennreal_less_zero_iff extended_Gromov_product_at_def less_eq_ennreal.rep_eq less_imp_le not_le zero_le)
  next
    case True
    then have "esqrt(extended_Gromov_distance x y) \<le> 2 * ennreal(dist x y)"
      using Gromov_completion_dist_comparison(3)[of x y] unfolding min_def by auto
    also have "... \<le> esqrt 4"
      by (metis (no_types, hide_lams) esqrt_4 Gromov_completion_dist_le_1[of x y] ennreal_le_1 mult.comm_neutral mult_left_mono zero_le)
    finally have *: "extended_Gromov_distance x y \<le> 4"
      unfolding esqrt_le by simp
    have "ennreal M0+4 \<le> D"
      unfolding D_def by auto
    also have "... \<le> extended_Gromov_product_at basepoint x x"
      using that by (auto simp add: extended_Gromov_distance_commute)
    also have "... \<le> extended_Gromov_product_at basepoint x y + extended_Gromov_distance x y"
      by (rule extended_Gromov_product_at_diff3[of basepoint x x y])
    also have "... \<le> extended_Gromov_product_at basepoint x y + 4"
      using * by simp
    finally show "M0 \<le> extended_Gromov_product_at basepoint x y"
      by (simp add: add.commute ennreal_minus_le_iff)
  qed
  ultimately show ?thesis unfolding \<open>M = ennreal M0\<close> by auto
qed

text \<open>On the other hand, far away from infinity, it is equivalent to control the extended Gromov
distance or the new distance on the space.\<close>
lemma inside_Gromov_distance_approx:
  assumes "C < (\<infinity>::ennreal)"
  shows "\<exists>e>0. \<forall>x y. extended_Gromov_distance (to_Gromov_completion basepoint) x \<le> C \<longrightarrow> dist x y \<le> e
          \<longrightarrow> esqrt(extended_Gromov_distance x y) \<le> 2 * ennreal(dist x y)"
proof -
  define e0 where "e0 = eexp(-enn2ereal(epsilonG(TYPE('a)) * C))"
  have "e0 > 0" unfolding e0_def
    by (metis assms eexp.simps(3) eln_eexp enn2ereal_eq_top_iff ennreal_neq_top ennreal_top_eq_mult_iff ereal_uminus_uminus gr_zeroI infinity_ennreal_def not_less top_greatest)
  have "e0 < \<infinity>" unfolding e0_def apply auto
    by (metis eexp_special_values(4) ereal_less(5) less_ennreal.rep_eq neg_0_less_iff_less_erea not_less_zero top.not_eq_extremum zero_ennreal.rep_eq)
  have "e0 / 4 > 0" "e0/4 < \<infinity>"
    using \<open>e0 > 0\<close> \<open>e0 < \<infinity>\<close> apply auto
    apply (metis \<open>0 < e0\<close> ennreal_divide_eq_0_iff not_gr_zero top_neq_numeral)
    by (metis ennreal_divide_eq_top_iff top.not_eq_extremum zero_neq_numeral)
  define e where "e = enn2real (e0/4)"
  have "e > 0"
    unfolding e_def using \<open>e0/4 > 0\<close> \<open>e0/4 < \<infinity>\<close> by (simp add: enn2real_positive_iff)
  moreover have "esqrt(extended_Gromov_distance x y) \<le> 2 * ennreal(dist x y)"
    if "extended_Gromov_distance (to_Gromov_completion basepoint) x \<le> C" "dist x y \<le> e" for x y::"'a Gromov_completion"
  proof -
    have R: "min a b \<le> c \<Longrightarrow> a \<le> c \<or> b \<le> c" for a b c::ennreal unfolding min_def
      by presburger
    have *: "2 * (e0/4) = e0/2"
    proof -
      have "2 / 4 = (1::real) / 2"
        by simp
      then have "inverse 4 * 2 = inverse (2::ennreal)"
        by (metis divide_ennreal_def ennreal_divide_numeral ennreal_numeral mult.left_neutral mult_2 mult_2_right mult_numeral_1_right zero_le_numeral)
      then show ?thesis
        unfolding divide_ennreal_def apply (subst mult.commute) by (simp add: mult.assoc)
    qed
    have "2 * ennreal (dist x y) \<le> 2 * ennreal e"
      using that by (intro mono_intros)
    also have "... = e0/2"
      unfolding e_def using \<open>e0/4 < \<infinity>\<close> * by auto
    also have "... < e0"
      by (metis \<open>e0 < \<infinity>\<close> \<open>e0 > 0\<close> divide_less_ennreal ennreal_divide_self ennreal_numeral_less_top infinity_ennreal_def mult.commute not_gr_zero one_less_numeral semiring_norm(76) zero_neq_numeral)
    also have "... \<le> eexp(-enn2ereal(epsilonG(TYPE('a)) * extended_Gromov_distance (to_Gromov_completion basepoint) x))"
      unfolding e0_def by (intro mono_intros that)
    also have "... \<le> eexp(-enn2ereal(epsilonG(TYPE('a)) * extended_Gromov_product_at basepoint x y))"
      by (intro mono_intros)
    finally show ?thesis
      using R[OF Gromov_completion_dist_comparison(3)[of x y]] by auto
  qed
  ultimately show ?thesis by auto
qed


subsection \<open>Topology of the Gromov boundary\<close>

text \<open>The convergence of sequences in the Gromov boundary can be characterized, essentially
by definition: sequences tend to a point at infinity iff the Gromov product with this point tends
to infinity, while sequences tend to a point inside iff the extended distance tends to $0$. In both
cases, it is just a matter of unfolding the definition of the distance, and see which one of the two
terms (exponential of minus the Gromov product, or extended distance) realizes the minimum. We have
constructed the distance essentially so that this property is satisfied.

We could also have defined first the topology, satisfying these conditions, but then we would have
had to check that it coincides with the topology that the distance defines, so it seems more
economical to proceed in this way.\<close>

lemma Gromov_completion_boundary_limit:
  assumes "x \<in> Gromov_boundary"
  shows "(u \<longlongrightarrow> x) F \<longleftrightarrow> ((\<lambda>n. extended_Gromov_product_at basepoint (u n) x) \<longlongrightarrow> \<infinity>) F"
proof
  assume *: "((\<lambda>n. extended_Gromov_product_at basepoint (u n) x) \<longlongrightarrow> \<infinity>) F"
  have "((\<lambda>n. ennreal(dist (u n) x)) \<longlongrightarrow> 0) F"
  proof (rule tendsto_sandwich[of "\<lambda>_. 0" _ _ "(\<lambda>n. eexp (- enn2ereal(ennreal(epsilonG(TYPE('a))) * extended_Gromov_product_at basepoint (u n) x)))"])
    have "((\<lambda>n. eexp (- enn2ereal(ennreal(epsilonG(TYPE('a))) * extended_Gromov_product_at basepoint (u n) x))) \<longlongrightarrow> eexp (- enn2ereal(ennreal(epsilonG(TYPE('a))) * (\<infinity>::ennreal)))) F"
      apply (intro tendsto_intros *) apply auto
      by (metis constant_in_extended_predist_pos(1) less_numeral_extra(3))
    then show "((\<lambda>n. eexp (- enn2ereal(ennreal(epsilonG(TYPE('a))) * extended_Gromov_product_at basepoint (u n) x))) \<longlongrightarrow> 0) F"
      by auto
  qed (auto simp add: Gromov_completion_dist_comparison)
  then have "((\<lambda>n. enn2real(ennreal(dist (u n) x))) \<longlongrightarrow> 0) F"
    by (intro tendsto_enn2real, auto)
  then show "(u \<longlongrightarrow> x) F"
    by (subst tendsto_dist_iff, auto)
next
  assume *: "(u \<longlongrightarrow> x) F"
  have a: "esqrt(extended_Gromov_distance (u n) x) = \<infinity>" for n
    unfolding extended_Gromov_distance_PInf_boundary(2)[OF assms, of "u n"] by auto
  have "min (esqrt(extended_Gromov_distance (u n) x)) (eexp (- enn2ereal(epsilonG(TYPE('a)) * extended_Gromov_product_at basepoint (u n) x)))
        = eexp (- enn2ereal(epsilonG(TYPE('a)) * extended_Gromov_product_at basepoint (u n) x))" for n
    unfolding a min_def using neq_top_trans by force
  moreover have "((\<lambda>n. min (esqrt(extended_Gromov_distance (u n) x)) (eexp (- enn2ereal(epsilonG(TYPE('a)) * extended_Gromov_product_at basepoint (u n) x)))) \<longlongrightarrow> 0) F"
  proof (rule tendsto_sandwich[of "\<lambda>_. 0" _ _ "\<lambda>n. 2 * ennreal(dist (u n) x)"])
    have "((\<lambda>n. 2 * ennreal (dist (u n) x)) \<longlongrightarrow> 2 * ennreal 0) F"
      apply (intro tendsto_intros) using * tendsto_dist_iff by auto
    then show "((\<lambda>n. 2 * ennreal (dist (u n) x)) \<longlongrightarrow> 0) F" by auto
  qed (auto simp add: Gromov_completion_dist_comparison)
  ultimately have "((\<lambda>n. eexp (- enn2ereal(epsilonG(TYPE('a)) * extended_Gromov_product_at basepoint (u n) x))) \<longlongrightarrow> 0) F"
    by auto
  then have "((\<lambda>n. (1/ennreal (epsilonG TYPE('a))) * e2ennreal(- eln (eexp (- enn2ereal(epsilonG(TYPE('a)) * extended_Gromov_product_at basepoint (u n) x))))) \<longlongrightarrow> (1/ennreal (epsilonG TYPE('a))) * e2ennreal(- eln 0)) F"
    by (intro tendsto_intros, auto)
  then have "((\<lambda>n. (1/ennreal (epsilonG TYPE('a))) * (epsilonG(TYPE('a)) * extended_Gromov_product_at basepoint (u n) x)) \<longlongrightarrow> (1/ennreal (epsilonG TYPE('a))) * \<infinity>) F"
    by auto
  moreover have "(1/ennreal (epsilonG TYPE('a))) * (epsilonG(TYPE('a)) * extended_Gromov_product_at basepoint (u n) x) = extended_Gromov_product_at basepoint (u n) x" for n
    by (metis constant_in_extended_predist_pos(3) ennreal_divide_times ennreal_neq_top mult.commute mult.left_neutral mult_divide_eq_ennreal mult_eq_0_iff)
  moreover have "(1/ennreal (epsilonG TYPE('a))) * \<infinity> = \<infinity>"
    by (simp add: ennreal_mult_top)
  ultimately show "((\<lambda>n. extended_Gromov_product_at basepoint (u n) x) \<longlongrightarrow> \<infinity>) F"
    by auto
qed

lemma extended_Gromov_product_tendsto_PInf_a_b:
  assumes "(\<lambda>n. extended_Gromov_product_at a (u n) (v n)) \<longlonglongrightarrow> \<infinity>"
  shows "(\<lambda>n. extended_Gromov_product_at b (u n) (v n)) \<longlonglongrightarrow> \<infinity>"
proof (rule tendsto_sandwich[of "\<lambda>n. extended_Gromov_product_at a (u n) (v n) - dist a b" _ _ "\<lambda>_. \<infinity>"])
  have "extended_Gromov_product_at a (u n) (v n) - ennreal (dist a b) \<le> extended_Gromov_product_at b (u n) (v n)" for n
    using extended_Gromov_product_at_diff1[of a "u n" "v n" b] by (simp add: add.commute ennreal_minus_le_iff)
  then show "\<forall>\<^sub>F n in sequentially. extended_Gromov_product_at a (u n) (v n) - ennreal (dist a b) \<le> extended_Gromov_product_at b (u n) (v n)"
    by auto
  have "(\<lambda>n. extended_Gromov_product_at a (u n) (v n) - ennreal (dist a b)) \<longlonglongrightarrow> \<infinity> - ennreal (dist a b)"
    by (intro tendsto_intros assms) auto
  then show "(\<lambda>n. extended_Gromov_product_at a (u n) (v n) - ennreal (dist a b)) \<longlonglongrightarrow> \<infinity>"
    by auto
qed (auto)

lemma Gromov_completion_inside_limit:
  assumes "x \<notin> Gromov_boundary"
  shows "(u \<longlongrightarrow> x) F \<longleftrightarrow> ((\<lambda>n. extended_Gromov_distance (u n) x) \<longlongrightarrow> 0) F"
proof
  assume *: "((\<lambda>n. extended_Gromov_distance (u n) x) \<longlongrightarrow> 0) F"
  have "((\<lambda>n. ennreal(dist (u n) x)) \<longlongrightarrow> 0) F"
  proof (rule tendsto_sandwich[of "\<lambda>_. 0" _ _ "\<lambda>n. esqrt (extended_Gromov_distance (u n) x)"])
    have "((\<lambda>n. esqrt (extended_Gromov_distance (u n) x)) \<longlongrightarrow> esqrt 0) F"
      by (intro tendsto_intros *)
    then show "((\<lambda>n. esqrt (extended_Gromov_distance (u n) x)) \<longlongrightarrow> 0) F"
      by auto
  qed (auto simp add: Gromov_completion_dist_comparison)
  then have "((\<lambda>n. enn2real(ennreal(dist (u n) x))) \<longlongrightarrow> 0) F"
    by (intro tendsto_enn2real, auto)
  then show "(u \<longlongrightarrow> x) F"
    by (subst tendsto_dist_iff, auto)
next
  assume *: "(u \<longlongrightarrow> x) F"
  have "x \<in> range to_Gromov_completion" using assms unfolding Gromov_boundary_def by auto
  have "((\<lambda>n. esqrt(extended_Gromov_distance (u n) x)) \<longlongrightarrow> 0) F"
  proof (rule tendsto_sandwich[of "\<lambda>_. 0" _ _ "\<lambda>n. 2 * ennreal(dist (u n) x)"])
    have A: "extended_Gromov_distance (to_Gromov_completion basepoint) x < \<infinity>"
      by (metis Gromov_boundary_extended_product_PInf assms extended_Gromov_product_e_x_x infinity_ennreal_def top.not_eq_extremum)
    obtain e where e: "e>0" "\<And>y. dist x y \<le> e \<Longrightarrow> esqrt(extended_Gromov_distance x y) \<le> 2 * ennreal (dist x y)"
      using inside_Gromov_distance_approx[OF A] by auto
    have B: "eventually (\<lambda>n. dist x (u n) < e) F"
      using order_tendstoD(2)[OF iffD1[OF tendsto_dist_iff *] \<open>e > 0\<close>] by (simp add: dist_commute)
    then have "eventually (\<lambda>n. esqrt(extended_Gromov_distance x (u n)) \<le> 2 * ennreal (dist x (u n))) F"
      using eventually_mono[OF _ e(2)] less_imp_le by (metis (mono_tags, lifting))
    then show "eventually (\<lambda>n. esqrt(extended_Gromov_distance (u n) x) \<le> 2 * ennreal (dist (u n) x)) F"
      by (simp add: dist_commute extended_Gromov_distance_commute)
    have "((\<lambda>n. 2 * ennreal(dist (u n) x)) \<longlongrightarrow> 2 * ennreal 0) F"
      apply (intro tendsto_intros) using tendsto_dist_iff * by auto
    then show "((\<lambda>n. 2 * ennreal(dist (u n) x)) \<longlongrightarrow> 0) F"
      by simp
  qed (auto)
  then have "((\<lambda>n. esqrt(extended_Gromov_distance (u n) x) * esqrt(extended_Gromov_distance (u n) x)) \<longlongrightarrow> 0 * 0) F"
    by (intro tendsto_intros, auto)
  then show "((\<lambda>n. extended_Gromov_distance (u n) x) \<longlongrightarrow> 0) F"
    by auto
qed

lemma to_Gromov_completion_lim [simp, tendsto_intros]:
  "((\<lambda>n. to_Gromov_completion (u n)) \<longlongrightarrow> to_Gromov_completion a) F \<longleftrightarrow> (u \<longlongrightarrow> a) F"
proof (subst Gromov_completion_inside_limit, auto)
  assume "((\<lambda>n. ennreal (dist (u n) a)) \<longlongrightarrow> 0) F"
  then have "((\<lambda>n. enn2real(ennreal (dist (u n) a))) \<longlongrightarrow> enn2real 0) F"
    by (intro tendsto_enn2real, auto)
  then show "(u \<longlongrightarrow> a) F"
    by (subst tendsto_dist_iff, auto)
next
  assume "(u \<longlongrightarrow> a) F"
  then have "((\<lambda>n. dist (u n) a) \<longlongrightarrow> 0) F"
    using tendsto_dist_iff by auto
  then show "((\<lambda>n. ennreal (dist (u n) a)) \<longlongrightarrow> 0) F"
    by (intro tendsto_intros)
qed

text \<open>Now, we can also come back to our original definition of the completion, where points on the
boundary correspond to equivalence classes of sequences whose mutual Gromov product tends to
infinity. We show that this is compatible with our topology: the sequences that are in the equivalence
class of a point on the boundary are exactly the sequences that converge to this point. This is also
a direct consequence of the definitions, although the proof requires some unfolding (and playing
with the hyperbolicity inequality several times).\<close>

text \<open>First, we show that a sequence in the equivalence class of $x$ converges to $x$.\<close>

lemma Gromov_completion_converge_to_boundary_aux:
  assumes "x \<in> Gromov_boundary" "abs_Gromov_completion v = x" "Gromov_completion_rel v v"
  shows "(\<lambda>n. extended_Gromov_product_at basepoint (to_Gromov_completion (v n)) x) \<longlonglongrightarrow> \<infinity>"
proof -
  have A: "eventually (\<lambda>n. extended_Gromov_product_at basepoint (to_Gromov_completion (v n)) x \<ge> ennreal M) sequentially" for M
  proof -
    have "Gromov_converging_at_boundary v"
      using Gromov_boundary_abs_converging assms by blast
    then obtain N where N: "\<And>m n. m \<ge> N \<Longrightarrow> n \<ge> N \<Longrightarrow> Gromov_product_at basepoint (v m) (v n) \<ge> M + deltaG(TYPE('a))"
      unfolding Gromov_converging_at_boundary_def by metis
    have "extended_Gromov_product_at basepoint (to_Gromov_completion (v n)) x \<ge> ennreal M" if "n \<ge> N" for n
    unfolding extended_Gromov_product_at_def proof (rule Inf_greatest, auto)
      fix wv wx assume H: "abs_Gromov_completion wv = to_Gromov_completion (v n)"
                          "x = abs_Gromov_completion wx"
                          "Gromov_completion_rel wv wv" "Gromov_completion_rel wx wx"
      then have wv: "wv p = v n" for p
        using Gromov_completion_rel_to_const Quotient3_Gromov_completion Quotient3_rel to_Gromov_completion_def by fastforce
      have "Gromov_completion_rel v wx"
        using assms H Quotient3_rel[OF Quotient3_Gromov_completion] by auto
      then have *: "(\<lambda>p. Gromov_product_at basepoint (v p) (wx p)) \<longlonglongrightarrow> \<infinity>"
        unfolding Gromov_completion_rel_def using Gromov_converging_at_boundary_imp_not_constant' \<open>Gromov_converging_at_boundary v\<close> by auto
      have "eventually (\<lambda>p. ereal(Gromov_product_at basepoint (v p) (wx p)) > M + deltaG(TYPE('a))) sequentially"
        using order_tendstoD[OF *, of "ereal (M + deltaG TYPE('a))"] by auto
      then obtain P where P: "\<And>p. p \<ge> P \<Longrightarrow> ereal(Gromov_product_at basepoint (v p) (wx p)) > M + deltaG(TYPE('a))"
        unfolding eventually_sequentially by auto
      have *: "ennreal (Gromov_product_at basepoint (v n) (wx p)) \<ge> ennreal M" if "p \<ge> max P N" for p
      proof (intro mono_intros)
        have "M \<le> min (M + deltaG(TYPE('a))) (M + deltaG(TYPE('a))) - deltaG(TYPE('a))"
          by auto
        also have "... \<le> min (Gromov_product_at basepoint (v n) (v p)) (Gromov_product_at basepoint (v p) (wx p)) - deltaG(TYPE('a))"
          apply (intro mono_intros)
          using N[OF \<open>n \<ge> N\<close>, of p] \<open>p \<ge> max P N\<close> P[of p] \<open>p \<ge> max P N\<close> by auto
        also have "... \<le> Gromov_product_at basepoint (v n) (wx p) "
          by (rule hyperb_ineq)
        finally show "M \<le> Gromov_product_at basepoint (v n) (wx p) "
          by simp
      qed
      then have "eventually (\<lambda>p. ennreal (Gromov_product_at basepoint (v n) (wx p)) \<ge> ennreal M) sequentially"
        unfolding eventually_sequentially by metis
      then show "ennreal M \<le> liminf (\<lambda>p. ennreal (Gromov_product_at basepoint (wv p) (wx p)))"
        unfolding wv by (simp add: Liminf_bounded)
    qed
    then show ?thesis unfolding eventually_sequentially by auto
  qed
  have B: "eventually (\<lambda>n. extended_Gromov_product_at basepoint (to_Gromov_completion (v n)) x > M) sequentially" if "M < top" for M
  proof -
    obtain N where "ennreal N > M" using \<open>M < top\<close> ennreal_rat_dense by blast
    then have "a \<ge> ennreal N \<Longrightarrow> a > M" for a by auto
    then show ?thesis using A[of N] eventually_elim2 by force
  qed
  then show ?thesis
    by (rule order_tendstoI, auto)
qed

text \<open>Then, we prove the converse and therefore the equivalence.\<close>

lemma Gromov_completion_converge_to_boundary:
  assumes "x \<in> Gromov_boundary"
  shows "((\<lambda>n. to_Gromov_completion(u n)) \<longlonglongrightarrow> x) \<longleftrightarrow> (Gromov_completion_rel u u \<and> abs_Gromov_completion u = x)"
proof
  assume "Gromov_completion_rel u u \<and> abs_Gromov_completion u = x"
  then show "((\<lambda>n. to_Gromov_completion(u n)) \<longlonglongrightarrow> x)"
    using Gromov_completion_converge_to_boundary_aux[OF assms, of u] unfolding Gromov_completion_boundary_limit[OF assms] by auto
next
  assume H: "(\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> x"
  have Lu: "(\<lambda>n. extended_Gromov_product_at basepoint (to_Gromov_completion (u n)) x) \<longlonglongrightarrow> \<infinity>"
    using iffD1[OF Gromov_completion_boundary_limit[OF assms] H] by simp
  have A: "\<exists>N. \<forall>n \<ge> N. \<forall> m\<ge>N. Gromov_product_at basepoint (u m) (u n) \<ge> M" for M
  proof -
    have "eventually (\<lambda>n. extended_Gromov_product_at basepoint (to_Gromov_completion (u n)) x > M + deltaG(TYPE('a))) sequentially"
      by (rule order_tendstoD[OF Lu], auto)
    then obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> extended_Gromov_product_at basepoint (to_Gromov_completion (u n)) x > M + deltaG(TYPE('a))"
      unfolding eventually_sequentially by auto
    have "Gromov_product_at basepoint (u m) (u n) \<ge> M" if "n \<ge> N" "m\<ge> N" for m n
    proof -
      have "ennreal M \<le> min (ennreal (M + deltaG(TYPE('a)))) (ennreal (M + deltaG(TYPE('a)))) - ennreal(deltaG(TYPE('a)))"
        by (simp add: ennreal_minus)
      also have "... \<le> min (extended_Gromov_product_at basepoint (to_Gromov_completion (u m)) x) (extended_Gromov_product_at basepoint x (to_Gromov_completion (u n))) - deltaG(TYPE('a))"
        apply (intro mono_intros) using N[OF \<open>n \<ge> N\<close>] N[OF \<open>m \<ge> N\<close>]
        by (auto simp add: extended_Gromov_product_at_commute)
      also have "... \<le> extended_Gromov_product_at basepoint (to_Gromov_completion (u m)) (to_Gromov_completion (u n))"
        by (rule extended_hyperb_ineq)
      finally show ?thesis by auto
    qed
    then show ?thesis by auto
  qed
  have "\<exists>N. \<forall>n \<ge> N. \<forall> m\<ge>N. Gromov_product_at a (u m) (u n) \<ge> M" for M a
  proof -
    obtain N where N: "\<And>m n. m \<ge> N \<Longrightarrow> n \<ge> N \<Longrightarrow> Gromov_product_at basepoint (u m) (u n) \<ge> M + dist a basepoint"
      using A[of "M + dist a basepoint"] by auto
    have "Gromov_product_at a (u m) (u n) \<ge> M" if "m \<ge> N" "n \<ge> N" for m n
      using N[OF that] Gromov_product_at_diff1[of a "u m" "u n" basepoint] by auto
    then show ?thesis by auto
  qed
  then have "Gromov_converging_at_boundary u"
    unfolding Gromov_converging_at_boundary_def by auto
  then have "Gromov_completion_rel u u" using Gromov_converging_at_boundary_rel by auto

  define v where "v = rep_Gromov_completion x"
  then have "Gromov_converging_at_boundary v"
    using Gromov_boundary_rep_converging[OF assms] by auto
  have v: "abs_Gromov_completion v = x" "Gromov_completion_rel v v"
    using Quotient3_abs_rep[OF Quotient3_Gromov_completion] Quotient3_rep_reflp[OF Quotient3_Gromov_completion]
    unfolding v_def by auto
  then have Lv: "(\<lambda>n. extended_Gromov_product_at basepoint (to_Gromov_completion (v n)) x) \<longlonglongrightarrow> \<infinity>"
    using Gromov_completion_converge_to_boundary_aux[OF assms] by auto

  have *: "(\<lambda>n. min (extended_Gromov_product_at basepoint (to_Gromov_completion (u n)) x) (extended_Gromov_product_at basepoint x (to_Gromov_completion (v n))) -
          ennreal (deltaG TYPE('a))) \<longlonglongrightarrow> min \<infinity> \<infinity> - ennreal (deltaG TYPE('a))"
    apply (intro tendsto_intros) using Lu Lv by (auto simp add: extended_Gromov_product_at_commute)
  have "(\<lambda>n. enn2ereal(extended_Gromov_product_at basepoint (to_Gromov_completion (u n)) (to_Gromov_completion (v n)))) \<longlonglongrightarrow> enn2ereal \<infinity>"
    apply (intro tendsto_intros)
    apply (rule tendsto_sandwich[of "\<lambda>n. min (extended_Gromov_product_at basepoint (to_Gromov_completion (u n)) x)
                                             (extended_Gromov_product_at basepoint x (to_Gromov_completion (v n))) - deltaG(TYPE('a))" _ _ "\<lambda>_. \<infinity>"])
    using extended_hyperb_ineq not_eventuallyD apply blast using * by auto
  then have "(\<lambda>n. Gromov_product_at basepoint (u n) (v n)) \<longlonglongrightarrow> \<infinity>"
    by auto
  then have "(\<lambda>n. Gromov_product_at a (u n) (v n)) \<longlonglongrightarrow> \<infinity>" for a
    using Gromov_product_tendsto_PInf_a_b by auto
  then have "Gromov_completion_rel u v"
    unfolding Gromov_completion_rel_def
    using \<open>Gromov_converging_at_boundary u\<close> \<open>Gromov_converging_at_boundary v\<close> by auto
  then have "abs_Gromov_completion u = abs_Gromov_completion v"
    using Quotient3_rel[OF Quotient3_Gromov_completion] v(2) \<open>Gromov_completion_rel u u\<close> by auto
  then have "abs_Gromov_completion u = x"
    using v(1) by auto
  then show "Gromov_completion_rel u u \<and> abs_Gromov_completion u = x"
    using \<open>Gromov_completion_rel u u\<close> by auto
qed

text \<open>In particular, it follows that a sequence which is \verb+Gromov_converging_at_boundary+ is
indeed converging to a point on the boundary, the equivalence class of this sequence.\<close>

lemma Gromov_converging_at_boundary_converges:
  assumes "Gromov_converging_at_boundary u"
  shows "\<exists>x \<in> Gromov_boundary. (\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> x"
apply (rule bexI[of _ "abs_Gromov_completion u"])
apply (subst Gromov_completion_converge_to_boundary)
using assms by (auto simp add: Gromov_converging_at_boundary_rel)

lemma Gromov_converging_at_boundary_converges':
  assumes "Gromov_converging_at_boundary u"
  shows "convergent (\<lambda>n. to_Gromov_completion (u n))"
unfolding convergent_def using Gromov_converging_at_boundary_converges[OF assms] by auto

lemma lim_imp_Gromov_converging_at_boundary:
  fixes u::"nat \<Rightarrow> 'a::Gromov_hyperbolic_space"
  assumes "(\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> x" "x \<in> Gromov_boundary"
  shows "Gromov_converging_at_boundary u"
using Gromov_boundary_abs_converging Gromov_completion_converge_to_boundary assms by blast

text \<open>If one perturbs a sequence inside the space by a bounded distance, one does not change the
limit on the boundary.\<close>

lemma Gromov_converging_at_boundary_bounded_perturbation:
  assumes "(\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> x"
          "x \<in> Gromov_boundary"
          "\<And>n. dist (u n) (v n) \<le> C"
  shows "(\<lambda>n. to_Gromov_completion (v n)) \<longlonglongrightarrow> x"
proof -
  have "(\<lambda>n. extended_Gromov_product_at basepoint (to_Gromov_completion (v n)) x) \<longlonglongrightarrow> \<infinity>"
  proof (rule tendsto_sandwich[of "\<lambda>n. extended_Gromov_product_at basepoint (to_Gromov_completion (u n)) x - C" _ _ "\<lambda>n. \<infinity>"])
    have "extended_Gromov_product_at basepoint (to_Gromov_completion (u n)) x - ennreal C \<le> extended_Gromov_product_at basepoint (to_Gromov_completion (v n)) x" for n
    proof -
      have "extended_Gromov_product_at basepoint (to_Gromov_completion (u n)) x \<le> extended_Gromov_product_at basepoint (to_Gromov_completion (v n)) x
                  + extended_Gromov_distance (to_Gromov_completion (u n)) (to_Gromov_completion (v n))"
        by (intro mono_intros)
      also have "... \<le> extended_Gromov_product_at basepoint (to_Gromov_completion (v n)) x + C"
        using assms(3)[of n] by (auto simp add: ennreal_leI)
      finally show ?thesis
        by (simp add: add.commute ennreal_minus_le_iff)
    qed
    then show "\<forall>\<^sub>F n in sequentially. extended_Gromov_product_at basepoint (to_Gromov_completion (u n)) x - ennreal C \<le> extended_Gromov_product_at basepoint (to_Gromov_completion (v n)) x"
      by auto
    have "(\<lambda>n. extended_Gromov_product_at basepoint (to_Gromov_completion (u n)) x - ennreal C) \<longlonglongrightarrow> \<infinity> - ennreal C"
      apply (intro tendsto_intros)
      unfolding Gromov_completion_boundary_limit[OF \<open>x \<in> Gromov_boundary\<close>, symmetric] using assms(1) by auto
    then show "(\<lambda>n. extended_Gromov_product_at basepoint (to_Gromov_completion (u n)) x - ennreal C) \<longlonglongrightarrow> \<infinity>"
      by auto
  qed (auto)
  then show ?thesis
    unfolding Gromov_completion_boundary_limit[OF \<open>x \<in> Gromov_boundary\<close>] by simp
qed

text \<open>Combining the two cases, we deduce that a point in the Gromov boundary is the limit of
its representative sequence in the space.\<close>

lemma rep_Gromov_completion_limit:
  "(\<lambda>n. to_Gromov_completion (rep_Gromov_completion x n)) \<longlonglongrightarrow> x"
proof (cases "x \<in> Gromov_boundary")
  case True
  show ?thesis
    unfolding Gromov_completion_converge_to_boundary[OF True]
    using Gromov_boundary_rep_converging Gromov_converging_at_boundary_rel Quotient3_Gromov_completion Quotient3_abs_rep True by fastforce
next
  case False
  then obtain y where y: "x = to_Gromov_completion y"
    using not_in_Gromov_boundary by blast
  show ?thesis unfolding y by auto
qed

text \<open>We prove that the extended Gromov distance is a continuous function of one variable,
by separating the different cases at infinity and inside the space. Note that it is not a
continuous function of both variables: if $u_n$ is inside the space but tends to a point $x$ in the
boundary, then the extended Gromov distance between $u_n$ and $u_n$ is $0$, but for the limit it is
$\infty$.\<close>

lemma extended_Gromov_distance_continuous:
  "continuous_on UNIV (\<lambda>y. extended_Gromov_distance x y)"
proof (cases "x \<in> Gromov_boundary")
  text \<open>First, if $x$ is in the boundary, then all distances to $x$ are infinite, and the statement
  is trivial.\<close>
  case True
  then have *: "extended_Gromov_distance x y = \<infinity>" for y
    by auto
  show ?thesis
    unfolding * using continuous_on_topological by blast
next
  text \<open>Next, consider the case where $x$ is inside the space. We split according to whether $y$ is
  inside the space or at infinity.\<close>
  case False
  then obtain a where a: "x = to_Gromov_completion a"
    unfolding Gromov_boundary_def by auto
  have "(\<lambda>n. extended_Gromov_distance x (u n)) \<longlonglongrightarrow> extended_Gromov_distance x y" if "u \<longlonglongrightarrow> y" for u y
  proof (cases "y \<in> Gromov_boundary")
    text \<open>If $y$ is at infinity, then we know that the Gromov product of $u_n$ and $y$ tends to
    infinity. Therefore, the extended distance from $u_n$ to any fixed point also tends to infinity
    (as the Gromov product is bounded from below by the extended distance).\<close>
    case True
    have *: "(\<lambda>n. extended_Gromov_product_at a (u n) y) \<longlonglongrightarrow> \<infinity>"
      by (rule extended_Gromov_product_tendsto_PInf_a_b[OF iffD1[OF Gromov_completion_boundary_limit, OF True \<open>u \<longlonglongrightarrow> y\<close>]])
    have "(\<lambda>n. extended_Gromov_distance x (u n)) \<longlonglongrightarrow> \<infinity>"
      apply (rule tendsto_sandwich[of "\<lambda>n. extended_Gromov_product_at a (u n) y" _ _ "\<lambda>_. \<infinity>"])
      unfolding a using extended_Gromov_product_le_dist[of a "u _" y] * by auto
    then show ?thesis using True by auto
  next
    text \<open>If $y$ is inside the space, then we use the triangular inequality for the extended Gromov
    distance to conclure.\<close>
    case False
    have *: "(\<lambda>n. extended_Gromov_distance (u n) y) \<longlonglongrightarrow> 0"
      by (rule iffD1[OF Gromov_completion_inside_limit[OF False] \<open>u \<longlonglongrightarrow> y\<close>])
    show "(\<lambda>n. extended_Gromov_distance x (u n)) \<longlonglongrightarrow> extended_Gromov_distance x y"
    proof (rule tendsto_sandwich[of "\<lambda>n. extended_Gromov_distance x y - extended_Gromov_distance (u n) y" _ _
                                    "\<lambda>n. extended_Gromov_distance x y + extended_Gromov_distance (u n) y"])
      have "extended_Gromov_distance x y - extended_Gromov_distance (u n) y \<le> extended_Gromov_distance x (u n)" for n
        using extended_Gromov_distance_triangle[of y x "u n"]
        by (auto simp add: extended_Gromov_distance_commute False ennreal_minus_le_iff extended_Gromov_distance_def)
      then show "\<forall>\<^sub>F n in sequentially. extended_Gromov_distance x y - extended_Gromov_distance (u n) y \<le> extended_Gromov_distance x (u n)"
        by auto
      have "extended_Gromov_distance x (u n) \<le> extended_Gromov_distance x y + extended_Gromov_distance (u n) y" for n
        using extended_Gromov_distance_triangle[of x "u n" y] by (auto simp add: extended_Gromov_distance_commute)
      then show "\<forall>\<^sub>F n in sequentially. extended_Gromov_distance x (u n) \<le> extended_Gromov_distance x y + extended_Gromov_distance (u n) y"
        by auto
      have "(\<lambda>n. extended_Gromov_distance x y - extended_Gromov_distance (u n) y) \<longlonglongrightarrow> extended_Gromov_distance x y - 0"
        by (intro tendsto_intros *, auto)
      then show "(\<lambda>n. extended_Gromov_distance x y - extended_Gromov_distance (u n) y) \<longlonglongrightarrow> extended_Gromov_distance x y"
        by simp
      have "(\<lambda>n. extended_Gromov_distance x y + extended_Gromov_distance (u n) y) \<longlonglongrightarrow> extended_Gromov_distance x y + 0"
        by (intro tendsto_intros *)
      then show "(\<lambda>n. extended_Gromov_distance x y + extended_Gromov_distance (u n) y) \<longlonglongrightarrow> extended_Gromov_distance x y"
        by simp
    qed
  qed
  then show ?thesis
    unfolding continuous_on_sequentially comp_def by auto
qed

lemma extended_Gromov_distance_continuous':
  "continuous_on UNIV (\<lambda>x. extended_Gromov_distance x y)"
using extended_Gromov_distance_continuous[of y] extended_Gromov_distance_commute[of _ y] by auto

text \<open>We deduce the basic fact that the original space is open in the Gromov completion\<close>

lemma to_Gromov_completion_range_open:
  "open (range to_Gromov_completion)"
proof -
  have *: "range to_Gromov_completion = (\<lambda>x. extended_Gromov_distance (to_Gromov_completion basepoint) x)-`{..<\<infinity>}"
    using Gromov_boundary_def extended_Gromov_distance_PInf_boundary(2) by fastforce
  show ?thesis
    unfolding * using extended_Gromov_distance_continuous open_lessThan open_vimage by blast
qed

lemma Gromov_boundary_closed:
  "closed Gromov_boundary"
unfolding Gromov_boundary_def using to_Gromov_completion_range_open by auto

text \<open>The original space is also dense in its Gromov completion, as all points at infinity are
by definition limits of some sequence in the space.\<close>

lemma to_Gromov_completion_range_dense [simp]:
  "closure (range to_Gromov_completion) = UNIV"
apply (auto simp add: closure_sequential) using rep_Gromov_completion_limit by force

lemma to_Gromov_completion_homeomorphism:
  "homeomorphism_on UNIV to_Gromov_completion"
by (rule homeomorphism_on_sequentially, auto)

lemma to_Gromov_completion_continuous:
  "continuous_on UNIV to_Gromov_completion"
by (rule homeomorphism_on_continuous[OF to_Gromov_completion_homeomorphism])

text \<open>The Gromov boundary is always complete. Indeed, consider a Cauchy sequence $u_n$ in the
boundary, and approximate well enough $u_n$ by a point $v_n$ inside. Then the sequence $v_n$
is Gromov converging at infinity (the respective Gromov products tend to infinity essentially
by definition), and its limit point is the limit of the original sequence $u$.\<close>

proposition Gromov_boundary_complete:
  "complete Gromov_boundary"
proof (rule completeI)
  fix u::"nat \<Rightarrow> 'a Gromov_completion" assume "\<forall>n. u n \<in> Gromov_boundary" "Cauchy u"
  then have u: "\<And>n. u n \<in> Gromov_boundary" by auto
  have *: "\<exists>x \<in> range to_Gromov_completion. dist (u n) x < 1/real(n+1)" for n
    by (rule closure_approachableD, auto simp add: to_Gromov_completion_range_dense)
  have "\<exists>v. \<forall>n. dist (to_Gromov_completion (v n)) (u n) < 1/real(n+1)"
    using of_nat_less_top apply (intro choice) using * by (auto simp add: dist_commute)
  then obtain v where v: "\<And>n. dist (to_Gromov_completion (v n)) (u n) < 1/real(n+1)"
    by blast
  have "(\<lambda>n. dist (to_Gromov_completion (v n)) (u n)) \<longlonglongrightarrow> 0"
    apply (rule tendsto_sandwich[of "\<lambda>_. 0" _ _ "\<lambda>n. 1/real(n+1)"])
    using v LIMSEQ_ignore_initial_segment[OF lim_1_over_n, of 1] unfolding eventually_sequentially
    by (auto simp add: less_imp_le)

  have "Gromov_converging_at_boundary v"
  proof (rule Gromov_converging_at_boundaryI[of basepoint])
    fix M::real
    obtain D1 e1 where D1: "e1 > 0" "D1 < \<infinity>" "\<And>x y::'a Gromov_completion. dist x y \<le> e1 \<Longrightarrow> extended_Gromov_distance x (to_Gromov_completion basepoint) \<ge> D1 \<Longrightarrow> extended_Gromov_product_at basepoint x y \<ge> ennreal M"
      using large_Gromov_product_approx[of "ennreal M"] by auto
    obtain D2 e2 where D2: "e2 > 0" "D2 < \<infinity>" "\<And>x y::'a Gromov_completion. dist x y \<le> e2 \<Longrightarrow> extended_Gromov_distance x (to_Gromov_completion basepoint) \<ge> D2 \<Longrightarrow> extended_Gromov_product_at basepoint x y \<ge> D1"
      using large_Gromov_product_approx[OF \<open>D1 < \<infinity>\<close>] by auto
    define e where "e = (min e1 e2)/3"
    have "e > 0" unfolding e_def using \<open>e1 > 0\<close> \<open>e2 > 0\<close> by auto
    then obtain N1 where N1: "\<And>n m. n \<ge> N1 \<Longrightarrow> m \<ge> N1 \<Longrightarrow> dist (u n) (u m) < e"
      using \<open>Cauchy u\<close> unfolding Cauchy_def by blast
    have "eventually (\<lambda>n. dist (to_Gromov_completion (v n)) (u n) < e) sequentially"
      by (rule order_tendstoD[OF \<open>(\<lambda>n. dist (to_Gromov_completion (v n)) (u n)) \<longlonglongrightarrow> 0\<close>], fact)
    then obtain N2 where N2: "\<And>n. n \<ge> N2 \<Longrightarrow> dist (to_Gromov_completion (v n)) (u n) < e"
      unfolding eventually_sequentially by auto
    have "ennreal M \<le> extended_Gromov_product_at basepoint (to_Gromov_completion (v m)) (to_Gromov_completion (v n))"
      if "n \<ge> max N1 N2" "m \<ge> max N1 N2" for m n
    proof (rule D1(3))
      have "dist (to_Gromov_completion (v m)) (to_Gromov_completion (v n))
        \<le> dist (to_Gromov_completion (v m)) (u m) + dist (u m) (u n) + dist (u n) (to_Gromov_completion (v n))"
        by (intro mono_intros)
      also have "... \<le> e + e + e"
        apply (intro mono_intros)
        using N1[of m n] N2[of n] N2[of m] that by (auto simp add: dist_commute)
      also have "... \<le> e1" unfolding e_def by auto
      finally show "dist (to_Gromov_completion (v m)) (to_Gromov_completion (v n)) \<le> e1" by simp

      have "e \<le> e2" unfolding e_def using \<open>e2 > 0\<close> by auto
      have "D1 \<le> extended_Gromov_product_at basepoint (u m) (to_Gromov_completion (v m))"
        apply (rule D2(3)) using N2[of m] that \<open>e \<le> e2\<close> u[of m] by (auto simp add: dist_commute)
      also have "... \<le> extended_Gromov_distance (to_Gromov_completion basepoint) (to_Gromov_completion (v m))"
        using extended_Gromov_product_le_dist[of basepoint "to_Gromov_completion (v m)" "u m"]
        by (simp add: extended_Gromov_product_at_commute)
      finally show "D1 \<le> extended_Gromov_distance (to_Gromov_completion (v m)) (to_Gromov_completion basepoint)"
        by (simp add: extended_Gromov_distance_commute)
    qed
    then have "M \<le> Gromov_product_at basepoint (v m) (v n)" if "n \<ge> max N1 N2" "m \<ge> max N1 N2" for m n
      using that by auto
    then show "\<exists>N. \<forall>n\<ge>N. \<forall>m\<ge>N. M \<le> Gromov_product_at basepoint (v m) (v n)"
      by blast
  qed
  then obtain l where l: "l \<in> Gromov_boundary" "(\<lambda>n. to_Gromov_completion (v n)) \<longlonglongrightarrow> l"
    using Gromov_converging_at_boundary_converges by blast
  have "(\<lambda>n. dist (u n) l) \<longlonglongrightarrow> 0+0"
  proof (rule tendsto_sandwich[of "\<lambda>_. 0" _ _ "\<lambda>n. dist (u n) (to_Gromov_completion (v n)) + dist (to_Gromov_completion (v n)) l"])
    show "(\<lambda>n. dist (u n) (to_Gromov_completion (v n)) + dist (to_Gromov_completion (v n)) l) \<longlonglongrightarrow> 0 + 0"
      apply (intro tendsto_intros)
      using iffD1[OF tendsto_dist_iff l(2)] \<open>(\<lambda>n. dist (to_Gromov_completion (v n)) (u n)) \<longlonglongrightarrow> 0\<close>
      by (auto simp add: dist_commute)
  qed (auto simp add: dist_triangle)
  then have "u \<longlonglongrightarrow> l"
    using iffD2[OF tendsto_dist_iff] by auto
  then show "\<exists>l\<in>Gromov_boundary. u \<longlonglongrightarrow> l"
    using l(1) by auto
qed

text \<open>When the initial space is complete, then the whole Gromov completion is also complete:
for Cauchy sequences tending to the Gromov boundary, then the convergence is proved as in the
completeness of the boundary above. For Cauchy sequences that remain bounded, the convergence
is reduced to the convergence inside the original space, which holds by assumption.\<close>

proposition Gromov_completion_complete:
  assumes "complete (UNIV::'a::Gromov_hyperbolic_space set)"
  shows "complete (UNIV::'a Gromov_completion set)"
proof (rule completeI, auto)
  fix u0::"nat \<Rightarrow> 'a Gromov_completion" assume "Cauchy u0"
  show "\<exists>l. u0 \<longlonglongrightarrow> l"
  proof (cases "limsup (\<lambda>n. extended_Gromov_distance (to_Gromov_completion basepoint) (u0 n)) = \<infinity>")
    case True
    then obtain r where r: "strict_mono r" "(\<lambda>n. extended_Gromov_distance (to_Gromov_completion basepoint) (u0 (r n))) \<longlonglongrightarrow> \<infinity>"
      using limsup_subseq_lim[of "(\<lambda>n. extended_Gromov_distance (to_Gromov_completion basepoint) (u0 n))"] unfolding comp_def
      by auto
    define u where "u = u0 o r"
    then have "(\<lambda>n. extended_Gromov_distance (to_Gromov_completion basepoint) (u n)) \<longlonglongrightarrow> \<infinity>"
      unfolding comp_def using r(2) by simp
    have "Cauchy u"
      using \<open>Cauchy u0\<close> r(1) u_def by (simp add: Cauchy_subseq_Cauchy)

    have *: "\<exists>x \<in> range to_Gromov_completion. dist (u n) x < 1/real(n+1)" for n
      by (rule closure_approachableD, auto simp add: to_Gromov_completion_range_dense)
    have "\<exists>v. \<forall>n. dist (to_Gromov_completion (v n)) (u n) < 1/real(n+1)"
      using of_nat_less_top apply (intro choice) using * by (auto simp add: dist_commute)
    then obtain v where v: "\<And>n. dist (to_Gromov_completion (v n)) (u n) < 1/real(n+1)"
      by blast
    have "(\<lambda>n. dist (to_Gromov_completion (v n)) (u n)) \<longlonglongrightarrow> 0"
      apply (rule tendsto_sandwich[of "\<lambda>_. 0" _ _ "\<lambda>n. 1/real(n+1)"])
      using v LIMSEQ_ignore_initial_segment[OF lim_1_over_n, of 1] unfolding eventually_sequentially
      by (auto simp add: less_imp_le)

    have "Gromov_converging_at_boundary v"
    proof (rule Gromov_converging_at_boundaryI[of basepoint])
      fix M::real
      obtain D1 e1 where D1: "e1 > 0" "D1 < \<infinity>" "\<And>x y::'a Gromov_completion. dist x y \<le> e1 \<Longrightarrow> extended_Gromov_distance x (to_Gromov_completion basepoint) \<ge> D1 \<Longrightarrow> extended_Gromov_product_at basepoint x y \<ge> ennreal M"
        using large_Gromov_product_approx[of "ennreal M"] by auto
      obtain D2 e2 where D2: "e2 > 0" "D2 < \<infinity>" "\<And>x y::'a Gromov_completion. dist x y \<le> e2 \<Longrightarrow> extended_Gromov_distance x (to_Gromov_completion basepoint) \<ge> D2 \<Longrightarrow> extended_Gromov_product_at basepoint x y \<ge> D1"
        using large_Gromov_product_approx[OF \<open>D1 < \<infinity>\<close>] by auto
      define e where "e = (min e1 e2)/3"
      have "e > 0" unfolding e_def using \<open>e1 > 0\<close> \<open>e2 > 0\<close> by auto
      then obtain N1 where N1: "\<And>n m. n \<ge> N1 \<Longrightarrow> m \<ge> N1 \<Longrightarrow> dist (u n) (u m) < e"
        using \<open>Cauchy u\<close> unfolding Cauchy_def by blast
      have "eventually (\<lambda>n. dist (to_Gromov_completion (v n)) (u n) < e) sequentially"
        by (rule order_tendstoD[OF \<open>(\<lambda>n. dist (to_Gromov_completion (v n)) (u n)) \<longlonglongrightarrow> 0\<close>], fact)
      then obtain N2 where N2: "\<And>n. n \<ge> N2 \<Longrightarrow> dist (to_Gromov_completion (v n)) (u n) < e"
        unfolding eventually_sequentially by auto
      have "eventually (\<lambda>n. extended_Gromov_distance (to_Gromov_completion basepoint) (u n) > D2) sequentially"
        by (rule order_tendstoD[OF \<open>(\<lambda>n. extended_Gromov_distance (to_Gromov_completion basepoint) (u n)) \<longlonglongrightarrow> \<infinity>\<close>], fact)
      then obtain N3 where N3: "\<And>n. n \<ge> N3 \<Longrightarrow> extended_Gromov_distance (to_Gromov_completion basepoint) (u n) > D2"
        unfolding eventually_sequentially by auto
      define N where "N = N1+N2+N3"
      have N: "N \<ge> N1" "N \<ge> N2" "N \<ge> N3" unfolding N_def by auto
      have "ennreal M \<le> extended_Gromov_product_at basepoint (to_Gromov_completion (v m)) (to_Gromov_completion (v n))"
        if "n \<ge> N" "m \<ge> N" for m n
      proof (rule D1(3))
        have "dist (to_Gromov_completion (v m)) (to_Gromov_completion (v n))
          \<le> dist (to_Gromov_completion (v m)) (u m) + dist (u m) (u n) + dist (u n) (to_Gromov_completion (v n))"
          by (intro mono_intros)
        also have "... \<le> e + e + e"
          apply (intro mono_intros)
          using N1[of m n] N2[of n] N2[of m] that N by (auto simp add: dist_commute)
        also have "... \<le> e1" unfolding e_def by auto
        finally show "dist (to_Gromov_completion (v m)) (to_Gromov_completion (v n)) \<le> e1" by simp

        have "e \<le> e2" unfolding e_def using \<open>e2 > 0\<close> by auto
        have "D1 \<le> extended_Gromov_product_at basepoint (u m) (to_Gromov_completion (v m))"
          apply (rule D2(3)) using N2[of m] N3[of m] that N \<open>e \<le> e2\<close>
          by (auto simp add: dist_commute extended_Gromov_distance_commute)
        also have "... \<le> extended_Gromov_distance (to_Gromov_completion basepoint) (to_Gromov_completion (v m))"
          using extended_Gromov_product_le_dist[of basepoint "to_Gromov_completion (v m)" "u m"]
          by (simp add: extended_Gromov_product_at_commute)
        finally show "D1 \<le> extended_Gromov_distance (to_Gromov_completion (v m)) (to_Gromov_completion basepoint)"
          by (simp add: extended_Gromov_distance_commute)
      qed
      then have "M \<le> Gromov_product_at basepoint (v m) (v n)" if "n \<ge> N" "m \<ge> N" for m n
        using that by auto
      then show "\<exists>N. \<forall>n\<ge>N. \<forall>m\<ge>N. M \<le> Gromov_product_at basepoint (v m) (v n)"
        by blast
    qed
    then obtain l where l: "l \<in> Gromov_boundary" "(\<lambda>n. to_Gromov_completion (v n)) \<longlonglongrightarrow> l"
      using Gromov_converging_at_boundary_converges by blast
    have "(\<lambda>n. dist (u n) l) \<longlonglongrightarrow> 0+0"
    proof (rule tendsto_sandwich[of "\<lambda>_. 0" _ _ "\<lambda>n. dist (u n) (to_Gromov_completion (v n)) + dist (to_Gromov_completion (v n)) l"])
      show "(\<lambda>n. dist (u n) (to_Gromov_completion (v n)) + dist (to_Gromov_completion (v n)) l) \<longlonglongrightarrow> 0 + 0"
        apply (intro tendsto_intros)
        using iffD1[OF tendsto_dist_iff l(2)] \<open>(\<lambda>n. dist (to_Gromov_completion (v n)) (u n)) \<longlonglongrightarrow> 0\<close>
        by (auto simp add: dist_commute)
    qed (auto simp add: dist_triangle)
    then have "u \<longlonglongrightarrow> l"
      using iffD2[OF tendsto_dist_iff] by auto
    then have "u0 \<longlonglongrightarrow> l"
      unfolding u_def using r(1) \<open>Cauchy u0\<close> Cauchy_converges_subseq by auto
    then show "\<exists>l. u0 \<longlonglongrightarrow> l"
      by auto
  next
    case False
    define C where "C = limsup (\<lambda>n. extended_Gromov_distance (to_Gromov_completion basepoint) (u0 n)) + 1"
    have "C < \<infinity>" unfolding C_def using False less_top by fastforce
    have "limsup (\<lambda>n. extended_Gromov_distance (to_Gromov_completion basepoint) (u0 n)) < C"
      unfolding C_def using False by auto
    then have "eventually (\<lambda>n. extended_Gromov_distance (to_Gromov_completion basepoint) (u0 n) < C) sequentially"
      using Limsup_lessD by blast
    then obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> extended_Gromov_distance (to_Gromov_completion basepoint) (u0 n) < C"
      unfolding eventually_sequentially by auto
    define r where "r = (\<lambda>n. n + N)"
    have r: "strict_mono r" unfolding r_def strict_mono_def by auto
    define u where "u = (u0 o r)"
    have "Cauchy u"
      using \<open>Cauchy u0\<close> r(1) u_def by (simp add: Cauchy_subseq_Cauchy)
    have u: "extended_Gromov_distance (to_Gromov_completion basepoint) (u n) \<le> C" for n
      unfolding u_def comp_def r_def using N by (auto simp add: less_imp_le)
    define v where "v = (\<lambda>n. from_Gromov_completion (u n))"
    have uv: "u n = to_Gromov_completion (v n)" for n
      unfolding v_def apply (rule to_from_Gromov_completion[symmetric]) using u[of n] \<open>C < \<infinity>\<close> by auto
    have "Cauchy v"
    proof (rule metric_CauchyI)
      obtain a::real where a: "a > 0" "\<And>x y::'a Gromov_completion. extended_Gromov_distance (to_Gromov_completion basepoint) x \<le> C \<Longrightarrow> dist x y \<le> a
          \<Longrightarrow> esqrt(extended_Gromov_distance x y) \<le> 2 * ennreal(dist x y)"
        using inside_Gromov_distance_approx[OF \<open>C < \<infinity>\<close>] by auto
      fix e::real assume "e > 0"
      define e2 where "e2 = min (sqrt (e/2) /2) a"
      have "e2 > 0" unfolding e2_def using \<open>e > 0\<close> \<open>a > 0\<close> by auto
      then obtain N where N: "\<And>m n. m \<ge> N \<Longrightarrow> n \<ge> N \<Longrightarrow> dist (u m) (u n) < e2"
        using \<open>Cauchy u\<close> unfolding Cauchy_def by blast
      have "dist (v m) (v n) < e" if "n \<ge> N" "m \<ge> N" for m n
      proof -
        have "ennreal(sqrt(dist (v m) (v n))) = esqrt(extended_Gromov_distance (u m) (u n))"
          unfolding uv by (auto simp add: esqrt_ennreal_ennreal_sqrt)
        also have "... \<le> 2 * ennreal(dist (u m) (u n))"
          apply (rule a(2)) using u[of m] N[OF \<open>m \<ge> N\<close> \<open>n \<ge> N\<close>] unfolding e2_def by auto
        also have "... = ennreal(2 * dist (u m) (u n))"
          by (simp add: ennreal_mult')
        also have "... \<le> ennreal(2 * e2)"
          apply (intro mono_intros) using N[OF \<open>m \<ge> N\<close> \<open>n \<ge> N\<close>] less_imp_le by auto
        finally have "sqrt(dist (v m) (v n)) \<le> 2 * e2"
          unfolding ennreal_le_iff2 using \<open>e2 > 0\<close> by auto
        also have "... \<le> sqrt (e/2)"
          unfolding e2_def by auto
        finally have "dist (v m) (v n) \<le> e/2"
          by auto
        then show ?thesis
          using \<open>e > 0\<close> by auto
      qed
      then show "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (v m) (v n) < e" by auto
    qed
    then obtain l where "v \<longlonglongrightarrow> l"
      using \<open>complete (UNIV::'a set)\<close> complete_def by blast
    then have "u \<longlonglongrightarrow> (to_Gromov_completion l)"
      unfolding uv by auto
    then have "u0 \<longlonglongrightarrow> (to_Gromov_completion l)"
      unfolding u_def using r(1) \<open>Cauchy u0\<close> Cauchy_converges_subseq by auto
    then show "\<exists>l. u0 \<longlonglongrightarrow> l"
      by auto
  qed
qed

instance Gromov_completion::("{Gromov_hyperbolic_space, complete_space}") complete_space
  apply standard
  using Gromov_completion_complete complete_def convergent_def complete_UNIV by auto

text \<open>When the original space is proper, i.e., closed balls are compact, and geodesic, then the
Gromov completion (and therefore the Gromov boundary) are compact. The idea to extract a convergent
subsequence of a sequence $u_n$ in the boundary is to take the point $v_n$ at distance $T$ along
a geodesic tending to the point $u_n$ on the boundary, where $T$ is fixed and large. The points
$v_n$ live in a bounded subset of the space, hence they have a convergent subsequence $v_{j(n)}$.
It follows that $u_{j(n)}$ is almost converging, up to an error that tends to $0$ when $T$ tends
to infinity. By a diagonal argument, we obtain a convergent subsequence of $u_n$.

As we have already proved that the space is complete, there is a shortcut to the above argument,
avoiding subsequences and diagonal argument altogether. Indeed, in a complete space it suffices
to show that for any $\epsilon>0$ it is covered by finitely many balls of radius $\epsilon$ to get
the compactness. This is what we do in the following proof, although the argument is precisely
modelled on the first proof we have explained.\<close>

theorem Gromov_completion_compact:
  assumes "proper (UNIV::'a::Gromov_hyperbolic_space_geodesic set)"
  shows "compact (UNIV::'a Gromov_completion set)"
proof -
  have "\<exists>k. finite k \<and> (UNIV::'a Gromov_completion set) \<subseteq> (\<Union>x\<in>k. ball x e)" if "e>0" for e
  proof -
    define D::real where "D = max 0 (-ln(e/4)/epsilonG(TYPE('a)))"
    have "D \<ge> 0" unfolding D_def by auto
    have "exp(-epsilonG(TYPE('a)) * D) \<le> exp(ln (e / 4))"
      unfolding D_def apply (intro mono_intros) unfolding max_def
      apply auto
      using constant_in_extended_predist_pos(1)[where ?'a = 'a] by (auto simp add: divide_simps)
    then have "exp(-epsilonG(TYPE('a)) * D) \<le> e/4" using \<open>e > 0\<close> by auto
    define e0::real where "e0 = e * e / 16"
    have "e0 > 0" using \<open>e > 0\<close> unfolding e0_def by auto
    obtain k::"'a set" where k: "finite k" "cball basepoint D \<subseteq> (\<Union>x\<in>k. ball x e0)"
      using compact_eq_totally_bounded[of "cball (basepoint::'a) D"] assms \<open>e0 > 0\<close>
      unfolding proper_def by auto
    have A: "\<exists>y \<in> k. dist (to_Gromov_completion y) (to_Gromov_completion x) \<le> e/4" if "dist basepoint x \<le> D" for x::'a
    proof -
      obtain z where z: "z \<in> k" "dist z x < e0" using \<open>dist basepoint x \<le> D\<close> k(2) by auto
      have "ennreal(dist (to_Gromov_completion z) (to_Gromov_completion x)) \<le> esqrt(extended_Gromov_distance (to_Gromov_completion z) (to_Gromov_completion x))"
        by (intro mono_intros)
      also have "... = ennreal(sqrt (dist z x))"
        by auto
      finally have "dist (to_Gromov_completion z) (to_Gromov_completion x) \<le> sqrt (dist z x)"
        by auto
      also have "... \<le> sqrt e0"
        using z(2) by auto
      also have "... \<le> e/4"
        unfolding e0_def using \<open>e > 0\<close> by (auto simp add: less_imp_le real_sqrt_divide)
      finally have "dist (to_Gromov_completion z) (to_Gromov_completion x) \<le> e/4"
        by auto
      then show ?thesis
        using \<open>z \<in> k\<close> by auto
    qed
    have B: "\<exists>y \<in> k. dist (to_Gromov_completion y) (to_Gromov_completion x) \<le> e/2" for x
    proof (cases "dist basepoint x \<le> D")
      case True
      have "e/4 \<le> e/2" using \<open>e > 0\<close> by auto
      then show ?thesis using A[OF True] by force
    next
      case False
      define x2 where "x2 = geodesic_segment_param {basepoint--x} basepoint D"
      have *: "Gromov_product_at basepoint x x2 = D"
        unfolding x2_def apply (rule Gromov_product_geodesic_segment) using False \<open>D \<ge> 0\<close> by auto
      have "ennreal(dist (to_Gromov_completion x) (to_Gromov_completion x2))
            \<le> eexp (- enn2ereal(epsilonG(TYPE('a)) * extended_Gromov_product_at basepoint (to_Gromov_completion x) (to_Gromov_completion x2)))"
        by (intro mono_intros)
      also have "... = eexp (- enn2ereal(epsilonG(TYPE('a)) * ennreal D))"
        using * by auto
      also have "... = ennreal(exp(-epsilonG(TYPE('a)) * D))"
        apply (subst ennreal_mult'[symmetric]) using \<open>D \<ge> 0\<close> by auto
      also have "...\<le> ennreal(e/4)"
        by (intro mono_intros, fact)
      finally have "dist (to_Gromov_completion x) (to_Gromov_completion x2) \<le> e/4"
        using \<open>e > 0\<close> by auto
      have "dist basepoint x2 \<le> D"
        unfolding x2_def using False \<open>0 \<le> D\<close> by auto
      then obtain y where "y \<in> k" "dist (to_Gromov_completion y) (to_Gromov_completion x2) \<le> e/4"
        using A by auto
      have "dist (to_Gromov_completion y) (to_Gromov_completion x)
            \<le> dist (to_Gromov_completion y) (to_Gromov_completion x2) + dist (to_Gromov_completion x) (to_Gromov_completion x2)"
        by (intro mono_intros)
      also have "... \<le> e/4 + e/4"
        by (intro mono_intros, fact, fact)
      also have "... = e/2" by simp
      finally show ?thesis using \<open>y \<in> k\<close> by auto
    qed
    have C: "\<exists>y \<in> k. dist (to_Gromov_completion y) x < e" for x
    proof -
      obtain x1 where x1: "dist x x1 < e/2" "x1 \<in> range to_Gromov_completion"
        using to_Gromov_completion_range_dense \<open>e > 0\<close>
        by (metis (no_types, hide_lams) UNIV_I closure_approachableD divide_pos_pos zero_less_numeral)
      then obtain z where z: "x1 = to_Gromov_completion z" by auto
      then obtain y where y: "y \<in> k" "dist (to_Gromov_completion y) (to_Gromov_completion z) \<le> e/2"
        using B by auto
      have "dist (to_Gromov_completion y) x \<le>
              dist (to_Gromov_completion y) (to_Gromov_completion z) + dist x x1"
        unfolding z by (intro mono_intros)
      also have "... < e/2 + e/2"
        using x1(1) y(2) by auto
      also have "... = e"
        by auto
      finally show ?thesis using \<open>y \<in> k\<close> by auto
    qed
    show ?thesis
      apply (rule exI[of _ "to_Gromov_completion`k"])
      using C \<open>finite k\<close> by auto
  qed
  then show ?thesis
    unfolding compact_eq_totally_bounded
    using Gromov_completion_complete[OF proper_imp_complete[OF assms]] by auto
qed

text \<open>If the inner space is second countable, so is its completion, as the former is dense in the
latter.\<close>

instance Gromov_completion::("{Gromov_hyperbolic_space, second_countable_topology}") second_countable_topology
proof
  obtain A::"'a set" where "countable A" "closure A = UNIV"
    using second_countable_metric_dense_subset by auto
  define Ab where "Ab = to_Gromov_completion`A"
  have "range to_Gromov_completion \<subseteq> closure Ab"
    unfolding Ab_def
    by (metis \<open>closure A = UNIV\<close> closed_closure closure_subset image_closure_subset to_Gromov_completion_continuous)
  then have "closure Ab = UNIV"
    by (metis closed_closure closure_minimal dual_order.antisym to_Gromov_completion_range_dense top_greatest)
  moreover have "countable Ab" unfolding Ab_def using \<open>countable A\<close> by auto
  ultimately have "\<exists>Ab::'a Gromov_completion set. countable Ab \<and> closure Ab = UNIV"
    by auto
  then show "\<exists>B::'a Gromov_completion set set. countable B \<and> open = generate_topology B"
    using second_countable_iff_dense_countable_subset topological_basis_imp_subbasis by auto
qed

text \<open>The same follows readily for the Polish space property.\<close>

instance metric_completion::("{Gromov_hyperbolic_space, polish_space}") polish_space
by standard


subsection \<open>The Gromov completion of the real line.\<close>

text \<open>We show in the paragraph that the Gromov completion of the real line is obtained by adding
one point at $+\infty$ and one point at $-\infty$. In other words, it coincides with ereal.

To show this, we have to understand which sequences of reals are Gromov-converging to the
boundary. We show in the next lemma that they are exactly the sequences that converge to $-\infty$
or to $+\infty$.\<close>

lemma real_Gromov_converging_to_boundary:
  fixes u::"nat \<Rightarrow> real"
  shows "Gromov_converging_at_boundary u \<longleftrightarrow> ((u \<longlonglongrightarrow> \<infinity>) \<or> (u \<longlonglongrightarrow> - \<infinity>))"
proof -
  have *: "Gromov_product_at 0 m n \<ge> min m n" for m n::real
    unfolding Gromov_product_at_def dist_real_def by auto
  have A: "Gromov_converging_at_boundary u" if "u \<longlonglongrightarrow> \<infinity>" for u::"nat \<Rightarrow> real"
  proof (rule Gromov_converging_at_boundaryI[of 0])
    fix M::real
    have "eventually (\<lambda>n. ereal (u n) > M) sequentially"
      by (rule order_tendstoD(1)[OF \<open>u \<longlonglongrightarrow> \<infinity>\<close>, of "ereal M"], auto)
    then obtain N where "\<And>n. n \<ge> N \<Longrightarrow> ereal (u n) > M"
      unfolding eventually_sequentially by auto
    then have A: "u n \<ge> M" if "n \<ge> N" for n
      by (simp add: less_imp_le that)
    have "M \<le> Gromov_product_at 0 (u m) (u n)" if "n \<ge> N" "m \<ge> N" for m n
      using A[OF \<open>m \<ge> N\<close>] A[OF \<open>n \<ge> N\<close>] *[of "u m" "u n"] by auto
    then show "\<exists>N. \<forall>n\<ge>N. \<forall>m\<ge>N. M \<le> Gromov_product_at 0 (u m) (u n)"
      by auto
  qed
  have *: "Gromov_product_at 0 m n \<ge> - max m n" for m n::real
    unfolding Gromov_product_at_def dist_real_def by auto
  have B: "Gromov_converging_at_boundary u" if "u \<longlonglongrightarrow> -\<infinity>" for u::"nat \<Rightarrow> real"
  proof (rule Gromov_converging_at_boundaryI[of 0])
    fix M::real
    have "eventually (\<lambda>n. ereal (u n) < - M) sequentially"
      by (rule order_tendstoD(2)[OF \<open>u \<longlonglongrightarrow> -\<infinity>\<close>, of "ereal (-M)"], auto)
    then obtain N where "\<And>n. n \<ge> N \<Longrightarrow> ereal (u n) < - M"
      unfolding eventually_sequentially by auto
    then have A: "u n \<le> - M" if "n \<ge> N" for n
      by (simp add: less_imp_le that)
    have "M \<le> Gromov_product_at 0 (u m) (u n)" if "n \<ge> N" "m \<ge> N" for m n
      using A[OF \<open>m \<ge> N\<close>] A[OF \<open>n \<ge> N\<close>] *[of "u m" "u n"] by auto
    then show "\<exists>N. \<forall>n\<ge>N. \<forall>m\<ge>N. M \<le> Gromov_product_at 0 (u m) (u n)"
      by auto
  qed
  have L: "(u \<longlonglongrightarrow> \<infinity>) \<or> (u \<longlonglongrightarrow> - \<infinity>)" if "Gromov_converging_at_boundary u" for u::"nat \<Rightarrow> real"
  proof -
    have "(\<lambda>n. abs(u n)) \<longlonglongrightarrow> \<infinity>"
      using Gromov_converging_at_boundary_imp_unbounded[OF that, of 0] unfolding dist_real_def by auto

    obtain r where r: "strict_mono r" "(\<lambda>n. ereal (u (r n))) \<longlonglongrightarrow> liminf (\<lambda>n. ereal(u n))"
      using liminf_subseq_lim[of "\<lambda>n. ereal(u n)"] unfolding comp_def by auto
    have "(\<lambda>n. abs(ereal (u (r n)))) \<longlonglongrightarrow> abs(liminf (\<lambda>n. ereal(u n)))"
      apply (intro tendsto_intros) using r(2) by auto
    moreover have "(\<lambda>n. abs(ereal (u (r n)))) \<longlonglongrightarrow> \<infinity>"
      using \<open>(\<lambda>n. abs(u n)) \<longlonglongrightarrow> \<infinity>\<close> apply auto
      using filterlim_compose filterlim_subseq[OF r(1)] by blast
    ultimately have A: "abs(liminf (\<lambda>n. ereal(u n))) = \<infinity>"
      using LIMSEQ_unique by auto

    obtain r where r: "strict_mono r" "(\<lambda>n. ereal (u (r n))) \<longlonglongrightarrow> limsup (\<lambda>n. ereal(u n))"
      using limsup_subseq_lim[of "\<lambda>n. ereal(u n)"] unfolding comp_def by auto
    have "(\<lambda>n. abs(ereal (u (r n)))) \<longlonglongrightarrow> abs(limsup (\<lambda>n. ereal(u n)))"
      apply (intro tendsto_intros) using r(2) by auto
    moreover have "(\<lambda>n. abs(ereal (u (r n)))) \<longlonglongrightarrow> \<infinity>"
      using \<open>(\<lambda>n. abs(u n)) \<longlonglongrightarrow> \<infinity>\<close> apply auto
      using filterlim_compose filterlim_subseq[OF r(1)] by blast
    ultimately have B: "abs(limsup (\<lambda>n. ereal(u n))) = \<infinity>"
      using LIMSEQ_unique by auto

    have "\<not>(liminf u = - \<infinity> \<and> limsup u = \<infinity>)"
    proof (rule ccontr, auto)
      assume "liminf u = -\<infinity>" "limsup u = \<infinity>"
      have "\<exists>N. \<forall>n \<ge> N. \<forall>m \<ge>N. Gromov_product_at 0 (u m) (u n) \<ge> 1"
        using that unfolding Gromov_converging_at_boundary_def by blast
      then obtain N where N: "\<And>m n. m \<ge> N \<Longrightarrow> n \<ge> N \<Longrightarrow> Gromov_product_at 0 (u m) (u n) \<ge> 1"
        by auto
      have "\<exists>n \<ge> N. ereal(u n) > ereal 0"
        apply (rule limsup_obtain) unfolding \<open>limsup u = \<infinity>\<close> by auto
      then obtain n where n: "n \<ge> N" "u n > 0" by auto

      have "\<exists>n \<ge> N. ereal(u n) < ereal 0"
        apply (rule liminf_obtain) unfolding \<open>liminf u = -\<infinity>\<close> by auto
      then obtain m where m: "m \<ge> N" "u m < 0" by auto

      have "Gromov_product_at 0 (u m) (u n) = 0"
        unfolding Gromov_product_at_def dist_real_def using m n by auto
      then show False using N[OF m(1) n(1)] by auto
    qed
    then have "liminf u = \<infinity> \<or> limsup u = - \<infinity>"
      using A B by auto
    then show ?thesis
      by (simp add: Liminf_PInfty Limsup_MInfty)
  qed
  show ?thesis using L A B by auto
qed

text \<open>There is one single point at infinity in the Gromov completion of reals, i.e., two
sequences tending to infinity are equivalent.\<close>

lemma real_Gromov_completion_rel_PInf:
  fixes u v::"nat \<Rightarrow> real"
  assumes "u \<longlonglongrightarrow> \<infinity>" "v \<longlonglongrightarrow> \<infinity>"
  shows "Gromov_completion_rel u v"
proof -
  have *: "Gromov_product_at 0 m n \<ge> min m n" for m n::real
    unfolding Gromov_product_at_def dist_real_def by auto
  have **: "Gromov_product_at a m n \<ge> min m n - abs a" for m n a::real
    using Gromov_product_at_diff1[of 0 m n a] *[of m n] by auto
  have "(\<lambda>n. Gromov_product_at a (u n) (v n)) \<longlonglongrightarrow> \<infinity>" for a
  proof (rule tendsto_sandwich[of "\<lambda>n. min (u n) (v n) - abs a" _ _ "\<lambda>n. \<infinity>"])
    have "ereal (min (u n) (v n) - \<bar>a\<bar>) \<le> ereal (Gromov_product_at a (u n) (v n))" for n
      using **[of "u n" "v n" a] by auto
    then show "\<forall>\<^sub>F n in sequentially. ereal (min (u n) (v n) - \<bar>a\<bar>) \<le> ereal (Gromov_product_at a (u n) (v n))"
      by auto
    have "(\<lambda>x. min (ereal(u x)) (ereal (v x)) - ereal \<bar>a\<bar>) \<longlonglongrightarrow> min \<infinity> \<infinity> - ereal \<bar>a\<bar>"
      apply (intro tendsto_intros) using assms by auto
    then show "(\<lambda>x. ereal (min (u x) (v x) - \<bar>a\<bar>)) \<longlonglongrightarrow> \<infinity>"
      apply auto unfolding ereal_minus(1)[symmetric] by auto
  qed (auto)
  moreover have "Gromov_converging_at_boundary u" "Gromov_converging_at_boundary v"
    using real_Gromov_converging_to_boundary assms by auto
  ultimately show ?thesis unfolding Gromov_completion_rel_def by auto
qed

text \<open>There is one single point at minus infinity in the Gromov completion of reals, i.e., two
sequences tending to minus infinity are equivalent.\<close>

lemma real_Gromov_completion_rel_MInf:
  fixes u v::"nat \<Rightarrow> real"
  assumes "u \<longlonglongrightarrow> -\<infinity>" "v \<longlonglongrightarrow> -\<infinity>"
  shows "Gromov_completion_rel u v"
proof -
  have *: "Gromov_product_at 0 m n \<ge> - max m n" for m n::real
    unfolding Gromov_product_at_def dist_real_def by auto
  have **: "Gromov_product_at a m n \<ge> - max m n - abs a" for m n a::real
    using Gromov_product_at_diff1[of 0 m n a] *[of m n] by auto
  have "(\<lambda>n. Gromov_product_at a (u n) (v n)) \<longlonglongrightarrow> \<infinity>" for a
  proof (rule tendsto_sandwich[of "\<lambda>n. min (-u n) (-v n) - abs a" _ _ "\<lambda>n. \<infinity>"])
    have "ereal (min (-u n) (-v n) - \<bar>a\<bar>) \<le> ereal (Gromov_product_at a (u n) (v n))" for n
      using **[of "u n" "v n" a] by auto
    then show "\<forall>\<^sub>F n in sequentially. ereal (min (-u n) (-v n) - \<bar>a\<bar>) \<le> ereal (Gromov_product_at a (u n) (v n))"
      by auto
    have "(\<lambda>x. min (-ereal(u x)) (-ereal (v x)) - ereal \<bar>a\<bar>) \<longlonglongrightarrow> min (-(-\<infinity>)) (-(-\<infinity>)) - ereal \<bar>a\<bar>"
      apply (intro tendsto_intros) using assms by auto
    then show "(\<lambda>x. ereal (min (-u x) (-v x) - \<bar>a\<bar>)) \<longlonglongrightarrow> \<infinity>"
      apply auto unfolding ereal_minus(1)[symmetric] by auto
  qed (auto)
  moreover have "Gromov_converging_at_boundary u" "Gromov_converging_at_boundary v"
    using real_Gromov_converging_to_boundary assms by auto
  ultimately show ?thesis unfolding Gromov_completion_rel_def by auto
qed

text \<open>It follows from the two lemmas above that the Gromov completion of reals is obtained by
adding one single point at infinity and one single point at minus infinity. Hence, it is in
bijection with the extended reals.\<close>

function to_real_Gromov_completion::"ereal \<Rightarrow> real Gromov_completion"
  where "to_real_Gromov_completion (ereal r) = to_Gromov_completion r"
  | "to_real_Gromov_completion (\<infinity>) = abs_Gromov_completion (\<lambda>n. n)"
  | "to_real_Gromov_completion (-\<infinity>) = abs_Gromov_completion (\<lambda>n. -n)"
by (auto intro: ereal_cases)
termination by standard (rule wf_empty)

text \<open>To prove the bijectivity, we prove by hand injectivity and surjectivity using the above
lemmas.\<close>

lemma bij_to_real_Gromov_completion:
  "bij to_real_Gromov_completion"
proof -
  have [simp]: "Gromov_completion_rel (\<lambda>n. n) (\<lambda>n. n)"
    by (intro real_Gromov_completion_rel_PInf tendsto_intros)
  have [simp]: "Gromov_completion_rel (\<lambda>n. -real n) (\<lambda>n. -real n)"
    by (intro real_Gromov_completion_rel_MInf tendsto_intros)

  have "\<exists>x. to_real_Gromov_completion x = y" for y
  proof (cases "y \<in> Gromov_boundary")
    case False
    then obtain x where "y = to_Gromov_completion x" unfolding Gromov_boundary_def by auto
    then have "y = to_real_Gromov_completion x" by auto
    then show ?thesis by blast
  next
    case True
    define u where u: "u = rep_Gromov_completion y"
    have y: "abs_Gromov_completion u = y" "Gromov_completion_rel u u"
      unfolding u using Quotient3_abs_rep[OF Quotient3_Gromov_completion]
      Quotient3_rep_reflp[OF Quotient3_Gromov_completion] by auto
    have "Gromov_converging_at_boundary u"
      using u True by (simp add: Gromov_boundary_rep_converging)
    then have "(u \<longlonglongrightarrow> \<infinity>) \<or> (u \<longlonglongrightarrow> - \<infinity>)" using real_Gromov_converging_to_boundary by auto
    then show ?thesis
    proof
      assume "u \<longlonglongrightarrow> \<infinity>"
      have "abs_Gromov_completion (\<lambda>n. n) = abs_Gromov_completion u "
        apply (rule Quotient3_rel_abs[OF Quotient3_Gromov_completion])
        by (intro real_Gromov_completion_rel_PInf[OF _ \<open>u \<longlonglongrightarrow> \<infinity>\<close>] tendsto_intros)
      then have "to_real_Gromov_completion \<infinity> = y"
        unfolding y by auto
      then show ?thesis by blast
    next
      assume "u \<longlonglongrightarrow> -\<infinity>"
      have "abs_Gromov_completion (\<lambda>n. -real n) = abs_Gromov_completion u "
        apply (rule Quotient3_rel_abs[OF Quotient3_Gromov_completion])
        by (intro real_Gromov_completion_rel_MInf[OF _ \<open>u \<longlonglongrightarrow> -\<infinity>\<close>] tendsto_intros)
      then have "to_real_Gromov_completion (-\<infinity>) = y"
        unfolding y by auto
      then show ?thesis by blast
    qed
  qed
  then have "surj to_real_Gromov_completion"
    unfolding surj_def by metis

  have "to_real_Gromov_completion \<infinity> \<in> Gromov_boundary"
       "to_real_Gromov_completion (-\<infinity>) \<in> Gromov_boundary"
    by (auto intro!: abs_Gromov_completion_in_Gromov_boundary tendsto_intros simp add: real_Gromov_converging_to_boundary)
  moreover have "to_real_Gromov_completion \<infinity> \<noteq> to_real_Gromov_completion (-\<infinity>)"
  proof -
    have "Gromov_product_at 0 (real n) (-real n) = 0" for n::nat
      unfolding Gromov_product_at_def dist_real_def by auto
    then have *: "(\<lambda>n. ereal(Gromov_product_at 0 (real n) (-real n))) \<longlonglongrightarrow> ereal 0" by auto
    have "\<not>((\<lambda>n. Gromov_product_at 0 (real n) (-real n)) \<longlonglongrightarrow> \<infinity>)"
      using LIMSEQ_unique[OF *] by fastforce
    then have "\<not>(Gromov_completion_rel (\<lambda>n. n) (\<lambda>n. -n))"
      unfolding Gromov_completion_rel_def by auto (metis nat.simps(3) of_nat_0 of_nat_eq_0_iff)
    then show ?thesis
      using Quotient3_rel[OF Quotient3_Gromov_completion, of "\<lambda>n. n" "\<lambda>n. -real n"] by auto
  qed
  ultimately have "x = y" if "to_real_Gromov_completion x = to_real_Gromov_completion y" for x y
    using that injD[OF to_Gromov_completion_inj] apply (cases x y rule: ereal2_cases)
    by (auto) (metis not_in_Gromov_boundary')+
  then have "inj to_real_Gromov_completion"
    unfolding inj_def by auto
  then show "bij to_real_Gromov_completion"
    using \<open>surj to_real_Gromov_completion\<close> by (simp add: bijI)
qed

text \<open>Next, we prove that we have a homeomorphism. By compactness of ereals, it suffices to show
that the inclusion map is continuous everywhere. It would be a pain to distinguish all the time if points are
at infinity or not, we rather use a criterion saying that it suffices to prove sequential
continuity for sequences taking values in a dense subset of the space, here we take the reals.
Hence, it suffices to show that if a sequence of reals $v_n$ converges to a limit $a$ in the
extended reals, then the image of $v_n$ in the Gromov completion (which is an inner point) converges
to the point corresponding to $a$. We treat separately the cases $a\in \mathbb{R}$, $a = \infty$ and
$a = -\infty$. In the first case, everything is trivial. In the other cases, we have characterized
in general sequences inside the space that converge to a boundary point, as sequences in the equivalence
class defining this boundary point. Since we have described explicitly these equivalence classes in
the case of the Gromov completion of the reals (they are respectively the sequences tending to
$\infty$ and to $-\infty$), the result follows readily without any additional computation.\<close>

proposition homeo_to_real_Gromov_completion:
  "homeomorphism_on UNIV to_real_Gromov_completion"
proof (rule homeomorphism_on_compact)
  show "inj to_real_Gromov_completion"
    using bij_to_real_Gromov_completion by (simp add: bij_betw_def)
  show "compact (UNIV::ereal set)"
    by (simp add: compact_UNIV)
  show "continuous_on UNIV to_real_Gromov_completion"
  proof (rule continuous_on_extension_sequentially[of _ "{-\<infinity><..<\<infinity>}"], auto)
    fix u::"nat \<Rightarrow> ereal" and b::ereal assume u: "\<forall>n. u n \<noteq> - \<infinity> \<and> u n \<noteq> \<infinity>" "u \<longlonglongrightarrow> b"
    define v where "v = (\<lambda>n. real_of_ereal (u n))"
    have uv: "u n = ereal (v n)" for n
      using u unfolding v_def by (simp add: ereal_infinity_cases ereal_real)
    show "(\<lambda>n. to_real_Gromov_completion (u n)) \<longlonglongrightarrow> to_real_Gromov_completion b"
    proof (cases b)
      case (real r)
      then show ?thesis using \<open>u \<longlonglongrightarrow> b\<close> unfolding uv by auto
    next
      case PInf
      then have *: "(\<lambda>n. ereal (v n)) \<longlonglongrightarrow> \<infinity>" using \<open>u \<longlonglongrightarrow> b\<close> unfolding uv by auto
      have A: "Gromov_completion_rel real v" "Gromov_completion_rel real real" "Gromov_completion_rel v v"
        by (auto intro!: real_Gromov_completion_rel_PInf * tendsto_intros)
      then have B: "abs_Gromov_completion v = abs_Gromov_completion real"
        using Quotient3_rel_abs[OF Quotient3_Gromov_completion] by force
      then show ?thesis using \<open>u \<longlonglongrightarrow> b\<close> PInf
        unfolding uv apply auto
        apply (subst Gromov_completion_converge_to_boundary)
        using id_nat_ereal_tendsto_PInf real_Gromov_converging_to_boundary A B by auto
    next
      case MInf
      then have *: "(\<lambda>n. ereal (v n)) \<longlonglongrightarrow> -\<infinity>" using \<open>u \<longlonglongrightarrow> b\<close> unfolding uv by auto
      have A: "Gromov_completion_rel (\<lambda>n. -real n) v" "Gromov_completion_rel (\<lambda>n. -real n) (\<lambda>n. -real n)" "Gromov_completion_rel v v"
        by (auto intro!: real_Gromov_completion_rel_MInf * tendsto_intros)
      then have B: "abs_Gromov_completion v = abs_Gromov_completion (\<lambda>n. -real n)"
        using Quotient3_rel_abs[OF Quotient3_Gromov_completion] by force
      then show ?thesis using \<open>u \<longlonglongrightarrow> b\<close> MInf
        unfolding uv apply auto
        apply (subst Gromov_completion_converge_to_boundary)
        using id_nat_ereal_tendsto_PInf real_Gromov_converging_to_boundary A B
        by (auto simp add: ereal_minus_real_tendsto_MInf)
    qed
  qed
qed


section \<open>Extension of quasi-isometries to the boundary\<close>

text \<open>In this section, we show that a quasi-isometry between geodesic Gromov hyperbolic spaces
extends to a homeomorphism between their boundaries.\<close>

text \<open>Applying a quasi-isometry on a geodesic triangle essentially sends it to a geodesic triangle,
in hyperbolic spaces. It follows that, up to an additive constant, the Gromov product, which is the
distance to the center of the triangle, is multiplied by a constant between $\lambda^{-1}$ and
$\lambda$ when one applies a quasi-isometry. This argument is given in the next lemma. This implies
that two points are close in the Gromov completion if and only if their images are also close in the
Gromov completion of the image. Essentially, this lemma implies that a quasi-isometry has a
continuous extension to the Gromov boundary, which is a homeomorphism.\<close>

lemma Gromov_product_at_quasi_isometry:
  fixes f::"'a::Gromov_hyperbolic_space_geodesic \<Rightarrow> 'b::Gromov_hyperbolic_space_geodesic"
  assumes "quasi_isometry lambda C f"
  shows "Gromov_product_at (f x) (f y) (f z) \<ge> Gromov_product_at x y z / lambda - 165 * lambda^2 * (C + lambda + deltaG(TYPE('b))^2 + deltaG(TYPE('a)))"
        "Gromov_product_at (f x) (f y) (f z) \<le> lambda * Gromov_product_at x y z + 165 * lambda^2 * (C + lambda + deltaG(TYPE('b))^2 + deltaG(TYPE('a)))"
proof -
  have "lambda \<ge> 1" "C \<ge> 0" using quasi_isometry_onD[OF assms(1)] by auto
  define D where "D = 81 * lambda^2 * (C + lambda + deltaG(TYPE('b))^2)"
  have Dxy: "hausdorff_distance (f`{x--y}) {f x--f y} \<le> D"
    unfolding D_def apply (rule geodesic_quasi_isometric_image[OF assms(1)]) by auto
  have Dyz: "hausdorff_distance (f`{y--z}) {f y--f z} \<le> D"
    unfolding D_def apply (rule geodesic_quasi_isometric_image[OF assms(1)]) by auto
  have Dxz: "hausdorff_distance (f`{x--z}) {f x--f z} \<le> D"
    unfolding D_def apply (rule geodesic_quasi_isometric_image[OF assms(1)]) by auto

  define E where "E = (lambda * (4 * deltaG(TYPE('a))) + C) + D"
  have "E \<ge> 0" unfolding E_def D_def using \<open>lambda \<ge> 1\<close> \<open>C \<ge> 0\<close> by auto
  obtain w where w: "infdist w {x--y} \<le> 4 * deltaG(TYPE('a))"
                    "infdist w {x--z} \<le> 4 * deltaG(TYPE('a))"
                    "infdist w {y--z} \<le> 4 * deltaG(TYPE('a))"
                    "dist w x = Gromov_product_at x y z"
    using slim_triangle[of "{x--y}" x y "{x--z}" z "{y--z}"] by auto
  have "infdist (f w) {f x--f y} \<le> infdist (f w) (f`{x--y}) + hausdorff_distance (f`{x--y}) {f x--f y}"
    by (intro mono_intros quasi_isometry_on_bounded[OF quasi_isometry_on_subset[OF assms(1)], of "{x--y}"], auto)
  also have "... \<le> (lambda * infdist w {x--y} + C) + D"
    apply (intro mono_intros) using quasi_isometry_on_infdist[OF assms(1)] Dxy by auto
  also have "... \<le> (lambda * (4 * deltaG(TYPE('a))) + C) + D"
    apply (intro mono_intros) using w \<open>lambda \<ge> 1\<close> by auto
  finally have Exy: "infdist (f w) {f x--f y} \<le> E" unfolding E_def by auto

  have "infdist (f w) {f y--f z} \<le> infdist (f w) (f`{y--z}) + hausdorff_distance (f`{y--z}) {f y--f z}"
    by (intro mono_intros quasi_isometry_on_bounded[OF quasi_isometry_on_subset[OF assms(1)], of "{y--z}"], auto)
  also have "... \<le> (lambda * infdist w {y--z} + C) + D"
    apply (intro mono_intros) using quasi_isometry_on_infdist[OF assms(1)] Dyz by auto
  also have "... \<le> (lambda * (4 * deltaG(TYPE('a))) + C) + D"
    apply (intro mono_intros) using w \<open>lambda \<ge> 1\<close> by auto
  finally have Eyz: "infdist (f w) {f y--f z} \<le> E" unfolding E_def by auto

  have "infdist (f w) {f x--f z} \<le> infdist (f w) (f`{x--z}) + hausdorff_distance (f`{x--z}) {f x--f z}"
    by (intro mono_intros quasi_isometry_on_bounded[OF quasi_isometry_on_subset[OF assms(1)], of "{x--z}"], auto)
  also have "... \<le> (lambda * infdist w {x--z} + C) + D"
    apply (intro mono_intros) using quasi_isometry_on_infdist[OF assms(1)] Dxz by auto
  also have "... \<le> (lambda * (4 * deltaG(TYPE('a))) + C) + D"
    apply (intro mono_intros) using w \<open>lambda \<ge> 1\<close> by auto
  finally have Exz: "infdist (f w) {f x--f z} \<le> E" unfolding E_def by auto

  have "2 * ((1/lambda * dist w x - C)) \<le> 2 * dist (f w) (f x)"
    using quasi_isometry_onD(2)[OF assms(1), of w x] by auto
  also have "... = (dist (f w) (f x) + dist (f w) (f y)) + (dist (f w) (f x) + dist (f w) (f z)) - (dist (f w) (f y) + dist (f w) (f z))"
    by auto
  also have "... \<le> (dist (f x) (f y) + 2 * infdist (f w) {f x--f y}) + (dist (f x) (f z) + 2 * infdist (f w) {f x--f z}) - dist (f y) (f z)"
    by (intro geodesic_segment_distance mono_intros, auto)
  also have "... \<le> 2 * Gromov_product_at (f x) (f y) (f z) + 4 * E"
    unfolding Gromov_product_at_def using Exy Exz by (auto simp add: algebra_simps divide_simps)
  finally have *: "Gromov_product_at x y z / lambda - C - 2 * E \<le> Gromov_product_at (f x) (f y) (f z)"
    unfolding w(4) by simp

  have "2 * Gromov_product_at (f x) (f y) (f z) - 2 * E \<le> 2 * Gromov_product_at (f x) (f y) (f z) - 2 * infdist (f w) {f y--f z}"
    using Eyz by auto
  also have "... = dist (f x) (f y) + dist (f x) (f z) - (dist (f y) (f z) + 2 * infdist (f w) {f y--f z})"
    unfolding Gromov_product_at_def by (auto simp add: algebra_simps divide_simps)
  also have "... \<le> (dist (f w) (f x) + dist (f w) (f y)) + (dist (f w) (f x) + dist (f w) (f z)) - (dist (f w) (f y) + dist (f w) (f z))"
    by (intro geodesic_segment_distance mono_intros, auto)
  also have "... = 2 * dist (f w) (f x)"
    by auto
  also have "... \<le> 2 * (lambda * dist w x + C)"
    using quasi_isometry_onD(1)[OF assms(1), of w x] by auto
  finally have "Gromov_product_at (f x) (f y) (f z) \<le> lambda * dist w x + C + E"
    by auto
  then have **: "Gromov_product_at (f x) (f y) (f z) \<le> lambda * Gromov_product_at x y z + C + 2 * E"
    unfolding w(4) using \<open>E \<ge> 0\<close> by auto

  have "C + 2 * E = 1 * 1 * C + 2 * ((lambda * 1 * 4 * deltaG(TYPE('a)) + 1 * 1 * C) + 81 * lambda * lambda * (C + lambda + deltaG(TYPE('b))^2))"
    unfolding E_def D_def power2_eq_square by auto
  also have "... \<le> lambda * lambda * C + 2 * ((lambda * lambda * 4 * deltaG(TYPE('a)) + lambda * lambda * C) + 81 * lambda * lambda * (C + lambda + deltaG(TYPE('b))^2))"
    apply (intro mono_intros \<open>lambda \<ge> 1\<close> \<open>C \<ge> 0\<close>) using \<open>lambda \<ge> 1\<close> by auto
  also have "... = lambda * lambda * (165 * C + 162 * lambda + 162 * deltaG(TYPE('b))^2 + 8 * deltaG(TYPE('a)))"
    by (simp add: algebra_simps)
  also have "... \<le> lambda * lambda * (165 * C + 165 * lambda + 165 * deltaG(TYPE('b))^2 + 165 * deltaG(TYPE('a)))"
    apply (intro mono_intros) using \<open>lambda \<ge> 1\<close> by auto
  finally have I: "C + 2 * E \<le> 165 * lambda^2 * (C + lambda + deltaG(TYPE('b))^2 + deltaG(TYPE('a)))"
    by (auto simp add: algebra_simps power2_eq_square)

  show "Gromov_product_at (f x) (f y) (f z) \<ge> Gromov_product_at x y z / lambda - 165 * lambda^2 * (C + lambda + deltaG(TYPE('b))^2 + deltaG(TYPE('a)))"
    using * I by auto
  show "Gromov_product_at (f x) (f y) (f z) \<le> lambda * Gromov_product_at x y z + 165 * lambda^2 * (C + lambda + deltaG(TYPE('b))^2 + deltaG(TYPE('a)))"
    using ** I by auto
qed

lemma Gromov_converging_at_infinity_quasi_isometry:
  fixes f::"'a::Gromov_hyperbolic_space_geodesic \<Rightarrow> 'b::Gromov_hyperbolic_space_geodesic"
  assumes "lambda C-quasi_isometry f"
  shows "Gromov_converging_at_boundary (\<lambda>n. f (u n)) \<longleftrightarrow> Gromov_converging_at_boundary u"
proof
  assume "Gromov_converging_at_boundary u"
  show "Gromov_converging_at_boundary (\<lambda>n. f (u n))"
  proof (rule Gromov_converging_at_boundaryI[of "f (basepoint)"])
    have "lambda \<ge> 1" "C \<ge> 0" using quasi_isometry_onD[OF assms(1)] by auto
    define D where "D = 165 * lambda^2 * (C + lambda + deltaG(TYPE('b))^2 + deltaG(TYPE('a)))"
    fix M::real
    obtain M2::real where M2: "M = M2/lambda - D"
      using \<open>lambda \<ge> 1\<close> by (auto simp add: algebra_simps divide_simps)
    obtain N where N: "\<And>m n. m \<ge> N \<Longrightarrow> n \<ge> N \<Longrightarrow> Gromov_product_at basepoint (u m) (u n) \<ge> M2"
      using \<open>Gromov_converging_at_boundary u\<close> unfolding Gromov_converging_at_boundary_def by blast
    have "Gromov_product_at (f basepoint) (f (u m)) (f (u n)) \<ge> M" if "m \<ge> N" "n \<ge> N" for m n
    proof -
      have "M \<le> Gromov_product_at basepoint (u m) (u n)/lambda - D"
        unfolding M2 using N[OF that] \<open>lambda \<ge> 1\<close> by (auto simp add: divide_simps)
      also have "... \<le> Gromov_product_at (f basepoint) (f (u m)) (f (u n))"
        unfolding D_def by (rule Gromov_product_at_quasi_isometry[OF assms(1)])
      finally show ?thesis by simp
    qed
    then show "\<exists>N. \<forall>n\<ge>N. \<forall>m\<ge>N. M \<le> Gromov_product_at (f basepoint) (f (u m)) (f (u n))"
      unfolding comp_def by auto
  qed
next
  assume "Gromov_converging_at_boundary (\<lambda>n. f (u n))"
  show "Gromov_converging_at_boundary u"
  proof (rule Gromov_converging_at_boundaryI[of "basepoint"])
    have "lambda \<ge> 1" "C \<ge> 0" using quasi_isometry_onD[OF assms(1)] by auto
    define D where "D = 165 * lambda^2 * (C + lambda + deltaG(TYPE('b))^2 + deltaG(TYPE('a)))"
    fix M::real
    define M2 where "M2 = lambda * M + D"
    have M2: "M = (M2 - D)/lambda" unfolding M2_def using \<open>lambda \<ge> 1\<close> by (auto simp add: algebra_simps divide_simps)
    obtain N where N: "\<And>m n. m \<ge> N \<Longrightarrow> n \<ge> N \<Longrightarrow> Gromov_product_at (f basepoint) (f (u m)) (f (u n)) \<ge> M2"
      using \<open>Gromov_converging_at_boundary (\<lambda>n. f (u n))\<close> unfolding Gromov_converging_at_boundary_def by blast
    have "Gromov_product_at basepoint (u m) (u n) \<ge> M" if "m \<ge> N" "n \<ge> N" for m n
    proof -
      have "M2 \<le> Gromov_product_at (f basepoint) (f (u m)) (f (u n))"
        using N[OF that] by auto
      also have "... \<le> lambda * Gromov_product_at basepoint (u m) (u n) + D"
        unfolding D_def by (rule Gromov_product_at_quasi_isometry[OF assms(1)])
      finally show "M \<le> Gromov_product_at basepoint (u m) (u n)"
        unfolding M2 using \<open>lambda \<ge> 1\<close> by (auto simp add: algebra_simps divide_simps)
    qed
    then show "\<exists>N. \<forall>n\<ge>N. \<forall>m\<ge>N. Gromov_product_at basepoint (u m) (u n) \<ge> M"
      by auto
  qed
qed

text \<open>We define the extension to the completion of a function $f: X \to Y$ where $X$ and $Y$
are geodesic Gromov-hyperbolic spaces, as a function from $X \cup \partial X$ to $Y\cup \partial Y$,
as follows. If $x$ is in the space, we just use $f(x)$ (with the suitable coercions for the
definition). Otherwise, we wish to define $f(x)$ as the limit of $f(u_n)$ for all sequences tending
to $x$. For the definition, we use one such sequence chosen arbitrarily (this is the role of
\verb+rep_Gromov_completion x+ below, it is indeed a sequence in the space tending to $x$), and
we use the limit of $f(u_n)$ (if it exists, otherwise the framework will choose some point for us
but it will make no sense whatsoever).

For quasi-isometries, we have indeed that $f(u_n)$ converges if $u_n$ converges to a boundary point,
by \verb+Gromov_converging_at_infinity_quasi_isometry+, so this definition is meaningful. Moreover,
continuity of the extension follows readily from this (modulo a suitable criterion for continuity
based on sequences convergence, established in \verb+continuous_at_extension_sequentially'+).\<close>

definition Gromov_extension::"('a::Gromov_hyperbolic_space_geodesic \<Rightarrow> 'b::Gromov_hyperbolic_space_geodesic) \<Rightarrow> ('a Gromov_completion \<Rightarrow> 'b Gromov_completion)"
  where "Gromov_extension f x = (if x \<in> Gromov_boundary then lim (to_Gromov_completion o f o (rep_Gromov_completion x))
                                 else to_Gromov_completion (f (from_Gromov_completion x)))"

lemma Gromov_extension_inside_space [simp]:
  "Gromov_extension f (to_Gromov_completion x) = to_Gromov_completion (f x)"
unfolding Gromov_extension_def by auto

lemma Gromov_extension_boundary_to_boundary:
  fixes f::"'a::Gromov_hyperbolic_space_geodesic \<Rightarrow> 'b::Gromov_hyperbolic_space_geodesic"
  assumes "lambda C-quasi_isometry f"
          "x \<in> Gromov_boundary"
  shows "(Gromov_extension f) x \<in> Gromov_boundary"
proof -
  have *: "Gromov_converging_at_boundary (\<lambda>n. f (rep_Gromov_completion x n))"
    by (simp add: Gromov_converging_at_infinity_quasi_isometry[OF assms(1)] Gromov_boundary_rep_converging assms(2))
  show ?thesis
    unfolding Gromov_extension_def using assms(2) unfolding comp_def apply auto
    by (metis Gromov_converging_at_boundary_converges * limI)
qed

proposition Gromov_extension_continuous:
  fixes f::"'a::Gromov_hyperbolic_space_geodesic \<Rightarrow> 'b::Gromov_hyperbolic_space_geodesic"
  assumes "lambda C-quasi_isometry f"
          "x \<in> Gromov_boundary"
  shows "continuous (at x) (Gromov_extension f)"
proof -
  have "continuous (at x within (range to_Gromov_completion \<union> Gromov_boundary)) (Gromov_extension f)"
  proof (rule continuous_at_extension_sequentially'[OF \<open>x \<in> Gromov_boundary\<close>])
    fix b::"'a Gromov_completion" assume "b \<in> Gromov_boundary"
    show "\<exists>u. (\<forall>n. u n \<in> range to_Gromov_completion) \<and> u \<longlonglongrightarrow> b \<and> (\<lambda>n. Gromov_extension f (u n)) \<longlonglongrightarrow> Gromov_extension f b"
      apply (rule exI[of _ "to_Gromov_completion o (rep_Gromov_completion b)"], auto simp add: comp_def)
      unfolding Gromov_completion_converge_to_boundary[OF \<open>b \<in> Gromov_boundary\<close>]
      using Quotient3_abs_rep[OF Quotient3_Gromov_completion] Quotient3_rep_reflp[OF Quotient3_Gromov_completion] apply auto[1]
      unfolding Gromov_extension_def using \<open>b \<in> Gromov_boundary\<close> unfolding comp_def
      by (auto simp add: convergent_LIMSEQ_iff[symmetric] Gromov_boundary_rep_converging Gromov_converging_at_infinity_quasi_isometry[OF assms(1)]
               intro!: Gromov_converging_at_boundary_converges')
  next
    fix u and b::"'a Gromov_completion"
    assume u: "\<forall>n. u n \<in> range to_Gromov_completion" "b \<in> Gromov_boundary" "u \<longlonglongrightarrow> b"
    define v where "v = (\<lambda>n. from_Gromov_completion (u n))"
    have v: "u n = to_Gromov_completion (v n)" for n
      using u(1) unfolding v_def by (simp add: f_inv_into_f from_Gromov_completion_def)

    show "convergent (\<lambda>n. Gromov_extension f (u n))"
      using u unfolding v
      apply (auto intro!: Gromov_converging_at_boundary_converges' simp add: Gromov_converging_at_infinity_quasi_isometry[OF assms(1)])
      using Gromov_boundary_abs_converging Gromov_completion_converge_to_boundary by blast
  qed
  then show ?thesis by (simp add: Gromov_boundary_def)
qed

text \<open>With a suitable homeomorphism criterion, one proves in the same way that the extension
of a quasi-isometry to the boundary is a homeomorphism on its image.\<close>

proposition Gromov_extension_homeo:
  fixes f::"'a::Gromov_hyperbolic_space_geodesic \<Rightarrow> 'b::Gromov_hyperbolic_space_geodesic"
  assumes "lambda C-quasi_isometry f"
  shows "homeomorphism_on Gromov_boundary (Gromov_extension f)"
proof (rule homeomorphism_on_extension_sequentially'[of "range to_Gromov_completion"])
  fix u and b::"'a Gromov_completion"
  assume u: "\<forall>n. u n \<in> range to_Gromov_completion" "b \<in> Gromov_boundary" "u \<longlonglongrightarrow> b"
  define v where "v = (\<lambda>n. from_Gromov_completion (u n))"
  have v: "u n = to_Gromov_completion (v n)" for n
    using u(1) unfolding v_def by (simp add: f_inv_into_f from_Gromov_completion_def)

  show "convergent (\<lambda>n. Gromov_extension f (u n))"
    using u unfolding v
    apply (auto intro!: Gromov_converging_at_boundary_converges' simp add: Gromov_converging_at_infinity_quasi_isometry[OF assms(1)])
    using lim_imp_Gromov_converging_at_boundary by auto
next
  fix u c
  assume u: "\<forall>n. u n \<in> range to_Gromov_completion" "c \<in> Gromov_extension f ` Gromov_boundary" "(\<lambda>n. Gromov_extension f (u n)) \<longlonglongrightarrow> c"
  then have "c \<in> Gromov_boundary" using Gromov_extension_boundary_to_boundary[OF assms(1)] by auto
  define v where "v = (\<lambda>n. from_Gromov_completion (u n))"
  have v: "u n = to_Gromov_completion (v n)" for n
    using u(1) unfolding v_def by (simp add: f_inv_into_f from_Gromov_completion_def)
  have "Gromov_converging_at_boundary (\<lambda>n. f (v n))"
    apply (rule lim_imp_Gromov_converging_at_boundary[OF _ \<open>c \<in> Gromov_boundary\<close>])
    using u(3) unfolding v by auto
  then show "convergent u"
    using u unfolding v
    by (auto intro!: Gromov_converging_at_boundary_converges' simp add: Gromov_converging_at_infinity_quasi_isometry[OF assms(1), symmetric])
next
  fix b::"'a Gromov_completion" assume "b \<in> Gromov_boundary"
  show "\<exists>u. (\<forall>n. u n \<in> range to_Gromov_completion) \<and> u \<longlonglongrightarrow> b \<and> (\<lambda>n. Gromov_extension f (u n)) \<longlonglongrightarrow> Gromov_extension f b"
    apply (rule exI[of _ "to_Gromov_completion o (rep_Gromov_completion b)"], auto simp add: comp_def)
    unfolding Gromov_completion_converge_to_boundary[OF \<open>b \<in> Gromov_boundary\<close>]
    using Quotient3_abs_rep[OF Quotient3_Gromov_completion] Quotient3_rep_reflp[OF Quotient3_Gromov_completion] apply auto[1]
    unfolding Gromov_extension_def using \<open>b \<in> Gromov_boundary\<close> unfolding comp_def
    by (auto simp add: convergent_LIMSEQ_iff[symmetric] Gromov_boundary_rep_converging Gromov_converging_at_infinity_quasi_isometry[OF assms(1)]
             intro!: Gromov_converging_at_boundary_converges')
qed

text \<open>When the quasi-isometric embedding is a quasi-isometric isomorphism, i.e., it is onto up
to a bounded distance $C$, then its Gromov extension is onto on the boundary. Indeed, a point
in the image boundary is a limit of a sequence inside the space. Perturbing by a bounded distance
(which does not change the asymptotic behavior), it is the limit of a sequence inside the image of
$f$. Then the preimage under $f$ of this sequence does converge, and its limit is sent by the
extension on the original point, proving the surjectivity.\<close>

lemma Gromov_extension_onto:
  fixes f::"'a::Gromov_hyperbolic_space_geodesic \<Rightarrow> 'b::Gromov_hyperbolic_space_geodesic"
  assumes "lambda C-quasi_isometry_between UNIV UNIV f"
          "y \<in> Gromov_boundary"
  shows "\<exists>x \<in> Gromov_boundary. Gromov_extension f x = y"
proof -
  define u where "u = rep_Gromov_completion y"
  have *: "(\<lambda>n. to_Gromov_completion (u n)) \<longlonglongrightarrow> y"
    unfolding u_def using rep_Gromov_completion_limit by fastforce
  have "\<exists>v. \<forall>n. dist (f (v n)) (u n) \<le> C"
    apply (intro choice) using quasi_isometry_betweenD(3)[OF assms(1)] by auto
  then obtain v where v: "\<And>n. dist (f (v n)) (u n) \<le> C" by auto
  have *: "(\<lambda>n. to_Gromov_completion (f (v n))) \<longlonglongrightarrow> y"
    apply (rule Gromov_converging_at_boundary_bounded_perturbation[OF * \<open>y \<in> Gromov_boundary\<close>])
    using v by (simp add: dist_commute)
  then have "Gromov_converging_at_boundary (\<lambda>n. f (v n))"
    using assms(2) lim_imp_Gromov_converging_at_boundary by force
  then have "Gromov_converging_at_boundary v"
    using Gromov_converging_at_infinity_quasi_isometry[OF quasi_isometry_betweenD(1)[OF assms(1)]] by auto
  then obtain x where "x \<in> Gromov_boundary" "(\<lambda>n. to_Gromov_completion (v n)) \<longlonglongrightarrow> x"
    using Gromov_converging_at_boundary_converges by blast
  then have "(\<lambda>n. (Gromov_extension f) (to_Gromov_completion (v n))) \<longlonglongrightarrow> Gromov_extension f x"
    using isCont_tendsto_compose[OF Gromov_extension_continuous[OF quasi_isometry_betweenD(1)[OF assms(1)] \<open>x \<in> Gromov_boundary\<close>]] by fastforce
  then have "y = Gromov_extension f x"
    using * LIMSEQ_unique by auto
  then show ?thesis using \<open>x \<in> Gromov_boundary\<close> by auto
qed

lemma Gromov_extension_onto':
  fixes f::"'a::Gromov_hyperbolic_space_geodesic \<Rightarrow> 'b::Gromov_hyperbolic_space_geodesic"
  assumes "lambda C-quasi_isometry_between UNIV UNIV f"
  shows "(Gromov_extension f)`Gromov_boundary = Gromov_boundary"
using Gromov_extension_onto[OF assms] Gromov_extension_boundary_to_boundary[OF quasi_isometry_betweenD(1)[OF assms]] by auto

text \<open>Finally, we obtain that a quasi-isometry between two Gromov hyperbolic spaces induces a
homeomorphism of their boundaries.\<close>

theorem Gromov_boundaries_homeomorphic:
  fixes f::"'a::Gromov_hyperbolic_space_geodesic \<Rightarrow> 'b::Gromov_hyperbolic_space_geodesic"
  assumes "lambda C-quasi_isometry_between UNIV UNIV f"
  shows "(Gromov_boundary::'a Gromov_completion set) homeomorphic (Gromov_boundary::'b Gromov_completion set)"
using Gromov_extension_homeo[OF quasi_isometry_betweenD(1)[OF assms]] Gromov_extension_onto'[OF assms]
unfolding homeomorphic_def homeomorphism_on_def by auto

end (*of theory Gromov_Boundary*)
