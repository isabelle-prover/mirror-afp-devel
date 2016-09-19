(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)

theory Kingman
imports Ergodicity Fekete
begin

lemma
  fixes f g::"nat \<Rightarrow> real"
  assumes "f \<longlonglongrightarrow> l" "\<And>n. g n = f n"
  shows "g \<longlonglongrightarrow> l"
using assms(1) assms(2) by presburger


lemma e2ennreal_Liminf:
  "F \<noteq> bot \<Longrightarrow> e2ennreal (Liminf F f) = Liminf F (\<lambda>n. e2ennreal (f n))"
  by (rule Liminf_compose_continuous_mono[symmetric])
     (auto simp: mono_def e2ennreal_mono continuous_on_e2ennreal)

lemma e2ennreal_ereal: "e2ennreal (ereal x) = ennreal x"
  unfolding ennreal.abs_eq by (cases "0 \<le> x") (auto simp add: e2ennreal_neg max.absorb2)

lemma e2ennreal_eq_infty[simp]: "0 \<le> x \<Longrightarrow> e2ennreal x = top \<longleftrightarrow> x = \<infinity>"
  by (cases x) (auto simp: e2ennreal_infty e2ennreal_ereal)

section {*Subcocycles, subadditive ergodic theory*}

text {*Subadditive ergodic theory is the branch of ergodic theory devoted
to the study of subadditive cocycles (named subcocycles in what follows), i.e.,
functions such that $u(n+m, x) \leq u(n, x) + u(m, T^n x)$ for all $x$ and $m,n$.

For instance, birkhoff sums are examples of such subadditive cocycles (in fact, they are
additive), but more interesting examples are genuinely subadditive. The main result
of the theory is Kingman's theorem, asserting the almost sure convergence of
$u_n / n$ (this is a generalization of Birkhoff theorem). If the asymptotic average
$\lim \int u_n / n$ (which exists by subadditivity and Fekete lemma) is not $-\infty$,
then the convergence takes also place in $L^1$. We prove all this below.
*}

context mpt
begin

subsection {*Definition and basic properties*}

definition subcocycle::"(nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool"
  where "subcocycle u = ((\<forall>n. integrable M (u n)) \<and> (\<forall>n m x. u (n+m) x \<le> u n x + u m ((T^^n) x)))"

lemma subcocycle_ineq:
  assumes "subcocycle u"
  shows "u (n+m) x \<le> u n x + u m ((T^^n) x)"
using assms unfolding subcocycle_def by blast

lemma subcocycle_0_nonneg:
  assumes "subcocycle u"
  shows "u 0 x \<ge> 0"
proof -
  have "u (0+0) x \<le> u 0 x + u 0 ((T^^0) x)"
    using assms unfolding subcocycle_def by blast
  then show ?thesis by auto
qed

lemma subcocycle_integrable:
  assumes "subcocycle u"
  shows "integrable M (u n)"
        "u n \<in> borel_measurable M"
using assms unfolding subcocycle_def by auto

lemma subcocycle_birkhoff:
  assumes "integrable M f"
  shows "subcocycle (birkhoff_sum f)"
unfolding subcocycle_def by (auto simp add: assms birkhoff_sum_integral(1) birkhoff_sum_cocycle)

lemma subcocycle_add:
  assumes "subcocycle u" "subcocycle v"
  shows "subcocycle (\<lambda>n x. u n x + v n x)"
unfolding subcocycle_def
proof (auto)
  fix n
  show "integrable M (\<lambda>x. u n x + v n x)" using assms unfolding subcocycle_def by simp
next
  fix n m x
  have "u (n+m) x \<le> u n x + u m ((T ^^ n) x)" using assms(1) subcocycle_def by simp
  moreover have "v (n+m) x \<le> v n x + v m ((T ^^ n) x)" using assms(2) subcocycle_def by simp
  ultimately show "u (n + m) x + v (n + m) x \<le> u n x + v n x + (u m ((T ^^ n) x) + v m ((T ^^ n) x))"
    by simp
qed

lemma subcocycle_cmult:
  assumes "subcocycle u" "c \<ge> 0"
  shows "subcocycle (\<lambda>n x. c * u n x)"
using assms unfolding subcocycle_def by (auto, metis distrib_left mult_left_mono)

lemma subcocycle_max:
  assumes "subcocycle u" "subcocycle v"
  shows "subcocycle (\<lambda>n x. max (u n x) (v n x))"
unfolding subcocycle_def proof (auto)
  fix n
  show "integrable M (\<lambda>x. max (u n x) (v n x))" using assms unfolding subcocycle_def by auto
next
  fix n m x
  have "u (n+m) x \<le> u n x + u m ((T^^n) x)" using assms(1) unfolding subcocycle_def by auto
  then show "u (n + m) x \<le> max (u n x) (v n x) + max (u m ((T ^^ n) x)) (v m ((T ^^ n) x))"
    by simp
next
  fix n m x
  have "v (n+m) x \<le> v n x + v m ((T^^n) x)" using assms(2) unfolding subcocycle_def by auto
  then show "v (n + m) x \<le> max (u n x) (v n x) + max (u m ((T ^^ n) x)) (v m ((T ^^ n) x))"
    by simp
qed

lemma subcocycle_bounded_by_birkhoff1:
  assumes "subcocycle u" "n > 0"
  shows "u n x \<le> birkhoff_sum (u 1) n x"
proof (induction rule: ind_from_1[OF assms(2)])
  case 1
  show ?case by auto
next
  case (2 p)
  have "u (Suc p) x \<le> u p x + u 1 ((T^^p)x)" using assms(1) subcocycle_def by (metis Suc_eq_plus1)
  then show ?case using 2 birkhoff_sum_cocycle[where ?n=p and ?m=1] \<open> p>0 \<close> by (simp add: birkhoff_sum_def)
qed

text {*It is often important to bound a cocycle $u_n(x)$ by the Birkhoff sums of $u_N/N$. Compared
to the trivial upper bound for $u_1$, there are additional boundary errors that make the
estimate more cumbersome (but these terms only come from a $N$-neighborhood of $0$ and $n$, so
they are negligible if $N$ is fixed and $n$ tends to infinity.*}

lemma subcocycle_bounded_by_birkhoffN:
  assumes "subcocycle u" "n > 2*N" "N>0"
  shows "u n x \<le> birkhoff_sum (\<lambda>x. u N x / real N) (n - 2 * N) x
                + (\<Sum>i<N. \<bar>u 1 ((T ^^ i) x)\<bar>)
                + 2 * (\<Sum>i<2*N. \<bar>u 1 ((T ^^ (n - (2 * N - i))) x)\<bar>)"
proof -
  have Iar: "u (a*N+r) x \<le> u r x + (\<Sum>i<a. u N ((T^^(i * N + r))x))" for r a
  proof (induction a)
    case 0
    then show ?case by auto
  next
    case (Suc a)
    have "u ((a+1)*N+r) x = u((a*N+r) + N) x"
      by (simp add: semiring_normalization_rules(2) semiring_normalization_rules(23))
    also have "... \<le> u(a*N+r) x + u N ((T^^(a*N+r))x)"
      using assms(1) unfolding subcocycle_def by auto
    also have "... \<le> u r x + (\<Sum>i<a. u N ((T^^(i * N + r))x)) + u N ((T^^(a*N+r))x)"
      using Suc.IH by auto
    also have "... = u r x + (\<Sum>i<a+1. u N ((T^^(i * N + r))x))"
      by auto
    finally show ?case by auto
  qed

  have Ia: "u (a*N) x \<le> (\<Sum>i<a. u N ((T^^(i * N))x))" if "a>0" for a
  proof (induction rule: ind_from_1[OF that])
    case 1
    show ?case by auto
  next
    case (2 a)
    have "u ((a+1)*N) x = u((a*N) + N) x"
      by (simp add: semiring_normalization_rules(2) semiring_normalization_rules(23))
    also have "... \<le> u(a*N) x + u N ((T^^(a*N))x)"
      using assms(1) unfolding subcocycle_def by auto
    also have "... \<le> (\<Sum>i<a. u N ((T^^(i * N))x)) + u N ((T^^(a*N))x)"
      using 2 by auto
    also have "... = (\<Sum>i<a+1. u N ((T^^(i * N))x))"
      by auto
    finally show ?case by auto
  qed

  define E1 where "E1 = (\<Sum>i<N. abs(u 1 ((T^^i)x)))"
  define E2 where "E2 = (\<Sum>i<2*N. abs(u 1 ((T^^(n-(2*N-i))) x)))"
  have "E2 \<ge> 0" unfolding E2_def by auto


  obtain a0 s0 where 0: "s0 < N" "n = a0 * N + s0"
    by (metis `0 < N` add.commute mod_eqD mod_less_divisor)
  then have "a0 \<ge> 1" using `n > 2 * N` `N>0`
    by (metis Nat.add_0_right add.commute add_lessD1 add_mult_distrib comm_monoid_mult_class.mult_1 eq_imp_le
    less_imp_add_positive less_imp_le_nat less_one linorder_neqE_nat mult.left_neutral mult_not_zero not_add_less1 one_add_one)
  define a s where "a = a0-1" and "s = s0+N"
  then have as: "n = a * N + s" unfolding a_def s_def using `a0 \<ge> 1` 0 by (simp add: mult_eq_if)
  have s: "s \<ge> N" "s < 2*N" using 0 unfolding s_def by auto
  have a: "a*N > n - 2*N" "a*N \<le> n - N" using as s `n > 2*N` by auto
  then have "(a*N - (n-2*N)) \<le> N" using `n > 2*N` by auto
  have "a*N \<ge> n - 2*N" using a by simp

  {
    fix r::nat assume "r < N"
    have "a*N+r > n - 2*N" using `n>2*N` as s by auto

    define tr where "tr = n-(a*N+r)"
    have "tr > 0" unfolding tr_def using as s `r<N` by auto
    then have *: "n = (a*N+r) + tr" unfolding tr_def by auto

    have "birkhoff_sum (u 1) tr ((T^^(a*N+r))x) = (\<Sum>i<tr. u 1 ((T^^(a*N+r+i))x))"
      unfolding birkhoff_sum_def by (simp add: add.commute funpow_add)
    also have "... = (\<Sum>i\<in>{a*N+r..<a*N+r+tr}. u 1 ((T^^i) x))"
      by (rule setsum.reindex_bij_betw, rule bij_betw_byWitness[where ?f'= "\<lambda>i. i - (a * N + r)"], auto)
    also have "... \<le> (\<Sum>i\<in>{a*N+r..<a*N+r+tr}. abs(u 1 ((T^^i) x)))"
      by (simp add: setsum_mono)
    also have "... \<le> (\<Sum>i\<in>{n-2*N..<n}. abs(u 1 ((T^^i) x)))"
      apply (rule setsum_mono2) using as s `r<N` tr_def by auto
    also have "... = E2" unfolding E2_def
      apply (rule setsum.reindex_bij_betw[symmetric], rule bij_betw_byWitness[where ?f'= "\<lambda>i. i - (n-2*N)"])
      using `n > 2*N` by auto
    finally have A: "birkhoff_sum (u 1) tr ((T^^(a*N+r))x) \<le> E2" by simp

    have "u n x \<le> u (a*N+r) x + u tr ((T^^(a*N+r))x)"
      using assms(1) * unfolding subcocycle_def by auto
    also have "... \<le> u (a*N+r) x + birkhoff_sum (u 1) tr ((T^^(a*N+r))x)"
      using subcocycle_bounded_by_birkhoff1[OF assms(1)] `tr > 0` by auto
    finally have B: "u n x \<le> u (a*N+r) x + E2"
      using A by auto

    have "u (a*N+r) x \<le> (\<Sum>i<N. abs(u 1 ((T^^i)x))) + (\<Sum>i<a. u N ((T^^(i*N+r))x))"
    proof (cases "r=0")
      case True
      then have "a>0" using `a*N+r > n - 2*N` not_less by fastforce
      have "u(a*N+r) x \<le> (\<Sum>i<a. u N ((T^^(i*N+r))x))" using Ia[OF `a>0`] True by auto
      moreover have "0 \<le> (\<Sum>i<N. abs(u 1 ((T^^i)x)))" by auto
      ultimately show ?thesis by linarith
    next
      case False
      then have I: "u (a*N+r) x \<le> u r x + (\<Sum>i<a. u N ((T^^(i * N + r))x))" using Iar by auto
      have "u r x \<le> (\<Sum>i<r. u 1 ((T^^i)x))"
        using subcocycle_bounded_by_birkhoff1[OF assms(1)] False unfolding birkhoff_sum_def by auto
      also have "... \<le> (\<Sum>i<r. abs(u 1 ((T^^i)x)))"
        by (simp add: setsum_mono)
      also have "... \<le> (\<Sum>i<N. abs(u 1 ((T^^i)x)))"
        apply (rule setsum_mono2) using `r<N` by auto
      finally show ?thesis using I by auto
    qed
    then have "u n x \<le> E1 + (\<Sum>i<a. u N ((T^^(i*N+r))x)) + E2"
      unfolding E1_def using B by auto
  } note * = this


  have I: "u N ((T^^j) x) \<le> E2" if "j\<in>{n-2*N..<a*N}" for j
  proof -
    have "u N ((T^^j) x) \<le> (\<Sum>i<N. u 1 ((T^^i) ((T^^j)x)))"
      using subcocycle_bounded_by_birkhoff1[OF assms(1) `N>0`] unfolding birkhoff_sum_def by auto
    also have "... = (\<Sum>i<N. u 1 ((T^^(i+j))x))" by (simp add: funpow_add)
    also have "... \<le> (\<Sum>i<N. abs(u 1 ((T^^(i+j))x)))" by (rule setsum_mono, auto)
    also have "... = (\<Sum>k\<in>{j..<N+j}. abs(u 1 ((T^^k)x)))"
      by (rule setsum.reindex_bij_betw, rule bij_betw_byWitness[where ?f'= "\<lambda>k. k-j"], auto)
    also have "... \<le> (\<Sum>i\<in>{n-2*N..<n}. abs(u 1 ((T^^i) x)))"
      apply (rule setsum_mono2) using `j\<in>{n-2*N..<a*N}` `a*N \<le> n - N` by auto
    also have "... = E2" unfolding E2_def
      apply (rule setsum.reindex_bij_betw[symmetric], rule bij_betw_byWitness[where ?f'= "\<lambda>i. i - (n-2*N)"])
      using `n > 2*N` by auto
    finally show ?thesis by auto
  qed
  have "(\<Sum>j<a*N. u N ((T^^j) x)) - (\<Sum>j<n-2*N. u N ((T^^j) x)) = (\<Sum>j\<in>{n-2*N..<a*N}. u N ((T^^j) x))"
    using setsum_add_nat_ivl[OF _ `a*N \<ge> n - 2*N`, of 0 "\<lambda>j. u N ((T^^j) x)", symmetric] atLeast0LessThan by simp
  also have "... \<le> (\<Sum>j\<in>{n-2*N..<a*N}. E2)" by (rule setsum_mono[OF I])
  also have "... = (a*N - (n-2*N)) * E2" by simp
  also have "... \<le> N * E2" using `(a*N - (n-2*N)) \<le> N` `E2 \<ge> 0` by (simp add: mult_right_mono)
  finally have J: "(\<Sum>j<a*N. u N ((T^^j) x)) \<le> (\<Sum>j<n-2*N. u N ((T^^j) x)) + N * E2" by auto

  have "N * u n x = (\<Sum>r<N. u n x)" by auto
  also have "... \<le> (\<Sum>r<N. E1 + E2 + (\<Sum>i<a. u N ((T^^(i*N+r))x)))"
    apply (rule setsum_mono) using * by fastforce
  also have "... = (\<Sum>r<N. E1 + E2) + (\<Sum>r<N. (\<Sum>i<a. u N ((T^^(i*N+r))x)))"
    by (rule setsum.distrib)
  also have "... = N* (E1 + E2) + (\<Sum>j<a*N. u N ((T^^j) x))"
    using setsum_arith_progression by auto
  also have "... \<le> N *(E1+E2) + (\<Sum>j<n-2*N. u N ((T^^j) x)) + N*E2"
    using J by auto
  also have "... = N * (E1+E2) + N * (\<Sum>j<n-2*N. u N ((T^^j) x) / N) + N * E2"
    using `N>0` by (simp add: setsum_distrib_left)
  also have "... = N*(E1 + E2 + (\<Sum>j<n-2*N. u N ((T^^j) x) / N) + E2)"
    by (simp add: distrib_left)
  finally have "u n x \<le> E1 + 2*E2 + birkhoff_sum (\<lambda>x. u N x / N) (n-2*N) x"
    unfolding birkhoff_sum_def using `N>0` by auto
  then show ?thesis unfolding E1_def E2_def by auto
qed

text {*Many natural cocycles are only defined almost everywhere, and then the
subadditivity property only makes sense almost everywhere. We wish now to show
that such an a.e.-subcocycle coincides almost everywhere with a genuine subcocycle
in the above sense. Then, all the results for subcocycles will apply to such
a.e.-subcocycles.*

The subcocycle will be defined in a recursive way. This means that is can not be defined in a
proof (since complicated function definitions are not available inside proofs). Since it is
defined in terms of $u$, then $u$ has to be available at the top level, which is most
conveniently done using a context.
*}
context
  fixes u::"nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes H: "\<And>m n. AE x in M. u (n+m) x \<le> u n x + u m ((T^^n) x)"
          "\<And>n. integrable M (u n)"
begin

private fun v :: "nat \<Rightarrow> 'a \<Rightarrow> real" where "v n x = (
  if n = 0 then max (u 0 x) 0
  else if n = 1 then u 1 x
  else min (u n x) (Min ((\<lambda>k. v k x + v (n-k) ((T^^k) x))`{0<..<n})))"

private lemma integrable_v:
  "integrable M (v n)" for n
proof (induction n rule: nat_less_induct)
  case (1 n)
  consider "n=0" | "n=1" | "n>1" by linarith
  then show ?case
  proof (cases)
    assume "n = 0"
    have "v 0 x = max (u 0 x) 0" for x by simp
    then show ?thesis using integrable_max[OF H(2)[of 0]] `n=0` by auto
  next
    assume "n = 1"
    have "v 1 x = u 1 x" for x by simp
    then show ?thesis using H(2)[of 1] `n=1` by auto
  next
    assume "n > 1"
    {
      fix x
      have *: "(\<lambda>k. v k x + v (n-k) ((T^^k) x))`{0<..<n} = {v k x + v (n-k) ((T^^k) x) |k. k \<in> {0<..<n}}"
        by blast
      have "v n x = min (u n x) (Min ((\<lambda>k. v k x + v (n-k) ((T^^k) x))`{0<..<n}))"
        using `1<n` by auto
      then have "v n x = min (u n x) (Min { v k x + v (n-k) ((T^^k) x) |k. k \<in> {0<..<n}})"
        using * by auto
    }
    moreover have "integrable M (\<lambda>x. min (u n x) (Min { v k x + v (n-k) ((T^^k) x) |k. k \<in> {0<..<n}}))"
      apply (rule integrable_min)
      apply (simp add: H(2))
      apply (rule integrable_Min, simp)
      using `n >1` apply auto[1]
      apply (rule Bochner_Integration.integrable_add)
      using "1.IH" apply auto[1]
      apply (rule Tn_integral_preserving(1))
      using "1.IH" by (metis \<open>1 < n\<close> diff_less greaterThanLessThan_iff max_0_1(2) max_less_iff_conj)
    ultimately show ?case by auto
  qed
qed

private lemma u_eq_v_AE:
  "AE x in M. v n x = u n x" for n
proof (induction n rule: nat_less_induct)
  case (1 n)
  consider "n=0" | "n=1" | "n>1" by linarith
  then show ?case
  proof (cases)
    assume "n = 0"
    have "AE x in M. u 0 x \<le> u 0 x + u 0 x" using H(1)[of 0 0] by auto
    then have "AE x in M. u 0 x \<ge> 0" by auto
    moreover have "v 0 x = max (u 0 x) 0" for x by simp
    ultimately show ?thesis using `n=0` by auto
  next
    assume "n = 1"
    have "v 1 x = u 1 x" for x by simp
    then show ?thesis using `n=1` by simp
  next
    assume "n > 1"
    {
      fix k assume "k<n"
      then have "AE x in M. v k x = u k x" using "1.IH" by simp
      with T_AE_iterates[OF this] have "AE x in M. \<forall>s. v k ((T^^s) x) = u k ((T^^s) x)" by simp
    } note * = this
    have "AE x in M. \<forall>k \<in> {..<n}. \<forall>s. v k ((T^^s) x) = u k ((T^^s) x)"
      apply (rule AE_finite_allI) using * by simp_all
    moreover have "AE x in M. \<forall>i j. u (i+j) x \<le> u i x + u j ((T^^i) x)"
      apply (subst AE_all_countable, intro allI)+ using H(1) by simp
    moreover
    {
      fix x assume "\<forall>k \<in> {..<n}. \<forall>s. v k ((T^^s) x) = u k ((T^^s) x)"
                   "\<forall>i j. u (i+j) x \<le> u i x + u j ((T^^i) x)"
      then have Hx: "\<And>k s. k < n \<Longrightarrow> v k ((T^^s) x) = u k ((T^^s) x)"
                    "\<And>i j. u (i+j) x \<le> u i x + u j ((T^^i) x)"
        by auto
      {
        fix k assume "k \<in> {0<..<n}"
        then have K: "k<n" "n-k<n" by auto
        have "u n x \<le> u k x + u (n-k) ((T^^k) x)" using Hx(2) K by (metis le_add_diff_inverse less_imp_le_nat)
        also have "... = v k x + v (n-k) ((T^^k)x)" using Hx(1)[OF `k <n`, of 0] Hx(1)[OF `n-k <n`, of k] by auto
        finally have "u n x \<le> v k x + v (n-k) ((T^^k)x)" by simp
      }
      then have *: "\<And>z. z \<in> (\<lambda>k. v k x + v (n-k) ((T^^k) x))`{0<..<n} \<Longrightarrow> u n x \<le> z" by blast
      have "u n x \<le> Min ((\<lambda>k. v k x + v (n-k) ((T^^k) x))`{0<..<n})"
        apply (rule Min.boundedI) using `n>1` * by auto
      moreover have "v n x = min (u n x) (Min ((\<lambda>k. v k x + v (n-k) ((T^^k) x))`{0<..<n}))"
        using `1<n` by auto
      ultimately have "v n x = u n x" by auto
    }
    ultimately show ?thesis by auto
  qed
qed

private lemma subcocycle_v:
  "v (n+m) x \<le> v n x + v m ((T^^n) x)"
proof -
  consider "n=0" | "m=0" | "n>0 \<and> m >0" by auto
  then show ?thesis
  proof (cases)
    case 1
    then have "v n x \<ge> 0" by simp
    then show ?thesis using `n=0` by auto
  next
    case 2
    then have "v m x \<ge> 0" by simp
    then show ?thesis using `m=0` by auto
  next
    case 3
    then have "n+m > 1" by simp
    then have "v (n+m) x = min (u(n+m) x) (Min ((\<lambda>k. v k x + v ((n+m)-k) ((T^^k) x))`{0<..<n+m}))" by simp
    also have "... \<le> Min ((\<lambda>k. v k x + v ((n+m)-k) ((T^^k) x))`{0<..<n+m})" by simp
    also have "... \<le> v n x + v ((n+m)-n) ((T^^n) x)"
      apply (rule Min_le, simp)
      by (metis (lifting) \<open>0 < n \<and> 0 < m\<close> add.commute greaterThanLessThan_iff image_iff less_add_same_cancel2)
    finally show ?thesis by simp
  qed
qed

lemma subcocycle_AE_in_context:
  "\<exists>w. subcocycle w \<and> (AE x in M. \<forall>n. w n x = u n x)"
proof -
  have "subcocycle v" using subcocycle_v integrable_v unfolding subcocycle_def by auto
  moreover have "AE x in M. \<forall>n. v n x = u n x"
    by (subst AE_all_countable, intro allI, rule u_eq_v_AE)
  ultimately show ?thesis by blast
qed

end

lemma subcocycle_AE:
  fixes u::"nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes "\<And>m n. AE x in M. u (n+m) x \<le> u n x + u m ((T^^n) x)"
          "\<And>n. integrable M (u n)"
  shows "\<exists>w. subcocycle w \<and> (AE x in M. \<forall>n. w n x = u n x)"
using subcocycle_AE_in_context assms by blast


subsection {*The asymptotic average*}

text {*In this subsection, we define the asymptotic average of a subcocycle $u$, i.e., the
limit of $\int u_n(x)/n$ (the convergence follows from subadditivity) and study its basic
properties, especially in terms of operations on subcocycles.*}

definition subcocycle_avg_ereal::"(nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> ereal" where
  "subcocycle_avg_ereal u = Inf {ereal((\<integral>x. u n x \<partial>M) / n) |n. n > 0}"

lemma subcocycle_avg_finite:
  "subcocycle_avg_ereal u < \<infinity>"
unfolding subcocycle_avg_ereal_def using Inf_less_iff less_ereal.simps(4) by blast

lemma subcocycle_avg_subadditive:
  assumes "subcocycle u"
  shows "subadditive (\<lambda>n. (\<integral>x. u n x \<partial>M))"
unfolding subadditive_def proof (intro allI)
  have int_u [measurable]: "\<And>n. integrable M (u n)" using assms unfolding subcocycle_def by auto
  fix m n
  have "(\<integral>x. u (n+m) x \<partial>M) \<le> (\<integral>x. u n x + u m ((T^^n) x) \<partial>M)"
    apply (rule integral_mono)
    using int_u apply (auto simp add: Tn_integral_preserving(1))
    using assms unfolding subcocycle_def by auto
  also have "... \<le> (\<integral>x. u n x \<partial>M) + (\<integral>x. u m ((T^^n) x) \<partial>M)"
    using int_u by (auto simp add: Tn_integral_preserving(1))
  also have "... = (\<integral>x. u n x \<partial>M) + (\<integral>x. u m x \<partial>M)"
    using int_u by (auto simp add: Tn_integral_preserving(2))
  finally show "(\<integral>x. u (n+m) x \<partial>M) \<le> (\<integral>x. u n x \<partial>M) + (\<integral>x. u m x \<partial>M)" by simp
qed

lemma subcocycle_int_tendsto_avg_ereal:
  assumes "subcocycle u"
  shows "(\<lambda>n. (\<integral>x. u n x / n \<partial>M)) \<longlonglongrightarrow> subcocycle_avg_ereal u"
unfolding subcocycle_avg_ereal_def
using subadditive_converges_ereal[OF subcocycle_avg_subadditive[OF assms]] by auto

lemma subcocycle_avg_ereal_add:
  assumes "subcocycle u" "subcocycle v"
  shows "subcocycle_avg_ereal (\<lambda>n x. u n x + v n x) = subcocycle_avg_ereal u + subcocycle_avg_ereal v"
proof -
  have int [simp]: "\<And>n. integrable M (u n)" "\<And>n. integrable M (v n)" using assms unfolding subcocycle_def by auto
  {
    fix n
    have "(\<integral>x. u n x / n \<partial>M) + (\<integral>x. v n x / n \<partial>M) = (\<integral>x. u n x / n + v n x / n \<partial>M)"
      by (rule Bochner_Integration.integral_add[symmetric], auto)
    also have "... = (\<integral>x. (u n x + v n x) / n \<partial>M)"
      by (rule Bochner_Integration.integral_cong, auto simp add: add_divide_distrib)
    finally have "ereal (\<integral>x. u n x / n \<partial>M) + (\<integral>x. v n x / n \<partial>M) = (\<integral>x. (u n x + v n x) / n \<partial>M)"
      by auto
  }
  moreover have "(\<lambda>n. ereal (\<integral>x. u n x / n \<partial>M) + (\<integral>x. v n x / n \<partial>M))
                  \<longlonglongrightarrow> subcocycle_avg_ereal u + subcocycle_avg_ereal v"
    apply (rule tendsto_add_ereal_general[OF _ subcocycle_int_tendsto_avg_ereal[OF assms(1)]
          subcocycle_int_tendsto_avg_ereal[OF assms(2)]])
    using subcocycle_avg_finite by auto
  ultimately have "(\<lambda>n. (\<integral>x. (u n x + v n x) / n \<partial>M)) \<longlonglongrightarrow> subcocycle_avg_ereal u + subcocycle_avg_ereal v"
    by auto
  moreover have "(\<lambda>n. (\<integral>x. (u n x + v n x) / n \<partial>M)) \<longlonglongrightarrow> subcocycle_avg_ereal (\<lambda>n x. u n x + v n x)"
    by (rule subcocycle_int_tendsto_avg_ereal[OF subcocycle_add[OF assms]])
  ultimately show ?thesis using LIMSEQ_unique by blast
qed

lemma subcocycle_avg_ereal_cmult:
  assumes "subcocycle u" "c \<ge> (0::real)"
  shows "subcocycle_avg_ereal (\<lambda>n x. c * u n x) = c * subcocycle_avg_ereal u"
proof (cases "c=0")
  case True
  have *: "ereal (\<integral>x. (c * u n x) / n \<partial>M) = 0" if "n>0" for n
    by (subst True, auto)
  have "(\<lambda>n. ereal (\<integral>x. (c * u n x) / n \<partial>M)) \<longlonglongrightarrow> 0"
    by (subst tendsto_explicit, metis * less_le_trans zero_less_one)
  moreover have "(\<lambda>n. ereal (\<integral>x. (c * u n x) / n \<partial>M)) \<longlonglongrightarrow> subcocycle_avg_ereal (\<lambda>n x. c * u n x)"
    using subcocycle_int_tendsto_avg_ereal[OF subcocycle_cmult[OF assms]] by auto
  ultimately have "subcocycle_avg_ereal (\<lambda>n x. c * u n x) = 0"
    using LIMSEQ_unique by blast
  then show ?thesis using True by auto
next
  case False
  have int: "\<And>n. integrable M (u n)" using assms unfolding subcocycle_def by auto
  have "ereal (\<integral>x. c * u n x / n \<partial>M) = c * ereal (\<integral>x. u n x / n \<partial>M)" for n by auto
  then have "(\<lambda>n. c * ereal (\<integral>x. u n x / n \<partial>M)) \<longlonglongrightarrow> subcocycle_avg_ereal (\<lambda>n x. c * u n x)"
    using subcocycle_int_tendsto_avg_ereal[OF subcocycle_cmult[OF assms]] by auto
  moreover have "(\<lambda>n. c * ereal (\<integral>x. u n x / n \<partial>M)) \<longlonglongrightarrow> c * subcocycle_avg_ereal u"
    apply (rule tendsto_mult_ereal) using False subcocycle_int_tendsto_avg_ereal[OF assms(1)] by auto
  ultimately show ?thesis using LIMSEQ_unique by blast
qed

lemma subcocycle_avg_ereal_max:
  assumes "subcocycle u" "subcocycle v"
  shows "subcocycle_avg_ereal (\<lambda>n x. max (u n x) (v n x)) \<ge> max (subcocycle_avg_ereal u) (subcocycle_avg_ereal v)"
proof (auto)
  have int: "integrable M (u n)" "integrable M (v n)" for n using assms unfolding subcocycle_def by auto
  have int2: "integrable M (\<lambda>x. max (u n x) (v n x))" for n using integrable_max int by auto

  have "(\<integral>x. u n x / n \<partial>M) \<le> (\<integral>x. max (u n x) (v n x) / n \<partial>M)" for n
    apply (rule integral_mono) using int int2 by (auto simp add: divide_simps)
  then show "subcocycle_avg_ereal u \<le> subcocycle_avg_ereal (\<lambda>n x. max (u n x) (v n x))"
    using LIMSEQ_le[OF subcocycle_int_tendsto_avg_ereal[OF assms(1)]
          subcocycle_int_tendsto_avg_ereal[OF subcocycle_max[OF assms]]] by auto

  have "(\<integral>x. v n x / n \<partial>M) \<le> (\<integral>x. max (u n x) (v n x) / n \<partial>M)" for n
    apply (rule integral_mono) using int int2 by (auto simp add: divide_simps)
  then show "subcocycle_avg_ereal v \<le> subcocycle_avg_ereal (\<lambda>n x. max (u n x) (v n x))"
    using LIMSEQ_le[OF subcocycle_int_tendsto_avg_ereal[OF assms(2)]
          subcocycle_int_tendsto_avg_ereal[OF subcocycle_max[OF assms]]] by auto
qed

lemma subcocycle_avg_ereal_birkhoff:
  assumes "integrable M u"
  shows "subcocycle_avg_ereal (birkhoff_sum u) = (\<integral>x. u x \<partial>M)"
proof -
  have *: "ereal (\<integral>x. (birkhoff_sum u n x) / n \<partial>M) = (\<integral>x. u x \<partial>M)" if "n>0" for n
    using birkhoff_sum_integral(2)[OF assms] that by auto
  have "(\<lambda>n. ereal (\<integral>x. (birkhoff_sum u n x) / n \<partial>M)) \<longlonglongrightarrow> (\<integral>x. u x \<partial>M)"
    by (subst tendsto_explicit, metis * less_le_trans zero_less_one)
  moreover have "(\<lambda>n. ereal (\<integral>x. (birkhoff_sum u n x) / n \<partial>M)) \<longlonglongrightarrow> subcocycle_avg_ereal (birkhoff_sum u)"
    using subcocycle_int_tendsto_avg_ereal[OF subcocycle_birkhoff[OF assms]] by auto
  ultimately show ?thesis using LIMSEQ_unique by blast
qed

text {*In nice situations, where one can avoid the use of ereal, the following
definition is more convenient*}

definition subcocycle_avg::"(nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> real" where
  "subcocycle_avg u = real_of_ereal(subcocycle_avg_ereal u)"

lemma subcocycle_avg_real_ereal:
  assumes "subcocycle_avg_ereal u > - \<infinity>"
  shows "subcocycle_avg_ereal u = ereal(subcocycle_avg u)"
unfolding subcocycle_avg_def using assms subcocycle_avg_finite[of u] ereal_real by auto

lemma subcocycle_int_tendsto_avg:
  assumes "subcocycle u" "subcocycle_avg_ereal u > - \<infinity>"
  shows "(\<lambda>n. (\<integral>x. u n x / n \<partial>M)) \<longlonglongrightarrow> subcocycle_avg u"
using subcocycle_avg_real_ereal[OF assms(2)] subcocycle_int_tendsto_avg_ereal[OF assms(1)] by auto

lemma subcocycle_avg_add:
  assumes "subcocycle u" "subcocycle v" "subcocycle_avg_ereal u > - \<infinity>" "subcocycle_avg_ereal v > - \<infinity>"
  shows "subcocycle_avg_ereal (\<lambda>n x. u n x + v n x) > -\<infinity>"
        "subcocycle_avg (\<lambda>n x. u n x + v n x) = subcocycle_avg u + subcocycle_avg v"
using assms subcocycle_avg_finite real_of_ereal_add
unfolding subcocycle_avg_def subcocycle_avg_ereal_add[OF assms(1) assms(2)] by auto

lemma subcocycle_avg_cmult:
  assumes "subcocycle u" "c \<ge> (0::real)" "subcocycle_avg_ereal u > - \<infinity>"
  shows "subcocycle_avg_ereal (\<lambda>n x. c * u n x) > - \<infinity>"
        "subcocycle_avg (\<lambda>n x. c * u n x) = c * subcocycle_avg u"
using assms subcocycle_avg_finite unfolding subcocycle_avg_def subcocycle_avg_ereal_cmult[OF assms(1) assms(2)] by auto

lemma subcocycle_avg_max:
  assumes "subcocycle u" "subcocycle v" "subcocycle_avg_ereal u > - \<infinity>" "subcocycle_avg_ereal v > - \<infinity>"
  shows "subcocycle_avg_ereal (\<lambda>n x. max (u n x) (v n x)) > -\<infinity>"
        "subcocycle_avg (\<lambda>n x. max (u n x) (v n x)) \<ge> max (subcocycle_avg u) (subcocycle_avg v)"
proof -
  show *: "subcocycle_avg_ereal (\<lambda>n x. max (u n x) (v n x)) > - \<infinity>"
    using assms(3) subcocycle_avg_ereal_max[OF assms(1) assms(2)] by auto
  have "ereal (subcocycle_avg (\<lambda>n x. max (u n x) (v n x))) \<ge> max (ereal(subcocycle_avg u)) (ereal(subcocycle_avg v))"
    using subcocycle_avg_real_ereal[OF assms(3)] subcocycle_avg_real_ereal[OF assms(4)]
      subcocycle_avg_real_ereal[OF *] subcocycle_avg_ereal_max[OF assms(1) assms(2)] by auto
  then show "subcocycle_avg (\<lambda>n x. max (u n x) (v n x)) \<ge> max (subcocycle_avg u) (subcocycle_avg v)"
    by auto
qed

lemma subcocycle_avg_birkhoff:
  assumes "integrable M u"
  shows "subcocycle_avg_ereal (birkhoff_sum u) > - \<infinity>"
        "subcocycle_avg (birkhoff_sum u) = (\<integral>x. u x \<partial>M)"
unfolding subcocycle_avg_def subcocycle_avg_ereal_birkhoff[OF assms(1)] by auto

end



subsection {*Almost sure convergence of subcocycles*}

text {*In this paragraph, we prove Kingman's theorem, i.e., the almost sure convergence of
subcocycles. Their limit is almost surely invariant. There is no really easy proof. The one we use
below is arguably the simplest known one, due to Steele (1989). The idea is to show that the limsup
of the subcocycle is bounded by the liminf (which is almost surely constant along trajectories), by
using subadditivity along time intervals where the liminf is almost reached, of length at most $N$.
For some points, the liminf takes a large time $>N$ to be reached. We neglect those times,
introducing an additional error that gets smaller with $N$, thanks to Birkhoff ergodic theorem
applied to the set of bad points. The error is most easily managed if the subcocycle is assumed to
be nonpositive, which one can assume in a first step. The general case is reduced to this one by
replacing $u_n$ with $u_n - S_n u_1 \leq 0$, and using Birkhoff theorem to control $S_n u_1$.*}

context fmpt begin

lemma kingman_theorem_AE_aux1:
  assumes "subcocycle u" "\<And>x. u 1 x \<le> 0"
  shows "\<exists>(g::'a\<Rightarrow>ereal). (g\<in>borel_measurable Invariants \<and> (\<forall>x. g x < \<infinity>) \<and> (AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> g x))"
proof -
  define l where "l = (\<lambda>x. liminf (\<lambda>n. u n x / n))"
  have u_meas [measurable]: "\<And>n. u n \<in> borel_measurable M" using assms(1) unfolding subcocycle_def by auto
  then have l_meas [measurable]: "l \<in> borel_measurable M" unfolding l_def by auto

  {
    fix x assume *: "(\<lambda>n. birkhoff_sum (u 1) n x / n) \<longlonglongrightarrow> real_cond_exp M Invariants (u 1) x"
    then have "(\<lambda>n. birkhoff_sum (u 1) n x / n) \<longlonglongrightarrow> ereal(real_cond_exp M Invariants (u 1) x)"
      by auto
    then have a: "liminf (\<lambda>n. birkhoff_sum (u 1) n x / n) = ereal(real_cond_exp M Invariants (u 1) x)"
      using lim_imp_Liminf by force

    have "ereal(u n x / n) \<le> ereal(birkhoff_sum (u 1) n x / n)" if "n>0" for n
      using subcocycle_bounded_by_birkhoff1[OF assms(1) that, of x] that by (simp add: divide_right_mono)
    with eventually_mono[OF eventually_gt_at_top[of 0] this]
    have "eventually (\<lambda>n. ereal(u n x / n) \<le> ereal(birkhoff_sum (u 1) n x / n)) sequentially" by auto
    then have "liminf (\<lambda>n. u n x / n) \<le> liminf (\<lambda>n. birkhoff_sum (u 1) n x / n)"
      by (simp add: Liminf_mono)
    then have "l x < \<infinity>" unfolding l_def using a by auto
  }
  then have "AE x in M. l x < \<infinity>"
    using birkhoff_theorem_AE_nonergodic[of "u 1"] subcocycle_def assms(1) by auto

  have l_dec: "\<And>x. l x \<le> l (T x)"
  proof -
    fix x
    have "l x = liminf (\<lambda>n. ereal ((u (n+1) x)/(n+1)))"
      unfolding l_def by (rule liminf_shift[of "\<lambda>n. ereal (u n x / real n)", symmetric])
    also have "... \<le> liminf (\<lambda>n. ereal((u 1 x)/(n+1)) + ereal((u n (T x))/(n+1)))"
    proof (rule Liminf_mono[OF eventuallyI])
      fix n
      have "u (1+n) x \<le> u 1 x + u n ((T^^1) x)" using assms(1) unfolding subcocycle_def by blast
      then have "u (n+1) x \<le> u 1 x + u n (T x)" by auto
      then have "(u (n+1) x)/(n+1) \<le> (u 1 x)/(n+1) + (u n (T x))/(n+1)"
        by (metis add_divide_distrib divide_right_mono of_nat_0_le_iff)
      then show "ereal ((u (n+1) x)/(n+1)) \<le> ereal((u 1 x)/(n+1)) + ereal((u n (T x))/(n+1))" by auto
    qed
    also have "... = 0 + liminf(\<lambda>n. ereal((u n (T x))/(n+1)))"
    proof (rule ereal_liminf_lim_add[of "\<lambda>n. ereal((u 1 x)/real(n+1))" 0 "\<lambda>n. ereal((u n (T x))/(n+1))"])
      have "(\<lambda>n. 1/real(n+1)) \<longlonglongrightarrow> 0" using lim_1_over_n LIMSEQ_ignore_initial_segment by blast
      with tendsto_mult_right_zero[OF this] have "(\<lambda>n. (u 1 x)/real(n+1)) \<longlonglongrightarrow> 0" by auto
      then show "(\<lambda>n. ereal((u 1 x)/real(n+1))) \<longlonglongrightarrow> 0" by (simp add: zero_ereal_def)
    qed (simp)
    also have "... = 1 * liminf(\<lambda>n. ereal((u n (T x))/(n+1)))" by simp
    also have "... = liminf(\<lambda>n. (n+1)/n * ereal((u n (T x))/(n+1)))"
    proof (rule ereal_liminf_lim_mult[symmetric])
      have "real (n+1) / real n = 1 + 1/real n" if "n>0" for n by (simp add: divide_simps mult.commute that)
      with eventually_mono[OF eventually_gt_at_top[of "0::nat"] this]
      have "eventually (\<lambda>n. real (n+1) / real n = 1 + 1/real n) sequentially" by simp
      moreover have "(\<lambda>n. 1 + 1/real n) \<longlonglongrightarrow> 1 + 0"
        apply (rule tendsto_add) using lim_1_over_n by auto
      ultimately have "(\<lambda>n. real (n+1) / real n) \<longlonglongrightarrow> 1" using Lim_transform_eventually by (simp add: filterlim_cong)
      then show "(\<lambda>n. ereal(real (n+1) / real n)) \<longlonglongrightarrow> 1" by (simp add: one_ereal_def)
    qed (auto)
    also have "... = l (T x)" unfolding l_def by auto
    finally show "l x \<le> l (T x)" by simp
  qed
  have "AE x in M. l (T x) = l x" apply (rule AE_increasing_then_invariant) using l_dec by auto
  then obtain g0 where g0: "g0 \<in> borel_measurable Invariants" "AE x in M. l x = g0 x"
    using Invariants_quasi_Invariants_functions[OF l_meas] by auto
  define g where "g = (\<lambda>x. if g0 x = \<infinity> then 0 else g0 x)"
  have g: "g \<in> borel_measurable Invariants" "AE x in M. g x = l x"
    unfolding g_def using g0(1) `AE x in M. l x = g0 x` `AE x in M. l x < \<infinity>` by auto
  have [measurable]: "g \<in> borel_measurable M" using g(1) Invariants_measurable_func by blast
  have "\<And>x. g x < \<infinity>" unfolding g_def by auto

  define A where "A = {x \<in> space M. l x < \<infinity> \<and> (\<forall>n. l ((T^^n) x) = g ((T^^n) x))}"
  have A_meas [measurable]: "A \<in> sets M" unfolding A_def by auto
  have "AE x in M. x \<in> A" unfolding A_def using T_AE_iterates[OF g(2)] `AE x in M. l x < \<infinity>` by auto
  then have "space M - A \<in> null_sets M" by (simp add: AE_iff_null set_diff_eq)

  have l_inv: "l((T^^n) x) = l x" if "x \<in> A" for x n
  proof -
    have "l((T^^n) x) = g((T^^n) x)" using \<open> x \<in> A \<close> unfolding A_def by blast
    also have "... = g x" using g(1) A_def Invariants_func_is_invariant_n that by blast
    also have "... = g((T^^0) x)" by auto
    also have "... = l((T^^0) x)" using \<open> x \<in> A \<close> unfolding A_def by (metis (mono_tags, lifting) mem_Collect_eq)
    finally show ?thesis by auto
  qed

  define F where "F = (\<lambda> K e x. real_of_ereal(max (l x) (-ereal K)) + e)"
  have F_meas [measurable]: "F K e \<in> borel_measurable M" for K e unfolding F_def by auto
  define B where "B = (\<lambda>N K e. {x \<in> A. \<exists>n\<in>{1..N}. u n x - n * F K e x < 0})"
  have B_meas [measurable]: "B N K e \<in> sets M" for N K e unfolding B_def by (measurable)
  define I where "I = (\<lambda>N K e x. (indicator (- B N K e) x)::real)"
  have I_meas [measurable]: "I N K e \<in> borel_measurable M" for N K e unfolding I_def by auto
  have I_int: "integrable M (I N K e)" for N K e
    unfolding I_def apply (subst integrable_cong[where ?g = "indicator (space M - B N K e)::_ \<Rightarrow> real"], auto)
    by (auto split: split_indicator simp: less_top[symmetric])

  have main: "AE x in M. limsup (\<lambda>n. u n x / n) \<le> F K e x + abs(F K e x) * ereal(real_cond_exp M Invariants (I N K e) x)"
    if "N>(1::nat)" "K>(0::real)" "e>(0::real)" for N K e
  proof -
    let ?B = "B N K e" and ?I = "I N K e" and ?F = "F K e"

    define t where "t = (\<lambda>x. if x \<in> ?B then Min {n\<in>{1..N}. u n x - n * ?F x < 0} else 1)"
    have [measurable]: "t \<in> measurable M (count_space UNIV)" unfolding t_def by measurable
    have t1: "t x \<in> {1..N}" for x
    proof (cases "x \<in> ?B")
      case False
      then have "t x = 1" by (simp add: t_def)
      then show ?thesis using `N>1`by auto
    next
      case True
      let ?A = "{n\<in>{1..N}. u n x - n * ?F x < 0}"
      have "t x = Min ?A" using True by (simp add: t_def)
      moreover have "Min ?A \<in> ?A" apply (rule Min_in, simp) using True B_def by blast
      ultimately show ?thesis by auto
    qed

    have bound1: "u (t x) x \<le> t x * ?F x + birkhoff_sum ?I (t x) x * abs(?F x)" for x
    proof (cases "x \<in> ?B")
      case True
      let ?A = "{n\<in>{1..N}. u n x - n * F K e x < 0}"
      have "t x = Min ?A" using True by (simp add: t_def)
      moreover have "Min ?A \<in> ?A" apply (rule Min_in, simp) using True B_def by blast
      ultimately have "u (t x) x \<le> (t x) * ?F x" by auto
      moreover have "0 \<le> birkhoff_sum ?I (t x) x * abs(?F x)" unfolding birkhoff_sum_def I_def by (simp add: setsum_nonneg)
      ultimately show ?thesis by auto
    next
      case False
      then have "0 \<le> ?F x + ?I x * abs(?F x)" unfolding I_def by auto
      then have "u 1 x \<le> ?F x + ?I x * abs(?F x)" using assms(2)[of x] by auto
      moreover have "t x = 1" unfolding t_def using False by auto
      ultimately show ?thesis by auto
    qed

    define TB where "TB = (\<lambda>x. (T^^(t x)) x)"
    have [measurable]: "TB \<in> measurable M M" unfolding TB_def by auto
    define S where "S = (\<lambda>n x. (\<Sum>i<n. t((TB^^i) x)))"
    have [measurable]: "S n \<in> measurable M (count_space UNIV)" for n unfolding S_def by measurable
    have TB_pow: "(TB^^n) x = (T^^(S n x)) x" for n x
    unfolding S_def TB_def by (induction n, auto, metis (mono_tags, lifting) add.commute funpow_add o_apply)

    have uS: "u (S n x) x \<le> (S n x) * ?F x + birkhoff_sum ?I (S n x) x * abs(?F x)" if "x \<in> A" "n>0" for x n
    proof (induction rule: ind_from_1[OF `n>0`])
      case 1
      show ?case unfolding S_def using bound1 by auto
    next
      case (2 n)
      have *: "?F((TB^^n) x) = ?F x" apply (subst TB_pow) unfolding F_def using l_inv[OF `x\<in>A`] by auto
      have **: "S n x + t ((TB^^n) x) = S (Suc n) x" unfolding S_def by auto
      have "u (S (Suc n) x) x = u (S n x + t((TB^^n) x)) x" unfolding S_def by auto
      also have "... \<le> u (S n x) x + u (t((TB^^n) x)) ((T^^(S n x)) x)"
        using assms(1) unfolding subcocycle_def by auto
      also have "... \<le> u (S n x) x + u (t((TB^^n) x)) ((TB^^n) x)"
        using TB_pow by auto
      also have "... \<le> (S n x) * ?F x + birkhoff_sum ?I (S n x) x * abs(?F x) +
                  t ((TB^^n) x) * ?F ((TB^^n) x) + birkhoff_sum ?I (t ((TB^^n) x)) ((TB^^n) x) * abs(?F ((TB^^n) x))"
        using 2 bound1[of "((TB^^n) x)"] by auto
      also have "... = (S n x) * ?F x + birkhoff_sum ?I (S n x) x * abs(?F x) +
                  t ((TB^^n) x) * ?F x + birkhoff_sum ?I (t ((TB^^n) x)) ((T^^(S n x)) x) * abs(?F x)"
        using * TB_pow by auto
      also have "... = (real(S n x) + t ((TB^^n) x)) * ?F x +
                  (birkhoff_sum ?I (S n x) x + birkhoff_sum ?I (t ((TB^^n) x)) ((T^^(S n x)) x)) * abs(?F x)"
        by (simp add: mult.commute ring_class.ring_distribs(1))
      also have "... = (S n x + t ((TB^^n) x)) * ?F x +
                  (birkhoff_sum ?I (S n x) x + birkhoff_sum ?I (t ((TB^^n) x)) ((T^^(S n x)) x)) * abs(?F x)"
        by simp
      also have "... = (S (Suc n) x) * ?F x + birkhoff_sum ?I (S (Suc n) x) x * abs(?F x)"
        by (subst birkhoff_sum_cocycle[symmetric], subst **, subst **, simp)
      finally show ?case by simp
    qed

    have un: "u n x \<le> n * ?F x + N * abs(?F x) + birkhoff_sum ?I n x * abs(?F x)" if "x \<in> A" "n>N" for x n
    proof -
      let ?A = "{i. S i x > n}"
      let ?iA = "Inf ?A"
      have "n < (\<Sum>i<n + 1. 1)" by auto
      also have "... \<le> S (n+1) x" unfolding S_def apply (rule setsum_mono) using t1 by auto
      finally have "?A \<noteq> {}" by blast
      then have "?iA \<in> ?A" by (meson Inf_nat_def1)
      moreover have "0 \<notin> ?A" unfolding S_def by auto
      ultimately have "?iA \<noteq> 0" by fastforce
      define j where "j = ?iA - 1"
      then have "j < ?iA" using `?iA \<noteq> 0` by auto
      then have "j \<notin> ?A" by (meson bdd_below_def cInf_lower le0 not_less)
      then have "S j x \<le> n" by auto
      define k where "k = n - S j x"
      have "n = S j x + k" unfolding k_def using `S j x \<le> n` by auto
      have "n < S (j+1) x" unfolding j_def using `?iA \<noteq> 0` `?iA \<in> ?A` by auto
      also have "... = S j x + t((TB^^j) x)" unfolding S_def by auto
      also have "... \<le> S j x + N" using t1 by auto
      finally have "k \<le> N" unfolding k_def using `n > N` by auto
      then have "S j x > 0" unfolding k_def using `n > N` by auto
      then have "j > 0" unfolding S_def using not_gr0 by fastforce

      have "birkhoff_sum ?I (S j x) x \<le> birkhoff_sum ?I n x"
        unfolding birkhoff_sum_def I_def using `S j x \<le> n`
        by (metis finite_Collect_less_nat indicator_pos_le lessThan_def lessThan_subset_iff setsum_mono2)

      have "u n x \<le> u (S j x) x"
      proof (cases "k=0")
        case True
        show ?thesis using True unfolding k_def using `S j x \<le> n` by auto
      next
        case False
        then have "k > 0" by simp
        have "u k ((T^^(S j x)) x) \<le> birkhoff_sum (u 1) k ((T ^^ S j x) x)"
          using subcocycle_bounded_by_birkhoff1[OF assms(1) `k>0`, of "(T^^(S j x)) x"] by simp
        also have "... \<le> 0" unfolding birkhoff_sum_def using setsum_mono assms(2) by (simp add: setsum_nonpos)
        also have "u n x \<le> u (S j x) x + u k ((T^^(S j x)) x)"
          apply (subst `n = S j x + k`) using assms(1) subcocycle_def by auto
        ultimately show ?thesis by auto
      qed
      also have "... \<le> (S j x) * ?F x + birkhoff_sum ?I (S j x) x * abs(?F x)"
        using uS[OF `x \<in> A` `j>0`] by simp
      also have "... \<le> (S j x) * ?F x + birkhoff_sum ?I n x * abs(?F x)"
        using `birkhoff_sum ?I (S j x) x \<le> birkhoff_sum ?I n x` by (simp add: mult_right_mono)
      also have "... = n * ?F x - k * ?F x + birkhoff_sum ?I n x * abs(?F x)"
        by (metis `n = S j x + k` add_diff_cancel_right' le_add2 left_diff_distrib' of_nat_diff)
      also have "... \<le> n * ?F x + k * abs(?F x) + birkhoff_sum ?I n x * abs(?F x)"
        by (auto, metis abs_ge_minus_self abs_mult abs_of_nat)
      also have "... \<le> n * ?F x + N * abs(?F x) + birkhoff_sum ?I n x * abs(?F x)"
        using `k \<le> N` by (simp add: mult_right_mono)
      finally show ?thesis by simp
    qed

    have "limsup (\<lambda>n. u n x / n) \<le> ?F x + limsup (\<lambda>n. abs(?F x) * ereal(birkhoff_sum ?I n x / n))" if "x \<in> A" for x
    proof -
      have "(\<lambda>n. ?F x + N * abs(?F x) / n) \<longlonglongrightarrow> ?F x + 0"
        apply (rule tendsto_add, auto) using tendsto_mult[OF _ lim_1_over_n] by auto
      then have "(\<lambda>n. ereal(?F x + N * abs(?F x)/n)) \<longlonglongrightarrow> ereal(?F x)" by auto
      then have *: "limsup (\<lambda>n. ?F x + N * abs(?F x)/n) = ?F x"
        using sequentially_bot tendsto_iff_Liminf_eq_Limsup by blast

      {
        fix n assume "n > N"
        have "u n x / real n \<le> ?F x + N * abs(?F x) / n + abs(?F x) * birkhoff_sum ?I n x / n"
          using un[OF `x \<in> A` `n > N`] using `n>N` by (auto simp add: divide_simps mult.commute)
        then have "ereal(u n x/n) \<le> ereal(?F x + N * abs(?F x) / n) + abs(?F x) * ereal(birkhoff_sum ?I n x / n)"
          by auto
      }
      then have "eventually (\<lambda>n. ereal(u n x / n) \<le> ereal(?F x + N * abs(?F x) / n) + abs(?F x) * ereal(birkhoff_sum ?I n x / n)) sequentially"
        using eventually_mono[OF eventually_gt_at_top[of N]] by auto
      with Limsup_mono[OF this]
      have "limsup (\<lambda>n. u n x / n) \<le> limsup (\<lambda>n. ereal(?F x + N * abs(?F x) / n) + abs(?F x) * ereal(birkhoff_sum ?I n x / n))"
        by auto
      also have "... \<le> limsup (\<lambda>n. ?F x + N * abs(?F x) / n) + limsup (\<lambda>n. abs(?F x) * ereal(birkhoff_sum ?I n x / n))"
        by (rule ereal_limsup_add_mono)
      also have "... = ?F x + limsup (\<lambda>n. abs(?F x) * ereal(birkhoff_sum ?I n x / n))"
        using * by auto
      finally show ?thesis by auto
    qed
    then have *: "AE x in M. limsup (\<lambda>n. u n x / n) \<le> ?F x + limsup (\<lambda>n. abs(?F x) * ereal(birkhoff_sum ?I n x / n))"
      using `AE x in M. x \<in> A` by auto

    {
      fix x assume H: "(\<lambda>n. birkhoff_sum ?I n x / n) \<longlonglongrightarrow> real_cond_exp M Invariants ?I x"
      have "(\<lambda>n. abs(?F x) * ereal(birkhoff_sum ?I n x / n)) \<longlonglongrightarrow> abs(?F x) * ereal(real_cond_exp M Invariants ?I x)"
        by (rule tendsto_mult_ereal, auto simp add: H)
      then have "limsup (\<lambda>n. abs(?F x) * ereal(birkhoff_sum ?I n x / n)) = abs(?F x) * ereal(real_cond_exp M Invariants ?I x)"
        using sequentially_bot tendsto_iff_Liminf_eq_Limsup by blast
    }
    moreover have "AE x in M. (\<lambda>n. birkhoff_sum ?I n x / n) \<longlonglongrightarrow> real_cond_exp M Invariants ?I x"
      by (rule birkhoff_theorem_AE_nonergodic[OF I_int])
    ultimately have "AE x in M. limsup (\<lambda>n. abs(?F x) * ereal(birkhoff_sum ?I n x / n)) = abs(?F x) * ereal(real_cond_exp M Invariants ?I x)"
      by auto
    then show ?thesis using * by auto
  qed

  have bound2: "AE x in M. limsup (\<lambda>n. u n x / n) \<le> F K e x" if "K > 0" "e > 0" for K e
  proof -
    define C where "C = (\<lambda>N. A - B N K e)"
    have C_meas [measurable]: "\<And>N. C N \<in> sets M" unfolding C_def by auto
    {
      fix x assume "x \<in> A"
      have "F K e x > l x" using `x \<in> A` `e > 0` unfolding F_def A_def
        by (cases "l x", auto, metis add.commute ereal_max less_add_same_cancel2 max_less_iff_conj real_of_ereal.simps(1))
      then have "\<exists>n>0. ereal(u n x / n) < F K e x" unfolding l_def using liminf_upper_bound by fastforce
      then obtain n where "n>0" "ereal(u n x / n) < F K e x" by auto
      then have "u n x - n * F K e x < 0" by (simp add: divide_less_eq mult.commute)
      then have "x \<notin> C n" unfolding C_def B_def using `x \<in> A` `n>0` by auto
      then have "x \<notin> (\<Inter>n. C n)" by auto
    }
    then have "(\<Inter>n. C n) = {}" unfolding C_def by auto
    then have *: "0 = measure M (\<Inter>n. C n)" by auto
    have "(\<lambda>n. measure M (C n)) \<longlonglongrightarrow> 0"
      apply (subst *, rule finite_Lim_measure_decseq, auto) unfolding C_def B_def decseq_def by auto
    moreover have "measure M (C n) = (\<integral>x. norm(real_cond_exp M Invariants (I n K e) x) \<partial>M)" for n
    proof -
      have *: "AE x in M. 0 \<le> real_cond_exp M Invariants (I n K e) x"
        apply (rule real_cond_exp_pos, auto) unfolding I_def by auto

      have "measure M (C n) = (\<integral>x. indicator (C n) x \<partial>M)"
        by auto
      also have "... = (\<integral>x. I n K e x \<partial>M)"
        apply (rule integral_cong_AE, auto)
        unfolding C_def I_def indicator_def using `AE x in M. x \<in> A` by auto
      also have "... = (\<integral>x. real_cond_exp M Invariants (I n K e) x \<partial>M)"
        by (rule real_cond_exp_int(2)[symmetric, OF I_int])
      also have "... = (\<integral>x. norm(real_cond_exp M Invariants (I n K e) x) \<partial>M)"
        apply (rule integral_cong_AE, auto) using * by auto
      finally show ?thesis by auto
    qed
    ultimately have *: "(\<lambda>n. (\<integral>x. norm(real_cond_exp M Invariants (I n K e) x) \<partial>M)) \<longlonglongrightarrow> 0" by simp

    have "\<exists>r. subseq r \<and> (AE x in M. (\<lambda>n. real_cond_exp M Invariants (I (r n) K e) x) \<longlonglongrightarrow> 0)"
      apply (rule tendsto_L1_AE_subseq) using * real_cond_exp_int[OF I_int] by auto
    then obtain r where "subseq r" "AE x in M. (\<lambda>n. real_cond_exp M Invariants (I (r n) K e) x) \<longlonglongrightarrow> 0"
      by auto
    moreover have "AE x in M. \<forall>N \<in> {1<..}. limsup (\<lambda>n. u n x / n) \<le> F K e x + abs(F K e x) * ereal(real_cond_exp M Invariants (I N K e) x)"
      apply (rule AE_count_union) using main[OF _ `K>0` `e>0`] by auto
    moreover
    {
      fix x assume H: "(\<lambda>n. real_cond_exp M Invariants (I (r n) K e) x) \<longlonglongrightarrow> 0"
                      "\<And>N. N > 1 \<Longrightarrow> limsup (\<lambda>n. u n x / n) \<le> F K e x + abs(F K e x) * ereal(real_cond_exp M Invariants (I N K e) x)"
      have 1: "eventually (\<lambda>N. limsup (\<lambda>n. u n x / n) \<le> F K e x + abs(F K e x) * ereal(real_cond_exp M Invariants (I (r N) K e) x)) sequentially"
        apply (rule eventually_mono[OF eventually_gt_at_top[of 1] H(2)]) using `subseq r` less_le_trans seq_suble by blast
      have "(\<lambda>N. F K e x + (abs(F K e x) * ereal(real_cond_exp M Invariants (I (r N) K e) x))) \<longlonglongrightarrow> ereal(F K e x) + (abs(F K e x) * ereal 0)"
        by (rule tendsto_add_ereal_general, simp, simp, rule tendsto_mult_ereal, auto simp add: H(1))
      then have 2: "(\<lambda>N. F K e x + (abs(F K e x) * ereal(real_cond_exp M Invariants (I (r N) K e) x))) \<longlonglongrightarrow> F K e x"
        by auto
      have "limsup (\<lambda>n. u n x / n) \<le> F K e x"
        apply (rule LIMSEQ_le_const[OF 2]) using 1 by (simp add: eventually_at_top_linorder)
    }
    ultimately show "AE x in M. limsup (\<lambda>n. u n x / n) \<le> F K e x" by auto
  qed
  have "AE x in M. limsup (\<lambda>n. u n x / n) \<le> real_of_ereal(max (l x) (-ereal K))" if "K>(0::nat)" for K
  proof -
    have "\<And>e. e > (0::real) \<Longrightarrow> AE x in M. limsup (\<lambda>n. u n x / n) \<le> real_of_ereal(max (l x) (-ereal K)) + ereal e"
      using bound2 `K>0` unfolding F_def by auto
    then show ?thesis by (rule AE_upper_bound_inf_ereal, auto)
  qed
  then have "AE x in M. \<forall>K\<in>{(0::nat)<..}. limsup (\<lambda>n. u n x / n) \<le> real_of_ereal(max (l x) (-ereal K))"
    by (rule AE_count_union, auto)
  moreover have "(\<lambda>n. u n x / n) \<longlonglongrightarrow> l x"
    if H: "\<forall>K\<in>{(0::nat)<..}. limsup (\<lambda>n. u n x / n) \<le> real_of_ereal(max (l x) (-ereal K))" for x
  proof -
    have "limsup (\<lambda>n. u n x / n) \<le> l x"
    proof (cases "l x = \<infinity>")
      case False
      then have "(\<lambda>K. real_of_ereal(max (l x) (-ereal K))) \<longlonglongrightarrow> l x"
        using ereal_truncation_real_bottom by auto
      moreover have "eventually (\<lambda>K. limsup (\<lambda>n. u n x / n) \<le> real_of_ereal(max (l x) (-ereal K))) sequentially"
        using H by (metis (no_types, lifting) eventually_at_top_linorder eventually_gt_at_top greaterThan_iff)
      ultimately show "limsup (\<lambda>n. u n x / n) \<le> l x" using Lim_bounded2_ereal eventually_sequentially by auto
    qed (simp)
    then have "limsup (\<lambda>n. ereal (u n x / real n)) = l x"
      using Liminf_le_Limsup l_def eq_iff sequentially_bot by blast
    then show "(\<lambda>n. u n x / n) \<longlonglongrightarrow> l x"
      by (simp add: l_def tendsto_iff_Liminf_eq_Limsup)
  qed
  ultimately have "AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> l x" by auto
  then have "AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> g x" using g(2) by auto
  then show "\<exists>(g::'a\<Rightarrow>ereal). (g\<in>borel_measurable Invariants \<and> (\<forall>x. g x < \<infinity>) \<and> (AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> g x))"
    using g(1) `\<And>x. g x < \<infinity>` by auto
qed

theorem kingman_theorem_AE_aux2:
  assumes "subcocycle u"
  shows "\<exists>(g::'a\<Rightarrow>ereal). (g\<in>borel_measurable Invariants \<and> (\<forall>x. g x < \<infinity>) \<and> (AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> g x))"
proof -
  define v where "v = (\<lambda>n x. u n x + birkhoff_sum (\<lambda>x. - u 1 x) n x)"
  have "subcocycle v" unfolding v_def
    apply (rule subcocycle_add[OF assms], rule subcocycle_birkhoff)
    using assms unfolding subcocycle_def by auto
  have "\<exists>(gv::'a\<Rightarrow>ereal). (gv\<in>borel_measurable Invariants \<and> (\<forall>x. gv x < \<infinity>) \<and> (AE x in M. (\<lambda>n. v n x / n) \<longlonglongrightarrow> gv x))"
    apply (rule kingman_theorem_AE_aux1[OF `subcocycle v`]) unfolding v_def by auto
  then obtain gv where gv: "gv \<in> borel_measurable Invariants" "AE x in M. (\<lambda>n. v n x / n) \<longlonglongrightarrow> (gv x::ereal)" "\<And>x. gv x < \<infinity>"
    by blast
  define g where "g = (\<lambda>x. gv x + ereal(real_cond_exp M Invariants (u 1) x))"
  have g_meas: "g \<in> borel_measurable Invariants" unfolding g_def using gv(1) by auto
  have g_fin: "\<And>x. g x < \<infinity>" unfolding g_def using gv(3) by auto

  have "AE x in M. (\<lambda>n. birkhoff_sum (u 1) n x / n) \<longlonglongrightarrow> real_cond_exp M Invariants (u 1) x"
    apply (rule birkhoff_theorem_AE_nonergodic) using assms unfolding subcocycle_def by auto
  moreover
  {
    fix x assume H: "(\<lambda>n. v n x / n) \<longlonglongrightarrow> (gv x)"
                   "(\<lambda>n. birkhoff_sum (u 1) n x / n) \<longlonglongrightarrow> real_cond_exp M Invariants (u 1) x"
    then have "(\<lambda>n. ereal(birkhoff_sum (u 1) n x / n)) \<longlonglongrightarrow> ereal(real_cond_exp M Invariants (u 1) x)"
      by auto
    {
      fix n
      have "u n x = v n x + birkhoff_sum (u 1) n x"
        unfolding v_def birkhoff_sum_def apply auto by (simp add: setsum_negf)
      then have "u n x / n = v n x / n + birkhoff_sum (u 1) n x / n" by (simp add: add_divide_distrib)
      then have "ereal(u n x / n) = ereal(v n x / n) + ereal(birkhoff_sum (u 1) n x / n)"
        by auto
    } note * = this
    have "(\<lambda>n. ereal(u n x / n)) \<longlonglongrightarrow> g x" unfolding * g_def
      apply (rule tendsto_add_ereal_general) using H by auto
  }
  ultimately have "AE x in M. (\<lambda>n. ereal(u n x / n)) \<longlonglongrightarrow> g x" using gv(2) by auto
  then show ?thesis using g_meas g_fin by blast
qed

text {* For applications, it is convenient to have a limit which is really measurable with respect
to the invariant sigma algebra and does not come from a hard to use abstract existence statement.
Hence we introduce the following definition for the would-be limit -- Kingman's theorem shows that
it is indeed a limit.*}

definition subcocycle_lim_ereal::"(nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> ereal)"
  where "subcocycle_lim_ereal u = (
    if (\<exists>(g::'a\<Rightarrow>ereal). (g\<in>borel_measurable Invariants \<and>
      (\<forall>x. g x < \<infinity>) \<and> (AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> g x)))
    then (SOME (g::'a\<Rightarrow>ereal). g\<in>borel_measurable Invariants \<and>
      (\<forall>x. g x < \<infinity>) \<and> (AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> g x))
    else (\<lambda>_. 0))"

definition subcocycle_lim::"(nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real)"
  where "subcocycle_lim u = (\<lambda>x. real_of_ereal(subcocycle_lim_ereal u x))"

lemma subcocycle_lim_meas_Inv [measurable]:
  "subcocycle_lim_ereal u \<in> borel_measurable Invariants"
  "subcocycle_lim u \<in> borel_measurable Invariants"
proof -
  show "subcocycle_lim_ereal u \<in> borel_measurable Invariants"
    proof (cases "\<exists>(g::'a\<Rightarrow>ereal). (g\<in>borel_measurable Invariants \<and> (\<forall>x. g x < \<infinity>) \<and> (AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> g x))")
    case True
    then have "subcocycle_lim_ereal u = (SOME (g::'a\<Rightarrow>ereal). g\<in>borel_measurable Invariants \<and>
          (\<forall>x. g x < \<infinity>) \<and> (AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> g x))"
      unfolding subcocycle_lim_ereal_def by auto
    then show ?thesis using someI_ex[OF True] by auto
  next
    case False
    then have "subcocycle_lim_ereal u = (\<lambda>_. 0)" unfolding subcocycle_lim_ereal_def by auto
    then show ?thesis by auto
  qed
  then show "subcocycle_lim u \<in> borel_measurable Invariants" unfolding subcocycle_lim_def by auto
qed

lemma subcocycle_lim_meas [measurable]:
  "subcocycle_lim_ereal u \<in> borel_measurable M"
  "subcocycle_lim u \<in> borel_measurable M"
using subcocycle_lim_meas_Inv Invariants_measurable_func apply blast
using subcocycle_lim_meas_Inv Invariants_measurable_func by blast

lemma subcocycle_lim_ereal_not_PInf:
  "subcocycle_lim_ereal u x < \<infinity>"
proof (cases "\<exists>(g::'a\<Rightarrow>ereal). (g\<in>borel_measurable Invariants \<and> (\<forall>x. g x < \<infinity>) \<and> (AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> g x))")
  case True
  then have "subcocycle_lim_ereal u = (SOME (g::'a\<Rightarrow>ereal). g\<in>borel_measurable Invariants \<and>
        (\<forall>x. g x < \<infinity>) \<and> (AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> g x))"
    unfolding subcocycle_lim_ereal_def by auto
  then show ?thesis using someI_ex[OF True] by auto
next
  case False
  then have "subcocycle_lim_ereal u = (\<lambda>_. 0)" unfolding subcocycle_lim_ereal_def by auto
  then show ?thesis by auto
qed

text {*We reformulate the subadditive ergodic theorem of Kingman with this definition.
From this point on, the technical definition of \verb+subcocycle_lim_ereal+ will never be used, only
the following property will be relevant.*}

theorem kingman_theorem_AE_nonergodic_ereal:
  assumes "subcocycle u"
  shows "AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_lim_ereal u x"
proof -
  have *: "\<exists>(g::'a\<Rightarrow>ereal). (g\<in>borel_measurable Invariants \<and> (\<forall>x. g x < \<infinity>) \<and> (AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> g x))"
    using kingman_theorem_AE_aux2[OF assms] by auto
  then have "subcocycle_lim_ereal u = (SOME (g::'a\<Rightarrow>ereal). g\<in>borel_measurable Invariants \<and>
        (\<forall>x. g x < \<infinity>) \<and> (AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> g x))"
    unfolding subcocycle_lim_ereal_def by auto
  then show ?thesis using someI_ex[OF *] by auto
qed

lemma subcocycle_lim_ereal_add:
  assumes "subcocycle u" "subcocycle v"
  shows "AE x in M. subcocycle_lim_ereal (\<lambda>n x. u n x + v n x) x = subcocycle_lim_ereal u x + subcocycle_lim_ereal v x"
proof -
  have "AE x in M. (\<lambda>n. (u n x + v n x)/n) \<longlonglongrightarrow> subcocycle_lim_ereal (\<lambda>n x. u n x + v n x) x"
    by (rule kingman_theorem_AE_nonergodic_ereal[OF subcocycle_add[OF assms]])
  moreover have "AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_lim_ereal u x"
    by (rule kingman_theorem_AE_nonergodic_ereal[OF assms(1)])
  moreover have "AE x in M. (\<lambda>n. v n x / n) \<longlonglongrightarrow> subcocycle_lim_ereal v x"
    by (rule kingman_theorem_AE_nonergodic_ereal[OF assms(2)])
  moreover
  {
    fix x assume H: "(\<lambda>n. (u n x + v n x)/n) \<longlonglongrightarrow> subcocycle_lim_ereal (\<lambda>n x. u n x + v n x) x"
                    "(\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_lim_ereal u x"
                    "(\<lambda>n. v n x / n) \<longlonglongrightarrow> subcocycle_lim_ereal v x"
    have "(\<lambda>n. ereal (u n x / n) + (v n x / n)) \<longlonglongrightarrow> subcocycle_lim_ereal u x + subcocycle_lim_ereal v x"
      apply (rule tendsto_add_ereal_general[OF _ H(2) H(3)]) using subcocycle_lim_ereal_not_PInf by auto
    moreover have "ereal (u n x / n) + (v n x / n) = (u n x + v n x)/n" for n
      by (simp add: add_divide_distrib)
    ultimately have "(\<lambda>n. (u n x + v n x)/n) \<longlonglongrightarrow> subcocycle_lim_ereal u x + subcocycle_lim_ereal v x"
      by auto
    then have "subcocycle_lim_ereal (\<lambda>n x. u n x + v n x) x = subcocycle_lim_ereal u x + subcocycle_lim_ereal v x"
      using H(1) by (simp add: LIMSEQ_unique)
  }
  ultimately show ?thesis by auto
qed

lemma subcocycle_lim_ereal_cmult:
  assumes "subcocycle u" "c\<ge>(0::real)"
  shows "AE x in M. subcocycle_lim_ereal (\<lambda>n x. c * u n x) x = c * subcocycle_lim_ereal u x"
proof -
  have "AE x in M. (\<lambda>n. (c * u n x)/n) \<longlonglongrightarrow> subcocycle_lim_ereal (\<lambda>n x. c * u n x) x"
    by (rule kingman_theorem_AE_nonergodic_ereal[OF subcocycle_cmult[OF assms]])
  moreover have "AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_lim_ereal u x"
    by (rule kingman_theorem_AE_nonergodic_ereal[OF assms(1)])
  moreover
  {
    fix x assume H: "(\<lambda>n. (c * u n x)/n) \<longlonglongrightarrow> subcocycle_lim_ereal (\<lambda>n x. c * u n x) x"
                    "(\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_lim_ereal u x"
    have "(\<lambda>n. c * ereal (u n x / n)) \<longlonglongrightarrow> c * subcocycle_lim_ereal u x"
      by (rule tendsto_cmult_ereal[OF _ H(2)], auto)
    then have "subcocycle_lim_ereal (\<lambda>n x. c * u n x) x = c * subcocycle_lim_ereal u x"
      using H(1) by (simp add: LIMSEQ_unique)
  }
  ultimately show ?thesis by auto
qed

lemma subcocycle_lim_ereal_max:
  assumes "subcocycle u" "subcocycle v"
  shows "AE x in M. subcocycle_lim_ereal (\<lambda>n x. max (u n x) (v n x)) x
                    = max (subcocycle_lim_ereal u x) (subcocycle_lim_ereal v x)"
proof -
  have "AE x in M. (\<lambda>n. max (u n x) (v n x) / n) \<longlonglongrightarrow> subcocycle_lim_ereal (\<lambda>n x. max (u n x) (v n x)) x"
    by (rule kingman_theorem_AE_nonergodic_ereal[OF subcocycle_max[OF assms]])
  moreover have "AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_lim_ereal u x"
    by (rule kingman_theorem_AE_nonergodic_ereal[OF assms(1)])
  moreover have "AE x in M. (\<lambda>n. v n x / n) \<longlonglongrightarrow> subcocycle_lim_ereal v x"
    by (rule kingman_theorem_AE_nonergodic_ereal[OF assms(2)])
  moreover
  {
    fix x assume H: "(\<lambda>n. max (u n x) (v n x) / n) \<longlonglongrightarrow> subcocycle_lim_ereal (\<lambda>n x. max (u n x) (v n x)) x"
                    "(\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_lim_ereal u x"
                    "(\<lambda>n. v n x / n) \<longlonglongrightarrow> subcocycle_lim_ereal v x"
    have "(\<lambda>n. max (ereal(u n x / n)) (ereal(v n x / n)))
            \<longlonglongrightarrow> max (subcocycle_lim_ereal u x) (subcocycle_lim_ereal v x)"
      apply (rule tendsto_max) using H by auto
    moreover have "max (ereal(u n x / n)) (ereal(v n x / n)) = max (u n x) (v n x) / n" for n
      by (simp del: ereal_max add:ereal_max[symmetric] max_divide_distrib_right)
    ultimately have "(\<lambda>n. max (u n x) (v n x) / n)
          \<longlonglongrightarrow> max (subcocycle_lim_ereal u x) (subcocycle_lim_ereal v x)"
      by auto
    then have "subcocycle_lim_ereal (\<lambda>n x. max (u n x) (v n x)) x
                = max (subcocycle_lim_ereal u x) (subcocycle_lim_ereal v x)"
      using H(1) by (simp add: LIMSEQ_unique)
  }
  ultimately show ?thesis by auto
qed

lemma subcocycle_lim_ereal_birkhoff:
  assumes "integrable M u"
  shows "AE x in M. subcocycle_lim_ereal (birkhoff_sum u) x = ereal(real_cond_exp M Invariants u x)"
proof -
  have "AE x in M. (\<lambda>n. birkhoff_sum u n x / n) \<longlonglongrightarrow> real_cond_exp M Invariants u x"
    by (rule birkhoff_theorem_AE_nonergodic[OF assms])
  moreover have "AE x in M. (\<lambda>n. birkhoff_sum u n x / n) \<longlonglongrightarrow> subcocycle_lim_ereal (birkhoff_sum u) x"
    by (rule kingman_theorem_AE_nonergodic_ereal[OF subcocycle_birkhoff[OF assms]])
  moreover
  {
    fix x assume H: "(\<lambda>n. birkhoff_sum u n x / n) \<longlonglongrightarrow> real_cond_exp M Invariants u x"
                    "(\<lambda>n. birkhoff_sum u n x / n) \<longlonglongrightarrow> subcocycle_lim_ereal (birkhoff_sum u) x"
    have "(\<lambda>n. birkhoff_sum u n x / n) \<longlonglongrightarrow> ereal(real_cond_exp M Invariants u x)"
      using H(1) by auto
    then have "subcocycle_lim_ereal (birkhoff_sum u) x = ereal(real_cond_exp M Invariants u x)"
      using H(2) by (simp add: LIMSEQ_unique)
  }
  ultimately show ?thesis by auto
qed

subsection {*$L^1$ and a.e.\ convergence of subcocycles with finite asymptotic average*}

text {*In this subsection, we show that the almost sure convergence in Kingman theorem
also takes place in $L^1$ if the limit is integrable, i.e., if the asymptotic average
of the subcocycle is $> -\infty$. To deduce it from the almost sure convergence, we only need
to show that there is no loss of mass, i.e., that the integral of the limit is not
strictly larger than the limit of the integrals (thanks to Scheffe criterion). This follows
from comparison to Birkhoff sums, for which we know that the average of the limit is
the same as the average of the function.*}

lemma subcocycle_lim_ereal_atmost_uN_invariants:
  assumes "subcocycle u" "N>(0::nat)"
  shows "AE x in M. subcocycle_lim_ereal u x \<le> real_cond_exp M Invariants (\<lambda>x. u N x / N) x"
proof -
  have "AE x in M. (\<lambda>n. u 1 ((T^^n) x) / n) \<longlonglongrightarrow> 0"
    apply (rule limit_foTn_over_n) using assms(1) unfolding subcocycle_def by auto
  moreover have "AE x in M. (\<lambda>n. birkhoff_sum (\<lambda>x. u N x/N) n x / n) \<longlonglongrightarrow> real_cond_exp M Invariants (\<lambda>x. u N x / N) x"
    apply (rule birkhoff_theorem_AE_nonergodic) using assms(1) unfolding subcocycle_def by auto
  moreover have "AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_lim_ereal u x"
    by (rule kingman_theorem_AE_nonergodic_ereal[OF assms(1)])
  moreover
  {
    fix x assume H: "(\<lambda>n. u 1 ((T^^n) x) / n) \<longlonglongrightarrow> 0"
                    "(\<lambda>n. birkhoff_sum (\<lambda>x. u N x/N) n x / n) \<longlonglongrightarrow> real_cond_exp M Invariants (\<lambda>x. u N x / N) x"
                    "(\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_lim_ereal u x"

    let ?f = "\<lambda>n. birkhoff_sum (\<lambda>x. u N x / real N) (n - 2 * N) x / n
                  + (\<Sum>i<N. (1/n) * \<bar>u 1 ((T ^^ i) x)\<bar>)
                  + 2 * (\<Sum>i<2*N. \<bar>u 1 ((T ^^ (n - (2 * N - i))) x)\<bar> / n)"
    {
      fix n assume "n\<ge>2*N+1"
      then have "n > 2 * N" by simp
      have "u n x / n \<le> (birkhoff_sum (\<lambda>x. u N x / real N) (n - 2 * N) x
                  + (\<Sum>i<N. \<bar>u 1 ((T ^^ i) x)\<bar>)
                  + 2 * (\<Sum>i<2*N. \<bar>u 1 ((T ^^ (n - (2 * N - i))) x)\<bar>)) / n"
        using subcocycle_bounded_by_birkhoffN[OF assms(1) `n>2*N` `N>0`, of x] `n>2*N` by (simp add: divide_right_mono)
      also have "... = ?f n"
        apply (subst add_divide_distrib)+ by (auto simp add: setsum_divide_distrib[symmetric])
      finally have "u n x / n \<le> ?f n" by simp
      then have "u n x / n \<le> ereal(?f n)" by simp
    }

    have *: "(\<lambda>n. (1/n)*\<bar>u 1 ((T ^^ i) x)\<bar>) \<longlonglongrightarrow> 0 * \<bar>u 1 ((T ^^ i) x)\<bar>" for i
        by (rule tendsto_mult, auto simp add: lim_1_over_n)
    have "(\<lambda>n. (\<Sum>i<N. (1/n)*\<bar>u 1 ((T ^^ i) x)\<bar>)) \<longlonglongrightarrow> (\<Sum>i<N. 0)"
      apply (rule tendsto_setsum) using * by auto
    then have S1: "(\<lambda>n. (\<Sum>i<N. (1/n)*\<bar>u 1 ((T ^^ i) x)\<bar>)) \<longlonglongrightarrow> 0" by simp

    have S2: "(\<lambda>n. birkhoff_sum (\<lambda>x. u N x / real N) (n - 2 * N) x / n) \<longlonglongrightarrow> real_cond_exp M Invariants (\<lambda>x. u N x / N) x"
      using tendsto_shift_1_over_n'[OF H(2), of "2*N"] by simp

    have A: "(\<lambda>n. abs(u 1((T^^n) x)) / n) \<longlonglongrightarrow> 0" using tendsto_norm[OF H(1)] by auto
    have B: "(\<lambda>n. abs(u 1((T^^(n-(2*N-i))) x)) / n) \<longlonglongrightarrow> 0" for i
      using tendsto_shift_1_over_n'[OF A, of "2*N-i"] by simp
    have "(\<lambda>n. 2 * (\<Sum>i<2*N. \<bar>u 1 ((T ^^ (n - (2 * N - i))) x)\<bar>/n)) \<longlonglongrightarrow> 2 * (\<Sum>i<2*N. 0)"
      apply (rule tendsto_mult, simp)
      apply (rule tendsto_setsum) using B by blast
    then have S3: "(\<lambda>n. 2 * (\<Sum>i<2*N. \<bar>u 1 ((T ^^ (n - (2 * N - i))) x)\<bar>/n)) \<longlonglongrightarrow> 0" by simp

    have "(\<lambda>n. ?f n) \<longlonglongrightarrow> real_cond_exp M Invariants (\<lambda>x. u N x / N) x + 0 + 0"
      apply (rule tendsto_add, rule tendsto_add) using S1 S2 S3 by auto
    then have "(\<lambda>n. ereal(?f n)) \<longlonglongrightarrow> real_cond_exp M Invariants (\<lambda>x. u N x / N) x"
      by auto
    with ereal_lim_mono[OF `\<And>n. n \<ge> 2*N+1 \<Longrightarrow> u n x / n \<le> ereal(?f n)` H(3) this]
    have "subcocycle_lim_ereal u x \<le> real_cond_exp M Invariants (\<lambda>x. u N x / N) x" by simp
  }
  ultimately show ?thesis by auto
qed

text {*To apply Scheffe criterion, we need to deal with nonnegative functions, or equivalently
with nonpositive functions after a change of sign. Hence, as in the proof of the almost
sure version of Kingman theorem above, we first give the proof assuming that the
subcocycle is nonpositive, and deduce the general statement by adding a suitable
Birkhoff sum.*}

lemma kingman_theorem_L1_aux:
  assumes "subcocycle u" "subcocycle_avg_ereal u > -\<infinity>" "\<And>x. u 1 x \<le> 0"
  shows "AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_lim u x"
        "integrable M (subcocycle_lim u)"
        "(\<lambda>n. (\<integral>\<^sup>+x. abs(u n x / n - subcocycle_lim u x) \<partial>M)) \<longlonglongrightarrow> 0"
proof -
  have int_u [measurable]: "\<And>n. integrable M (u n)" using assms(1) subcocycle_def by auto
  then have int_F [measurable]: "\<And>n. integrable M (\<lambda>x. - u n x/ n)" by auto

  have F_pos: "- u n x / n \<ge> 0" for x and n::nat
  proof (cases "n > 0")
    case True
    have "u n x \<le> (\<Sum>i<n. u 1 ((T ^^ i) x))"
      using subcocycle_bounded_by_birkhoff1[OF assms(1) `n>0`] unfolding birkhoff_sum_def by simp
    also have "... \<le> 0" using setsum_mono[OF assms(3)] by auto
    finally have "u n x \<le> 0" by simp
    then have "-u n x \<ge> 0" by simp
    with divide_nonneg_nonneg[OF this] show "- u n x / n \<ge> 0" using `n>0` by auto
  qed (auto)


  {
    fix x assume *: "(\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_lim_ereal u x"
    have H: "(\<lambda>n. - u n x / n) \<longlonglongrightarrow> - subcocycle_lim_ereal u x"
      using tendsto_cmult_ereal[OF _ *, of "-1"] by auto
    have "liminf (\<lambda>n. -u n x / n) = - subcocycle_lim_ereal u x"
         "(\<lambda>n. - u n x / n) \<longlonglongrightarrow> - subcocycle_lim_ereal u x"
         "- subcocycle_lim_ereal u x \<ge> 0"
      using H apply (simp add: tendsto_iff_Liminf_eq_Limsup, simp)
      apply (rule LIMSEQ_le_const[OF H]) using F_pos by auto
  }
  then have AE_1: "AE x in M. liminf (\<lambda>n. -u n x / n) = - subcocycle_lim_ereal u x"
                  "AE x in M. (\<lambda>n. - u n x / n) \<longlonglongrightarrow> - subcocycle_lim_ereal u x"
                  "AE x in M. - subcocycle_lim_ereal u x \<ge> 0"
    using kingman_theorem_AE_nonergodic_ereal[OF assms(1)] by auto

  have "(\<integral>\<^sup>+ x. -subcocycle_lim_ereal u x \<partial>M) = (\<integral>\<^sup>+ x. liminf (\<lambda>n. -u n x / n) \<partial>M)"
    apply (rule nn_integral_cong_AE) using AE_1(1) by auto
  also have "... \<le> liminf (\<lambda>n. \<integral>\<^sup>+ x. -u n x / n \<partial>M)"
    apply (subst e2ennreal_Liminf)
    apply (simp_all add: e2ennreal_ereal)
    using F_pos by (intro nn_integral_liminf) (simp add: int_F)
  also have "... = - subcocycle_avg_ereal u"
  proof -
    have "(\<lambda>n. (\<integral>x. u n x / n \<partial>M)) \<longlonglongrightarrow> subcocycle_avg_ereal u"
      by (rule subcocycle_int_tendsto_avg_ereal[OF assms(1)])
    with tendsto_cmult_ereal[OF _ this, of "-1"]
    have "(\<lambda>n. (\<integral>x. - u n x / n \<partial>M)) \<longlonglongrightarrow> - subcocycle_avg_ereal u" by simp
    then have "- subcocycle_avg_ereal u = liminf (\<lambda>n. (\<integral>x. - u n x / n \<partial>M))"
      by (simp add: tendsto_iff_Liminf_eq_Limsup)
    moreover have "(\<integral>\<^sup>+ x. ennreal (-u n x / n) \<partial>M) = ennreal(\<integral>x. - u n x / n \<partial>M)" for n
      apply (rule nn_integral_eq_integral[OF int_F]) using F_pos by auto
    ultimately show ?thesis
      by (auto simp: e2ennreal_Liminf e2ennreal_ereal)
  qed
  finally have "(\<integral>\<^sup>+ x. -subcocycle_lim_ereal u x \<partial>M) \<le> - subcocycle_avg_ereal u" by simp
  also have "\<dots> < \<infinity>" using assms(2)
    by (cases "subcocycle_avg_ereal u") (auto simp: e2ennreal_ereal e2ennreal_neg)
  finally have *: "(\<integral>\<^sup>+ x. -subcocycle_lim_ereal u x \<partial>M) < \<infinity>" .
  have "AE x in M. e2ennreal (- subcocycle_lim_ereal u x) \<noteq> \<infinity>"
    apply (rule nn_integral_PInf_AE) using * by auto
  then have **: "AE x in M. - subcocycle_lim_ereal u x \<noteq> \<infinity>"
    using AE_1(3) by eventually_elim simp

  {
    fix x assume H: "- subcocycle_lim_ereal u x \<noteq> \<infinity>"
                    "(\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_lim_ereal u x"
                    "- subcocycle_lim_ereal u x \<ge> 0"
    then have 1: "abs(subcocycle_lim_ereal u x) \<noteq> \<infinity>" by auto
    then have 2: "(\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_lim u x" using H(2) unfolding subcocycle_lim_def by auto
    then have 3: "(\<lambda>n. - (u n x / n)) \<longlonglongrightarrow> - subcocycle_lim u x" using tendsto_mult[OF _ 2, of "\<lambda>_. -1", of "-1"] by auto
    have 4: "-subcocycle_lim u x \<ge> 0" using H(3) unfolding subcocycle_lim_def by auto

    have "abs(subcocycle_lim_ereal u x) \<noteq> \<infinity>"
         "(\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_lim u x"
         "(\<lambda>n. - (u n x / n)) \<longlonglongrightarrow> - subcocycle_lim u x"
         "-subcocycle_lim u x \<ge> 0"
      using 1 2 3 4 by auto
  }
  then have AE_2: "AE x in M. abs(subcocycle_lim_ereal u x) \<noteq> \<infinity>"
                  "AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_lim u x"
                  "AE x in M. (\<lambda>n. - (u n x / n)) \<longlonglongrightarrow> - subcocycle_lim u x"
                  "AE x in M. -subcocycle_lim u x \<ge> 0"
    using kingman_theorem_AE_nonergodic_ereal[OF assms(1)] ** AE_1(3) by auto
  then show "AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_lim u x" by simp

  have "(\<integral>\<^sup>+x. abs(subcocycle_lim u x) \<partial>M) = (\<integral>\<^sup>+x. -subcocycle_lim_ereal u x \<partial>M)"
    apply (rule nn_integral_cong_AE)
    using AE_2 unfolding subcocycle_lim_def abs_real_of_ereal
    apply eventually_elim
    by (auto simp: e2ennreal_ereal)
  then have A: "(\<integral>\<^sup>+x. abs(subcocycle_lim u x) \<partial>M) < \<infinity>" using * by auto
  show int_Gr: "integrable M (subcocycle_lim u)"
    apply (rule integrableI_bounded) using A by auto

  have B: "(\<lambda>n. (\<integral>\<^sup>+ x. norm((- u n x /n) - (-subcocycle_lim u x)) \<partial>M)) \<longlonglongrightarrow> 0"
  proof (rule Scheffe_lemma1, auto simp add: int_Gr int_u AE_2(2) AE_2(3))
    {
      fix n assume "n>(0::nat)"
      have *: "AE x in M. subcocycle_lim u x \<le> real_cond_exp M Invariants (\<lambda>x. u n x / n) x"
        using subcocycle_lim_ereal_atmost_uN_invariants[OF assms(1) `n>0`] AE_2(1)
        unfolding subcocycle_lim_def by auto
      have "(\<integral>x. subcocycle_lim u x \<partial>M) \<le> (\<integral>x. real_cond_exp M Invariants (\<lambda>x. u n x / n) x \<partial>M)"
        apply (rule integral_mono_AE[OF int_Gr _ *], rule real_cond_exp_int(1)) using int_u by auto
      also have "... = (\<integral>x. u n x / n \<partial>M)" apply (rule real_cond_exp_int(2)) using int_u by auto
      finally have A: "(\<integral>x. subcocycle_lim u x \<partial>M) \<le> (\<integral>x. u n x / n \<partial>M)" by auto

      have "(\<integral>\<^sup>+x. abs(u n x) / n \<partial>M) = (\<integral>\<^sup>+x. - u n x / n \<partial>M)"
        apply (rule nn_integral_cong) using F_pos abs_of_nonneg by (intro arg_cong[where f=ennreal]) fastforce
      also have "... = (\<integral>x. - u n x / n \<partial>M)"
        apply (rule nn_integral_eq_integral) using F_pos int_F by auto
      also have "... \<le> (\<integral>x. - subcocycle_lim u x \<partial>M)" using A by (auto intro!: ennreal_leI)
      also have "... = (\<integral>\<^sup>+x. - subcocycle_lim u x \<partial>M)"
        apply (rule nn_integral_eq_integral[symmetric]) using int_Gr AE_2(4) by auto
      also have "... = (\<integral>\<^sup>+x. abs(subcocycle_lim u x) \<partial>M)"
        apply (rule nn_integral_cong_AE) using AE_2(4) by auto
      finally have "(\<integral>\<^sup>+x. abs(u n x) / n \<partial>M) \<le> (\<integral>\<^sup>+x. abs(subcocycle_lim u x) \<partial>M)" by simp
    }
    with eventually_mono[OF eventually_gt_at_top[of 0] this]
    have "eventually (\<lambda>n. (\<integral>\<^sup>+x. abs(u n x) / n \<partial>M) \<le> (\<integral>\<^sup>+x. abs(subcocycle_lim u x) \<partial>M)) sequentially"
      by fastforce
    then show "limsup (\<lambda>n. \<integral>\<^sup>+ x. abs(u n x) / n \<partial>M) \<le> \<integral>\<^sup>+ x. abs(subcocycle_lim u x) \<partial>M"
      using Limsup_eventually_bounded by fastforce
  qed
  moreover have "norm((- u n x /n) - (-subcocycle_lim u x)) = abs(u n x / n - subcocycle_lim u x)"
    for n x by auto
  ultimately show "(\<lambda>n. \<integral>\<^sup>+ x. ennreal \<bar>u n x / real n - subcocycle_lim u x\<bar> \<partial>M) \<longlonglongrightarrow> 0"
    by auto
qed

theorem kingman_theorem_nonergodic:
  assumes "subcocycle u" "subcocycle_avg_ereal u > -\<infinity>"
  shows "AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_lim u x"
        "integrable M (subcocycle_lim u)"
        "(\<lambda>n. (\<integral>\<^sup>+x. abs(u n x / n - subcocycle_lim u x) \<partial>M)) \<longlonglongrightarrow> 0"
proof -
  have [measurable]: "u n \<in> borel_measurable M" for n using assms(1) unfolding subcocycle_def by auto
  have int_u [measurable]: "integrable M (u 1)" using assms(1) subcocycle_def by auto
  define v where "v = (\<lambda>n x. u n x + birkhoff_sum (\<lambda>x. - u 1 x) n x)"
  have [measurable]: "v n \<in> borel_measurable M" for n unfolding v_def by auto
  define w where "w = birkhoff_sum (u 1)"
  have [measurable]: "w n \<in> borel_measurable M" for n unfolding w_def by auto
  have "subcocycle v" unfolding v_def
    apply (rule subcocycle_add[OF assms(1)], rule subcocycle_birkhoff)
    using assms unfolding subcocycle_def by auto
  have "subcocycle w" unfolding w_def by (rule subcocycle_birkhoff[OF int_u])
  have uvw: "u n x = v n x + w n x" for n x
    unfolding v_def w_def birkhoff_sum_def by (auto simp add: setsum_negf)
  then have "subcocycle_avg_ereal (\<lambda>n x. u n x) = subcocycle_avg_ereal v + subcocycle_avg_ereal w"
    using subcocycle_avg_ereal_add[OF `subcocycle v` `subcocycle w`] by auto
  then have "subcocycle_avg_ereal u = subcocycle_avg_ereal v + subcocycle_avg_ereal w"
    by auto
  then have "subcocycle_avg_ereal v > -\<infinity>"
    unfolding w_def using subcocycle_avg_ereal_birkhoff[OF int_u] assms(2) by auto
  have "subcocycle_avg_ereal w > - \<infinity>"
    unfolding w_def using subcocycle_avg_birkhoff[OF int_u] by auto

  have "\<And>x. v 1 x \<le> 0" unfolding v_def by auto
  have v: "AE x in M. (\<lambda>n. v n x / n) \<longlonglongrightarrow> subcocycle_lim v x"
            "integrable M (subcocycle_lim v)"
            "(\<lambda>n. (\<integral>\<^sup>+x. abs(v n x / n - subcocycle_lim v x) \<partial>M)) \<longlonglongrightarrow> 0"
    using kingman_theorem_L1_aux[OF `subcocycle v` `subcocycle_avg_ereal v > -\<infinity>` `\<And>x. v 1 x \<le> 0`] by auto
  have w: "AE x in M. (\<lambda>n. w n x / n) \<longlonglongrightarrow> subcocycle_lim w x"
            "integrable M (subcocycle_lim w)"
            "(\<lambda>n. (\<integral>\<^sup>+x. abs(w n x / n - subcocycle_lim w x) \<partial>M)) \<longlonglongrightarrow> 0"
  proof -
    show "AE x in M. (\<lambda>n. w n x / n) \<longlonglongrightarrow> subcocycle_lim w x"
      unfolding w_def subcocycle_lim_def using subcocycle_lim_ereal_birkhoff[OF int_u]
      birkhoff_theorem_AE_nonergodic[OF int_u] by auto
    show "integrable M (subcocycle_lim w)"
      apply (subst integrable_cong_AE[where ?g= "\<lambda>x. real_cond_exp M Invariants (u 1) x"])
      unfolding w_def subcocycle_lim_def
      using subcocycle_lim_ereal_birkhoff[OF int_u] real_cond_exp_int(1)[OF int_u] by auto
    have "(\<integral>\<^sup>+x. abs(w n x / n - subcocycle_lim w x) \<partial>M)
        = (\<integral>\<^sup>+x. abs(birkhoff_sum (u 1) n x / n - real_cond_exp M Invariants (u 1) x) \<partial>M)" for n
      apply (rule nn_integral_cong_AE)
      unfolding w_def subcocycle_lim_def using subcocycle_lim_ereal_birkhoff[OF int_u] by auto
    then show "(\<lambda>n. (\<integral>\<^sup>+x. abs(w n x / n - subcocycle_lim w x) \<partial>M)) \<longlonglongrightarrow> 0"
      using birkhoff_theorem_L1_nonergodic[OF int_u] by auto
  qed

  {
    fix x assume H: "(\<lambda>n. v n x / n) \<longlonglongrightarrow> subcocycle_lim v x"
                    "(\<lambda>n. w n x / n) \<longlonglongrightarrow> subcocycle_lim w x"
                    "(\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_lim_ereal u x"
    then have "(\<lambda>n. v n x / n + w n x / n) \<longlonglongrightarrow> subcocycle_lim v x + subcocycle_lim w x"
      unfolding H(3) using tendsto_add[OF H(1) H(2)] by simp
    then have *: "(\<lambda>n. ereal(u n x / n)) \<longlonglongrightarrow> ereal(subcocycle_lim v x + subcocycle_lim w x)"
      unfolding uvw by (simp add: add_divide_distrib)
    then have "subcocycle_lim_ereal u x = ereal(subcocycle_lim v x + subcocycle_lim w x)"
      using H(3) LIMSEQ_unique by blast
    then have **: "subcocycle_lim u x = subcocycle_lim v x + subcocycle_lim w x"
      using subcocycle_lim_def by auto
    have "u n x / n - subcocycle_lim u x = v n x / n - subcocycle_lim v x + w n x / n - subcocycle_lim w x" for n
      apply (subst **, subst uvw) using add_divide_distrib add.commute by auto
    then have "(\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_lim u x
          \<and> subcocycle_lim u x = subcocycle_lim v x + subcocycle_lim w x
          \<and> (\<forall>n. u n x / n - subcocycle_lim u x = v n x / n - subcocycle_lim v x + w n x / n - subcocycle_lim w x)"
      using * ** by auto
  }
  then have AE: "AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_lim u x"
                "AE x in M. subcocycle_lim u x = subcocycle_lim v x + subcocycle_lim w x"
                "AE x in M. \<forall>n. u n x / n - subcocycle_lim u x = v n x / n - subcocycle_lim v x + w n x / n - subcocycle_lim w x"
    using v(1) w(1) kingman_theorem_AE_nonergodic_ereal[OF assms(1)] by auto
  then show "AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_lim u x" by simp
  show "integrable M (subcocycle_lim u)"
    apply (subst integrable_cong_AE[where ?g = "\<lambda>x. subcocycle_lim v x + subcocycle_lim w x"])
    by (auto simp add: AE(2) v(2) w(2))

  show "(\<lambda>n. (\<integral>\<^sup>+x. abs(u n x / n - subcocycle_lim u x) \<partial>M)) \<longlonglongrightarrow> 0"
  proof (rule tendsto_sandwich[where ?f = "\<lambda>_. 0"
    and ?h = "\<lambda>n. (\<integral>\<^sup>+x. abs(v n x / n - subcocycle_lim v x) \<partial>M) + (\<integral>\<^sup>+x. abs(w n x / n - subcocycle_lim w x) \<partial>M)"], auto)
    {
      fix n
      have "(\<integral>\<^sup>+x. abs(u n x / n - subcocycle_lim u x) \<partial>M)
        = (\<integral>\<^sup>+x. abs((v n x / n - subcocycle_lim v x) + (w n x / n - subcocycle_lim w x)) \<partial>M)"
        apply (rule nn_integral_cong_AE) using AE(3) by auto
      also have "... \<le> (\<integral>\<^sup>+x. ennreal(abs(v n x / n - subcocycle_lim v x)) + abs(w n x / n - subcocycle_lim w x) \<partial>M)"
        by (rule nn_integral_mono, auto simp add: ennreal_plus[symmetric] simp del: ennreal_plus)
      also have "... = (\<integral>\<^sup>+x. abs(v n x / n - subcocycle_lim v x) \<partial>M) + (\<integral>\<^sup>+x. abs(w n x / n - subcocycle_lim w x) \<partial>M)"
        by (rule nn_integral_add, auto, measurable)
      finally have "(\<integral>\<^sup>+x. abs(u n x / n - subcocycle_lim u x) \<partial>M)
        \<le> (\<integral>\<^sup>+x. abs(v n x / n - subcocycle_lim v x) \<partial>M) + (\<integral>\<^sup>+x. abs(w n x / n - subcocycle_lim w x) \<partial>M)"
        using tendsto_sandwich by simp
    }
    then show "eventually (\<lambda>n. (\<integral>\<^sup>+x. abs(u n x / n - subcocycle_lim u x) \<partial>M)
        \<le> (\<integral>\<^sup>+x. abs(v n x / n - subcocycle_lim v x) \<partial>M) + (\<integral>\<^sup>+x. abs(w n x / n - subcocycle_lim w x) \<partial>M)) sequentially"
      by auto

    have "(\<lambda>n. (\<integral>\<^sup>+x. abs(v n x / n - subcocycle_lim v x) \<partial>M) + (\<integral>\<^sup>+x. abs(w n x / n - subcocycle_lim w x) \<partial>M))
              \<longlonglongrightarrow> 0 + 0"
      by (rule tendsto_add[OF v(3) w(3)])
    then show "(\<lambda>n. (\<integral>\<^sup>+x. abs(v n x / n - subcocycle_lim v x) \<partial>M) + (\<integral>\<^sup>+x. abs(w n x / n - subcocycle_lim w x) \<partial>M))
              \<longlonglongrightarrow> 0"
      by simp
  qed
qed

lemma subcocycle_lim_avg:
  assumes "subcocycle u" "subcocycle_avg_ereal u > -\<infinity>"
  shows "(\<integral>x. subcocycle_lim u x \<partial>M) = subcocycle_avg u"
proof -
  have H: "(\<lambda>n. (\<integral>\<^sup>+x. norm(u n x / n - subcocycle_lim u x) \<partial>M)) \<longlonglongrightarrow> 0"
          "integrable M (subcocycle_lim u)"
    using kingman_theorem_nonergodic[OF assms] by auto
  have "(\<lambda>n. (\<integral>x. u n x / n \<partial>M)) \<longlonglongrightarrow> (\<integral>x. subcocycle_lim u x \<partial>M)"
    apply (rule tendsto_L1_int[OF _ H(2) H(1)]) using subcocycle_integrable[OF assms(1)] by auto
  then have "(\<lambda>n. (\<integral>x. u n x / n \<partial>M)) \<longlonglongrightarrow> ereal (\<integral>x. subcocycle_lim u x \<partial>M)" by auto
  moreover have "(\<lambda>n. (\<integral>x. u n x / n \<partial>M)) \<longlonglongrightarrow> ereal (subcocycle_avg u)"
    using subcocycle_int_tendsto_avg[OF assms] by auto
  ultimately show ?thesis using LIMSEQ_unique by blast
qed

lemma subcocycle_lim_real_ereal:
  assumes "subcocycle u" "subcocycle_avg_ereal u > -\<infinity>"
  shows "AE x in M. subcocycle_lim_ereal u x = ereal(subcocycle_lim u x)"
proof -
  {
    fix x assume H: "(\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_lim_ereal u x"
                    "(\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_lim u x"
    then have "(\<lambda>n. u n x / n) \<longlonglongrightarrow> ereal(subcocycle_lim u x)" by auto
    then have "subcocycle_lim_ereal u x = ereal(subcocycle_lim u x)"
      using H(1) LIMSEQ_unique by blast
  }
  then show ?thesis
    using kingman_theorem_AE_nonergodic_ereal[OF assms(1)] kingman_theorem_nonergodic(1)[OF assms] by auto
qed

lemma subcocycle_lim_add:
  assumes "subcocycle u" "subcocycle v" "subcocycle_avg_ereal u > -\<infinity>" "subcocycle_avg_ereal v > -\<infinity>"
  shows "subcocycle_avg_ereal (\<lambda>n x. u n x + v n x) > - \<infinity>"
        "AE x in M. subcocycle_lim (\<lambda>n x. u n x + v n x) x = subcocycle_lim u x + subcocycle_lim v x"
proof -
  show *: "subcocycle_avg_ereal (\<lambda>n x. u n x + v n x) > - \<infinity>"
    using subcocycle_avg_add[OF assms(1) assms(2)] assms(3) assms(4) by auto
  have "AE x in M. (\<lambda>n. (u n x + v n x)/n) \<longlonglongrightarrow> subcocycle_lim (\<lambda>n x. u n x + v n x) x"
    by (rule kingman_theorem_nonergodic(1)[OF subcocycle_add[OF assms(1) assms(2)] *])
  moreover have "AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_lim u x"
    by (rule kingman_theorem_nonergodic[OF assms(1) assms(3)])
  moreover have "AE x in M. (\<lambda>n. v n x / n) \<longlonglongrightarrow> subcocycle_lim v x"
    by (rule kingman_theorem_nonergodic[OF assms(2) assms(4)])
  moreover
  {
    fix x assume H: "(\<lambda>n. (u n x + v n x)/n) \<longlonglongrightarrow> subcocycle_lim (\<lambda>n x. u n x + v n x) x"
                    "(\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_lim u x"
                    "(\<lambda>n. v n x / n) \<longlonglongrightarrow> subcocycle_lim v x"
    have "(\<lambda>n. (u n x / n) + (v n x / n)) \<longlonglongrightarrow> subcocycle_lim u x + subcocycle_lim v x"
      by (rule tendsto_add[OF H(2) H(3)])
    moreover have "(u n x / n) + (v n x / n) = (u n x + v n x)/n" for n
      by (simp add: add_divide_distrib)
    ultimately have "(\<lambda>n. (u n x + v n x)/n) \<longlonglongrightarrow> subcocycle_lim u x + subcocycle_lim v x"
      by auto
    then have "subcocycle_lim (\<lambda>n x. u n x + v n x) x = subcocycle_lim u x + subcocycle_lim v x"
      using H(1) by (simp add: LIMSEQ_unique)
  }
  ultimately show "AE x in M. subcocycle_lim (\<lambda>n x. u n x + v n x) x
                    = subcocycle_lim u x + subcocycle_lim v x"
    by auto
qed

lemma subcocycle_lim_cmult:
  assumes "subcocycle u" "subcocycle_avg_ereal u > -\<infinity>" "c\<ge>(0::real)"
  shows "subcocycle_avg_ereal (\<lambda>n x. c * u n x) > - \<infinity>"
        "AE x in M. subcocycle_lim (\<lambda>n x. c * u n x) x = c * subcocycle_lim u x"
proof -
  show *: "subcocycle_avg_ereal (\<lambda>n x. c * u n x) > - \<infinity>"
    using subcocycle_avg_cmult[OF assms(1) assms(3)] assms(2) assms(3) by auto

  have "AE x in M. (\<lambda>n. (c * u n x)/n) \<longlonglongrightarrow> subcocycle_lim (\<lambda>n x. c * u n x) x"
    by (rule kingman_theorem_nonergodic(1)[OF subcocycle_cmult[OF assms(1) assms(3)] *])
  moreover have "AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_lim u x"
    by (rule kingman_theorem_nonergodic(1)[OF assms(1) assms(2)])
  moreover
  {
    fix x assume H: "(\<lambda>n. (c * u n x)/n) \<longlonglongrightarrow> subcocycle_lim (\<lambda>n x. c * u n x) x"
                    "(\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_lim u x"
    have "(\<lambda>n. c * (u n x / n)) \<longlonglongrightarrow> c * subcocycle_lim u x"
      by (rule tendsto_mult[OF _ H(2)], auto)
    then have "subcocycle_lim (\<lambda>n x. c * u n x) x = c * subcocycle_lim u x"
      using H(1) by (simp add: LIMSEQ_unique)
  }
  ultimately show "AE x in M. subcocycle_lim (\<lambda>n x. c * u n x) x = c * subcocycle_lim u x" by auto
qed

lemma subcocycle_lim_max:
  assumes "subcocycle u" "subcocycle v" "subcocycle_avg_ereal u > -\<infinity>" "subcocycle_avg_ereal v > -\<infinity>"
  shows "subcocycle_avg_ereal (\<lambda>n x. max (u n x) (v n x)) > - \<infinity>"
        "AE x in M. subcocycle_lim (\<lambda>n x. max (u n x) (v n x)) x = max (subcocycle_lim u x) (subcocycle_lim v x)"
proof -
  show *: "subcocycle_avg_ereal (\<lambda>n x. max (u n x) (v n x)) > - \<infinity>"
    using subcocycle_avg_max(1)[OF assms(1) assms(2)] assms(3) assms(4) by auto
  have "AE x in M. (\<lambda>n. max (u n x) (v n x) / n) \<longlonglongrightarrow> subcocycle_lim (\<lambda>n x. max (u n x) (v n x)) x"
    by (rule kingman_theorem_nonergodic[OF subcocycle_max[OF assms(1) assms(2)] *])
  moreover have "AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_lim u x"
    by (rule kingman_theorem_nonergodic[OF assms(1) assms(3)])
  moreover have "AE x in M. (\<lambda>n. v n x / n) \<longlonglongrightarrow> subcocycle_lim v x"
    by (rule kingman_theorem_nonergodic[OF assms(2) assms(4)])
  moreover
  {
    fix x assume H: "(\<lambda>n. max (u n x) (v n x) / n) \<longlonglongrightarrow> subcocycle_lim (\<lambda>n x. max (u n x) (v n x)) x"
                    "(\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_lim u x"
                    "(\<lambda>n. v n x / n) \<longlonglongrightarrow> subcocycle_lim v x"
    have "(\<lambda>n. max (u n x / n) (v n x / n)) \<longlonglongrightarrow> max (subcocycle_lim u x) (subcocycle_lim v x)"
      apply (rule tendsto_max) using H by auto
    moreover have "max (u n x / n) (v n x / n) = max (u n x) (v n x) / n" for n
      by (simp add: max_divide_distrib_right)
    ultimately have "(\<lambda>n. max (u n x) (v n x) / n) \<longlonglongrightarrow> max (subcocycle_lim u x) (subcocycle_lim v x)"
      by auto
    then have " subcocycle_lim (\<lambda>n x. max (u n x) (v n x)) x = max (subcocycle_lim u x) (subcocycle_lim v x)"
      using H(1) by (simp add: LIMSEQ_unique)
  }
  ultimately show "AE x in M. subcocycle_lim (\<lambda>n x. max (u n x) (v n x)) x
                    = max (subcocycle_lim u x) (subcocycle_lim v x)" by auto
qed

lemma subcocycle_lim_birkhoff:
  assumes "integrable M u"
  shows "subcocycle_avg_ereal (birkhoff_sum u) > -\<infinity>"
        "AE x in M. subcocycle_lim (birkhoff_sum u) x = real_cond_exp M Invariants u x"
proof -
  show *: "subcocycle_avg_ereal (birkhoff_sum u) > -\<infinity>"
    using subcocycle_avg_birkhoff[OF assms] by auto
  have "AE x in M. (\<lambda>n. birkhoff_sum u n x / n) \<longlonglongrightarrow> real_cond_exp M Invariants u x"
    by (rule birkhoff_theorem_AE_nonergodic[OF assms])
  moreover have "AE x in M. (\<lambda>n. birkhoff_sum u n x / n) \<longlonglongrightarrow> subcocycle_lim (birkhoff_sum u) x"
    by (rule kingman_theorem_nonergodic(1)[OF subcocycle_birkhoff[OF assms] *])
  moreover
  {
    fix x assume H: "(\<lambda>n. birkhoff_sum u n x / n) \<longlonglongrightarrow> real_cond_exp M Invariants u x"
                    "(\<lambda>n. birkhoff_sum u n x / n) \<longlonglongrightarrow> subcocycle_lim (birkhoff_sum u) x"
    then have "subcocycle_lim (birkhoff_sum u) x = real_cond_exp M Invariants u x"
      using H(2) by (simp add: LIMSEQ_unique)
  }
  ultimately show "AE x in M. subcocycle_lim (birkhoff_sum u) x = real_cond_exp M Invariants u x" by auto
qed

subsection {*Conditional expectations of subcocycles*}

text {*In this subsection, we show that the conditional expectations of a subcocycle
(with respect to the invariant subalgebra) also converge, with the same limit as the
cocycle.

Note that the conditional expectation of a subcocycle $u$ is still a subcocycle, with the
same average at each step so with the same asymptotic average. Kingman theorem can be applied to
it, and what we have to show is that the limit of this subcocycle is the same as the limit
of the original subcocycle.

When the asymptotic average is $>-\infty$, both limits have the same integral, and moreover
the domination of the subcocycle by the Birkhoff sums of $u_n$ for fixed $n$
(which converge to the conditional expectation of $u_n$) implies that one limit is smaller than
the other. Hence, they coincide almost everywhere.

The case when the asymptotic average is $-\infty$ is deduced from the previous one by truncation.
*}

theorem kingman_theorem_nonergodic_invariant:
  assumes "subcocycle u" "subcocycle_avg_ereal u > -\<infinity>"
  shows "AE x in M. (\<lambda>n. real_cond_exp M Invariants (u n) x / n) \<longlonglongrightarrow> subcocycle_lim u x"
        "(\<lambda>n. (\<integral>\<^sup>+x. abs(real_cond_exp M Invariants (u n) x / n - subcocycle_lim u x) \<partial>M)) \<longlonglongrightarrow> 0"
proof -
  have int [simp]: "integrable M (u n)" for n using subcocycle_integrable[OF assms(1)] by auto
  then have int2: "integrable M (real_cond_exp M Invariants (u n))" for n using real_cond_exp_int by auto
  {
    fix n m
    have "u (n+m) x \<le> u n x + u m ((T^^n) x)" for x
      using subcocycle_ineq[OF assms(1)] by auto
    have "AE x in M. real_cond_exp M Invariants (u (n+m)) x \<le> real_cond_exp M Invariants (\<lambda>x. u n x + u m ((T^^n) x)) x"
      apply (rule real_cond_exp_mono)
      using subcocycle_ineq[OF assms(1)] apply auto
      by (rule Bochner_Integration.integrable_add, auto simp add: Tn_integral_preserving)
    moreover have "AE x in M. real_cond_exp M Invariants (u n) x + real_cond_exp M Invariants (\<lambda>x. u m ((T^^n) x)) x
                    = real_cond_exp M Invariants (\<lambda>x. u n x + u m ((T^^n) x)) x"
      by (rule real_cond_exp_add, auto simp add: Tn_integral_preserving)
    moreover have "AE x in M. real_cond_exp M Invariants (u m) x = real_cond_exp M Invariants (u m \<circ> ((T^^n))) x"
      by (rule Invariants_of_foTn, simp)
    moreover have "AE x in M. real_cond_exp M Invariants (u m) x = real_cond_exp M Invariants (u m) ((T^^n) x)"
      using Invariants_func_is_invariant_n[symmetric, of "real_cond_exp M Invariants (u m)"] by auto
    ultimately have "AE x in M. real_cond_exp M Invariants (u (n+m)) x
        \<le> real_cond_exp M Invariants (u n) x + real_cond_exp M Invariants (u m) ((T^^n) x)"
      unfolding o_def by auto
  }
  with subcocycle_AE[OF this int2]
  obtain w where w: "subcocycle w" "AE x in M. \<forall>n. w n x = real_cond_exp M Invariants (u n) x"
    by blast
  have [measurable]: "integrable M (w n)" for n using subcocycle_integrable[OF w(1)] by simp

  {
    fix n::nat
    have "(\<integral>x. w n x / n \<partial>M) = (\<integral>x. real_cond_exp M Invariants (u n) x / n \<partial>M)"
      apply (rule integral_cong_AE) using w(2) by auto
    also have "... = (\<integral>x. real_cond_exp M Invariants (u n) x \<partial>M) / n"
      by (rule integral_divide_zero)
    also have "... = (\<integral>x. u n x \<partial>M) / n"
      by (simp add: divide_simps real_cond_exp_int(2)[OF int[of n]])
    also have "... = (\<integral>x. u n x / n \<partial>M)"
      by (rule integral_divide_zero[symmetric])
    finally have "ereal (\<integral>x. w n x / n \<partial>M) = ereal (\<integral>x. u n x / n \<partial>M)" by simp
  } note * = this
  have "(\<lambda>n. (\<integral>x. u n x / n \<partial>M)) \<longlonglongrightarrow> subcocycle_avg_ereal w"
    apply (rule Lim_transform_eventually[OF _ subcocycle_int_tendsto_avg_ereal[OF w(1)]])
    using * by auto
  then have "subcocycle_avg_ereal u = subcocycle_avg_ereal w"
    using subcocycle_int_tendsto_avg_ereal[OF assms(1)] LIMSEQ_unique by auto
  then have "subcocycle_avg_ereal w > -\<infinity>" using assms(2) by simp
  have "subcocycle_avg u = subcocycle_avg w"
    using `subcocycle_avg_ereal u = subcocycle_avg_ereal w` unfolding subcocycle_avg_def by simp

  have *: "AE x in M. N > 0 \<longrightarrow> subcocycle_lim_ereal u x \<le> real_cond_exp M Invariants (\<lambda>x. u N x / N) x" for N
    by (cases "N=0", auto simp add: subcocycle_lim_ereal_atmost_uN_invariants[OF assms(1)])
  have "AE x in M. \<forall>N. N > 0 \<longrightarrow> subcocycle_lim_ereal u x \<le> real_cond_exp M Invariants (\<lambda>x. u N x / N) x"
    by (subst AE_all_countable, intro allI, simp add: *)
  moreover have "AE x in M. subcocycle_lim_ereal u x = ereal(subcocycle_lim u x)"
    by (rule subcocycle_lim_real_ereal[OF assms])
  moreover have "AE x in M. (\<lambda>N. u N x / N) \<longlonglongrightarrow> subcocycle_lim u x"
    using kingman_theorem_nonergodic[OF assms] by simp
  moreover have "AE x in M. (\<lambda>N. w N x / N) \<longlonglongrightarrow> subcocycle_lim w x"
    using kingman_theorem_nonergodic[OF w(1) `subcocycle_avg_ereal w > -\<infinity>` ] by simp
  moreover have "AE x in M. \<forall>n. w n x = real_cond_exp M Invariants (u n) x"
    using w(2) by simp
  moreover have "AE x in M. \<forall>n. real_cond_exp M Invariants (u n) x / n = real_cond_exp M Invariants (\<lambda>x. u n x / n) x"
    apply (subst AE_all_countable, intro allI) using real_cond_exp_cdiv[OF int] by auto
  moreover
  {
    fix x assume x: "\<forall>N. N > 0 \<longrightarrow> subcocycle_lim_ereal u x \<le> real_cond_exp M Invariants (\<lambda>x. u N x / N) x"
                    "subcocycle_lim_ereal u x = ereal(subcocycle_lim u x)"
                    "(\<lambda>N. u N x / N) \<longlonglongrightarrow> subcocycle_lim u x"
                    "(\<lambda>N. w N x / N) \<longlonglongrightarrow> subcocycle_lim w x"
                    "\<forall>n. w n x = real_cond_exp M Invariants (u n) x"
                    "\<forall>n. real_cond_exp M Invariants (u n) x / n = real_cond_exp M Invariants (\<lambda>x. u n x / n) x"
    {
      fix N::nat assume "N\<ge>1"
      have "subcocycle_lim u x \<le> real_cond_exp M Invariants (\<lambda>x. u N x / N) x"
        using x(1) x(2) `N\<ge>1` by auto
      also have "... = real_cond_exp M Invariants (u N) x / N"
        using x(6) by simp
      also have "... = w N x / N"
        using x(5) by simp
      finally have "subcocycle_lim u x \<le> w N x / N"
        by simp
    } note * = this
    have "subcocycle_lim u x \<le> subcocycle_lim w x"
      apply (rule LIMSEQ_le_const[OF x(4)]) using * by auto
  }
  ultimately have *: "AE x in M. subcocycle_lim u x \<le> subcocycle_lim w x"
    by auto
  have **: "(\<integral>x. subcocycle_lim u x \<partial>M) = (\<integral>x. subcocycle_lim w x \<partial>M)"
    using subcocycle_lim_avg[OF assms] subcocycle_lim_avg[OF w(1) `subcocycle_avg_ereal w > -\<infinity>`]
            `subcocycle_avg u = subcocycle_avg w` by simp
  have AE_eq: "AE x in M. subcocycle_lim u x = subcocycle_lim w x"
    by (rule integral_ineq_eq_0_then_AE[OF * kingman_theorem_nonergodic(2)[OF assms]
        kingman_theorem_nonergodic(2)[OF w(1) `subcocycle_avg_ereal w > -\<infinity>`] **])
  moreover have "AE x in M. (\<lambda>n. w n x / n) \<longlonglongrightarrow> subcocycle_lim w x"
    by (rule kingman_theorem_nonergodic(1)[OF w(1) `subcocycle_avg_ereal w > -\<infinity>`])
  moreover have "AE x in M. \<forall>n. w n x = real_cond_exp M Invariants (u n) x"
    using w(2) by auto
  moreover
  {
    fix x assume H: "subcocycle_lim u x = subcocycle_lim w x"
                    "(\<lambda>n. w n x / n) \<longlonglongrightarrow> subcocycle_lim w x"
                    "\<forall>n. w n x = real_cond_exp M Invariants (u n) x"
    then have "(\<lambda>n. real_cond_exp M Invariants (u n) x / n) \<longlonglongrightarrow> subcocycle_lim u x"
      by auto
  }
  ultimately show "AE x in M. (\<lambda>n. real_cond_exp M Invariants (u n) x / n) \<longlonglongrightarrow> subcocycle_lim u x"
    by auto

  {
    fix n::nat
    have "AE x in M. subcocycle_lim u x = subcocycle_lim w x"
      using AE_eq by simp
    moreover have "AE x in M. w n x = real_cond_exp M Invariants (u n) x"
      using w(2) by auto
    moreover
    {
      fix x assume H: "subcocycle_lim u x = subcocycle_lim w x"
                    "w n x = real_cond_exp M Invariants (u n) x"
      then have "ennreal \<bar>real_cond_exp M Invariants (u n) x / real n - subcocycle_lim u x\<bar>
                = ennreal \<bar>w n x / real n - subcocycle_lim w x\<bar>"
      by auto
    }
    ultimately have "AE x in M. ennreal \<bar>real_cond_exp M Invariants (u n) x / real n - subcocycle_lim u x\<bar>
        = ennreal \<bar>w n x / real n - subcocycle_lim w x\<bar>"
      by auto
    then have "(\<integral>\<^sup>+ x. ennreal \<bar>real_cond_exp M Invariants (u n) x / real n - subcocycle_lim u x\<bar> \<partial>M)
              = (\<integral>\<^sup>+ x. ennreal \<bar>w n x / real n - subcocycle_lim w x\<bar> \<partial>M)"
      by (rule nn_integral_cong_AE)
  }
  moreover have "(\<lambda>n. (\<integral>\<^sup>+ x. \<bar>w n x / real n - subcocycle_lim w x\<bar> \<partial>M)) \<longlonglongrightarrow> 0"
    by (rule kingman_theorem_nonergodic(3)[OF w(1) `subcocycle_avg_ereal w > -\<infinity>`])
  ultimately show "(\<lambda>n. (\<integral>\<^sup>+ x. \<bar>real_cond_exp M Invariants (u n) x / real n - subcocycle_lim u x\<bar> \<partial>M)) \<longlonglongrightarrow> 0"
    by auto
qed

theorem kingman_theorem_AE_nonergodic_invariant_ereal:
  assumes "subcocycle u"
  shows "AE x in M. (\<lambda>n. real_cond_exp M Invariants (u n) x / n) \<longlonglongrightarrow> subcocycle_lim_ereal u x"
proof -
  have [simp]: "subcocycle u" using assms by simp
  have int [simp]: "integrable M (u n)" for n using subcocycle_integrable[OF assms(1)] by auto

  have limsup_ineq_K: "AE x in M.
    limsup (\<lambda>n. real_cond_exp M Invariants (u n) x / n) \<le> max (subcocycle_lim_ereal u x) (-real K)" for K::nat
  proof -
    define v where "v =(\<lambda> (n::nat) (x::'a). (-n * real K))"
    have [simp]: "subcocycle v"
      unfolding v_def subcocycle_def by (auto simp add: algebra_simps)
    have "ereal (\<integral>x. v n x / n \<partial>M) = ereal(- real K * measure M (space M))" if "n\<ge>1" for n
      unfolding v_def using that by simp
    then have "(\<lambda>n. ereal (\<integral>x. v n x / n \<partial>M)) \<longlonglongrightarrow> ereal(- real K * measure M (space M))"
      using tendsto_explicit by force
    moreover have "(\<lambda>n. ereal (\<integral>x. v n x / n \<partial>M)) \<longlonglongrightarrow> subcocycle_avg_ereal v"
      using subcocycle_int_tendsto_avg_ereal[OF `subcocycle v`] by auto
    ultimately have "subcocycle_avg_ereal v = - real K * measure M (space M)"
      using LIMSEQ_unique by blast
    then have "subcocycle_avg_ereal v > -\<infinity>"
      by auto

    {
      fix x assume H: "(\<lambda>n. v n x / n) \<longlonglongrightarrow> subcocycle_lim_ereal v x"
      have "ereal(v n x / n) = -real K" if "n\<ge>1" for n
        unfolding v_def using that by auto
      then have "(\<lambda>n. ereal(v n x / n)) \<longlonglongrightarrow> - real K"
        using tendsto_explicit by force
      then have "subcocycle_lim_ereal v x = -real K"
        using H LIMSEQ_unique by blast
    }
    then have "AE x in M. subcocycle_lim_ereal v x = -real K"
      using kingman_theorem_AE_nonergodic_ereal[OF `subcocycle v`] by auto

    define w where "w = (\<lambda>n x. max (u n x) (v n x))"
    have [simp]: "subcocycle w"
      unfolding w_def by (rule subcocycle_max, auto)
    have "subcocycle_avg_ereal w \<ge> subcocycle_avg_ereal v"
      unfolding w_def using subcocycle_avg_ereal_max by auto
    then have "subcocycle_avg_ereal w > -\<infinity>"
      using `subcocycle_avg_ereal v > -\<infinity>` by auto

    have *: "AE x in M. real_cond_exp M Invariants (u n) x \<le> real_cond_exp M Invariants (w n) x" for n
      apply (rule real_cond_exp_mono)
      using subcocycle_integrable[OF assms, of n] subcocycle_integrable[OF `subcocycle w`, of n] apply auto
      unfolding w_def by auto
    have "AE x in M. \<forall>n. real_cond_exp M Invariants (u n) x \<le> real_cond_exp M Invariants (w n) x"
      apply (subst AE_all_countable) using * by auto
    moreover have "AE x in M. (\<lambda>n. real_cond_exp M Invariants (w n) x / n) \<longlonglongrightarrow> subcocycle_lim w x"
      apply (rule kingman_theorem_nonergodic_invariant(1))
      using `subcocycle_avg_ereal w > -\<infinity>` by auto
    moreover have "AE x in M. subcocycle_lim_ereal w x = max (subcocycle_lim_ereal u x) (subcocycle_lim_ereal v x)"
      unfolding w_def using subcocycle_lim_ereal_max by auto
    moreover
    {
      fix x assume H: "(\<lambda>n. real_cond_exp M Invariants (w n) x / n) \<longlonglongrightarrow> subcocycle_lim w x"
                      "subcocycle_lim_ereal w x = max (subcocycle_lim_ereal u x) (subcocycle_lim_ereal v x)"
                      "subcocycle_lim_ereal v x = - real K"
                      "\<forall>n. real_cond_exp M Invariants (u n) x \<le> real_cond_exp M Invariants (w n) x"
      have "subcocycle_lim_ereal w x > -\<infinity>"
        using H(2) H(3) MInfty_neq_ereal(1) ereal_MInfty_lessI max.cobounded2 by fastforce
      then have "subcocycle_lim_ereal w x = ereal(subcocycle_lim w x)"
        unfolding subcocycle_lim_def using subcocycle_lim_ereal_not_PInf[of w x] ereal_real by force
      moreover have "(\<lambda>n. real_cond_exp M Invariants (w n) x / n) \<longlonglongrightarrow> ereal(subcocycle_lim w x)" using H(1) by auto
      ultimately have "(\<lambda>n. real_cond_exp M Invariants (w n) x / n) \<longlonglongrightarrow> subcocycle_lim_ereal w x" by auto
      then have *: "limsup (\<lambda>n. real_cond_exp M Invariants (w n) x / n) = subcocycle_lim_ereal w x"
        using tendsto_iff_Liminf_eq_Limsup trivial_limit_at_top_linorder by blast

      have "ereal(real_cond_exp M Invariants (u n) x / n) \<le> real_cond_exp M Invariants (w n) x / n" for n
        using H(4) by (auto simp add: divide_simps)
      then have "eventually (\<lambda>n. ereal(real_cond_exp M Invariants (u n) x / n) \<le> real_cond_exp M Invariants (w n) x / n) sequentially"
        by auto
      then have "limsup (\<lambda>n. real_cond_exp M Invariants (u n) x / n) \<le> limsup (\<lambda>n. real_cond_exp M Invariants (w n) x / n)"
        using Limsup_mono[of _ _ sequentially] by force
      then have "limsup (\<lambda>n. real_cond_exp M Invariants (u n) x / n) \<le> max (subcocycle_lim_ereal u x) (-real K)"
        using * H(2) H(3) by auto
    }
    ultimately show ?thesis using `AE x in M. subcocycle_lim_ereal v x = -real K` by auto
  qed
  have "AE x in M. \<forall>K::nat.
        limsup (\<lambda>n. real_cond_exp M Invariants (u n) x / n) \<le> max (subcocycle_lim_ereal u x) (-real K)"
    apply (subst AE_all_countable) using limsup_ineq_K by auto

  moreover have "AE x in M. liminf (\<lambda>n. real_cond_exp M Invariants (u n) x / n) \<ge> subcocycle_lim_ereal u x"
  proof -
    have *: "AE x in M. N > 0 \<longrightarrow> subcocycle_lim_ereal u x \<le> real_cond_exp M Invariants (\<lambda>x. u N x / N) x" for N
      by (cases "N=0", auto simp add: subcocycle_lim_ereal_atmost_uN_invariants[OF assms(1)])
    have "AE x in M. \<forall>N. N > 0 \<longrightarrow> subcocycle_lim_ereal u x \<le> real_cond_exp M Invariants (\<lambda>x. u N x / N) x"
      by (subst AE_all_countable, intro allI, simp add: *)
    moreover have "AE x in M. \<forall>n. real_cond_exp M Invariants (u n) x / n = real_cond_exp M Invariants (\<lambda>x. u n x / n) x"
      apply (subst AE_all_countable, intro allI) using real_cond_exp_cdiv by auto
    moreover
    {
      fix x assume x: "\<forall>N. N > 0 \<longrightarrow> subcocycle_lim_ereal u x \<le> real_cond_exp M Invariants (\<lambda>x. u N x / N) x"
                      "\<forall>n. real_cond_exp M Invariants (u n) x / n = real_cond_exp M Invariants (\<lambda>x. u n x / n) x"
      then have *: "subcocycle_lim_ereal u x \<le> real_cond_exp M Invariants (u n) x / n" if "n \<ge> 1" for n
        using that by auto
      have "subcocycle_lim_ereal u x \<le> liminf (\<lambda>n. real_cond_exp M Invariants (u n) x / n)"
        apply (subst liminf_bounded_iff) using * less_le_trans by blast
    }
    ultimately show ?thesis by auto
  qed

  moreover
  {
    fix x assume H: "\<forall>K::nat. limsup (\<lambda>n. real_cond_exp M Invariants (u n) x / n)
                              \<le> max (subcocycle_lim_ereal u x) (-real K)"
                    "liminf (\<lambda>n. real_cond_exp M Invariants (u n) x / n) \<ge> subcocycle_lim_ereal u x"
    have "(\<lambda>K::nat. max (subcocycle_lim_ereal u x) (-real K)) \<longlonglongrightarrow> subcocycle_lim_ereal u x"
      by (rule ereal_truncation_bottom)
    with LIMSEQ_le_const[OF this]
    have *: "limsup (\<lambda>n. real_cond_exp M Invariants (u n) x / n) \<le> subcocycle_lim_ereal u x"
      using H(1) by auto
    have "(\<lambda>n. real_cond_exp M Invariants (u n) x / n) \<longlonglongrightarrow> subcocycle_lim_ereal u x"
      apply (subst tendsto_iff_Liminf_eq_Limsup[OF trivial_limit_at_top_linorder])
      using H(2) * Liminf_le_Limsup[OF trivial_limit_at_top_linorder, of "(\<lambda>n. real_cond_exp M Invariants (u n) x / n)"]
      by auto
  }
  ultimately show ?thesis by auto
qed



end

subsection {*Subcocycles in the ergodic case*}

context ergodic_pmpt begin

lemma subcocycle_ergodic_lim_avg:
  assumes "subcocycle u"
  shows "AE x in M. subcocycle_lim_ereal u x = subcocycle_avg_ereal u"
        "AE x in M. subcocycle_lim u x = subcocycle_avg u"
proof -
  have I: "integrable M (u N)" for N using subcocycle_integrable[OF assms]by auto
  obtain c::ereal where c: "AE x in M. subcocycle_lim_ereal u x = c"
    using Invariant_func_is_AE_constant[OF subcocycle_lim_meas_Inv(1)] by blast
  have "c = subcocycle_avg_ereal u"
  proof (cases "subcocycle_avg_ereal u = - \<infinity>")
    case True
    {
      fix N assume "N > (0::nat)"
      have "AE x in M. real_cond_exp M Invariants (\<lambda>x. u N x / N) x = (\<integral> x. u N x / N \<partial>M)"
        apply (rule Invariants_cond_exp_is_integral) using I by auto
      moreover have "AE x in M. subcocycle_lim_ereal u x \<le> real_cond_exp M Invariants (\<lambda>x. u N x / N) x"
        using subcocycle_lim_ereal_atmost_uN_invariants[OF assms `N>0`] by simp
      ultimately have "AE x in M. c \<le> (\<integral>x. u N x / N \<partial>M)"
        using c by force
      then have "c \<le> (\<integral>x. u N x / N \<partial>M)" by auto
    }
    then have "\<forall>N\<ge>1. c \<le> (\<integral>x. u N x / N \<partial>M)" by auto
    with Lim_bounded2_ereal[OF subcocycle_int_tendsto_avg_ereal[OF assms] this]
    have "c \<le> subcocycle_avg_ereal u" by simp
    then show ?thesis using True by auto
  next
    case False
    then have fin: "subcocycle_avg_ereal u > - \<infinity>" by simp
    obtain cr::real where cr: "AE x in M. subcocycle_lim u x = cr"
      using Invariant_func_is_AE_constant[OF subcocycle_lim_meas_Inv(2)] by blast
    have "AE x in M. c = ereal cr" using c cr subcocycle_lim_real_ereal[OF assms fin] by force
    then have "c = ereal cr" by auto
    have "subcocycle_avg u = (\<integral>x. subcocycle_lim u x \<partial>M)"
      using subcocycle_lim_avg[OF assms fin] by auto
    also have "... = (\<integral>x. cr \<partial>M)"
      apply (rule integral_cong_AE) using cr by auto
    also have "... = cr"
      by (simp add: prob_space.prob_space prob_space_axioms)
    finally have "ereal(subcocycle_avg u) = ereal cr" by simp
    then show ?thesis using \<open> c = ereal cr \<close> subcocycle_avg_real_ereal[OF fin] by auto
  qed
  then show "AE x in M. subcocycle_lim_ereal u x = subcocycle_avg_ereal u" using c by auto
  then show "AE x in M. subcocycle_lim u x = subcocycle_avg u"
    unfolding subcocycle_lim_def subcocycle_avg_def by auto
qed

theorem kingman_theorem_AE_ereal:
  assumes "subcocycle u"
  shows "AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_avg_ereal u"
using kingman_theorem_AE_nonergodic_ereal[OF assms] subcocycle_ergodic_lim_avg(1)[OF assms] by auto

theorem kingman_theorem:
  assumes "subcocycle u" "subcocycle_avg_ereal u > -\<infinity>"
  shows "AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_avg u"
        "(\<lambda>n. (\<integral>\<^sup>+x. abs(u n x / n - subcocycle_avg u) \<partial>M)) \<longlonglongrightarrow> 0"
proof -
  have *: "AE x in M. subcocycle_lim u x = subcocycle_avg u"
    using subcocycle_ergodic_lim_avg(2)[OF assms(1)] by auto
  then show "AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_avg u"
    using kingman_theorem_nonergodic(1)[OF assms] by auto
  have "(\<integral>\<^sup>+x. abs(u n x / n - subcocycle_avg u) \<partial>M) = (\<integral>\<^sup>+x. abs(u n x / n - subcocycle_lim u x) \<partial>M)" for n
    apply (rule nn_integral_cong_AE) using * by auto
  then show "(\<lambda>n. (\<integral>\<^sup>+x. abs(u n x / n - subcocycle_avg u) \<partial>M)) \<longlonglongrightarrow> 0"
    using kingman_theorem_nonergodic(3)[OF assms] by auto
qed

end


subsection {*Subocycles for invertible maps*}

text {*If $T$ is invertible, then a subcocycle $u_n$ for $T$ gives rise to another subcocycle
for $T^{-1}$. Intuitively, if $u$ is subadditive along the time interval $[0,n)$, then
it should also be subadditive along the time interval $[-n,0)$. This is true, and
formalized with the following statement.*}

proposition (in mpt) subcocycle_u_Tinv:
  assumes "subcocycle u"
          "invertible_qmpt"
  shows "mpt.subcocycle M Tinv (\<lambda>n x. u n (((Tinv)^^n) x))"
proof -
  have bij: "bij T" using `invertible_qmpt` unfolding invertible_qmpt_def by auto
  have int: "integrable M (u n)" for n
    using subcocycle_integrable[OF assms(1)] by simp
  interpret I: mpt M Tinv using Tinv_mpt[OF assms(2)] by simp
  show "I.subcocycle (\<lambda>n x. u n (((Tinv)^^n) x))" unfolding I.subcocycle_def
  proof(auto)
    show "integrable M (\<lambda>x. u n ((Tinv ^^ n) x))" for n
      using I.Tn_integral_preserving(1)[OF int[of n]] by simp
    fix n m::nat and x::'a
    define y where "y = (Tinv^^(m+n)) x"
    have "(T^^m) y = (T^^m) ((Tinv^^m) ((Tinv^^n) x))" unfolding y_def by (simp add: funpow_add)
    then have *: "(T^^m) y = (Tinv^^n) x"
      using fn_o_inv_fn_is_id[OF bij, of m] by (metis Tinv_def comp_def)
    have "u (n + m) ((Tinv ^^ (n + m)) x) = u (m+n) y"
      unfolding y_def by (simp add: add.commute[of n m])
    also have "... \<le> u m y + u n ((T^^m) y)"
      using subcocycle_ineq[OF `subcocycle u`, of m n y] by simp
    also have "... = u m ((Tinv^^(m+n)) x) + u n ((Tinv^^n) x)"
      using * y_def by auto
    finally show "u (n + m) ((Tinv ^^ (n + m)) x) \<le> u n ((Tinv ^^ n) x) + u m ((Tinv ^^ m) ((Tinv ^^ n) x))"
      by (simp add: funpow_add)
  qed
qed

proposition (in mpt) subcocycle_avg_ereal_Tinv:
  assumes "subcocycle u"
          "invertible_qmpt"
  shows "mpt.subcocycle_avg_ereal M (\<lambda>n x. u n (((Tinv)^^n) x)) = subcocycle_avg_ereal u"
proof -
  have bij: "bij T" using `invertible_qmpt` unfolding invertible_qmpt_def by auto
  have int: "integrable M (u n)" for n
    using subcocycle_integrable[OF assms(1)] by simp
  interpret I: mpt M Tinv using Tinv_mpt[OF assms(2)] by simp
  have "(\<lambda>n. (\<integral>x. u n (((Tinv)^^n) x) / n \<partial>M)) \<longlonglongrightarrow> I.subcocycle_avg_ereal (\<lambda>n x. u n (((Tinv)^^n) x))"
    using I.subcocycle_int_tendsto_avg_ereal[OF subcocycle_u_Tinv[OF assms]] by simp
  moreover have "(\<integral>x. u n x / n \<partial>M) = ereal (\<integral>x. u n (((Tinv)^^n) x) / n \<partial>M)" for n
    apply (simp)
    apply (rule disjI2)
    apply (rule I.Tn_integral_preserving(2)[symmetric])
    apply (simp add: int)
    done
  ultimately have "(\<lambda>n. (\<integral>x. u n x / n \<partial>M)) \<longlonglongrightarrow> I.subcocycle_avg_ereal (\<lambda>n x. u n (((Tinv)^^n) x))"
    by presburger
  moreover have "(\<lambda>n. (\<integral>x. u n x / n \<partial>M)) \<longlonglongrightarrow> subcocycle_avg_ereal u"
    using subcocycle_int_tendsto_avg_ereal[OF `subcocycle u`] by simp
  ultimately show ?thesis
    using LIMSEQ_unique by simp
qed

text {*The asymptotic limit of the subcocycle is the same for $T$ and $T^{-1}$. This is clear
in the ergodic case, and follows from the ergodic decomposition in the general case. We
give a direct proof below using the fact that the asymptotic limit is the same for
the subcocycle conditioned by the invariant sigma-algebra, which is clearly the same for
$T$ and $T^{-1}$ as it is constant along orbits.*}

proposition (in fmpt) subcocycle_lim_ereal_Tinv:
  assumes "subcocycle u"
          "invertible_qmpt"
  shows "AE x in M. fmpt.subcocycle_lim_ereal M Tinv (\<lambda>n x. u n (((Tinv)^^n) x)) x = subcocycle_lim_ereal u x"
proof -
  have bij: "bij T" using `invertible_qmpt` unfolding invertible_qmpt_def by auto
  have int: "integrable M (u n)" for n
    using subcocycle_integrable[OF assms(1)] by simp
  interpret I: fmpt M Tinv using Tinv_fmpt[OF assms(2)] by simp
  have *: "AE x in M. real_cond_exp M I.Invariants (u n) x
                    = real_cond_exp M I.Invariants (\<lambda> x. u n (((Tinv)^^n) x)) x" for n
    using I.Invariants_of_foTn int unfolding o_def by simp
  have "AE x in M. \<forall>n. real_cond_exp M I.Invariants (u n) x
                    = real_cond_exp M I.Invariants (\<lambda> x. u n (((Tinv)^^n) x)) x"
    apply (subst AE_all_countable) using * by simp
  moreover have "AE x in M. (\<lambda>n. real_cond_exp M Invariants (u n) x / n) \<longlonglongrightarrow> subcocycle_lim_ereal u x"
    using kingman_theorem_AE_nonergodic_invariant_ereal[OF `subcocycle u`] by simp
  moreover have "AE x in M. (\<lambda>n. real_cond_exp M I.Invariants (\<lambda> x. u n (((Tinv)^^n) x)) x / n)
          \<longlonglongrightarrow> I.subcocycle_lim_ereal (\<lambda> n x. u n (((Tinv)^^n) x)) x"
    using I.kingman_theorem_AE_nonergodic_invariant_ereal[OF subcocycle_u_Tinv[OF assms]] by simp
  moreover
  {
    fix x assume H: "\<forall>n. real_cond_exp M I.Invariants (u n) x
                      = real_cond_exp M I.Invariants (\<lambda> x. u n (((Tinv)^^n) x)) x"
                    "(\<lambda>n. real_cond_exp M Invariants (u n) x / n) \<longlonglongrightarrow> subcocycle_lim_ereal u x"
                    "(\<lambda>n. real_cond_exp M I.Invariants (\<lambda> x. u n (((Tinv)^^n) x)) x / n)
                        \<longlonglongrightarrow> I.subcocycle_lim_ereal (\<lambda> n x. u n (((Tinv)^^n) x)) x"
    have "ereal(real_cond_exp M Invariants (u n) x / n)
          = ereal(real_cond_exp M I.Invariants (\<lambda> x. u n (((Tinv)^^n) x)) x / n)" for n
      using H(1) Invariants_Tinv[OF `invertible_qmpt`] by auto
    then have "(\<lambda>n. real_cond_exp M Invariants (u n) x / n)
                \<longlonglongrightarrow> I.subcocycle_lim_ereal (\<lambda> n x. u n (((Tinv)^^n) x)) x"
      using H(3) by presburger
    then have "I.subcocycle_lim_ereal (\<lambda> n x. u n (((Tinv)^^n) x)) x = subcocycle_lim_ereal u x"
      using H(2) LIMSEQ_unique by auto
  }
  ultimately show ?thesis by auto
qed

proposition (in fmpt) subcocycle_lim_Tinv:
  assumes "subcocycle u"
          "invertible_qmpt"
  shows "AE x in M. fmpt.subcocycle_lim M Tinv (\<lambda>n x. u n (((Tinv)^^n) x)) x = subcocycle_lim u x"
proof -
  interpret I: fmpt M Tinv using Tinv_fmpt[OF assms(2)] by simp
  show ?thesis
    unfolding subcocycle_lim_def I.subcocycle_lim_def
    using subcocycle_lim_ereal_Tinv[OF assms] by auto
qed


end
