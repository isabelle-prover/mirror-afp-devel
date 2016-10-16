(*  Author:  Sébastien Gouëzel   sebastien.gouezel@univ-rennes1.fr
    License: BSD
*)

theory Gouezel_Karlsson
imports Banach_Density Kingman

begin

lemma one_less_ennreal[simp]: "1 < ennreal x \<longleftrightarrow> 1 < x"
  including ennreal.lifting
  by transfer (auto simp: max.absorb2 less_max_iff_disj)


section {*Gouezel-Karlsson*}

text {*This section is devoted to the proof of the main ergodic result of
the article "Subadditive and multiplicative ergodic theorems" by Gouezel and
Karlsson (denoted [GK] below). It is a version of Kingman
theorem ensuring that, for subadditive cocycles, there are almost surely
many times $n$ where the cocycle is nearly additive at \emph{all} times
between $0$ and $n$.

This theorem is then used in this article to construct horofunctions
characterizing the behavior at infinity of compositions
of semi-contractions. This requires too many further notions to be implemented
in current Isabelle/HOL, but the main ergodic result is completely
proved below, in Theorem~\verb+Gouezel_Karlsson+, following the arguments in the paper (but in a
slightly more general setting here as we are not making any ergodicity assumption).

To simplify the exposition, the theorem is proved assuming that the limit of the subcocycle
vanishes almost everywhere, in the locale \verb+Gouezel_Karlsson_Kingman+.
The final result is proved by an easy reduction to this case.

The main steps of the proof are as follows:
- assume first that the map is invertible, and consider the inverse map and the corresponding
inverse subcocycle. With combinatorial arguments that only work for this inverse subcocycle, we
control the density of bad times given some allowed error $d>0$, in a precise quantitative way, in
Lemmas~\verb+upper_density_all_times+ and~\verb+upper_density_large_k+. We put these estimates
together in Lemma~\verb+upper_density_delta+.
- These estimates are then transfered to the original time direction and the original subcocycle in
Lemma~\verb+upper_density_good_direction_invertible+. The fact that we have quantitative estimates
in terms of Banach densities is central here, just having some infiniteness statement would not be
enough.
- The invertibility assumption is removed in Lemma~\verb+upper_density_good_direction+ by
using the result in the natural extension.
- Finally, the main result is deduced in Lemma~\verb+infinite_AE+ (still assuming that the
asymptotic limit vanishes almost everywhere), and in full generality in
Theorem~\verb+Gouezel_Karlsson_Kingman+.
*}


lemma upper_density_eventually_measure:
  fixes a::real
  assumes [measurable]: "\<And>n. {x \<in> space M. P x n} \<in> sets M"
    and "emeasure M {x \<in> space M. upper_Banach_density {n. P x n} < a} > b"
  shows "\<exists>N. emeasure M {x \<in> space M. \<forall>n \<ge> N. card ({n. P x n} \<inter> {..<n}) < a * n} > b"
proof -
  define G where "G = {x \<in> space M. upper_Banach_density {n. P x n} < a}"
  define H where "H = (\<lambda>N. {x \<in> space M. \<forall>n \<ge> N. card ({n. P x n} \<inter> {..<n}) < a * n})"
  have [measurable]: "G \<in> sets M" "\<And>N. H N \<in> sets M" unfolding G_def H_def by auto
  have "G \<subseteq> (\<Union>N. H N)"
  proof
    fix x assume "x \<in> G"
    then have "x \<in> space M" unfolding G_def by simp
    have "eventually (\<lambda>n. card({n. P x n} \<inter> {..<n}) < a * n) sequentially"
      using `x \<in> G` unfolding G_def using upper_Banach_density_event1 by auto
    then obtain N where "\<And>n. n \<ge> N \<Longrightarrow> card({n. P x n} \<inter> {..<n}) < a * n"
      using eventually_sequentially by auto
    then have "x \<in> H N" unfolding H_def using `x \<in> space M` by auto
    then show "x \<in> (\<Union>N. H N)" by blast
  qed
  have "b < emeasure M G" using assms(2) unfolding G_def by simp
  also have "... \<le> emeasure M (\<Union>N. H N)"
    apply (rule emeasure_mono) using `G \<subseteq> (\<Union>N. H N)` by auto
  finally have "emeasure M (\<Union>N. H N) > b" by simp
  moreover have "(\<lambda>N. emeasure M (H N)) \<longlonglongrightarrow> emeasure M (\<Union>N. H N)"
    apply (rule Lim_emeasure_incseq) unfolding H_def incseq_def by auto
  ultimately have "eventually (\<lambda>N. emeasure M (H N) > b) sequentially"
    by (simp add: order_tendsto_iff)
  then obtain N where "emeasure M (H N) > b"
    using eventually_False_sequentially eventually_mono by blast
  then show ?thesis unfolding H_def by blast
qed


locale Gouezel_Karlsson_Kingman = pmpt +
  fixes u::"nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes subu: "subcocycle u"
    and subu_fin: "subcocycle_avg_ereal u > -\<infinity>"
    and subu_0: "AE x in M. subcocycle_lim u x = 0"
begin

lemma int_u [measurable]:
  "integrable M (u n)"
using subu unfolding subcocycle_def by auto

text {*Next lemma is Lemma 2.1 in [GK]*}

lemma upper_density_all_times:
  assumes "d > (0::real)"
  shows "\<exists>c> (0::real).
        emeasure M {x \<in> space M. upper_Banach_density {n. \<exists>l \<in> {1..n}. u n x - u (n-l) x \<le> - c * l} < d} > 1 - d"
proof -
  define f where "f = (\<lambda>x. abs (u 1 x))"
  have [measurable]: "f \<in> borel_measurable M" unfolding f_def by auto
  define G where "G = {x \<in> space M. (\<lambda>n. birkhoff_sum f n x / n) \<longlonglongrightarrow> real_cond_exp M Invariants f x
                      \<and> (\<lambda>n. u n x / n) \<longlonglongrightarrow> 0}"
  have [measurable]: "G \<in> sets M" unfolding G_def by auto
  have "AE x in M. (\<lambda>n. birkhoff_sum f n x / n) \<longlonglongrightarrow> real_cond_exp M Invariants f x"
    apply (rule birkhoff_theorem_AE_nonergodic) using subu unfolding f_def subcocycle_def by auto
  moreover have "AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> 0"
    using subu_0 kingman_theorem_nonergodic(1)[OF subu subu_fin] by auto
  ultimately have "AE x in M. x \<in> G" unfolding G_def by auto
  then have "emeasure M G = 1" by (simp add: emeasure_eq_1_AE)

  define V where "V = (\<lambda>c x. {n. \<exists>l \<in> {1..n}. u n x - u (n-l) x \<le> - c * l})"
  define Good where "Good = (\<lambda>c. {x \<in> G. upper_Banach_density (V c x) < d})"
  have [measurable]: "Good c \<in> sets M" for c unfolding Good_def V_def by auto

  have I: "upper_Banach_density (V c x) \<le> real_cond_exp M Invariants f x / c" if "c>0" "x \<in> G" for c x
  proof -
    have [simp]: "c>0" "c \<noteq> 0" "c \<ge> 0" using `c>0` by auto
    define U where "U = (\<lambda>n. abs(u 0 x) + birkhoff_sum f n x - c * card (V c x \<inter> {1..n}))"
    have main: "u n x \<le> U n" for n
    proof (rule nat_less_induct)
      fix n assume H: "\<forall>m<n. u m x \<le> U m"
      consider "n=0" | "n\<ge>1 \<and> n \<notin> V c x" | "n\<ge>1 \<and> n \<in> V c x" by linarith
      then show "u n x \<le> U n"
      proof (cases)
        assume "n=0"
        then show ?thesis unfolding U_def by auto
      next
        assume A: "n\<ge>1 \<and> n \<notin> V c x"
        then have "n \<ge> 1" by simp
        then have "n-1<n" by simp
        have "{1..n} = {1..n-1} \<union> {n}" using \<open>1 \<le> n\<close> atLeastLessThanSuc by auto
        then have *: "card (V c x \<inter> {1..n}) = card (V c x \<inter> {1..n-1})" using A by auto
        have "u n x \<le> u (n-1) x + u 1 ((T^^(n-1)) x)"
          using `n\<ge>1` subu unfolding subcocycle_def by (metis le_add_diff_inverse2)
        also have "... \<le> U (n-1) + f ((T^^(n-1)) x)" unfolding f_def using H `n-1<n` by auto
        also have "... = abs(u 0 x) + birkhoff_sum f (n-1) x + f ((T^^(n-1)) x) - c * card (V c x \<inter> {1..n-1})"
          unfolding U_def by auto
        also have "... = abs(u 0 x) + birkhoff_sum f n x - c * card (V c x \<inter> {1..n})"
          using * birkhoff_sum_cocycle[of f "n-1" 1 x] \<open>1 \<le> n\<close> by auto
        also have "... = U n" unfolding U_def by simp
        finally show ?thesis by auto
      next
        assume B: "n\<ge>1 \<and> n \<in> V c x"
        then obtain l where l: "l\<in>{1..n}" "u n x - u (n-l) x \<le> - c * l" unfolding V_def by blast
        then have "n-l < n" by simp
        have m: "\<And>r ra rb. - ((r::real) * ra) - r * rb = - (r * (rb + ra))"
          by (metis (no_types) distrib_left mult_minus_left uminus_add_conv_diff)

        have "card(V c x \<inter> {1..n}) \<le> card ((V c x \<inter> {1..n-l}) \<union> {n-l+1..n})"
          by (rule card_mono, auto)
        also have "... \<le> card (V c x \<inter> {1..n-l}) + card {n-l+1..n}"
          by (rule card_Un_le)
        also have "... \<le> card (V c x \<inter> {1..n-l}) + l" by auto
        finally have "card(V c x \<inter> {1..n}) \<le> card (V c x \<inter> {1..n-l}) + real l" by auto
        then have *: "-c * card (V c x \<inter> {1..n-l}) - c * l \<le> -c * card(V c x \<inter> {1..n})"
          using m by auto

        have "birkhoff_sum f ((n-l) + l) x = birkhoff_sum f (n-l) x + birkhoff_sum f l ((T^^(n-l))x)"
          by (rule birkhoff_sum_cocycle)
        moreover have "birkhoff_sum f l ((T^^(n-l))x) \<ge> 0"
          unfolding f_def birkhoff_sum_def using setsum_nonneg by auto
        ultimately have **: "birkhoff_sum f (n-l) x \<le> birkhoff_sum f n x" using l(1) by auto

        have "u n x \<le> u (n-l) x - c * l" using l by simp
        also have "... \<le> U (n-l) - c* l" using H `n-l < n` by auto
        also have "... = abs(u 0 x) + birkhoff_sum f (n-l) x - c * card (V c x \<inter> {1..n-l}) - c*l"
          unfolding U_def by auto
        also have "... \<le> abs(u 0 x) + birkhoff_sum f n x - c * card (V c x \<inter> {1..n})"
          using * ** by simp
        finally show ?thesis unfolding U_def by auto
      qed
    qed

    have "(\<lambda>n. abs(u 0 x) * (1/n) + birkhoff_sum f n x / n - u n x / n) \<longlonglongrightarrow> abs(u 0 x) * 0 + real_cond_exp M Invariants f x - 0"
      apply (rule tendsto_diff)
      apply (rule tendsto_add)
      apply (rule tendsto_mult, auto simp add: lim_1_over_n)
      using `x \<in> G` unfolding G_def apply (auto)
      done
    moreover have "(abs(u 0 x) + birkhoff_sum f n x - u n x)/n = abs(u 0 x) * (1/n) + birkhoff_sum f n x / n - u n x / n" for n
      by (auto simp add: add_divide_distrib diff_divide_distrib)
    ultimately have "(\<lambda>n. (abs(u 0 x) + birkhoff_sum f n x - u n x)/n) \<longlonglongrightarrow> real_cond_exp M Invariants f x"
      by auto
    then have a: "limsup (\<lambda>n. (abs(u 0 x) + birkhoff_sum f n x - u n x)/n) = real_cond_exp M Invariants f x"
      by (simp add: assms lim_imp_Limsup)

    have "c * card (V c x \<inter> {1..n})/n \<le> (abs(u 0 x) + birkhoff_sum f n x - u n x)/n" for n
      using main[of n] unfolding U_def by (simp add: divide_right_mono)
    then have "limsup (\<lambda>n. c * card (V c x \<inter> {1..n})/n) \<le> limsup (\<lambda>n. (abs(u 0 x) + birkhoff_sum f n x - u n x)/n)"
      by (simp add: Limsup_mono)
    then have b: "limsup (\<lambda>n. c * card (V c x \<inter> {1..n})/n) \<le> real_cond_exp M Invariants f x"
      using a by simp

    have "ereal(upper_Banach_density (V c x)) = limsup (\<lambda>n. card (V c x \<inter> {1..n})/n)"
      using upper_Banach_density_shift[of "V c x" 1 0] by auto
    also have "... = limsup (\<lambda>n. ereal(1/c) * ereal(c * card (V c x \<inter> {1..n})/n))"
      by auto
    also have "... = (1/c) * limsup (\<lambda>n. c * card (V c x \<inter> {1..n})/n)"
      by (rule limsup_ereal_mult_left, auto)
    also have "... \<le> ereal (1/c) * real_cond_exp M Invariants f x"
      by (rule ereal_mult_left_mono[OF b], auto)
    finally show "upper_Banach_density (V c x) \<le> real_cond_exp M Invariants f x / c"
      by auto
  qed

  {
    fix r::real
    obtain c::nat where "r / d < c" using reals_Archimedean2 by auto
    then have "r/d < real c+1" by auto
    then have "r / (real c+1) < d" using `d>0` by (simp add: divide_less_eq mult.commute)
    then have "\<exists>c::nat. r / (real c+1) < d" by auto
  }
  then have unG: "(\<Union>c::nat. {x \<in> G. real_cond_exp M Invariants f x / (c+1) < d}) = G"
    by auto

  have *: "r < d * (real n + 1)" if "m \<le> n" "r < d * (real m + 1)" for m n r
  proof -
    have "d * (real m + 1) \<le> d * (real n + 1)" using `d>0` `m \<le> n` by auto
    then show ?thesis using `r < d * (real m + 1)` by auto
  qed
  have "(\<lambda>c. emeasure M {x \<in> G. real_cond_exp M Invariants f x / (real c+1) < d})
          \<longlonglongrightarrow> emeasure M (\<Union>c::nat. {x \<in> G. real_cond_exp M Invariants f x / (c+1) < d})"
    apply (rule Lim_emeasure_incseq) unfolding incseq_def by (auto simp add: divide_simps *)
  then have "(\<lambda>c. emeasure M {x \<in> G. real_cond_exp M Invariants f x / (real c+1) < d}) \<longlonglongrightarrow> emeasure M G"
    using unG by auto
  then have "(\<lambda>c. emeasure M {x \<in> G. real_cond_exp M Invariants f x / (real c+1) < d}) \<longlonglongrightarrow> 1"
    using `emeasure M G = 1` by simp
  then have "eventually (\<lambda>c. emeasure M {x \<in> G. real_cond_exp M Invariants f x / (real c+1) < d} > 1 - d) sequentially"
    apply (rule order_tendstoD)
    apply (insert \<open>0<d\<close>, auto simp add: ennreal_1[symmetric] ennreal_lessI simp del: ennreal_1)
    done
  then obtain c0 where c0: "emeasure M {x \<in> G. real_cond_exp M Invariants f x / (real c0+1) < d} > 1 - d"
    using eventually_sequentially by auto
  define c where "c = real c0 + 1"
  then have "c > 0" by auto
  have *: "emeasure M {x \<in> G. real_cond_exp M Invariants f x / c < d} > 1 - d"
    unfolding c_def using c0 by auto
  have "{x \<in> G. real_cond_exp M Invariants f x / c < d} \<subseteq> {x \<in> space M. upper_Banach_density (V c x) < d}"
    apply auto
    using G_def apply blast
    using I[OF `c>0`] by fastforce
  then have "emeasure M {x \<in> G. real_cond_exp M Invariants f x / c < d} \<le> emeasure M {x \<in> space M. upper_Banach_density (V c x) < d}"
    apply (rule emeasure_mono) unfolding V_def by auto
  then have "emeasure M {x \<in> space M. upper_Banach_density (V c x) < d} > 1 - d" using * by auto
  then show ?thesis unfolding V_def using `c>0` by auto
qed

text {*Next lemma is Lemma 2.2 in [GK]*}

lemma upper_density_large_k:
  assumes "d > (0::real)" "d \<le> 1"
  shows "\<exists>k::nat.
        emeasure M {x \<in> space M. upper_Banach_density {n. \<exists>l \<in> {k..n}. u n x - u (n-l) x \<le> - d * l} < d} > 1 - d"
proof -
  have [simp]: "d>0" "d \<noteq> 0" "d \<ge> 0" using `d>0` by auto
  define rho where "rho = d * d * d / 4"
  have [simp]: "rho > 0" "rho \<noteq> 0" "rho \<ge> 0" unfolding rho_def using assms by auto

  text {*First step: choose a time scale $s$ at which all the computations will be done. the
  integral of $u_s$ should be suitably small -- how small precisely is given by $\rho$.*}
  {
    fix n
    have "ennreal(\<integral>x. abs(u n x / n) \<partial>M) = (\<integral>\<^sup>+x. abs(u n x /n) \<partial>M)"
      apply (rule nn_integral_eq_integral[symmetric]) using int_u by auto
    also have "... = (\<integral>\<^sup>+x. abs(u n x /n - subcocycle_lim u x) \<partial>M)"
      apply (rule nn_integral_cong_AE) using subu_0 by auto
    finally have "ennreal(\<integral>x. abs(u n x / n) \<partial>M) = (\<integral>\<^sup>+x. abs(u n x /n - subcocycle_lim u x) \<partial>M)"
      by simp
  }
  moreover have "(\<lambda>n. \<integral>\<^sup>+x. abs(u n x /n - subcocycle_lim u x) \<partial>M) \<longlonglongrightarrow> 0"
    by (rule kingman_theorem_nonergodic(3)[OF subu subu_fin])
  ultimately have "(\<lambda>n. ennreal(\<integral>x. abs(u n x / n) \<partial>M)) \<longlonglongrightarrow> 0"
    by auto
  then have "(\<lambda>n. (\<integral>x. abs(u n x / n) \<partial>M)) \<longlonglongrightarrow> 0"
    by (simp add: ennreal_0[symmetric] del: ennreal_0)
  then have "eventually (\<lambda>n. (\<integral>x. abs(u n x / n) \<partial>M) < rho) sequentially"
    by (rule order_tendstoD(2), auto)
  then obtain s::nat where [simp]: "s>0" and s_int: "(\<integral>x. abs(u s x / s) \<partial>M) < rho"
    by (metis (mono_tags, lifting) neq0_conv eventually_sequentially gr_implies_not0
        linorder_not_le of_nat_0_eq_iff order_refl zero_neq_one)



  text {*Second step: a truncation argument, to decompose $|u_1|$ as a sum of a constant (its
  contribution will be small if $k$ is large at the end of the argument) and of a function with
  small integral). *}

  have "(\<lambda>n. (\<integral>x. abs(u 1 x) * indicator {x \<in> space M. abs(u 1 x) \<ge> n} x \<partial>M)) \<longlonglongrightarrow> (\<integral>x. 0 \<partial>M)"
  proof (rule integral_dominated_convergence[where ?w= "\<lambda>x. abs(u 1 x)"])
    show "AE x in M. norm (abs(u 1 x) * indicator {x \<in> space M. abs(u 1 x) \<ge> n} x) \<le> abs(u 1 x)" for n
      unfolding indicator_def by auto
    {
      fix x
      have "abs(u 1 x) * indicator {x \<in> space M. abs(u 1 x) \<ge> n} x = (0::real)" if "n > abs(u 1 x)" for n::nat
        unfolding indicator_def using that by auto
      then have "eventually (\<lambda>n. abs(u 1 x) * indicator {x \<in> space M. abs(u 1 x) \<ge> n} x = 0) sequentially"
        by (metis (mono_tags, lifting) eventually_at_top_linorder reals_Archimedean2 less_le_trans of_nat_le_iff)
      then have "(\<lambda>n. abs(u 1 x) * indicator {x \<in> space M. abs(u 1 x) \<ge> n} x) \<longlonglongrightarrow> 0"
        by (rule Lim_eventually)
    }
    then show "AE x in M. (\<lambda>n. abs(u 1 x) * indicator {x \<in> space M. abs(u 1 x) \<ge> n} x) \<longlonglongrightarrow> 0"
      by simp
  qed (auto simp add: int_u)
  then have "eventually (\<lambda>n. (\<integral>x. abs(u 1 x) * indicator {x \<in> space M. abs(u 1 x) \<ge> n} x \<partial>M) < rho) sequentially"
    by (rule order_tendstoD(2), auto)
  then obtain Knat::nat where Knat: "Knat > 0" "(\<integral>x. abs(u 1 x) * indicator {x \<in> space M. abs(u 1 x) \<ge> Knat} x \<partial>M) < rho"
    by (metis (mono_tags, lifting) eventually_sequentially gr_implies_not0 neq0_conv
        linorder_not_le of_nat_0_eq_iff order_refl zero_neq_one)
  define K where "K = real Knat"
  then have [simp]: "K \<ge> 0" "K>0" and K: "(\<integral>x. abs(u 1 x) * indicator {x \<in> space M. abs(u 1 x) \<ge> K} x \<partial>M) < rho"
    using Knat by auto

  define F where "F = (\<lambda>x. abs(u 1 x) * indicator {x. abs(u 1 x) \<ge> K} x)"
  have int_F [measurable]: "integrable M F"
    unfolding F_def apply (rule Bochner_Integration.integrable_bound[where ?f = "\<lambda>x. abs(u 1 x)"])
    unfolding indicator_def by (auto simp add: int_u)
  have "(\<integral>x. F x \<partial>M) = (\<integral>x. abs(u 1 x) * indicator {x \<in> space M. abs(u 1 x) \<ge> K} x \<partial>M)"
    apply (rule integral_cong_AE) unfolding F_def by (auto simp add: indicator_def)
  then have F_int: "(\<integral>x. F x \<partial>M) < rho" using K by auto
  have F_pos: "F x \<ge> 0" for x unfolding F_def by auto
  have u1_bound: "abs(u 1 x) \<le> K + F x" for x
    unfolding F_def indicator_def apply (cases "x \<in> {x \<in> space M. K \<le> \<bar>u 1 x\<bar>}") by auto

  define F2 where "F2 = (\<lambda>x. F x + abs(u s x/s))"
  have int_F2 [measurable]: "integrable M F2"
    unfolding F2_def using int_F int_u[of s] by auto
  have F2_pos: "F2 x \<ge> 0" for x unfolding F2_def using F_pos by auto
  have "(\<integral>x. F2 x \<partial>M) = (\<integral>x. F x \<partial>M) + (\<integral>x. abs(u s x/s) \<partial>M)"
    unfolding F2_def apply (rule Bochner_Integration.integral_add) using int_F int_u by auto
  then have F2_int: "(\<integral>x. F2 x \<partial>M) < 2 * rho"
    using F_int s_int by auto

  text {*We can now choose $k$, large enough. The reason for our choice will only appear
  at the end of the proof.*}
  define k where "k = max (2 * s + 1) (nat(ceiling((2 * d * s + 2 * K * s)/(d/2))))"
  have "k > 2 * s" unfolding k_def by auto
  have "k \<ge> (2 * d * s + 2 * K * s)/(d/2)"
    unfolding k_def by linarith
  then have "(2 * d * s + 2 * K * s)/k \<le> d/2"
    using `k > 2 * s` by (simp add: divide_simps mult.commute)


  text {*Third step: definition of a good set $G$ where everything goes well.*}

  define G where "G = {x \<in> space M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> 0
                      \<and> (\<lambda>n. birkhoff_sum (\<lambda>x. abs(u s x / s)) n x / n) \<longlonglongrightarrow> real_cond_exp M Invariants (\<lambda>x. abs(u s x / s)) x
                      \<and> (\<lambda>n. birkhoff_sum F n x / n) \<longlonglongrightarrow> real_cond_exp M Invariants F x
                      \<and> real_cond_exp M Invariants F x + real_cond_exp M Invariants (\<lambda>x. abs(u s x / s)) x = real_cond_exp M Invariants F2 x}"
  have [measurable]: "G \<in> sets M" unfolding G_def by auto
  have "AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> 0"
    using kingman_theorem_nonergodic(1)[OF subu subu_fin] subu_0 by auto
  moreover have "AE x in M.(\<lambda>n. birkhoff_sum (\<lambda>x. abs(u s x / s)) n x / n) \<longlonglongrightarrow> real_cond_exp M Invariants (\<lambda>x. abs(u s x / s)) x"
    apply (rule birkhoff_theorem_AE_nonergodic) using int_u[of s] by auto
  moreover have "AE x in M. (\<lambda>n. birkhoff_sum F n x / n) \<longlonglongrightarrow> real_cond_exp M Invariants F x"
    by (rule birkhoff_theorem_AE_nonergodic[OF int_F])
  moreover have "AE x in M. real_cond_exp M Invariants F x + real_cond_exp M Invariants (\<lambda>x. abs(u s x / s)) x = real_cond_exp M Invariants F2 x"
    unfolding F2_def apply (rule AE_symmetric[OF real_cond_exp_add]) using int_u[of s] int_F int_u[of s] by auto
  ultimately have "AE x in M. x \<in> G" unfolding G_def by auto
  then have "emeasure M G = 1" by (simp add: emeasure_eq_1_AE)

  text {*Estimation of Banach densities of bad times, for points in $G$.
  There is a trivial part, named $U$ below, that has to be treated separately because it creates
  problematic boundary effects.*}

  define U where "U = (\<lambda>x. {n. \<exists>l \<in> {n-s<..n}. u n x - u (n-l) x \<le> - d * l})"
  define V where "V = (\<lambda>x. {n. \<exists>l \<in> {k..n-s}. u n x - u (n-l) x \<le> - d * l})"

  text {*Trivial estimate for $U(x)$: this set is finite for $x\in G$.*}

  have densU: "upper_Banach_density (U x) = 0" if "x \<in> G" for x
  proof -
    define C where "C = Max {abs(u m x) |m. m<s} + d * s"
    have *: "U x \<subseteq> {n. u n x \<le> C - d * n}"
    proof (auto)
      fix n assume "n \<in> U x"
      then obtain l where l: "l\<in> {n-s <..n}" "u n x - u (n-l) x \<le> - d * l" unfolding U_def by auto
      define m where "m = n-l"
      have "m < s" unfolding m_def using l by auto
      have "u n x \<le> u m x - d * l" using l m_def by auto
      also have "... \<le> abs(u m x) - d * n + d * m" unfolding m_def using l
        by (simp add: linordered_field_class.sign_simps(38) of_nat_diff)
      also have "... \<le> Max {abs(u m x) |m. m<s} - d * n + d * m"
        using `m < s` apply (auto) by (rule Max_ge, auto)
      also have "... \<le> Max {abs(u m x) |m. m<s} + d * s - d * n"
        using `m < s` `d>0` by auto
      finally show "u n x \<le> C - d * n"
        unfolding C_def by auto
    qed
    have "eventually (\<lambda>n. u n x / n > -d/2) sequentially"
      apply (rule order_tendstoD(1)) using `x \<in> G` `d>0` unfolding G_def by auto
    then obtain N where N: "\<And>n. n \<ge> N \<Longrightarrow> u n x / n > - d/2"
      using eventually_sequentially by auto
    {
      fix n assume *: "u n x \<le> C - d * n" "n > N"
      then have "n \<ge> N" "n > 0" by auto
      have "2 * u n x \<le> 2 * C - 2 * d * n" using * by auto
      moreover have "2 * u n x \<ge> - d * n" using N[OF `n \<ge> N`] `n > 0` by (simp add: divide_simps)
      ultimately have "- d * n \<le> 2 * C - 2 * d * n" by auto
      then have "d * n \<le> 2 * C" by auto
      then have "n \<le> 2 * C / d" using `d>0` by (simp add: mult.commute divide_simps)
    }
    then have "{n. u n x \<le> C - d * n} \<subseteq> {..max (nat (floor(2*C/d))) N}"
      by (auto, meson le_max_iff_disj le_nat_floor not_le)
    then have "finite {n. u n x \<le> C - d * n}"
      using finite_subset by blast
    then have "finite (U x)" using * finite_subset by blast
    then show ?thesis using upper_Banach_density_finite by auto
  qed

  text {*Main step: control of $u$ along the sequence $ns+t$, with a term
  $-(d/2) Card(V(x) \cap [1,ns+t])$ on the right.
  Then, after averaging in $t$, Birkhoff theorem will imply that
  $Card(V(x) \cap [1,n])$ is suitably small.*}

  define Z where "Z = (\<lambda>t n x. Max {u i x|i. i< s} + (\<Sum>i<n. abs(u s ((T^^(i * s + t))x)))
                  + birkhoff_sum F (n * s + t) x - (d/2) * card(V x \<inter> {1..n * s + t}))"
  have Main: "u (n * s + t) x \<le> Z t n x" if "t < s" for n x t
  proof (rule nat_less_induct[where ?n = n])
    fix n assume H: "\<forall>m<n. u (m * s + t) x \<le> Z t m x"
    consider "n=0"|"n>0 \<and> V x \<inter> {(n-1)* s+t<..n* s+t} = {}"|"n>0 \<and> V x \<inter> {(n-1)* s+t<..n* s+t} \<noteq> {}" by auto
    then show "u (n* s+t) x \<le> Z t n x"
    proof (cases)
      assume "n=0"
      then have "V x \<inter> {1..n * s + t} = {}" unfolding V_def using `t<s` `k>2* s` by auto
      then have *: "card(V x \<inter> {1..n * s+t}) = 0" by simp
      have **: "0 \<le> (\<Sum>i<t. F ((T ^^ i) x))" by (rule setsum_nonneg, simp add: F_pos)
      have "u (n * s + t) x = u t x" using `n=0` by auto
      also have "... \<le> Max {u i x|i. i< s}" by (rule Max_ge, auto simp add: `t<s`)
      also have "... \<le> Z t n x"
        unfolding Z_def birkhoff_sum_def using `n=0` * ** by auto
      finally show ?thesis by simp
    next
      assume A: "n>0 \<and> V x \<inter> {(n-1)* s+t<..n* s+t} = {}"
      then have "n\<ge>1" by simp
      have "n * s + t = (n-1) * s + t + s" using `n\<ge>1` by (simp add: add.commute add.left_commute mult_eq_if)
      have "V x \<inter> {1..n * s + t} = V x \<inter> {1..(n-1) * s + t} \<union> V x \<inter> {(n-1) * s + t<..n * s + t}"
        using `n\<ge>1` by (auto, simp add: mult_eq_if)
      then have *: "card(V x \<inter> {1..n * s+t}) = card(V x \<inter> {1..(n-1) * s+t})" using A by auto

      have **: "birkhoff_sum F ((n-1) * s + t) x \<le> birkhoff_sum F (n * s + t) x"
        unfolding birkhoff_sum_def apply (rule setsum_mono2)
        using `n* s+t = (n-1)* s+t + s` F_pos by auto

      have "(\<Sum>i<n-1. abs(u s ((T^^(i* s+t))x))) + u s ((T^^((n-1)* s+t)) x)
        \<le> (\<Sum>i<n-1. abs(u s ((T^^(i* s+t))x))) + abs(u s ((T^^((n-1)* s+t)) x))" by auto
      also have "... \<le> (\<Sum>i<n. abs(u s ((T^^(i* s+t))x)))"
        using `n\<ge>1` lessThan_Suc_atMost setsum_lessThan_Suc[where ?n = "n-1" and ?f = "\<lambda>i. abs(u s ((T^^(i* s+t))x))" , symmetric] by auto
      finally have ***: "(\<Sum>i<n-1. abs(u s ((T^^(i* s+t))x))) + u s ((T^^((n-1)* s+t)) x) \<le> (\<Sum>i<n. abs(u s ((T^^(i* s+t))x)))"
        by simp

      have "u (n* s+t) x = u ((n-1)* s+t + s) x"
        using `n\<ge>1` by (simp add: add.commute add.left_commute mult_eq_if)
      also have "... \<le> u ((n-1)* s+t) x + u s ((T^^((n-1)* s+t)) x)"
        using subcocycle_ineq[OF subu, of "(n-1)* s+t" s x] by simp
      also have "... \<le> Max {u i x|i. i< s} + (\<Sum>i<n-1. abs(u s ((T^^(i* s+t))x)))
        + birkhoff_sum F ((n-1) * s+t) x - (d/2) * card(V x \<inter> {1..(n-1) * s+t}) + u s ((T^^((n-1)* s+t)) x)"
        using H `n\<ge>1` unfolding Z_def by auto
      also have "... \<le> Max {u i x|i. i< s} + (\<Sum>i<n. abs(u s ((T^^(i* s+t))x)))
        + birkhoff_sum F (n * s+t) x - (d/2) * card(V x \<inter> {1..n * s+t})"
        using * ** *** by auto
      also have "... \<le> Z t n x" unfolding Z_def by (auto simp add: divide_simps)
      finally show ?thesis by simp
    next
      assume B: "n>0 \<and> V x \<inter> {(n-1)* s+t<..n* s+t} \<noteq> {}"
      then have [simp]: "n>0" "n\<ge>1" "n \<noteq> 0" by auto
      obtain m where m: "m \<in> V x \<inter> {(n-1)* s+t<..n* s+t}" using B by blast
      then obtain l where l: "l \<in> {k..m-s}" "u m x - u (m-l) x \<le> - d * l" unfolding V_def by auto
      then have "m-s>0" using `k>2* s` by auto
      then have "m-l \<ge> s" using l by auto
      define p where "p = (m-l-t) div s"
      have p1: "m-l \<ge> p* s + t"
        unfolding p_def
        using `m-l \<ge> s` `s>t`
        minus_mod_eq_div_mult [symmetric, of "m - l - t" s]
        by simp
      have p2: "m-l < p* s + t + s"
        unfolding p_def using `m-l \<ge> s` `s>t`
        div_mult_mod_eq[of "m-l-t" s] mod_less_divisor[OF `s>0`, of "m-l-t"] by linarith
      then have "l \<ge> m - p* s - t -s" by auto
      then have "l \<ge> (n-1)* s + t -p* s - t- s" using m by auto
      then have "l + 2* s\<ge> (n* s+t) - (p* s+t)" by (simp add: diff_mult_distrib)
      have "(p+1)* s+t\<le>(n-1)* s+t"
        using `k> 2* s` m l(1) p1 by (auto simp add: algebra_simps)
      then have "p+1 \<le> n-1"
        using `s>0` by (meson add_le_cancel_right mult_le_cancel2)
      then have "p \<le> n-1" "p<n" by auto
      have "(p* s + t) + k \<le> (n* s + t)"
        using m l(1) p1 by (auto simp add: algebra_simps)
      then have "(1::real) \<le> ((n* s + t) - (p* s + t)) / k"
        using `k > 2* s` by auto

      have In: "u (n * s + t) x \<le> u m x + (\<Sum>i \<in> {(n-1)* s+t..<n* s+t}. abs(u 1 ((T^^i) x)))"
      proof (cases "m = n * s + t")
        case True
        have "(\<Sum>i \<in> {(n-1)* s+t..<n* s+t}. abs(u 1 ((T^^i) x))) \<ge> 0"
          by (rule setsum_nonneg, auto)
        then show ?thesis using True by auto
      next
        case False
        then have m2: "n * s + t - m >0" "(n-1)* s+t \<le> m" using m by auto
        have "birkhoff_sum (u 1) (n* s+t-m) ((T^^m) x) = (\<Sum>i<n* s+t-m. u 1 ((T^^i)((T^^m) x)))"
          unfolding birkhoff_sum_def by auto
        also have "... = (\<Sum>i<n* s+t-m. u 1 ((T^^(i+m)) x))"
          by (simp add: funpow_add)
        also have "... = (\<Sum>j \<in> {m..<n* s+t}. u 1 ((T^^j) x))"
          by (rule setsum.reindex_bij_betw, rule bij_betw_byWitness[where ?f'= "\<lambda>i. i - m"], auto)
        also have "... \<le> (\<Sum>j \<in> {m..<n* s+t}. abs(u 1 ((T^^j) x)))"
          by (rule setsum_mono, auto)
        also have "... \<le> (\<Sum>j \<in> {(n-1)* s+t..<m}. abs(u 1 ((T^^j) x))) + (\<Sum>j \<in> {m..<n* s+t}. abs(u 1 ((T^^j) x)))"
          by auto
        also have "... = (\<Sum>j \<in> {(n-1)* s+t..<n* s+t}. abs(u 1 ((T^^j) x)))"
          apply (rule setsum_add_nat_ivl) using m2 by auto
        finally have *: "birkhoff_sum (u 1) (n* s+t-m) ((T^^m) x) \<le> (\<Sum>j \<in> {(n-1)* s+t..<n* s+t}. abs(u 1 ((T^^j) x)))"
          by auto

        have "u (n* s+t) x \<le> u m x + u (n* s+t-m) ((T^^m) x)"
          using subcocycle_ineq[OF subu, of m "n* s+t-m"] m2 by auto
        also have "... \<le> u m x + birkhoff_sum (u 1) (n* s+t-m) ((T^^m) x)"
          using subcocycle_bounded_by_birkhoff1[OF subu `n* s+t - m >0`, of "(T^^m)x"] by simp
        finally show ?thesis using * by auto
      qed

      have Ip: "u (m-l) x \<le> u (p* s+t) x + (\<Sum>i \<in> {p* s+t..<(p+1)* s+t}. abs(u 1 ((T^^i) x)))"
      proof (cases "m-l = p* s+t")
        case True
        have "(\<Sum>i \<in> {p* s+t..<(p+1)* s+t}. abs(u 1 ((T^^i) x))) \<ge> 0"
          by (rule setsum_nonneg, auto)
        then show ?thesis using True by auto
      next
        case False
        then have "m-l - (p* s+t) > 0" using p1 by auto
        have I: "p * s + t + (m - l - (p * s + t)) = m - l" using p1 by auto

        have "birkhoff_sum (u 1) (m-l - (p* s+t)) ((T^^(p* s+t)) x) = (\<Sum>i<m-l - (p* s+t). u 1 ((T^^i) ((T^^(p* s+t)) x)))"
          unfolding birkhoff_sum_def by auto
        also have "... = (\<Sum>i<m-l - (p* s+t). u 1 ((T^^(i+p* s+t)) x))"
          by (simp add: funpow_add)
        also have "... = (\<Sum>j \<in> {p* s+t..<m-l}. u 1 ((T^^j) x))"
          by (rule setsum.reindex_bij_betw, rule bij_betw_byWitness[where ?f'= "\<lambda>i. i - (p* s+t)"], auto)
        also have "... \<le> (\<Sum>j \<in> {p* s+t..<m-l}. abs(u 1 ((T^^j) x)))"
          by (rule setsum_mono, auto)
        also have "... \<le> (\<Sum>j \<in> {p* s+t..<m-l}. abs(u 1 ((T^^j) x))) + (\<Sum>j \<in> {m-l..<(p+1)* s+t}. abs(u 1 ((T^^j) x)))"
          by auto
        also have "... = (\<Sum>j \<in> {p* s+t..<(p+1)* s+t}. abs(u 1 ((T^^j) x)))"
          apply (rule setsum_add_nat_ivl) using p1 p2 by auto
        finally have *: "birkhoff_sum (u 1) (m-l - (p* s+t)) ((T^^(p* s+t)) x)
          \<le> (\<Sum>j \<in> {p* s+t..<(p+1)* s+t}. abs(u 1 ((T^^j) x)))"
          by auto

        have "u (m-l) x \<le> u (p* s+t) x + u (m-l - (p* s+t)) ((T^^(p* s+t)) x)"
          using subcocycle_ineq[OF subu, of "p* s+t" "m-l - (p* s+t)" x] I by auto
        also have "... \<le> u (p* s+t) x + birkhoff_sum (u 1) (m-l - (p* s+t)) ((T^^(p* s+t)) x)"
          using subcocycle_bounded_by_birkhoff1[OF subu `m-l - (p* s+t) > 0`, of "(T^^(p* s+t)) x"] by simp
        finally show ?thesis using * by auto
      qed

      have "(\<Sum>i \<in> {p* s+t..<(p+1)* s+t}. abs(u 1 ((T^^i) x))) \<le> (\<Sum>i \<in> {p* s+t..<(p+1)* s+t}. K + F ((T^^i) x))"
        apply (rule setsum_mono) using u1_bound by auto
      moreover have "(\<Sum>i \<in> {(n-1)* s+t..<n* s+t}. abs(u 1 ((T^^i) x))) \<le> (\<Sum>i \<in> {(n-1)* s+t..<n* s+t}. K + F ((T^^i) x))"
        apply (rule setsum_mono) using u1_bound by auto
      ultimately have "(\<Sum>i \<in> {p* s+t..<(p+1)* s+t}. abs(u 1 ((T^^i) x))) + (\<Sum>i \<in> {(n-1)* s+t..<n* s+t}. abs(u 1 ((T^^i) x)))
        \<le> (\<Sum>i \<in> {p* s+t..<(p+1)* s+t}. K + F ((T^^i) x)) + (\<Sum>i \<in> {(n-1)* s+t..<n* s+t}. K + F ((T^^i) x))"
        by auto
      also have "... = 2* K* s + (\<Sum>i \<in> {p* s+t..<(p+1)* s+t}. F ((T^^i) x)) + (\<Sum>i \<in>{(n-1)* s+t..<n* s+t}. F ((T^^i) x))"
        by (auto simp add: mult_eq_if setsum.distrib)
      also have "... \<le> 2* K * s + (\<Sum>i \<in> {p* s+t..<(n-1)* s+t}. F ((T^^i) x)) + (\<Sum>i \<in>{(n-1)* s+t..<n* s+t}. F ((T^^i) x))"
        apply (auto, rule setsum_mono2) using `(p+1)* s+t\<le>(n-1)* s+t` F_pos by auto
      also have "... = 2* K * s + (\<Sum>i \<in> {p* s+t..<n* s+t}. F ((T^^i) x))"
        apply (auto, rule setsum_add_nat_ivl) using `p\<le>n-1` by auto
      finally have A0: "(\<Sum>i \<in> {p* s+t..<(p+1)* s+t}. abs(u 1 ((T^^i) x))) + (\<Sum>i \<in> {(n-1)* s+t..<n* s+t}. abs(u 1 ((T^^i) x)))
        \<le> 2* K * s + (\<Sum>i \<in> {p* s+t..<n* s+t}. F ((T^^i) x))"
        by simp

      have "card(V x \<inter> {p * s + t<.. n* s+t}) \<le> card {p * s + t<.. n* s+t}" by (rule card_mono, auto)
      have "2 * d * s + 2 * K * s > 0" using `K>0` `s>0` `d>0`
        by (metis add_pos_pos mult_2 mult_zero_left of_nat_0_less_iff pos_divide_less_eq times_divide_eq_right)
      then have "2 * d * s + 2 * K * s \<le> ((n* s + t) - (p* s + t)) * ((2 * d * s + 2 * K * s) / k)"
        using `1 \<le> ((n* s + t) - (p* s + t)) / k` by (simp add: le_divide_eq_1 pos_le_divide_eq)
      also have "... \<le> ((n* s + t) - (p* s + t)) * (d/2)"
        apply (rule mult_left_mono) using `(2 * d * s + 2 * K * s)/k \<le> d/2` by auto
      finally have "2 * d * s + 2 * K * s \<le> ((n* s + t) - (p* s + t)) * (d/2)"
        by auto
      then have "-d * ((n* s+t) - (p* s+t)) + 2 * d * s + 2 * K * s \<le> -d * ((n* s+t) - (p* s+t)) + ((n* s + t) - (p* s + t)) * (d/2)"
        by linarith
      also have "... = (-d/2) * card {p * s + t<.. n* s+t}"
        by auto
      also have "... \<le> (-d/2) * card(V x \<inter> {p * s + t<.. n* s+t})"
        using `card(V x \<inter> {p * s + t<.. n* s+t}) \<le> card {p * s + t<.. n* s+t}` by auto
      finally have A1: "-d * ((n* s+t) - (p* s+t)) + 2 * d * s + 2 * K * s \<le> (-d/2) * card(V x \<inter> {p * s + t<.. n* s+t})"
        by simp

      have "V x \<inter> {1.. n* s+t} = V x \<inter> {1..p * s + t} \<union> V x \<inter> {p * s + t<.. n* s+t}"
        using \<open>p * s + t + k \<le> n * s + t\<close> by auto
      then have "card (V x \<inter> {1.. n* s+t}) = card(V x \<inter> {1..p * s + t} \<union> V x \<inter> {p * s + t<.. n* s+t})"
        by auto
      also have "... = card (V x \<inter> {1..p * s + t}) + card (V x \<inter> {p * s + t<.. n* s+t})"
        by (rule card_Un_disjoint, auto)
      finally have A2: "card (V x \<inter> {1..p * s + t}) + card (V x \<inter> {p * s + t<.. n* s+t}) = card (V x \<inter> {1.. n* s+t})"
        by simp

      have A3: "(\<Sum>i<p. abs(u s ((T ^^ (i * s + t)) x))) \<le> (\<Sum>i<n. abs(u s ((T ^^ (i * s + t)) x)))"
        apply (rule setsum_mono2) using `p\<le>n-1` by auto

      have A4: "birkhoff_sum F (p * s + t) x + (\<Sum>i \<in> {p* s+t..<n* s+t}. F ((T^^i) x)) = birkhoff_sum F (n * s + t) x"
        unfolding birkhoff_sum_def apply (subst atLeast0LessThan[symmetric])+ apply (rule setsum_add_nat_ivl)
        using `p\<le>n-1` by auto

      have "u (n* s+t) x \<le> u m x + (\<Sum>i \<in> {(n-1)* s+t..<n* s+t}. abs(u 1 ((T^^i) x)))"
        using In by simp
      also have "... \<le> (u m x - u (m-l) x) + u (m-l) x + (\<Sum>i \<in> {(n-1)* s+t..<n* s+t}. abs(u 1 ((T^^i) x)))"
        by simp
      also have "... \<le> - d * l + u (p* s+t) x + (\<Sum>i \<in> {p* s+t..<(p+1)* s+t}. abs(u 1 ((T^^i) x))) + (\<Sum>i \<in> {(n-1)* s+t..<n* s+t}. abs(u 1 ((T^^i) x)))"
        using Ip l by auto
      also have "... \<le> - d * ((n* s+t) - (p* s+t)) + 2*d* s + u (p* s+t) x + (\<Sum>i \<in> {p* s+t..<(p+1)* s+t}. abs(u 1 ((T^^i) x))) + (\<Sum>i \<in> {(n-1)* s+t..<n* s+t}. abs(u 1 ((T^^i) x)))"
        using `l + 2* s\<ge> (n* s+t) - (p* s+t)` apply (auto simp add: algebra_simps)
        by (metis assms(1) distrib_left mult.commute mult_2 of_nat_add of_nat_le_iff real_mult_le_cancel_iff2)
      also have "... \<le> -d * ((n* s+t) - (p* s+t)) + 2*d* s + Z t p x + 2* K * s + (\<Sum>i \<in> {p* s+t..<n* s+t}. F ((T^^i) x))"
        using A0 H `p<n` by auto
      also have "... \<le> Z t p x - d/2 * card(V x \<inter> {p * s + t<.. n* s+t}) + (\<Sum>i \<in> {p* s+t..<n* s+t}. F ((T^^i) x))"
        using A1 by auto
      also have "... = Max {u i x |i. i < s} + (\<Sum>i<p. abs(u s ((T ^^ (i * s + t)) x))) + birkhoff_sum F (p * s + t) x
          - d / 2 * card (V x \<inter> {1..p * s + t}) - d/2 * card(V x \<inter> {p * s + t<.. n* s+t}) + (\<Sum>i \<in> {p* s+t..<n* s+t}. F ((T^^i) x))"
        unfolding Z_def by auto
      also have "... \<le> Max {u i x |i. i < s} + (\<Sum>i<n. abs(u s ((T ^^ (i * s + t)) x)))
        + (birkhoff_sum F (p * s + t) x + (\<Sum>i \<in> {p* s+t..<n* s+t}. F ((T^^i) x)))
        - d/2 * card (V x \<inter> {1..p * s + t}) - d/2 * card(V x \<inter> {p * s + t<.. n* s+t})"
        using A3 by auto
      also have "... = Z t n x"
        unfolding Z_def using A2 A4 by (auto simp add: algebra_simps, metis distrib_left of_nat_add)
      finally show ?thesis by simp
    qed
  qed

  have Main2: "(d/2) * card(V x \<inter> {1..n}) \<le> Max {u i x|i. i< s} + birkhoff_sum (\<lambda>x. abs(u s x/ s)) (n+2* s) x
    + birkhoff_sum F (n + 2 * s) x + (1/s) * (\<Sum>i<2* s. abs(u (n+i) x))" for n x
  proof -
    define N where "N = (n div s) + 1"
    then have "n \<le> N * s"
      using `s>0` by (metis Suc_eq_plus1 less_imp_le_nat mult.commute split_div_lemma)
    have "N * s \<le> n + s" unfolding N_def
      by (metis \<open>0 < s\<close> div_add_self2 mult.commute neq0_conv split_div_lemma)

    have eq_t: "(d/2) * card(V x \<inter> {1..n}) \<le> abs(u(N* s+t) x) + (Max {u i x|i. i< s} + birkhoff_sum F (n + 2* s) x)
            + (\<Sum>i<N. abs(u s ((T^^(i* s+t))x)))"
      if "t<s" for t
    proof -
      have *: "birkhoff_sum F (N * s+t) x \<le> birkhoff_sum F (n+ 2* s) x"
        unfolding birkhoff_sum_def apply (rule setsum_mono2) using F_pos `N * s \<le> n + s` `t<s` by auto

      have "card(V x \<inter> {1..n}) \<le> card(V x \<inter> {1..N* s+t})"
        apply (rule card_mono) using `n \<le> N * s` by auto
      then have "(d/2) * card(V x \<inter> {1..n}) \<le> (d/2) * card(V x \<inter> {1..N* s+t})"
        by auto
      also have "... \<le> - u (N* s+t) x + Max {u i x|i. i< s} + (\<Sum>i<N. abs(u s ((T^^(i* s+t))x))) + birkhoff_sum F (N * s+t) x"
        using Main[OF `t < s`, of N x] unfolding Z_def by auto
      also have "... \<le> abs(u(N* s+t) x) + Max {u i x|i. i< s} + birkhoff_sum F (n + 2* s) x + (\<Sum>i<N. abs(u s ((T^^(i* s+t))x)))"
        using * by auto
      finally show ?thesis by simp
    qed

    have "(\<Sum>t<s. abs(u(N* s+t) x)) = (\<Sum>i\<in>{N* s..<N* s+s}. abs (u i x))"
      by (rule setsum.reindex_bij_betw, rule bij_betw_byWitness[where ?f'= "\<lambda>i. i - N* s"], auto)
    also have "... \<le> (\<Sum>i\<in>{n..<n + 2* s}. abs (u i x))"
      apply (rule setsum_mono2) using `n \<le> N * s` `N * s \<le> n + s` by auto
    also have "... = (\<Sum>i<2* s. abs (u (n+i) x))"
      by (rule setsum.reindex_bij_betw[symmetric], rule bij_betw_byWitness[where ?f'= "\<lambda>i. i - n"], auto)
    finally have **: "(\<Sum>t<s. abs(u(N* s+t) x)) \<le> (\<Sum>i<2* s. abs (u (n+i) x))"
      by simp

    have "(\<Sum>t<s. (\<Sum>i<N. abs(u s ((T^^(i* s+t))x)))) = (\<Sum>i<N* s. abs(u s ((T^^i) x)))"
      by (rule setsum_arith_progression)
    also have "... \<le> (\<Sum>i<n + 2* s. abs(u s ((T^^i) x)))"
      apply (rule setsum_mono2) using `N * s \<le> n + s` by auto
    finally have ***: "(\<Sum>t<s. (\<Sum>i<N. abs(u s ((T^^(i* s+t))x)))) \<le> s * birkhoff_sum (\<lambda>x. abs(u s x/ s)) (n+2* s) x"
      unfolding birkhoff_sum_def using `s>0` by (auto simp add: setsum_divide_distrib[symmetric])

    have ****: "s * (\<Sum>i<n + 2* s. abs(u s ((T^^i) x)) /s) = (\<Sum>i<n + 2* s. abs(u s ((T^^i) x)))"
      by (auto simp add: setsum_divide_distrib[symmetric])

    have "s * (d/2) * card(V x \<inter> {1..n}) = (\<Sum>t<s. (d/2) * card(V x \<inter> {1..n}))"
      by auto
    also have "... \<le> (\<Sum>t<s. abs(u(N* s+t) x) + (Max {u i x|i. i< s} + birkhoff_sum F (n + 2* s) x)
            + (\<Sum>i<N. abs(u s ((T^^(i* s+t))x))))"
      apply (rule setsum_mono) using eq_t by auto
    also have "... = (\<Sum>t<s. abs(u(N* s+t) x)) + (\<Sum>t<s. Max {u i x|i. i< s} + birkhoff_sum F (n + 2* s) x) + (\<Sum>t<s. (\<Sum>i<N. abs(u s ((T^^(i* s+t))x))))"
      by (auto simp add: setsum.distrib)
    also have "... \<le> (\<Sum>i<2* s. abs (u (n+i) x)) + s * (Max {u i x|i. i< s} + birkhoff_sum F (n + 2* s) x) + s * birkhoff_sum (\<lambda>x. abs(u s x/ s)) (n+2* s) x"
      using ** *** by auto
    also have "... = s * ((1/s) * (\<Sum>i<2* s. abs (u (n+i) x)) + Max {u i x|i. i< s} + birkhoff_sum F (n + 2* s) x + birkhoff_sum (\<lambda>x. abs(u s x/ s)) (n+2* s) x)"
      by (auto simp add: divide_simps mult.commute distrib_left)
    finally show ?thesis
      by auto
  qed

  have densV: "upper_Banach_density (V x) \<le> (2/d) * real_cond_exp M Invariants F2 x" if "x \<in> G" for x
  proof -
    have *: "(\<lambda>n. u n x/n) \<longlonglongrightarrow> 0" using `x\<in>G` unfolding G_def by auto
    have **: "(\<lambda>n. abs(u n x/n)) \<longlonglongrightarrow> 0" by (rule tendsto_rabs_zero [OF *])
    have A: "(\<lambda>n. abs(u (n+i) x) / n) \<longlonglongrightarrow> 0" for i
      apply (rule tendsto_shift_1_over_n) using ** by auto

    define Bound where "Bound = (\<lambda>n. (Max {u i x|i. i< s}*(1/n) + birkhoff_sum (\<lambda>x. abs(u s x/ s)) (n+2* s) x / n
      + birkhoff_sum F (n + 2* s) x / n + (1/s) * (\<Sum>i<2* s. abs(u (n+i) x) / n)))"
    have "Bound \<longlonglongrightarrow> (Max {u i x|i. i< s} * 0 + real_cond_exp M Invariants (\<lambda>x. abs(u s x/s)) x + real_cond_exp M Invariants F x +
      (1/s) * (\<Sum>i<2* s. 0))"
      unfolding Bound_def
      apply (rule tendsto_add)+
      apply (rule tendsto_mult, simp, simp add: lim_1_over_n)
      apply (rule tendsto_shift_1_over_n)
      using `x\<in>G` unfolding G_def apply simp
      apply (rule tendsto_shift_1_over_n)
      using `x\<in>G` unfolding G_def apply simp
      apply (rule tendsto_mult)
      apply simp
      apply (rule tendsto_setsum)
      using A apply auto
      done
    then have "Bound \<longlonglongrightarrow> real_cond_exp M Invariants (\<lambda>x. abs(u s x/s)) x + real_cond_exp M Invariants F x"
      by simp
    moreover have "real_cond_exp M Invariants (\<lambda>x. abs(u s x/s)) x + real_cond_exp M Invariants F x = real_cond_exp M Invariants F2 x"
      using `x \<in> G` unfolding G_def by auto
    ultimately have B_conv: "Bound \<longlonglongrightarrow> real_cond_exp M Invariants F2 x" by simp

    have *: "(d/2) * card(V x \<inter> {1..n}) / n \<le> Bound n" for n
    proof -
      have "(d/2) * card(V x \<inter> {1..n}) / n \<le> (Max {u i x|i. i< s} + birkhoff_sum (\<lambda>x. abs(u s x/ s)) (n+2* s) x
        + birkhoff_sum F (n + 2* s) x + (1/s) * (\<Sum>i<2* s. abs(u (n+i) x)))/n"
        using Main2[of x n] using divide_right_mono of_nat_0_le_iff by blast
      also have "... = Bound n"
        unfolding Bound_def by (auto simp add: add_divide_distrib setsum_divide_distrib[symmetric])
      finally show ?thesis by simp
    qed

    have "ereal(d/2 * upper_Banach_density (V x)) = ereal(d/2) * ereal(upper_Banach_density (V x))"
      by auto
    also have "... = ereal (d/2) * limsup(\<lambda>n. card(V x \<inter> {1..n}) / n)"
      using upper_Banach_density_shift[of "V x" 1 0] by auto
    also have "... = limsup(\<lambda>n. ereal (d/2) * (card(V x \<inter> {1..n}) / n))"
      by (rule limsup_ereal_mult_left[symmetric], auto)
    also have "... \<le> limsup Bound"
      apply (rule Limsup_mono) using * not_eventuallyD by auto
    also have "... = ereal(real_cond_exp M Invariants F2 x)"
      using B_conv convergent_limsup_cl convergent_def convergent_real_imp_convergent_ereal limI by force
    finally have "d/2 * upper_Banach_density (V x) \<le> real_cond_exp M Invariants F2 x"
      by auto
    then show ?thesis
      by (simp add: divide_simps mult.commute)
  qed

  define epsilon where "epsilon = 2 * rho / d"
  have [simp]: "epsilon > 0" "epsilon \<noteq> 0" "epsilon \<ge> 0" unfolding epsilon_def by auto
  have "emeasure M {x\<in>space M. real_cond_exp M Invariants F2 x \<ge> epsilon} \<le> (1/epsilon) * (\<integral>x. real_cond_exp M Invariants F2 x \<partial>M)"
    apply (rule integral_Markov_inequality)
    apply (rule real_cond_exp_int(1))
    apply (simp add: int_F2)
    apply (rule real_cond_exp_pos)
    apply (simp add: F2_pos)
    apply auto
    done
  also have "... = (1/epsilon) * (\<integral>x. F2 x \<partial>M)"
    apply (intro arg_cong[where f=ennreal])
    by (simp, rule real_cond_exp_int(2), simp add: int_F2)
  also have "... < (1/epsilon) * 2 * rho"
    using F2_int by (intro ennreal_lessI) (auto simp add: divide_simps)
  also have "... = d"
    unfolding epsilon_def by auto
  finally have *: "emeasure M {x\<in>space M. real_cond_exp M Invariants F2 x \<ge> epsilon} < d"
    by simp

  define G2 where "G2 = {x \<in> G. real_cond_exp M Invariants F2 x < epsilon}"
  have [measurable]: "G2 \<in> sets M" unfolding G2_def by simp
  have "1 = emeasure M G"
    using `emeasure M G = 1` by simp
  also have "... \<le> emeasure M (G2 \<union> {x\<in>space M. real_cond_exp M Invariants F2 x \<ge> epsilon})"
    apply (rule emeasure_mono) unfolding G2_def using sets.sets_into_space[OF `G \<in> sets M`] by auto
  also have "... \<le> emeasure M G2 + emeasure M {x\<in>space M. real_cond_exp M Invariants F2 x \<ge> epsilon}"
    by (rule emeasure_subadditive, auto)
  also have "... < emeasure M G2 + d"
    using * by auto
  finally have "1 - d < emeasure M G2"
    using emeasure_eq_measure \<open>d \<le> 1\<close> by (auto intro!: ennreal_less_iff[THEN iffD2] simp del: ennreal_plus simp add: ennreal_plus[symmetric])

  have "upper_Banach_density {n. \<exists>l \<in> {k..n}. u n x - u (n-l) x \<le> - d * l} < d"
    if "x \<in> G2" for x
  proof -
    have "x \<in> G" using `x \<in> G2` unfolding G2_def by auto
    have "{n. \<exists>l \<in> {k..n}. u n x - u (n-l) x \<le> - d * l} \<subseteq> U x \<union> V x"
      unfolding U_def V_def by fastforce
    then have "upper_Banach_density {n. \<exists>l \<in> {k..n}. u n x - u (n-l) x \<le> - d * l} \<le> upper_Banach_density (U x \<union> V x)"
      by (rule upper_Banach_density_subset)
    also have "... \<le> upper_Banach_density (U x) + upper_Banach_density (V x)"
      by (rule upper_Banach_density_union)
    also have "... \<le> (2/d) * real_cond_exp M Invariants F2 x"
      using densU[OF `x \<in> G`] densV[OF `x \<in> G`] by auto
    also have "... < (2/d) * epsilon"
      using `x \<in> G2` unfolding G2_def by (simp add: divide_simps)
    text {*This is where the choice of $\rho$ at the beginning of the proof is relevant:
    we choose it so that the above term is at most $d$.*}
    also have "... = d" unfolding epsilon_def rho_def by auto
    finally show ?thesis by simp
  qed
  then have "G2 \<subseteq> {x \<in> space M. upper_Banach_density {n. \<exists>l \<in> {k..n}. u n x - u (n-l) x \<le> - d * l} < d}"
    using sets.sets_into_space[OF `G2 \<in> sets M`] by blast
  then have "emeasure M G2 \<le> emeasure M {x \<in> space M. upper_Banach_density {n. \<exists>l \<in> {k..n}. u n x - u (n-l) x \<le> - d * l} < d}"
    by (rule emeasure_mono, auto)
  then have "emeasure M {x \<in> space M. upper_Banach_density {n. \<exists>l \<in> {k..n}. u n x - u (n-l) x \<le> - d * l} < d} > 1 -d"
    using `emeasure M G2 > 1 - d` by auto
  then show ?thesis by blast
qed

text {*The two previous lemmas are put together in the following lemma,
corresponding to Lemma 2.3 in [GK]*}

lemma upper_density_delta:
  fixes d::real
  assumes "d > 0" "d \<le> 1"
  shows "\<exists>delta::nat\<Rightarrow>real. (\<forall>l. delta l > 0) \<and> (delta \<longlonglongrightarrow> 0) \<and>
        emeasure M {x \<in> space M. \<forall>(N::nat). card {n \<in>{..<N}. \<exists>l \<in> {1..n}. u n x - u (n-l) x \<le> - delta l * l} \<le> d * N} > 1 - d"
proof -
  define d2 where "d2 = d/2"
  have [simp]: "d2 > 0" unfolding d2_def using assms by simp
  have "d2/2 > 0" by simp
  obtain c0 where c0: "c0> (0::real)" "emeasure M {x \<in> space M. upper_Banach_density {n. \<exists>l \<in> {1..n}. u n x - u (n-l) x \<le> - c0 * l} < d2/2} > 1 - (d2/2)"
    using upper_density_all_times[OF `d2/2 > 0`] by blast
  have "\<exists>N. emeasure M {x \<in> space M. \<forall>n \<ge> N. card ({n. \<exists>l \<in> {1..n}. u n x - u (n-l) x \<le> - c0 * l} \<inter> {..<n}) < (d2/2) * n} > 1 - (d2/2)"
    apply (rule upper_density_eventually_measure) using c0(2) by auto
  then obtain N1 where N1: "emeasure M {x \<in> space M. \<forall>B \<ge> N1. card ({n. \<exists>l \<in> {1..n}. u n x - u (n-l) x \<le> - c0 * l} \<inter> {..<B}) < (d2/2) * B} > 1 - (d2/2)"
    by blast
  define O1 where "O1 = {x \<in> space M. \<forall>B \<ge> N1. card ({n. \<exists>l \<in> {1..n}. u n x - u (n-l) x \<le> - c0 * l} \<inter> {..<B}) < (d2/2) * B}"
  have [measurable]: "O1 \<in> sets M" unfolding O1_def by auto
  have "emeasure M O1 > 1 - (d2/2)" unfolding O1_def using N1 by auto

  have *: "\<exists>N. emeasure M {x \<in> space M. \<forall>B \<ge> N. card({n. \<exists>l \<in> {N..n}. u n x - u (n-l) x \<le> - e * l} \<inter> {..<B}) < e * B} > 1 - e"
    if "e>0" "e \<le> 1" for e::real
  proof -
    obtain k where k: "emeasure M {x \<in> space M. upper_Banach_density {n. \<exists>l \<in> {k..n}. u n x - u (n-l) x \<le> - e * l} < e} > 1 - e"
      using upper_density_large_k[OF `e>0` \<open>e \<le> 1\<close>] by blast
    then obtain N0 where N0: "emeasure M {x \<in> space M. \<forall>B \<ge> N0. card({n. \<exists>l \<in> {k..n}. u n x - u (n-l) x \<le> - e * l} \<inter> {..<B}) < e * B} > 1 - e"
      using upper_density_eventually_measure[OF _ k] by auto
    define N where "N = max k N0"
    have "emeasure M {x \<in> space M. \<forall>B \<ge> N0. card({n. \<exists>l \<in> {k..n}. u n x - u (n-l) x \<le> - e * l} \<inter> {..<B}) < e * B}
            \<le> emeasure M {x \<in> space M. \<forall>B \<ge> N. card({n. \<exists>l \<in> {N..n}. u n x - u (n-l) x \<le> - e * l} \<inter> {..<B}) < e * B}"
    proof (rule emeasure_mono, auto)
      fix x B assume H: "x \<in> space M" "\<forall>B\<ge>N0. card ({n. \<exists>l\<in>{k..n}. u n x - u (n - l) x \<le> - (e * real l)} \<inter> {..<B}) < e * B" "N \<le> B"

      have "card({n. \<exists>l \<in> {N..n}. u n x - u (n-l) x \<le> - (e * real l)} \<inter> {..<B}) \<le> card({n. \<exists>l \<in> {k..n}. u n x - u (n-l) x \<le> -(e * real l)} \<inter> {..<B})"
        unfolding N_def by (rule card_mono, auto)
      then have "real(card({n. \<exists>l \<in> {N..n}. u n x - u (n-l) x \<le> - (e * real l)} \<inter> {..<B})) \<le> card({n. \<exists>l \<in> {k..n}. u n x - u (n-l) x \<le> -(e * real l)} \<inter> {..<B})"
        by simp
      also have "... < e * B" using H(2) `B\<ge>N` unfolding N_def by auto
      finally show "card ({n. \<exists>l\<in>{N..n}. u n x - u (n - l) x \<le> - (e * real l)} \<inter> {..<B}) < e * B"
        by auto
    qed
    then have "emeasure M {x \<in> space M. \<forall>B \<ge> N. card({n. \<exists>l \<in> {N..n}. u n x - u (n-l) x \<le> - e * l} \<inter> {..<B}) < e * B} > 1 - e"
      using N0 by simp
    then show ?thesis by auto
  qed

  define Ne where "Ne = (\<lambda>(e::real). SOME N. emeasure M {x \<in> space M. \<forall>B \<ge> N. card({n. \<exists>l \<in> {N..n}. u n x - u (n-l) x \<le> - e * l} \<inter> {..<B}) < e * B} > 1 - e)"
  have Ne: "emeasure M {x \<in> space M. \<forall>B \<ge> Ne e. card({n. \<exists>l \<in> {Ne e..n}. u n x - u (n-l) x \<le> - e * l} \<inter> {..<B}) < e * B} > 1 - e"
    if "e>0" "e \<le> 1" for e::real
  unfolding Ne_def by (rule someI_ex[OF *[OF that]])
  define eps where "eps = (\<lambda>(n::nat). d2 * (1/2)^n)"
  have [simp]: "eps n > 0" for n unfolding eps_def by auto
  then have [simp]: "eps n \<ge> 0" for n by (rule less_imp_le)

  have "eps n \<le> (1 / 2) * 1" for n
    unfolding eps_def d2_def
    using \<open>d \<le> 1\<close> by (intro mult_mono power_le_one) auto
  also have "\<dots> < 1" by auto
  finally have [simp]: "eps n < 1" for n by simp
  then have [simp]: "eps n \<le> 1" for n by (rule less_imp_le)

  have "(\<lambda>n. d2 * (1/2)^n) \<longlonglongrightarrow> d2 * 0"
    by (rule tendsto_mult, auto simp add: LIMSEQ_realpow_zero)
  then have "eps \<longlonglongrightarrow> 0" unfolding eps_def by auto

  define Nf where "Nf = (\<lambda>N. (if (N = 0) then 0
                else if (N = 1) then N1 + 1
                else max (N1+1) (Max {Ne(eps n)|n. n \<le> N}) + N))"
  {
    fix N::nat
    consider "N=0" | "N=1" | "N>1" by fastforce
    then have "Nf N < Nf (N+1)"
    proof (cases)
      assume "N>1"
      have "Max {Ne (eps n) |n. n \<le> N} \<le> Max {Ne (eps n) |n. n \<le> Suc N}"
        by (rule Max_mono, auto)
      then show ?thesis unfolding Nf_def by auto
    qed (auto simp add: Nf_def)
  }
  then have "subseq Nf"
    using subseq_Suc_iff by auto

  define On where "On = (\<lambda>(N::nat).
    (if (N=1) then O1
    else {x \<in> space M. \<forall>B \<ge> Nf N. card({n. \<exists>l \<in> {Nf N..n}. u n x - u (n-l) x \<le> - (eps N) * l} \<inter> {..<B}) < (eps N) * B}))"
  have [measurable]: "On N \<in> sets M" for N unfolding On_def by auto
  have "emeasure M (On N) > 1 - eps N" if "N>0" for N
  proof -
    consider "N=1" | "N>1" using `N>0` by linarith
    then show ?thesis
    proof (cases)
      case 1
      then show ?thesis unfolding On_def eps_def using `emeasure M O1 > 1 - (d2/2)` by auto
    next
      case 2
      have "Ne (eps N) \<le> Max {Ne(eps n)|n. n \<le> N}"
        by (rule Max.coboundedI, auto)
      also have "... \<le> Nf N" unfolding Nf_def using `N>1` by auto
      finally have "Ne (eps N) \<le> Nf N" by simp
      have "1 - eps N < emeasure M {x \<in> space M. \<forall>B \<ge> Ne(eps N). card({n. \<exists>l \<in> {Ne(eps N)..n}. u n x - u (n-l) x \<le> - (eps N) * l} \<inter> {..<B}) < (eps N) * B}"
        by (rule Ne) simp_all
      also have "... \<le> emeasure M {x \<in> space M. \<forall>B \<ge> Nf N. card({n. \<exists>l \<in> {Nf N..n}. u n x - u (n-l) x \<le> - (eps N) * l} \<inter> {..<B}) < (eps N) * B}"
      proof (rule emeasure_mono, auto)
        fix x n assume H: "x \<in> space M"
                          "\<forall>n\<ge>Ne (eps N). card ({n. \<exists>l\<in>{Ne (eps N)..n}. u n x - u (n - l) x \<le> - (eps N * l)} \<inter> {..<n}) < eps N * n"
                          "Nf N \<le> n"
        have "card({n. \<exists>l \<in> {Nf N..n}. u n x - u (n-l) x \<le> - (eps N * l)} \<inter> {..<n}) \<le> card({n. \<exists>l \<in> {Ne(eps N)..n}. u n x - u (n-l) x \<le> -(eps N) * l} \<inter> {..<n})"
          apply (rule card_mono) using `Ne (eps N) \<le> Nf N` by auto
        then have "real(card({n. \<exists>l \<in> {Nf N..n}. u n x - u (n-l) x \<le> - (eps N * l)} \<inter> {..<n})) \<le> card({n. \<exists>l \<in> {Ne(eps N)..n}. u n x - u (n-l) x \<le> -(eps N) * l} \<inter> {..<n})"
          by simp
        also have "... < (eps N) * n" using H(2) `n \<ge> Nf N` `Ne (eps N) \<le> Nf N` by auto
        finally show "real (card ({n. \<exists>l\<in>{Nf N..n}. u n x - u (n - l) x \<le> - (eps N * l)} \<inter> {..<n})) < eps N * real n"
          by auto
      qed
      also have "... = emeasure M (On N)"
        unfolding On_def using `N>1` by auto
      finally show ?thesis by simp
    qed
  qed
  then have *: "emeasure M (On (N+1)) > 1 - eps (N+1)" for N by simp

  define Ogood where "Ogood = (\<Inter>N. On (N+1))"
  have [measurable]: "Ogood \<in> sets M" unfolding Ogood_def by auto
  have "emeasure M Ogood \<ge> 1 - (\<Sum>N. eps(N+1))"
    unfolding Ogood_def
    apply (rule emeasure_intersection)
    apply simp
    apply simp
    apply (simp add: eps_def summable_mult summable_divide summable_geometric)
    using * apply (simp add: less_imp_le)
    done
  moreover have "(\<Sum>N. eps(N+1)) = d2"
    unfolding eps_def
    apply (subst suminf_mult)
    apply (simp, rule summable_divide, rule summable_geometric, simp)
    using sums_unique[OF power_half_series, symmetric] by auto
  finally have "emeasure M Ogood \<ge> 1 - d2" by simp
  then have "emeasure M Ogood > 1 - d" unfolding d2_def using `d>0` \<open>d \<le> 1\<close>
    by (simp add: emeasure_eq_measure real_sum_of_halves ennreal_less_iff)

  have Ogood_union: "Ogood = (\<Union>(K::nat). Ogood \<inter> {x \<in> space M. \<forall>n \<in> {1..Nf 1}. \<forall>l \<in> {1..n}. u n x - u (n-l) x > - (real K * l)})"
  apply auto using sets.sets_into_space[OF `Ogood \<in> sets M`] apply blast
  proof -
    fix x
    define M where "M = Max {abs(u n x - u (n-l) x)/l | n l. n \<in> {1..Nf 1} \<and> l \<in> {1..n}}"
    obtain N::nat where "N > M" using reals_Archimedean2 by blast

    have "finite { (n, l) | n l. n \<in> {1..Nf 1} \<and> l \<in> {1..n}}"
      by (rule finite_subset[where ?B= "{1.. Nf 1} \<times> {1..Nf 1}"], auto)
    moreover have "{abs(u n x - u (n-l) x)/l | n l. n \<in> {1..Nf 1} \<and> l \<in> {1..n}}
      = (\<lambda> (n, l). abs(u n x - u (n-l) x)/l)` { (n, l) | n l. n \<in> {1..Nf 1} \<and> l \<in> {1..n}}"
      by auto
    ultimately have fin: "finite {abs(u n x - u (n-l) x)/l | n l. n \<in> {1..Nf 1} \<and> l \<in> {1..n}}"
      by auto
    {
      fix n l assume nl: "n \<in> {1..Nf 1} \<and> l \<in> {1..n}"
      then have "real l>0" by simp
      have "abs(u n x - u (n-l) x)/l \<le> M"
        unfolding M_def apply (rule Max_ge) using fin nl by auto
      then have "abs(u n x - u (n-l) x)/l < real N" using `N>M` by simp
      then have "abs(u n x - u (n-l) x)< real N * l" using \<open>0 < real l\<close> pos_divide_less_eq by blast
      then have "u n x - u (n-l) x > - (real N * l)" by simp
    }
    then have "\<forall>n\<in>{Suc 0..Nf (Suc 0)}. \<forall>l\<in>{Suc 0..n}. - (real N * real l) < u n x - u (n - l) x"
      by auto
    then show "\<exists>N. \<forall>n\<in>{Suc 0..Nf (Suc 0)}. \<forall>l\<in>{Suc 0..n}. - (real N * real l) < u n x - u (n - l) x"
      by auto
  qed
  have "(\<lambda>K. emeasure M (Ogood \<inter> {x \<in> space M. \<forall>n \<in> {1..Nf 1}. \<forall>l \<in> {1..n}. u n x - u (n-l) x > - (real K * l)}))
    \<longlonglongrightarrow> emeasure M (\<Union>(K::nat). Ogood \<inter> {x \<in> space M. \<forall>n \<in> {1..Nf 1}. \<forall>l \<in> {1..n}. u n x - u (n-l) x > - (real K * l)})"
    apply (rule Lim_emeasure_incseq, auto)
    unfolding incseq_def apply auto
    proof -
      fix m n x na l
      assume "m \<le> (n::nat)" "\<forall>n\<in>{Suc 0..Nf (Suc 0)}. \<forall>l\<in>{Suc 0..n}. - (real m * real l) < u n x - u (n - l) x"
             "Suc 0 \<le> l" "l \<le> na" "na \<le> Nf (Suc 0)"
      then have "- (real m * real l) < u na x - u (na - l) x" by auto
      moreover have "- (real n * real l) \<le> - (real m * real l)" using `m \<le> n` by (simp add: mult_mono)
      ultimately show "- (real n * real l) < u na x - u (na - l) x" by auto
    qed
  moreover have "emeasure M (\<Union>(K::nat). Ogood \<inter> {x \<in> space M. \<forall>n \<in> {1..Nf 1}. \<forall>l \<in> {1..n}. u n x - u (n-l) x > - (real K * l)}) > 1 - d"
    using Ogood_union `emeasure M Ogood > 1 - d` by auto
  ultimately have a: "eventually (\<lambda>K. emeasure M (Ogood \<inter> {x \<in> space M. \<forall>n \<in> {1..Nf 1}. \<forall>l \<in> {1..n}. u n x - u (n-l) x > - (real K * l)}) > 1 - d) sequentially"
    by (rule order_tendstoD(1))
  have b: "eventually (\<lambda>K. K \<ge> max c0 d2) sequentially"
    using eventually_at_top_linorder nat_ceiling_le_eq by blast
  have "eventually (\<lambda>K. K \<ge> max c0 d2 \<and> emeasure M (Ogood \<inter> {x \<in> space M. \<forall>n \<in> {1..Nf 1}. \<forall>l \<in> {1..n}. u n x - u (n-l) x > - (real K * l)}) > 1 - d) sequentially"
    by (rule eventually_elim2[OF a b], auto)
  then obtain K where K: "K\<ge>max c0 d2" "emeasure M (Ogood \<inter> {x \<in> space M. \<forall>n \<in> {1..Nf 1}. \<forall>l \<in> {1..n}. u n x - u (n-l) x > - (real K * l)}) > 1 - d"
    using eventually_False_sequentially eventually_elim2 by blast

  define Og where "Og = Ogood \<inter> {x \<in> space M. \<forall>n \<in> {1..Nf 1}. \<forall>l \<in> {1..n}. u n x - u (n-l) x > - (real K * l)}"
  have [measurable]: "Og \<in> sets M" unfolding Og_def by simp
  have "emeasure M Og > 1 - d" unfolding Og_def using K by simp

  have fin: "finite {N. Nf N \<le> n}" for n
    using pseudo_inverse_finite_set[OF filterlim_subseq[OF `subseq Nf`]] by auto
  define prev_N where "prev_N = (\<lambda>n. Max {N. Nf N \<le> n})"
  define delta where "delta = (\<lambda>l. if (prev_N l \<le> 1) then K else eps (prev_N l))"
  have "\<forall>l. delta l > 0"
    unfolding delta_def using `K\<ge>max c0 d2` `c0>0` by auto

  have "LIM n sequentially. prev_N n :> at_top"
    unfolding prev_N_def apply (rule tendsto_at_top_pseudo_inverse2)
    using `subseq Nf` by (simp add: filterlim_subseq)
  then have "eventually (\<lambda>l. prev_N l > 1) sequentially"
    by (simp add: eventually_gt_at_top filterlim_iff)
  then have "eventually (\<lambda>l. delta l = eps(prev_N l)) sequentially"
    unfolding delta_def by (simp add: eventually_mono)
  moreover have "(\<lambda>l. eps(prev_N l)) \<longlonglongrightarrow> 0"
    by (rule filterlim_compose[OF `eps \<longlonglongrightarrow> 0` `LIM n sequentially. prev_N n :> at_top`])
  ultimately have "delta \<longlonglongrightarrow> 0" by (simp add: filterlim_cong)

  have "delta n \<le> K" for n
  proof -
    have *: "d2 * (1 / 2) ^ prev_N n \<le> real K * 1"
      apply (rule mult_mono') using `K \<ge> max c0 d2` `d2>0` by (auto simp add: power_le_one less_imp_le)
    then show ?thesis unfolding delta_def apply auto unfolding eps_def using * by auto
  qed

  define bad_times where "bad_times = (\<lambda>x. {n \<in> {Nf 1..}. \<exists>l\<in>{1..n}. u n x - u (n-l) x \<le> - (c0 * l)} \<union>
                      (\<Union>N\<in>{2..}. {n \<in> {Nf N..}. \<exists>l \<in> {Nf N..n}. u n x - u (n-l) x \<le> - (eps N * l)}))"
  have card_bad_times: "card (bad_times x \<inter> {..<B}) \<le> d2 * B" if "x \<in> Og" for x B
  proof -
    have "(\<Sum>N\<in>{..<B}. (1/(2::real))^N) \<le> (\<Sum>N. (1/2)^N)"
      by (rule setsum_le_suminf, auto simp add: summable_geometric)
    also have "... = 2" using suminf_geometric[of "1/(2::real)"] by auto
    finally have *: "(\<Sum>N\<in>{..<B}. (1/(2::real))^N) \<le> 2" by simp

    have "(\<Sum> N \<in> {2..<B}. eps N * B) \<le> (\<Sum> N \<in> {2..<B+2}. eps N * B)"
      by (rule setsum_mono2, auto)
    also have "... = (\<Sum>N\<in>{2..<B+2}. d2 * (1/2)^N * B)"
      unfolding eps_def by auto
    also have "... = (\<Sum>N\<in>{..<B}. d2 * (1/2)^(N+2) * B)"
      by (rule setsum.reindex_bij_betw[symmetric],rule bij_betw_byWitness[where ?f' = "\<lambda>i. i-2"], auto)
    also have "... = (\<Sum>N\<in>{..<B}. (d2 * (1/4) * B) * (1/2)^N)"
      by (auto, metis (lifting) mult.commute mult.left_commute)
    also have "... = (d2 * (1/4) * B) * (\<Sum>N\<in>{..<B}. (1/2)^N)"
      by (rule setsum_distrib_left[symmetric])
    also have "... \<le> (d2 * (1/4) * B) * 2"
      apply (rule mult_left_mono) using * `d2 > 0` apply auto
      by (metis \<open>0 < d2\<close> mult_eq_0_iff mult_le_0_iff not_le of_nat_eq_0_iff of_nat_le_0_iff)
    finally have I: "(\<Sum> N \<in> {2..<B}. eps N * B) \<le> d2/2 * B"
      by auto

    have "x \<in> On 1" using `x \<in> Og` unfolding Og_def Ogood_def by auto
    then have "x \<in> O1" unfolding On_def by auto
    have B1: "real(card({n \<in> {Nf 1..}. \<exists>l\<in>{1..n}. u n x - u (n-l) x \<le> - (c0 * l)} \<inter> {..<B})) \<le> (d2/2) * B" for B
    proof (cases "B \<ge> N1")
      case True
      have "card({n \<in> {Nf 1..}. \<exists>l\<in>{1..n}. u n x - u (n-l) x \<le> - (c0 * l)} \<inter> {..<B})
        \<le> card({n. \<exists>l\<in>{1..n}. u n x - u (n-l) x \<le> - (c0 * l)} \<inter> {..<B})"
        by (rule card_mono, auto)
      also have "... \<le> (d2/2) * B"
        using `x \<in> O1` unfolding O1_def using True by auto
      finally show ?thesis by auto
    next
      case False
      then have "B < Nf 1" unfolding Nf_def by auto
      then have "{n \<in> {Nf 1..}. \<exists>l\<in>{1..n}. u n x - u (n-l) x \<le> - (c0 * l)} \<inter> {..<B} = {}"
        by auto
      then have "card ({n \<in> {Nf 1..}. \<exists>l\<in>{1..n}. u n x - u (n-l) x \<le> - (c0 * l)} \<inter> {..<B}) = 0"
        by auto
      also have "... \<le> (d2/2) * B"
        by (metis \<open>0 < d2 / 2\<close> divide_le_eq div_0 linordered_field_class.sign_simps(24) of_nat_0 of_nat_0_le_iff)
      finally show ?thesis by simp
    qed

    have BN: "real(card ({n \<in> {Nf N..}. \<exists>l \<in> {Nf N..n}. u n x - u (n-l) x \<le> - (eps N * l)} \<inter> {..<B})) \<le> eps N * B" if "N \<ge> 2" for N B
    proof -
      have "x \<in> On ((N-1) + 1)" using `x \<in> Og` unfolding Og_def Ogood_def by auto
      then have "x \<in> On N" using `N\<ge>2` by auto
      show ?thesis
      proof (cases "B \<ge> Nf N")
        case True
        have "card ({n \<in> {Nf N..}. \<exists>l \<in> {Nf N..n}. u n x - u (n-l) x \<le> - (eps N * l)} \<inter> {..<B}) \<le>
          card ({n. \<exists>l \<in> {Nf N..n}. u n x - u (n-l) x \<le> - (eps N * l)} \<inter> {..<B})"
          by (rule card_mono, auto)
        also have "... \<le> eps N * B"
          using `x \<in> On N` `N\<ge>2` True unfolding On_def by auto
        finally show ?thesis by simp
      next
        case False
        then have "{n \<in> {Nf N..}. \<exists>l \<in> {Nf N..n}. u n x - u (n-l) x \<le> - (eps N * l)} \<inter> {..<B} = {}"
          by auto
        then have "card ({n \<in> {Nf N..}. \<exists>l \<in> {Nf N..n}. u n x - u (n-l) x \<le> - (eps N * l)} \<inter> {..<B}) = 0"
          by auto
        also have "... \<le> eps N * B"
          by (metis \<open>\<And>n. 0 < eps n\<close> le_less mult_eq_0_iff mult_pos_pos of_nat_0 of_nat_0_le_iff)
        finally show ?thesis by simp
      qed
    qed

    {
      fix N assume "N \<ge> B"
      have "Nf N \<ge> B" using seq_suble[OF `subseq Nf`, of N] `N \<ge> B` by simp
      then have "{Nf N..} \<inter> {..<B} = {}" by auto
      then have "{n \<in> {Nf N..}. \<exists>l \<in> {Nf N..n}. u n x - u (n-l) x \<le> - (eps N * l)} \<inter> {..<B} = {}" by auto
    }
    then have *: "(\<Union>N\<in>{B..}. {n \<in> {Nf N..}. \<exists>l \<in> {Nf N..n}. u n x - u (n-l) x \<le> - (eps N * l)} \<inter> {..<B}) = {}"
      by auto

    have "{2..} \<subseteq> {2..<B} \<union> {B..}" by auto
    then have "(\<Union>N\<in>{2..}. {n \<in> {Nf N..}. \<exists>l \<in> {Nf N..n}. u n x - u (n-l) x \<le> - (eps N * l)} \<inter> {..<B})
      \<subseteq> (\<Union>N\<in>{2..<B}. {n \<in> {Nf N..}. \<exists>l \<in> {Nf N..n}. u n x - u (n-l) x \<le> - (eps N * l)} \<inter> {..<B})
        \<union> (\<Union>N\<in>{B..}. {n \<in> {Nf N..}. \<exists>l \<in> {Nf N..n}. u n x - u (n-l) x \<le> - (eps N * l)} \<inter> {..<B})"
      by auto
    also have "... = (\<Union>N\<in>{2..<B}. {n \<in> {Nf N..}. \<exists>l \<in> {Nf N..n}. u n x - u (n-l) x \<le> - (eps N * l)} \<inter> {..<B})"
      using * by auto
    finally have *: "bad_times x \<inter> {..<B} \<subseteq> {n \<in> {Nf 1..}. \<exists>l\<in>{1..n}. u n x - u (n-l) x \<le> - (c0 * l)} \<inter> {..<B}
            \<union> (\<Union>N\<in>{2..<B}. {n \<in> {Nf N..}. \<exists>l \<in> {Nf N..n}. u n x - u (n-l) x \<le> - (eps N * l)} \<inter> {..<B})"
      unfolding bad_times_def by auto
    have "card(bad_times x \<inter> {..<B}) \<le> card({n \<in> {Nf 1..}. \<exists>l\<in>{1..n}. u n x - u (n-l) x \<le> - (c0 * l)} \<inter> {..<B}
        \<union> (\<Union>N\<in>{2..<B}. {n \<in> {Nf N..}. \<exists>l \<in> {Nf N..n}. u n x - u (n-l) x \<le> - (eps N * l)} \<inter> {..<B}))"
      by (rule card_mono[OF _ *], auto)
    also have "... \<le> card({n \<in> {Nf 1..}. \<exists>l\<in>{1..n}. u n x - u (n-l) x \<le> - (c0 * l)} \<inter> {..<B}) +
      card (\<Union>N\<in>{2..<B}. {n \<in> {Nf N..}. \<exists>l \<in> {Nf N..n}. u n x - u (n-l) x \<le> - (eps N * l)} \<inter> {..<B})"
      by (rule card_Un_le)
    also have "... \<le> card({n \<in> {Nf 1..}. \<exists>l\<in>{1..n}. u n x - u (n-l) x \<le> - (c0 * l)} \<inter> {..<B}) +
      (\<Sum> N\<in>{2..<B}. card ({n \<in> {Nf N..}. \<exists>l \<in> {Nf N..n}. u n x - u (n-l) x \<le> - (eps N * l)} \<inter> {..<B}))"
      by (simp del: UN_simps, rule card_finite_union, auto)
    finally have "real (card(bad_times x \<inter> {..<B})) \<le>
      real(card({n \<in> {Nf 1..}. \<exists>l\<in>{1..n}. u n x - u (n-l) x \<le> - (c0 * l)} \<inter> {..<B})
      + (\<Sum> N\<in>{2..<B}. card ({n \<in> {Nf N..}. \<exists>l \<in> {Nf N..n}. u n x - u (n-l) x \<le> - (eps N * l)} \<inter> {..<B})))"
      by (subst of_nat_le_iff, simp)
    also have "... = real(card({n \<in> {Nf 1..}. \<exists>l\<in>{1..n}. u n x - u (n-l) x \<le> - (c0 * l)} \<inter> {..<B}))
      + (\<Sum> N\<in>{2..<B}. real(card ({n \<in> {Nf N..}. \<exists>l \<in> {Nf N..n}. u n x - u (n-l) x \<le> - (eps N * l)} \<inter> {..<B})))"
      by auto
    also have "... \<le> (d2/2 * B) + (\<Sum> N\<in>{2..<B}. real(card ({n \<in> {Nf N..}. \<exists>l \<in> {Nf N..n}. u n x - u (n-l) x \<le> - (eps N * l)} \<inter> {..<B})))"
      using B1 by simp
    also have "... \<le> (d2/2 * B) + (\<Sum> N \<in> {2..<B}. eps N * B)"
      apply (simp, rule setsum_mono) using BN by auto
    also have "... \<le> (d2/2 * B) + (d2/2*B)"
      using I by auto
    finally show ?thesis by simp
  qed

  have ineq_on_Og: "u n x - u (n-l) x > - delta l * l" if "l \<in> {1..n}" "n \<notin> bad_times x" "x \<in> Og" for n x l
  proof -
    consider "n < Nf 1" | "n \<ge> Nf 1 \<and> prev_N l \<le> 1" | "n \<ge> Nf 1 \<and> prev_N l \<ge> 2" by linarith
    then show ?thesis
    proof (cases)
      assume "n < Nf 1"
      then have "{N. Nf N \<le> n} = {0}"
        apply auto using `subseq Nf` unfolding subseq_def
        apply (metis le_trans less_Suc0 less_imp_le_nat linorder_neqE_nat not_less)
        unfolding Nf_def by auto
      then have "prev_N n = 0" unfolding prev_N_def by auto
      moreover have "prev_N l \<le> prev_N n"
        unfolding prev_N_def apply (rule Max_mono) using `l \<in> {1..n}` fin apply auto
        unfolding Nf_def by auto
      ultimately have "prev_N l = 0" using `prev_N l \<le> prev_N n` by auto
      then have "delta l = K" unfolding delta_def by auto
      have "1 \<notin> {N. Nf N \<le> n}" using fin[of n]
        by (metis (full_types) Max_ge \<open>prev_N n = 0\<close> fin not_one_le_zero prev_N_def)
      then have "n < Nf 1" by auto
      moreover have "n \<ge> 1" using `l \<in> {1..n}` by auto
      ultimately have "n \<in> {1..Nf 1}" by auto
      then have "u n x - u (n-l) x > - (real K * l)" using `x \<in> Og` unfolding Og_def using `l \<in> {1..n}` by auto
      then show ?thesis using `delta l = K` by auto
    next
      assume H: "n \<ge> Nf 1 \<and> prev_N l \<le> 1"
      then have "delta l = K" unfolding delta_def by auto
      have "n \<notin> {n \<in> {Nf 1..}. \<exists>l\<in>{1..n}. u n x - u (n-l) x \<le> - (c0 * l)}"
        using `n \<notin> bad_times x` unfolding bad_times_def by auto
      then have "u n x - u (n-l) x > - (c0 * l)"
        using H `l \<in> {1..n}` by force
      moreover have "- (c0 * l) \<ge> - (real K * l)" using K(1) by (simp add: mult_mono)
      ultimately show ?thesis using `delta l = K` by auto
    next
      assume H: "n \<ge> Nf 1 \<and> prev_N l \<ge> 2"
      define N where "N = prev_N l"
      have "N \<ge> 2" unfolding N_def using H by auto
      have "prev_N l \<in> {N. Nf N \<le> l}"
        unfolding prev_N_def apply (rule Max_in, auto simp add: fin)
        unfolding Nf_def by auto
      then have "Nf N \<le> l" unfolding N_def by auto
      then have "Nf N \<le> n" using `l \<in> {1..n}` by auto
      have "n \<notin> {n \<in> {Nf N..}. \<exists>l \<in> {Nf N..n}. u n x - u (n-l) x \<le> - (eps N * l)}"
        using `n \<notin> bad_times x` `N\<ge>2` unfolding bad_times_def by auto
      then have "u n x - u (n-l) x > - (eps N * l)"
        using `Nf N \<le> n` `Nf N \<le> l` `l \<in> {1..n}` by force
      moreover have "eps N = delta l" unfolding delta_def N_def using H by auto
      ultimately show ?thesis by auto
    qed
  qed

  have "Og \<subseteq> {x \<in> space M. \<forall>(B::nat). card {n \<in>{..<B}. \<exists>l \<in> {1..n}. u n x - u (n-l) x \<le> - delta l * l} \<le> d * B}"
  proof (auto)
    fix x assume "x \<in> Og"
    then show "x \<in> space M" unfolding Og_def by auto
  next
    fix x B assume "x \<in> Og"
    have *: "{n. n < B \<and> (\<exists>l\<in>{Suc 0..n}. u n x - u (n - l) x \<le> - (delta l * real l))} \<subseteq> bad_times x \<inter> {..<B}"
      using ineq_on_Og `x\<in>Og` by force
    have "card {n. n < B \<and> (\<exists>l\<in>{Suc 0..n}. u n x - u (n - l) x \<le> - (delta l * real l))} \<le> card (bad_times x \<inter> {..<B})"
      apply (rule card_mono, simp) using * by auto
    also have "... \<le> d2 * B" using card_bad_times `x \<in> Og` by auto
    also have "... \<le> d * B" unfolding d2_def using `d>0` by auto
    finally show "card {n. n < B \<and> (\<exists>l\<in>{Suc 0..n}. u n x - u (n - l) x \<le> - (delta l * real l))} \<le> d * B"
      by simp
  qed
  then have "emeasure M Og \<le> emeasure M {x \<in> space M. \<forall>(B::nat). card {n \<in>{..<B}. \<exists>l \<in> {1..n}. u n x - u (n-l) x \<le> - delta l * l} \<le> d * B}"
    by (rule emeasure_mono, auto)
  then have "emeasure M {x \<in> space M. \<forall>(B::nat). card {n \<in>{..<B}. \<exists>l \<in> {1..n}. u n x - u (n-l) x \<le> - delta l * l} \<le> d * B} > 1-d"
    using `emeasure M Og > 1 - d` by auto
  then show ?thesis using `delta \<longlonglongrightarrow> 0` `\<forall>l. delta l > 0` by auto
qed

text {*We go back to the natural time direction, by using the previous result for the inverse map
and the inverse subcocycle, and a change of variables argument. The price to pay is that the
estimates we get are weaker: we have a control on a set of upper Banach density close to $1$, while
having a set of lower Banach density close to $1$ as before would be stronger. This will
nevertheless be sufficient for our purposes below.*}

lemma upper_density_good_direction_invertible:
  assumes "invertible_qmpt"
          "d>(0::real)" "d \<le> 1"
  shows "\<exists>delta::nat\<Rightarrow>real. (\<forall>l. delta l > 0) \<and> (delta \<longlonglongrightarrow> 0) \<and>
        emeasure M {x \<in> space M. upper_Banach_density {n. \<forall>l \<in> {1..n}. u n x - u (n-l) ((T^^l) x) > - delta l * l} \<ge> 1-d} \<ge> ennreal(1-d)"
proof -
  interpret I: Gouezel_Karlsson_Kingman M Tinv "(\<lambda>n x. u n ((Tinv^^n) x))"
  proof
    show "Tinv \<in> quasi_measure_preserving M M"
      using Tinv_qmpt[OF `invertible_qmpt`] unfolding qmpt_def qmpt_axioms_def by simp
    show "Tinv \<in> measure_preserving M M"
      using Tinv_mpt[OF `invertible_qmpt`] unfolding mpt_def mpt_axioms_def by simp
    show "mpt.subcocycle M Tinv (\<lambda>n x. u n ((Tinv ^^ n) x))"
      using subcocycle_u_Tinv[OF subu `invertible_qmpt`] by simp
    show "- \<infinity> < subcocycle_avg_ereal (\<lambda>n x. u n ((Tinv ^^ n) x))"
      using subcocycle_avg_ereal_Tinv[OF subu `invertible_qmpt`] subu_fin by simp
    show "AE x in M. fmpt.subcocycle_lim M Tinv (\<lambda>n x. u n ((Tinv ^^ n) x)) x = 0"
      using subcocycle_lim_Tinv[OF subu `invertible_qmpt`] subu_0 by auto
  qed
  have bij: "bij T" using `invertible_qmpt` unfolding invertible_qmpt_def by simp

  define e where "e = d * d / 2"
  have "e>0" "e\<le>1" unfolding e_def using `d>0` `d \<le> 1`
    by (auto, meson less_imp_le mult_left_le one_le_numeral order_trans)
  obtain delta::"nat \<Rightarrow> real" where d: "\<And>l. delta l > 0"
                                       "delta \<longlonglongrightarrow> 0"
        "emeasure M {x \<in> space M. \<forall>N.
        card {n \<in> {..<N}. \<exists>l\<in>{1..n}. u n ((Tinv ^^ n) x) - u (n - l) ((Tinv ^^ (n - l)) x) \<le> - delta l * real l} \<le> e * real N}
        > 1-e"
    using I.upper_density_delta[OF `e>0` `e\<le>1`] by blast

  define S where "S = {x \<in> space M. \<forall>N.
          card {n \<in> {..<N}. \<exists>l\<in>{1..n}. u n ((Tinv ^^ n) x) - u (n - l) ((Tinv ^^ (n - l)) x) \<le> - delta l * real l} \<le> e * real N}"
  have [measurable]: "S \<in> sets M" unfolding S_def by auto
  have "emeasure M S > 1 - e" unfolding S_def using d(3) by simp

  define Og where "Og = (\<lambda>n. {x \<in> space M. \<forall>l\<in>{1..n}. u n ((Tinv ^^ n) x) - u (n - l) ((Tinv ^^ (n - l)) x) > - delta l * real l})"
  have [measurable]: "Og n \<in> sets M" for n unfolding Og_def by auto
  define Pg where "Pg = (\<lambda>n. {x \<in> space M. \<forall>l\<in>{1..n}. u n x - u (n - l) ((T^^l) x) > - delta l * real l})"
  have [measurable]: "Pg n \<in> sets M" for n unfolding Pg_def by auto

  define Bad where "Bad = (\<lambda>i::nat. {x \<in> space M. \<forall>N\<ge>i. card {n \<in> {..<N}. x \<in> Pg n} \<le> (1-d) * real N})"
  have [measurable]: "Bad i \<in> sets M" for i unfolding Bad_def by auto
  then have "range Bad \<subseteq> sets M" by auto
  have "incseq Bad"
    unfolding Bad_def incseq_def by auto
  have inc: "{x \<in> space M. upper_Banach_density {n. \<forall>l \<in> {1..n}. u n x - u (n-l) ((T^^l) x) > - delta l * l} < 1-d}
        \<subseteq> (\<Union>i. Bad i)"
  proof
    fix x assume H: "x \<in> {x \<in> space M. upper_Banach_density {n. \<forall>l \<in> {1..n}. u n x - u (n-l) ((T^^l) x) > - delta l * l} < 1-d}"
    then have "x \<in> space M" by simp
    define A where "A = {n. \<forall>l \<in> {1..n}. u n x - u (n-l) ((T^^l) x) > - delta l * l}"
    have "upper_Banach_density A < 1-d" using H unfolding A_def by simp
    then have "\<exists>i. \<forall>N\<ge>i. card (A \<inter> {..<N}) \<le> (1-d)* real N"
      using upper_Banach_density_event1[of A "1-d"] by (metis (no_types, lifting) eventually_sequentially less_imp_le)
    then obtain i where "card (A \<inter> {..<N}) \<le> (1-d)* real N" if "N\<ge>i" for N by blast
    moreover have "A \<inter> {..<N} = {n. n<N \<and> (\<forall>l \<in> {1..n}. u n x - u (n-l) ((T^^l) x) > - delta l * l)}" for N
      unfolding A_def by auto
    ultimately have "x \<in> Bad i" unfolding Bad_def Pg_def using `x \<in> space M`
      by auto
    then show "x \<in> (\<Union>i. Bad i)" by blast
  qed

  have "emeasure M (Og n) \<le> emeasure M (Pg n)" for n
  proof -
    have *: "(T^^n)-`(Og n) \<inter> space M \<subseteq> Pg n" for n
    proof
      fix x assume x: "x \<in> (T^^n)-`(Og n) \<inter> space M"
      define y where "y = (T^^n) x"
      then have "y \<in> Og n" using x by auto
      have "y \<in> space M" using sets.sets_into_space[OF `Og n \<in> sets M`] `y \<in> Og n` by auto
      have "x = (Tinv^^n) y"
        unfolding y_def Tinv_def using inv_fn_o_fn_is_id[OF bij, of n] by (metis comp_apply)
      {
        fix l assume "l \<in> {1..n}"
        have "(T^^l) x = (T^^l) ((Tinv^^l) ((Tinv^^(n-l))y))"
          apply (subst `x = (Tinv^^n) y`) using funpow_add[of l "n-l" Tinv] \<open>l \<in> {1..n}\<close> by fastforce
        then have *: "(T^^l) x = (Tinv^^(n-l)) y"
          unfolding Tinv_def using fn_o_inv_fn_is_id[OF bij] by (metis comp_apply)
        then have "u n x - u (n-l) ((T^^l) x) = u n ((Tinv^^n) y) - u (n-l) ((Tinv^^(n-l)) y)"
          using `x = (Tinv^^n) y` by auto
        also have "... > - delta l * real l"
          using `y \<in> Og n` `l \<in> {1..n}` unfolding Og_def by auto
        finally have "u n x - u (n-l) ((T^^l) x) > - delta l * real l" by simp
      }
      then show "x \<in> Pg n"
        unfolding Pg_def using x by auto
    qed
    have "emeasure M (Og n) = emeasure M ((T^^n)-`(Og n) \<inter> space M)"
      using T_vrestr_same_emeasure(2) unfolding vimage_restr_def by auto
    also have "... \<le> emeasure M (Pg n)"
      apply (rule emeasure_mono) using * by auto
    finally show ?thesis by simp
  qed

  {
    fix N::nat assume "N \<ge> 1"
    have I: "card {n\<in>{..<N}. x \<in> Og n} \<ge> (1-e) * real N" if "x \<in> S" for x
    proof -
      have "x \<in> space M" using `x \<in> S` sets.sets_into_space[OF `S \<in> sets M`] by auto
      have a: "real (card {n. n < N \<and> (\<exists>l\<in>{Suc 0..n}. u n ((Tinv ^^ n) x) - u (n - l) ((Tinv ^^ (n - l)) x) \<le> - (delta l * real l))}) \<le> e * real N"
        using `x \<in> S` unfolding S_def by auto
      have *: "{n. n < N} = {n. n < N \<and> (\<exists>l\<in>{Suc 0..n}. u n ((Tinv ^^ n) x) - u (n - l) ((Tinv ^^ (n - l)) x) \<le> - (delta l * real l))}
              \<union> {n. n < N \<and> x \<in> Og n}" unfolding Og_def using `x \<in> space M`
        by (auto, meson atLeastAtMost_iff linorder_not_le)
      have "N = card {n. n < N}" by auto
      also have "... = card {n. n < N \<and> (\<exists>l\<in>{Suc 0..n}. u n ((Tinv ^^ n) x) - u (n - l) ((Tinv ^^ (n - l)) x) \<le> - (delta l * real l))}
              + card {n. n < N \<and> x \<in> Og n}"
        apply (subst *, rule card_Un_disjoint) unfolding Og_def by auto
      ultimately have "real N \<le> e * real N + card {n. n < N \<and> x \<in> Og n}"
        using a by auto
      then show ?thesis
        by (auto simp add: algebra_simps)
    qed

    define m where "m = measure M (Bad N)"
    have "m \<ge> 0" "1-m \<ge> 0" unfolding m_def by auto

    have *: "1-e \<le> emeasure M S" using `emeasure M S > 1 - e` by auto
    have "ennreal((1-e) * ((1-e) * real N)) = ennreal(1-e) * ennreal((1-e) * real N)"
      apply (rule ennreal_mult) using `e \<le> 1` by auto
    also have "... \<le> emeasure M S * ennreal((1-e) * real N)"
      using mult_right_mono[OF *] by simp
    also have "... = (\<integral>\<^sup>+ x\<in>S. ((1-e) * real N) \<partial>M)"
      by (metis \<open>S \<in> events\<close> mult.commute nn_integral_cmult_indicator)
    also have "... \<le> (\<integral>\<^sup>+x \<in> S. ennreal(card {n\<in>{..<N}. x \<in> Og n}) \<partial>M)"
      apply (rule nn_integral_mono) using I unfolding indicator_def by (simp)
    also have "... \<le> (\<integral>\<^sup>+x \<in> space M. ennreal(card {n\<in>{..<N}. x \<in> Og n}) \<partial>M)"
      by (rule nn_set_integral_set_mono, simp only: sets.sets_into_space[OF `S \<in> sets M`])
    also have "... = (\<integral>\<^sup>+x. ennreal(card {n\<in>{..<N}. x \<in> Og n}) \<partial>M)"
      by (rule nn_set_integral_space)
    also have "... = (\<integral>\<^sup>+x. ennreal (\<Sum>n\<in>{..<N}. ((indicator (Og n) x)::nat)) \<partial>M)"
      apply (rule nn_integral_cong) using setsum_indicator_eq_card2[of "{..<N}" Og] by auto
    also have "... = (\<integral>\<^sup>+x. (\<Sum>n\<in>{..<N}. indicator (Og n) x) \<partial>M)"
      apply (rule nn_integral_cong, auto, simp only: setsum_ennreal[symmetric])
      by (metis ennreal_0 ennreal_eq_1 indicator_eq_1_iff indicator_simps(2) real_of_nat_indicator)
    also have "... = (\<Sum>n \<in>{..<N}. (\<integral>\<^sup>+x. (indicator (Og n) x) \<partial>M))"
      by (rule nn_integral_setsum, simp)
    also have "... = (\<Sum>n \<in>{..<N}. emeasure M (Og n))"
      by simp
    also have "... \<le> (\<Sum>n \<in>{..<N}. emeasure M (Pg n))"
      apply (rule setsum_mono) using `\<And>n. emeasure M (Og n) \<le> emeasure M (Pg n)` by simp
    also have "... = (\<Sum>n \<in>{..<N}. (\<integral>\<^sup>+x. (indicator (Pg n) x) \<partial>M))"
      by simp
    also have "... = (\<integral>\<^sup>+x. (\<Sum>n\<in>{..<N}. indicator (Pg n) x) \<partial>M)"
      by (rule nn_integral_setsum[symmetric], simp)
    also have "... = (\<integral>\<^sup>+x. ennreal (\<Sum>n\<in>{..<N}. ((indicator (Pg n) x)::nat)) \<partial>M)"
      apply (rule nn_integral_cong, auto, simp only: setsum_ennreal[symmetric])
      by (metis ennreal_0 ennreal_eq_1 indicator_eq_1_iff indicator_simps(2) real_of_nat_indicator)
    also have "... = (\<integral>\<^sup>+x. ennreal(card {n\<in>{..<N}. x \<in> Pg n}) \<partial>M)"
      apply (rule nn_integral_cong) using setsum_indicator_eq_card2[of "{..<N}" Pg] by auto
    also have "... = (\<integral>\<^sup>+x \<in> space M. ennreal(card {n\<in>{..<N}. x \<in> Pg n}) \<partial>M)"
      by (rule nn_set_integral_space[symmetric])
    also have "... = (\<integral>\<^sup>+x \<in> Bad N \<union> (space M - Bad N). ennreal(card {n\<in>{..<N}. x \<in> Pg n}) \<partial>M)"
      apply (rule nn_integral_cong) unfolding indicator_def by auto
    also have "... = (\<integral>\<^sup>+x \<in> Bad N. ennreal(card {n\<in>{..<N}. x \<in> Pg n}) \<partial>M)
                      + (\<integral>\<^sup>+x \<in> space M - Bad N. ennreal(card {n\<in>{..<N}. x \<in> Pg n}) \<partial>M)"
      by (rule nn_integral_disjoint_pair, auto)
    also have "... \<le> (\<integral>\<^sup>+x \<in> Bad N. ennreal((1-d) * real N) \<partial>M) + (\<integral>\<^sup>+x \<in> space M - Bad N. ennreal(real N) \<partial>M)"
      apply (rule add_mono)
      apply (rule nn_integral_mono, simp add: Bad_def indicator_def, auto)
      apply (rule nn_integral_mono, simp add: indicator_def, auto)
      using card_Collect_less_nat[of N] card_mono[of "{n. n < N}"] by (simp add: Collect_mono_iff)
    also have "... = ennreal((1-d) * real N) * emeasure M (Bad N) + ennreal(real N) * emeasure M (space M - Bad N)"
      by (simp add: nn_integral_cmult_indicator)
    also have "... = ennreal((1-d) * real N) * ennreal(m) + ennreal(real N) * ennreal(1-m)"
      unfolding m_def by (simp add: emeasure_eq_measure prob_compl)
    also have "... = ennreal((1-d) * real N * m + real N * (1-m))"
      using `m \<ge> 0` `1-m \<ge> 0` `d \<le> 1` ennreal_plus ennreal_mult by auto
    finally have "ennreal((1-e) * ((1-e) * real N)) \<le> ennreal((1-d) * real N * m + real N * (1-m))"
      by simp
    moreover have "(1-d) * real N * m + real N * (1-m) \<ge> 0"
      using `m \<ge> 0` `1-m \<ge> 0` `d \<le> 1` by auto
    ultimately have "(1-e) * ((1-e) * real N) \<le> (1-d) * real N * m + real N * (1-m)"
      using ennreal_le_iff by auto
    then have "0 \<le> (e * 2 - d * m - e * e) * real N"
      by (auto simp add: algebra_simps)
    then have "0 \<le> e * 2 - d * m - e * e"
      using `N \<ge> 1` by (simp add: zero_le_mult_iff)
    also have "... \<le> e * 2 - d * m"
      using `e > 0` by auto
    finally have "m \<le> e * 2 / d"
      using `d>0` by (auto simp add: algebra_simps divide_simps)
    then have "m \<le> d"
      unfolding e_def using `d>0` by (auto simp add: divide_simps)
    then have "emeasure M (Bad N) \<le> d"
      unfolding m_def by (simp add: emeasure_eq_measure ennreal_leI)
  }
  then have "emeasure M (\<Union>i. Bad i) \<le> d"
    using LIMSEQ_le_const2[OF Lim_emeasure_incseq[OF `range Bad \<subseteq> sets M` `incseq Bad`]] by auto
  then have "emeasure M {x \<in> space M. upper_Banach_density {n. \<forall>l \<in> {1..n}. u n x - u (n-l) ((T^^l) x) > - delta l * l} < 1-d} \<le> d"
    using emeasure_mono[OF inc, of M] by auto
  then have *: "measure M {x \<in> space M. upper_Banach_density {n. \<forall>l \<in> {1..n}. u n x - u (n-l) ((T^^l) x) > - delta l * l} < 1-d} \<le> d"
    using emeasure_eq_measure `d>0` by fastforce

  have "{x \<in> space M. upper_Banach_density {n. \<forall>l \<in> {1..n}. u n x - u (n-l) ((T^^l) x) > - delta l * l} \<ge> 1-d}
        = space M - {x \<in> space M. upper_Banach_density {n. \<forall>l \<in> {1..n}. u n x - u (n-l) ((T^^l) x) > - delta l * l} < 1-d}"
    by auto
  then have "measure M {x \<in> space M. upper_Banach_density {n. \<forall>l \<in> {1..n}. u n x - u (n-l) ((T^^l) x) > - delta l * l} \<ge> 1-d}
    = measure M (space M - {x \<in> space M. upper_Banach_density {n. \<forall>l \<in> {1..n}. u n x - u (n-l) ((T^^l) x) > - delta l * l} < 1-d})"
    by simp
  also have "... = measure M (space M)
    - measure M {x \<in> space M. upper_Banach_density {n. \<forall>l \<in> {1..n}. u n x - u (n-l) ((T^^l) x) > - delta l * l} < 1-d}"
    by (rule measure_Diff, auto)
  also have "... \<ge> 1 - d"
    using * prob_space by linarith
  finally have "emeasure M {x \<in> space M. upper_Banach_density {n. \<forall>l \<in> {1..n}. u n x - u (n-l) ((T^^l) x) > - delta l * l} \<ge> 1-d} \<ge> 1 - d"
    using emeasure_eq_measure by auto
  then show ?thesis using d(1) d(2) by blast
qed

text {*Now, we want to remove the invertibility assumption in the previous lemma. The idea is to
go to the natural extension of the system, use the result there and project it back.
However, if the system is not defined on a polish space, there is no reason why it should have
a natural extension, so we have first to project the original system on a polish space on which
the subcocycle is defined. This system is obtained by considering the joint distribution of the
subcocycle and all its iterates (this is indeed a polish system, as a space of functions from
$\mathbb{N}^2$ to $\mathbb{R}$).*}

lemma upper_density_good_direction:
  assumes "d>(0::real)" "d \<le> 1"
  shows "\<exists>delta::nat\<Rightarrow>real. (\<forall>l. delta l > 0) \<and> (delta \<longlonglongrightarrow> 0) \<and>
        emeasure M {x \<in> space M. upper_Banach_density {n. \<forall>l \<in> {1..n}. u n x - u (n-l) ((T^^l) x) > - delta l * l} \<ge> 1-d} \<ge> ennreal(1-d)"
proof -
  define U where "U = (\<lambda>x. (\<lambda>n. u n x))"
  define projJ where "projJ = (\<lambda>x. (\<lambda>n. U ((T^^n)x)))"
  define MJ where "MJ = (distr M borel (\<lambda>x. (\<lambda>n. U ((T^^n)x))))"
  define TJ::"(nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real)" where "TJ = nat_left_shift"
  have *: "mpt_factor projJ MJ TJ"
    unfolding projJ_def MJ_def TJ_def apply (rule fmpt_factor_projection)
    unfolding U_def by (rule measurable_coordinatewise_then_product, simp)
  interpret J: polish_pmpt MJ TJ
    unfolding projJ_def polish_pmpt_def apply (auto)
    apply (rule pmpt_factor) using * apply simp
    unfolding polish_pmpt_axioms_def MJ_def by auto
  have [simp]: "projJ \<in> measure_preserving M MJ" using mpt_factorE(1)[OF *] by simp
  then have [measurable]: "projJ \<in> measurable M MJ" by (simp add: measure_preservingE(1))

  text{*We define a subcocycle $uJ$ in the projection corresponding to the original
        subcocycle $u$ above. (With the natural definition, it is only a subcocycle almost
        everywhere.) We check that it shares most properties of $u$.*}

  define uJ::"nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> real) \<Rightarrow> real" where "uJ = (\<lambda>n x. x 0 n)"
  have [measurable]: "uJ n \<in> borel_measurable borel" for n
    unfolding uJ_def by (metis measurable_product_coordinates measurable_product_then_coordinatewise)
  moreover have "measurable borel borel = measurable MJ borel"
    apply (rule measurable_cong_sets) unfolding MJ_def by auto
  ultimately have [measurable]: "uJ n \<in> borel_measurable MJ" for n by fast
  have uJ_proj: "u n x = uJ n (projJ x)" for n x
    unfolding uJ_def projJ_def U_def by auto
  have uJ_int: "integrable MJ (uJ n)" for n
    apply (rule measure_preserving_preserves_integral'(1)[OF `projJ \<in> measure_preserving M MJ`])
    apply (subst uJ_proj[of n, symmetric]) using int_u[of n] by auto
  have uJ_int2: "(\<integral>x. uJ n x \<partial>MJ) = (\<integral>x. u n x \<partial>M)" for n
    unfolding uJ_proj
    apply (rule measure_preserving_preserves_integral'(2)[OF `projJ \<in> measure_preserving M MJ`])
    apply (subst uJ_proj[of n, symmetric]) using int_u[of n] by auto
  have uJ_AE: "AE x in MJ. uJ (n+m) x \<le> uJ n x + uJ m ((TJ^^n) x)" for m n
  proof -
    have "AE x in M. uJ (n+m) (projJ x) \<le> uJ n (projJ x) + uJ m (projJ ((T^^n) x))"
      unfolding uJ_proj[symmetric] using subcocycle_ineq[OF subu] by auto
    moreover have "AE x in M. projJ ((T^^n) x) = (TJ^^n) (projJ x)"
      using qmpt_factor_iterates[OF mpt_factor_is_qmpt_factor[OF *]] by auto
    ultimately have *: "AE x in M. uJ (n+m) (projJ x) \<le> uJ n (projJ x) + uJ m ((TJ^^n) (projJ x))"
      by auto
    show ?thesis
      apply (rule quasi_measure_preserving_AE'[OF measure_preserving_is_quasi_measure_preserving[OF `projJ \<in> measure_preserving M MJ`], OF *])
      by auto
  qed
  have uJ_0: "AE x in MJ. (\<lambda>n. uJ n x / n) \<longlonglongrightarrow> 0"
  proof -
    have "AE x in M. (\<lambda>n. u n x / n) \<longlonglongrightarrow> subcocycle_lim u x"
      by (rule kingman_theorem_nonergodic(1)[OF subu subu_fin])
    moreover have "AE x in M. subcocycle_lim u x = 0"
      using subu_0 by simp
    ultimately have *: "AE x in M. (\<lambda>n. uJ n (projJ x) / n) \<longlonglongrightarrow> 0"
      unfolding uJ_proj by auto
    show ?thesis
      apply (rule quasi_measure_preserving_AE'[OF measure_preserving_is_quasi_measure_preserving[OF `projJ \<in> measure_preserving M MJ`], OF *])
      by auto
  qed

  text {*Then, we go to the natural extension of $TJ$, to have an invertible system.*}

  define MI where "MI = J.natural_extension_measure"
  define TI where "TI = J.natural_extension_map"
  define projI where "projI = J.natural_extension_proj"
  interpret I: pmpt MI TI unfolding MI_def TI_def by (rule J.natural_extension(1))
  have "I.mpt_factor projI MJ TJ" unfolding projI_def
    using I.mpt_factorE(1) J.natural_extension(3) MI_def TI_def by auto
  then have [simp]: "projI \<in> measure_preserving MI MJ" using I.mpt_factorE(1) by auto
  then have [measurable]: "projI \<in> measurable MI MJ" by (simp add: measure_preservingE(1))
  have "I.invertible_qmpt"
    using J.natural_extension(2) MI_def TI_def by auto

  text {*We define a natural subcocycle $uI$ there, and check its properties.*}

  define uI where uI_proj: "uI = (\<lambda>n x. uJ n (projI x))"
  have [measurable]: "uI n \<in> borel_measurable MI" for n unfolding uI_proj by auto
  have uI_int: "integrable MI (uI n)" for n
    unfolding uI_proj by (rule measure_preserving_preserves_integral(1)[OF `projI \<in> measure_preserving MI MJ` uJ_int])
  have "(\<integral>x. uJ n x \<partial>MJ) = (\<integral>x. uI n x \<partial>MI)" for n
    unfolding uI_proj by (rule measure_preserving_preserves_integral(2)[OF `projI \<in> measure_preserving MI MJ` uJ_int])
  then have uI_int2: "(\<integral>x. uI n x \<partial>MI) = (\<integral>x. u n x \<partial>M)" for n
    using uJ_int2 by simp
  have uI_AE: "AE x in MI. uI (n+m) x \<le> uI n x + uI m (((TI)^^n) x)" for m n
  proof -
    have "AE x in MI. uJ (n+m) (projI x) \<le> uJ n (projI x) + uJ m (((TJ)^^n) (projI x))"
      apply (rule quasi_measure_preserving_AE[OF measure_preserving_is_quasi_measure_preserving[OF `projI \<in> measure_preserving MI MJ`]])
      using uJ_AE by auto
    moreover have "AE x in MI. ((TJ)^^n) (projI x) = projI (((TI)^^n) x)"
      using I.qmpt_factor_iterates[OF I.mpt_factor_is_qmpt_factor[OF `I.mpt_factor projI MJ TJ`]]
      by auto
    ultimately show ?thesis unfolding uI_proj by auto
  qed
  have uI_0: "AE x in MI. (\<lambda>n. uI n x / n) \<longlonglongrightarrow> 0"
    unfolding uI_proj
    apply (rule quasi_measure_preserving_AE[OF measure_preserving_is_quasi_measure_preserving[OF `projI \<in> measure_preserving MI MJ`]])
    using uJ_0 by simp

  text{*As $uI$ is only a subcocycle almost everywhere, we correct it to get a genuine subcocycle,
        to which we will apply Lemma \verb+upper_density_good_direction_invertible+.*}

  obtain vI where H: "I.subcocycle vI" "AE x in MI. \<forall>n. vI n x = uI n x"
    using I.subcocycle_AE[OF uI_AE uI_int] by blast
  have [measurable]: "\<And>n. vI n \<in> borel_measurable MI" "\<And>n. integrable MI (vI n)"
    using I.subcocycle_integrable[OF H(1)] by auto
  have "(\<integral>x. vI n x \<partial>MI) = (\<integral>x. uI n x \<partial>MI)" for n
    apply (rule integral_cong_AE) using H(2) by auto
  then have "(\<integral>x. vI n x \<partial>MI) = (\<integral>x. u n x \<partial>M)" for n
    using uI_int2 by simp
  then have "I.subcocycle_avg_ereal vI = subcocycle_avg_ereal u"
    unfolding I.subcocycle_avg_ereal_def subcocycle_avg_ereal_def by auto
  then have vI_fin: "I.subcocycle_avg_ereal vI > -\<infinity>" using subu_fin by simp
  have "AE x in MI. (\<lambda>n. vI n x / n) \<longlonglongrightarrow> 0"
    using uI_0 H(2) by auto
  moreover have "AE x in MI. (\<lambda>n. vI n x / n) \<longlonglongrightarrow> I.subcocycle_lim vI x"
    by (rule I.kingman_theorem_nonergodic(1)[OF H(1) vI_fin])
  ultimately have vI_0: "AE x in MI. I.subcocycle_lim vI x = 0"
    using LIMSEQ_unique by auto

  interpret GKK: Gouezel_Karlsson_Kingman MI TI vI
    apply standard
    using H(1) vI_fin vI_0 by auto
  obtain delta where delta: "\<And>l. delta l > 0" "delta \<longlonglongrightarrow> 0"
      "emeasure MI {x \<in> space MI. upper_Banach_density {n. \<forall>l\<in>{1..n}. - delta l * real l < vI n x - vI (n - l) ((TI ^^ l) x)} \<ge> 1 - d } \<ge> 1 - d"
    using GKK.upper_density_good_direction_invertible[OF `I.invertible_qmpt` `d>0` `d\<le>1`] by blast

  text{*Then, we need to go back to the original system, showing that the estimates for $TI$ carry
        over. First, we go to $TJ$.*}

  have BJ: "emeasure MJ {x \<in> space MJ. upper_Banach_density {n. \<forall>l\<in>{1..n}. - delta l * real l < uJ n x - uJ (n - l) ((TJ ^^ l) x)} \<ge> 1 - d } \<ge> 1 - d"
  proof -
    have *: "AE x in MI. uJ n (projI x) = vI n x" for n
      using uI_proj H(2) by auto
    have **: "AE x in MI. \<forall>n. uJ n (projI x) = vI n x"
      by (subst AE_all_countable, auto intro: *)
    have "AE x in MI. \<forall>m n. uJ n (projI ((TI^^m) x)) = vI n ((TI^^m) x)"
      by (rule I.T_AE_iterates[OF **])
    then have "AE x in MI. (\<forall>m n. uJ n (projI ((TI^^m) x)) = vI n ((TI^^m) x)) \<and> (\<forall>n. projI ((TI^^n) x) = (TJ^^n) (projI x))"
      using I.qmpt_factor_iterates[OF I.mpt_factor_is_qmpt_factor[OF `I.mpt_factor projI MJ TJ`]] by auto
    then obtain ZI where ZI: "\<And>x. x \<in> space MI - ZI \<Longrightarrow> (\<forall>m n. uJ n (projI ((TI^^m) x)) = vI n ((TI^^m) x)) \<and> (\<forall>n. projI ((TI^^n) x) = (TJ^^n) (projI x))"
                             "ZI \<in> null_sets MI"
      using AE_E3 by blast

    have *: "uJ n (projI x) - uJ (n - l) ((TJ ^^ l) (projI x)) = vI n x - vI (n - l) ((TI ^^ l) x)" if "x \<in> space MI - ZI" for x n l
    proof -
      have "(TI^^0) x = x" "(TJ^^0) (projI x) = (projI x)" by auto
      then show ?thesis using ZI(1)[OF that] by metis
    qed
    have "projI-`{x \<in> space MJ. upper_Banach_density {n. \<forall>l\<in>{1..n}. - delta l * real l < uJ n x - uJ (n - l) ((TJ ^^ l) x)} \<ge> 1 - d} \<inter> space MI - ZI
          = {x \<in> space MI - ZI. upper_Banach_density {n. \<forall>l\<in>{1..n}. - delta l * real l < uJ n (projI x) - uJ (n - l) ((TJ ^^ l) (projI x))} \<ge> 1 - d}"
      by (auto simp add: measurable_space[OF `projI \<in> measurable MI MJ`])
    also have "... = {x \<in> space MI - ZI. upper_Banach_density {n. \<forall>l\<in>{1..n}. - delta l * real l < vI n x - vI (n - l) ((TI ^^ l) x)} \<ge> 1 - d}"
      using * by auto
    also have "... = {x \<in> space MI. upper_Banach_density {n. \<forall>l\<in>{1..n}. - delta l * real l < vI n x - vI (n - l) ((TI ^^ l) x)} \<ge> 1 - d} - ZI"
      by auto
    finally have *: "projI-`{x \<in> space MJ. upper_Banach_density {n. \<forall>l\<in>{1..n}. - delta l * real l < uJ n x - uJ (n - l) ((TJ ^^ l) x)} \<ge> 1 - d} \<inter> space MI - ZI
      = {x \<in> space MI. upper_Banach_density {n. \<forall>l\<in>{1..n}. - delta l * real l < vI n x - vI (n - l) ((TI ^^ l) x)} \<ge> 1 - d} - ZI"
      by simp

    have "emeasure MJ {x \<in> space MJ. upper_Banach_density {n. \<forall>l\<in>{1..n}. - delta l * real l < uJ n x - uJ (n - l) ((TJ ^^ l) x)} \<ge> 1 - d}
          = emeasure MI (projI-`{x \<in> space MJ. upper_Banach_density {n. \<forall>l\<in>{1..n}. - delta l * real l < uJ n x - uJ (n - l) ((TJ ^^ l) x)} \<ge> 1 - d} \<inter> space MI)"
      by (rule measure_preservingE(2)[symmetric], auto)
    also have "... = emeasure MI ((projI-`{x \<in> space MJ. upper_Banach_density {n. \<forall>l\<in>{1..n}. - delta l * real l < uJ n x - uJ (n - l) ((TJ ^^ l) x)} \<ge> 1 - d} \<inter> space MI) - ZI)"
      by (rule emeasure_Diff_null_set[OF `ZI \<in> null_sets MI`, symmetric], measurable)
    also have "... = emeasure MI ({x \<in> space MI. upper_Banach_density {n. \<forall>l\<in>{1..n}. - delta l * real l < vI n x - vI (n - l) ((TI ^^ l) x)} \<ge> 1 - d} - ZI)"
      using * by simp
    also have "... = emeasure MI {x \<in> space MI. upper_Banach_density {n. \<forall>l\<in>{1..n}. - delta l * real l < vI n x - vI (n - l) ((TI ^^ l) x)} \<ge> 1 - d}"
      by (rule emeasure_Diff_null_set[OF `ZI \<in> null_sets MI`], measurable)
    also have "... \<ge> 1-d"
      using delta(3) by simp
    finally show ?thesis by simp
  qed

  text {*Then, we got back to $T$ with virtually the same argument.*}

  have "emeasure M {x \<in> space M. upper_Banach_density {n. \<forall>l\<in>{1..n}. - delta l * real l < u n x - u (n - l) ((T ^^ l) x)} \<ge> 1 - d } \<ge> 1 - d"
  proof -
      obtain Z where Z: "\<And>x. x \<in> space M - Z \<Longrightarrow> (\<forall>n. projJ ((T^^n) x) = (TJ^^n) (projJ x))"
                        "Z \<in> null_sets M"
      using AE_E3[OF qmpt_factor_iterates[OF mpt_factor_is_qmpt_factor[OF `mpt_factor projJ MJ TJ`]]] by blast

    have *: "uJ n (projJ x) - uJ (n - l) ((TJ ^^ l) (projJ x)) = u n x - u (n - l) ((T^^ l) x)" if "x \<in> space M - Z" for x n l
    proof -
      have "(T^^0) x = x" "(TJ^^0) (projJ x) = (projJ x)" by auto
      then show ?thesis using Z(1)[OF that] uJ_proj by metis
    qed
    have "projJ-`{x \<in> space MJ. upper_Banach_density {n. \<forall>l\<in>{1..n}. - delta l * real l < uJ n x - uJ (n - l) ((TJ ^^ l) x)} \<ge> 1 - d} \<inter> space M - Z
          = {x \<in> space M - Z. upper_Banach_density {n. \<forall>l\<in>{1..n}. - delta l * real l < uJ n (projJ x) - uJ (n - l) ((TJ ^^ l) (projJ x))} \<ge> 1 - d}"
      by (auto simp add: measurable_space[OF `projJ \<in> measurable M MJ`])
    also have "... = {x \<in> space M - Z. upper_Banach_density {n. \<forall>l\<in>{1..n}. - delta l * real l < u n x - u (n - l) ((T ^^ l) x)} \<ge> 1 - d}"
      using * by auto
    also have "... = {x \<in> space M. upper_Banach_density {n. \<forall>l\<in>{1..n}. - delta l * real l < u n x - u (n - l) ((T ^^ l) x)} \<ge> 1 - d} - Z"
      by auto
    finally have *: "projJ-`{x \<in> space MJ. upper_Banach_density {n. \<forall>l\<in>{1..n}. - delta l * real l < uJ n x - uJ (n - l) ((TJ ^^ l) x)} \<ge> 1 - d} \<inter> space M - Z
      = {x \<in> space M. upper_Banach_density {n. \<forall>l\<in>{1..n}. - delta l * real l < u n x - u (n - l) ((T ^^ l) x)} \<ge> 1 - d} - Z"
      by simp

    have "emeasure MJ {x \<in> space MJ. upper_Banach_density {n. \<forall>l\<in>{1..n}. - delta l * real l < uJ n x - uJ (n - l) ((TJ ^^ l) x)} \<ge> 1 - d}
        = emeasure M (projJ-`{x \<in> space MJ. upper_Banach_density {n. \<forall>l\<in>{1..n}. - delta l * real l < uJ n x - uJ (n - l) ((TJ ^^ l) x)} \<ge> 1 - d} \<inter> space M)"
      by (rule measure_preservingE(2)[symmetric], auto)
    also have "... = emeasure M ((projJ-`{x \<in> space MJ. upper_Banach_density {n. \<forall>l\<in>{1..n}. - delta l * real l < uJ n x - uJ (n - l) ((TJ ^^ l) x)} \<ge> 1 - d} \<inter> space M) - Z)"
      by (rule emeasure_Diff_null_set[OF `Z \<in> null_sets M`, symmetric], measurable)
    also have "... = emeasure M ({x \<in> space M. upper_Banach_density {n. \<forall>l\<in>{1..n}. - delta l * real l < u n x - u (n - l) ((T ^^ l) x)} \<ge> 1 - d} - Z)"
      using * by simp
    also have "... = emeasure M {x \<in> space M. upper_Banach_density {n. \<forall>l\<in>{1..n}. - delta l * real l < u n x - u (n - l) ((T ^^ l) x)} \<ge> 1 - d}"
      by (rule emeasure_Diff_null_set[OF `Z \<in> null_sets M`], measurable)
    finally show ?thesis using BJ by simp
  qed
  then show ?thesis using delta(1) delta(2) by auto
qed

text {*From the quantitative lemma above, we deduce the qualitative statement we are after,
still in the setting of the locale.*}

lemma infinite_AE:
  shows "AE x in M. \<exists>delta::nat\<Rightarrow>real. (\<forall>l. delta l > 0) \<and> (delta \<longlonglongrightarrow> 0) \<and>
          (infinite {n. \<forall>l \<in> {1..n}. u n x - u (n-l) ((T^^l) x) > - delta l * l})"
proof -
  have "\<exists>deltaf::real \<Rightarrow> nat \<Rightarrow> real. \<forall>d. ((d > 0 \<and> d \<le> 1) \<longrightarrow> ((\<forall>l. deltaf d l > 0) \<and> (deltaf d \<longlonglongrightarrow> 0) \<and>
        emeasure M {x \<in> space M. upper_Banach_density {n. \<forall>l \<in> {1..n}. u n x - u (n-l) ((T^^l) x) > - (deltaf d l) * l} \<ge> 1-d} \<ge> ennreal(1-d)))"
    apply (subst choice_iff'[symmetric]) using upper_density_good_direction by auto
  then obtain deltaf::"real \<Rightarrow> nat \<Rightarrow> real" where H: "\<And>d. d > 0 \<and> d \<le>1 \<Longrightarrow> (\<forall>l. deltaf d l > 0) \<and> (deltaf d \<longlonglongrightarrow> 0) \<and>
      emeasure M {x \<in> space M. upper_Banach_density {n. \<forall>l \<in> {1..n}. u n x - u (n-l) ((T^^l) x) > - (deltaf d l) * l} \<ge> 1-d} \<ge> ennreal(1-d)"
    by blast

  define U where "U = (\<lambda>d. {x \<in> space M. upper_Banach_density {n. \<forall>l \<in> {1..n}. u n x - u (n-l) ((T^^l) x) > - (deltaf d l) * l} \<ge> 1-d})"
  have [measurable]: "U d \<in> sets M" for d
    unfolding U_def by auto
  have *: "emeasure M (U d) \<ge> 1 - d" if "d>0 \<and> d\<le> 1" for d
    unfolding U_def using H that by auto
  define V where "V= (\<Union>n::nat. U (1/(n+2)))"
  have [measurable]: "V \<in> sets M"
    unfolding V_def by auto
  have a: "emeasure M V \<ge> 1 - 1 / (n + 2)" for n::nat
  proof -
    have "1 - 1 / (n + 2) = 1 - 1 / (real n + 2)"
      by auto
    also have "... \<le> emeasure M (U (1/(real n+2)))"
      using *[of "1 / (real n + 2)"] by auto
    also have "... \<le> emeasure M V"
      apply (rule Measure_Space.emeasure_mono) unfolding V_def by auto
    finally show ?thesis by simp
  qed
  have b: "(\<lambda>n::nat. 1 - 1 / (n + 2)) \<longlonglongrightarrow> ennreal(1 - 0)"
    by (rule tendsto_ennrealI, rule tendsto_diff, simp, rule LIMSEQ_ignore_initial_segment[OF lim_1_over_n])
  have "emeasure M V \<ge> 1 - 0"
    apply (rule Lim_bounded_ereal) using a b by auto
  then have "emeasure M V = 1"
    by (simp add: emeasure_ge_1_iff)
  then have "AE x in M. x \<in> V"
    by (simp add: emeasure_eq_measure prob_eq_1)
  moreover
  {
    fix x assume "x \<in> V"
    then obtain n::nat where "x \<in> U (1/(real n+2))" unfolding V_def by blast
    define d where "d = 1/(real n + 2)"
    have "0 < d" "d\<le>1" unfolding d_def by auto
    have "0 < 1-d" unfolding d_def by auto
    also have "... \<le> upper_Banach_density {n. \<forall>l \<in> {1..n}. u n x - u (n-l) ((T^^l) x) > - (deltaf d l) * l}"
      using `x \<in> U (1/(real n+2))` unfolding U_def d_def by auto
    finally have "infinite {n. \<forall>l \<in> {1..n}. u n x - u (n-l) ((T^^l) x) > - (deltaf d l) * l}"
      using upper_Banach_density_finite by force
    then have "\<exists>delta::nat\<Rightarrow>real. (\<forall>l. delta l > 0) \<and> (delta \<longlonglongrightarrow> 0) \<and>
          (infinite {n. \<forall>l \<in> {1..n}. u n x - u (n-l) ((T^^l) x) > - delta l * l})"
      using H `0 < d` `d\<le>1` by auto
  }
  ultimately show ?thesis by auto
qed

end

text {*Finally, we obtain the full statement, by reducing to the previous situation where the
asymptotic average vanishes.*}

theorem (in pmpt) Gouezel_Karlsson_Kingman:
  assumes "subcocycle u" "subcocycle_avg_ereal u > -\<infinity>"
  shows "AE x in M. \<exists>delta::nat\<Rightarrow>real. (\<forall>l. delta l > 0) \<and> (delta \<longlonglongrightarrow> 0) \<and>
          (infinite {n. \<forall>l \<in> {1..n}. u n x - u (n-l) ((T^^l) x) - l * subcocycle_lim u x > - delta l * l})"
proof -
  have [measurable]: "integrable M (u n)" "u n \<in> borel_measurable M" for n
    using subcocycle_integrable[OF assms(1)] by auto

  define v where "v = birkhoff_sum (\<lambda>x. -subcocycle_lim u x)"
  have int [measurable]: "integrable M (\<lambda>x. -subcocycle_lim u x)"
    using kingman_theorem_nonergodic(2)[OF assms] by auto
  have "subcocycle v" unfolding v_def
    apply (rule subcocycle_birkhoff)
    using assms `integrable M (\<lambda>x. -subcocycle_lim u x)` unfolding subcocycle_def by auto
  have "subcocycle_avg_ereal v > - \<infinity>"
    unfolding v_def using subcocycle_avg_ereal_birkhoff[OF int] kingman_theorem_nonergodic(2)[OF assms] by auto
  have "AE x in M. subcocycle_lim v x = real_cond_exp M Invariants (\<lambda>x. -subcocycle_lim u x) x"
    unfolding v_def by (rule subcocycle_lim_birkhoff[OF int])
  moreover have "AE x in M. real_cond_exp M Invariants (\<lambda>x. - subcocycle_lim u x) x = - subcocycle_lim u x"
    by (rule real_cond_exp_F_meas[OF int], auto)
  ultimately have AEv: "AE x in M. subcocycle_lim v x = - subcocycle_lim u x"
    by auto

  define w where "w = (\<lambda>n x. u n x + v n x)"
  have a: "subcocycle w"
    unfolding w_def by (rule subcocycle_add[OF assms(1) `subcocycle v`])
  have b: "subcocycle_avg_ereal w > -\<infinity>"
    unfolding w_def by (rule subcocycle_avg_add(1)[OF assms(1) `subcocycle v` assms(2) `subcocycle_avg_ereal v > - \<infinity>`])
  have "AE x in M. subcocycle_lim w x = subcocycle_lim u x + subcocycle_lim v x"
    unfolding w_def by (rule subcocycle_lim_add[OF assms(1) `subcocycle v` assms(2) `subcocycle_avg_ereal v > - \<infinity>`])
  then have c: "AE x in M. subcocycle_lim w x = 0"
    using AEv by auto

  interpret Gouezel_Karlsson_Kingman M T w
    apply standard using a b c by auto
  have "AE x in M. \<exists>delta::nat\<Rightarrow>real. (\<forall>l. delta l > 0) \<and> (delta \<longlonglongrightarrow> 0) \<and>
          (infinite {n. \<forall>l \<in> {1..n}. w n x - w (n-l) ((T^^l) x) > - delta l * l})"
    using infinite_AE by auto
  moreover
  {
    fix x assume H: "\<exists>delta::nat\<Rightarrow>real. (\<forall>l. delta l > 0) \<and> (delta \<longlonglongrightarrow> 0) \<and>
          (infinite {n. \<forall>l \<in> {1..n}. w n x - w (n-l) ((T^^l) x) > - delta l * l})"
            "x \<in> space M"
    have *: "v n x = - n * subcocycle_lim u x" for n
      unfolding v_def using birkhoff_sum_of_invariants[OF _ `x \<in> space M`] by auto
    have **: "v n ((T^^l) x) = - n * subcocycle_lim u x" for n l
    proof -
      have "v n ((T^^l) x) = - n * subcocycle_lim u ((T^^l) x)"
        unfolding v_def using birkhoff_sum_of_invariants[OF _ T_spaceM_stable(2)[OF `x \<in> space M`]] by auto
      also have "... = - n * subcocycle_lim u x"
        using Invariants_func_is_invariant_n[OF subcocycle_lim_meas_Inv(2) `x \<in> space M`] by auto
      finally show ?thesis by simp
    qed
    have "w n x - w (n-l) ((T^^l) x) = u n x - u (n-l) ((T^^l) x) - l * subcocycle_lim u x" if "l \<in> {1..n}" for n l
      unfolding w_def using *[of n] **[of "n-l" l] that apply (auto simp add: algebra_simps)
      by (metis comm_semiring_class.distrib diff_add_inverse nat_le_iff_add of_nat_add)
    then have "\<exists>delta::nat\<Rightarrow>real. (\<forall>l. delta l > 0) \<and> (delta \<longlonglongrightarrow> 0) \<and>
          (infinite {n. \<forall>l \<in> {1..n}. u n x - u (n-l) ((T^^l) x) - l * subcocycle_lim u x > - delta l * l})"
      using H(1) by auto
  }
  ultimately show ?thesis by auto
qed

end
