section \<open>Lambert Series\<close>
theory Lambert_Series
  imports
  "HOL-Complex_Analysis.Complex_Analysis"
  "HOL-Real_Asymp.Real_Asymp"
  "Dirichlet_Series.Dirichlet_Series_Analysis"
  "Dirichlet_Series.Divisor_Count"
  Polylog.Polylog
  Lambert_Series_Library
  Number_Theoretic_Functions_Extras
  Summation_Tests_More
begin

subsection \<open>Definition\<close>

(*<*)
no_notation Infinite_Set_Sum.abs_summable_on (infix "abs'_summable'_on" 50)
(*>*)

text \<open>
  Given any sequence $a(n)$ for $n \geq 1$, the corresponding \<^emph>\<open>Lambert series\<close> is defined as
  \[L(a, q) = \sum_{n=1}^\infty a(n) \frac{q^n}{1-q^n}\ .\]
\<close>
definition lambert :: "(nat \<Rightarrow> 'a :: {real_normed_field, banach}) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "lambert a q =
     (let f = (\<lambda>n. a (Suc n) * q ^ (Suc n) / (1 - q ^ (Suc n))) in
      if  summable f then \<Sum>n. f n else 0)"

lemma lambert_eqI:
  assumes "(\<lambda>n. a (Suc n) * q ^ (Suc n) / (1 - q ^ (Suc n))) sums x"
  shows   "lambert a q = x"
  using assms unfolding lambert_def Let_def sums_iff by simp

lemma lambert_cong [cong]:
  "(\<And>n. n > 0 \<Longrightarrow> a n = a' n) \<Longrightarrow> q = q' \<Longrightarrow> lambert a q = lambert a' q'"
  by (simp add: lambert_def)

lemma lambert_0 [simp]: "lambert a 0 = 0"
  by (simp add: lambert_def)

lemma lambert_0' [simp]: "lambert (\<lambda>_. 0) q = 0"
  by (simp add: lambert_def)

lemma lambert_cmult: "lambert (\<lambda>n. c * a n) q = c * lambert a q"
proof (cases "c = 0")
  case False
  define f where "f = (\<lambda>n. a (Suc n) * q ^ (Suc n) / (1 - q ^ (Suc n)))"
  show ?thesis
  proof (cases "summable f")
    case True
    hence "(\<lambda>n. c * (a (Suc n) * q ^ (Suc n) / (1 - q ^ (Suc n)))) sums (c * (\<Sum>n. f n))"
      unfolding mult.assoc by (intro sums_mult) (auto simp: f_def)
    thus ?thesis using True
      by (intro lambert_eqI) (auto simp: lambert_def f_def algebra_simps)
  next
    case False
    hence "\<not>summable (\<lambda>n. c * f n)"
      using \<open>c \<noteq> 0\<close> by simp
    with False show ?thesis
      by (simp add: lambert_def f_def algebra_simps)
  qed
qed auto

lemma lambert_cmult': "lambert (\<lambda>n. a n * c) q = lambert a q * c"
  using lambert_cmult[of c a q] by (simp add: mult_ac)

lemma lambert_uminus: "lambert (\<lambda>n. -a n) q = -lambert a q"
  using lambert_cmult[of "-1" a q] by simp


text \<open>
  We will later see that if $\sum_{n=1}^\infty a(n)$ exists then the Lambert series converges
  everywhere except on the unit circle; otherwise it has the same convergence radius as $a$
  (and that radius then has to be ${<}\,1$).
\<close>
definition lambert_conv_radius :: "(nat \<Rightarrow> 'a :: {banach, real_normed_field}) \<Rightarrow> ereal"
  where "lambert_conv_radius a = (if summable a then \<infinity> else conv_radius a)"

lemma lambert_conv_radius_gt_1_iff: "lambert_conv_radius a > 1 \<longleftrightarrow> summable a"
proof
  assume *: "lambert_conv_radius a > 1"
  {
    assume "\<not>summable a"
    hence "conv_radius a > 1"
      using * by (auto simp: lambert_conv_radius_def)
    hence "summable (\<lambda>n. a n * 1 ^ n)"
      by (intro summable_in_conv_radius) (auto simp: one_ereal_def)
    with \<open>\<not>summable a\<close> have False
      by simp
  }
  thus "summable a"
    by blast
qed (auto simp: lambert_conv_radius_def)


subsection \<open>Uniform convergence, continuity, holomorphicity\<close>

text \<open>
  We will now show some (uniform) convergence results for $L(a, q)$, which will then give us
  the holomorphicity and continuity of $L(a, q)$. We will also show some absolute summability
  results.
\<close>

context
  fixes a :: "nat \<Rightarrow> 'a :: {real_normed_field, banach}"
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> 'a" and A :: "'a"
  defines "f \<equiv> \<lambda>k q. a k * q ^ k / (1 - q ^ k)"
  defines "A \<equiv> (\<Sum>n. a (Suc n))"
begin

text \<open>
  Let $a(n)$ have convergence radius $r$. In discs of radius $\text{min}(1, r)$, the Lambert
  series for $a(n)$ converges uniformly. This is a simple application of Weierstraß's $M$ test.
\<close>
lemma uniform_limit_lambert1_aux:
  fixes r :: real
  assumes "0 < r" "r < min 1 (conv_radius a)"
  shows   "uniform_limit (ball 0 r) (\<lambda>n q. (\<Sum>k<n. f (Suc k) q)) (\<lambda>q. \<Sum>k. f (Suc k) q) sequentially"
proof -
  from assms have r: "r > 0" "r < 1" "r < conv_radius a"
    by auto
  show "uniform_limit (ball 0 r) (\<lambda>n q. (\<Sum>k<n. f (Suc k) q)) (\<lambda>q. \<Sum>k. f (Suc k) q) sequentially"
  proof (rule Weierstrass_m_test_ev)
    have "eventually (\<lambda>k. 1 - r ^ k \<ge> 1 / 2) at_top"
      using r by real_asymp
    hence "eventually (\<lambda>k. \<forall>q\<in>ball 0 r. norm (f k q) \<le> 2 * norm (a k) * r ^ k) at_top"
      using eventually_gt_at_top[of 0]
    proof eventually_elim
      case k: (elim k)
      show "\<forall>q\<in>ball 0 r. norm (f k q) \<le> 2 * norm (a k) * r ^ k"
      proof
        fix q :: 'a assume q: "q \<in> ball 0 r"
        have "norm (f k q) = norm (a k) * norm q ^ k / norm (1 - q ^ k)"
          by (simp add: f_def norm_mult norm_divide norm_power)
        also {
          have "1 / 2 \<le> 1 - r ^ k"
            using k by simp
          also have "\<dots> \<le> norm (1 :: 'a) - norm (q ^ k)"
            using q by (auto simp: norm_power intro!: power_mono)
          also have "\<dots> \<le> norm (1 - q ^ k)"
            by norm
          finally have "norm (1 - q ^ k) \<ge> 1 / 2" .
        }
        hence "norm (a k) * norm q ^ k / norm (1 - q ^ k) \<le> 
               norm (a k) * r ^ k / (1 / 2)"
          using q r k
          by (intro mult_mono power_mono frac_le)
             (auto intro!: mult_pos_pos simp: power_less_1_iff norm_power dest!: power_eq_1_iff)
        finally show "norm (f k q) \<le> 2 * norm (a k) * r ^ k"
          by simp
      qed
    qed
    thus "\<forall>\<^sub>F k in sequentially. \<forall>q\<in>ball 0 r. norm (f (Suc k) q) \<le> 2 * norm (a (Suc k)) * r ^ Suc k"
      by (rule eventually_compose_filterlim[OF _ filterlim_Suc])
  next
    have "summable (\<lambda>k. 2 * (norm (a (Suc k) * of_real r ^ Suc k)))"
      by (subst summable_Suc_iff, intro summable_mult abs_summable_in_conv_radius) (use r in auto)
    thus "summable (\<lambda>k. 2 * norm (a (Suc k)) * r ^ Suc k)"
      using \<open>r > 0\<close> by (simp add: norm_mult norm_power mult_ac)
  qed
qed

lemma uniform_limit_lambert1:
  fixes r :: real
  assumes "0 < r" "r < min 1 (conv_radius a)"
  shows   "uniform_limit (ball 0 r) (\<lambda>n q. (\<Sum>k<n. f (Suc k) q)) (lambert a) sequentially"
proof -
  have lim: "uniform_limit (ball 0 r) (\<lambda>n q. (\<Sum>k<n. f (Suc k) q)) (\<lambda>q. \<Sum>k. f (Suc k) q) sequentially"
    using assms by (rule uniform_limit_lambert1_aux)
  also have "?this \<longleftrightarrow> ?thesis"
  proof (intro uniform_limit_cong ballI allI refl always_eventually)
    fix q :: 'a assume q: "q \<in> ball 0 r"
    have *: "(\<lambda>n. a (Suc n) * q ^ Suc n / (1 - q ^ Suc n)) sums (\<Sum>k. f (Suc k) q)"
      using tendsto_uniform_limitI[OF lim q] unfolding f_def by (simp add: sums_def)
    show "(\<Sum>k. f (Suc k) q) = lambert a q"
      by (rule sym, rule lambert_eqI) (fact *)
  qed
  finally show ?thesis .
qed    

text \<open>
  Since $a_n \frac{q^n}{1-q^n} = -a_n - a_n\frac{(\frac{1}{q})^n}{1-(\frac{1}{q})^n}$,
  we can substitute $q \mapsto \frac{1}{q}$ in the above uniform convergence result to deduce
  that uniform convergence also holds on any annulus $r \leq |q| \leq R$ with $1 < r < R$.
\<close>
lemma uniform_limit_lambert2:
  fixes r R :: real
  assumes r: "1 < r" "r < R"
  assumes "summable a"
  defines "D \<equiv> cball 0 R - ball 0 r"
  shows   "uniform_limit D (\<lambda>n q. (\<Sum>k<n. f (Suc k) q)) (\<lambda>q. -A - lambert a (1 / q)) sequentially"
proof -
  define g where "g = (\<lambda>n q. a n * (1 / q) ^ n / (1 - (1 / q) ^ n))"
  from r(1) obtain r' where r': "1 < r'" "r' < r"
    using dense by blast
  have "uniform_limit D (\<lambda>n q. \<Sum>k<n. f (Suc k) (1 / q)) (\<lambda>q. lambert a (1 / q)) sequentially"
    using uniform_limit_lambert1
  proof (rule uniform_limit_compose[where g = "\<lambda>q. 1 / q"])
    have "conv_radius a \<ge> norm (of_real 1 :: 'a)"
      by (rule conv_radius_geI) (use \<open>summable a\<close> in auto)
    hence "min 1 (conv_radius a) = 1"
      by (simp add: min_def one_ereal_def)
    with r' show "1 / r' > 0" "ereal (1 / r') < min 1 (conv_radius a)"
      by auto
  next
    show "1 / q \<in> ball 0 (1 / r')" if "q \<in> D" for q
      using that r r' by (auto simp: D_def norm_divide divide_simps not_less)
  qed
  moreover have "summable (\<lambda>n. a (Suc n))"
    using \<open>summable a\<close> by (simp add: summable_Suc_iff)
  hence "(\<lambda>n. \<Sum>k<n. a (Suc k)) \<longlonglongrightarrow> A"
    unfolding A_def summable_sums_iff sums_def .
  ultimately have "uniform_limit D (\<lambda>n q. -(\<Sum>k<n. a (Suc k)) - (\<Sum>k<n. f (Suc k) (1/q)))
           (\<lambda>q. -A - lambert a (1 / q)) sequentially"
    by (intro uniform_limit_intros uniform_limit_const')
  also have "?this \<longleftrightarrow> ?thesis"
  proof (intro uniform_limit_cong refl always_eventually allI ballI)
    fix n :: nat and q :: 'a
    assume q: "q \<in> D"
    hence q': "q \<noteq> 0"
      using r by (auto simp: D_def)
    have q'': "q ^ k \<noteq> 1" if "k > 0" for k
      using q r that by (auto dest!: power_eq_1_iff simp: D_def)
    have "-(\<Sum>k<n. a (Suc k)) - (\<Sum>k<n. f (Suc k) (1 / q)) =
           (\<Sum>k<n. -a (Suc k) - f (Suc k) (1 / q))"
      by (simp add: sum_negf sum_subtractf)
    also have *: "-a k - f k (1 / q) = f k q" if "k > 0" for k
      using that q' q''[of k] by (auto simp: f_def field_simps)
    have "(\<Sum>k<n. -a (Suc k) - f (Suc k) (1 / q)) = (\<Sum>k<n. f (Suc k) q)"
      by (intro sum.cong refl *) auto
    finally show "-(\<Sum>k<n. a (Suc k)) - (\<Sum>k<n. f (Suc k) (1 / q)) = (\<Sum>k<n. f (Suc k) q)" .
  qed
  finally show ?thesis .
qed

text \<open>
  With some more book-keeping, we show that the series converges uniformly in all compact
  sets that do not touch the unit circle and, if $\sum_{n=1}^\infty a(n)$ does not exist,
  lie fully within the convergence radius of $a(n)$. This is mentioned in Knopp's Theorem~259.
\<close>
theorem uniform_limit_lambert:
  assumes "compact X" "X \<subseteq> eball 0 (lambert_conv_radius a) - sphere 0 1"
  shows   "uniform_limit X (\<lambda>n q. (\<Sum>k<n. f (Suc k) q)) (lambert a) sequentially"
proof -
  from assms have norm_neq_1: "norm x \<noteq> 1" if "x \<in> X" for x
    using that by auto
  have 1: "uniform_limit (X \<inter> cball 0 1) (\<lambda>n q. (\<Sum>k<n. f (Suc k) q)) (lambert a) sequentially"
  proof (cases "X \<inter> cball 0 1 \<subseteq> {0}")
    case True
    hence "X \<inter> cball 0 1 = {} \<or> X \<inter> cball 0 1 = {0}"
      by auto
    thus ?thesis
      by (elim disjE) (simp_all add: f_def lambert_def)
  next
    case False
    obtain r :: real
      where r: "r > 0" "r < 1" "r < conv_radius a" "\<And>x. x \<in> X \<inter> cball 0 1 \<Longrightarrow> norm x < r"
    proof -
      define c where "c = (if lambert_conv_radius a > 1 then 1
                           else real_of_ereal (lambert_conv_radius a))"
      have "compact ((ereal \<circ> norm) ` (X \<inter> cball 0 1))"
        by (intro compact_continuous_image continuous_intros compact_insert) (use assms in auto)
      hence "Sup ((ereal \<circ> norm) ` (X \<inter> cball 0 1)) \<in> (ereal \<circ> norm) ` (X \<inter> cball 0 1)"
        using False by (intro closed_contains_Sup_cl) (auto intro: compact_imp_closed)
      then obtain q where q: "q \<in> (X \<inter> cball 0 1)"
        "ereal (norm q) = Sup ((ereal \<circ> norm) ` (X \<inter> cball 0 1))"
        unfolding o_def by force
      have q': "norm q' \<le> norm q" if "q' \<in> X \<inter> cball 0 1" for q'
        using Sup_upper q that unfolding o_def by (metis ereal_less_eq(3) imageI insertCI)
      have "q \<noteq> 0"
        using q' False by force
      have "conv_radius a \<ge> norm (1 :: 'a)" if "summable a"
        by (rule conv_radius_geI) (use that in auto)
      hence "norm q < conv_radius a" "norm q < 1"
        using q(1) assms \<open>q \<noteq> 0\<close>
        by (auto simp: lambert_conv_radius_def eball_def ereal_le_less split: if_splits)
      then obtain r where r: "norm q < r" "r < 1" "r < conv_radius a"
        by (smt (verit, ccfv_SIG) ereal_dense2 ereal_less(3) less_ereal.simps(1) linorder_not_le order_less_le_trans)
      show ?thesis
      proof (rule that[of r])
        show "r > 0"
          using r q \<open>q \<noteq> 0\<close> by (smt (verit) norm_ge_zero)
        show "r < 1" "ereal r < conv_radius a"
          using r by auto
        show "norm q' < r" if "q' \<in> X \<inter> cball 0 1" for q'
          using assms q q' that \<open>q \<noteq> 0\<close> r
          by (force simp: lambert_conv_radius_def eball_def split: if_splits)
      qed
    qed
    have "uniform_limit (ball 0 r) (\<lambda>n q. (\<Sum>k<n. f (Suc k) q)) (lambert a) sequentially"
      by (rule uniform_limit_lambert1) (use r in auto)
    thus "uniform_limit (X \<inter> cball 0 1) (\<lambda>n q. (\<Sum>k<n. f (Suc k) q)) (lambert a) sequentially"
      by (rule uniform_limit_on_subset) (use r in auto)
  qed

  have 2: "uniform_limit (X - ball 0 1) (\<lambda>n q. (\<Sum>k<n. f (Suc k) q)) (lambert a) sequentially"
  proof (cases "\<exists>q\<in>X. norm q > 1")
    case False
    hence *: "X - ball 0 1 = {}"
      using norm_neq_1 by fastforce
    show ?thesis
      unfolding * by simp
  next
    case True
    then obtain q where q: "q \<in> X" "norm q > 1"
      by auto
    with assms have "lambert_conv_radius a > 1"
      by (smt (verit, ccfv_SIG) Diff_subset dist_0_norm ereal_less(3) in_eball_iff linorder_not_le order_less_le_trans subsetD)
    hence "summable a"
      by (simp add: lambert_conv_radius_gt_1_iff)
    obtain r where r: "r > 1" "\<And>x. x \<in> X - cball 0 1 \<Longrightarrow> norm x > r"
    proof -
      have compact: "compact (norm ` (X - ball 0 1))"
        by (intro compact_continuous_image compact_diff continuous_intros) (use assms in auto)
      hence "Inf (norm ` (X - ball 0 1)) \<in> norm ` (X - ball 0 1)"
        using q by (intro closed_contains_Inf)
                   (auto intro: compact_imp_closed bounded_imp_bdd_below compact_imp_bounded)
      then obtain q' where q': "q' \<in> X - ball 0 1" "norm q' = Inf (norm ` (X - ball 0 1))"
        by force
      have "norm q' > 1"
        using q' assms by auto
      then obtain r where r: "1 < r" "r < norm q'"
        using dense by blast

      show ?thesis
      proof (rule that[of r])
        show "r > 1"
          using q' assms r by auto
        show "norm q'' > r" if "q'' \<in> X - cball 0 1" for q''
        proof -
          have "r < Inf (norm ` (X - ball 0 1))"
            using r q' by simp
          also have "\<dots> \<le> norm q''"
            by (rule cInf_lower) 
               (use that assms compact in \<open>auto intro!: bounded_imp_bdd_below compact_imp_bounded\<close>)
          finally show ?thesis .
        qed
      qed
    qed

    obtain R where R: "R > r" "\<And>x. x \<in> X \<Longrightarrow> norm x < R"
    proof -
      have "bounded X"
        using assms compact_imp_bounded by blast
      then obtain R where R: "norm x \<le> R" if "x \<in> X" for x
        unfolding bounded_iff by blast
      show ?thesis
      proof (rule that[of "R + 1"])
        show "r < R + 1"
          using r(2)[of q] q R[of q] by auto
        show "norm x < R + 1" if "x \<in> X" for x
          using R[of x] that by auto
      qed
    qed

    have lim: "uniform_limit (cball 0 R - ball 0 r) (\<lambda>n q. (\<Sum>k<n. f (Suc k) q))
                (\<lambda>q. -A - lambert a (1 / q)) sequentially"
      by (rule uniform_limit_lambert2) (use r R \<open>summable a\<close> in auto)
    also have "?this \<longleftrightarrow> uniform_limit (cball 0 R - ball 0 r) (\<lambda>n q. (\<Sum>k<n. f (Suc k) q))
                           (lambert a) sequentially"
    proof (intro uniform_limit_cong refl always_eventually allI ballI)
      fix q :: 'a assume q: "q \<in> cball 0 R - ball 0 r"
      with lim have "(\<lambda>n. (\<Sum>k<n. f (Suc k) q)) \<longlonglongrightarrow> -A - lambert a (1 / q)"
        by (rule tendsto_uniform_limitI)
      hence "(\<lambda>k. f (Suc k) q) sums (-A - lambert a (1 / q))"
        by (simp add: sums_def)
      thus "-A - lambert a (1 / q) = lambert a q"
        unfolding lambert_def[of a q] by (simp add: sums_iff f_def)
    qed
    finally show ?thesis
      by (rule uniform_limit_on_subset) (use r R norm_neq_1 in force)+
  qed

  have "uniform_limit ((X \<inter> cball 0 1) \<union> (X - ball 0 1))
          (\<lambda>n q. (\<Sum>k<n. f (Suc k) q)) (lambert a) sequentially"
    using 1 2 by (rule uniform_limit_on_Un)
  also have "(X \<inter> cball 0 1) \<union> (X - ball 0 1) = X"
    using norm_neq_1 by auto
  finally show ?thesis .
qed

lemma sums_lambert:
  assumes "norm q < lambert_conv_radius a" "norm q \<noteq> 1"
  shows   "(\<lambda>k. f (Suc k) q) sums lambert a q"
proof -
  have "(\<lambda>n. (\<Sum>k<n. f (Suc k) q)) \<longlonglongrightarrow> lambert a q"
  proof (rule tendsto_uniform_limitI[OF uniform_limit_lambert])
    show "compact {q}" "{q} \<subseteq> eball 0 (lambert_conv_radius a) - sphere 0 1"
      using assms by auto
  qed auto
  thus ?thesis
    by (simp add: sums_def)
qed

text \<open>
  A side effect of this: the functional equation
  \[L(a, \tfrac{1}{q}) = -\big(\sum\nolimits_{n=1}^\infty a(n)\big) - L(a, q)\ ,\]
  which is valid for all $q$ with $q \neq 0$ and $|q| \neq 1$ if $\sum_{n=1}^\infty a(n)$ exists.
\<close>
theorem lambert_reciprocal:
  assumes "summable a" and "q \<noteq> 0" and "norm q \<noteq> 1"
  shows   "lambert a (1 / q) = -A - lambert a q"
proof -
  have *: "lambert a (1 / q) = -A - lambert a q" if q: "norm q > 1" for q
  proof -
    obtain r where r: "1 < r" "r < norm q"
      using q dense by blast
    have "uniform_limit (cball 0 (norm q + 1) - ball 0 r)
            (\<lambda>n q. \<Sum>k<n. f (Suc k) q)
            (\<lambda>q. - A - lambert a (1 / q)) sequentially"
      by (rule uniform_limit_lambert2) (use assms r in auto)
    hence "(\<lambda>k. f (Suc k) q) sums (-A - lambert a (1 / q))"
      unfolding sums_def by (rule tendsto_uniform_limitI) (use r in auto)
    moreover have "uniform_limit {q} (\<lambda>n q. \<Sum>k<n. f (Suc k) q) (lambert a) sequentially"
      using assms r
      by (intro uniform_limit_lambert compact_diff compact_cball)
         (auto simp: lambert_conv_radius_def)
    hence "(\<lambda>k. f (Suc k) q) sums lambert a q"
      unfolding sums_def by (rule tendsto_uniform_limitI) (use r in auto)
    ultimately show ?thesis
      by (simp add: sums_iff algebra_simps)
  qed

  show ?thesis
  proof (cases "norm q > 1")
    case False
    thus ?thesis using assms
      using *[of "1 / q"] by (auto simp: norm_divide)
  qed (use *[of q] in auto)
qed     

lemma summable_lambert:
  assumes "norm q < lambert_conv_radius a" "norm q \<noteq> 1"
  shows   "summable (\<lambda>k. f k q)"
  using sums_lambert[OF assms] unfolding sums_iff by (subst (asm) summable_Suc_iff) auto


text \<open>
  We have shown that the Lambert series for $a(n)$ converges everywhere except on the unit circle if
  $\sum_{n=1}^\infty a(n)$ exists, and it converges within the convergence radius of $R$ of $a(n)$
  otherwise.

  We will now show that within $\text{min}(1, R)$, this convergence is absolute.
\<close>
lemma norm_summable_lambert:
  assumes "norm q < min 1 (conv_radius a)"
  shows   "summable (\<lambda>k. norm (f k q))"
proof (cases "q = 0")
  case [simp]: True
  have "eventually (\<lambda>k. norm (f k q) = 0) at_top"
    using eventually_gt_at_top[of 0] by eventually_elim (auto simp: f_def)
  thus ?thesis
    using summable_cong by fastforce
next
  case False
  define R where "R = (if conv_radius a > 1 then 1 else real_of_ereal (conv_radius a))"
  have R: "ereal R = min 1 (conv_radius a)"
    using conv_radius_nonneg[of a] by (cases "conv_radius a") (auto simp: R_def)
  with assms have "norm q < R"
    by (metis less_ereal.simps(1))
  then obtain r where r: "norm q < r" "r < R"
    using dense by blast
  hence "r > 0"
    using norm_ge_zero le_less_trans by blast
  have "r < 1"
    using r R by (metis ereal_less(3) less_ereal.simps(1) min_less_iff_conj)
  have "r < conv_radius a"
    using r R by (metis less_ereal.simps(1) min_less_iff_conj)
  have "norm q < 1"
    using assms by auto
  note r' = \<open>r > 0\<close> \<open>r < 1\<close> \<open>r < conv_radius a\<close>
  show ?thesis
  proof (rule summable_powser_comparison_test_bigo)
    show "summable (\<lambda>n. a n * of_real r ^ n)"
      by (rule summable_in_conv_radius) (use r r' R in auto)
  next
    have "(\<lambda>n. norm (f n q)) = (\<lambda>n. norm (a n) * norm q ^ n / norm (1 - q ^ n))"
      by (simp add: f_def norm_mult norm_divide norm_power)
    also have "1 - norm q ^ n \<le> norm (1 - q ^ n)" for n
      by (metis norm_one norm_power norm_triangle_ineq2)
    hence "(\<lambda>n. norm (a n) * norm q ^ n / norm (1 - q ^ n)) \<in>
                 O(\<lambda>n. norm (a n) * (norm q ^ n / (1 - norm q ^ n)))"
      using \<open>q \<noteq> 0\<close> \<open>norm q < 1\<close>
      by (intro bigoI[of _ 1] eventually_mono[OF eventually_gt_at_top[of 0]])
         (auto intro!: mult_left_mono divide_left_mono mult_pos_pos add_pos_pos 
               dest!: power_eq_1_iff simp: power_le_one power_less_1_iff)
    also have "(\<lambda>n. norm (a n) * (norm q ^ n / (1 - norm q ^ n))) \<in> O(\<lambda>n. norm (a n) * norm q ^ n)"
      by (intro landau_o.big.mult_left) (use \<open>q \<noteq> 0\<close> \<open>norm q < 1\<close> in real_asymp)
    also have "(\<lambda>n. norm (a n) * norm q ^ n) =
                 (\<lambda>n. norm (a n * of_real r ^ n * (q / of_real r) ^ n))"
      using \<open>r > 0\<close> by (intro ext) (auto simp: norm_mult norm_divide norm_power power_divide)
    finally show "(\<lambda>n. f n q) \<in> O(\<lambda>n. a n * of_real r ^ n * (q / of_real r) ^ n)"
      by (subst (asm) landau_o.big.norm_iff)
  next
    show "norm (q / of_real r) < 1"
      using r r' by (simp add: norm_divide field_simps)
  qed
qed

text \<open>
  If additionally $\sum_{k=1}^\infty a(k)$ converges absolutely, the absolute convergence of the
  Lambert series also holds everywhere.
\<close>
lemma norm_summable_lambert':
  assumes "summable (\<lambda>k. norm (a k))" and "norm q \<noteq> 1"
  shows   "summable (\<lambda>k. norm (f k q))"
proof -
  have *: "summable (\<lambda>k. norm (f k q))" if q: "norm q < 1" for q
  proof -
    have "conv_radius a \<ge> norm (1 :: 'a)"
      using assms(1) by (intro conv_radius_geI) (auto dest: summable_norm_cancel)
    with q have "ereal (norm q) < conv_radius a"
      by (simp add: ereal_le_less)
    thus ?thesis
      using assms(2) q by (intro norm_summable_lambert) auto
  qed

  show ?thesis
  proof (cases "norm q < 1")
    case True
    thus ?thesis using *[of q] by simp
  next
    case False
    hence [simp]: "q \<noteq> 0"
      by auto
    have [simp]: "q ^ k = 1 \<longleftrightarrow> k = 0" for k
      using assms(2) by (auto dest: power_eq_1_iff)
    have "summable (\<lambda>k. norm (a k + f k (inverse q)))"
      using False assms(2) by (intro summable_norm_add assms *) (auto simp: norm_divide field_simps)
    moreover have "eventually (\<lambda>k. f k q = -a k - f k (inverse q)) at_top"
      using eventually_gt_at_top[of 0]
      by eventually_elim (use False assms(2) in \<open>auto simp: fun_eq_iff field_simps f_def\<close>)
    hence "eventually (\<lambda>k. norm (f k q) = norm (a k + f k (inverse q))) at_top"
      by eventually_elim (auto simp: norm_uminus_minus)
    ultimately show ?thesis
      using summable_cong by fast
  qed
qed

lemma abs_summable_on_lambert:
  assumes "norm q < min 1 (conv_radius a)"
  shows   "(\<lambda>k. f k q) abs_summable_on {1..}"
proof -
  have "summable (\<lambda>k. norm (f (Suc k) q))"
    by (subst summable_Suc_iff, rule norm_summable_lambert) (use assms in auto)
  hence "(\<lambda>k. f (Suc k) q) abs_summable_on UNIV"
    by (subst summable_on_UNIV_nonneg_real_iff) auto
  also have "?this \<longleftrightarrow> ?thesis"
    by (intro summable_on_reindex_bij_witness[of _ "\<lambda>k. k - 1" Suc]) auto
  finally show ?thesis .
qed

lemma abs_summable_on_lambert':
  assumes "summable (\<lambda>k. norm (a k))" and "norm q \<noteq> 1"
  shows   "(\<lambda>k. f k q) abs_summable_on {1..}"
proof -
  have "summable (\<lambda>k. norm (f (Suc k) q))"
    by (subst summable_Suc_iff, rule norm_summable_lambert') (use assms in auto)
  hence "(\<lambda>k. f (Suc k) q) abs_summable_on UNIV"
    by (subst summable_on_UNIV_nonneg_real_iff) auto
  also have "?this \<longleftrightarrow> ?thesis"
    by (intro summable_on_reindex_bij_witness[of _ "\<lambda>k. k - 1" Suc]) auto
  finally show ?thesis .
qed
  
lemma summable_on_lambert:
  assumes "norm q < min 1 (conv_radius a)"
  shows   "(\<lambda>k. f k q) summable_on {1..}"
  using abs_summable_summable[OF abs_summable_on_lambert[OF assms]] .

lemma has_sum_lambert:
  assumes "norm q < min 1 (conv_radius a)"
  shows   "((\<lambda>k. f k q) has_sum lambert a q) {1..}"
proof -
  have "((\<lambda>k. f (Suc k) q) has_sum lambert a q) UNIV"
  proof (rule norm_summable_imp_has_sum)
    show "summable (\<lambda>n. norm (f (Suc n) q))"
      using norm_summable_lambert[OF assms] by (subst summable_Suc_iff)
    show "(\<lambda>k. f (Suc k) q) sums lambert a q"
      by (rule sums_lambert) (use assms in \<open>auto simp: lambert_conv_radius_def\<close>)
  qed
  also have "?this \<longleftrightarrow> ?thesis"
    by (intro has_sum_reindex_bij_witness[of _ "\<lambda>k. k - 1" Suc]) auto
  finally show ?thesis .
qed

text \<open>
  We can also show a more precise convergence result that essentially fully reduces the question
  of convegence of a Lambert series to that of its ``corresponding'' power series:
  $\sum_{k=1}^\infty a(k) \frac{q^k}{1-q^k}$ converges if and only if the ``corresponding''
  power series $\sum_{k=1}^\infty a(k) q^k$ converges or if $\sum_{k=1}^\infty a(k)$ converges.

  This is Theorem~259 in Knopp's book. A key ingredient, aside from the results we have amassed
  so far, is the du-Bois Reymond summation test.
\<close>
theorem summable_lambert_iff:
  assumes "norm q \<noteq> 1"
  shows   "summable (\<lambda>k. f k q) \<longleftrightarrow> summable a \<or> summable (\<lambda>k. a k * q ^ k)"
proof (cases "summable a")
  case True
  hence "summable (\<lambda>k. f k q)" using assms
    by (intro summable_lambert) (auto simp: lambert_conv_radius_def)
  with True show ?thesis
    by auto
next
  case not_summable: False
  have [simp]: "q ^ k \<noteq> 1" if "k > 0" for k
    using that assms by (auto dest: power_eq_1_iff)
  have "summable (\<lambda>k. f k q) \<longleftrightarrow> summable (\<lambda>k. a k * q ^ k)"
  proof (cases "norm q < 1")
    case False
    with assms have q: "norm q > 1"
      by simp
    have "\<not>summable (\<lambda>k. a k * q ^ k)"
      using q not_summable conv_radius_geI[of a q] summable_in_conv_radius[of 1 a]
      by (auto simp: ereal_le_less one_ereal_def)
    moreover have "\<not>summable (\<lambda>k. f k q)"
    proof
      assume "summable (\<lambda>k. f k q)"
      hence *: "summable (\<lambda>k. a k / (1 - q ^ k) * q ^ k)"
        by (auto simp: f_def)
      hence "summable (\<lambda>k. a k / (1 - q ^ k) * 1 ^ k)"
        by (rule powser_inside) (use q in auto)
      hence "summable (\<lambda>k. a k / (1 - q ^ k) - a k / (1 - q ^ k) * q ^ k)"
        by (intro summable_diff *) auto
      moreover have "eventually (\<lambda>k. a k / (1 - q ^ k) - a k / (1 - q ^ k) * q ^ k = a k) at_top"
        using eventually_gt_at_top[of 0]
        by eventually_elim (simp add: divide_simps, simp add: algebra_simps)
      ultimately have "summable a"
        using summable_cong by fast
      with not_summable show False
        by contradiction
    qed
    ultimately show ?thesis
      by simp
  next
    case q: True
    show ?thesis
    proof
      assume "summable (\<lambda>k. f k q)"
      hence "summable (\<lambda>k. f k q * (1 - q ^ k))"
      proof (rule dubois_reymond_summation_test)
        have "summable (\<lambda>k. norm (q - 1) * norm q ^ k)"
          using q by (intro summable_mult summable_geometric) auto
        also have "(\<lambda>k. norm (q - 1) * norm q ^ k) = (\<lambda>k. norm ((q - 1) * q ^ k))"
          by (simp add: norm_mult norm_power)
        also have "\<dots> = (\<lambda>k. norm (1 - q ^ k - (1 - q ^ Suc k)))"
          by (simp add: algebra_simps)
        finally show "summable (\<lambda>k. norm (1 - q ^ k - (1 - q ^ Suc k)))" .
      qed
      moreover have "eventually (\<lambda>k. f k q * (1 - q ^ k) = a k * q ^ k) at_top"
        using eventually_gt_at_top[of 0] by eventually_elim (auto simp: divide_simps f_def)
      ultimately show "summable (\<lambda>k. a k * q ^ k)"
        using summable_cong by fast
    next
      assume "summable (\<lambda>k. a k * q ^ k)"
      hence "summable (\<lambda>k. a k * q ^ k * (1 / (1 - q ^ k)))"
      proof (rule dubois_reymond_summation_test)
        show "summable (\<lambda>k. norm (1 / (1 - q ^ k) - 1 / (1 - q ^ Suc k)))"
        proof (rule summable_comparison_test_ev)
          show "summable (\<lambda>k. 2 / (1 - norm q) ^ 2 * norm q ^ k)"
            using q by (intro summable_mult summable_geometric) auto
        next
          show "eventually (\<lambda>k. norm (norm (1 / (1 - q ^ k) - 1 / (1 - q ^ Suc k))) \<le>
                                  2 / (1 - norm q) ^ 2 * norm q ^ k) at_top"
            using eventually_gt_at_top[of 0]
          proof eventually_elim
            case k: (elim k)
            have "norm (1 - q) \<le> norm (1 :: 'a) + 1"
              using q by norm
            hence 1: "norm (1 - q) \<le> 2"
              by simp
            have 2: "norm (1 - q ^ l) \<ge> 1 - norm q" if l: "l > 0" for l
            proof -
              have "norm (1 - q ^ l) \<ge> norm (1 :: 'a) - norm (q ^ l)"
                by norm
              moreover have "norm (q ^ l) \<le> norm q ^ 1"
                using q l unfolding norm_power by (intro power_decreasing) auto
              ultimately show ?thesis
                by simp
            qed
  
            have "1 / (1 - q ^ k) - 1 / (1 - q ^ Suc k) =
                    (q ^ k - q ^ Suc k) / ((1 - q ^ k) * (1 - q ^ Suc k))"
              using k by (simp add: divide_simps del: power_Suc)
            also have "\<dots> = (1 - q) * q ^ k / ((1 - q ^ k) * (1 - q ^ Suc k))"
              by (simp add: algebra_simps)
            also have "norm \<dots> = norm (1 - q) * norm q ^ k / (norm (1 - q ^ k) * norm (1 - q ^ Suc k))"
              by (simp add: norm_mult norm_divide norm_power)
            also have "\<dots> \<le> 2 * norm q ^ k / ((1 - norm q) * (1 - norm q))" using q k
              by (intro frac_le mult_mono mult_pos_pos zero_le_power norm_ge_zero 1 2)
                 (auto simp del: power_Suc)
            finally show ?case
              by (simp add: power2_eq_square)
          qed
        qed
      qed
      thus "summable (\<lambda>k. f k q)"
        by (simp add: f_def)
    qed
  qed
  with not_summable show ?thesis
    by blast
qed

end


lemma holomorphic_lambert [holomorphic_intros]:
  assumes "X \<subseteq> eball 0 (lambert_conv_radius a) - sphere 0 1"
  shows   "lambert a holomorphic_on X"
proof -
  have "lambert a holomorphic_on eball 0 (lambert_conv_radius a) - sphere 0 1"
  proof (rule holomorphic_uniform_sequence)
    show "open (eball 0 (lambert_conv_radius a) - sphere (0 :: complex) 1)"
      by (intro open_Diff) auto
  next
    fix q :: complex
    assume q: "q \<in> eball 0 (lambert_conv_radius a) - sphere 0 1"
    have "open (eball 0 (lambert_conv_radius a) - sphere 0 1 :: complex set)"
      by auto
    then obtain r where r: "r > 0" "cball q r \<subseteq> eball 0 (lambert_conv_radius a) - sphere 0 1"
      unfolding open_contains_cball using q by blast
    define f where "f \<equiv> \<lambda>k q. a k * q ^ k / (1 - q ^ k)"
    show "\<exists>d>0. cball q d \<subseteq> eball 0 (lambert_conv_radius a) - sphere 0 1 \<and>
               uniform_limit (cball q d) (\<lambda>n q. \<Sum>k<n. f (Suc k) q) (lambert a) sequentially"
    proof (intro exI[of _ r] conjI)
      show "uniform_limit (cball q r) (\<lambda>n q. \<Sum>k<n. f (Suc k) q) (lambert a) sequentially"
        unfolding f_def by (rule uniform_limit_lambert) (use r in auto)
    qed (use r in auto)
  next
    show "(\<lambda>q. \<Sum>k<n. a (Suc k) * q ^ Suc k / (1 - q ^ Suc k)) holomorphic_on
             eball 0 (lambert_conv_radius a) - sphere 0 1" for n :: nat
      by (intro holomorphic_intros) (auto simp del: power_Suc dest!: power_eq_1_iff)
  qed
  thus ?thesis
    by (rule holomorphic_on_subset) fact
qed

lemma holomorphic_lambert' [holomorphic_intros]:
  assumes "f holomorphic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<in> eball 0 (lambert_conv_radius a) - sphere 0 1"
  shows   "(\<lambda>z. lambert a (f z)) holomorphic_on A"
  by (rule holomorphic_on_compose_gen[OF assms(1) holomorphic_lambert[OF order.refl],
           unfolded o_def])
     (use assms(2) in auto)

lemma analytic_lambert [analytic_intros]:
  fixes a :: "nat \<Rightarrow> complex"
  assumes "A \<subseteq> eball 0 (lambert_conv_radius a) - sphere 0 1"
  shows   "lambert a analytic_on A"
proof -
  have "open (eball 0 (lambert_conv_radius a) - sphere 0 1 :: complex set)"
    by auto
  hence "lambert a analytic_on eball 0 (lambert_conv_radius a) - sphere 0 1"
    using holomorphic_lambert[OF order.refl, of a]
    by (auto simp: analytic_on_open)
  thus ?thesis
    by (rule analytic_on_subset) fact
qed

lemma analytic_lambert' [analytic_intros]:
  assumes "f analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> f z \<in> eball 0 (lambert_conv_radius a) - sphere 0 1"
  shows   "(\<lambda>z. lambert a (f z)) analytic_on A"
  by (rule analytic_on_compose_gen[OF assms(1) analytic_lambert[OF order.refl], unfolded o_def])
     (use assms(2) in auto)

lemma continuous_on_lambert [continuous_intros]:
  fixes a :: "nat \<Rightarrow> 'a :: {real_normed_field, banach, heine_borel}"
  assumes "A \<subseteq> eball 0 (lambert_conv_radius a) - sphere 0 1"
  shows   "continuous_on A (lambert a)"
proof -
  have "isCont (lambert a) q" if q: "q \<in> eball 0 (lambert_conv_radius a) - sphere 0 1" for q
  proof -
    have "open (eball 0 (lambert_conv_radius a) - sphere 0 1 :: 'a set)"
      by auto
    with q obtain r where r: "r > 0" "cball q r \<subseteq> eball 0 (lambert_conv_radius a) - sphere 0 1"
      unfolding open_contains_cball by blast
    have "continuous_on (cball q r) (lambert a)"
    proof (rule uniform_limit_theorem)
      show "uniform_limit (cball q r)
              (\<lambda>n q. \<Sum>k<n. a (Suc k) * q ^ Suc k / (1 - q ^ Suc k)) (lambert a) at_top"
        by (intro uniform_limit_lambert) (use r in auto)
      show "\<forall>\<^sub>F n in sequentially. continuous_on (cball q r)
              (\<lambda>q. \<Sum>k<n. a (Suc k) * q ^ Suc k / (1 - q ^ Suc k))" using q r
        by (auto intro!: always_eventually continuous_intros simp del: power_Suc dest!: power_eq_1_iff)
    qed auto
    hence "continuous_on (ball q r) (lambert a)"
      by (rule continuous_on_subset) auto
    thus ?thesis using \<open>r > 0\<close>
      by (subst (asm) continuous_on_eq_continuous_at) auto
  qed
  with assms show ?thesis
    by (intro continuous_at_imp_continuous_on) auto
qed

lemma continuous_on_lambert' [continuous_intros]:
  fixes a :: "nat \<Rightarrow> 'a :: {real_normed_field, banach, heine_borel}"
  assumes "continuous_on A f" "\<And>z. z \<in> A \<Longrightarrow> f z \<in> eball 0 (lambert_conv_radius a) - sphere 0 1"
  shows   "continuous_on A (\<lambda>z. lambert a (f z))"
  by (rule continuous_on_compose2[OF continuous_on_lambert[OF order.refl] assms(1)])
     (use assms(2) in auto)

lemma tendsto_lambert [tendsto_intros]:
  fixes a :: "nat \<Rightarrow> 'a :: {real_normed_field, banach, heine_borel}"
  assumes "(f \<longlongrightarrow> c) F" "c \<in> eball 0 (lambert_conv_radius a) - sphere 0 1"
  shows   "((\<lambda>x. lambert a (f x)) \<longlongrightarrow> lambert a c) F"
proof -
  have "open (eball 0 (lambert_conv_radius a) - sphere 0 1 :: 'a set)"
    by (intro open_Diff closed_sphere) auto
  hence "isCont (lambert a) c"
    using continuous_on_lambert[OF order.refl] 
    by (intro continuous_on_interior) (use assms in \<open>auto simp: interior_open\<close>)
  thus ?thesis
    using assms(1) by (simp add: isCont_tendsto_compose)
qed

text \<open>
  If $\sum_{n=1}^\infty a(n)$ exists, the Lambert series of $a(n)$ tends to it for $q\to\infty$.
\<close>
lemma tendsto_lambert_at_infinity:
  assumes "summable (a :: nat \<Rightarrow> 'a :: {real_normed_field, banach, heine_borel})"
  shows   "(lambert a \<longlongrightarrow> -(\<Sum>n. a (Suc n))) at_infinity"
proof (rule Lim_transform_eventually)
  have "((\<lambda>q. -(\<Sum>n. a (Suc n)) - lambert a (1 / q)) \<longlongrightarrow> -(\<Sum>n. a (Suc n)) - lambert a 0) at_infinity"
    by (rule tendsto_diff tendsto_lambert tendsto_intros tendsto_divide_0 filterlim_ident)+
       (use assms in \<open>auto simp: lambert_conv_radius_def\<close>)
  thus "((\<lambda>q. -(\<Sum>n. a (Suc n)) - lambert a (1 / q)) \<longlongrightarrow> -(\<Sum>n. a (Suc n))) at_infinity"
    by simp
next
  have "eventually (\<lambda>q :: 'a. norm q > 1) at_infinity"
    by (metis dual_order.strict_trans1 eventually_at_infinity gt_ex)
  thus "\<forall>\<^sub>F x in at_infinity. -(\<Sum>n. a (Suc n)) - lambert a (1 / x) = lambert a x"
    by eventually_elim (subst lambert_reciprocal, use assms in auto)
qed


subsection \<open>Power series expansion\<close>

text \<open>
  By exchanging the order of summation, we can prove the power series expansion of $L(a,q)$ as
  \[L(a,q) = \sum_{n=1}^\infty (a*1)(n) q^n\]
  where $*$ denotes the Dirichlet product, i.e.\ $(a * 1)(n) = \sum_{d\mid n} a(d)$.

  This gives particularly nice results when $a(n)$ is a number-theoretic function.
\<close>
theorem has_sum_lambert_powser:
  assumes "norm q < min 1 (conv_radius a)"
  assumes "dirichlet_prod a (\<lambda>_. 1) = b"
  shows   "((\<lambda>n. b n * q ^ n) has_sum lambert a q) {1..}"
proof -
  have q: "norm q < 1" "norm q < conv_radius a"
    using assms by auto
  have q': "norm q < lambert_conv_radius a"
    using q by (auto simp: lambert_conv_radius_def)
  have "((\<lambda>(n, k). a n * q ^ (k * n)) has_sum lambert a q) ({1..} \<times> {1..})"
  proof (rule has_sum_SigmaI; (unfold prod.case)?)
    show "((\<lambda>n. a n * q ^ n / (1 - q ^ n)) has_sum lambert a q) {1..}"
      by (intro has_sum_lambert) (use assms in \<open>auto simp: lambert_conv_radius_def\<close>)
  next
    show "(\<lambda>(n, k). a n * q ^ (k * n)) summable_on {1..} \<times> {1..}"
    proof (rule abs_summable_summable)
      show "(\<lambda>(n, k). a n * q ^ (k * n)) abs_summable_on {1..} \<times> {1..}"
      proof (rule summable_on_SigmaI; (unfold prod.case)?)
        fix n :: nat
        assume n: "n \<in> {1..}"
        have "((\<lambda>k. norm (a n) * (norm q ^ n) ^ k) has_sum
                (norm (a n) * (norm q ^ n / (1 - norm q ^ n)))) {1..}"
          using has_sum_geometric[of "norm q ^ n" 1] q n
          by (intro has_sum_cmult_right) (auto simp: norm_power power_less_1_iff)
        thus "((\<lambda>k. norm (a n * q ^ (k * n))) has_sum
                (norm (a n) * norm q ^ n / (1 - norm q ^ n))) {1..}"
          by (simp add: norm_mult norm_power norm_divide mult_ac flip: power_mult)
      next
        show "(\<lambda>n. norm (a n) * norm q ^ n / (1 - norm q ^ n)) summable_on {1..}"
        proof (rule abs_summable_summable)
          show "(\<lambda>x. norm (a x) * norm q ^ x / (1 - norm q ^ x)) abs_summable_on {1..}"
            using abs_summable_on_lambert[of "of_real (norm q)" "\<lambda>n. norm (a n)"] q' q
            by (cases "summable (\<lambda>n. norm (a n))")
               (auto simp: lambert_conv_radius_def split: if_splits)
        qed
      qed auto
    qed
  next
    fix n :: nat
    assume n: "n \<in> {1..}"
    have "((\<lambda>k. a n * (q ^ n) ^ k) has_sum a n * (q ^ n / (1 - q ^ n))) {1..}"
      using has_sum_geometric[of "q ^ n" 1] q n
      by (intro has_sum_cmult_right) (auto simp: power_less_1_iff norm_power)
    thus "((\<lambda>k. a n * q ^ (k * n)) has_sum a n * q ^ n / (1 - q ^ n)) {1..}"
      by (simp add: mult_ac flip: power_mult)
  qed
  also have "?this \<longleftrightarrow> ((\<lambda>(n, d). a d * q ^ n) has_sum lambert a q) (SIGMA n:{1..}. {d. d dvd n})"
    by (rule has_sum_reindex_bij_witness[of _ "\<lambda>(m, d). (d, m div d)"  "\<lambda>(n,k). (n * k, n)"])
       (auto simp: mult_ac)
  finally have 1: "((\<lambda>(n, d). a d * q ^ n) has_sum lambert a q) (SIGMA n:{1..}. {d. d dvd n})" .

  have 2: "((\<lambda>d. a d * q ^ n) has_sum (b n * q ^ n)) {d. d dvd n}" if n: "n > 0" for n
  proof -
    have "((\<lambda>d. a d * q ^ n) has_sum ((\<Sum>d | d dvd n. a d) * q ^ n)) {d. d dvd n}"
      by (intro has_sum_cmult_left has_sum_finite finite_divisors_nat n)
    also have "(\<Sum>d | d dvd n. a d) = dirichlet_prod a (\<lambda>_. 1) n"
      by (simp add: dirichlet_prod_def)
    also have "\<dots> = b n"
      using assms by simp
    finally show ?thesis .
  qed

  show "((\<lambda>n. b n * q ^ n) has_sum lambert a q) {1..}"
    using has_sum_SigmaD[OF 1, of "\<lambda>n. b n * q ^ n"] 2 by simp
qed

lemma sums_lambert_powser:
  assumes "norm q < min 1 (conv_radius a)"
  assumes "dirichlet_prod a (\<lambda>_. 1) = b"
  shows   "(\<lambda>n. b n * q ^ n) sums lambert a q"
proof -
  from assms(2) have [simp]: "b 0 = 0"
    using dirichlet_prod_0 by blast
  have "((\<lambda>n. b n * q ^ n) has_sum lambert a q) {1..}"
    by (rule has_sum_lambert_powser) fact+
  also have "?this \<longleftrightarrow> ((\<lambda>n. b n * q ^ n) has_sum lambert a q) UNIV"
    by (intro has_sum_cong_neutral) (auto simp: not_le)
  finally show ?thesis
    by (rule has_sum_imp_sums)
qed

lemma conv_radius_dirichlet_prod_1_ge:
  fixes a b :: "nat \<Rightarrow> 'a :: {real_normed_field, banach}"
  defines "b \<equiv> dirichlet_prod a (\<lambda>_. 1)"
  shows   "conv_radius b \<ge> min 1 (conv_radius a)"
proof (rule conv_radius_geI_ex)
  fix r :: real
  assume r: "0 < r" "r < min 1 (conv_radius a)"
  have "(\<lambda>n. b n * of_real r ^ n) sums lambert a (of_real r)"
    using r by (intro sums_lambert_powser) (auto simp: b_def)
  thus "\<exists>z. norm z = r \<and> summable (\<lambda>n. b n * z ^ n)"
    using r(1) by (intro exI[of _ "of_real r"]) (auto simp: sums_iff)
qed

lemma sums_lambert_powser':
  assumes "norm q < min 1 (conv_radius a)"
  assumes "fds b = fds a * fds_zeta" "b 0 = 0"
  shows   "(\<lambda>n. b n * q ^ n) sums lambert a q"
  using assms(1)
proof (rule sums_lambert_powser)
  have "fds_nth (fds a * fds_zeta) = dirichlet_prod a (\<lambda>_. 1)"
    by (auto simp: fds_nth_mult)
  also have "fds a * fds_zeta = fds b"
    using assms(2) by (simp only: )
  also have "fds_nth (fds b) = b"
    using assms(3) by (auto simp: fun_eq_iff fds_nth_fds)
  finally show "dirichlet_prod a (\<lambda>_. 1) = b" ..
qed


subsubsection \<open>Divisor \<open>\<sigma>\<close> function\<close>

text \<open>
  For any $q$ with $|q| < 1$ and any $\alpha\in\mathbb{C}$, we have
  \[\sum_{n=1}^\infty \sigma_\alpha(n) q^n = \sum_{n=1}^\infty n^\alpha \frac{q^n}{1-q^n}\]
  where $\sigma_\alpha(n)$ is the divisor \<open>\<sigma>\<close> function, i.e.
  $sigma_\alpha(n) = \sum_{d \mid n} d ^{\,\alpha}$.
\<close>
lemma divisor_sigma_powser_conv_lambert:
  fixes \<alpha> q :: "'a :: {nat_power_normed_field, banach}"
  assumes q: "norm q < 1"
  shows   "(\<lambda>n. divisor_sigma \<alpha> n * q ^ n) sums lambert (\<lambda>n. nat_power n \<alpha>) q"
proof (rule sums_lambert_powser')
  have "conv_radius (\<lambda>n. nat_power n \<alpha>) = 1"
  proof (rule tendsto_imp_conv_radius_eq)
    have "(\<lambda>n. ereal ((real n powr (\<alpha> \<bullet> 1)) powr (1 / real n))) \<longlonglongrightarrow> 1"
      unfolding one_ereal_def by (rule tendsto_ereal) real_asymp
    also have "?this \<longleftrightarrow> (\<lambda>n. ereal (norm (nat_power n \<alpha>) powr (1 / real n))) \<longlonglongrightarrow> 1"
      by (intro filterlim_cong refl eventually_mono[OF eventually_gt_at_top[of 0]])
         (simp add: norm_nat_power)
    finally show "(\<lambda>n. ereal (norm (nat_power n \<alpha>) powr (1 / real n))) \<longlonglongrightarrow> 1"
      by (simp add: norm_nat_power)
  qed auto
  thus "ereal (norm q) < min 1 (conv_radius (\<lambda>n. nat_power n \<alpha>))"
    using q by simp
next
  have "fds (divisor_sigma \<alpha>) = fds_zeta * fds_shift \<alpha> fds_zeta"
    by (rule fds_divisor_sigma)
  also have "fds_shift \<alpha> fds_zeta = fds (\<lambda>n. nat_power n \<alpha>)"
    by (simp add: fds_eq_iff)
  finally show "fds (divisor_sigma \<alpha>) = fds (\<lambda>n. nat_power n \<alpha>) * fds_zeta"
    by (simp add: mult.commute)
qed auto

lemma divisor_count_powser_conv_lambert:
  fixes q :: "'a :: {nat_power_normed_field, banach}"
  assumes q: "norm q < 1"
  shows   "(\<lambda>n. of_nat (divisor_count n) * q ^ n) sums lambert (\<lambda>_. 1) q"
  using divisor_sigma_powser_conv_lambert[OF assms, of 0]
  by (simp add: divisor_sigma_0_left)


subsubsection \<open>Möbius \<open>\<mu>\<close> function\<close>

text \<open>
  For any $q$ with $|q| < 1$, we have
  \[\sum_{n=1}^\infty \mu(n)\frac{q^n}{1-q^n} = q\]
  where $\mu(n)$ is Möbus' \<open>\<mu>\<close> function, which is $0$ if $n$ is not squarefree (i.e.\ contains
  the same prime factor more than once) and otherwise equal to $(-1)^k$, where $k$ is the
  number of prime factors of $n$.
\<close>
lemma lambert_moebius_mu:
  fixes q :: "'a :: {real_normed_field, banach}"
  assumes q: "norm q < 1"
  shows   "lambert moebius_mu q = q"
proof -
  have "(\<lambda>n. indicator {1} n * q ^ n) sums lambert moebius_mu q"
  proof (rule sums_lambert_powser')
    have "fds moebius_mu * fds_zeta = (1 :: 'a fds)"
      using fds_zeta_times_moebius_mu[where ?'a = 'a] by (simp only: mult.commute)
    also have "(1 :: 'a fds) = fds (indicator {1})"
      by (auto simp: fds_eq_iff fds_nth_one)
    finally show "fds (indicator {1} :: nat \<Rightarrow> 'a) = fds moebius_mu * fds_zeta" ..
  qed (use q in \<open>auto simp: conv_radius_moebius_mu\<close>)
  also have "(\<lambda>n. indicator {1} n * q ^ n) = (\<lambda>n. (if n = 1 then 1 else 0) * q ^ n)"
    by auto
  finally have "\<dots> sums lambert moebius_mu q" .
  moreover have "(\<lambda>n. (if n = 1 then 1 else 0) * q ^ n) sums (q ^ 1)"
    by (rule powser_sums_if)
  ultimately show "lambert moebius_mu q = q"
    by (simp add: sums_iff)
qed

lemma lambert_conv_radius_moebius_mu:
  "lambert_conv_radius (moebius_mu :: nat \<Rightarrow> 'a :: {real_normed_field, banach}) = 1"
proof -
  have "\<not>summable (moebius_mu :: nat \<Rightarrow> 'a)"
    using not_convergent_moebius_mu[where ?'a = 'a] summable_LIMSEQ_zero
    by (auto simp: convergent_def)
  thus ?thesis
    by (simp add: lambert_conv_radius_def conv_radius_moebius_mu)
qed


subsubsection \<open>Euler's totient function \<open>\<phi>\<close>\<close>

text \<open>
  For any $q$ with $|q| < 1$, we have
  \[\frac{q}{(1-q)^2} = \sum_{n=1}^\infty n q^n = \sum_{n=1}^\infty \varphi(n)\frac{q^n}{1-q^n}\]
  where $\varphi(n)$ is Euler's totient function, i.e.\ the number of positive integers not greater
  than $n$ that are coprime to $n$.
\<close>
lemma lambert_totient:
  fixes q :: "'a :: {real_normed_field, banach}"
  assumes q: "norm q < 1"
  shows   "lambert (\<lambda>n. of_nat (totient n) :: 'a) q = q / (1 - q) ^ 2"
proof -
  have "(\<lambda>n. of_nat n * q ^ n) sums lambert (\<lambda>n. of_nat (totient n) :: 'a) q"
  proof (rule sums_lambert_powser')
    show "fds (of_nat :: nat \<Rightarrow> 'a) = fds (\<lambda>n. of_nat (totient n)) * fds_zeta"
      by (rule fds_totient_times_zeta [symmetric])
  qed (use q in \<open>auto simp: conv_radius_totient\<close>)
  from sums_unique2[OF this n_powser_sums[OF q]] show ?thesis .
qed

lemma lambert_conv_radius_totient:
  "lambert_conv_radius (\<lambda>n. of_nat (totient n) :: 'a :: {real_normed_field, banach}) = 1"
proof -
  have "\<not>summable (\<lambda>n. of_nat (totient n) :: 'a :: {real_normed_field, banach})"
    using not_convergent_totient[where ?'a = 'a] summable_LIMSEQ_zero
    by (auto simp: convergent_def)
  thus ?thesis
    by (simp add: lambert_conv_radius_def conv_radius_totient)
qed


subsubsection \<open>Mangoldt's \<open>\<Lambda>\<close> function\<close>

text \<open>
  For any $q$ with $|q| < 1$, we have
  \[\sum_{n=1}^\infty \ln n\ q^n = \sum_{n=1}^\infty \Lambda(n)\frac{q^n}{1-q^n}\]
  where $\Lambda(n)$ is Mangoldt's function, which is defined to be equal to $\log n$ if $n$
  is prime and $0$ otherwise.
\<close>

lemma lambert_mangoldt:
  fixes q :: "'a :: {real_normed_field, banach}"
  assumes q: "norm q < 1"
  shows   "(\<lambda>n. of_real (ln (Suc n)) * q ^ (Suc n)) sums lambert mangoldt q"
proof -
  have "(\<lambda>n. (if n = 0 then 0 else of_real (ln n)) * q ^ n) sums lambert mangoldt q"
    by (rule sums_lambert_powser')
       (use q fds_mangoldt_times_zeta[where ?'a = 'a] in \<open>auto simp: conv_radius_mangoldt\<close>)
  also have "?this \<longleftrightarrow> (\<lambda>n. (if Suc n = 0 then 0 else of_real (ln (Suc n))) * q ^ Suc n) sums lambert mangoldt q"
    by (subst sums_Suc_iff) auto
  also have "\<dots> \<longleftrightarrow> ?thesis"
    by simp
  finally show ?thesis .
qed

lemma lambert_conv_radius_mangoldt:
  "lambert_conv_radius (mangoldt :: nat \<Rightarrow> 'a :: {real_normed_field, banach}) = 1"
proof -
  have "\<not>summable (mangoldt :: nat \<Rightarrow> 'a :: {real_normed_field, banach})"
    using not_convergent_mangoldt[where ?'a = 'a] summable_LIMSEQ_zero
    by (auto simp: convergent_def)
  thus ?thesis
    by (simp add: lambert_conv_radius_def conv_radius_mangoldt)
qed


subsubsection \<open>Liouville's \<open>\<lambda>\<close> function\<close>

text \<open>
  For any $q$ with $|q| < 1$, we have
  \[\sum_{n=1}^\infty q^{n^2} = \sum_{n=1}^\infty \lambda(n)\frac{q^n}{1-q^n}\]
  where $\lambda(n)$ is Liouville's function, which is defined as the number of prime factors
  of $n$ (taking multiplicity into account).
\<close>
lemma lambert_liouville_lambda:
  fixes q :: "'a :: {real_normed_field, banach}"
  assumes q: "norm q < 1"
  shows   "(\<lambda>n. ind is_square n * q ^ n) sums lambert liouville_lambda q"
  by (rule sums_lambert_powser')
     (use q fds_liouville_lambda_times_zeta[where ?'a = 'a] 
       in \<open>auto simp: conv_radius_liouville_lambda mult_ac\<close>)

lemma lambert_liouville_lambda':
  fixes q :: "'a :: {real_normed_field, banach}"
  assumes q: "norm q < 1"
  shows   "(\<lambda>n. q ^ ((n+1) ^ 2)) sums lambert liouville_lambda q"
proof -
  have "(\<lambda>n. ind is_square ((n+1)^2) * q ^ ((n+1) ^ 2)) sums lambert liouville_lambda q \<longleftrightarrow>
        (\<lambda>n. ind is_square n * q ^ n) sums lambert liouville_lambda q"
  proof (rule sums_mono_reindex)
    show "strict_mono (\<lambda>n::nat. (n + 1)\<^sup>2)"
      by (intro strict_monoI power_strict_mono) auto
    show "ind is_square n * q ^ n = 0" if "n \<notin> range (\<lambda>n. (n + 1)\<^sup>2)" for n
    proof (rule ccontr)
      assume "ind is_square n * q ^ n \<noteq> 0"
      hence "is_square n" "n > 0"
        by (auto simp: ind_def split: if_splits)
      then obtain m where "n = m ^ 2" "m > 0"
        by (elim is_nth_powerE) auto
      hence "n = ((m - 1) + 1) ^ 2"
        by auto
      with that show False by blast
    qed
  qed
  thus ?thesis
    using lambert_liouville_lambda[OF assms] by simp
qed

lemma lambert_conv_radius_liouville_lambda:
  "lambert_conv_radius (liouville_lambda :: nat \<Rightarrow> 'a :: {real_normed_field, banach}) = 1"
proof -
  have "\<not>summable (liouville_lambda :: nat \<Rightarrow> 'a)"
    using not_convergent_liouville_lambda[where ?'a = 'a] summable_LIMSEQ_zero
    by (auto simp: convergent_def)
  thus ?thesis
    by (simp add: lambert_conv_radius_def conv_radius_liouville_lambda)
qed


subsection \<open>Expressing a Lambert series in terms of a power series\<close>

text \<open>
  Let $a(n)$ be a sequence of numbers. Then we can express the value of the Lambert series
  as an infinite sum in terms of the ``normal'' power series $f(q) = \sum_{k=1}^\infty a(k) q^k$:
  \[ L(a, q) = \sum_{n=1}^\infty f(q^n) \]
  The proof is quite obvious, by expanding $f(q^n)$ into its power series and then switching
  the order of summation.

  This gives us a number of interesting relationships, including a connection between
  $L(n^a, q)$ and the polylogarithm function $\text{Li}_{-a}$.
\<close>
theorem lambert_conv_powser_has_sum:
  assumes q: "norm q < min 1 (conv_radius a)" and [simp]: "a 0 = 0"
  defines "f \<equiv> (\<lambda>q. \<Sum>n. a n * q ^ n)"
  shows   "((\<lambda>n. f (q ^ n)) has_sum lambert a q) {1..}"
proof -
  have "((\<lambda>(k, n). a k * (q ^ k) ^ n) has_sum lambert a q) ({1..} \<times> {1..})"
  proof (rule has_sum_SigmaI; (unfold prod.case)?)
    fix k :: nat
    assume k: "k \<in> {1..}"
    show "((\<lambda>y. a k * (q ^ k) ^ y) has_sum (a k * (q ^ k / (1 - q ^ k)))) {1..}"
      by (intro has_sum_cmult_right has_sum_geometric_from_1)
         (use q k in \<open>auto simp: power_less_1_iff norm_power\<close>)
  next
    have "((\<lambda>k. a k * q ^ k / (1 - q ^ k)) has_sum lambert a q) {1..}"
      using q by (intro has_sum_lambert) (auto simp: lambert_conv_radius_def split: if_splits)
    thus "((\<lambda>k. a k * (q ^ k / (1 - q ^ k))) has_sum lambert a q) {1..}"
      by (simp add: field_simps)
  next
    show "(\<lambda>(k, n). a k * (q ^ k) ^ n) summable_on {1..} \<times> {1..}"
    proof (rule abs_summable_summable, rule summable_on_SigmaI;
           (unfold prod.case norm_divide norm_power norm_mult norm_one norm_of_nat)?)
      fix k :: nat assume k: "k \<in> {1..}"
      show "((\<lambda>n. norm (a k) * (norm q ^ k) ^ n) has_sum 
              (norm (a k) * (norm q ^ k / (1 - norm q ^ k)))) {1..}"
        by (intro has_sum_cmult_right has_sum_geometric_from_1)
           (use k q in \<open>auto simp: power_less_1_iff\<close>)
    next
      show "(\<lambda>n. norm (a n) * (norm q ^ n / (1 - norm q ^ n))) summable_on {1..}"
        using summable_on_lambert[of "norm q" "\<lambda>n. norm (a n)"] q
        by (auto simp: lambert_conv_radius_def split: if_splits)
    qed auto
  qed
  hence *: "((\<lambda>(n, k). a k * q ^ (k * n)) has_sum lambert a q) ({1..} \<times> {1..})"
    by (subst (asm) has_sum_swap) (simp_all flip: power_mult add: mult.commute)

  show ?thesis
  proof (rule has_sum_SigmaD [OF *]; unfold prod.case)
    fix n :: nat assume n: "n \<in> {1..}"
    have "ereal (norm q ^ n) \<le> ereal (norm q ^ 1)"
      unfolding ereal_less_eq using n q by (intro power_decreasing) auto
    also have "\<dots> < conv_radius a"
      using q by (simp add: less_eq_ereal_def)
    finally have norm_q_n: "norm q ^ n < conv_radius a" .

    have "((\<lambda>k. a k * (q ^ n) ^ k) has_sum f (q ^ n)) UNIV"
    proof (rule norm_summable_imp_has_sum)
      from norm_q_n show "((\<lambda>k. a k * (q ^ n) ^ k) sums f (q ^ n))"
        unfolding f_def by (intro summable_sums summable_in_conv_radius) (auto simp: norm_power)
    next
      show "summable (\<lambda>k. norm (a k * (q ^ n) ^ k))"
        by (rule abs_summable_in_conv_radius) (use norm_q_n in \<open>auto simp: norm_power\<close>)
    qed
    also have "?this \<longleftrightarrow> ((\<lambda>k. a k * q ^ (k * n)) has_sum f (q ^ n)) {1..}" 
      by (intro has_sum_cong_neutral) (auto simp: mult.commute not_le simp flip: power_mult)
    finally show \<dots> .
  qed
qed

lemma lambert_conv_powser_has_sum':
  assumes "norm q < r" and "r \<le> 1"
  assumes "\<And>q. norm q < r \<Longrightarrow> (\<lambda>n. a (Suc n) * q ^ Suc n) sums f q"
  shows   "((\<lambda>n. f (q ^ n)) has_sum lambert a q) {1..}"
proof -
  define a' where "a' = (\<lambda>k. if k = 0 then 0 else a k)"
  have "norm q < r"
    by fact
  also have "r \<le> conv_radius a"
  proof (rule conv_radius_geI_ex)
    fix r' assume r': "0 < r'" "ereal r' < ereal r"
    show "\<exists>x. norm x = r' \<and> summable (\<lambda>n. a n * x ^ n)"
      by (rule exI[of _ "of_real r'"], subst summable_Suc_iff [symmetric]) 
         (use assms(3)[of "of_real r'"] r' in \<open>simp add: sums_iff\<close>)
  qed
  also have "conv_radius a = conv_radius a'"
    by (intro conv_radius_cong eventually_mono[OF eventually_gt_at_top[of 0]]) (auto simp: a'_def)
  finally have "((\<lambda>n. (\<Sum>k. a' k * (q ^ n) ^ k)) has_sum lambert a' q) {1..}"
    using assms(1,2) by (intro lambert_conv_powser_has_sum) (auto simp: a'_def)
  also have "?this \<longleftrightarrow> ((\<lambda>n. f (q ^ n)) has_sum lambert a' q) {1..}"
  proof (rule has_sum_cong)
    fix n :: nat assume n: "n \<in> {1..}"
    have "norm q ^ n \<le> norm q ^ 1"
      using assms(1,2) n by (intro power_decreasing) auto
    also have "\<dots> < r"
      using assms(1,2) by simp
    finally have "(\<lambda>k. a (Suc k) * (q ^ n) ^ Suc k) sums f (q ^ n)"
      by (intro assms) (auto simp: norm_power)
    hence "(\<lambda>k. a' (Suc k) * (q ^ n) ^ Suc k) sums f (q ^ n)"
      by (simp add: a'_def)
    hence "(\<lambda>k. a' k * (q ^ n) ^ k) sums f (q ^ n)"
      by (subst (asm) sums_Suc_iff) (simp add: a'_def)
    thus "(\<Sum>k. a' k * (q ^ n) ^ k) = f (q ^ n)"
      by (simp add: sums_iff)
  qed
  also have "lambert a' q = lambert a q"
    by (simp add: a'_def)
  finally show ?thesis .
qed

lemma lambert_conv_powser_sums:
  assumes q: "norm q < min 1 (conv_radius a)" and [simp]: "a 0 = 0"
  defines "f \<equiv> (\<lambda>q. \<Sum>n. a n * q ^ n)"
  shows   "(\<lambda>n. f (q ^ Suc n)) sums lambert a q"
proof -
  have "((\<lambda>n. f (q ^ n)) has_sum lambert a q) {1..}"
    unfolding f_def by (rule lambert_conv_powser_has_sum) fact+
  also have "?this \<longleftrightarrow> ((\<lambda>n. f (q ^ Suc n)) has_sum lambert a q) UNIV"
    by (rule has_sum_reindex_bij_witness[of _ Suc "\<lambda>n. n - 1"]) auto
  finally show ?thesis
    by (rule has_sum_imp_sums)
qed

lemma lambert_conv_powser_sums':
  assumes "norm q < r" and "r \<le> 1"
  assumes "\<And>q. norm q < r \<Longrightarrow> (\<lambda>n. a (Suc n) * q ^ Suc n) sums f q"
  shows   "(\<lambda>n. f (q ^ Suc n)) sums lambert a q"
proof -
  have "((\<lambda>n. f (q ^ n)) has_sum lambert a q) {1..}"
    by (rule lambert_conv_powser_has_sum') fact+
  also have "?this \<longleftrightarrow> ((\<lambda>n. f (q ^ Suc n)) has_sum lambert a q) UNIV"
    by (rule has_sum_reindex_bij_witness[of _ Suc "\<lambda>n. n - 1"]) auto
  finally show ?thesis
    by (rule has_sum_imp_sums)
qed

lemma lambert_mult_exp_conv_powser_has_sum:
  assumes "norm q < r" and "r \<le> 1" and c: "norm c \<le> 1"
  assumes "\<And>q. norm q < r \<Longrightarrow> (\<lambda>n. a (Suc n) * q ^ Suc n) sums f q"
  shows   "((\<lambda>n. f (c * q ^ n)) has_sum lambert (\<lambda>n. c ^ n * a n) q) {1..}"
proof (rule lambert_conv_powser_has_sum')
  fix q :: 'a assume q: "norm q < r"
  have "norm c * norm q \<le> 1 * norm q"
    using q c by (intro mult_right_mono) auto
  hence cq: "norm c * norm q < r"
    using q by simp
  have "(\<lambda>n. a (Suc n) * (c * q) ^ Suc n) sums f (c * q)"
    by (rule assms) (use cq in \<open>simp add: norm_mult\<close>)
  thus "(\<lambda>n. c ^ Suc n * a (Suc n) * q ^ Suc n) sums f (c * q)"
    by (simp add: power_mult_distrib algebra_simps)
qed (use assms in auto)

lemma lambert_mult_exp_conv_powser_sums:
  assumes "norm q < r" and "r \<le> 1" and c: "norm c \<le> 1"
  assumes "\<And>q. norm q < r \<Longrightarrow> (\<lambda>n. a (Suc n) * q ^ Suc n) sums f q"
  shows   "((\<lambda>n. f (c * q ^ Suc n)) sums lambert (\<lambda>n. c ^ n * a n) q)"
proof (rule lambert_conv_powser_sums')
  fix q :: 'a assume q: "norm q < r"
  have "norm c * norm q \<le> 1 * norm q"
    using q c by (intro mult_right_mono) auto
  hence cq: "norm c * norm q < r"
    using q by simp
  have "(\<lambda>n. a (Suc n) * (c * q) ^ Suc n) sums f (c * q)"
    by (rule assms) (use cq in \<open>simp add: norm_mult\<close>)
  thus "(\<lambda>n. c ^ Suc n * a (Suc n) * q ^ Suc n) sums f (c * q)"
    by (simp add: power_mult_distrib algebra_simps)
qed (use assms in auto)

lemma lambert_power_int_has_sum_polylog_gen:
  fixes q :: complex
  assumes q: "norm q < 1" and c: "norm c \<le> 1"
  shows "((\<lambda>n. polylog (-a) (c * q ^ n)) has_sum lambert (\<lambda>n. c ^ n * of_nat n powi a) q) {1..}"
  using q
proof (rule lambert_mult_exp_conv_powser_has_sum)
  show "(\<lambda>n. of_nat (Suc n) powi a * q ^ Suc n) sums polylog (-a) q"
    if "norm q < 1" for q :: complex
    using sums_polylog[of q "-a"] that by simp
qed (use assms in auto)

lemma has_sum_lambert_recip_complex_gen:
  fixes q :: complex
  assumes q: "norm q < 1" and c: "norm c \<le> 1"
  shows   "((\<lambda>k. -ln (1 - c * q ^ k)) has_sum lambert (\<lambda>n. c ^ n / of_nat n) q) {1..}"
proof -
  have "((\<lambda>n. polylog 1 (c * q ^ n)) has_sum lambert (\<lambda>n. c ^ n * of_nat n powi - 1) q) {1..}"
    using lambert_power_int_has_sum_polylog_gen[OF q, of c "-1"] q c by simp
  also have "?this \<longleftrightarrow> ((\<lambda>n::nat. -ln (1 - c * q ^ n)) has_sum
                         lambert (\<lambda>n. c ^ n * of_nat n powi -1) q) {1..}"
  proof (intro has_sum_cong)
    fix n :: nat assume n: "n \<in> {1..}"
    have "norm c * norm (q ^ n) \<le> 1 * norm (q ^ n)"
      using q c by (intro mult_right_mono) auto
    also have "norm (q ^ n) \<le> norm q ^ 1"
      using n q unfolding norm_power by (intro power_decreasing) auto
    also have "1 * norm q ^ 1 < 1"
      using q by simp
    finally have cq: "norm (c * q ^ n) < 1"
      by (simp_all add: norm_mult)
    thus "polylog 1 (c * q ^ n) = -ln (1 - c * q ^ n)"
      by (subst polylog_1) auto
  qed
  also have "(\<lambda>n. c ^ n * of_nat n powi -1) = (\<lambda>n. c ^ n / of_nat n :: complex)"
    by (auto simp: field_simps)
  finally show ?thesis .
qed

lemma has_sum_lambert_recip_complex:
  fixes q :: complex
  assumes q: "norm q < 1"
  shows   "((\<lambda>k. -ln (1 - q ^ k)) has_sum lambert (\<lambda>n. 1 / of_nat n) q) {1..}"
  using has_sum_lambert_recip_complex_gen[OF assms, of 1] by simp

lemma has_sum_lambert_recip_complex':
  fixes q :: complex
  assumes q: "norm q < 1"
  shows   "((\<lambda>k. -ln (1 + q ^ k)) has_sum lambert (\<lambda>n. (-1) ^ n / of_nat n) q) {1..}"
  using has_sum_lambert_recip_complex_gen[OF assms, of "-1"] by simp

lemma has_sum_lambert_poly_complex:
  fixes q :: complex and a :: nat
  assumes q: "norm q < 1" and a: "a > 0"
  defines "E \<equiv> poly (eulerian_poly a)"
  shows   "((\<lambda>n. E (q ^ n) * q ^ n / (1 - q ^ n) ^ (a + 1)) has_sum
             lambert (\<lambda>n. complex_of_nat n ^ a) q) {1..}"
proof -
  have "((\<lambda>n. polylog (-a) (q ^ n)) has_sum lambert (\<lambda>n. of_nat n ^ a) q) {1..}"
    using lambert_power_int_has_sum_polylog_gen[OF q, of 1 a] q by simp
  also have "?this \<longleftrightarrow> ((\<lambda>n. E (q ^ n) * q ^ n / (1 - q ^ n) ^ (a+1))
                         has_sum lambert (\<lambda>n. of_nat n ^ a) q) {1..}"
  proof (rule has_sum_cong)
    fix n :: nat assume n: "n \<in> {1..}"
    have "norm (q ^ n) \<le> norm q ^ 1"
      using n q unfolding norm_power by (intro power_decreasing) auto
    also have "\<dots> < 1"
      using q by simp
    finally show "polylog (-a) (q ^ n) = E (q ^ n) * q ^ n / (1 - q ^ n) ^ (a+1)"
      using a by (subst polylog_neg_int_left)
                 (auto simp: E_def power_int_diff power_int_minus divide_simps)
  qed
  finally show ?thesis .
qed

lemma lambert_minus1_power_has_sum:
  assumes q: "norm q < 1"
  shows   "((\<lambda>n. q ^ n / (1 + q ^ n)) has_sum lambert (\<lambda>n. (-1) ^ Suc n) q) {1..}"
  using q
proof (rule lambert_conv_powser_has_sum')
  show "(\<lambda>n. (-1) ^ Suc (Suc n) * q ^ Suc n) sums (q / (1 + q))" if "norm q < 1" for q :: 'a
  proof -
    have "(\<lambda>n. (-1) ^ Suc (Suc n) * q ^ Suc n) sums (1 - 1 / (1 + q))"
      using sums_minus[OF geometric_sums[of "-q"]] that
      by (subst sums_Suc_iff) (auto simp: field_simps power_minus')
    also have "1 - 1 / (1 + q) = q / (1 + q)"
      using that by (auto simp: divide_simps add_eq_0_iff)
    finally show ?thesis .
  qed
qed auto

lemma lambert_exp_has_sum:
  fixes q :: "'a :: {real_normed_field, banach}"
  assumes q: "norm q < 1" and a: "norm a \<le> 1"
  shows   "((\<lambda>n. a * q ^ n / (1 - a * q ^ n)) has_sum lambert (\<lambda>n. a ^ n) q) {1..}"
proof -
  have "((\<lambda>n. a * q ^ n / (1 - a * q ^ n)) has_sum lambert (\<lambda>n. a ^ n * 1) q) {1..}"
    using q
  proof (rule lambert_mult_exp_conv_powser_has_sum)
    show "(\<lambda>n. 1 * q ^ Suc n) sums (q / (1 - q))" if "norm q < 1" for q :: 'a
      using geometric_sums_gen[of q 1] that by simp
  qed (use a in auto)
  thus ?thesis
    by simp
qed


subsection \<open>Connection to Euler's function\<close>

text \<open>
  In this section, we show a connection between Lambert series and Euler's function:
  \[\varphi(q) = \prod_{k=1}^\infty (1 - q ^ k)\]
  (not to be confused with Euler's totient function, commonly denoted with $\varphi(n)$)

  For this, we apply the results from the previous section to $a(n) = \frac{1}{n}$ to obtain:
  \[\sum_{k=1}^\infty \ln (1 - q^k) = -L\big(\tfrac{1}{n}, q\big)\]
\<close>
lemma sums_lambert_recip_complex:
  fixes q :: complex
  assumes q: "norm q < 1"
  shows   "((\<lambda>k. -ln (1 - q ^ Suc k)) sums lambert (\<lambda>n. 1 / of_nat n) q)"
  using q
proof (rule lambert_conv_powser_sums')
  show "(\<lambda>k. 1 / of_nat (Suc k) * q ^ Suc k) sums - Ln (1 - q)" if "norm q < 1" for q
    using sums_minus[OF Ln_series[of "-q"]] that
    by (subst sums_Suc_iff) (simp_all add: power_minus')
qed auto

lemma sums_lambert_recip_complex':
  fixes q :: complex
  assumes q: "norm q < 1"
  shows   "((\<lambda>k. -ln (1 + q ^ Suc k)) sums lambert (\<lambda>n. (-1)^n / of_nat n) q)"
  using q
proof (rule lambert_conv_powser_sums')
  show "(\<lambda>k. (-1)^Suc k / of_nat (Suc k) * q ^ Suc k) sums - Ln (1 + q)" if "norm q < 1" for q
    using sums_minus[OF Ln_series[of "q"]] that
    by (subst sums_Suc_iff) (simp_all add: power_minus')
qed auto

text \<open>
  By exponentiating this, we get:
  \[\varphi(q) \stackrel{\text{def}}{=} \prod_{n=1}^\infty \big(1 - q^n\big) =
     \exp\left(-\sum_{n=1}^\infty \frac{1}{n}\frac{q^n}{1-q^n}\right)\]
  In other words, the Lambert sum $\sum \frac{1}{n}\frac{q^n}{1-q^n}$ is a logarithm of
  Euler's function $\varphi(q)$.

  Note that this does not show that this is \<^emph>\<open>the\<close> logarithm of $\varphi(q)$, but merely that
  it is \<^emph>\<open>one\<close> of the branches of the multi-valued logarithm of $\varphi(q)$. Nevertheless, we 
  will -- just like is typically in textbooks -- ignore this in our informal explanations
  and write $\ln \varphi(q)$.
\<close>
theorem euler_phi_conv_lambert:
  fixes q :: complex
  assumes q: "norm q < 1"
  shows "(\<lambda>n. 1 - q ^ Suc n) has_prod exp (-lambert (\<lambda>n. 1 / of_nat n) q)"
proof -
  have not_1: "q ^ n \<noteq> 1" if "n > 0" for n
    using that q by (auto dest: power_eq_1_iff)
  have "(\<lambda>n. exp (-ln (1 - q ^ Suc n))) has_prod exp (lambert (\<lambda>n. 1 / of_nat n) q)"
    by (intro sums_imp_has_prod_exp sums_lambert_recip_complex q)
  also have "(\<lambda>n. exp (-ln (1 - q ^ Suc n))) = (\<lambda>n. inverse (1 - q ^ Suc n))"
    using q unfolding exp_minus by (subst exp_Ln) (auto simp del: power_Suc simp: not_1)
  finally have "(\<lambda>n. inverse (inverse (1 - q ^ Suc n))) has_prod
                   inverse (exp (lambert (\<lambda>n. 1 / complex_of_nat n) q))"
    by (intro has_prod_inverse)
  thus ?thesis
    using q by (simp del: power_Suc add: exp_minus)
qed

text \<open>
  With our general results on Lambert series, we also know that $\ln \varphi(q)$ has the power
  series expansion
  \[\ln\varphi(q) = -\sum_{n=1}^\infty \sigma_{-1}(n) q^n = 
      -\sum_{n=1}^\infty \frac{\sigma_1(n)}{n} q^n\ .\]
\<close>
lemma ln_euler_phi_powser:
  fixes q :: complex
  assumes q: "norm q < 1"
  shows "(\<lambda>n. divisor_sigma (-1) n * q ^ n) sums lambert (\<lambda>n. 1 / of_nat n) q"
  using divisor_sigma_powser_conv_lambert[OF q, of "-1"]
  by (simp add: powr_minus divide_inverse)

lemma ln_euler_phi_powser':
  fixes q :: complex
  assumes q: "norm q < 1"
  shows "(\<lambda>n. divisor_sum n / n * q ^ n) sums lambert (\<lambda>n. 1 / of_nat n) q"
  using ln_euler_phi_powser[OF q]
  by (simp add: divisor_sigma_minus divisor_sigma_1_left mult_ac)

text \<open>
  We also show the following variant of the above, also mentioned by Knopp:
\<close>
theorem euler_phi_variant_conv_lambert:
  fixes q :: complex
  assumes q: "norm q < 1"
  shows "(\<lambda>n. 1 + q ^ Suc n) has_prod exp (-lambert (\<lambda>n. (-1) ^ n / of_nat n) q)"
proof -
  have not_1: "q ^ n \<noteq> -1" if "n > 0" for n
  proof
    assume "q ^ n = -1"
    hence "norm q ^ n = 1"
      by (simp flip: norm_power)
    thus False
      using that q by (auto dest: power_eq_1_iff)
  qed
  have "(\<lambda>n. exp (-ln (1 + q ^ Suc n))) has_prod exp (lambert (\<lambda>n. (-1)^n / of_nat n) q)"
    by (intro sums_imp_has_prod_exp sums_lambert_recip_complex' q)
  also have "(\<lambda>n. exp (-ln (1 + q ^ Suc n))) = (\<lambda>n. inverse (1 + q ^ Suc n))"
    using q unfolding exp_minus
    by (subst exp_Ln) (auto simp del: power_Suc simp: not_1 add_eq_0_iff)
  finally have "(\<lambda>n. inverse (inverse (1 + q ^ Suc n))) has_prod
                   inverse (exp (lambert (\<lambda>n. (-1)^n / complex_of_nat n) q))"
    by (intro has_prod_inverse)
  thus ?thesis
    using q by (simp del: power_Suc add: exp_minus)
qed


subsection \<open>Application: Fibonacci numbers\<close>

text \<open>
  Lastly, we show a connection between the Fibonacci numbers and Lambert series, namely that:
  \[\sum_{n=1}^\infty \frac{1}{F_n} =
      \sqrt{5}\left[L\big(1, \tfrac{1}{2}(3-\sqrt{5})\big) - L\big(1, \tfrac{1}{2}(7-3\sqrt{5})\big)\right]\]
\<close>

lemma fib_closed_form_alt:
  defines "\<phi> \<equiv> (1 + sqrt 5) / 2"
  shows   "real (fib n) = (\<phi> ^ n - (-1 / \<phi>) ^ n) / sqrt 5"
proof -
  have "real (fib n) = (\<phi> ^ n - ((1 - sqrt 5) / 2) ^ n) / sqrt 5"
    unfolding \<phi>_def by (rule fib_closed_form)
  also have "1 + sqrt 5 > 0"
    by (intro add_pos_pos) auto
  hence "(1 - sqrt 5) / 2 = -(1 / \<phi>)"
    by (simp add: \<phi>_def field_simps)
  finally show ?thesis
    by simp
qed

theorem sum_inv_even_fib_conv_lambert:
  defines "L \<equiv> lambert (\<lambda>_. 1)"
  shows   "((\<lambda>n. 1 / real (fib (2*n))) has_sum
             (sqrt 5 * (L ((3 - sqrt 5) / 2) - L ((7 - 3 * sqrt 5) / 2)))) {1..}"
proof -
  define \<phi> :: real where "\<phi> = (1 + sqrt 5) / 2"
  have "1 + sqrt 5 > 0"
    by (intro add_pos_pos) auto
  hence [simp]: "1 + sqrt 5 \<noteq> 0"
    by auto
  have pos: "\<phi> > 1"
    by (auto simp: \<phi>_def intro: add_pos_pos)
  have [simp]: "\<phi> ^ k = 1 \<longleftrightarrow> k = 0" for k
    by (auto simp: \<phi>_def dest: power_eq_1_iff)
  have "((\<lambda>n. 1 * (1/\<phi>^2)^n / (1 - (1/\<phi>^2)^n) -  1 * (1/\<phi>^4)^n / (1 - (1/\<phi>^4)^n))
          has_sum (L (1/\<phi>^2) - L(1/\<phi>^4))) {1..}"
    unfolding L_def using pos
    by (intro has_sum_diff has_sum_lambert) (auto simp: field_simps intro!: one_less_power)
  also have "(\<lambda>n. 1 * (1/\<phi>^2)^n / (1 - (1/\<phi>^2)^n) -  1 * (1/\<phi>^4)^n / (1 - (1/\<phi>^4)^n)) =
             (\<lambda>n. 1 / (\<phi> ^ (2 * n) - (1 / \<phi>) ^ (2 * n)))" using pos
    by (simp add: divide_simps fun_eq_iff flip: power_mult)
       (simp add: algebra_simps flip: power_add)?
  also have "(\<dots> has_sum (L (1/\<phi>^2) - L(1/\<phi>^4))) {1..} \<longleftrightarrow>
             ((\<lambda>n. 1 / sqrt 5 * (1 / real (fib (2 * n)))) has_sum (L (1/\<phi>^2) - L(1/\<phi>^4))) {1..}"
  proof (intro has_sum_cong)
    fix n :: nat assume n: "n \<in> {1..}"
    have "\<phi> ^ (2 * n) - (1 / \<phi>) ^ (2 * n) = (\<phi> ^ (2 * n) - (-1 / \<phi>) ^ (2 * n))"
      by simp
    also have "\<dots> = real (fib (2 * n)) * sqrt 5"
      by (subst fib_closed_form_alt) (simp add: \<phi>_def)
    finally show "1 / (\<phi> ^ (2 * n) - (1 / \<phi>) ^ (2 * n)) = 1 / sqrt 5 * (1 / real (fib (2 * n)))"
      by simp
  qed
  also have "1 / \<phi> ^ 2 = (3 - sqrt 5) / 2"
    by (simp add: \<phi>_def power_divide power2_eq_square divide_simps) (auto simp: algebra_simps)?
  also have "1 / \<phi> ^ 4 = (7 - 3 * sqrt 5) / 2"
    by (simp add: \<phi>_def power_divide eval_nat_numeral divide_simps) (auto simp: algebra_simps)?
  finally have "((\<lambda>n. sqrt 5 * (1 / sqrt 5 * (1 / real (fib (2 * n))))) has_sum
                   sqrt 5 * (L ((3 - sqrt 5) / 2) - L ((7 - 3 * sqrt 5) / 2))) {1..}"
    by (intro has_sum_cmult_right)
  thus ?thesis
    by simp
qed    

end