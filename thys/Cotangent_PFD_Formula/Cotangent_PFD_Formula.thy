(*
  File:     Cotangent_PFD_Formula.thy
  Author:   Manuel Eberl, University of Innsbruck

  A proof of the "partial fraction decomposition"-style sum formula for the contangent function.
*)
section \<open>The Partial-Fraction Formula for the Cotangent Function\<close>
theory Cotangent_PFD_Formula
  imports "HOL-Complex_Analysis.Complex_Analysis" "HOL-Real_Asymp.Real_Asymp" 
begin

subsection \<open>Auxiliary lemmas\<close>

(* TODO Move *)
text \<open>
  The following variant of the comparison test for showing summability allows us to use
  a `Big-O' estimate, which works well together with Isabelle's automation for real asymptotics.
\<close>
lemma summable_comparison_test_bigo:
  fixes f :: "nat \<Rightarrow> real"
  assumes "summable (\<lambda>n. norm (g n))" "f \<in> O(g)"
  shows   "summable f"
proof -
  from \<open>f \<in> O(g)\<close> obtain C where C: "eventually (\<lambda>x. norm (f x) \<le> C * norm (g x)) at_top"
    by (auto elim: landau_o.bigE)
  thus ?thesis
    by (rule summable_comparison_test_ev) (insert assms, auto intro: summable_mult)
qed

lemma uniformly_on_image:
  "uniformly_on (f ` A) g = filtercomap (\<lambda>h. h \<circ> f) (uniformly_on A (g \<circ> f))"
  unfolding uniformly_on_def by (simp add: filtercomap_INF)

lemma uniform_limit_image:
  "uniform_limit (f ` A) g h F \<longleftrightarrow> uniform_limit A (\<lambda>x y. g x (f y)) (\<lambda>x. h (f x)) F"
  by (simp add: uniformly_on_image filterlim_filtercomap_iff o_def)

lemma Ints_add_iff1 [simp]: "x \<in> \<int> \<Longrightarrow> x + y \<in> \<int> \<longleftrightarrow> y \<in> \<int>"
  by (metis Ints_add Ints_diff add.commute add_diff_cancel_right')

lemma Ints_add_iff2 [simp]: "y \<in> \<int> \<Longrightarrow> x + y \<in> \<int> \<longleftrightarrow> x \<in> \<int>"
  by (metis Ints_add Ints_diff add_diff_cancel_right')

text \<open>
  If a set is discrete (i.e. the difference between any two points is bounded from below),
  it has no limit points:
\<close>
lemma discrete_imp_not_islimpt:
  assumes e: "0 < e"
    and d: "\<forall>x \<in> S. \<forall>y \<in> S. dist y x < e \<longrightarrow> y = x"
  shows "\<not>x islimpt S"
proof
  assume "x islimpt S"
  hence "x islimpt S - {x}"
    by (meson islimpt_punctured)
  moreover from assms have "closed (S - {x})"
    by (intro discrete_imp_closed) auto
  ultimately show False
    unfolding closed_limpt by blast
qed

text \<open>
  In particular, the integers have no limit point:
\<close>
lemma Ints_not_limpt: "\<not>((x :: 'a :: real_normed_algebra_1) islimpt \<int>)"
  by (rule discrete_imp_not_islimpt[of 1]) (auto elim!: Ints_cases simp: dist_of_int)

text \<open>
  The following lemma allows evaluating telescoping sums of the form
  \[\sum\limits_{n=0}^\infty \left(f(n) - f(n + k)\right)\]
  where $f(n) \longrightarrow 0$, i.e.\ where all terms except for the first \<open>k\<close> are
  cancelled by later summands.
\<close>
lemma sums_long_telescope:
  fixes f :: "nat \<Rightarrow> 'a :: {topological_group_add, topological_comm_monoid_add, ab_group_add}"
  assumes lim: "f \<longlonglongrightarrow> 0"
  shows "(\<lambda>n. f n - f (n + c)) sums (\<Sum>k<c. f k)" (is "_ sums ?S")
proof -
  thm tendsto_diff
  have "(\<lambda>N. ?S - (\<Sum>n<c. f (N + n))) \<longlonglongrightarrow> ?S - 0"
    by (intro tendsto_intros tendsto_null_sum filterlim_compose[OF assms]; real_asymp)
  hence "(\<lambda>N. ?S - (\<Sum>n<c. f (N + n))) \<longlonglongrightarrow> ?S"
    by simp
  moreover have "eventually (\<lambda>N. ?S - (\<Sum>n<c. f (N + n)) = (\<Sum>n<N. f n - f (n + c))) sequentially"
    using eventually_ge_at_top[of c]
  proof eventually_elim
    case (elim N)
    have "(\<Sum>n<N. f n - f (n + c)) = (\<Sum>n<N. f n) - (\<Sum>n<N. f (n + c))"
      by (simp only: sum_subtractf)
    also have "(\<Sum>n<N. f n) = (\<Sum>n\<in>{..<c} \<union> {c..<N}. f n)"
      using elim by (intro sum.cong) auto
    also have "\<dots> = (\<Sum>n<c. f n) + (\<Sum>n\<in>{c..<N}. f n)"
      by (subst sum.union_disjoint) auto
    also have "(\<Sum>n<N. f (n + c)) = (\<Sum>n\<in>{c..<N+c}. f n)"
      using elim by (intro sum.reindex_bij_witness[of _ "\<lambda>n. n - c" "\<lambda>n. n + c"]) auto
    also have "\<dots> = (\<Sum>n\<in>{c..<N}\<union>{N..<N+c}. f n)"
      using elim by (intro sum.cong) auto
    also have "\<dots> = (\<Sum>n\<in>{c..<N}. f n) + (\<Sum>n\<in>{N..<N+c}. f n)"
      by (subst sum.union_disjoint) auto
    also have "(\<Sum>n\<in>{N..<N+c}. f n) = (\<Sum>n<c. f (N + n))"
      by (intro sum.reindex_bij_witness[of _ "\<lambda>n. n + N" "\<lambda>n. n - N"]) auto
    finally show ?case
      by simp
  qed
  ultimately show ?thesis
    unfolding sums_def by (rule Lim_transform_eventually)
qed


subsection \<open>Definition of auxiliary function\<close>

text \<open>
  The following function is the infinite sum appearing on the right-hand side of the
  cotangent formula. It can be written either as
  \[\sum_{n=1}^\infty\left(\frac{1}{x + n} + \frac{1}{x - n}\right)\]
  or as
  \[2x \sum_{n=1}^\infty \frac{1}{x^2 - n^2}\ .\]
\<close>
definition cot_pfd :: "'a :: {real_normed_field, banach} \<Rightarrow> 'a" where
  "cot_pfd x = (\<Sum>n. 2 * x / (x ^ 2 - of_nat (Suc n) ^ 2))"

text \<open>
  The sum in the definition of \<^const>\<open>cot_pfd\<close> converges uniformly on compact sets.
  This implies, in particular, that \<^const>\<open>cot_pfd\<close> is holomorphic (and thus also continuous).
\<close>
lemma uniform_limit_cot_pfd_complex:
  assumes "R \<ge> 0"
  shows   "uniform_limit (cball 0 R :: complex set)
             (\<lambda>N x. \<Sum>n<N. 2 * x / (x ^ 2 - of_nat (Suc n) ^ 2)) cot_pfd sequentially"
  unfolding cot_pfd_def
proof (rule Weierstrass_m_test_ev)
  have "eventually (\<lambda>N. of_nat (N + 1) > R) at_top"
    by real_asymp
  thus "\<forall>\<^sub>F N in sequentially. \<forall>(x::complex)\<in>cball 0 R. norm (2 * x / (x ^ 2 - of_nat (Suc N) ^ 2)) \<le>
          2 * R / (real (N + 1) ^ 2 - R ^ 2)"
  proof eventually_elim
    case (elim N)
    show ?case
    proof safe
      fix x :: complex assume x: "x \<in> cball 0 R"
      have "(1 + real N)\<^sup>2 - R\<^sup>2 \<le> norm ((1 + of_nat N :: complex) ^ 2) - norm (x ^ 2)"
        using x by (auto intro: power_mono simp: norm_power simp flip: of_nat_Suc)
      also have "\<dots> \<le> norm (x\<^sup>2 - (1 + of_nat N :: complex)\<^sup>2)"
        by (metis norm_minus_commute norm_triangle_ineq2)
      finally show "norm (2 * x / (x\<^sup>2 - (of_nat (Suc N))\<^sup>2)) \<le> 2 * R / (real (N + 1) ^ 2 - R ^ 2)"
        unfolding norm_mult norm_divide using \<open>R \<ge> 0\<close> x elim
        by (intro mult_mono frac_le) (auto intro: power_strict_mono)
    qed
  qed
next
  show "summable (\<lambda>N. 2 * R / (real (N + 1) ^ 2 - R ^ 2))"
  proof (rule summable_comparison_test_bigo)
    show "(\<lambda>N. 2 * R / (real (N + 1) ^ 2 - R ^ 2)) \<in> O(\<lambda>N. 1 / real N ^ 2)"
      by real_asymp
  next
    show "summable (\<lambda>n. norm (1 / real n ^ 2))"
      using inverse_power_summable[of 2] by (simp add: field_simps)
  qed
qed

lemma sums_cot_pfd_complex:
  fixes x :: complex
  shows "(\<lambda>n. 2 * x / (x ^ 2 - of_nat (Suc n) ^ 2)) sums cot_pfd x"
  using tendsto_uniform_limitI[OF uniform_limit_cot_pfd_complex[of "norm x"], of x]
  by (simp add: sums_def)

lemma sums_cot_pfd_complex':
  fixes x :: complex
  assumes "x \<notin> \<int>"
  shows   "(\<lambda>n. 1 / (x + of_nat (Suc n)) + 1 / (x - of_nat (Suc n))) sums cot_pfd x"
proof -
  have "(\<lambda>n. 2 * x / (x ^ 2 - of_nat (Suc n) ^ 2)) sums cot_pfd x"
    by (rule sums_cot_pfd_complex)
  also have "(\<lambda>n. 2 * x / (x ^ 2 - of_nat (Suc n) ^ 2)) = 
             (\<lambda>n. 1 / (x + of_nat (Suc n)) + 1 / (x - of_nat (Suc n)))" (is "?lhs = ?rhs")
  proof
    fix n :: nat
    have neq1: "x + of_nat (Suc n) \<noteq> 0"
      using assms by (metis Ints_0 Ints_add_iff2 Ints_of_nat)
    have neq2: "x - of_nat (Suc n) \<noteq> 0"
      using assms by force
    have neq3: "x ^ 2 - of_nat (Suc n) ^ 2 \<noteq> 0"
     using assms by (metis Ints_of_nat eq_iff_diff_eq_0 minus_in_Ints_iff power2_eq_iff)
    show "?lhs n = ?rhs n" using neq1 neq2 neq3
      by (simp add: divide_simps del: of_nat_Suc) (auto simp: power2_eq_square algebra_simps)
  qed
  finally show ?thesis .
qed

lemma summable_cot_pfd_complex:
  fixes x :: complex
  shows "summable (\<lambda>n. 2 * x / (x ^ 2 - of_nat (Suc n) ^ 2))"
  using sums_cot_pfd_complex[of x] by (simp add: sums_iff)

lemma summable_cot_pfd_real:
  fixes x :: real
  shows "summable (\<lambda>n. 2 * x / (x ^ 2 - of_nat (Suc n) ^ 2))"
proof -
  have "summable (\<lambda>n. complex_of_real (2 * x / (x ^ 2 - of_nat (Suc n) ^ 2)))"
    using summable_cot_pfd_complex[of "of_real x"] by simp
  also have "?this \<longleftrightarrow> ?thesis"
    by (rule summable_of_real_iff)
  finally show ?thesis .
qed

lemma sums_cot_pfd_real:
  fixes x :: real
  shows "(\<lambda>n. 2 * x / (x ^ 2 - of_nat (Suc n) ^ 2)) sums cot_pfd x"
  using summable_cot_pfd_real[of x] by (simp add: cot_pfd_def sums_iff)

lemma cot_pfd_complex_of_real [simp]: "cot_pfd (complex_of_real x) = of_real (cot_pfd x)"
  using sums_of_real[OF sums_cot_pfd_real[of x], where ?'a = complex]
        sums_cot_pfd_complex[of "of_real x"] sums_unique2 by auto

lemma uniform_limit_cot_pfd_real:
  assumes "R \<ge> 0"
  shows   "uniform_limit (cball 0 R :: real set)
             (\<lambda>N x. \<Sum>n<N. 2 * x / (x ^ 2 - of_nat (Suc n) ^ 2)) cot_pfd sequentially"
proof -
  have "uniform_limit (cball 0 R)
          (\<lambda>N x. Re (\<Sum>n<N. 2 * x / (x ^ 2 - of_nat (Suc n) ^ 2))) (\<lambda>x. Re (cot_pfd x)) sequentially"
    by (intro uniform_limit_intros uniform_limit_cot_pfd_complex assms)
  hence "uniform_limit (of_real ` cball 0 R)
          (\<lambda>N x. Re (\<Sum>n<N. 2 * x / (x ^ 2 - of_nat (Suc n) ^ 2))) (\<lambda>x. Re (cot_pfd x)) sequentially"
    by (rule uniform_limit_on_subset) auto
  thus ?thesis
    by (simp add: uniform_limit_image)
qed


subsection \<open>Holomorphicity and continuity\<close>

lemma holomorphic_on_cot_pfd [holomorphic_intros]:
  assumes "A \<subseteq> -(\<int>-{0})"
  shows   "cot_pfd holomorphic_on A"
proof -
  have *: "open (-(\<int>-{0}) :: complex set)"
    by (intro open_Compl closed_subset_Ints) auto
  define f :: "nat \<Rightarrow> complex \<Rightarrow> complex"
    where "f = (\<lambda>N x. \<Sum>n<N. 2 * x / (x ^ 2 - of_nat (Suc n) ^ 2))"
  have "cot_pfd holomorphic_on -(\<int>-{0})"
  proof (rule holomorphic_uniform_sequence[OF *])
    fix n :: nat
    have **: "x\<^sup>2 - (of_nat (Suc n))\<^sup>2 \<noteq> 0" if "x \<in> -(\<int>-{0})" for x :: complex and n :: nat
    proof
      assume "x\<^sup>2 - (of_nat (Suc n))\<^sup>2 = 0"
      hence "(of_nat (Suc n))\<^sup>2 = x\<^sup>2"
        by algebra
      hence "x = of_nat (Suc n) \<or> x = -of_nat (Suc n)"
        by (subst (asm) eq_commute, subst (asm) power2_eq_iff) auto
      moreover have "(of_nat (Suc n) :: complex) \<in> \<int>" "(-of_nat (Suc n) :: complex) \<in> \<int>"
        by (intro Ints_minus Ints_of_nat)+
      ultimately show False using that
        by (auto simp del: of_nat_Suc)
    qed
    show "f n holomorphic_on -(\<int> - {0})"
      unfolding f_def by (intro holomorphic_intros **)
  next
    fix z :: complex assume z: "z \<in> -(\<int> - {0})"
    from * z obtain r where r: "r > 0" "cball z r \<subseteq> -(\<int>-{0})"
      using open_contains_cball by blast
    have "uniform_limit (cball z r) f cot_pfd sequentially"
      using uniform_limit_cot_pfd_complex[of "norm z + r"] unfolding f_def
    proof (rule uniform_limit_on_subset)
      show "cball z r \<subseteq> cball 0 (norm z + r)"
        unfolding cball_subset_cball_iff by (auto simp: dist_norm)
    qed (use \<open>r > 0\<close> in auto)
    with r show "\<exists>d>0. cball z d \<subseteq> - (\<int> - {0}) \<and> uniform_limit (cball z d) f cot_pfd sequentially"
      by blast
  qed
  thus ?thesis
    by (rule holomorphic_on_subset) fact
qed

lemma continuous_on_cot_pfd_complex [continuous_intros]:
  assumes "A \<subseteq> -(\<int>-{0})"
  shows   "continuous_on A (cot_pfd :: complex \<Rightarrow> complex)"
  by (rule holomorphic_on_imp_continuous_on holomorphic_intros assms)+

lemma continuous_on_cot_pfd_real [continuous_intros]:
  assumes "A \<subseteq> -(\<int>-{0})"
  shows   "continuous_on A (cot_pfd :: real \<Rightarrow> real)"
proof -
  have "continuous_on A (Re \<circ> cot_pfd \<circ> of_real)"
    by (intro continuous_intros) (use assms in auto)
  also have "Re \<circ> cot_pfd \<circ> of_real = cot_pfd"
    by auto
  finally show ?thesis .
qed


subsection \<open>Functional equations\<close>

text \<open>
  In this section, we will show three few functional equations for the function \<^const>\<open>cot_pfd\<close>.
  The first one is trivial; the other two are a bit tedious and not very insightful, so I
  will not comment on them.
\<close>

text \<open>\<^const>\<open>cot_pfd\<close> is an odd function:\<close>
lemma cot_pfd_complex_minus [simp]: "cot_pfd (-x :: complex) = -cot_pfd x"
proof -
  have "(\<lambda>n. 2 * (-x) / ((-x) ^ 2 - of_nat (Suc n) ^ 2)) =
        (\<lambda>n. - (2 * x / (x ^ 2 - of_nat (Suc n) ^ 2)))"
    by simp
  also have "\<dots> sums -cot_pfd x"
    by (intro sums_minus sums_cot_pfd_complex)
  finally show ?thesis
    using sums_cot_pfd_complex[of "-x"] sums_unique2 by blast
qed

lemma cot_pfd_real_minus [simp]: "cot_pfd (-x :: real) = -cot_pfd x"
  using cot_pfd_complex_minus[of "of_real x"]
  unfolding of_real_minus [symmetric] cot_pfd_complex_of_real of_real_eq_iff .

text \<open>\<^const>\<open>cot_pfd\<close> is periodic with period 1:\<close>
lemma cot_pfd_plus_1_complex:
  assumes "x \<notin> \<int>"
  shows   "cot_pfd (x + 1 :: complex) = cot_pfd x - 1 / (x + 1) + 1 / x"
proof -
  have *: "x ^ 2 \<noteq> of_nat n ^ 2" if "x \<notin> \<int>" for x :: complex and n
    using that by (metis Ints_of_nat minus_in_Ints_iff power2_eq_iff)
  have **: "x + of_nat n \<noteq> 0" if "x \<notin> \<int>" for x :: complex and n
    using that by (metis Ints_0 Ints_add_iff2 Ints_of_nat)
  have [simp]: "x \<noteq> 0"
    using assms by auto
  have [simp]: "x + 1 \<noteq> 0"
    using assms by (metis "**" of_nat_1)
  have [simp]: "x + 2 \<noteq> 0"
    using **[of x 2] assms by simp

  have lim: "(\<lambda>n. 1 / (x + of_nat (Suc n))) \<longlonglongrightarrow> 0"
    by (intro tendsto_divide_0[OF tendsto_const] tendsto_add_filterlim_at_infinity[OF tendsto_const]
              filterlim_compose[OF tendsto_of_nat] filterlim_Suc)
  have sum1: "(\<lambda>n. 1 / (x + of_nat (Suc n)) - 1 / (x + of_nat (Suc n + 2))) sums
          (\<Sum>n<2. 1 / (x + of_nat (Suc n)))"
    using sums_long_telescope[OF lim, of 2] by (simp add: algebra_simps)

  have "(\<lambda>n. 2 * x / (x\<^sup>2 - (of_nat (Suc n))\<^sup>2) - 2 * (x + 1) / ((x + 1)^2 - (of_nat (Suc (Suc n)))\<^sup>2))
          sums (cot_pfd x - (cot_pfd (x + 1) - 2 * (x + 1) / ((x + 1)^2 - (of_nat (Suc 0) ^ 2))))"
    using sums_cot_pfd_complex[of "x + 1"]
    by (intro sums_diff sums_cot_pfd_complex, subst sums_Suc_iff) auto
  also have "2 * (x + 1) / ((x + 1)^2 - (of_nat (Suc 0) ^ 2)) = 2 * (x + 1) / (x * (x + 2))"
    by (simp add: algebra_simps power2_eq_square)
  also have "(\<lambda>n. 2 * x / (x\<^sup>2 - (of_nat (Suc n))\<^sup>2) -
                  2 * (x + 1) / ((x + 1)\<^sup>2 - (of_nat (Suc (Suc n)))\<^sup>2)) =
             (\<lambda>n. 1 / (x + of_nat (Suc n)) - 1 / (x + of_nat (Suc n + 2)))"
    using *[of x] *[of "x + 1"] **[of x] **[of "x + 1"] assms
    apply (intro ext)
    apply (simp add: divide_simps del: of_nat_add of_nat_Suc)
    apply (simp add: algebra_simps power2_eq_square)
    done
  finally have sum2: "(\<lambda>n. 1 / (x + of_nat (Suc n)) - 1 / (x + of_nat (Suc n + 2))) sums
                         (cot_pfd x - cot_pfd (x + 1) + 2 * (x + 1) / (x * (x + 2)))"
    by (simp add: algebra_simps)

  have "cot_pfd x - cot_pfd (x + 1) + 2 * (x + 1) / (x * (x + 2)) =
        (\<Sum>n<2. 1 / (x + of_nat (Suc n)))"
    using sum1 sum2 sums_unique2 by blast
  hence "cot_pfd x - cot_pfd (x + 1) = -2 * (x + 1) / (x * (x + 2)) + 1 / (x + 1) + 1 / (x + 2)"
    by (simp add: eval_nat_numeral divide_simps) algebra?
  also have "\<dots> = 1 / (x + 1) - 1 / x"
    by (simp add: divide_simps) algebra?
  finally show ?thesis
    by algebra
qed
   
lemma cot_pfd_plus_1_real: 
  assumes "x \<notin> \<int>"
  shows   "cot_pfd (x + 1 :: real) = cot_pfd x - 1 / (x + 1) + 1 / x"
proof -
  have "cot_pfd (complex_of_real (x + 1)) = cot_pfd (of_real x) - 1 / (of_real x + 1) + 1 / of_real x"
    using cot_pfd_plus_1_complex[of x] assms by simp
  also have "\<dots> = complex_of_real (cot_pfd x - 1 / (x + 1) + 1 / x)"
    by simp
  finally show ?thesis
    unfolding cot_pfd_complex_of_real of_real_eq_iff .
qed

text \<open>
  \<^const>\<open>cot_pfd\<close> satisfies the following functional equation:
  \[2 f(x) = f\left(\frac{x}{2}\right) + f\left(\frac{x+1}{2}\right) + \frac{2}{x+1}\]
\<close>
lemma cot_pfd_funeq_complex:
  fixes x :: complex
  assumes "x \<notin> \<int>"
  shows   "2 * cot_pfd x = cot_pfd (x / 2) + cot_pfd ((x + 1) / 2) + 2 / (x + 1)"
proof -
  define f :: "complex \<Rightarrow> nat \<Rightarrow> complex" where "f = (\<lambda>x n. 1 / (x + of_nat (Suc n)))"
  define g :: "complex \<Rightarrow> nat \<Rightarrow> complex" where "g = (\<lambda>x n. 1 / (x - of_nat (Suc n)))"
  define h :: "complex \<Rightarrow> nat \<Rightarrow> complex" where "h = (\<lambda>x n. 2 * (f x (n + 1) + g x n))"

  have sums: "(\<lambda>n. f x n + g x n) sums cot_pfd x" if "x \<notin> \<int>" for x
    unfolding f_def g_def by (intro sums_cot_pfd_complex' that)

  have "x / 2 \<notin> \<int>"
  proof
    assume "x / 2 \<in> \<int>"
    hence "2 * (x / 2) \<in> \<int>"
      by (intro Ints_mult) auto
    thus False using assms by simp
  qed
  moreover have "(x + 1) / 2 \<notin> \<int>"
  proof
    assume "(x + 1) / 2 \<in> \<int>"
    hence "2 * ((x + 1) / 2) - 1 \<in> \<int>"
      by (intro Ints_mult Ints_diff) auto
    thus False using assms by (simp add: field_simps)
  qed
  ultimately have "(\<lambda>n. (f (x / 2) n + g (x / 2) n) + (f ((x+1) / 2) n + g ((x+1) / 2) n)) sums
                     (cot_pfd (x / 2) + cot_pfd ((x + 1) / 2))"
    by (intro sums_add sums)

  also have "(\<lambda>n. (f (x / 2) n + g (x / 2) n) + (f ((x+1) / 2) n + g ((x+1) / 2) n)) =
             (\<lambda>n. h x (2 * n) + h x (2 * n + 1))"
  proof
    fix n :: nat
    have "(f (x / 2) n + g (x / 2) n) + (f ((x+1) / 2) n + g ((x+1) / 2) n) =
          (f (x / 2) n + f ((x+1) / 2) n) + (g (x / 2) n + g ((x+1) / 2) n)"
      by algebra
    also have "f (x / 2) n + f ((x+1) / 2) n = 2 * (f x (2 * n + 1) + f x (2 * n + 2))"
      by (simp add: f_def field_simps)
    also have "g (x / 2) n + g ((x+1) / 2) n = 2 * (g x (2 * n) + g x (2 * n + 1))"
      by (simp add: g_def field_simps)
    also have "2 * (f x (2 * n + 1) + f x (2 * n + 2)) + \<dots> =
               h x (2 * n) + h x (2 * n + 1)"
      unfolding h_def by (simp add: algebra_simps)
    finally show "(f (x / 2) n + g (x / 2) n) + (f ((x+1) / 2) n + g ((x+1) / 2) n) =
                  h x (2 * n) + h x (2 * n + 1)" .
  qed
  finally have sum1:
    "(\<lambda>n. h x (2 * n) + h x (2 * n + 1)) sums (cot_pfd (x / 2) + cot_pfd ((x + 1) / 2))" .

  have "f x \<longlonglongrightarrow> 0" unfolding f_def
    by (intro tendsto_divide_0[OF tendsto_const]
              tendsto_add_filterlim_at_infinity[OF tendsto_const]
              filterlim_compose[OF tendsto_of_nat] filterlim_Suc)
  hence "(\<lambda>n. 2 * (f x n + g x n) + 2 * (f x (Suc n) - f x n)) sums (2 * cot_pfd x + 2 * (0 - f x 0))"
    by (intro sums_add sums sums_mult telescope_sums assms)
  also have "(\<lambda>n. 2 * (f x n + g x n) + 2 * (f x (Suc n) - f x n)) = h x"
    by (simp add: h_def algebra_simps fun_eq_iff)
  finally have *: "h x sums (2 * cot_pfd x - 2 * f x 0)"
    by simp

  have "(\<lambda>n. sum (h x) {n * 2..<n * 2 + 2}) sums (2 * cot_pfd x - 2 * f x 0)"
    using sums_group[OF *, of 2] by simp
  also have "(\<lambda>n. sum (h x) {n*2..<n*2+2}) = (\<lambda>n. h x (2 * n) + h x (2 * n + 1))"
    by (simp add: mult_ac)
  finally have sum2: "(\<lambda>n. h x (2 * n) + h x (2 * n + 1)) sums (2 * cot_pfd x - 2 * f x 0)" .

  have "cot_pfd (x / 2) + cot_pfd ((x + 1) / 2) = 2 * cot_pfd x - 2 * f x 0"
    using sum1 sum2 sums_unique2 by blast
  also have "2 * f x 0 = 2 / (x + 1)"
    by (simp add: f_def)
  finally show ?thesis by algebra
qed

lemma cot_pfd_funeq_real:
  fixes x :: real
  assumes "x \<notin> \<int>"
  shows   "2 * cot_pfd x = cot_pfd (x / 2) + cot_pfd ((x + 1) / 2) + 2 / (x + 1)"
proof -
  have "complex_of_real (2 * cot_pfd x) = 2 * cot_pfd (complex_of_real x)"
    by simp
  also have "\<dots> = complex_of_real (cot_pfd (x / 2) + cot_pfd ((x + 1) / 2) + 2 / (x + 1))"
    using assms by (subst cot_pfd_funeq_complex) (auto simp flip: cot_pfd_complex_of_real)
  finally show ?thesis
    by (simp only: of_real_eq_iff)
qed


subsection \<open>The limit at 0\<close>

lemma cot_pfd_real_tendsto_0: "cot_pfd \<midarrow>0\<rightarrow> (0 :: real)"
proof -
  have "filterlim cot_pfd (nhds 0) (at (0 :: real) within ball 0 1)"
  proof (rule swap_uniform_limit)
    show "uniform_limit (ball 0 1)
            (\<lambda>N x. \<Sum>n<N. 2 * x / (x\<^sup>2 - (real (Suc n))\<^sup>2)) cot_pfd sequentially"
      using uniform_limit_cot_pfd_real[OF zero_le_one] by (rule uniform_limit_on_subset) auto
    have "((\<lambda>x. 2 * x / (x\<^sup>2 - (real (Suc n))\<^sup>2)) \<longlongrightarrow> 0) (at 0 within ball 0 1)" for n
    proof (rule filterlim_mono)
      show "((\<lambda>x. 2 * x / (x\<^sup>2 - (real (Suc n))\<^sup>2)) \<longlongrightarrow> 0) (at 0)"
        by real_asymp
    qed (auto simp: at_within_le_at)
    thus "\<forall>\<^sub>F N in sequentially.
             ((\<lambda>x. \<Sum>n<N. 2 * x / (x\<^sup>2 - (real (Suc n))\<^sup>2)) \<longlongrightarrow> 0) (at 0 within ball 0 1)"
      by (intro always_eventually allI tendsto_null_sum)
  qed auto
  thus ?thesis
    by (simp add: at_within_open_NO_MATCH)
qed


subsection \<open>Final result\<close>

text \<open>
  To show the final result, we first prove the real case using Herglotz's trick, following
  the presentation in `Proofs from {THE BOOK}'.~\<^cite>\<open>\<open>Chapter~23\<close> in "thebook"\<close>.
\<close>
lemma cot_pfd_formula_real:
  assumes "x \<notin> \<int>"
  shows   "pi * cot (pi * x) = 1 / x + cot_pfd x"
proof -
  have ev_not_int: "eventually (\<lambda>x. r x \<notin> \<int>) (at x)"
    if "filterlim r (at (r x)) (at x)" for r :: "real \<Rightarrow> real" and x :: real
  proof (rule eventually_compose_filterlim[OF _ that])
    show "eventually (\<lambda>x. x \<notin> \<int>) (at (r x))"
      using Ints_not_limpt[of "r x"] islimpt_iff_eventually by blast
  qed

  text \<open>
    We define the function $h(z)$ as the difference of the left-hand side and right-hand side.
    The left-hand side and right-hand side have singularities at the integers, but we will
    later see that these can be removed as \<open>h\<close> tends to \<open>0\<close> there.
  \<close>
  define f :: "real \<Rightarrow> real" where "f = (\<lambda>x. pi * cot (pi * x))"
  define g :: "real \<Rightarrow> real" where "g = (\<lambda>x. 1 / x + cot_pfd x)"
  define h where "h = (\<lambda>x. if x \<in> \<int> then 0 else f x - g x)"

  have [simp]: "h x = 0" if "x \<in> \<int>" for x
    using that by (simp add: h_def)

  text \<open>
    It is easy to see that the left-hand side and the right-hand side, and as a consequence
    also our function \<open>h\<close>, are odd and periodic with period 1.
  \<close>
  have odd_h: "h (-x) = -h x" for x
    by (simp add: h_def minus_in_Ints_iff f_def g_def)
  have per_f: "f (x + 1) = f x" for x
    by (simp add: f_def algebra_simps cot_def)
  have per_g: "g (x + 1) = g x" if "x \<notin> \<int>" for x
    using that by (simp add: g_def cot_pfd_plus_1_real)
  interpret h: periodic_fun_simple' h
    by standard (auto simp: h_def per_f per_g)

  text \<open>
    \<open>h\<close> tends to 0 at 0 (and thus at all the integers).
  \<close>  
  have h_lim: "h \<midarrow>0\<rightarrow> 0"
  proof (rule Lim_transform_eventually)
    have "eventually (\<lambda>x. x \<notin> \<int>) (at (0 :: real))"
      by (rule ev_not_int) real_asymp
    thus "eventually (\<lambda>x::real. pi * cot (pi * x) - 1 / x - cot_pfd x = h x) (at 0)"
      by eventually_elim (simp add: h_def f_def g_def)
  next
    have "(\<lambda>x::real. pi * cot (pi * x) - 1 / x) \<midarrow>0\<rightarrow> 0"
      unfolding cot_def by real_asymp
    hence "(\<lambda>x::real. pi * cot (pi * x) - 1 / x - cot_pfd x) \<midarrow>0\<rightarrow> 0 - 0"
      by (intro tendsto_intros cot_pfd_real_tendsto_0)
    thus "(\<lambda>x. pi * cot (pi * x) - 1 / x - cot_pfd x) \<midarrow>0\<rightarrow> 0"
      by simp
  qed

  text \<open>
    This means that our \<open>h\<close> is in fact continuous everywhere:
  \<close>
  have cont_h: "continuous_on A h" for A
  proof -
    have "isCont h x" for x
    proof (cases "x \<in> \<int>")
      case True
      then obtain n where [simp]: "x = of_int n"
        by (auto elim: Ints_cases)
      show ?thesis unfolding isCont_def
        by (subst at_to_0) (use h_lim in \<open>simp add: filterlim_filtermap h.plus_of_int\<close>)
    next
      case False
      have "continuous_on (-\<int>) (\<lambda>x. f x - g x)"
        by (auto simp: f_def g_def sin_times_pi_eq_0 mult.commute[of pi] intro!: continuous_intros)
      hence "isCont (\<lambda>x. f x - g x) x"
        by (rule continuous_on_interior)
           (use False in \<open>auto simp: interior_open open_Compl[OF closed_Ints]\<close>)
      also have "eventually (\<lambda>y. y \<in> -\<int>) (nhds x)"
        using False by (intro eventually_nhds_in_open) auto
      hence "eventually (\<lambda>x. f x - g x = h x) (nhds x)"
        by eventually_elim (auto simp: h_def)
      hence "isCont (\<lambda>x. f x - g x) x \<longleftrightarrow> isCont h x"
        by (rule isCont_cong)
      finally show ?thesis .
    qed
    thus ?thesis
      by (simp add: continuous_at_imp_continuous_on)
  qed
  note [continuous_intros] = continuous_on_compose2[OF cont_h]

  text \<open>
    Through the functional equations of the sine and cosine function, we can derive
    the following functional equation for \<open>f\<close> that holds for all non-integer reals:
  \<close>
  have eq_f: "f x = (f (x / 2) + f ((x + 1) / 2)) / 2" if "x \<notin> \<int>" for x
  proof -
    have "x / 2 \<notin> \<int>"
      using that by (metis Ints_add field_sum_of_halves)
    hence nz1: "sin (x/2 * pi) \<noteq> 0"
      by (subst sin_times_pi_eq_0) auto

    have "(x + 1) / 2 \<notin> \<int>"
    proof
      assume "(x + 1) / 2 \<in> \<int>"
      hence "2 * ((x + 1) / 2) - 1 \<in> \<int>"
        by (intro Ints_mult Ints_diff) auto
      thus False using that by (simp add: field_simps)
    qed
    hence nz2: "sin ((x+1)/2 * pi) \<noteq> 0"
      by (subst sin_times_pi_eq_0) auto

    have nz3: "sin (x * pi) \<noteq> 0"
      using that by (subst sin_times_pi_eq_0) auto

    have eq: "sin (pi * x) = 2 * sin (pi * x / 2) * cos (pi * x / 2)"
             "cos (pi * x) = (cos (pi * x / 2))\<^sup>2 - (sin (pi * x / 2))\<^sup>2"
      using sin_double[of "pi * x / 2"] cos_double[of "pi * x / 2"] by simp_all
    show ?thesis using nz1 nz2 nz3
      apply (simp add: f_def cot_def field_simps )
      apply (simp add: add_divide_distrib sin_add cos_add power2_eq_square eq algebra_simps)
      done
  qed

  text \<open>
    The corresponding functional equation for \<^const>\<open>cot_pfd\<close> that we have already shown
    leads to the same functional equation for \<open>g\<close> as we just showed for \<open>f\<close>:
  \<close>
  have eq_g: "g x = (g (x / 2) + g ((x + 1) / 2)) / 2" if "x \<notin> \<int>" for x
    using cot_pfd_funeq_real[OF that] by (simp add: g_def)

  text \<open>
    This then leads to the same functional equation for \<open>h\<close>, and because \<open>h\<close> is continuous
    everywhere, we can extend the validity of the equation to the full domain.
  \<close>
  have eq_h: "h x = (h (x / 2) + h ((x + 1) / 2)) / 2" for x
  proof -
    have "eventually (\<lambda>x. x \<notin> \<int>) (at x)" "eventually (\<lambda>x. x / 2 \<notin> \<int>) (at x)"
         "eventually (\<lambda>x. (x + 1) / 2 \<notin> \<int>) (at x)"
      by (rule ev_not_int; real_asymp)+
    hence "eventually (\<lambda>x. h x - (h (x / 2) + h ((x + 1) / 2)) / 2 = 0) (at x)"
    proof eventually_elim
      case (elim x)
      thus ?case using eq_f[of x] eq_g[of x]
        by (simp add: h_def field_simps)
    qed
    hence "(\<lambda>x. h x - (h (x / 2) + h ((x + 1) / 2)) / 2) \<midarrow>x\<rightarrow> 0"
      by (simp add: tendsto_eventually)
    moreover have "continuous_on UNIV (\<lambda>x. h x - (h (x / 2) + h ((x + 1) / 2)) / 2)"
      by (auto intro!: continuous_intros)
    ultimately have "h x - (h (x / 2) + h ((x + 1) / 2)) / 2 = 0"
      by (meson LIM_unique UNIV_I continuous_on_def)
    thus ?thesis
      by simp
  qed

  text \<open>
    Since \<open>h\<close> is periodic with period 1 and continuous, it must attain a global maximum \<open>h\<close> 
    somewhere in the interval $[0, 1]$. Let's call this maximum $m$ and let $x_0$ be some point
    in the interval $[0, 1]$ such that $h(x_0) = m$.
  \<close>
  define m where "m = Sup (h ` {0..1})"
  have "m \<in> h ` {0..1}"
    unfolding m_def
  proof (rule closed_contains_Sup)
    have "compact (h ` {0..1})"
      by (intro compact_continuous_image cont_h) auto
    thus "bdd_above (h ` {0..1})" "closed (h ` {0..1})"
      by (auto intro: compact_imp_closed compact_imp_bounded bounded_imp_bdd_above)
  qed auto
  then obtain x0 where x0: "x0 \<in> {0..1}" "h x0 = m"
    by blast

  have h_le_m: "h x \<le> m" for x
  proof -
    have "h x = h (frac x)"
      unfolding frac_def by (rule h.minus_of_int [symmetric])
    also have "\<dots> \<le> m" unfolding m_def
    proof (rule cSup_upper)
      have "frac x \<in> {0..1}"
        using frac_lt_1[of x] by auto
      thus "h (frac x) \<in> h ` {0..1}"
        by blast
    next
      have "compact (h ` {0..1})"
        by (intro compact_continuous_image cont_h) auto
      thus "bdd_above (h ` {0..1})"
        by (auto intro: compact_imp_bounded bounded_imp_bdd_above)
    qed
    finally show ?thesis .
  qed

  text \<open>
    Through the functional equation for \<open>h\<close>, we can show that if \<open>h\<close> attains its maximum at
    some point \<open>x\<close>, it also attains it at $\frac{1}{2} x$. By iterating this, it attains the
    maximum at all points of the form $2^{-n} x_0$.
  \<close>
  have h_eq_m_iter_aux: "h (x / 2) = m" if "h x = m" for x
    using eq_h[of x] that h_le_m[of "x / 2"] h_le_m[of "(x + 1) / 2"] by simp
  have h_eq_m_iter: "h (x0 / 2 ^ n) = m" for n
  proof (induction n)
    case (Suc n)
    have "h (x0 / 2 ^ Suc n) = h (x0 / 2 ^ n / 2)"
      by (simp add: field_simps)
    also have "\<dots> = m"
      by (rule h_eq_m_iter_aux) (use Suc.IH in auto)
    finally show ?case .
  qed (use x0 in auto)

  text \<open>
    Since the sequence $n \mapsto 2^{-n} x_0$ tends to 0 and \<open>h\<close> is continuous, we derive \<open>m = 0\<close>.
  \<close>
  have "(\<lambda>n. h (x0 / 2 ^ n)) \<longlonglongrightarrow> h 0"
    by (rule continuous_on_tendsto_compose[OF cont_h[of UNIV]]) (force | real_asymp)+
  moreover from h_eq_m_iter have "(\<lambda>n. h (x0 / 2 ^ n)) \<longlonglongrightarrow> m"
    by simp
  ultimately have "m = h 0"
    using tendsto_unique by force
  hence "m = 0"
    by simp

  text \<open>
    Since \<open>h\<close> is odd, this means that \<open>h\<close> is identically zero everywhere, and our result follows.
  \<close>
  have "h x = 0"
    using h_le_m[of x] h_le_m[of "-x"] \<open>m = 0\<close> odd_h[of x] by linarith
  thus ?thesis
    using assms by (simp add: h_def f_def g_def)
qed


text \<open>
  We now lift the result from the domain \<open>\<real>\<setminus>\<int>\<close> to \<open>\<complex>\<setminus>\<int>\<close>. We do this by noting that \<open>\<complex>\<setminus>\<int>\<close> is
  connected and the point $\frac{1}{2}$ is both in \<open>\<complex>\<setminus>\<int>\<close> and a limit point of \<open>\<real>\<setminus>\<int>\<close>.
\<close>
lemma one_half_limit_point_Reals_minus_Ints: "(1 / 2 :: complex) islimpt \<real> - \<int>"
proof (rule islimptI)
  fix T :: "complex set"
  assume "1 / 2 \<in> T" "open T"
  then obtain r where r: "r > 0" "ball (1 / 2) r \<subseteq> T"
    using open_contains_ball by blast
  define y where "y = 1 / 2 + min r (1 / 2) / 2"
  have "y \<in> {0<..<1}"
    using r by (auto simp: y_def)
  hence "complex_of_real y \<in> \<real> - \<int>"
    by (auto elim!: Ints_cases)
  moreover have "complex_of_real y \<noteq> 1 / 2"
  proof
    assume "complex_of_real y = 1 / 2"
    also have "1 / 2 = complex_of_real (1 / 2)"
      by simp
    finally have "y = 1 / 2"
      unfolding of_real_eq_iff .
    with r show False
      by (auto simp: y_def)
  qed
  moreover have "complex_of_real y \<in> ball (1 / 2) r"
    using \<open>r > 0\<close> by (auto simp: y_def dist_norm)
  with r have "complex_of_real y \<in> T"
    by blast
  ultimately show "\<exists>y\<in>\<real> - \<int>. y \<in> T \<and> y \<noteq> 1 / 2"
    by blast
qed

theorem cot_pfd_formula_complex:
  fixes z :: complex
  assumes "z \<notin> \<int>"
  shows   "pi * cot (pi * z) = 1 / z + cot_pfd z"
proof -
  let ?f = "\<lambda>z::complex. pi * cot (pi * z) - 1 / z - cot_pfd z"
  have "pi * cot (pi * z) - 1 / z - cot_pfd z = 0"
  proof (rule analytic_continuation[where f = ?f])
    show "?f holomorphic_on -\<int>" 
      unfolding cot_def by (intro holomorphic_intros) (auto simp: sin_eq_0)
  next
    show "open (-\<int> :: complex set)" "connected (-\<int> :: complex set)"
      by (auto intro!: path_connected_imp_connected path_connected_complement_countable countable_int)
  next
    show "\<real> - \<int> \<subseteq> (-\<int> :: complex set)"
      by auto
  next
    show "(1 / 2 :: complex) islimpt \<real> - \<int>"
      by (rule one_half_limit_point_Reals_minus_Ints)
  next
    show "1 / (2 :: complex) \<in> -\<int>"
      using fraction_not_in_ints[of 2 1, where ?'a = complex] by auto
  next
    show "z \<in> -\<int>"
      using assms by simp
  next
    show "?f z = 0" if "z \<in> \<real> - \<int>" for z
    proof -
      have "complex_of_real pi * cot (complex_of_real pi * z) - 1 / z - cot_pfd z =
            complex_of_real (pi * cot (pi * Re z) - 1 / Re z - cot_pfd (Re z))"
        using that by (auto elim!: Reals_cases simp: cot_of_real)
      also have "\<dots> = 0"
        by (subst cot_pfd_formula_real) (use that in \<open>auto elim!: Reals_cases\<close>)
      finally show ?thesis .
    qed
  qed
  thus ?thesis
    by algebra
qed

end