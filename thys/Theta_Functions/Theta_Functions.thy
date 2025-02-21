section \<open>General theta functions\<close>
theory Theta_Functions
imports
  Nome
  "Combinatorial_Q_Analogues.Q_Binomial_Identities"
  Theta_Functions_Library
begin

subsection \<open>The Ramanujan theta function\<close>

text \<open>
  We define the other theta functions in terms of the Ramanujan theta function:
  \[f(a,b) = \sum_{n=-\infty}^\infty a^{n(n+1)/2} b^{n(n-1)/2}\hskip1.5em (\text{for}\ |ab|<1)\]
  This is, in some sense, more general than Jacobi's theta function: Jacobi's theta function can
  be expressed very easily in terms of Ramanujan's; the other direction is only straightforward
  in the real case. Due to the presence of square roots, the complex case becomes tedious
  due to branch cuts.

  However, even in the complex case, results can be transferred from Jacobi's theta function
  to Ramanujan's by using the connection on the real line and then doing analytic continuation.

  Some of the proofs below are loosely based on Ramanujan's lost notebook (as edited by 
  Berndt~\<^cite>\<open>berndt1991\<close>).
\<close>
definition ramanujan_theta :: "'a :: {real_normed_field, banach} \<Rightarrow> 'a \<Rightarrow> 'a" where
  "ramanujan_theta a b =
     (if norm (a*b) < 1 then (\<Sum>\<^sub>\<infinity>n. a powi (n*(n+1) div 2) * b powi (n*(n-1) div 2)) else 0)"

lemma ramanujan_theta_outside [simp]: "norm (a * b) \<ge> 1 \<Longrightarrow> ramanujan_theta a b = 0"
  by (simp add: ramanujan_theta_def)

lemma uniform_limit_ramanujan_theta:
  fixes A :: "('a \<times> 'a :: {real_normed_field, banach}) set"
  assumes "compact A" "\<And>a b. (a, b) \<in> A \<Longrightarrow> norm (a * b) < 1"
  shows   "uniform_limit A (\<lambda>X (a,b). \<Sum>n\<in>X. a powi (n*(n+1) div 2) * b powi (n*(n-1) div 2))
             (\<lambda>(a,b). \<Sum>\<^sub>\<infinity>n. a powi (n*(n+1) div 2) * b powi (n*(n-1) div 2))
             (finite_subsets_at_top UNIV)"
proof (cases "A = {}")
  case False
  define f where "f = (\<lambda>n ab. fst ab powi (n*(n+1) div 2) * snd ab powi (n*(n-1) div 2) :: 'a)"
  define y where "y = max (1/2) (Sup ((\<lambda>(a,b). norm (a * b)) ` A))"
  define x where "x = max 2 (Sup ((\<lambda>(a,b). max (norm a) (norm b)) ` A))"

  have le_x: "norm a \<le> x" "norm b \<le> x" if "(a, b) \<in> A" for a b
  proof -
    have bounded: "bounded ((\<lambda>(a,b). max (norm a) (norm b)) ` A)"
      unfolding case_prod_unfold
      by (intro compact_imp_bounded compact_continuous_image continuous_intros assms)
    have "(\<lambda>(a,b). max (norm a) (norm b)) (a, b) \<le> Sup ((\<lambda>(a,b). max (norm a) (norm b)) ` A)"
      by (rule cSup_upper imageI)+
         (use that bounded in \<open>auto intro: bounded_imp_bdd_above\<close>)
    also have "\<dots> \<le> x"
      unfolding x_def by linarith
    finally show "norm a \<le> x" "norm b \<le> x"
      by simp_all
  qed

  have le_y: "norm (a*b) \<le> y" if "(a, b) \<in> A" for a b
  proof -
    have bounded: "bounded ((\<lambda>(a,b). norm (a * b)) ` A)"
      unfolding case_prod_unfold
      by (intro compact_imp_bounded compact_continuous_image continuous_intros assms)
    have "(\<lambda>(a,b). norm (a * b)) (a, b) \<le> Sup ((\<lambda>(a,b). norm (a * b)) ` A)"
      by (rule cSup_upper imageI)+
         (use that bounded in \<open>auto intro: bounded_imp_bdd_above\<close>)
    also have "\<dots> \<le> y"
      unfolding y_def by linarith
    finally show ?thesis
      by simp
  qed

  have "x > 1" "y > 0"
    unfolding x_def y_def by linarith+

  have "y < 1"
  proof -
    have "Sup ((\<lambda>(a,b). norm (a * b)) ` A) \<in> (\<lambda>(a,b). norm (a * b)) ` A" using \<open>A \<noteq> {}\<close>
      unfolding case_prod_unfold
      by (intro closed_contains_Sup compact_imp_closed compact_continuous_image
                bounded_imp_bdd_above compact_imp_bounded continuous_intros assms) auto
    with assms show ?thesis
      by (auto simp: y_def)
  qed

  define h where "h = (\<lambda>n. x ^ nat \<bar>n\<bar> * y ^ nat (min (n*(n+1) div 2) (n*(n-1) div 2)))"

  have "uniform_limit A (\<lambda>X wq. \<Sum>n\<in>X. f n wq) (\<lambda>wq. \<Sum>\<^sub>\<infinity>n. f n wq) (finite_subsets_at_top UNIV)"
  proof (rule Weierstrass_m_test_general, clarify)
    fix n :: int and a b :: 'a
    assume ab: "(a, b) \<in> A"
    have eq: "n * (n + 1) div 2 = n * (n - 1) div 2 + n"
      by (simp add: algebra_simps)
    have nonneg: "n * (n - 1) div 2 \<ge> 0" "n * (n + 1) div 2 \<ge> 0" "n * (n - 1) \<ge> 0" "n * (n + 1) \<ge> 0"
      by (auto simp: zero_le_mult_iff)

    have "norm (f n (a, b)) = norm a powi (n*(n+1) div 2) * norm b powi (n*(n-1) div 2)"
      by (simp add: f_def norm_mult norm_power_int)
    also have "(n*(n+1) div 2) = int (nat (n*(n+1) div 2))"
      by (auto simp: zero_le_mult_iff)
    also have "(n*(n-1) div 2) = int (nat (n*(n-1) div 2))"
      by (auto simp: zero_le_mult_iff)
    also have "norm a powi int (nat (n*(n+1) div 2)) * norm b powi int (nat (n*(n-1) div 2)) =
               norm a ^ nat (n*(n+1) div 2) * norm b ^ nat (n*(n-1) div 2)"
      unfolding power_int_of_nat ..
    also have "\<dots> = (if n \<ge> 0 then norm a ^ nat \<bar>n\<bar> * norm (a*b) ^ nat (n*(n-1) div 2)
                              else norm b ^ nat \<bar>n\<bar> * norm (a*b) ^ nat (n*(n+1) div 2))"
      using nonneg(1,2) [[linarith_split_limit = 0]] unfolding eq
      by (auto simp flip: power_add simp: power_mult_distrib norm_mult nat_eq_iff nonneg(3,4)
               intro!: arg_cong[of _ _ "\<lambda>n. x ^ n" for x] split: if_splits)
    also have "\<dots> \<le> x ^ nat \<bar>n\<bar> * norm (a*b) ^ nat (min (n*(n+1) div 2) (n*(n-1) div 2))"
      using le_x[of a b] ab \<open>x > 1\<close> le_y[of a b] \<open>y < 1\<close> [[linarith_split_limit = 0]]
      by (auto intro!: mult_mono power_mono power_decreasing nat_mono)
    also have "\<dots> \<le> x ^ nat \<bar>n\<bar> * y ^ nat (min (n*(n+1) div 2) (n*(n-1) div 2))"
      by (intro mult_left_mono power_mono le_y) (use ab \<open>x > 1\<close> in auto)
    also have "\<dots> = h n"
      by (simp add: h_def)
    finally show "norm (f n (a, b)) \<le> h n" .
  next
    obtain y' where y': "y < y'" "y' < 1"
      using \<open>y < 1\<close> dense by blast
    have "summable (\<lambda>n. norm (h (int n)))"
    proof (rule summable_comparison_test_bigo)
      have "(\<lambda>n. x ^ n * y ^ nat (min (int n * (int n + 1) div 2) (int n * (int n - 1) div 2))) \<in> O(\<lambda>n. y' ^ n)"
        using \<open>x > 1\<close> \<open>y > 0\<close> y' by real_asymp
      thus "(\<lambda>n. norm (h (int n))) \<in> O(\<lambda>n. y' ^ n)"
        unfolding h_def by (simp add: norm_power norm_mult nat_power_eq power_int_def)
    next
      show "summable (\<lambda>n. norm (y' ^ n))"
        unfolding norm_power by (rule summable_geometric) (use \<open>y > 0\<close> y' in auto)
    qed
    hence "(\<lambda>n. h (int n)) summable_on UNIV"
      by (rule norm_summable_imp_summable_on)
    also have "?this \<longleftrightarrow> h summable_on {0..}"
      by (rule summable_on_reindex_bij_witness[of _nat int]) auto
    finally have *: "h summable_on {0..}" .

    from * have "h summable_on {0<..}"
      by (rule summable_on_subset) auto
    also have "h summable_on {0<..} \<longleftrightarrow> h summable_on {..<0}"
      by (rule summable_on_reindex_bij_witness[of _ "\<lambda>n. -n" "\<lambda>n. -n"]) 
         (auto simp: h_def algebra_simps)
    finally have "h summable_on {..<0}" .
    from this and * have "h summable_on {..<0} \<union> {0..}"
      by (rule summable_on_union)
    also have "{..<0} \<union> {0..} = (UNIV :: int set)"
      by auto
    finally show "h summable_on UNIV" .
  qed
  thus ?thesis
    by (simp add: f_def case_prod_unfold)
qed auto

lemma has_sum_ramanujan_theta:
  assumes "norm (a*b) < 1"
  shows   "((\<lambda>n. a powi (n*(n+1) div 2) * b powi (n*(n-1) div 2)) has_sum ramanujan_theta a b) UNIV"
proof -
  show ?thesis
    using uniform_limit_ramanujan_theta[of "{(a, b)}"] assms
    by (simp add: ramanujan_theta_def has_sum_def uniform_limit_singleton)
qed


lemma ramanujan_theta_commute: "ramanujan_theta a b = ramanujan_theta b a"
proof (cases "norm (a * b) < 1")
  case ab: True
  have "((\<lambda>n. a powi (n*(n+1) div 2) * b powi (n*(n-1) div 2)) has_sum ramanujan_theta a b) UNIV"
    by (intro has_sum_ramanujan_theta ab)
  also have "?this \<longleftrightarrow> ((\<lambda>n. b powi (n*(n+1) div 2) * a powi (n*(n-1) div 2)) has_sum ramanujan_theta a b) UNIV"
    by (intro has_sum_reindex_bij_witness[of _ uminus uminus]) (auto simp: algebra_simps)
  finally have \<dots> .
  moreover have "((\<lambda>n. b powi (n*(n+1) div 2) * a powi (n*(n-1) div 2)) has_sum ramanujan_theta b a) UNIV"
    by (intro has_sum_ramanujan_theta) (use ab in \<open>simp_all add: norm_mult mult.commute\<close>)
  ultimately show ?thesis
    using has_sum_unique by blast
qed (simp_all add: ramanujan_theta_def mult.commute)

lemma ramanujan_theta_0_left [simp]: "ramanujan_theta 0 b = 1 + b"
proof -
  have *: "n * (n + 1) div 2 = 0 \<longleftrightarrow> n \<in> {0, -1}" for n :: int
  proof -
    have "even (n * (n + 1))"
      by auto
    hence "n * (n + 1) div 2 = 0 \<longleftrightarrow> n * (n + 1) = 0"
      by (elim evenE) simp_all
    also have "\<dots> \<longleftrightarrow> n \<in> {0, -1}"
      unfolding mult_eq_0_iff by auto
    finally show ?thesis .
  qed
  have "((\<lambda>n. 0 powi (n*(n+1) div 2) * b powi (n*(n-1) div 2)) has_sum (1 + b)) {0, -1}"
    by (rule has_sum_finiteI) auto
  also have "?this \<longleftrightarrow> ((\<lambda>n. 0 powi (n*(n+1) div 2) * b powi (n*(n-1) div 2)) has_sum (1 + b)) UNIV"
    by (intro has_sum_cong_neutral) (auto simp: *)
  finally have "((\<lambda>n. 0 powi (n*(n+1) div 2) * b powi (n*(n-1) div 2)) has_sum (1 + b)) UNIV" .
  moreover have "((\<lambda>n. 0 powi (n*(n+1) div 2) * b powi (n*(n-1) div 2)) has_sum ramanujan_theta 0 b) UNIV"
    by (intro has_sum_ramanujan_theta) auto
  ultimately show ?thesis
    using has_sum_unique by blast
qed

lemma ramanujan_theta_0_right [simp]: "ramanujan_theta a 0 = 1 + a"
  by (subst ramanujan_theta_commute) simp_all

lemma has_sum_ramanujan_theta1:
  assumes "norm (a*b) < 1" and [simp]: "a \<noteq> 0"
  shows   "((\<lambda>n. a powi n * (a*b) powi (n*(n-1) div 2)) has_sum ramanujan_theta a b) UNIV"
proof -
  have eq: "n*(n+1) div 2 = n*(n-1) div 2 + n" for n :: int
    by (cases "even n") (auto elim!: evenE oddE simp: algebra_simps)
  have "((\<lambda>n. a powi (n*(n+1) div 2) * b powi (n*(n-1) div 2)) has_sum ramanujan_theta a b) UNIV"
    by (rule has_sum_ramanujan_theta) (use assms in auto)
  thus ?thesis
    unfolding eq by (simp add: power_int_mult_distrib power_int_add mult_ac)
qed

lemma has_sum_ramanujan_theta2:
  assumes "norm (a * b) < 1"
  shows    "((\<lambda>n. (a*b) powi (n*(n-1) div 2) * (a powi n + b powi n)) has_sum
               (ramanujan_theta a b - 1)) {1..}"
proof (cases "a * b = 0")
  case True
  have "((\<lambda>n. (a*b) powi (n*(n-1) div 2) * (a powi n + b powi n)) has_sum (ramanujan_theta a b - 1)) {1}"
    using True by (intro has_sum_finiteI) auto
  also have "?this \<longleftrightarrow> ?thesis"
    using True by (intro has_sum_cong_neutral) (auto simp: dvd_div_eq_0_iff) 
  finally show ?thesis .
next
  case False
  hence [simp]: "a \<noteq> 0" "b \<noteq> 0"
    by auto
  define S1 where "S1 = (\<Sum>\<^sub>\<infinity>n\<in>{1..}. a powi (n*(n+1) div 2) * b powi (n*(n-1) div 2))"
  define S2 where "S2 = (\<Sum>\<^sub>\<infinity>n\<in>{..-1}. a powi (n*(n+1) div 2) * b powi (n*(n-1) div 2))"
  have eq: "n*(n+1) div 2 = n*(n-1) div 2 + n" for n :: int
    by (cases "even n") (auto elim!: evenE oddE simp: algebra_simps)

  have 1: "((\<lambda>n. a powi (n*(n+1) div 2) * b powi (n*(n-1) div 2)) has_sum ramanujan_theta a b) UNIV"
    by (rule has_sum_ramanujan_theta) (use assms in auto)

  have [intro]: "(\<lambda>n. a powi (n*(n+1) div 2) * b powi (n*(n-1) div 2)) summable_on A" for A
    by (rule summable_on_subset_banach, rule has_sum_imp_summable[OF 1]) auto

  have S1: "((\<lambda>n. a powi (n*(n+1) div 2) * b powi (n*(n-1) div 2)) has_sum S1) {1..}"
    unfolding S1_def by (rule has_sum_infsum) rule
  also have "(\<lambda>n. a powi (n*(n+1) div 2) * b powi (n*(n-1) div 2)) =
             (\<lambda>n. (a*b) powi (n*(n-1) div 2) * a powi n)"
    unfolding eq by (auto simp: power_int_mult_distrib power_int_add mult_ac)
  finally have S1': "((\<lambda>n. (a * b) powi (n * (n - 1) div 2) * a powi n) has_sum S1) {1..}" .

  have S2: "((\<lambda>n. a powi (n*(n+1) div 2) * b powi (n*(n-1) div 2)) has_sum S2) {..-1}"
    unfolding S2_def by (rule has_sum_infsum) rule
  also have "?this \<longleftrightarrow> ((\<lambda>n. b powi (n*(n+1) div 2) * a powi (n*(n-1) div 2)) has_sum S2) {1..}"
    by (rule has_sum_reindex_bij_witness[of _ uminus uminus]) (auto simp: algebra_simps)
  also have "(\<lambda>n. b powi (n*(n+1) div 2) * a powi (n*(n-1) div 2)) =
             (\<lambda>n. (a*b) powi (n*(n-1) div 2) * b powi n)"
    unfolding eq by (auto simp: power_int_mult_distrib power_int_add mult_ac)
  finally have S2': "((\<lambda>n. (a * b) powi (n * (n - 1) div 2) * b powi n) has_sum S2) {1..}" .

  have "((\<lambda>n. a powi (n*(n+1) div 2) * b powi (n*(n-1) div 2)) has_sum (ramanujan_theta a b - 1)) (UNIV-{0})"
    using 1 by (rule has_sum_Diff) (auto simp: has_sum_finite_iff)
  also have "UNIV - {0::int} = {1..} \<union> {..-1}"
    by auto
  finally have "((\<lambda>n. a powi (n*(n+1) div 2) * b powi (n*(n-1) div 2)) has_sum
                   (ramanujan_theta a b - 1)) ({1..} \<union> {..-1})" .
  moreover have "((\<lambda>n. a powi (n*(n+1) div 2) * b powi (n*(n-1) div 2)) has_sum
                   (S1 + S2)) ({1..} \<union> {..-1})"
    by (intro has_sum_Un_disjoint S1 S2) auto
  ultimately have "ramanujan_theta a b - 1 = S1 + S2"
    using has_sum_unique by blast

  moreover have "((\<lambda>n. (a * b) powi (n * (n - 1) div 2) * (a powi n + b powi n)) has_sum (S1 + S2)) {1..}"
    using has_sum_add[OF S1' S2'] by (simp add: algebra_simps)
  ultimately show "((\<lambda>n. (a*b) powi (n*(n-1) div 2) * (a powi n + b powi n)) 
                     has_sum (ramanujan_theta a b - 1)) {1..}"
    by simp
qed

lemma ramanujan_theta_of_real:
  "ramanujan_theta (of_real a) (of_real b) = of_real (ramanujan_theta a b)"
proof (cases "norm (a*b) < 1")
  case ab: True
  have "((\<lambda>n. of_real (a powi (n*(n+1) div 2) * b powi (n*(n-1) div 2)) :: 'a) has_sum
          of_real (ramanujan_theta a b)) UNIV"
    by (intro has_sum_of_real has_sum_ramanujan_theta) (use ab in auto)
  also have "(\<lambda>n. of_real (a powi (n*(n+1) div 2) * b powi (n*(n-1) div 2)) :: 'a) = 
                 (\<lambda>n. of_real a powi (n*(n+1) div 2) * of_real b powi (n*(n-1) div 2))" by simp
  finally have "((\<lambda>n. of_real a powi (n * (n + 1) div 2) * of_real b powi (n * (n - 1) div 2)) has_sum
                  (of_real (ramanujan_theta a b) :: 'a)) UNIV" .
  moreover have "((\<lambda>n. of_real a powi (n*(n+1) div 2) * of_real b powi (n*(n-1) div 2) :: 'a) has_sum 
                     ramanujan_theta (of_real a) (of_real b)) UNIV"
    by (rule has_sum_ramanujan_theta) (use ab in \<open>auto simp: norm_mult\<close>)
  ultimately show ?thesis
    using has_sum_unique by blast
qed (auto simp: ramanujan_theta_def norm_mult abs_mult)

lemma ramanujan_theta_cnj:
  "ramanujan_theta (cnj a) (cnj b) = cnj (ramanujan_theta a b)"
proof (cases "norm (a*b) < 1")
  case ab: True
  have "((\<lambda>n. cnj (a powi (n*(n+1) div 2) * b powi (n*(n-1) div 2))) has_sum cnj (ramanujan_theta a b)) UNIV"
    unfolding has_sum_cnj_iff by (intro has_sum_ramanujan_theta) (use ab in auto)
  also have "(\<lambda>n. cnj (a powi (n*(n+1) div 2) * b powi (n*(n-1) div 2))) = 
             (\<lambda>n. cnj a powi (n*(n+1) div 2) * cnj b powi (n*(n-1) div 2))"
    by simp
  finally have "((\<lambda>n. cnj a powi (n*(n+1) div 2) * cnj b powi (n*(n-1) div 2)) has_sum
                  cnj (ramanujan_theta a b)) UNIV" .
  moreover have "((\<lambda>n. cnj a powi (n*(n+1) div 2) * cnj b powi (n*(n-1) div 2)) has_sum 
                     ramanujan_theta (cnj a) (cnj b)) UNIV"
    by (rule has_sum_ramanujan_theta) (use ab in \<open>auto simp: norm_mult\<close>)
  ultimately show ?thesis
    using has_sum_unique by blast
qed (auto simp: ramanujan_theta_def norm_mult)

lemma ramanujan_theta_holomorphic [holomorphic_intros]:
  assumes "f holomorphic_on A" "g holomorphic_on A"
  assumes "\<And>z. z \<in> A \<Longrightarrow> norm (f z * g z) < 1"  "open A"
  shows   "(\<lambda>z. ramanujan_theta (f z) (g z)) holomorphic_on A"
proof -
  have "(\<lambda>z. ramanujan_theta (f z) (g z)) analytic_on {z}" if "z \<in> A" for z
  proof -
    obtain r where r: "r > 0" "cball z r \<subseteq> A"
      using \<open>open A\<close> \<open>z \<in> A\<close> open_contains_cball_eq by blast
    define h where "h = (\<lambda>X (w,q). \<Sum>n\<in>X. w powi (n*(n+1) div 2) * q powi (n*(n-1) div 2) :: complex)"
    define H where "H = (\<lambda>(w,q). \<Sum>\<^sub>\<infinity>n. w powi (n*(n+1) div 2) * q powi (n*(n-1) div 2) :: complex)"

    have lim: "uniform_limit (cball z r)
                 (\<lambda>X x. h X (f x, g x)) (\<lambda>x. H (f x, g x)) (finite_subsets_at_top UNIV)"
      unfolding h_def H_def
    proof (rule uniform_limit_compose'[OF uniform_limit_ramanujan_theta])
      show "compact ((\<lambda>x. (f x, g x)) ` cball z r)" using r
        by (intro compact_continuous_image)
           (auto intro!: continuous_intros holomorphic_on_imp_continuous_on
                         assms(1,2)[THEN holomorphic_on_subset])
    qed (use r assms(3,4) in auto)

    have "(\<lambda>x. H (f x, g x)) holomorphic_on ball z r"
      by (rule holomorphic_uniform_limit[OF _ lim])
         (use r in \<open>auto intro!: always_eventually continuous_intros holomorphic_intros
                                 holomorphic_on_imp_continuous_on
                                 assms(1,2)[THEN holomorphic_on_subset] assms(3)
                         simp: h_def zero_le_mult_iff\<close>)
    also have "?this \<longleftrightarrow> (\<lambda>x. ramanujan_theta (f x) (g x)) holomorphic_on ball z r"
    proof (rule holomorphic_cong)
      fix w assume "w \<in> ball z r"
      hence "w \<in> A"
        using r by auto
      hence "norm (f w * g w) < 1"
        using assms(3) by auto
      thus "H (f w, g w) = ramanujan_theta (f w) (g w)"
        by (auto simp: H_def ramanujan_theta_def)
    qed auto
    finally show ?thesis
      using \<open>r > 0\<close> analytic_at_ball by blast
  qed
  hence "(\<lambda>z. ramanujan_theta (f z) (g z)) analytic_on A"
    using analytic_on_analytic_at by blast
  thus ?thesis
    using analytic_imp_holomorphic by auto
qed

lemma ramanujan_theta_analytic [analytic_intros]:
  assumes "f analytic_on A" "g analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> norm (f z * g z) < 1"
  shows   "(\<lambda>z. ramanujan_theta (f z) (g z)) analytic_on A"
proof -
  from assms(1) obtain B1 where B1: "open B1" "A \<subseteq> B1" "f holomorphic_on B1"
    using analytic_on_holomorphic by metis
  from assms(2) obtain B2 where B2: "open B2" "A \<subseteq> B2" "g holomorphic_on B2"
    using analytic_on_holomorphic by metis
  note [holomorphic_intros] = holomorphic_on_subset[OF B1(3)] holomorphic_on_subset[OF B2(3)]

  define B3 where "B3 = B1 \<inter> B2 \<inter> (\<lambda>z. f z * g z) -` ball 0 1"
  have "open B3" using B1 B2 unfolding B3_def
    by (intro continuous_open_preimage holomorphic_on_imp_continuous_on
              holomorphic_intros open_halfspace_Im_gt) auto
  hence B3: "open B3" "B3 \<subseteq> B1" "B3 \<subseteq> B2" "\<And>z. z \<in> B3 \<Longrightarrow> f z * g z \<in> ball 0 1"
    unfolding B3_def by auto
  
  have "(\<lambda>z. ramanujan_theta (f z) (g z)) holomorphic_on B3"
    using B3 by (auto intro!: holomorphic_intros)
  moreover have "A \<subseteq> B3"
    using assms(3) B1 B2 by (auto simp: B3_def)
  ultimately show ?thesis
    using \<open>open B3\<close> analytic_on_holomorphic by metis
qed

lemma tendsto_ramanujan_theta [tendsto_intros]:
  fixes f g :: "'a \<Rightarrow> 'b :: {real_normed_field, banach, heine_borel}"
  assumes "(f \<longlongrightarrow> a) F" "(g \<longlongrightarrow> b) F" "norm (a * b) < 1"
  shows   "((\<lambda>z. ramanujan_theta (f z) (g z)) \<longlongrightarrow> ramanujan_theta a b) F"
proof -
  have "isCont (\<lambda>(w,q). ramanujan_theta w q) z" if z: "norm (fst z * snd z) < 1" for z :: "'b \<times> 'b"
  proof -
    have "z \<in> (\<lambda>z. (fst z * snd z)) -` ball 0 1"
      using z by auto
    moreover have "open ((\<lambda>z. (fst z * snd z :: 'b)) -` ball 0 1)"
      by (intro open_vimage continuous_intros) auto
    ultimately obtain r where r: "r > 0" "cball z r \<subseteq> (\<lambda>z. (fst z * snd z)) -` ball 0 1"
      by (meson open_contains_cball)

    have "continuous_on (cball z r)
            (\<lambda>(a, b). \<Sum>\<^sub>\<infinity>n. a powi (n * (n + 1) div 2) * b powi (n * (n - 1) div 2))"
    proof (rule uniform_limit_theorem)
      show "uniform_limit (cball z r)
              (\<lambda>X (a, b). \<Sum>n\<in>X. a powi (n * (n + 1) div 2) * b powi (n * (n - 1) div 2))
              (\<lambda>(a, b). \<Sum>\<^sub>\<infinity>n. a powi (n * (n + 1) div 2) * b powi (n * (n - 1) div 2)) 
              (finite_subsets_at_top UNIV)"
        by (rule uniform_limit_ramanujan_theta) (use r in auto)
    qed (auto intro!: always_eventually continuous_intros 
              simp: case_prod_unfold dist_norm zero_le_mult_iff)
    also have "?this \<longleftrightarrow> continuous_on (cball z r) (\<lambda>(a,b). ramanujan_theta a b)"
      by (intro continuous_on_cong) (use r in \<open>auto simp: ramanujan_theta_def\<close>)
    finally have "continuous_on (ball z r) (\<lambda>(a,b). ramanujan_theta a b)"
      by (rule continuous_on_subset) auto
    thus ?thesis
      using \<open>r > 0\<close> centre_in_ball continuous_on_interior interior_ball by blast
  qed
  from this[of "(a, b)"] have isCont: "isCont (\<lambda>(w,q). ramanujan_theta w q) (a, b)"
    using assms by simp
  have lim: "((\<lambda>x. (f x, g x)) \<longlongrightarrow> (a, b)) F"
    using assms by (intro tendsto_intros)
  show ?thesis
    using isCont_tendsto_compose[OF isCont lim] by simp
qed

lemma continuous_on_ramanujan_theta [continuous_intros]:
  fixes f g :: "'a :: topological_space \<Rightarrow> 'b :: {real_normed_field, banach, heine_borel}"
  assumes "continuous_on A f" "continuous_on A g" "\<And>z. z \<in> A \<Longrightarrow> norm (f z * g z) < 1"
  shows   "continuous_on A (\<lambda>z. ramanujan_theta (f z) (g z))"
proof -
  have *: "continuous_on {z. norm (fst z * snd z) < 1} (\<lambda>(a,b). ramanujan_theta a b :: 'b)"
    unfolding continuous_on by (auto intro!: tendsto_eq_intros simp: case_prod_unfold)
  have "continuous_on A ((\<lambda>(x,y). ramanujan_theta x y) \<circ> (\<lambda>x. (f x, g x)))"
    by (intro continuous_on_compose continuous_on_subset[OF *] continuous_intros)
       (use assms in auto)
  thus ?thesis
    by (simp add: o_def)
qed

lemma continuous_ramanujan_theta [continuous_intros]:
  fixes f g :: "'a :: t2_space \<Rightarrow> 'b :: {real_normed_field, banach, heine_borel}"
  assumes "continuous F f" "continuous F g" "norm (f (netlimit F) * g (netlimit F)) < 1"
  shows   "continuous F (\<lambda>z. ramanujan_theta (f z) (g z))"
  unfolding continuous_def
  using assms by (auto intro!: tendsto_eq_intros simp: continuous_def)

lemma ramanujan_theta_1_left: 
  "ramanujan_theta 1 a = 2 * ramanujan_theta a (a ^ 3)"
proof (cases "a \<noteq> 0 \<and> norm a < 1")
  case False
  hence "a = 0 \<or> norm a \<ge> 1"
    by auto
  thus ?thesis
  proof
    assume "norm a \<ge> 1"
    thus ?thesis
      by (auto simp: ramanujan_theta_def norm_power power_less_one_iff
               simp flip: power_Suc2 power_Suc)
  qed auto
next
  case a: True
  hence [simp]: "a \<noteq> 0"
    by auto
  define S1 where "S1 = (\<Sum>\<^sub>\<infinity>n\<in>{0..}. a powi (n*(n+1) div 2))"
  define S2 where "S2 = (\<Sum>\<^sub>\<infinity>n\<in>{..-1}. a powi (n*(n+1) div 2))"

  have 1: "((\<lambda>n. a powi (n*(n+1) div 2)) has_sum ramanujan_theta 1 a) UNIV"
    using has_sum_ramanujan_theta[of a 1] a by (simp add: ramanujan_theta_commute)
  have summable: "(\<lambda>n. a powi (n*(n+1) div 2)) summable_on A" for A
    by (rule summable_on_subset_banach, rule has_sum_imp_summable[OF 1]) auto

  have S1: "((\<lambda>n. a powi (n*(n+1) div 2)) has_sum S1) {0..}"
    unfolding S1_def by (rule has_sum_infsum, rule summable)
  also have "?this \<longleftrightarrow> ((\<lambda>n. a powi (n*(n+1) div 2)) has_sum S1) {..-1}"
    by (intro has_sum_reindex_bij_witness[of _ "\<lambda>n. -n-1" "\<lambda>n. -n-1"]) (auto simp: algebra_simps)
  finally have S1': "((\<lambda>n. a powi (n*(n+1) div 2)) has_sum S1) {..-1}" .

  have "((\<lambda>n. a powi (n*(n+1) div 2)) has_sum (S1 + S1)) ({..-1} \<union> {0..})"
    by (intro has_sum_Un_disjoint S1 S1') auto
  also have "{..-1} \<union> {0::int..} = UNIV"
    by auto
  finally have "((\<lambda>n. a powi (n * (n + 1) div 2)) has_sum (2*S1)) UNIV"
    by simp
  with 1 have "ramanujan_theta 1 a = 2 * S1"
    using has_sum_unique by blast

  define S2 where "S2 = (\<Sum>\<^sub>\<infinity>n | n \<ge> 0 \<and> even n. a powi (n*(n+1) div 2))"
  define S3 where "S3 = (\<Sum>\<^sub>\<infinity>n | n \<ge> 0 \<and> odd n. a powi (n*(n+1) div 2))"
  have "((\<lambda>n. a powi (n*(n+1) div 2)) has_sum (S2 + S3)) ({n. n \<ge> 0 \<and> even n} \<union> {n. n \<ge> 0 \<and> odd n})"
    unfolding S2_def S3_def by (intro has_sum_Un_disjoint has_sum_infsum summable) auto
  also have "{n. n \<ge> 0 \<and> even n} \<union> {n. n \<ge> 0 \<and> odd n} = {0::int..}"
    by auto
  finally have "S1 = S2 + S3"
    using S1 has_sum_unique by blast

  have "((\<lambda>n. a powi (n*(n+1) div 2)) has_sum S2) {n. n \<ge> 0 \<and> even n}"
    unfolding S2_def by (intro has_sum_Un_disjoint has_sum_infsum summable)
  also have "?this \<longleftrightarrow> ((\<lambda>n. a powi (n*(2*n+1))) has_sum S2) {0..}"
    by (intro has_sum_reindex_bij_witness[of _ "\<lambda>n. 2*n" "\<lambda>n. n div 2"]) auto
  also have "(\<lambda>n::int. n*(2*n+1)) = (\<lambda>n. (n*(n-1) div 2) + 3*((n*(n+1)) div 2))"
  proof
    fix n :: int
    show "n*(2*n+1) = (n*(n-1) div 2) + 3*((n*(n+1)) div 2)"
      by (cases "even n") (auto elim!: evenE oddE simp: algebra_simps)
  qed
  also have "(\<lambda>n. a powi \<dots> n) = (\<lambda>n. a powi (n*(n-1) div 2) * (a ^ 3) powi (n*(n+1) div 2))"
    by (simp add: power_int_add power_int_power)
  finally have S2: "((\<lambda>n. a powi (n*(n-1) div 2) * (a ^ 3) powi (n*(n+1) div 2)) has_sum S2) {0..}" .

  have "((\<lambda>n. a powi (n*(n+1) div 2)) has_sum S3) {n. n \<ge> 0 \<and> odd n}"
    unfolding S3_def by (intro has_sum_Un_disjoint has_sum_infsum summable)
  also have "?this \<longleftrightarrow> ((\<lambda>n. a powi (n*(2*n-1))) has_sum S3) {1..}"
    by (intro has_sum_reindex_bij_witness[of _ "\<lambda>n. 2*n-1" "\<lambda>n. (n+1) div 2"]) 
       (auto elim!: oddE simp: algebra_simps)
  also have "(\<lambda>n::int. n*(2*n-1)) = (\<lambda>n. (n*(n+1) div 2) + 3*(n*(n-1) div 2))"
  proof
    fix n :: int
    show "n*(2*n-1) = (n*(n+1) div 2) + 3*(n*(n-1) div 2)"
      by (cases "even n") (auto elim!: evenE oddE simp: algebra_simps)
  qed
  also have "(\<lambda>n. a powi \<dots> n) = (\<lambda>n. a powi (n*(n+1) div 2) * (a^3) powi (n*(n-1) div 2))"
    by (simp add: power_int_add power_int_power)
  finally have "((\<lambda>n. a powi (n*(n+1) div 2) * (a^3) powi (n*(n-1) div 2)) has_sum S3) {1..}" .
  also have "?this \<longleftrightarrow> ((\<lambda>n. a powi (n*(n-1) div 2) * (a^3) powi (n*(n+1) div 2)) has_sum S3) {..-1}"
    by (intro has_sum_reindex_bij_witness[of _ "\<lambda>n. -n" "\<lambda>n. -n"]) (auto simp: algebra_simps)
  finally have S3: "((\<lambda>n. a powi (n*(n-1) div 2) * (a^3) powi (n*(n+1) div 2)) has_sum S3) {..-1}" .

  have "((\<lambda>n. a powi (n*(n-1) div 2) * (a^3) powi (n*(n+1) div 2)) has_sum (S2 + S3)) ({0..} \<union> {..-1})"
    by (intro has_sum_Un_disjoint S2 S3) auto
  also have "{0::int..} \<union> {..-1} = UNIV"
    by auto
  finally have "((\<lambda>n. (a^3) powi (n*(n+1) div 2) * a powi (n*(n-1) div 2)) has_sum S2 + S3) UNIV"
    by (simp add: mult.commute)
  moreover have "((\<lambda>n. (a^3) powi (n*(n+1) div 2) * a powi (n*(n-1) div 2)) has_sum
                   ramanujan_theta (a^3) a) UNIV"
    by (intro has_sum_ramanujan_theta) 
       (use a in \<open>auto simp: norm_power power_less_one_iff simp flip: power_Suc2\<close>)
  ultimately have "ramanujan_theta (a^3) a = S2 + S3"
    using has_sum_unique by blast
  also have "S2 + S3 = S1"
    by (rule sym) fact
  also have "S1 = ramanujan_theta 1 a / 2"
    using \<open>ramanujan_theta 1 a = 2 * S1\<close> by (simp add: field_simps)
  finally show ?thesis
    by (simp add: field_simps ramanujan_theta_commute)
qed

lemma ramanujan_theta_1_right: "ramanujan_theta a 1 = 2 * ramanujan_theta a (a ^ 3)"
  by (subst ramanujan_theta_commute, rule ramanujan_theta_1_left)

lemma ramanujan_theta_neg1_left [simp]: "ramanujan_theta (-1) a = 0"
proof (cases "a \<noteq> 0 \<and> norm a < 1")
  case False
  hence "a = 0 \<or> norm a \<ge> 1"
    by auto
  thus ?thesis
  proof
    assume "norm a \<ge> 1"
    thus ?thesis
      by (auto simp: ramanujan_theta_def norm_power power_less_one_iff
               simp flip: power_Suc2 power_Suc)
  qed auto
next
  case a: True
  hence [simp]: "a \<noteq> 0"
    by auto
  define S1 where "S1 = (\<Sum>\<^sub>\<infinity>n\<in>{1..}. (-1) powi (n*(n+1) div 2) * a powi (n*(n-1) div 2))"
  define S2 where "S2 = (\<Sum>\<^sub>\<infinity>n\<in>{..-2}. (-1) powi (n*(n+1) div 2) * a powi (n*(n-1) div 2))"

  have sum: "((\<lambda>n. (-1) powi (n*(n+1) div 2) * a powi (n*(n-1) div 2)) has_sum ramanujan_theta (-1) a) UNIV"
    using has_sum_ramanujan_theta[of "-1" a] a by simp
  have summable: "(\<lambda>n. (-1) powi (n*(n+1) div 2) * a powi (n*(n-1) div 2)) summable_on A" for A
    by (rule summable_on_subset_banach, rule has_sum_imp_summable[OF sum]) auto

  have S1: "((\<lambda>n. (-1) powi (n*(n+1) div 2) * a powi (n*(n-1) div 2)) has_sum S1) {1..}"
    unfolding S1_def by (rule has_sum_infsum, rule summable)
  also have "?this \<longleftrightarrow> ((\<lambda>n. (-1) powi ((n-2)*(n-1) div 2) * a powi (n*(n-1) div 2)) has_sum S1) {..0}"
    by (intro has_sum_reindex_bij_witness[of _ "\<lambda>n. -n+1" "\<lambda>n. -n+1"]) (auto simp: algebra_simps)
  also have "(\<lambda>n. (n-2)*(n-1) div 2) = (\<lambda>n::int. n*(n+1) div 2 - 2 * n + 1)"
    by (auto simp: algebra_simps)
  also have "(\<lambda>n. (-1) powi (n*(n+1) div 2 - 2*n + 1)) =
             (\<lambda>n. - ((-1) powi (n*(n+1) div 2) :: 'a))"
    by (simp add: power_int_add power_int_diff)
  finally have S1': "((\<lambda>n. ((-1) powi (n*(n+1) div 2) * a powi (n*(n-1) div 2))) has_sum (-S1)) {..0}"
    by (simp add: has_sum_uminus)

  have "((\<lambda>n. ((-1) powi (n*(n+1) div 2) * a powi (n*(n-1) div 2))) has_sum (-S1 + S1)) ({..0} \<union> {1..})"
    by (intro has_sum_Un_disjoint S1 S1') auto
  also have "{..0} \<union> {1::int..} = UNIV"
    by auto
  also have "-S1 + S1 = 0"
    by simp
  finally show ?thesis
    using sum has_sum_unique by blast
qed

lemma ramanujan_theta_neg1_right [simp]: "ramanujan_theta a (-1) = 0"
  by (subst ramanujan_theta_commute) auto

lemma ramanujan_theta_mult_power_int:
  assumes [simp]: "a \<noteq> 0" "b \<noteq> 0"
  shows   "ramanujan_theta a b =
             a powi (m*(m+1) div 2) * b powi (m*(m-1) div 2) *
             ramanujan_theta (a * (a*b) powi m) (b * (a*b) powi (-m))"
proof (cases "norm (a * b) < 1")
  case False
  thus ?thesis
    by (simp add: ramanujan_theta_def field_simps power_int_minus)
next
  case True
  hence [simp]: "a \<noteq> 0" "b \<noteq> 0"
    by auto
  define e1 e2 where "e1 = (m*(m+1) div 2)" and "e2 = (m*(m-1) div 2)"
  define a' b' where "a' = a*(a*b) powi m" and "b' = b*(a*b) powi -m"
  have eq: "n * (n + 1) div 2 = n * (n - 1) div 2 + n" for n :: int
    by (auto simp: algebra_simps)

  have "((\<lambda>n. a powi e1 * b powi e2 * (a' powi (n*(n+1) div 2) * b' powi (n*(n-1) div 2)))
           has_sum (a powi e1 * b powi e2 * ramanujan_theta a' b')) UNIV"
    by (intro has_sum_cmult_right has_sum_ramanujan_theta)
       (use True in \<open>auto simp: a'_def b'_def power_int_minus field_simps\<close>)

  also have "(\<lambda>n. a powi e1 * b powi e2 * (a' powi (n*(n+1) div 2) * b' powi (n*(n-1) div 2))) =
             (\<lambda>n. a powi ((n+m)*(n+m+1) div 2) * b powi ((n+m)*(n+m-1) div 2))" (is "?lhs = ?rhs")
  proof
    fix n :: int
    have "a powi e1 * b powi e2 * (a' powi (n*(n+1) div 2) * b' powi (n*(n-1) div 2)) = 
          a powi (e1 + (n*(n+1) div 2) + m*(n*(n+1) div 2) - m*(n*(n-1) div 2)) *
          b powi (e2 + (n*(n-1) div 2) + m*(n*(n+1) div 2) - m*(n*(n-1) div 2))"
      unfolding a'_def b'_def
      by (simp add: a'_def b'_def power_int_mult_distrib power_int_add power_int_diff power_int_minus
                    power_int_divide_distrib field_simps flip: power_int_mult)

    also have "e1 + (n*(n+1) div 2) + m*(n*(n+1) div 2) - m*(n*(n-1) div 2) = 
               (m * (m + 1) + 2 * m * n) div 2 + (n*(n+1) div 2)"
      unfolding eq by (simp add: algebra_simps e1_def)
    also have "\<dots> = (m * (m + 1) + 2 * m * n + n * (n + 1)) div 2"
      by (rule div_add [symmetric]) auto
    also have "(m * (m + 1) + 2 * m * n + n * (n + 1)) = (n+m)*(n+m+1)"
      by Groebner_Basis.algebra

    also have "e2 + (n*(n-1) div 2) + m*(n*(n+1) div 2) - m*(n*(n-1) div 2) = 
               (m*(m-1) + 2*m*n) div 2 + (n*(n-1) div 2)"
      unfolding eq by (simp add: algebra_simps e2_def)
    also have "\<dots> = (m*(m-1) + 2*m*n + n*(n-1)) div 2"
      by (rule div_add [symmetric]) auto
    also have "m*(m-1) + 2*m*n + n*(n-1) = (n+m)*(n+m-1)"
      by Groebner_Basis.algebra

    finally show "?lhs n = ?rhs n" .
  qed

  also have "((\<lambda>n. a powi ((n+m)*(n+m+1) div 2) * b powi ((n+m)*(n+m-1) div 2)) has_sum 
               (a powi e1 * b powi e2 * ramanujan_theta a' b')) UNIV \<longleftrightarrow> 
             ((\<lambda>n. a powi (n * (n + 1) div 2) * b powi (n * (n - 1) div 2)) has_sum
               (a powi e1 * b powi e2 * ramanujan_theta a' b')) UNIV"
    by (intro has_sum_reindex_bij_witness[of _ "\<lambda>n. n - m" "\<lambda>n. n + m"]) auto
  finally have \<dots> .
  moreover have "((\<lambda>n. a powi (n * (n + 1) div 2) * b powi (n * (n - 1) div 2)) has_sum
                   ramanujan_theta a b) UNIV"
    by (rule has_sum_ramanujan_theta) (use True in auto)
  ultimately have "a powi e1 * b powi e2 * ramanujan_theta a' b' = ramanujan_theta a b"
    using has_sum_unique by blast
  thus ?thesis
    by (simp add: e1_def e2_def a'_def b'_def)
qed

lemma ramanujan_theta_mult:
  assumes [simp]: "a \<noteq> 0" "b \<noteq> 0"
  shows   "ramanujan_theta a b = a * ramanujan_theta (a\<^sup>2 * b) (1 / a)"
  using ramanujan_theta_mult_power_int[of a b 1]
  by (simp add: eval_nat_numeral field_simps)

lemma ramanujan_theta_mult':
  assumes [simp]: "a \<noteq> 0" "b \<noteq> 0"
  shows   "ramanujan_theta a b = b * ramanujan_theta (1 / b) (a * b\<^sup>2)"
  using ramanujan_theta_mult[of b a] by (simp add: ramanujan_theta_commute mult.commute)

subsection \<open>The Jacobi theta function in terms of the nome\<close>

text \<open>
  Based on Ramanujan's \<open>\<theta>\<close> function, we introduce a version of Jacobi's \<open>\<theta>\<close> function:
  \[\vartheta(w,q) = \sum_{n=-\infty}^\infty w^n q^{n^2}\hskip1.5em (\text{for}\ |q|<1, w\neq 0)\]
  Both parameters are still in terms of the nome rather than the complex plane.
  This has some advantages, and we can easily derive the other versions from it later.
\<close>
definition jacobi_theta_nome :: "'a :: {real_normed_field,banach} \<Rightarrow> 'a \<Rightarrow> 'a" where
  "jacobi_theta_nome w q = (if w = 0 then 0 else ramanujan_theta (q*w) (q/w))"

lemma jacobi_theta_nome_0_left [simp]: "jacobi_theta_nome 0 q = 0"
  by (simp add: jacobi_theta_nome_def)

lemma jacobi_theta_nome_outside [simp]: 
  assumes "norm q \<ge> 1"
  shows   "jacobi_theta_nome w q = 0"
proof (cases "w = 0")
  case False
  thus ?thesis using assms
    by (simp add: jacobi_theta_nome_def norm_mult ramanujan_theta_def power_less_one_iff norm_power
             flip: power2_eq_square)
qed auto

lemma has_sum_jacobi_theta_nome:
  assumes "norm q < 1" and [simp]: "w \<noteq> 0"
  shows   "((\<lambda>n. w powi n * q powi (n ^ 2)) has_sum jacobi_theta_nome w q) UNIV"
proof (cases "q = 0")
  case True
  have "((\<lambda>_::int. 1) has_sum jacobi_theta_nome w q) {0}"
    by (intro has_sum_finiteI) (use True in \<open>auto simp: jacobi_theta_nome_def\<close>)
  also have "?this \<longleftrightarrow> ?thesis"
    using True by (intro has_sum_cong_neutral) auto
  finally show ?thesis .
next
  case False
  hence [simp]: "q \<noteq> 0" "w \<noteq> 0"
    by auto
  have "((\<lambda>n. (q*w) powi (n*(n+1) div 2) * (q/w) powi (n*(n-1) div 2)) has_sum ramanujan_theta (q*w) (q/w)) UNIV"
    by (rule has_sum_ramanujan_theta)
       (use assms in \<open>auto simp: norm_power power_less_one_iff simp flip: power2_eq_square\<close>)
  also have "(\<lambda>n. (q*w) powi (n*(n+1) div 2) * (q/w) powi (n*(n-1) div 2)) =
             (\<lambda>n. w powi ((n*(n+1) div 2) - (n*(n-1) div 2)) * q powi ((n*(n+1) div 2) + (n*(n-1) div 2)))"
    by (simp add: power_int_mult_distrib power_int_divide_distrib power_int_add power_int_diff field_simps)
  also have "(\<lambda>n::int. (n*(n+1) div 2) - (n*(n-1) div 2)) = (\<lambda>n. n)"
    by (auto simp: fun_eq_iff algebra_simps)
  also have "(\<lambda>n::int. (n*(n+1) div 2) + (n*(n-1) div 2)) = (\<lambda>n. n ^ 2)"
    by (auto simp: fun_eq_iff algebra_simps power2_eq_square simp flip: div_add)
  finally show ?thesis
    by (simp add: jacobi_theta_nome_def)
qed

lemma jacobi_theta_nome_same:
  "q \<noteq> 0 \<Longrightarrow> jacobi_theta_nome q q = 2 * jacobi_theta_nome (1 / q^2) (q^4)"
  by (simp add: jacobi_theta_nome_def ramanujan_theta_1_right 
           flip: power_diff power2_eq_square)

lemma jacobi_theta_nome_minus_same: "q \<noteq> 0 \<Longrightarrow> jacobi_theta_nome (-q) q = 0"
  by (simp add: jacobi_theta_nome_def)

lemma jacobi_theta_nome_minus_same': "q \<noteq> 0 \<Longrightarrow> jacobi_theta_nome q (-q) = 0"
  by (simp add: jacobi_theta_nome_def)

lemma jacobi_theta_nome_0_right [simp]: "w \<noteq> 0 \<Longrightarrow> jacobi_theta_nome w 0 = 1"
  by (simp add: jacobi_theta_nome_def)

lemma jacobi_theta_nome_of_real:
  "jacobi_theta_nome (of_real w) (of_real q) = of_real (jacobi_theta_nome w q)"
  by (simp add: jacobi_theta_nome_def flip: ramanujan_theta_of_real)

lemma jacobi_theta_nome_cnj:
  "jacobi_theta_nome (cnj w) (cnj q) = cnj (jacobi_theta_nome w q)"
  by (simp add: jacobi_theta_nome_def flip: ramanujan_theta_cnj)

lemma jacobi_theta_nome_minus_left:
  "jacobi_theta_nome (-w) q = jacobi_theta_nome w (-q)"
  by (simp add: jacobi_theta_nome_def)

lemma jacobi_theta_nome_quasiperiod':
  assumes [simp]: "w \<noteq> 0" "q \<noteq> 0"
  shows   "w * q * jacobi_theta_nome (q\<^sup>2 * w) q = jacobi_theta_nome w q"
proof -
  have "jacobi_theta_nome w q = ramanujan_theta (q * w) (q / w)"
    by (simp add: jacobi_theta_nome_def)
  also have "\<dots> = w * q * ramanujan_theta (q ^ 3 * w) (1 / (q * w))"
    using ramanujan_theta_mult[of "q*w" "q/w"]
    by (simp add: field_simps eval_nat_numeral)
  also have "ramanujan_theta (q ^ 3 * w) (1 / (q * w)) = jacobi_theta_nome (q\<^sup>2 * w) q"
    by (simp add: jacobi_theta_nome_def eval_nat_numeral field_simps)
  finally show ?thesis ..
qed

lemma jacobi_theta_nome_ii_left: "jacobi_theta_nome \<i> q = jacobi_theta_nome (-1) (q^4)"
proof (cases "norm q < 1")
  case q: True
  define S where "S = jacobi_theta_nome \<i> q"
  have sum1: "((\<lambda>n. \<i> powi n * q powi n\<^sup>2) has_sum S) UNIV"
    unfolding S_def by (rule has_sum_jacobi_theta_nome) (use q in auto)
  also have "?this \<longleftrightarrow> ((\<lambda>n. \<i> powi (-n) * q powi (-n)\<^sup>2) has_sum S) UNIV"
    by (rule has_sum_reindex_bij_witness[of _ uminus uminus]) auto
  finally have sum2: "((\<lambda>n. (-\<i>) powi n * q powi n\<^sup>2) has_sum S) UNIV" 
    by (simp add: power_int_minus flip: power_int_inverse)
  have "((\<lambda>n. (\<i> powi n + (-\<i>) powi n) * q powi n\<^sup>2) has_sum (S + S)) UNIV" 
    unfolding ring_distribs by (intro has_sum_add sum1 sum2)
  also have "?this \<longleftrightarrow> ((\<lambda>n. 2 * \<i> powi n * q powi n\<^sup>2) has_sum (S + S)) {n. even n}"
    by (intro has_sum_cong_neutral) auto
  also have "\<dots> \<longleftrightarrow> ((\<lambda>n. 2 * (\<i> powi (2*n) * q powi (2*n)\<^sup>2)) has_sum (S + S)) UNIV"
    by (intro has_sum_reindex_bij_witness[of _ "\<lambda>n. 2*n" "\<lambda>n. n div 2"]) auto
  finally have sum3: "((\<lambda>n. 2 * (\<i> powi (2*n) * (q^4) powi n ^ 2)) has_sum (2 * S)) UNIV"
    by (simp flip: mult_2[of S] power_int_mult add: power_int_mult)
  have "((\<lambda>n. \<i> powi (2*n) * (q^4) powi n ^ 2) has_sum S) UNIV"
    using has_sum_cmult_right[OF sum3, of "1/2"] by simp
  also have "(\<lambda>n. \<i> powi (2*n)) = (\<lambda>n. (-1) powi n)"
    by (simp add: power_int_mult)
  finally have "((\<lambda>n. (-1) powi n * (q^4) powi n\<^sup>2) has_sum S) UNIV" .
  moreover have "((\<lambda>n. (-1) powi n * (q^4) powi n\<^sup>2) has_sum jacobi_theta_nome (-1) (q^4)) UNIV"
    by (rule has_sum_jacobi_theta_nome) (use q in \<open>auto simp: norm_power power_less_one_iff\<close>)
  ultimately show ?thesis
    using has_sum_unique unfolding S_def by blast
qed (auto simp: norm_power power_less_one_iff)

lemma jacobi_theta_nome_quasiperiod:
  assumes [simp]: "w \<noteq> 0" "q \<noteq> 0"
  shows   "jacobi_theta_nome (q\<^sup>2 * w) q = jacobi_theta_nome w q / (w * q)"
  using jacobi_theta_nome_quasiperiod'[of w q] by (simp add: field_simps)

lemma jacobi_theta_nome_holomorphic [holomorphic_intros]:
  assumes "f holomorphic_on A" "g holomorphic_on A"
  assumes "\<And>z. z \<in> A \<Longrightarrow> norm (f z) \<noteq> 0" "\<And>z. z \<in> A \<Longrightarrow> norm (g z) < 1" "open A"
  shows   "(\<lambda>z. jacobi_theta_nome (f z) (g z)) holomorphic_on A"
proof -
  have "(\<lambda>z. ramanujan_theta (g z * f z) (g z / f z)) holomorphic_on A"
    by (intro holomorphic_intros) 
       (use assms in \<open>auto simp: norm_power power_less_one_iff simp flip: power2_eq_square\<close>)
  also have "?this \<longleftrightarrow> ?thesis"
    by (intro holomorphic_cong) (use assms(3,4) in \<open>auto simp: jacobi_theta_nome_def\<close>)
  finally show ?thesis .
qed

lemma jacobi_theta_nome_analytic [analytic_intros]:
  assumes "f analytic_on A" "g analytic_on A"
  assumes "\<And>z. z \<in> A \<Longrightarrow> f z \<noteq> 0" "\<And>z. z \<in> A \<Longrightarrow> norm (g z) < 1"
  shows   "(\<lambda>z. jacobi_theta_nome (f z) (g z)) analytic_on A"
proof -
  from assms(1) obtain B1 where B1: "open B1" "A \<subseteq> B1" "f holomorphic_on B1"
    using analytic_on_holomorphic by metis
  from assms(2) obtain B2 where B2: "open B2" "A \<subseteq> B2" "g holomorphic_on B2"
    using analytic_on_holomorphic by metis
  note [holomorphic_intros] = holomorphic_on_subset[OF B1(3)] holomorphic_on_subset[OF B2(3)]

  define B3 where "B3 = B1 \<inter> B2 \<inter> (\<lambda>z. (f z, g z)) -` ((-{0}) \<times> ball 0 1)"
  have "open B3" using B1 B2 unfolding B3_def
    by (intro continuous_open_preimage holomorphic_on_imp_continuous_on
              holomorphic_intros continuous_intros open_halfspace_Im_gt) (auto intro!: open_Times)
  hence B3: "open B3" "B3 \<subseteq> B1" "B3 \<subseteq> B2" "\<And>z. z \<in> B3 \<Longrightarrow> f z \<noteq> 0 \<and> g z \<in> ball 0 1"
    unfolding B3_def by auto

  have "(\<lambda>z. jacobi_theta_nome (f z) (g z)) holomorphic_on B3"
    using B3 by (auto intro!: holomorphic_intros)
  moreover have "A \<subseteq> B3"
    using assms(3,4) B1 B2 by (auto simp: B3_def)
  ultimately show ?thesis
    using \<open>open B3\<close> analytic_on_holomorphic by metis
qed

lemma tendsto_jacobi_theta_nome [tendsto_intros]:
  fixes f g :: "'a \<Rightarrow> 'b :: {real_normed_field, banach, heine_borel}"
  assumes "(f \<longlongrightarrow> w) F" "(g \<longlongrightarrow> q) F" "w \<noteq> 0" "norm q < 1"
  shows   "((\<lambda>z. jacobi_theta_nome (f z) (g z)) \<longlongrightarrow> jacobi_theta_nome w q) F"
proof -
  have "((\<lambda>z. jacobi_theta_nome (f z) (g z)) \<longlongrightarrow> ramanujan_theta (q * w) (q / w)) F"
  proof (rule Lim_transform_eventually)
    show "((\<lambda>z. ramanujan_theta (g z * f z) (g z / f z)) \<longlongrightarrow>
            ramanujan_theta (q * w) (q / w)) F"
      by (intro tendsto_intros assms)
         (use assms(3,4) in \<open>simp_all flip: power2_eq_square add: norm_power power_less_one_iff\<close>)
  next
    have "eventually (\<lambda>x. f x \<in> -{0}) F"
      by (rule topological_tendstoD[OF assms(1)]) (use assms(3) in auto)
    thus "eventually (\<lambda>z. ramanujan_theta (g z * f z) (g z / f z) = jacobi_theta_nome (f z) (g z)) F"
      by eventually_elim (simp add: jacobi_theta_nome_def)
  qed
  thus ?thesis
    using assms(3) by (simp add: jacobi_theta_nome_def)
qed

lemma continuous_on_jacobi_theta_nome [continuous_intros]:
  fixes f g :: "'a :: topological_space \<Rightarrow> 'b :: {real_normed_field, banach, heine_borel}"
  assumes "continuous_on A f" "continuous_on A g"
  assumes "\<And>z. z \<in> A \<Longrightarrow> f z \<noteq> 0" "\<And>z. z \<in> A \<Longrightarrow> norm (g z) < 1"
  shows   "continuous_on A (\<lambda>z. jacobi_theta_nome (f z) (g z))"
proof -
  have *: "continuous_on {z. fst z \<noteq> 0 \<and> norm (snd z) < 1} (\<lambda>(a,b). jacobi_theta_nome a b :: 'b)"
    unfolding continuous_on by (auto intro!: tendsto_eq_intros simp: case_prod_unfold)
  have "continuous_on A ((\<lambda>(x,y). jacobi_theta_nome x y) \<circ> (\<lambda>x. (f x, g x)))"
    by (intro continuous_on_compose continuous_on_subset[OF *] continuous_intros)
       (use assms in auto)
  thus ?thesis
    by (simp add: o_def)
qed

lemma continuous_jacobi_theta_nome [continuous_intros]:
  fixes f g :: "'a :: t2_space \<Rightarrow> 'b :: {real_normed_field, banach, heine_borel}"
  assumes "continuous F f" "continuous F g" "f (netlimit F) \<noteq> 0" "norm (g (netlimit F)) < 1"
  shows   "continuous F (\<lambda>z. jacobi_theta_nome (f z) (g z))"
  unfolding continuous_def
  using assms by (auto intro!: tendsto_eq_intros simp: continuous_def)


subsection \<open>The Jacobi theta function in the upper half of the complex plane\<close>

text \<open>
  We now define the more usual version of the Jacobi \<open>\<theta>\<close> function, which takes two complex
  parameters $z$ and $t$ where $z$ is arbitrary and $t$ must lie in the upper half of the
  complex plane.
\<close>
definition jacobi_theta_00 :: "complex \<Rightarrow> complex \<Rightarrow> complex" where
  "jacobi_theta_00 z t = jacobi_theta_nome (to_nome z ^ 2) (to_nome t)"

lemma jacobi_theta_00_outside: "Im t \<le> 0 \<Longrightarrow> jacobi_theta_00 z t = 0"
  by (simp add: jacobi_theta_00_def mult_le_0_iff to_nome_def)

lemma has_sum_jacobi_theta_00:
  assumes "Im t > 0"
  shows   "((\<lambda>n. to_nome (of_int n ^ 2 * t + 2 * of_int n * z)) has_sum jacobi_theta_00 z t) UNIV"
  using has_sum_jacobi_theta_nome[of "exp (\<i> * of_real pi * t)" "exp (2 * \<i> * of_real pi * z)"] assms
  by (simp add: jacobi_theta_00_def algebra_simps exp_add exp_power_int to_nome_def
           flip: exp_of_nat_mult)

lemma sums_jacobi_theta_00:
  assumes "Im t > 0"
  shows   "((\<lambda>n. if n = 0 then 1 else 2 * to_nome t ^ n\<^sup>2 * 
             cos (2 * of_nat n * of_real pi * z)) sums jacobi_theta_00 z t)"
proof -
  define f where "f = (\<lambda>n::int. to_nome (of_int n ^ 2 * t + 2 * of_int n * z))"
  define S1 where "S1 = (\<Sum>\<^sub>\<infinity>n\<in>{1..}. f n)"
  define S2 where "S2 = (\<Sum>\<^sub>\<infinity>n\<in>{..-1}. f n)"

  have sum: "(f has_sum jacobi_theta_00 z t) UNIV"
    unfolding f_def by (rule has_sum_jacobi_theta_00) fact
  have [simp]: "f summable_on A" for A
    by (rule summable_on_subset_banach, rule has_sum_imp_summable[OF sum]) auto

  have "(f has_sum S1) {1..}" "(f has_sum S2) {..-1}"
    unfolding S1_def S2_def by (rule has_sum_infsum; simp)+
  moreover have "(f has_sum 1) {0}"
    by (rule has_sum_finiteI) (auto simp: f_def)
  ultimately have "(f has_sum (1 + S1 + S2)) ({0} \<union> {1..} \<union> {..-1})"
    by (intro has_sum_Un_disjoint) auto
  also have "{0} \<union> {1..} \<union> {..-1::int} = UNIV"
    by auto
  finally have "(f has_sum 1 + S1 + S2) UNIV" .
  with sum have eq: "jacobi_theta_00 z t = 1 + S1 + S2"
    using has_sum_unique by blast

  note \<open>(f has_sum S2) {..-1}\<close>
  also have "(f has_sum S2) {..-1} \<longleftrightarrow> ((\<lambda>n. f (-n)) has_sum S2) {1..}"
    by (intro has_sum_reindex_bij_witness[of _ uminus uminus]) auto
  finally have "((\<lambda>n. f n + f (-n)) has_sum (S1 + S2)) {1..}"
    using \<open>(f has_sum S1) {1..}\<close> by (intro has_sum_add)
  also have "?this \<longleftrightarrow> ((\<lambda>n. f (int n) + f (-int n)) has_sum (S1 + S2)) {1..}"
    by (rule has_sum_reindex_bij_witness[of _ int nat]) auto
  also have "(\<lambda>n::nat. f (int n) + f (-int n)) =
             (\<lambda>n. 2 * to_nome t ^ (n ^ 2) * cos (2 * of_nat n * of_real pi * z))"
    by (auto simp: f_def exp_add exp_diff ring_distribs to_nome_def mult_ac cos_exp_eq
             simp flip: exp_of_nat_mult)
  also have "(\<dots> has_sum (S1 + S2)) {1..} \<longleftrightarrow> 
             ((\<lambda>n. if n = 0 then 1 else 2 * to_nome t ^ (n ^ 2) *
                     cos (2 * of_nat n * of_real pi * z)) has_sum (S1 + S2)) {1..}"
    by (intro has_sum_cong) auto
  finally have "((\<lambda>n. if n = 0 then 1 else 2 * to_nome t ^ (n ^ 2) * cos (2 * of_nat n * of_real pi * z)) 
                    has_sum (1 + (S1 + S2))) ({0} \<union> {1..})"
    by (intro has_sum_Un_disjoint) (auto intro: has_sum_finiteI)
  also have "1 + (S1 + S2) = jacobi_theta_00 z t"
    using eq by (simp add: add_ac)
  also have "{0} \<union> {1::nat..} = UNIV"
    by auto
  finally show ?thesis
    by (rule has_sum_imp_sums)
qed

lemma jacobi_theta_00_holomorphic [holomorphic_intros]:
  assumes "f holomorphic_on A" "g holomorphic_on A" "\<And>z. z \<in> A \<Longrightarrow> Im (g z) > 0" "open A"
  shows   "(\<lambda>z. jacobi_theta_00 (f z) (g z)) holomorphic_on A"
  unfolding jacobi_theta_00_def using assms(3,4)
  by (auto intro!: holomorphic_intros assms(1,2) simp: to_nome_def)

lemma jacobi_theta_00_analytic [analytic_intros]:
  assumes "f analytic_on A" "g analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> Im (g z) > 0"
  shows   "(\<lambda>z. jacobi_theta_00 (f z) (g z)) analytic_on A"
  unfolding jacobi_theta_00_def using assms(3)
  by (auto intro!: analytic_intros assms(1,2) simp: to_nome_def)

lemma jacobi_theta_00_plus_half_left:
  "jacobi_theta_00 (z + 1 / 2) t = jacobi_theta_00 z (t + 1)"
proof -
  define q where "q = exp (\<i> * of_real pi * t)"
  define w where "w = exp (2 * \<i> * of_real pi * z)"
  have "jacobi_theta_00 (z + 1 / 2) t = jacobi_theta_nome (-w) q"
    by (simp add: jacobi_theta_00_def w_def q_def algebra_simps exp_add to_nome_def flip: exp_of_nat_mult)
  also have "\<dots> = jacobi_theta_nome w (-q)"
    by (simp add: jacobi_theta_nome_minus_left)
  also have "\<dots> = jacobi_theta_00 z (t + 1)"
    by (simp add: jacobi_theta_00_def algebra_simps exp_add q_def w_def to_nome_def flip: exp_of_nat_mult)
  finally show ?thesis .
qed

lemma jacobi_theta_00_plus_2_right: "jacobi_theta_00 z (t + 2) = jacobi_theta_00 z t"
  by (simp add: jacobi_theta_00_def algebra_simps exp_add to_nome_def)

interpretation jacobi_theta_00_left: periodic_fun_simple' "\<lambda>z. jacobi_theta_00 z t"
proof
  fix z :: complex
  have "jacobi_theta_00 (z + 1) t = jacobi_theta_00 (z + 1/2 + 1/2) t"
    by (simp add: add.commute)
  also have "\<dots> = jacobi_theta_00 z (t + 2)"
    unfolding jacobi_theta_00_plus_half_left by (simp add: add.commute)
  also have "jacobi_theta_00 z (t + 2) = jacobi_theta_00 z t"
    by (rule jacobi_theta_00_plus_2_right)
  finally show "jacobi_theta_00 (z + 1) t = jacobi_theta_00 z t" .
qed

interpretation jacobi_theta_00_right: periodic_fun_simple "\<lambda>t. jacobi_theta_00 z t" 2
proof
  fix t :: complex
  show "jacobi_theta_00 z (t + 2) = jacobi_theta_00 z t"
    by (rule jacobi_theta_00_plus_2_right)
qed

lemma jacobi_theta_00_plus_quasiperiod:
  "jacobi_theta_00 (z + t) t = jacobi_theta_00 z t / to_nome (t + 2 * z)"
proof -
  define q where "q = exp (\<i> * of_real pi * t)"
  define w where "w = exp (2 * \<i> * of_real pi * z)"
  have "jacobi_theta_00 (z + t) t = jacobi_theta_nome (q\<^sup>2 * w) q"
    by (simp add: w_def q_def jacobi_theta_00_def algebra_simps exp_add to_nome_def
             flip: exp_of_nat_mult)
  also have "\<dots> = jacobi_theta_nome w q / (w * q)"
    by (subst jacobi_theta_nome_quasiperiod) (auto simp: w_def q_def)
  also have "\<dots> = exp (-pi * \<i> * (t + 2 * z)) * jacobi_theta_00 z t"
    by (simp add: w_def q_def jacobi_theta_00_def field_simps exp_add exp_minus exp_diff to_nome_def
             flip: exp_of_nat_mult)
  finally show ?thesis
    by (simp add: exp_minus exp_diff exp_add to_nome_def field_simps)
qed

lemma jacobi_theta_00_quasiperiodic:
  "jacobi_theta_00 (z + of_int m + of_int n * t) t =
     jacobi_theta_00 z t / to_nome (of_int (n^2) * t + 2 * of_int n * z)"
proof -
  write jacobi_theta_00 ("\<theta>")
  have "\<theta> (z + of_int m + of_int n * t) t =
        \<theta> (z  + of_int n * t + of_int m) t"
    by (simp add: add_ac)
  also have "\<dots> = \<theta> (z + of_int n * t) t"
    by (rule jacobi_theta_00_left.plus_of_int)
  also have "\<dots> = \<theta> z t / to_nome (of_int (n^2) * t + 2 * of_int n * z)"
  proof -
    have *: "\<theta> (z + of_nat n * t) t = \<theta> z t / to_nome (of_nat (n^2) * t + 2 * of_nat n * z)" 
      for z :: complex and n :: nat
    proof (induction n)
      case (Suc n)
      have "\<theta> (z + of_nat (Suc n) * t) t = \<theta> (z + of_nat n * t + t) t"
        by (simp add: algebra_simps)
      also have "\<dots> = \<theta> z t / (to_nome (of_nat (n\<^sup>2) * t + 2 * of_nat n * z) * 
                               to_nome (t + 2 * (z + of_nat n * t)))"
        by (subst jacobi_theta_00_plus_quasiperiod, subst Suc.IH) auto
      also have "to_nome (of_nat (n\<^sup>2) * t + 2 * of_nat n * z) * to_nome (t + 2 * (z + of_nat n * t)) =
                 to_nome ((of_nat (n\<^sup>2) * t + 2 * of_nat n * z) + (t + 2 * (z + of_nat n * t)))"
        by (rule to_nome_add [symmetric])
      also have "(of_nat (n\<^sup>2) * t + 2 * of_nat n * z) + (t + 2 * (z + of_nat n * t)) =
                 of_nat ((Suc n)\<^sup>2) * t + 2 * of_nat (Suc n) * z"
        by (simp add: algebra_simps power2_eq_square)
      finally show ?case .
    qed auto
    show ?thesis
    proof (cases "n \<ge> 0")
      case True
      thus ?thesis
        using *[of z "nat n"] by simp
    next
      case False
      thus ?thesis
        using *[of "z + of_int n * t" "nat (-n)"] False
        by (simp add: field_simps power2_eq_square to_nome_add to_nome_diff to_nome_minus)
    qed
  qed
  finally show ?thesis .
qed

lemma jacobi_theta_00_onequarter_left:
  "jacobi_theta_00 (1/4) t = jacobi_theta_00 (1/2) (4 * t)"
  by (simp add: jacobi_theta_00_def to_nome_power jacobi_theta_nome_ii_left)

lemma jacobi_theta_00_eq_0: "jacobi_theta_00 ((t + 1) / 2) t = 0"
proof -
  have "jacobi_theta_00 ((t + 1) / 2) t = jacobi_theta_nome (to_nome (t + 1)) (to_nome t)"
    by (simp add: jacobi_theta_00_def to_nome_power add_divide_distrib)
  also have "\<dots> = 0"
    by (simp add: to_nome_add jacobi_theta_nome_minus_same)
  finally show ?thesis .
qed

lemma jacobi_theta_00_eq_0': "jacobi_theta_00 ((of_int m + 1/2) + (of_int n + 1/2) * t) t = 0"
proof -
  have "jacobi_theta_00 ((of_int m + 1/2) + (of_int n + 1/2) * t) t =
        jacobi_theta_00 ((t + 1) / 2 + of_int m + of_int n * t) t"
    by (simp add: algebra_simps add_divide_distrib)
  also have "\<dots> = 0"
    by (simp only: jacobi_theta_00_quasiperiodic jacobi_theta_00_eq_0) auto
  finally show ?thesis .
qed

lemma tendsto_jacobi_theta_00 [tendsto_intros]:
  assumes "(f \<longlongrightarrow> w) F" "(g \<longlongrightarrow> q) F" "Im q > 0"
  shows   "((\<lambda>z. jacobi_theta_00 (f z) (g z)) \<longlongrightarrow> jacobi_theta_00 w q) F"
  unfolding jacobi_theta_00_def
  by (intro tendsto_intros assms(1,2)) (use assms(3) in \<open>auto simp: norm_to_nome\<close>)

lemma continuous_on_jacobi_theta_00 [continuous_intros]:
  assumes "continuous_on A f" "continuous_on A g"
  assumes "\<And>z. z \<in> A \<Longrightarrow> Im (g z) > 0"
  shows   "continuous_on A (\<lambda>z. jacobi_theta_00 (f z) (g z))"
  unfolding jacobi_theta_00_def
  by (intro continuous_intros assms(1,2)) (use assms(3) in \<open>auto simp: norm_to_nome\<close>)

lemma continuous_jacobi_theta_00 [continuous_intros]:
  assumes "continuous F f" "continuous F g" "Im (g (netlimit F)) > 0"
  shows   "continuous F (\<lambda>z. jacobi_theta_00 (f z) (g z))"
  unfolding jacobi_theta_00_def
  by (intro continuous_intros assms(1,2)) (use assms(3) in \<open>auto simp: norm_to_nome\<close>)



subsection \<open>The auxiliary theta functions in terms of the nome\<close>

definition jacobi_theta_nome_00 :: "'a :: {real_normed_field, banach} \<Rightarrow> 'a \<Rightarrow> 'a" where
  "jacobi_theta_nome_00 w q = jacobi_theta_nome (w^2) q"

definition jacobi_theta_nome_01 :: "'a :: {real_normed_field, banach} \<Rightarrow> 'a \<Rightarrow> 'a" where
  "jacobi_theta_nome_01 w q = jacobi_theta_nome (-(w^2)) q"

definition jacobi_theta_nome_10 :: "'a :: {real_normed_field, banach, ln} \<Rightarrow> 'a \<Rightarrow> 'a" where
  "jacobi_theta_nome_10 w q = w * q powr (1/4) * jacobi_theta_nome (w ^ 2 * q) q"

definition jacobi_theta_nome_11 :: "complex \<Rightarrow> complex \<Rightarrow> complex" where
  "jacobi_theta_nome_11 w q = \<i> * w * q powr (1/4) * jacobi_theta_nome (-(w ^ 2) * q) q"

lemmas jacobi_theta_nome_xx_defs = 
  jacobi_theta_nome_00_def jacobi_theta_nome_01_def
   jacobi_theta_nome_10_def jacobi_theta_nome_11_def

lemma jacobi_theta_nome_00_outside [simp]: "norm q \<ge> 1 \<Longrightarrow> jacobi_theta_nome_00 w q = 0"
  and jacobi_theta_nome_01_outside [simp]: "norm q \<ge> 1 \<Longrightarrow> jacobi_theta_nome_01 w q = 0"
  and jacobi_theta_nome_10_outside [simp]: "norm q' \<ge> 1 \<Longrightarrow> jacobi_theta_nome_10 w' q' = 0"
  and jacobi_theta_nome_11_outside [simp]: "norm q'' \<ge> 1 \<Longrightarrow> jacobi_theta_nome_11 w'' q'' = 0"
  by (simp_all add: jacobi_theta_nome_xx_defs)

lemma jacobi_theta_nome_01_conv_00: "jacobi_theta_nome_01 w' q' = jacobi_theta_nome_00 w' (-q')"
  and jacobi_theta_nome_11_conv_10: "jacobi_theta_nome_11 w q = jacobi_theta_nome_10 (\<i> * w) q"
  by (simp_all add: jacobi_theta_nome_xx_defs power_mult_distrib jacobi_theta_nome_minus_left)

lemma jacobi_theta_nome_00_0_right [simp]: "w \<noteq> 0 \<Longrightarrow> jacobi_theta_nome_00 w 0 = 1"
  and jacobi_theta_nome_01_0_right [simp]: "w \<noteq> 0 \<Longrightarrow> jacobi_theta_nome_01 w 0 = 1"
  and jacobi_theta_nome_10_0_right [simp]: "jacobi_theta_nome_10 w' 0 = 0"
  and jacobi_theta_nome_11_0_right [simp]: "jacobi_theta_nome_11 w'' 0 = 0"
  by (simp_all add: jacobi_theta_nome_xx_defs)

lemma jacobi_theta_nome_00_of_real:
        "jacobi_theta_nome_00 (of_real w :: 'a :: {banach, real_normed_field}) (of_real q) = 
         of_real (jacobi_theta_nome_00 w q)"
  and jacobi_theta_nome_01_of_real:
        "jacobi_theta_nome_01 (of_real w :: 'a) (of_real q) = of_real (jacobi_theta_nome_01 w q)"
  and jacobi_theta_nome_10_complex_of_real:
        "q \<ge> 0 \<Longrightarrow> jacobi_theta_nome_10 (complex_of_real w) (of_real q) =
                     of_real (jacobi_theta_nome_10 w q)"
  by (simp_all add: jacobi_theta_nome_xx_defs flip: jacobi_theta_nome_of_real powr_of_real)

lemma jacobi_theta_nome_00_cnj:
        "jacobi_theta_nome_00 (cnj w) (cnj q) = cnj (jacobi_theta_nome_00 w q)"
  and jacobi_theta_nome_01_cnj:
        "jacobi_theta_nome_01 (cnj w) (cnj q) = cnj (jacobi_theta_nome_01 w q)"
  and jacobi_theta_nome_10_cnj:
        "(Im q = 0 \<Longrightarrow> Re q \<ge> 0) \<Longrightarrow>
           jacobi_theta_nome_10 (cnj w) (cnj q) = cnj (jacobi_theta_nome_10 w q)"
  and jacobi_theta_nome_11_cnj:
        "(Im q = 0 \<Longrightarrow> Re q \<ge> 0) \<Longrightarrow>
           jacobi_theta_nome_11 (cnj w) (cnj q) = -cnj (jacobi_theta_nome_11 w q)"
  by (simp_all add: jacobi_theta_nome_xx_defs cnj_powr flip: jacobi_theta_nome_cnj)


lemma has_sum_jacobi_theta_nome_00:
  assumes "norm q < 1" "w \<noteq> 0"
  shows   "((\<lambda>n. w powi (2*n) * q powi n\<^sup>2) has_sum jacobi_theta_nome_00 w q) UNIV"
  using has_sum_jacobi_theta_nome[of q "w^2"] assms
  by (simp add: jacobi_theta_nome_00_def power_int_mult_distrib power_int_mult power_mult_distrib)

lemma has_sum_jacobi_theta_nome_01:
  assumes "norm q < 1" "w \<noteq> 0"
  shows   "((\<lambda>n. (-1) powi n * w powi (2*n) * q powi n\<^sup>2) has_sum jacobi_theta_nome_01 w q) UNIV"
  using has_sum_jacobi_theta_nome[of q "-(w^2)"] assms
  by (simp add: jacobi_theta_nome_01_def power_int_mult power_mult_distrib 
           flip: power_int_mult_distrib)

lemma has_sum_jacobi_theta_nome_10':
  assumes q: "norm q < 1" and [simp]: "w \<noteq> 0" "q \<noteq> 0"
  shows   "((\<lambda>n. w powi (2*n+1) * q powi (n*(n+1))) has_sum
             (jacobi_theta_nome_10 w q / q powr (1/4))) UNIV"
proof -
  have "((\<lambda>n. w * ((w\<^sup>2 * q) powi n * q powi (n ^ 2))) has_sum 
          (w * jacobi_theta_nome (w ^ 2 * q) q)) UNIV"
    by (intro has_sum_cmult_right has_sum_jacobi_theta_nome) (use q in auto)
  also have "(\<lambda>n. w * ((w\<^sup>2 * q) powi n * q powi (n ^ 2))) = (\<lambda>n. w powi (2*n+1) * q powi (n*(n+1)))"
    by (simp add: power_int_mult_distrib power_int_power power_int_add ring_distribs)
       (simp_all add: algebra_simps power2_eq_square)?
  finally show ?thesis
    by (simp add: jacobi_theta_nome_10_def)
qed

lemma has_sum_jacobi_theta_nome_10:
  fixes q :: "'a :: {real_normed_field, banach, ln}"
  assumes q: "norm q < 1" and [simp]: "w \<noteq> 0" "exp (ln q) = q"
  shows   "((\<lambda>n. w powi (2*n+1) * q powr (of_int n + 1 / 2) ^ 2) has_sum
             (jacobi_theta_nome_10 w q)) UNIV"
proof -
  have "exp (ln q) \<noteq> 0"
    by (rule exp_not_eq_zero)
  hence [simp]: "q \<noteq> 0"
    by auto
  have "((\<lambda>n. q powr (1/4) * (w powi (2*n+1) * q powi (n*(n+1)))) has_sum
             (q powr (1/4) * (jacobi_theta_nome_10 w q / q powr (1/4)))) UNIV"
    by (intro has_sum_cmult_right has_sum_jacobi_theta_nome_10') fact+
  also have "(q powr (1/4) * (jacobi_theta_nome_10 w q / q powr (1/4))) = jacobi_theta_nome_10 w q"
    by simp
  also have "(\<lambda>n::int. q powr (1/4) * (w powi (2*n+1) * q powi (n*(n+1)))) =
             (\<lambda>n::int. w powi (2*n+1) * q powr ((of_int n + 1/2) ^ 2))"
  proof
    fix n :: int
    have "q powr (1/4) * (w powi (2*n+1) * q powi (n*(n+1))) =
          w powi (2*n+1) * (q powr (1/4) * q powi (n*(n+1)))"
      by (simp add: mult_ac)
    also have "\<dots> = w powi (2*n+1) * (q powr (1/4) * q powr (of_int (n*(n+1))))"
    proof -
      have "q powr (of_int (n*(n+1))) = exp (of_int (n*(n+1)) * ln q)"
        by (simp add: powr_def)
      also have "\<dots> = q powi (n * (n + 1))"
        by (subst exp_power_int [symmetric]) auto
      finally show ?thesis
        by simp
    qed
    also have "q powr (1/4) * q powr of_int (n*(n+1)) = 
               q powr (1/4 + of_int (n*(n+1)))"
      by (simp add: powr_def field_simps flip: exp_add)
    also have "1/4 + of_int (n*(n+1)) = (of_int n + 1/2 :: 'a) ^ 2"
      by (simp add: field_simps power2_eq_square)
    finally show "q powr (1/4) * (w powi (2*n+1) * q powi (n*(n+1))) =
                  w powi (2*n+1) * q powr ((of_int n + 1/2) ^ 2)" .
  qed
  finally show ?thesis .
qed
    
lemma has_sum_jacobi_theta_nome_11':
  assumes q: "norm q < 1" and [simp]: "w \<noteq> 0" "q \<noteq> 0"
  shows   "((\<lambda>n. (-1) powi n * w powi (2*n+1) * q powi (n*(n+1))) has_sum
             (jacobi_theta_nome_11 w q / (\<i> * q powr (1/4)))) UNIV"
proof -
  have "((\<lambda>n. w * ((-(w\<^sup>2) * q) powi n * q powi (n ^ 2))) has_sum 
          (w * jacobi_theta_nome (-(w ^ 2) * q) q)) UNIV"
    by (intro has_sum_cmult_right has_sum_jacobi_theta_nome) (use q in auto)
  also have "(\<lambda>n. (-(w\<^sup>2) * q) powi n) = (\<lambda>n. (-1) powi n * (w ^ 2 * q) powi n)"
    by (subst power_int_mult_distrib [symmetric]) auto
  also have "(\<lambda>n. w * ((-1) powi n * (w\<^sup>2 * q) powi n * q powi (n ^ 2))) = 
             (\<lambda>n. (-1) powi n * w powi (2*n+1) * q powi (n*(n+1)))"
    by (simp add: power_int_mult_distrib power_int_power power_int_add ring_distribs)
       (simp_all add: algebra_simps power2_eq_square)?
  finally show ?thesis
    by (simp add: jacobi_theta_nome_11_def mult_ac)
qed

lemma has_sum_jacobi_theta_nome_11:
  assumes q: "norm q < 1" and [simp]: "w \<noteq> 0" "q \<noteq> 0"
  shows   "((\<lambda>n. \<i> * (-1) powi n * w powi (2*n+1) * q powr (of_int n + 1/2) ^ 2) has_sum
             (jacobi_theta_nome_11 w q)) UNIV"
proof -
  have "((\<lambda>n. (\<i>*w) powi (2*n+1) * q powr (of_int n + 1 / 2) ^ 2) has_sum
             (jacobi_theta_nome_10 (\<i>*w) q)) UNIV"
    by (intro has_sum_jacobi_theta_nome_10) (use q in auto)
  also have "(\<lambda>n. (\<i>*w) powi (2*n+1)) = (\<lambda>n. \<i> * \<i> powi (2*n) * w powi (2*n+1))"
    by (simp add: power_int_mult_distrib power_int_add mult_ac)
  also have "(\<lambda>n. \<i> powi (2*n)) = (\<lambda>n. (-1) powi n)"
    by (subst power_int_mult) auto
  finally show ?thesis
    by (simp add: jacobi_theta_nome_11_conv_10)
qed


lemma jacobi_theta_nome_00_holomorphic [holomorphic_intros]:
  assumes "f holomorphic_on A" "g holomorphic_on A"
  assumes "\<And>z. z \<in> A \<Longrightarrow> norm (f z) \<noteq> 0" "\<And>z. z \<in> A \<Longrightarrow> norm (g z) < 1" "open A"
  shows   "(\<lambda>z. jacobi_theta_nome_00 (f z) (g z)) holomorphic_on A"
  unfolding jacobi_theta_nome_00_def
  by (intro holomorphic_intros assms(1,2)) (use assms(3-) in auto)

lemma jacobi_theta_nome_01_holomorphic [holomorphic_intros]:
  assumes "f holomorphic_on A" "g holomorphic_on A"
  assumes "\<And>z. z \<in> A \<Longrightarrow> norm (f z) \<noteq> 0" "\<And>z. z \<in> A \<Longrightarrow> norm (g z) < 1" "open A"
  shows   "(\<lambda>z. jacobi_theta_nome_01 (f z) (g z)) holomorphic_on A"
  unfolding jacobi_theta_nome_01_def
  by (intro holomorphic_intros assms(1,2)) (use assms(3-) in auto)

lemma jacobi_theta_nome_10_holomorphic [holomorphic_intros]:
  assumes "f holomorphic_on A" "g holomorphic_on A"
  assumes "\<And>z. z \<in> A \<Longrightarrow> norm (f z) \<noteq> 0" 
  assumes "\<And>z. z \<in> A \<Longrightarrow> norm (g z) < 1 \<and> g z \<notin> \<real>\<^sub>\<le>\<^sub>0" "open A"
  shows   "(\<lambda>z. jacobi_theta_nome_10 (f z) (g z)) holomorphic_on A"
  unfolding jacobi_theta_nome_10_def
  by (intro holomorphic_intros assms(1,2)) (use assms(3-) in force)+

lemma jacobi_theta_nome_11_holomorphic [holomorphic_intros]:
  assumes "f holomorphic_on A" "g holomorphic_on A"
  assumes "\<And>z. z \<in> A \<Longrightarrow> norm (f z) \<noteq> 0" 
  assumes "\<And>z. z \<in> A \<Longrightarrow> norm (g z) < 1 \<and> g z \<notin> \<real>\<^sub>\<le>\<^sub>0" "open A"
  shows   "(\<lambda>z. jacobi_theta_nome_11 (f z) (g z)) holomorphic_on A"
  unfolding jacobi_theta_nome_11_def
  by (intro holomorphic_intros assms(1,2)) (use assms(3-) in force)+


lemma jacobi_theta_nome_00_analytic [analytic_intros]:
  assumes "f analytic_on A" "g analytic_on A"
  assumes "\<And>z. z \<in> A \<Longrightarrow> norm (f z) \<noteq> 0" "\<And>z. z \<in> A \<Longrightarrow> norm (g z) < 1"
  shows   "(\<lambda>z. jacobi_theta_nome_00 (f z) (g z)) analytic_on A"
  unfolding jacobi_theta_nome_00_def
  by (intro analytic_intros assms(1,2)) (use assms(3-) in auto)

lemma jacobi_theta_nome_01_analytic [analytic_intros]:
  assumes "f analytic_on A" "g analytic_on A"
  assumes "\<And>z. z \<in> A \<Longrightarrow> norm (f z) \<noteq> 0" "\<And>z. z \<in> A \<Longrightarrow> norm (g z) < 1"
  shows   "(\<lambda>z. jacobi_theta_nome_01 (f z) (g z)) analytic_on A"
  unfolding jacobi_theta_nome_01_def
  by (intro analytic_intros assms(1,2)) (use assms(3-) in auto)

lemma jacobi_theta_nome_10_analytic [analytic_intros]:
  assumes "f analytic_on A" "g analytic_on A"
  assumes "\<And>z. z \<in> A \<Longrightarrow> norm (f z) \<noteq> 0" 
  assumes "\<And>z. z \<in> A \<Longrightarrow> norm (g z) < 1 \<and> g z \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "(\<lambda>z. jacobi_theta_nome_10 (f z) (g z)) analytic_on A"
  unfolding jacobi_theta_nome_10_def
  by (intro analytic_intros assms(1,2)) (use assms(3-) in force)+

lemma jacobi_theta_nome_11_analytic [analytic_intros]:
  assumes "f analytic_on A" "g analytic_on A"
  assumes "\<And>z. z \<in> A \<Longrightarrow> norm (f z) \<noteq> 0" 
  assumes "\<And>z. z \<in> A \<Longrightarrow> norm (g z) < 1 \<and> g z \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "(\<lambda>z. jacobi_theta_nome_11 (f z) (g z)) analytic_on A"
  unfolding jacobi_theta_nome_11_def
  by (intro analytic_intros assms(1,2)) (use assms(3-) in force)+


lemma tendsto_jacobi_theta_nome_00 [tendsto_intros]:
  fixes f g :: "'a \<Rightarrow> 'b :: {real_normed_field, banach, heine_borel}"
  assumes "(f \<longlongrightarrow> w) F" "(g \<longlongrightarrow> q) F" "w \<noteq> 0" "norm q < 1"
  shows   "((\<lambda>z. jacobi_theta_nome_00 (f z) (g z)) \<longlongrightarrow> jacobi_theta_nome_00 w q) F"
  unfolding jacobi_theta_nome_00_def
  by (intro tendsto_intros assms(1,2)) (use assms(3,4) in auto)

lemma continuous_on_jacobi_theta_nome_00 [continuous_intros]:
  fixes f g :: "'a :: topological_space \<Rightarrow> 'b :: {real_normed_field, banach, heine_borel}"
  assumes "continuous_on A f" "continuous_on A g"
  assumes "\<And>z. z \<in> A \<Longrightarrow> f z \<noteq> 0" "\<And>z. z \<in> A \<Longrightarrow> norm (g z) < 1"
  shows   "continuous_on A (\<lambda>z. jacobi_theta_nome_00 (f z) (g z))"
  unfolding jacobi_theta_nome_00_def
  by (intro continuous_intros assms(1,2)) (use assms(3,4) in auto)

lemma continuous_jacobi_theta_nome_00 [continuous_intros]:
  fixes f g :: "'a :: t2_space \<Rightarrow> 'b :: {real_normed_field, banach, heine_borel}"
  assumes "continuous F f" "continuous F g" "f (netlimit F) \<noteq> 0" "norm (g (netlimit F)) < 1"
  shows   "continuous F (\<lambda>z. jacobi_theta_nome_00 (f z) (g z))"
  unfolding jacobi_theta_nome_00_def
  by (intro continuous_intros assms(1,2)) (use assms(3,4) in auto)


lemma tendsto_jacobi_theta_nome_01 [tendsto_intros]:
  fixes f g :: "'a \<Rightarrow> 'b :: {real_normed_field, banach, heine_borel}"
  assumes "(f \<longlongrightarrow> w) F" "(g \<longlongrightarrow> q) F" "w \<noteq> 0" "norm q < 1"
  shows   "((\<lambda>z. jacobi_theta_nome_01 (f z) (g z)) \<longlongrightarrow> jacobi_theta_nome_01 w q) F"
  unfolding jacobi_theta_nome_01_def
  by (intro tendsto_intros assms(1,2)) (use assms(3,4) in auto)

lemma continuous_on_jacobi_theta_nome_01 [continuous_intros]:
  fixes f g :: "'a :: topological_space \<Rightarrow> 'b :: {real_normed_field, banach, heine_borel}"
  assumes "continuous_on A f" "continuous_on A g"
  assumes "\<And>z. z \<in> A \<Longrightarrow> f z \<noteq> 0" "\<And>z. z \<in> A \<Longrightarrow> norm (g z) < 1"
  shows   "continuous_on A (\<lambda>z. jacobi_theta_nome_01 (f z) (g z))"
  unfolding jacobi_theta_nome_01_def
  by (intro continuous_intros assms(1,2)) (use assms(3,4) in auto)

lemma continuous_jacobi_theta_nome_01 [continuous_intros]:
  fixes f g :: "'a :: t2_space \<Rightarrow> 'b :: {real_normed_field, banach, heine_borel}"
  assumes "continuous F f" "continuous F g" "f (netlimit F) \<noteq> 0" "norm (g (netlimit F)) < 1"
  shows   "continuous F (\<lambda>z. jacobi_theta_nome_01 (f z) (g z))"
  unfolding jacobi_theta_nome_01_def
  by (intro continuous_intros assms(1,2)) (use assms(3,4) in auto)


lemma tendsto_jacobi_theta_nome_10_complex [tendsto_intros]:
  fixes f g :: "complex \<Rightarrow> complex"
  assumes "(f \<longlongrightarrow> w) F" "(g \<longlongrightarrow> q) F" "w \<noteq> 0" "norm q < 1" "q \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "((\<lambda>z. jacobi_theta_nome_10 (f z) (g z)) \<longlongrightarrow> jacobi_theta_nome_10 w q) F"
  unfolding jacobi_theta_nome_10_def
  by (intro tendsto_intros assms(1,2)) (use assms(3-5) in auto)

lemma continuous_on_jacobi_theta_nome_10_complex [continuous_intros]:
  fixes f g :: "complex \<Rightarrow> complex"
  assumes "continuous_on A f" "continuous_on A g"
  assumes "\<And>z. z \<in> A \<Longrightarrow> f z \<noteq> 0" "\<And>z. z \<in> A \<Longrightarrow> norm (g z) < 1 \<and> (Re (g z) > 0 \<or> Im (g z) \<noteq> 0)"
  shows   "continuous_on A (\<lambda>z. jacobi_theta_nome_10 (f z) (g z))"
  unfolding jacobi_theta_nome_10_def
  by (intro continuous_intros assms(1,2); use assms(3,4) in force)

lemma continuous_jacobi_theta_nome_10_complex [continuous_intros]:
  assumes "continuous F f" "continuous F g" "f (netlimit F) \<noteq> 0" 
  assumes "norm (g (netlimit F)) < 1" "Re (g (netlimit F)) > 0 \<or> Im (g (netlimit F)) \<noteq> 0"
  shows   "continuous F (\<lambda>z. jacobi_theta_nome_10 (f z) (g z))"
  unfolding jacobi_theta_nome_10_def
  by (intro continuous_intros assms(1,2); use assms(3-) in force)

lemma tendsto_jacobi_theta_nome_10_real [tendsto_intros]:
  fixes f g :: "real \<Rightarrow> real"
  assumes "(f \<longlongrightarrow> w) F" "(g \<longlongrightarrow> q) F" "w \<noteq> 0" "norm q < 1" "q > 0"
  shows   "((\<lambda>z. jacobi_theta_nome_10 (f z) (g z)) \<longlongrightarrow> jacobi_theta_nome_10 w q) F"
  unfolding jacobi_theta_nome_10_def
  by (intro tendsto_intros assms(1,2)) (use assms(3-5) in auto)

lemma continuous_on_jacobi_theta_nome_10_real [continuous_intros]:
  fixes f g :: "real \<Rightarrow> real"
  assumes "continuous_on A f" "continuous_on A g"
  assumes "\<And>z. z \<in> A \<Longrightarrow> f z \<noteq> 0" "\<And>z. z \<in> A \<Longrightarrow> g z \<in> {0<..<1}"
  shows   "continuous_on A (\<lambda>z. jacobi_theta_nome_10 (f z) (g z))"
  unfolding jacobi_theta_nome_10_def
  by (intro continuous_intros assms(1,2); use assms(3,4) in force)

lemma continuous_jacobi_theta_nome_10_real [continuous_intros]:
  fixes f g :: "real \<Rightarrow> real"
  assumes "continuous F f" "continuous F g" "f (netlimit F) \<noteq> 0" "g (netlimit F) \<in> {0<..<1}"
  shows   "continuous F (\<lambda>z. jacobi_theta_nome_10 (f z) (g z))"
  unfolding jacobi_theta_nome_10_def
  by (intro continuous_intros assms(1,2); use assms(3-) in auto)



lemma tendsto_jacobi_theta_nome_11_complex [tendsto_intros]:
  fixes f g :: "complex \<Rightarrow> complex"
  assumes "(f \<longlongrightarrow> w) F" "(g \<longlongrightarrow> q) F" "w \<noteq> 0" "norm q < 1" "q \<notin> \<real>\<^sub>\<le>\<^sub>0"
  shows   "((\<lambda>z. jacobi_theta_nome_11 (f z) (g z)) \<longlongrightarrow> jacobi_theta_nome_11 w q) F"
  unfolding jacobi_theta_nome_11_def
  by (intro tendsto_intros assms(1,2)) (use assms(3-5) in auto)

lemma continuous_on_jacobi_theta_nome_11_complex [continuous_intros]:
  fixes f g :: "complex \<Rightarrow> complex"
  assumes "continuous_on A f" "continuous_on A g"
  assumes "\<And>z. z \<in> A \<Longrightarrow> f z \<noteq> 0" "\<And>z. z \<in> A \<Longrightarrow> norm (g z) < 1 \<and> (Re (g z) > 0 \<or> Im (g z) \<noteq> 0)"
  shows   "continuous_on A (\<lambda>z. jacobi_theta_nome_11 (f z) (g z))"
  unfolding jacobi_theta_nome_11_def
  by (intro continuous_intros assms(1,2); use assms(3,4) in force)

lemma continuous_jacobi_theta_nome_11_complex [continuous_intros]:
  assumes "continuous F f" "continuous F g" "f (netlimit F) \<noteq> 0" 
  assumes "norm (g (netlimit F)) < 1" "Re (g (netlimit F)) > 0 \<or> Im (g (netlimit F)) \<noteq> 0"
  shows   "continuous F (\<lambda>z. jacobi_theta_nome_11 (f z) (g z))"
  unfolding jacobi_theta_nome_11_def
  by (intro continuous_intros assms(1,2); use assms(3-) in force)

lemma tendsto_jacobi_theta_nome_11_real [tendsto_intros]:
  fixes f g :: "real \<Rightarrow> real"
  assumes "(f \<longlongrightarrow> w) F" "(g \<longlongrightarrow> q) F" "w \<noteq> 0" "norm q < 1" "q > 0"
  shows   "((\<lambda>z. jacobi_theta_nome_11 (f z) (g z)) \<longlongrightarrow> jacobi_theta_nome_11 w q) F"
  unfolding jacobi_theta_nome_11_def
  by (intro tendsto_intros assms(1,2)) (use assms(3-5) in auto)

lemma continuous_on_jacobi_theta_nome_11_real [continuous_intros]:
  fixes f g :: "real \<Rightarrow> real"
  assumes "continuous_on A f" "continuous_on A g"
  assumes "\<And>z. z \<in> A \<Longrightarrow> f z \<noteq> 0" "\<And>z. z \<in> A \<Longrightarrow> g z \<in> {0<..<1}"
  shows   "continuous_on A (\<lambda>z. jacobi_theta_nome_11 (f z) (g z))"
  unfolding jacobi_theta_nome_11_def
  by (intro continuous_intros assms(1,2); use assms(3,4) in force)

lemma continuous_jacobi_theta_nome_11_real [continuous_intros]:
  fixes f g :: "real \<Rightarrow> real"
  assumes "continuous F f" "continuous F g" "f (netlimit F) \<noteq> 0" "g (netlimit F) \<in> {0<..<1}"
  shows   "continuous F (\<lambda>z. jacobi_theta_nome_11 (f z) (g z))"
  unfolding jacobi_theta_nome_11_def
  by (intro continuous_intros assms(1,2); use assms(3-) in auto)



subsection \<open>The auxiliary theta functions in the complex plane\<close>

definition jacobi_theta_01 :: "complex \<Rightarrow> complex \<Rightarrow> complex" where
  "jacobi_theta_01 z t = jacobi_theta_00 (z + 1/2) t"
                                  
definition jacobi_theta_10 :: "complex \<Rightarrow> complex \<Rightarrow> complex" where
  "jacobi_theta_10 z t = to_nome (z + t/4) * jacobi_theta_00 (z + t/2) t"

definition jacobi_theta_11 :: "complex \<Rightarrow> complex \<Rightarrow> complex" where
  "jacobi_theta_11 z t = to_nome (z + t/4 + 1/2) * jacobi_theta_00 (z + t/2 + 1/2) t"

lemma jacobi_theta_00_conv_nome: 
  "jacobi_theta_00 z t = jacobi_theta_nome_00 (to_nome z) (to_nome t)"
  by (simp add: jacobi_theta_00_def jacobi_theta_nome_00_def)

lemma jacobi_theta_01_conv_nome:
  "jacobi_theta_01 z t = jacobi_theta_nome_01 (to_nome z) (to_nome t)"
  by (simp add: jacobi_theta_01_def jacobi_theta_nome_01_def jacobi_theta_00_conv_nome 
                jacobi_theta_nome_00_def to_nome_add power_mult_distrib)

lemma jacobi_theta_10_conv_nome:
  assumes "Re t \<in> {-1<..1}"
  shows   "jacobi_theta_10 z t = jacobi_theta_nome_10 (to_nome z) (to_nome t)"
  using assms
  by (simp add: jacobi_theta_10_def jacobi_theta_nome_10_def jacobi_theta_00_conv_nome 
                jacobi_theta_nome_00_def to_nome_add power_mult_distrib to_nome_power to_nome_powr)

lemma jacobi_theta_11_conv_nome:
  assumes "Re t \<in> {-1<..1}"
  shows   "jacobi_theta_11 z t = jacobi_theta_nome_11 (to_nome z) (to_nome t)"
  using assms
  by (simp add: jacobi_theta_11_def jacobi_theta_nome_11_def jacobi_theta_00_conv_nome 
                jacobi_theta_nome_00_def to_nome_add power_mult_distrib to_nome_power to_nome_powr)


lemma has_sum_jacobi_theta_01:
  assumes "Im t > 0"
  shows   "((\<lambda>n. (-1) powi n * to_nome (of_int n ^ 2 * t + 2 * of_int n * z)) 
             has_sum jacobi_theta_01 z t) UNIV"
proof -
  have "((\<lambda>n. to_nome (of_int n ^ 2 * t + 2 * of_int n * (z + 1 / 2))) has_sum jacobi_theta_01 z t) UNIV"
    unfolding jacobi_theta_01_def by (intro has_sum_jacobi_theta_00 assms)
  also have "(\<lambda>n. to_nome (of_int n ^ 2 * t + 2 * of_int n * (z + 1 / 2))) =
             (\<lambda>n. (-1) powi n * to_nome (of_int n ^ 2 * t + 2 * of_int n * z))"
    by (simp add: ring_distribs exp_add mult_ac to_nome_add)
  finally show ?thesis .
qed

lemma sums_jacobi_theta_01:
  assumes "Im t > 0"
  shows   "((\<lambda>n. if n = 0 then 1 else 2 * (-1) ^ n *  to_nome t ^ n\<^sup>2 * 
             cos (2 * of_nat n * of_real pi * z)) sums jacobi_theta_01 z t)"
proof -
  have [simp]: "sin (of_nat n * of_real pi :: complex) = 0" for n
    by (metis of_real_0 of_real_mult of_real_of_nat_eq sin_npi sin_of_real)
  have [simp]: "cos (of_nat n * of_real pi :: complex) = (-1) ^ n" for n
  proof -
    have "cos (of_nat n * of_real pi) = complex_of_real (cos (real n * pi))"
      by (subst cos_of_real [symmetric]) simp
    also have "cos (real n * pi) = (-1) ^ n"
      by simp
    finally show ?thesis by simp
  qed
  show ?thesis
    using sums_jacobi_theta_00[of t "z + 1/2"] assms
    by (simp add: jacobi_theta_01_def  ring_distribs cos_add mult_ac cong: if_cong)
qed


interpretation jacobi_theta_01_left: periodic_fun_simple' "\<lambda>z. jacobi_theta_01 z t"
proof
  fix z :: complex
  show "jacobi_theta_01 (z + 1) t = jacobi_theta_01 z t"
    using jacobi_theta_00_left.plus_1[of "z + 1/2" t] by (simp add: jacobi_theta_01_def)
qed

interpretation jacobi_theta_01_right: periodic_fun_simple "\<lambda>t. jacobi_theta_01 z t" 2
proof
  fix t :: complex
  show "jacobi_theta_01 z (t + 2) = jacobi_theta_01 z t"
    using jacobi_theta_00_right.plus_period[of "z + 1/2" t] by (simp add: jacobi_theta_01_def)
qed

lemma jacobi_theta_10_plus1_left: "jacobi_theta_10 (z + 1) t = -jacobi_theta_10 z t"
  using jacobi_theta_00_left.plus_1[of "z + t / 2" t] 
  by (simp add: jacobi_theta_10_def to_nome_add algebra_simps)

lemma jacobi_theta_11_plus1_left: "jacobi_theta_11 (z + 1) t = -jacobi_theta_11 z t"
  using jacobi_theta_00_left.plus_1[of "z + t / 2 + 1 / 2" t] 
  by (simp add: jacobi_theta_11_def to_nome_add algebra_simps)

lemma jacobi_theta_10_plus2_right: "jacobi_theta_10 z (t + 2) = \<i> * jacobi_theta_10 z t"
  using jacobi_theta_00_right.plus_1[of "z + t / 2" t] 
        jacobi_theta_00_left.plus_1[of "z + t / 2" "t + 2"] 
  by (simp add: jacobi_theta_10_def to_nome_add algebra_simps add_divide_distrib)

lemma jacobi_theta_11_plus2_right: "jacobi_theta_11 z (t + 2) = \<i> * jacobi_theta_11 z t"
  using jacobi_theta_00_right.plus_1[of "z + t / 2 + 1 / 2" t] 
        jacobi_theta_00_left.plus_1[of "z + t / 2 + 1 / 2" "t + 2"] 
  by (simp add: jacobi_theta_11_def to_nome_add algebra_simps add_divide_distrib)



lemma jacobi_theta_00_plus_half_left': "jacobi_theta_00 (z + 1/2) t = jacobi_theta_01 z t"
  by (simp add: jacobi_theta_01_def to_nome_add algebra_simps)

lemma jacobi_theta_01_plus_half_left: "jacobi_theta_01 (z + 1/2) t = jacobi_theta_00 z t"
  using jacobi_theta_00_left.plus_1[of z t]
  by (simp add: jacobi_theta_01_def to_nome_add algebra_simps)

lemma jacobi_theta_10_plus_half_left': "jacobi_theta_10 (z + 1/2) t = jacobi_theta_11 z t"
  by (simp add: jacobi_theta_10_def jacobi_theta_11_def to_nome_add algebra_simps)

lemma jacobi_theta_11_plus_half_left': "jacobi_theta_11 (z + 1/2) t = -jacobi_theta_10 z t"
  using jacobi_theta_00_left.plus_1[of "z + t / 2" t]
  by (simp add: jacobi_theta_10_def jacobi_theta_11_def to_nome_add algebra_simps)



lemma tendsto_jacobi_theta_01 [tendsto_intros]:
  assumes "(f \<longlongrightarrow> w) F" "(g \<longlongrightarrow> q) F" "Im q > 0"
  shows   "((\<lambda>z. jacobi_theta_01 (f z) (g z)) \<longlongrightarrow> jacobi_theta_01 w q) F"
  unfolding jacobi_theta_01_def
  by (intro tendsto_intros assms(1,2)) (use assms(3) in \<open>auto simp: norm_to_nome\<close>)

lemma continuous_on_jacobi_theta_01 [continuous_intros]:
  assumes "continuous_on A f" "continuous_on A g"
  assumes "\<And>z. z \<in> A \<Longrightarrow> Im (g z) > 0"
  shows   "continuous_on A (\<lambda>z. jacobi_theta_01 (f z) (g z))"
  unfolding jacobi_theta_01_def
  by (intro continuous_intros assms(1,2)) (use assms(3) in \<open>auto simp: norm_to_nome\<close>)

lemma continuous_jacobi_theta_01 [continuous_intros]:
  assumes "continuous F f" "continuous F g" "Im (g (netlimit F)) > 0"
  shows   "continuous F (\<lambda>z. jacobi_theta_01 (f z) (g z))"
  unfolding jacobi_theta_01_def
  by (intro continuous_intros assms(1,2)) (use assms(3) in \<open>auto simp: norm_to_nome\<close>)

lemma holomorphic_jacobi_theta_01 [holomorphic_intros]:
  assumes "f holomorphic_on A" "g holomorphic_on A" "\<And>z. z \<in> A \<Longrightarrow> Im (g z) > 0" "open A"
  shows   "(\<lambda>z. jacobi_theta_01 (f z) (g z)) holomorphic_on A"
  unfolding jacobi_theta_01_def by (intro holomorphic_intros assms(1,2)) (use assms(3-) in auto)

lemma analytic_jacobi_theta_01 [analytic_intros]:
  assumes "f analytic_on A" "g analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> Im (g z) > 0"
  shows   "(\<lambda>z. jacobi_theta_01 (f z) (g z)) analytic_on A"
  unfolding jacobi_theta_01_def by (intro analytic_intros assms(1,2)) (use assms(3-) in auto)


lemma tendsto_jacobi_theta_10 [tendsto_intros]:
  assumes "(f \<longlongrightarrow> w) F" "(g \<longlongrightarrow> q) F" "Im q > 0"
  shows   "((\<lambda>z. jacobi_theta_10 (f z) (g z)) \<longlongrightarrow> jacobi_theta_10 w q) F"
  unfolding jacobi_theta_10_def
  by (intro tendsto_intros assms(1,2)) (use assms(3) in \<open>auto simp: norm_to_nome\<close>)

lemma continuous_on_jacobi_theta_10 [continuous_intros]:
  assumes "continuous_on A f" "continuous_on A g"
  assumes "\<And>z. z \<in> A \<Longrightarrow> Im (g z) > 0"
  shows   "continuous_on A (\<lambda>z. jacobi_theta_10 (f z) (g z))"
  unfolding jacobi_theta_10_def
  by (intro continuous_intros assms(1,2)) (use assms(3) in \<open>auto simp: norm_to_nome\<close>)

lemma continuous_jacobi_theta_10 [continuous_intros]:
  assumes "continuous F f" "continuous F g" "Im (g (netlimit F)) > 0"
  shows   "continuous F (\<lambda>z. jacobi_theta_10 (f z) (g z))"
  unfolding jacobi_theta_10_def
  by (intro continuous_intros continuous_divide assms(1,2))
     (use assms(3) in \<open>auto simp: norm_to_nome\<close>)

lemma holomorphic_jacobi_theta_10 [holomorphic_intros]:
  assumes "f holomorphic_on A" "g holomorphic_on A" "\<And>z. z \<in> A \<Longrightarrow> Im (g z) > 0" "open A"
  shows   "(\<lambda>z. jacobi_theta_10 (f z) (g z)) holomorphic_on A"
  unfolding jacobi_theta_10_def by (intro holomorphic_intros assms(1,2)) (use assms(3-) in auto)

lemma analytic_jacobi_theta_10 [analytic_intros]:
  assumes "f analytic_on A" "g analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> Im (g z) > 0"
  shows   "(\<lambda>z. jacobi_theta_10 (f z) (g z)) analytic_on A"
  unfolding jacobi_theta_10_def by (intro analytic_intros assms(1,2)) (use assms(3-) in auto)


lemma tendsto_jacobi_theta_11 [tendsto_intros]:
  assumes "(f \<longlongrightarrow> w) F" "(g \<longlongrightarrow> q) F" "Im q > 0"
  shows   "((\<lambda>z. jacobi_theta_11 (f z) (g z)) \<longlongrightarrow> jacobi_theta_11 w q) F"
  unfolding jacobi_theta_11_def
  by (intro tendsto_intros assms(1,2)) (use assms(3) in \<open>auto simp: norm_to_nome\<close>)

lemma continuous_on_jacobi_theta_11 [continuous_intros]:
  assumes "continuous_on A f" "continuous_on A g"
  assumes "\<And>z. z \<in> A \<Longrightarrow> Im (g z) > 0"
  shows   "continuous_on A (\<lambda>z. jacobi_theta_11 (f z) (g z))"
  unfolding jacobi_theta_11_def
  by (intro continuous_intros assms(1,2)) (use assms(3) in \<open>auto simp: norm_to_nome\<close>)

lemma continuous_jacobi_theta_11 [continuous_intros]:
  assumes "continuous F f" "continuous F g" "Im (g (netlimit F)) > 0"
  shows   "continuous F (\<lambda>z. jacobi_theta_11 (f z) (g z))"
  unfolding jacobi_theta_11_def
  by (intro continuous_intros continuous_divide assms(1,2))
     (use assms(3) in \<open>auto simp: norm_to_nome\<close>)

lemma holomorphic_jacobi_theta_11 [holomorphic_intros]:
  assumes "f holomorphic_on A" "g holomorphic_on A" "\<And>z. z \<in> A \<Longrightarrow> Im (g z) > 0" "open A"
  shows   "(\<lambda>z. jacobi_theta_11 (f z) (g z)) holomorphic_on A"
  unfolding jacobi_theta_11_def by (intro holomorphic_intros assms(1,2)) (use assms(3-) in auto)

lemma analytic_jacobi_theta_11 [analytic_intros]:
  assumes "f analytic_on A" "g analytic_on A" "\<And>z. z \<in> A \<Longrightarrow> Im (g z) > 0"
  shows   "(\<lambda>z. jacobi_theta_11 (f z) (g z)) analytic_on A"
  unfolding jacobi_theta_11_def by (intro analytic_intros assms(1,2)) (use assms(3-) in auto)

(* TODO: transformations under the modular group *)

end