section \<open>$q$-analogues of basic combinatorial symbols\<close>
theory Q_Analogues
imports "HOL-Complex_Analysis.Complex_Analysis" Q_Library
begin

text \<open>
  Various mathematical operations have generalisations in the form of $q$-analogues, 
  usually in the sense that one recovers the original notion if we let $q\to 1$.
\<close>

subsection \<open>The $q$-bracket $[n]_q$\<close>

text \<open>
  The $q$-bracket $[n]_q = \frac{1-q^n}{1-q}$ is the $q$-analogue of an integer $n$.
  The $q$-bracket has a removable singularity at $q = 1$ with $\lim_{q\to 1} [n]_q = n$.
\<close>
definition qbracket :: "'a \<Rightarrow> int \<Rightarrow> 'a :: field" where
  "qbracket q n = (if q = 1 then of_int n else (1 - q powi n) / (1 - q))"

lemma qbracket_1_left [simp]: "qbracket 1 n = of_int n"
  by (simp add: qbracket_def)

lemma qbracket_0_0 [simp]: "qbracket 0 0 = 0"
  by (auto simp: qbracket_def power_int_0_left_if)

lemma qbracket_0_nonneg [simp]: "n \<noteq> 0 \<Longrightarrow> qbracket 0 n = 1"
  by (auto simp: qbracket_def power_int_0_left_if)

lemma qbracket_0_left: "qbracket 0 n = (if n = 0 then 0 else 1)"
  by auto

lemma qbracket_0 [simp]: "qbracket q 0 = 0"
  by (simp add: qbracket_def)

lemma qbracket_1 [simp]: "qbracket q 1 = 1"
  by (simp add: qbracket_def)

lemma qbracket_2 [simp]: "qbracket q 2 = 1 + q"
  by (simp add: qbracket_def field_simps power2_eq_square)

lemma qbracket_of_real: "qbracket (of_real q :: 'a :: real_field) n = of_real (qbracket q n)"
  by (simp add: qbracket_def)

lemma qbracket_minus:
  assumes "q = 0 \<longrightarrow> n = 0"
  shows   "qbracket q (-n) = -qbracket (inverse q) n / q"
proof (cases "q = 1")
  case True
  thus ?thesis by auto
next
  case False
  have "qbracket q (-n) = qbracket (inverse q) n * (1 - 1 / q) / (1 - q)"
    using assms False by (auto simp add: qbracket_def power_int_minus divide_simps)
  also have "\<dots> = -qbracket (inverse q) n / q"
    using assms False by (simp add: divide_simps) (auto simp: field_simps qbracket_0_left)
  finally show ?thesis .
qed

lemma qbracket_inverse:
  assumes "q = 0 \<longrightarrow> n = 0"
  shows   "qbracket (inverse q) n = -q * qbracket q (-n)"
  using assms by (cases "q = 0") (auto simp: qbracket_minus qbracket_0_left)

lemma qbracket_nonneg_altdef: "n \<ge> 0 \<Longrightarrow> qbracket q n = (\<Sum>k<nat n. q ^ k)"
  by (auto simp: qbracket_def sum_gp_strict power_int_def)

lemma qbracket_nonpos_altdef:
  assumes n: "n \<le> 0" and [simp]: "q \<noteq> 0"
  shows   "qbracket q n = -(q powi n * (\<Sum>k<nat (-n). q ^ k))"
proof -
  have "qbracket q n = qbracket q (-(-n))"
    by simp
  also have "\<dots> = -qbracket (inverse q) (-n) / q"
    by (intro qbracket_minus) auto
  also have "\<dots> = -(\<Sum>k<nat (-n). inverse q ^ k) / q"
    using n by (subst qbracket_nonneg_altdef) auto
  also have "\<dots> = -(\<Sum>k<nat (-n). q powi (-(k+1)))"
    by (simp add: sum_divide_distrib field_simps power_int_diff)
  also have "(\<Sum>k<nat (-n). q powi (-(k+1))) = (\<Sum>k<nat (-n). q powi (n + k))"
    by (intro sum.reindex_bij_witness[of _ "\<lambda>k. nat (-n) - k - 1" "\<lambda>k. nat (-n) - k - 1"])
       (auto simp: of_nat_diff)
  also have "\<dots> = q powi n * (\<Sum>k<nat (-n). q ^ k)"
    by (simp add: power_int_add sum_distrib_left sum_distrib_right)
  finally show ?thesis .
qed

lemma norm_qbracket_le:
  fixes q :: "'a :: real_normed_field"
  assumes "n \<ge> 0" "norm q \<le> 1"
  shows   "norm (qbracket q n) \<le> real_of_int n"
proof -
  have "norm (qbracket q n) = norm (sum (\<lambda>k. q ^ k) {..<nat n})"
    using assms by (simp add: qbracket_nonneg_altdef)
  also have "\<dots> \<le> (\<Sum>k<nat n. norm q ^ k)"
    by (rule sum_norm_le) (simp_all add: norm_power)
  also have "\<dots> \<le> (\<Sum>k<nat n. 1 ^ k)"
    using assms by (intro sum_mono power_mono) auto
  finally show ?thesis
    using assms by simp
qed

lemma qbracket_add: 
  assumes "q \<noteq> 0 \<or> (k + l = 0 \<longrightarrow> k = 0)"
  shows   "qbracket q (k + l) = qbracket q l * q powi k + qbracket q k"
  using assms
  by (cases "q = 0")
     (auto simp: qbracket_def divide_simps power_int_add power_int_diff
                 power_int_0_left_if add_eq_0_iff,
      (simp add: algebra_simps)?)

lemma qbracket_diff:
  assumes "q \<noteq> 0 \<or> (k = l \<longrightarrow> k = 0)"
  shows "qbracket q (k - l) = qbracket q (-l) * q powi k + qbracket q k"
  using assms qbracket_add[of q k "-l"] by simp

lemma qbracket_diff':
  assumes "q \<noteq> 0 \<or> (k = l \<longrightarrow> k = 0)"
  shows   "qbracket q (k - l) = qbracket q k * q powi -l + qbracket q (-l)"
  using assms qbracket_add[of q "-l" k] by simp

lemma qbracket_plus1: "q \<noteq> 0 \<or> n \<noteq> -1 \<Longrightarrow> qbracket q (n + 1) = qbracket q n + q powi n"
  by (subst qbracket_add) (auto simp: add_eq_0_iff)

lemma qbracket_rec: "q \<noteq> 0 \<or> n \<noteq> 0 \<Longrightarrow> qbracket q n = qbracket q (n-1) + q powi (n-1)"
  using qbracket_plus1[of q "n-1"] by simp

lemma qbracket_eq_0_iff:
  fixes q :: "'a :: field"
  shows   "qbracket q n = 0 \<longleftrightarrow> (q = 1 \<and> of_int n = (0 :: 'a)) \<or> (q \<noteq> 1 \<and> q powi n = 1)"
  by (auto simp: qbracket_def)

lemma continuous_on_qbracket [continuous_intros]:
  fixes q :: "'a::topological_space \<Rightarrow> 'b :: real_normed_field"
  assumes [continuous_intros]: "continuous_on A q"
  assumes "\<And>x. n < 0 \<Longrightarrow> x \<in> A \<Longrightarrow> q x \<noteq> 0"
  shows   "continuous_on A (\<lambda>x. qbracket (q x) n)"
proof (cases "n \<ge> 0")
  case True
  thus ?thesis 
    by (auto simp: qbracket_nonneg_altdef intro!: continuous_intros)
next
  case False
  thus ?thesis using assms(2)
    by (auto simp: qbracket_nonpos_altdef intro!: continuous_intros)
qed

lemma tendsto_qbracket [tendsto_intros]:
  fixes q :: "'a::topological_space \<Rightarrow> 'b :: real_normed_field"
  assumes "(q \<longlongrightarrow> Q) F"
  assumes "n < 0 \<Longrightarrow> Q \<noteq> 0"
  shows   "((\<lambda>x. qbracket (q x) n) \<longlongrightarrow> qbracket Q n) F"
proof -
  have "continuous_on (if n < 0 then -{0} else UNIV) (\<lambda>x. qbracket x n :: 'b)"
    by (intro continuous_intros) auto
  moreover have "Q \<in> (if n < 0 then -{0} else UNIV)"
    using assms(2) by auto
  moreover have "open (if n < 0 then -{0::'b} else UNIV)"
    by auto
  ultimately have "isCont (\<lambda>x. qbracket x n :: 'b) Q"
    using continuous_on_eq_continuous_at by blast
  with assms(1) show ?thesis
    using continuous_within_tendsto_compose' by force
qed

lemma continuous_qbracket [continuous_intros]:
  fixes q :: "'a::t2_space \<Rightarrow> 'b :: real_normed_field"
  assumes "continuous F q"
  assumes "n < 0 \<Longrightarrow> q (netlimit F) \<noteq> 0"
  shows   "continuous F (\<lambda>x. qbracket (q x) n)"
  using assms unfolding continuous_def by (intro tendsto_intros) auto

lemma has_field_derivative_qbracket_real [derivative_intros]:
  fixes q :: real
  assumes "q \<noteq> 0 \<or> n \<ge> 0"
  defines "D \<equiv> (if q = 1 then of_int (n * (n - 1)) / 2
                 else (1 - q powi n)/(1-q)^2 - of_int n * q powi (n-1) / (1-q))"
  shows   "((\<lambda>q. qbracket q n) has_field_derivative D) (at q within A)"
proof (cases "q = 1")
  case False
  have "((\<lambda>q. (1 - q powi n) / (1 - q)) has_field_derivative D) (at q within A)"
    unfolding D_def using assms(1) False
    by (auto intro!: derivative_eq_intros simp: divide_simps power2_eq_square)
  also have ev: "eventually (\<lambda>q. q \<noteq> 1) (at q within A)"
    using False eventually_neq_at_within by blast
  have "((\<lambda>q. (1 - q powi n) / (1 - q)) has_field_derivative D) (at q within A) \<longleftrightarrow>
        ((\<lambda>q. qbracket q n) has_field_derivative D) (at q within A)"
    by (intro has_field_derivative_cong_eventually eventually_mono[OF ev]) (auto simp: qbracket_def False)
  finally show ?thesis .
next
  case True
  have ev: "eventually (\<lambda>q::real. q > 0) (at 1)"
    by real_asymp
  have "(\<lambda>q::real. ((1 - q powr n) / (1 - q) - of_int n) / (q - 1)) \<midarrow>1\<rightarrow> of_int (n * (n - 1)) / 2"
    by real_asymp
  also have "?this \<longleftrightarrow> (\<lambda>q::real. ((1 - q powi n) / (1 - q) - of_int n) / (q - 1)) \<midarrow>1\<rightarrow> of_int (n * (n - 1)) / 2"
    by (intro tendsto_cong) (use ev in eventually_elim, auto simp: powr_real_of_int')
  also have "\<dots> \<longleftrightarrow> ((\<lambda>y. (qbracket y n - qbracket q n) / (y - q)) \<longlongrightarrow> D) (at q)"
    unfolding D_def True
    by (intro filterlim_cong eventually_mono[OF eventually_neq_at_within[of 1]])
       (auto simp: qbracket_def)
  finally show ?thesis
    unfolding has_field_derivative_iff using Lim_at_imp_Lim_at_within by blast
qed

lemma has_field_derivative_qbracket_complex [derivative_intros]:
  fixes q :: complex
  assumes "q \<noteq> 0 \<or> n \<ge> 0"
  defines "D \<equiv> (if q = 1 then of_int (n * (n - 1)) / 2
                 else (1 - q powi n)/(1-q)^2 - of_int n * q powi (n-1) / (1-q))"
  shows   "((\<lambda>q. qbracket q n) has_field_derivative D) (at q within A)"
proof (cases "q = 1")
  case False
  have "((\<lambda>q. (1 - q powi n) / (1 - q)) has_field_derivative D) (at q within A)"
    unfolding D_def using assms(1) False
    by (auto intro!: derivative_eq_intros simp: divide_simps power2_eq_square)
  also have ev: "eventually (\<lambda>q. q \<noteq> 1) (at q within A)"
    using False eventually_neq_at_within by blast
  have "((\<lambda>q. (1 - q powi n) / (1 - q)) has_field_derivative D) (at q within A) \<longleftrightarrow>
        ((\<lambda>q. qbracket q n) has_field_derivative D) (at q within A)"
    by (intro has_field_derivative_cong_eventually eventually_mono[OF ev]) (auto simp: qbracket_def False)
  finally show ?thesis .
next
  case True
  define F :: "complex fps"
    where "F = fps_binomial (of_int n) - 1 - of_int n * fps_X"
  have F: "(\<lambda>w. ((1 - (1+w) powi n) / (1 - (1+w)) - of_int n) / ((1+w) - 1)) has_laurent_expansion
             fls_shift 2 (fps_to_fls F)"
    by (rule has_laurent_expansion_schematicI, (rule laurent_expansion_intros)+)
       (simp_all flip: fls_of_int fls_divide_fps_to_fls 
                 add: fls_times_fps_to_fls fls_X_times_conv_shift one_plus_fls_X_powi_eq F_def)
  have F': "fls_subdegree (fls_shift 2 (fps_to_fls F)) \<ge> 0"
  proof (cases "F = 0")
    case [simp]: False
    hence "subdegree F \<ge> 2"
      by (intro subdegree_geI) (auto simp: F_def numeral_2_eq_2 less_Suc_eq)
    thus ?thesis
      by (intro fls_shift_nonneg_subdegree) (simp add: fls_subdegree_fls_to_fps)
  qed auto

  have "(\<lambda>w. ((1 - w powi n) / (1 - w) - complex_of_int n) / (w - 1)) \<midarrow>1\<rightarrow> 
          fls_nth (fls_shift 2 (fps_to_fls F)) 0"
    using has_laurent_expansion_imp_tendsto[OF F F'] .
  also have "fls_nth (fls_shift 2 (fps_to_fls F)) 0 = of_int (n * (n - 1)) / 2"
    by (simp add: F_def numeral_2_eq_2 gbinomial_Suc_rec)
  finally have "(\<lambda>q :: complex. ((1 - q powi n) / (1 - q) - of_int n) / (q - 1)) \<midarrow>1\<rightarrow> of_int (n * (n - 1)) / 2" .
  also have "?this \<longleftrightarrow> ((\<lambda>y. (qbracket y n - qbracket q n) / (y - q)) \<longlongrightarrow> D) (at q)"
    unfolding D_def True
    by (intro filterlim_cong eventually_mono[OF eventually_neq_at_within[of 1]])
       (auto simp: qbracket_def)
  finally show ?thesis
    unfolding has_field_derivative_iff using Lim_at_imp_Lim_at_within by blast
qed

lemma holomorphic_on_qbracket [holomorphic_intros]:
  assumes "q holomorphic_on A"
  assumes "\<And>x. n < 0 \<Longrightarrow> x \<in> A \<Longrightarrow> q x \<noteq> 0"
  shows   "(\<lambda>x. qbracket (q x) n) holomorphic_on A"
proof -
  have "(\<lambda>x. qbracket x n) holomorphic_on (if n < 0 then -{0} else UNIV)"
    by (subst holomorphic_on_open) (auto intro!: derivative_eq_intros)
  hence "((\<lambda>x. qbracket x n) \<circ> q) holomorphic_on A"
    by (intro holomorphic_on_compose_gen) (use assms in auto)
  thus ?thesis
    by (simp add: o_def)
qed

lemma analytic_on_qbracket [analytic_intros]:
  assumes "q analytic_on A"
  assumes "\<And>x. n < 0 \<Longrightarrow> x \<in> A \<Longrightarrow> q x \<noteq> 0"
  shows   "(\<lambda>x. qbracket (q x) n) analytic_on A"
proof -
  have "(\<lambda>x. qbracket x n) holomorphic_on (if n < 0 then -{0} else UNIV)"
    by (intro holomorphic_intros) auto
  hence "(\<lambda>x. qbracket x n) analytic_on (if n < 0 then -{0} else UNIV)"
    by (subst analytic_on_open) auto
  hence "((\<lambda>x. qbracket x n) \<circ> q) analytic_on A"
    by (intro analytic_on_compose_gen) (use assms in auto)
  thus ?thesis
    by (simp add: o_def)
qed

lemma meromorphic_on_qbracket [meromorphic_intros]:
  assumes "q meromorphic_on A"
  shows   "(\<lambda>x. qbracket (q x) n) meromorphic_on A"
proof -
  have "(\<lambda>x. qbracket (q x) n) meromorphic_on {z}" if z: "z \<in> A" for z
  proof -
    have [meromorphic_intros]: "q meromorphic_on {z}"
      using assms by (rule meromorphic_on_subset) (use z in auto)
    show "(\<lambda>x. qbracket (q x) n) meromorphic_on {z}"
    proof (cases "eventually (\<lambda>x. q x \<noteq> 1) (at z)")
      case True
      have "(\<lambda>x. (1 - q x powi n) / (1 - q x)) meromorphic_on {z}"
        by (intro meromorphic_intros)
      also have "eventually (\<lambda>x. (1 - q x powi n) / (1 - q x) =  qbracket (q x) n) (at z)"
        using True by eventually_elim (auto simp: qbracket_def)
      hence "(\<lambda>x. (1 - q x powi n) / (1 - q x)) meromorphic_on {z} \<longleftrightarrow>
             (\<lambda>x. qbracket (q x) n) meromorphic_on {z}"
        by (intro meromorphic_on_cong) auto
      finally show ?thesis .
    next
      case False
      have "(\<lambda>z. q z - 1) meromorphic_on {z}"
        by (intro meromorphic_intros)
      with False have "eventually (\<lambda>x. q x = 1) (at z)"
        using not_essential_frequently_0_imp_eventually_0[of "\<lambda>z. q z - 1" z]
        by (auto simp: meromorphic_at_iff frequently_def)
      hence "eventually (\<lambda>x. qbracket (q x) n = of_int n) (at z)"
        by eventually_elim auto
      hence "(\<lambda>x. qbracket (q x) n) meromorphic_on {z} \<longleftrightarrow> (\<lambda>_. of_int n) meromorphic_on {z}"
        by (intro meromorphic_on_cong) auto
      thus ?thesis
        by auto
    qed
  qed
  thus ?thesis
    using meromorphic_on_meromorphic_at by blast
qed


subsection \<open>The $q$-factorial $[n]_q!$\<close>

text \<open>
  Since the $q$-bracket gives us the $q$-analogue of an integer $n$, we can use this
  to recursively define the $q$-factorial $[n]_q!$. Again, letting $q\to 1$, we recover
  the ``normal'' factorial.
\<close>
definition qfact :: "'a \<Rightarrow> int \<Rightarrow> 'a :: field" where
  "qfact q n = (if n < 0 then 0 else (\<Prod>k=1..n. qbracket q k))"

lemma qfact_1_of_nat [simp]: "qfact 1 (int n) = fact n"
proof -
  have "qfact 1 (int n) = of_int (\<Prod>k=1..int n. k)"
    by (simp add: qfact_def)
  also have "(\<Prod>k=1..int n. k) = (\<Prod>k=1..n. int k)"
    by (intro prod.reindex_bij_witness[of _ int nat]) auto
  finally show ?thesis
    by (simp add: fact_prod)
qed

lemma qfact_1_nonneg [simp]: "n \<ge> 0 \<Longrightarrow> qfact 1 n = fact (nat n)"
  by (subst qfact_1_of_nat [symmetric], subst int_nat_eq) auto

lemma qfact_neg [simp]: "n < 0 \<Longrightarrow> qfact q n = 0"
  by (simp add: qfact_def)

lemma qfact_0 [simp]: "qfact q 0 = 1"
  by (simp add: qfact_def)

lemma qfact_1 [simp]: "qfact q 1 = 1"
  by (simp add: qfact_def)

lemma qfact_2: "qfact q 2 = 1 + q"
proof -
  have "{1..2::int} = {1, 2}"
    by auto
  thus ?thesis
    by (simp add: qfact_def)
qed

lemma qfact_of_real: "qfact (of_real q :: 'a :: real_field) n = of_real (qfact q n)"
  by (simp add: qfact_def qbracket_of_real)

lemma qfact_plus1: "n \<noteq> -1 \<Longrightarrow> qfact q (n + 1) = qfact q n * qbracket q (n + 1)"
  unfolding qfact_def by (simp add: add.commute atLeastAtMostPlus1_int_conv)

lemma qfact_rec: "n > 0 \<Longrightarrow> qfact q n = qbracket q n * qfact q (n - 1)"
  using qfact_plus1[of "n - 1" q] by auto

lemma qfact_altdef: "q \<noteq> 1 \<Longrightarrow> n \<ge> 0 \<Longrightarrow> qfact q n = (\<Prod>k=1..n. 1 - q powi k) * (1 - q) powi (-n)"
  by (auto simp: qfact_def qbracket_def prod_dividef power_int_def field_simps)

lemma qfact_int_def: "qfact q (int n) = (\<Prod>k=1..n. qbracket q (int k))"
  unfolding qfact_def by (auto intro!: prod.reindex_bij_witness[of _ int nat])

lemma qfact_eq_0_iff:
  fixes q :: "'a :: field_char_0"
  shows "qfact q n = 0 \<longleftrightarrow> n < 0 \<or> (q \<noteq> 1 \<and> (\<exists>k\<in>{1..nat n}. q ^ k = 1))"
proof (cases "n < 0")
  case False
  have "qfact q (int m) = 0 \<longleftrightarrow> q \<noteq> 1 \<and> (\<exists>k\<in>{1..m}. q ^ k = 1)" for m
  proof (cases "q = 1")
    case False
    show ?thesis
    proof (induction m)
      case (Suc m)
      have *: "int (Suc m) - 1 = int m"
        by simp
      have "(qfact q (int (Suc m)) = 0) \<longleftrightarrow> (q ^ Suc m = 1 \<or> (\<exists>k\<in>{1..m}. q ^ k = 1))"
        using False by (simp add: qfact_rec Suc qbracket_eq_0_iff * del: of_nat_Suc)
      also have "\<dots> \<longleftrightarrow> (\<exists>k\<in>{1..Suc m}. q ^ k = 1)"
        by (subst atLeastAtMostSuc_conv) auto
      finally show ?case using False by simp
    qed auto
  qed auto
  from this[of "nat n"] False show ?thesis
    by simp
qed auto

lemma qfact_eq_0_iff' [simp]:
  fixes q :: "'a :: real_normed_field"
  assumes "norm q \<noteq> 1"
  shows   "qfact q n = 0 \<longleftrightarrow> n < 0"
  using assms by (subst qfact_eq_0_iff) (auto dest: power_eq_1_iff)

lemma prod_neg_qbracket_conv_qfact:
  assumes [simp]: "q \<noteq> 0"
  shows   "(\<Prod>k=1..n. qbracket q (-int k)) = (-1)^n * qfact q n / q ^ ((n+1) choose 2)"
proof (cases "q = 1")
  case [simp]: False
  have "(-1)^n * qfact q n / q ^ ((n+1) choose 2) =
          (\<Prod>k=1..n. (1 - q ^ k) / (1 - q)) / ((-1) ^ n * q ^ (Suc n choose 2))"
    by (simp add: qbracket_def prod_dividef qfact_int_def power_int_minus divide_simps)
  also have "(Suc n choose 2) = (\<Sum>k=1..n. k)"
    by (induction n) (auto simp: choose_two)
  also have "(-1) ^ n * q ^ (\<Sum>k=1..n. k) = (\<Prod>k=1..n. -(q ^ k))"
    by (simp add: power_sum prod_uminus)
  also have "(\<Prod>k=1..n. (1 - q ^ k) / (1 - q)) / (\<Prod>k=1..n. -(q ^ k)) =
             (\<Prod>k=1..n. (1 - q ^ k) / (1 - q) / (-(q ^ k)))"
    by (rule prod_dividef [symmetric])
  also have "\<dots> = (\<Prod>k=1..n. qbracket q (-int k))"
    by (intro prod.cong refl) (auto simp: qbracket_def power_int_minus divide_simps)
  finally show ?thesis ..
qed (auto simp: prod_uminus qfact_int_def)

lemma norm_qfact_le:
  fixes q :: "'a :: real_normed_field"
  assumes "n \<ge> 0" "norm q \<le> 1"
  shows   "norm (qfact q n) \<le> fact (nat n)"
proof -
  have "norm (qfact q n) = (\<Prod>k=1..n. norm (qbracket q k))"
    using assms by (simp add: qfact_def prod_norm)
  also have "\<dots> \<le> (\<Prod>k=1..n. real_of_int k)"
    using assms by (intro prod_mono norm_qbracket_le conjI) auto
  also have "\<dots> = of_nat (\<Prod>k=1..nat n. k)"
    unfolding of_nat_prod by (intro prod.reindex_bij_witness[of _ int nat]) auto
  also have "\<dots> = fact (nat n)"
    using assms by (simp add: fact_prod)
  finally show ?thesis .
qed


lemma continuous_on_qfact [continuous_intros]:
  fixes q :: "'a::topological_space \<Rightarrow> 'b :: real_normed_field"
  assumes [continuous_intros]: "continuous_on A q"
  shows   "continuous_on A (\<lambda>x. qfact (q x) n)"
proof (cases "n \<ge> 0")
  case True
  thus ?thesis 
    by (auto simp: qfact_def intro!: continuous_intros)
qed auto

lemma continuous_qfact [continuous_intros]:
  fixes q :: "'a::t2_space \<Rightarrow> 'b :: real_normed_field"
  assumes [continuous_intros]: "continuous F q"
  shows   "continuous F (\<lambda>x. qfact (q x) n)"
proof (cases "n \<ge> 0")
  case True
  thus ?thesis 
    by (auto simp: qfact_def intro!: continuous_intros)
qed auto

lemma tendsto_qfact [tendsto_intros]:
  fixes q :: "'a::topological_space \<Rightarrow> 'b :: real_normed_field"
  assumes [tendsto_intros]: "(q \<longlongrightarrow> Q) F"
  shows   "((\<lambda>x. qfact (q x) n) \<longlongrightarrow> qfact Q n) F"
proof (cases "n \<ge> 0")
  case True
  thus ?thesis 
    by (auto simp: qfact_def intro!: tendsto_intros)
qed auto

lemma holomorphic_on_qfact [holomorphic_intros]:
  assumes [holomorphic_intros]: "q holomorphic_on A"
  shows   "(\<lambda>x. qfact (q x) n) holomorphic_on A"
proof (cases "n \<ge> 0")
  case True
  thus ?thesis 
    by (auto simp: qfact_def intro!: holomorphic_intros)
qed auto

lemma analytic_on_qfact [analytic_intros]:
  assumes [analytic_intros]: "q analytic_on A"
  shows   "(\<lambda>x. qfact (q x) n) analytic_on A"
proof (cases "n \<ge> 0")
  case True
  thus ?thesis 
    by (auto simp: qfact_def intro!: analytic_intros)
qed auto

lemma meromorphic_on_qfact [meromorphic_intros]:
  assumes [meromorphic_intros]: "q meromorphic_on A"
  shows   "(\<lambda>x. qfact (q x) n) meromorphic_on A"
proof (cases "n \<ge> 0")
  case True
  thus ?thesis 
    by (auto simp: qfact_def intro!: meromorphic_intros)
qed auto



subsection \<open>$q$-binomial coefficients $\binom{n}{k}_{\!q}$\<close>

text \<open>
  We can also define $q$-binomial coefficients in such a way that we will get
  \[\binom{n}{k}_{\!q} = \frac{[n]_q!]}{[k]_q!\,[n-k]_q!}\]
  and therefore recover the ``normal'' binomial coefficients if we let $q\to 1$.
\<close>
fun qbinomial :: "'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a :: field" where
  "qbinomial q n 0 = 1"
| "qbinomial q 0 (Suc k) = 0"
| "qbinomial q (Suc n) (Suc k) = q ^ Suc k * qbinomial q n (Suc k) + qbinomial q n k"

lemma qbinomial_induct [case_names zero_right zero_left step]:
   "(\<And>n. P n 0) \<Longrightarrow> (\<And>k. P 0 (Suc k)) \<Longrightarrow> 
    (\<And>n k. P n (Suc k) \<Longrightarrow> P n k \<Longrightarrow> P (Suc n) (Suc k)) \<Longrightarrow> P n k"
  by (induction_schema, pat_completeness, lexicographic_order)

lemma qbinomial_1_left [simp]: "qbinomial 1 n k = of_nat (binomial n k)"
  by (induction n k rule: qbinomial_induct) simp_all

lemma qbinomial_eq_0 [simp]: "k > n \<Longrightarrow> qbinomial q n k = 0"
  by (induction q n k rule: qbinomial.induct) auto

lemma qbinomial_n_n [simp]: "qbinomial q n n = 1"
  by (induction n) simp_all

lemma qbinomial_0_left: "qbinomial 0 n k = (if k \<le> n then 1 else 0)"
  by (induction n k rule: qbinomial_induct) auto

lemma qbinomial_0_left' [simp]: "k \<le> n \<Longrightarrow> qbinomial 0 n k = 1"
  by (simp add: qbinomial_0_left)

lemma qbinomial_0_middle: "qbinomial q 0 k = (if k = 0 then 1 else 0)"
  by (cases k) auto

lemma qbinomial_of_real: "qbinomial (of_real q :: 'a :: real_field) m n = of_real (qbinomial q m n)"
  by (induction m n rule: qbinomial_induct) simp_all

lemma qbinomial_qfact_lemma:
  assumes "k \<le> n"
  shows   "qfact q k * qfact q (int (n - k)) * qbinomial q n k = qfact q n"
  using assms
proof (induction q n k rule: qbinomial.induct)
  case (3 q n k)
  show ?case
  proof (cases "n = k")
    case False
    with "3.prems" have "k < n"
      by auto
    hence "(qfact q (int (Suc k)) * qfact q (int (Suc n - Suc k)) * qbinomial q (Suc n) (Suc k)) =
              qbracket q (int (n-k)) * q^(k+1) *
                (qfact q (Suc k) * qfact q (int (n-Suc k)) * qbinomial q n (Suc k)) +
              (qbracket q (k+1) * (qfact q k * qfact q (int (n-k)) * qbinomial q n k))"
      by (simp add: qfact_rec of_nat_diff algebra_simps)
    also have "qfact q (Suc k) * qfact q (int (n-Suc k)) * qbinomial q n (Suc k) = qfact q (int n)"
      using \<open>k <  n\<close> by (subst 3) auto
    also have "qbracket q (k+1) * (qfact q k * qfact q (int (n-k)) * qbinomial q n k) =
               qbracket q (k+1) * qfact q (int n)"
      using \<open>k <  n\<close> by (subst 3) auto
    also have "qbracket q (int (n - k)) * q^(k+1) * qfact q (int n) +
                 qbracket q (int (k + 1)) * qfact q (int n) =
                 (qbracket q (int (n - k)) * q^(k+1) + qbracket q (int (k + 1))) * qfact q (int n)"
      by (simp add: algebra_simps)
    also have "qbracket q (int (n - k)) * q^(k+1) + qbracket q (int (k + 1)) = 
               qbracket q (int n - int k) * q powi (int (k+1)) + qbracket q (int (k+1))"
      using \<open>k < n\<close> by (simp add: power_int_add of_nat_diff)
    also have "\<dots> = qbracket q (int (k + 1) + (int n - int k))"
      by (rule qbracket_add [symmetric]) auto
    also have "\<dots> = qbracket q (int (Suc n))"
      by simp
    also have "\<dots> * qfact q (int n) = qfact q (int (Suc n))"
      by (simp add: qfact_rec)
    finally show ?thesis .
  qed simp_all
qed simp_all

lemma qbinomial_qfact:
  fixes q :: "'a :: field_char_0"
  assumes "\<not>(\<exists>k\<in>{1..n}. q ^ k = 1)"
  shows   "qbinomial q n k = qfact q n / (qfact q k * qfact q (int n - int k))"
proof (cases "k \<le> n")
  case True
  thus ?thesis using assms
    by (subst qbinomial_qfact_lemma[of k n q, symmetric])
       (auto simp add: qfact_eq_0_iff of_nat_diff divide_simps)
qed auto

lemma qbinomial_qfact':
  fixes q :: "'a :: real_normed_field"
  assumes "q = 1 \<or> norm q \<noteq> 1"
  shows   "qbinomial q n k = qfact q n / (qfact q k * qfact q (int n - int k))"
proof (cases "q = 1")
  case False
  thus ?thesis
    using assms by (subst qbinomial_qfact) (auto dest!: power_eq_1_iff)
next
  case True
  thus ?thesis
    by (cases "k \<le> n") (auto simp: binomial_fact simp flip: of_nat_diff)
qed

lemma qbinomial_symmetric:
  fixes q :: "'a :: real_normed_field"
  assumes "norm q \<noteq> 1" "k \<le> n"
  shows   "qbinomial q n (n - k) = qbinomial q n k"
  using assms by (subst (1 2) qbinomial_qfact') (auto simp: of_nat_diff)

lemma qbinomial_rec1:
  "n > 0 \<Longrightarrow> k > 0 \<Longrightarrow>
     qbinomial q n k = q ^ k * qbinomial q (n - 1) k + qbinomial q (n - 1) (k - 1)"
  by (cases n; cases k) auto

lemma qbinomial_rec2:
  fixes q :: "'a :: real_normed_field"
  assumes "norm q \<noteq> 1" "n > 0" "k < n"
  shows   "qbinomial q n k = (1 - q ^ n) / (1 - q ^ (n - k)) * qbinomial q (n-1) k"
proof (cases "q = 0")
  case [simp]: False
  have *: "q ^ i = q ^ j \<longleftrightarrow> i = j" for i j
  proof
    assume "q ^ i = q ^ j"
    hence "norm (q ^ i) = norm (q ^ j)"
      by (rule arg_cong)
    hence "norm q ^ i = norm q ^ j"
      by (simp add: norm_power)
    thus "i = j"
      by (subst (asm) power_inject_exp') (use assms in auto)
  qed auto
  show ?thesis using assms
    by (subst (1 2) qbinomial_qfact')  
       (use assms 
         in \<open>simp_all add: divide_simps of_nat_diff power_int_diff qfact_rec qbracket_eq_0_iff
                           power_0_left qbracket_def power_diff Groups.diff_right_commute *\<close>)
qed (use assms in \<open>auto simp: power_0_left\<close>)

lemma qbinomial_rec3:
  fixes q :: "'a :: real_normed_field"
  assumes "norm q \<noteq> 1" "k > 0" "k \<le> n"
  shows   "qbinomial q n k = (1 - q ^ n) / (1 - q ^ k) * qbinomial q (n-1) (k-1)"
  using assms 
  by (subst (1 2) qbinomial_qfact')
      (auto simp: divide_simps of_nat_diff power_int_diff qfact_rec qbracket_eq_0_iff
                  power_0_left qbracket_def power_diff dest: power_eq_1_iff)

lemma qbinomial_rec4:
  fixes q :: "'a :: real_normed_field"
  assumes "norm q \<noteq> 1" "n > 0" "k > 0" "k \<le> n"
  shows   "qbinomial q n k = (1 - q ^ (Suc n - k)) / (1 - q ^ k) * qbinomial q n (k-1)"
proof (cases "q = 0")
  case False
  have "q ^ Suc n \<noteq> q ^ k"
  proof
    assume *: "q ^ Suc n = q ^ k"
    have "q ^ Suc n = q ^ (Suc n - k) * q ^ k"
      by (subst power_add [symmetric]) (use assms in simp)
    with * have "q ^ (Suc n - k) = 1"
      using assms False by (auto simp: power_0_left)
    thus False using assms by (auto dest: power_eq_1_iff)
  qed
  thus ?thesis
    using assms
    by (subst (1 2) qbinomial_qfact')
       (auto simp: divide_simps of_nat_diff power_int_diff qfact_rec qbracket_eq_0_iff
               power_0_left qbracket_def power_diff dest: power_eq_1_iff)
qed (use assms in \<open>auto simp: power_0_left\<close>)

lemmas qbinomial_Suc_Suc [simp del] = qbinomial.simps(3)

lemma qbinomial_Suc_Suc':
  fixes q :: "'a :: real_normed_field"
  assumes q: "norm q \<noteq> 1"
  shows "qbinomial q (Suc n) (Suc k) = 
         qbinomial q n (Suc k) + q^(n-k) * qbinomial q n k"
proof (cases "k < n")
  case True
  have "qbinomial q (Suc n) (Suc k) = qbinomial q (Suc n) (Suc (n - Suc k))"
    by (subst qbinomial_symmetric [symmetric]) (use True q in auto)
  also have "\<dots> = q ^ (n - k) * qbinomial q n (n - k) + qbinomial q n (n - Suc k)"
    by (subst qbinomial_Suc_Suc) (use True in \<open>simp_all del: power_Suc add: Suc_diff_Suc\<close>)
  also have "qbinomial q n (n - k) = qbinomial q n k"
    by (rule qbinomial_symmetric) (use q True in auto)
  also have "qbinomial q n (n - Suc k) = qbinomial q n (Suc k)"
    by (rule qbinomial_symmetric) (use q True in auto)
  finally show ?thesis by simp
qed (use assms in \<open>auto simp: qbinomial_Suc_Suc\<close>)



lemma continuous_on_qbinomial [continuous_intros]:
  fixes q :: "'a::topological_space \<Rightarrow> 'b :: real_normed_field"
  assumes [continuous_intros]: "continuous_on A q"
  shows   "continuous_on A (\<lambda>x. qbinomial (q x) m n)"
  by (induction m n rule: qbinomial_induct)
     (auto intro!: continuous_intros simp: qbinomial.simps)

lemma continuous_qbinomial [continuous_intros]:
  fixes q :: "'a::t2_space \<Rightarrow> 'b :: real_normed_field"
  assumes [continuous_intros]: "continuous F q"
  shows   "continuous F (\<lambda>x. qbinomial (q x) m n)"
  by (induction m n rule: qbinomial_induct)
     (auto intro!: continuous_intros simp: qbinomial.simps)

lemma tendsto_qbinomial [tendsto_intros]:
  fixes q :: "'a::topological_space \<Rightarrow> 'b :: real_normed_field"
  assumes [tendsto_intros]: "(q \<longlongrightarrow> Q) F"
  shows   "((\<lambda>x. qbinomial (q x) m n) \<longlongrightarrow> qbinomial Q m n) F"
  by (induction m n rule: qbinomial_induct)
     (auto intro!: tendsto_intros simp: qbinomial.simps)

lemma holomorphic_on_qbinomial [holomorphic_intros]:
  assumes [holomorphic_intros]: "q holomorphic_on A"
  shows   "(\<lambda>x. qbinomial (q x) m n) holomorphic_on A"
  by (induction m n rule: qbinomial_induct)
     (auto intro!: holomorphic_intros simp: qbinomial.simps)

lemma analytic_on_qbinomial [analytic_intros]:
  assumes [analytic_intros]: "q analytic_on A"
  shows   "(\<lambda>x. qbinomial (q x) m n) analytic_on A"
  by (induction m n rule: qbinomial_induct)
     (auto intro!: analytic_intros simp: qbinomial.simps)

lemma meromorphic_on_qbinomial [meromorphic_intros]:
  assumes [meromorphic_intros]: "q meromorphic_on A"
  shows   "(\<lambda>x. qbinomial (q x) m n) meromorphic_on A"
  by (induction m n rule: qbinomial_induct)
     (auto intro!: meromorphic_intros simp: qbinomial.simps)


subsection \<open>The Gaussian polynomials\<close>

text \<open>
  The $q$-binomial coefficient $\binom{n}{k}_q$ is a polynomial of degree $k(n-k)$ in $q$.
  These polynomials are often called the \emph{Gaussian polynomials}.
\<close>

fun gauss_poly :: "nat \<Rightarrow> nat \<Rightarrow> 'a :: comm_semiring_1 poly" where
  "gauss_poly n 0 = 1"
| "gauss_poly 0 (Suc k) = 0"
| "gauss_poly (Suc n) (Suc k) = monom 1 (Suc k) * gauss_poly n (Suc k) + gauss_poly n k"

lemma poly_gauss_poly [simp]:
  "poly (gauss_poly n k) q = qbinomial q n k"
  by (induction q n k rule: qbinomial.induct) (auto simp: poly_monom qbinomial_Suc_Suc)

lemma of_nat_coeff_gauss_poly [simp]: "of_nat (coeff (gauss_poly n k) i) = coeff (gauss_poly n k) i"
  by (induction n k arbitrary: i rule: gauss_poly.induct) (auto simp: coeff_monom_mult)

lemma of_int_coeff_gauss_poly [simp]: "of_int (coeff (gauss_poly n k) i) = coeff (gauss_poly n k) i"
  by (induction n k arbitrary: i rule: gauss_poly.induct) (auto simp: coeff_monom_mult)

lemma norm_coeff_gauss_poly [simp]: 
  "norm (coeff (gauss_poly n k) i :: 'a :: {real_normed_algebra_1, comm_semiring_1}) = 
   coeff (gauss_poly n k) i"
proof -
  have "norm (coeff (gauss_poly n k) i :: 'a) = norm (of_nat (coeff (gauss_poly n k) i) :: 'a)"
    by (subst of_nat_coeff_gauss_poly) auto
  also have "\<dots> = coeff (gauss_poly n k) i"
    by (subst norm_of_nat) auto
  finally show ?thesis .
qed  

lemmas gauss_poly_Suc_Suc [simp del] = gauss_poly.simps(3)

lemma gauss_poly_eq_0 [simp]: "k > n \<Longrightarrow> gauss_poly n k = 0"
  by (induction n k rule: gauss_poly.induct) (auto simp: gauss_poly_Suc_Suc)

lemma coeff_0_gauss_poly [simp]: "k \<le> n \<Longrightarrow> coeff (gauss_poly n k) 0 = 1"
  by (induction n k rule: gauss_poly.induct) (auto simp: gauss_poly_Suc_Suc coeff_monom_mult)

lemma gauss_poly_eq_0_iff [simp]: "gauss_poly n k = 0 \<longleftrightarrow> k > n"
proof (cases "k \<le> n")
  case True
  hence "coeff (gauss_poly n k) 0 \<noteq> coeff 0 0"
    by auto
  hence "gauss_poly n k \<noteq> 0"
    by metis
  thus ?thesis using True 
    by simp
qed auto

lemma gauss_poly_n_n [simp]: "gauss_poly n n = 1"
  by (induction n) (auto simp: gauss_poly_Suc_Suc)

lemma coeff_gauss_poly_nonneg: "coeff (gauss_poly n k :: 'a :: linordered_semidom poly) i \<ge> 0"
  by (induction n k arbitrary: i rule: gauss_poly.induct)
     (auto simp: gauss_poly_Suc_Suc coeff_monom_mult)

lemma coeff_gauss_poly_le:
  "coeff (gauss_poly n k :: 'a :: linordered_semidom poly) i \<le> of_nat (n choose k)"
proof (induction n k arbitrary: i rule: gauss_poly.induct)
  case (3 n k)
  show ?case
  proof (cases "i \<ge> Suc k")
    case True
    hence "coeff (gauss_poly (Suc n) (Suc k) :: 'a poly) i =
           coeff (gauss_poly n (Suc k)) (i - Suc k) + coeff (gauss_poly n k) i"
      by (auto simp: gauss_poly_Suc_Suc coeff_monom_mult not_less)
    also have "\<dots> \<le> of_nat (n choose Suc k) + of_nat (n choose k)"
      by (intro add_mono "3.IH")
    finally show ?thesis
      by (simp add: add_ac)
  next
    case False
    hence "coeff (gauss_poly (Suc n) (Suc k) :: 'a poly) i = coeff (gauss_poly n k) i + 0"
      by (auto simp: gauss_poly_Suc_Suc coeff_monom_mult)
    also have "\<dots> \<le> of_nat (n choose k) + of_nat (n choose Suc k)"
      by (intro add_mono "3.IH") auto
    finally show ?thesis
      by (simp add: add_ac)
  qed
qed auto

lemma degree_gauss_poly: "degree (gauss_poly n k :: 'a :: idom poly) = k * (n - k)"
proof (cases "k \<le> n")
  case True
  have "int (degree (gauss_poly n k :: 'a poly)) = int k * (int n - int k)"
    using True
  proof (induction n k rule: gauss_poly.induct)
    case (3 n k)
    note [simp] = "3.IH"
    have "int (degree (gauss_poly (Suc n) (Suc k) :: 'a poly)) =
            int (degree (monom 1 (Suc k) * gauss_poly n (Suc k) + gauss_poly n k :: 'a poly))"
      by (auto simp: gauss_poly_Suc_Suc)
    also have "\<dots> = (int k + 1) * (int n - int k)"
    proof (cases "n = k")
      case True
      thus ?thesis using 3 by auto
    next
      case False
      have "int (degree (monom (1::'a) (Suc k) * gauss_poly n (Suc k))) = 
            int (Suc k + degree (gauss_poly n (Suc k) :: 'a poly))"
        using False "3.prems" by (subst degree_mult_eq) (auto simp: degree_monom_eq)
      also have "\<dots> = (int k + 1) * (int n - int k)"
        using False "3.prems" by (simp add: algebra_simps)
      finally have deg1: "int (degree (monom (1::'a) (Suc k) * gauss_poly n (Suc k))) = 
                            (int k + 1) * (int n - int k)" .
      have "int (degree (gauss_poly n k :: 'a poly)) < 
            int (degree (monom (1::'a) (Suc k) * gauss_poly n (Suc k)))"
        using False "3.prems" by (subst deg1) (auto simp: degree_mult_eq)
      thus ?thesis
        by (subst degree_add_eq_left) (use deg1 in auto)
    qed
    finally show ?case
      by (simp add: algebra_simps)
  qed auto
  also have "\<dots> = int (k * (n - k))"
    using True by (simp add: algebra_simps of_nat_diff)
  finally show ?thesis
    by linarith
qed auto

lemma norm_qbinomial_le_binomial:
  fixes q :: "'a :: real_normed_field"
  assumes "norm q < 1"
  shows   "norm (qbinomial q n k) \<le> real (n choose k) * (1 - norm q ^ (k*(n-k)+1)) / (1 - norm q)"
proof (cases "k \<le> n")
  case True
  have "qbinomial q n k = poly (gauss_poly n k) q"
    by simp
  also have "\<dots> = (\<Sum>i\<le>k*(n-k). coeff (gauss_poly n k) i * q ^ i)"
    unfolding poly_altdef using True by (simp add: degree_gauss_poly)
  also have "norm \<dots> \<le> (\<Sum>i\<le>k*(n-k). norm (coeff (gauss_poly n k) i * q ^ i))"
    by (rule norm_sum)
  also have "\<dots> = (\<Sum>i\<le>k * (n - k). coeff (gauss_poly n k) i * norm q ^ i)"
    by (simp add: norm_mult norm_power)
  also have "\<dots> \<le> (\<Sum>i\<le>k*(n-k). (n choose k) * norm q ^ i)"
    by (intro sum_mono mult_right_mono power_mono coeff_gauss_poly_le) auto
  also have "\<dots> = (n choose k) * (\<Sum>i\<le>k * (n - k). norm q ^ i)"
    by (simp add: sum_distrib_left)
  also have "\<dots> = real (n choose k) * (1 - norm q ^ (k * (n - k) + 1)) / (1 - norm q)"
    by (subst sum_gp0) (use assms in auto)
  finally show ?thesis .
qed auto

lemma norm_qbinomial_le_binomial':
  fixes q :: "'a :: real_normed_field"
  assumes "norm q < 1"
  shows   "norm (qbinomial q n k) \<le> real (n choose k) / (1 - norm q)"
proof -
  have "norm (qbinomial q n k) \<le> real (n choose k) * (1 - norm q ^ (k*(n-k)+1)) / (1 - norm q)"
    by (rule norm_qbinomial_le_binomial) fact+
  also have "\<dots> \<le> real (n choose k) * (1 - 0) / (1 - norm q)"
    by (intro mult_left_mono divide_right_mono diff_left_mono) (use assms in auto)
  finally show ?thesis
    by simp
qed


subsection \<open>The finite Pochhammer symbol $(a; q)_n$\<close>

text \<open>
  The definition of the $q$-Pochhammer symbol is a bit less obvious. Recall that the ordinary
  Pochhamer symbol is defined as
  \[a^{\overline{n}} = a (a+1) \cdots (a+n-1)\ .\]
  The $q$-Pochhammer symbol is defined as
  \[(a; q)_n = (1 - a) (1 - aq) (1 - aq^2) \cdots (1 - aq^{n-1})\]
  for $n\geq 0$. We extend the definition to $n < 0$ such that the recurrences that hold
  for $n\geq 0$ carry over to the negative domain as well. Effectively, what we do is to define
  \[(a; q)_{-n} = \frac{1}{(aq^{-n}; q)_n}\]
\<close>

definition qpochhammer :: "int \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a :: field" where
  "qpochhammer n a q =
     (if n \<ge> 0 then (\<Prod>k<nat n. (1 - a * q ^ k)) else (\<Prod>k=1..nat (-n). 1 / (1 - a / q^k)))"

text \<open>
  Seeing in which way it is an analogue of the ``normal'' Pochhammer symbol
  $a^{\overline{n}} = a (a+1) \cdots (a+n-1)$ is more involved than for the other analogues: 
  if we simply let $q = 1$, we merely get $(1-a)^n$.

  However, we do have:
  \[\lim\limits_{q\to 1} \frac{(q^a; q)_\infty}{(1-q)^n} = a^{\overline{n}}\]
\<close>
lemma qpochhammer_tendsto_pochhammer:
  "(\<lambda>q::real. qpochhammer (int n) (q powr a) q / (1 - q) ^ n) \<midarrow>1\<rightarrow> pochhammer a n"
proof (rule Lim_transform_eventually)
  have "(\<lambda>q. \<Prod>k<n. (1 - q powr (a + int k)) / (1 - q)) \<midarrow>1\<rightarrow> (\<Prod>k<n. a + real k)"
    by (rule tendsto_prod) real_asymp
  also have "(\<Prod>k<n. a + real k) = pochhammer a n"
    by (simp add: pochhammer_prod atLeast0LessThan)
  finally show "(\<lambda>q. \<Prod>k<n. (1 - q powr (a + int k)) / (1 - q)) \<midarrow>1\<rightarrow> pochhammer a n" .
next
  have "eventually (\<lambda>q. q \<in> {0<..} - {1}) (at (1::real))"
    by (intro eventually_at_in_open) auto
  thus "eventually (\<lambda>q. (\<Prod>k<n. (1 - q powr (a + int k)) / (1 - q)) =
                        qpochhammer (int n) (q powr a) q / (1 - q) ^ n) (at 1)"
    by eventually_elim (simp add: qpochhammer_def powr_add powr_realpow prod_dividef)
qed

lemma qpochhammer_nonneg_def: "qpochhammer (int n) a q = (\<Prod>k<n. (1 - a * q ^ k))"
  by (simp add: qpochhammer_def)

lemma qpochhammer_0 [simp]: "qpochhammer 0 a q = 1"
  by (simp add: qpochhammer_def)

lemma qpochhammer_1 [simp]: "qpochhammer 1 a q = 1 - a"
  by (simp add: qpochhammer_def)

lemma qpochhammer_1_right [simp]: "qpochhammer n a 1 = (1 - a) powi n"
  by (simp add: qpochhammer_def power_int_def field_simps)

lemma qpochhammer_neg1 [simp]: "q \<noteq> 0 \<Longrightarrow> q \<noteq> a \<Longrightarrow> qpochhammer (-1) a q = q / (q - a)"
  by (simp add: qpochhammer_def divide_simps)

lemma qpochhammer_0_middle [simp]: "qpochhammer n 0 q = 1"
  by (simp add: qpochhammer_def)

lemma qpochhammer_0_right: "qpochhammer n a 0 = (if n > 0 then 1 - a else 1)"
proof (cases "n \<ge> 0")
  case False
  thus ?thesis
    by (auto simp: qpochhammer_def power_0_left)
next
  case True
  hence "qpochhammer n a 0 = (\<Prod>k<nat n. 1 - a * (if k = 0 then 1 else 0))"
    by (auto simp add: qpochhammer_def power_0_left)
  also have "\<dots> = (\<Prod>k\<in>(if n = 0 then {} else {0::nat}). 1 - a)"
    using True by (intro prod.mono_neutral_cong_right) (auto split: if_splits)
  also have "\<dots> = (if n > 0 then 1 - a else 1)"
    using True by auto
  finally show ?thesis .
qed

lemma qpochhammer_0_right_pos [simp]: "n > 0 \<Longrightarrow> qpochhammer n a 0 = 1 - a"
  and qpochhammer_0_right_nonpos [simp]: "n \<le> 0 \<Longrightarrow> qpochhammer n a 0 = 1"
  by (simp_all add: qpochhammer_0_right)

lemma qpochhammer_nat_eq_0_iff:
  "qpochhammer (int n) a q = 0 \<longleftrightarrow> (\<exists>k<n. a * q ^ k = 1)"
proof -
  have "qpochhammer (int n) a q = (\<Prod>k<n. 1 - a * q ^ k)"
    unfolding qpochhammer_def by simp
  also have "\<dots> = 0 \<longleftrightarrow> (\<exists>k<n. a * q ^ k = 1)"
    by (simp add: Bex_def)
  finally show ?thesis .
qed

lemma qpochhammer_of_real:
  "qpochhammer n (of_real a :: 'a :: real_field) (of_real q) = of_real (qpochhammer n a q)"
  by (simp add: qpochhammer_def)

lemma qpochhammer_eq_0_iff:
  "qpochhammer n a q = 0 \<longleftrightarrow> (\<exists>k\<in>{min n 0..<max n 0}. a * q powi k = 1)"
proof (cases "n \<ge> 0")
  case True
  define m where "m = nat n"
  have n_eq: "n = int m"
    using True by (auto simp: m_def)
  have "qpochhammer n a q = 0 \<longleftrightarrow> (\<exists>k\<in>{..<m}. a * q ^ k = 1)"
    by (simp add: n_eq qpochhammer_nat_eq_0_iff Bex_def)
  also have "bij_betw int {k\<in>{..<m}. a * q ^ k = 1} {k\<in>{0..<int m}. a * q powi k = 1}"
    by (rule bij_betwI[of _ _ _ nat]) (auto simp: power_int_def)
  hence "(\<exists>k\<in>{..<m}. a * q ^ k = 1) \<longleftrightarrow> (\<exists>k\<in>{0..<int m}. a * q powi k = 1)"
    by (rule bij_betw_imp_Bex_iff)
  finally show ?thesis
    by (simp add: n_eq)
next
  case False
  define m where "m = nat (-n)"
  have n_eq: "n = -int m" and "m > 0"
    using False by (auto simp: m_def)
  have "qpochhammer n a q = (\<Prod>k=1..m. 1 / (1 - a / q ^ k))"
    using \<open>m > 0\<close> by (simp add: qpochhammer_def n_eq)
  also have "\<dots> = 0 \<longleftrightarrow> (\<exists>k\<in>{1..m}. 1 / (1 - a / q ^ k) = 0)"
    by simp
  also have "\<dots> \<longleftrightarrow> (\<exists>k\<in>{1..m}. a / q ^ k = 1)"
    by (intro bex_cong) (use \<open>m > 0\<close> in auto)
  also have "bij_betw (\<lambda>k. -int k) {k\<in>{1..m}. a / q ^ k = 1} {k\<in>{-int m..<0}. a * q powi k = 1}"
    by (rule bij_betwI[of _ _ _ "\<lambda>k. nat (-k)"]) (auto simp: power_int_def field_simps)
  hence "(\<exists>k\<in>{1..m}. a / q ^ k = 1) \<longleftrightarrow> (\<exists>k\<in>{-int m..<0}. a * q powi k = 1)"
    by (rule bij_betw_imp_Bex_iff)
  finally show ?thesis
    using \<open>m > 0\<close> by (simp add: n_eq)
qed

lemma qpochhammer_rec:
  assumes "\<And>k. int k \<in> {0<..-n} \<Longrightarrow> q ^ k \<noteq> a"
  shows   "qpochhammer (n + 1) a q = qpochhammer n a q * (1 - a * q powi n)"
proof -
  consider "n \<ge> 0" | "n = -1" | "n < 0"
    by linarith
  thus ?thesis
  proof cases
    assume "n = -1"
    thus ?thesis using assms[of 1]
      by (auto simp: qpochhammer_def field_simps)
  next
    assume "n \<ge> 0"
    thus ?thesis
      by (auto simp: qpochhammer_def nat_add_distrib power_int_def)
  next
    assume n: "n < 0"
    hence "qpochhammer n a q = (\<Prod>k=1..nat (-n). 1 / (1 - a / q ^ k))"
      by (auto simp: qpochhammer_def)
    also have "{1..nat (-n)} = insert (nat (-n)) {1..nat (-n-1)}"
      using n by auto
    also have "(\<Prod>k\<in>\<dots>. 1 / (1 - a / q ^ k)) =
                 (\<Prod>k=1..nat (-n-1). 1 / (1 - a / q ^ k)) * (1 / (1 - a / q ^ nat (-n)))"
      by (subst prod.insert) auto
    also have "(\<Prod>k=1..nat (-n-1). 1 / (1 - a / q ^ k)) = qpochhammer (n + 1) a q"
      using n by (simp add: qpochhammer_def)
    also have "a / q ^ nat (-n) = a * q powi n"
      using n by (simp add: power_int_def field_simps)
    finally show ?thesis
      using assms[of "nat (-n)"] n by (auto simp: power_int_def field_simps)
  qed
qed

lemma qpochhammer_plus1:
  assumes "n \<ge> 0 \<or> x * q powi n \<noteq> 1"
  shows   "qpochhammer (n + 1) x q = qpochhammer n x q * (1 - x * q powi n)"
proof (cases "q = 0")
  case True
  thus ?thesis by (auto simp: qpochhammer_def power_0_left power_int_def nat_add_distrib)
next
  case [simp]: False
  consider "n < -1" | "n = -1" | "n \<ge> 0"
    by linarith
  thus ?thesis
  proof cases
    assume "n < -1"
    define m where "m = nat (-n-1)"
    have n_eq: "n = -int m-1" and "m > 0"
      using \<open>n < -1\<close> by (simp_all add: m_def)
    show ?thesis using \<open>m > 0\<close> assms
      by (simp add: n_eq qpochhammer_def power_int_diff power_int_minus 
                    nat_add_distrib divide_simps mult_ac)
  next
    assume [simp]: "n = -1"
    show ?thesis using assms
      by (simp add: qpochhammer_def divide_simps)
  next
    assume "n \<ge> 0"
    define m where "m = nat n"
    have n_eq: "n = int m"
      using \<open>n \<ge> 0\<close> by (simp add: m_def)
    show ?thesis using assms
      by (simp add: n_eq qpochhammer_def nat_add_distrib)
  qed
qed

lemma qpochhammer_minus1:
  assumes "x * q powi (n - 1) \<noteq> 1"
  shows   "qpochhammer (n - 1) x q = qpochhammer n x q / (1 - x * q powi (n - 1))"
  using qpochhammer_plus1[of "n - 1" x q] assms by simp

lemma qpochhammer_1plus:
  assumes "n \<ge> 0 \<or> x * q powi n \<noteq> 1"
  shows   "qpochhammer (1 + n) x q = qpochhammer n x q * (1 - x * q powi n)"
  using qpochhammer_plus1[OF assms] by (simp add: add_ac)

lemma qpochhammer_nat_add:
  fixes m n :: nat
  shows "qpochhammer (int m + int n) x q = qpochhammer (int m) x q * qpochhammer n (q ^ m * x) q"
proof -
  have "qpochhammer (int m + int n) x q = (\<Prod>k<m+n. 1 - x * q ^ k)"
    by (simp add: qpochhammer_def nat_add_distrib)
  also have "\<dots> = (\<Prod>k\<in>{..<m}\<union>{m..<m+n}. 1 - x * q ^ k)"
    by (intro prod.cong refl) auto
  also have "\<dots> = (\<Prod>k<m. 1 - x * q ^ k) * (\<Prod>k=m..<m+n. 1 - x * q ^ k)"
    by (subst prod.union_disjoint) auto
  also have "(\<Prod>k<m. 1 - x * q ^ k) = qpochhammer m x q"
    by (simp add: qpochhammer_def)
  also have "(\<Prod>k=m..<m+n. 1 - x * q ^ k) = (\<Prod>k<n. 1 - x * q ^ m * q ^ k)"
    by (intro prod.reindex_bij_witness[of _ "\<lambda>k. k + m" "\<lambda>k. k - m"]) (auto simp flip: power_add)
  also have "\<dots> = qpochhammer n (q ^ m * x) q"
    by (simp add: qpochhammer_def mult_ac)
  finally show ?thesis .
qed

lemma qpochhammer_minus: 
  assumes "n < 0 \<longrightarrow> q \<noteq> 0"
  shows   "qpochhammer (-n) a q = 1 / qpochhammer n (a / q powi n) q"
proof (cases "q = 0")
  case [simp]: True
  from assms have "n \<ge> 0"
    by auto
  thus ?thesis                  
    by (simp add: power_int_0_left_if)
next
  case [simp]: False

  show ?thesis
  proof (cases n "0::int" rule: linorder_cases)
    case n: less
    define m where "m = nat (-n)"
    have n_eq: "n = -int m"
      using n by (simp add: m_def)
    have "1 / qpochhammer n (a / q powi n) q =
            (\<Prod>k=1..m. 1 - a / (q ^ k / q ^ m))"
      by (simp add: qpochhammer_def prod_dividef n_eq power_int_minus inverse_eq_divide)
    also have "\<dots> = (\<Prod>k<m. 1 - a * q ^ k)"
      by (rule prod.reindex_bij_witness[of _ "\<lambda>i. m - i" "\<lambda>i. m -i"]) 
         (auto simp: power_diff)
    also have "\<dots> = qpochhammer (-n) a q"
      by (simp add: qpochhammer_def n_eq)
    finally show ?thesis ..
  next
    case n: greater
    define m where "m = nat n"
    have n_eq: "n = int m" and "m > 0"
      using n by (simp_all add: m_def)
    have "qpochhammer (-n) a q = 1 / (\<Prod>k=1..m. 1 - a / q ^ k)"
      using \<open>m > 0\<close> by (simp add: qpochhammer_def prod_dividef n_eq)
    also have "(\<Prod>k=1..m. 1 - a / q ^ k) = (\<Prod>k<m. 1 - a * q ^ k / q ^ m)"
      by (rule prod.reindex_bij_witness[of _ "\<lambda>i. m - i" "\<lambda>i. m -i"]) 
         (auto simp: power_diff)
    also have "1 / \<dots> = 1 / qpochhammer n (a / q powi n) q"
      by (simp add: qpochhammer_def n_eq)
    finally show ?thesis .
  qed auto
qed

lemma qpochhammer_add:
  assumes "\<And>k. k \<in> {m+min n 0..<m+max n 0} \<Longrightarrow> x * q powi k \<noteq> 1" and [simp]: "q \<noteq> 0"
  shows   "qpochhammer (m + n) x q = qpochhammer m x q * qpochhammer n (q powi m * x) q"
proof -
  have *: "qpochhammer (m + int n) x q = qpochhammer m x q * qpochhammer (int n) (q powi m * x) q"
    if "\<forall>k<n. x * q powi (m + k) \<noteq> 1" for n :: nat and m :: int
    using that by (induction n) (auto simp: qpochhammer_1plus add_ac power_int_add)

  show ?thesis
  proof (cases "n \<ge> 0")
    case True
    define n' where "n' = nat n"
    have n_eq: "n = int n'"
      using True by (simp add: n'_def)
    show ?thesis
      using *[of n' m] assms by (auto simp: n_eq)
  next
    case False
    define n' where "n' = nat (-n)"
    have n_eq: "n = -int n'" and n': "n' > 0"
      using False by (simp_all add: n'_def)
    have "qpochhammer m x q = qpochhammer (m + n + int n') x q"
      by (simp add: n_eq)
    also have "\<dots> = qpochhammer (m + n) x q * qpochhammer (-n) (q powi (m + n) * x) q"
      by (subst *) (use assms in \<open>auto simp: n_eq\<close>)
    also have "\<dots> = qpochhammer (m + n) x q / qpochhammer n (q powi m * x) q"
      by (subst qpochhammer_minus) (use False in \<open>auto simp: power_int_add\<close>)
    finally have "qpochhammer m x q = qpochhammer (m + n) x q / qpochhammer n (q powi m  * x) q" .
    moreover have "qpochhammer n (q powi m * x) q \<noteq> 0"
    proof
      assume "qpochhammer n (q powi m * x) q = 0"
      then obtain k where k: "k \<in> {-int n'..<0}" "x * q powi (m + k) = 1"
        using n' by (auto simp: n_eq qpochhammer_eq_0_iff power_int_add mult_ac)
      moreover from k(1) have "m + k \<in> {m+min n 0..<m+max n 0}"
        using n' by (auto simp: n_eq)
      ultimately show False
        using k(2) assms by blast
    qed
    ultimately show ?thesis
      by (simp add: divide_simps power_int_add)
  qed
qed

lemma qfact_conv_qpochhammer_aux:
  assumes "n < 0 \<longrightarrow> q \<noteq> 0"
  shows   "qpochhammer n q q = qfact q n * (1 - q) powi n"
proof (cases "q = 1")
  case q: False
  show ?thesis
  proof (cases "n \<ge> 0")
    case True
    thus ?thesis
    proof (induction n rule: int_ge_induct)
      case base
      thus ?case by auto
    next
      case (step n)
      thus ?case using q
        by (subst qpochhammer_rec)
           (auto simp: qfact_plus1 power_int_diff qbracket_def power_int_add add_eq_0_iff2)
    qed
  qed (use assms in \<open>auto simp: qpochhammer_def not_le intro: bexI[of _ 1]\<close>)
qed (use assms in \<open>auto simp: qpochhammer_def power_0_left qfact_def not_less\<close>)

lemma qfact_conv_qpochhammer:
  assumes "if n \<ge> 0 then q \<noteq> 1 else q \<noteq> 0"
  shows   "qfact q n = qpochhammer n q q * (1 - q) powi (-n)"
  using qfact_conv_qpochhammer_aux[of n q] assms
  by (auto simp: power_int_minus divide_simps split: if_splits)

lemma qbinomial_conv_qpochhammer:
  fixes q :: "'a :: field_char_0"
  assumes "k \<le> n"
  assumes "\<And>k. 0 < k \<Longrightarrow> k \<le> n \<Longrightarrow> q ^ k \<noteq> 1"
  shows "qbinomial q n k = 
           qpochhammer (int n) q q / (qpochhammer (int k) q q * qpochhammer (int n - int k) q q)"
proof (cases "n = 0")
  case False
  with assms(2)[of 1] have [simp]: "q \<noteq> 1"
    by auto
  define P where "P = (\<lambda>n. qpochhammer (int n) q q)"
  have "qbinomial q n k = qfact q (int n) / (qfact q (int k) * qfact q (int n - int k))"
    using assms by (subst qbinomial_qfact) (use assms in auto)
  also have "\<dots> = P n / (P k * P (n - k))"
    by (subst (1 2 3) qfact_conv_qpochhammer)
       (use \<open>k \<le> n\<close> in \<open>auto simp: power_int_minus power_int_diff field_simps P_def of_nat_diff\<close>)
  finally show ?thesis
    using assms(1) by (simp add: P_def of_nat_diff)
qed (use assms(1) in auto)

lemma norm_qpochhammer_nonneg_le:
  fixes a q :: "'a::{real_normed_field}"
  assumes "norm q \<le> 1"
  shows   "norm (qpochhammer (int n) a q) \<le> (1 + norm a) ^ n"
proof -
  have "norm (qpochhammer (int n) a q) = (\<Prod>x<n. norm (1 - a * q ^ x))"
    by (simp add: qpochhammer_nonneg_def flip: prod_norm)
  also have "\<dots> \<le> (\<Prod>x<n. norm (1::'a) + norm (a * q ^ x))"
    by (intro prod_mono conjI norm_ge_zero) norm
  also have "\<dots> = (\<Prod>k<n. norm (1::'a) + norm a * norm q ^ k)"
    by (simp add: norm_power norm_mult)
  also have "\<dots> \<le> (\<Prod>k<n. norm (1::'a) + norm a * norm q ^ 0)"
    by (intro prod_mono add_mono mult_left_mono power_decreasing conjI) (use assms in auto)
  finally show ?thesis
    by simp
qed

lemma norm_qpochhammer_nonneg_ge:
  fixes a q :: "'a::{real_normed_field}"
  assumes "norm q \<le> 1" "norm a \<le> 1"
  shows   "norm (qpochhammer (int n) a q) \<ge> (1 - norm a) ^ n"
proof -
  have "(\<Prod>k<n. norm (1::'a) - norm a * norm q ^ 0) \<le>
        (\<Prod>k<n. norm (1::'a) - norm a * norm q ^ k)"
    by (intro prod_mono diff_mono mult_left_mono power_decreasing conjI) (use assms in auto)
  also have "\<dots> \<le> (\<Prod>k<n. norm (1::'a) - norm (a * q ^ k))"
    by (simp add: norm_power norm_mult)
  also have "\<dots> \<le> (\<Prod>k<n. norm (1 - a * q ^ k))"
  proof (intro prod_mono conjI) 
    fix i :: nat
    show "norm (1::'a) - norm (a * q ^ i) \<le> norm (1 - a * q ^ i)"
      by norm
    have "norm a * norm q ^ i \<le> 1 * 1 ^ i"
      using assms by (intro mult_mono power_mono) auto
    thus "norm (1::'a) - norm (a * q ^ i) \<ge> 0"
      by (simp add: norm_power norm_mult)
  qed
  also have "\<dots> = norm (qpochhammer (int n) a q)"
    by (simp add: qpochhammer_nonneg_def flip: prod_norm)
  finally show ?thesis 
    by simp
qed

lemma qpochhammer_nonneg_nonzero:
  fixes q :: "'a :: real_normed_field"
  assumes "norm q < 1" "norm a < 1"
  shows   "qpochhammer (int k) a q \<noteq> 0"
proof -
  have "0 < (1 - norm a) ^ k"
    using assms by simp
  also have "(1 - norm a) ^ k \<le> norm (qpochhammer (int k) a q)"
    by (rule norm_qpochhammer_nonneg_ge) (use assms in auto)
  finally show ?thesis
    by auto
qed

lemma qbinomial_conv_qpochhammer':
  fixes q :: "'a :: {real_normed_field}"
  assumes "norm q < 1" "k \<le> n"
  shows   "qbinomial q n k = qpochhammer (int k) (q ^ (n + 1 - k)) q / qpochhammer (int k) q q"
proof -
  have eq: "qpochhammer (int n) q q =
               qpochhammer (int k) (q ^ Suc (n - k)) q * qpochhammer (int (n - k)) q q"
    using qpochhammer_nat_add[of "n - k" k q q] assms by (simp add: of_nat_diff mult_ac)
  have [simp]: "q ^ k \<noteq> 1" if "k > 0" for k
    using assms by (simp add: q_power_neq_1 that)
  have "qbinomial q n k = (qpochhammer (int n) q q / qpochhammer (int n - int k) q q) / (qpochhammer (int k) q q)"
    by (subst qbinomial_conv_qpochhammer) (use assms in \<open>auto simp: field_simps\<close>)
  also have "\<dots> = qpochhammer (int k) (q ^ (n + 1 - k)) q / qpochhammer (int k) q q"
    unfolding eq using assms
    by (auto simp add: qpochhammer_nonneg_nonzero Suc_diff_le simp flip: of_nat_diff)
  finally show ?thesis .
qed

lemma norm_qbinomial_le:
  fixes a q :: "'a::{real_normed_field}"
  assumes "norm q < 1"
  shows   "norm (qbinomial q n k) \<le> ((1 + norm q) / (1 - norm q)) ^ k"
proof (cases "k \<le> n")
  case True
  have [simp]: "q ^ k \<noteq> 1" if "k > 0" for k
    using assms(1) q_power_neq_1 that by blast
  have "norm (qbinomial q n k) = 
          norm (qpochhammer (int k) (q ^ (Suc n - k)) q) / norm (qpochhammer (int k) q q)"
    by (subst qbinomial_conv_qpochhammer')
       (use assms True in \<open>auto simp: norm_divide norm_mult of_nat_diff\<close>)
  also have "\<dots> \<le> (1 + norm (q ^ (Suc n - k))) ^ k / (1 - norm q) ^ k"
    by (intro frac_le mult_mono norm_qpochhammer_nonneg_le
              norm_qpochhammer_nonneg_ge mult_pos_pos)
       (use assms in auto)
  also have "\<dots> \<le> (1 + norm q ^ 1) ^ k / (1 - norm q) ^ k"
    unfolding norm_power
    by (intro divide_right_mono power_mono add_left_mono power_decreasing)
       (use assms True in auto)
  also have "\<dots> = ((1 + norm q) / (1 - norm q)) ^ k"
    using assms by (simp add: power_divide True flip: power_add)
  finally show ?thesis .
qed (use assms in auto)

lemma norm_qbinomial_ge:
  fixes a q :: "'a::{real_normed_field}"
  assumes "norm q < 1" "k \<le> n"
  shows   "norm (qbinomial q n k) \<ge> ((1 - norm q) / (1 + norm q)) ^ k"
proof -
  have not_one: "q ^ k \<noteq> 1" if "k > 0" for k
    using assms(1) q_power_neq_1 that by blast
  have [simp]: "qpochhammer (int i) q q \<noteq> 0" for i
  proof
    assume "qpochhammer (int i) q q = 0"
    then obtain k where "q * q powi k = 1" "k \<ge> 0"
      by (subst (asm) qpochhammer_eq_0_iff) auto
    hence "q ^ Suc (nat k) = 1"
      by (cases k) auto
    thus False
      using not_one[of "Suc (nat k)"] by simp
  qed

  have "((1 - norm q) / (1 + norm q)) ^ k = (1 - norm q ^ 1) ^ k / (1 + norm q) ^ k"
    using assms by (simp add: power_divide flip: power_add)
  also have "\<dots> \<le> (1 - norm (q ^ (Suc n - k))) ^ k / (1 + norm q) ^ k"
    unfolding norm_power
    by (intro divide_right_mono diff_left_mono power_mono power_decreasing)
       (use assms in auto)
  also have "\<dots> \<le> norm (qpochhammer (int k) (q ^ (Suc n - k)) q) / norm (qpochhammer (int k) q q)"
    by (intro frac_le mult_mono norm_qpochhammer_nonneg_le
              norm_qpochhammer_nonneg_ge mult_pos_pos)
       (use assms in \<open>auto simp: norm_power power_le_one_iff\<close>)
  also have "\<dots> = norm (qbinomial q n k)"
    by (subst qbinomial_conv_qpochhammer')
       (use assms in \<open>auto simp: norm_divide norm_mult of_nat_diff not_one\<close>)
  finally show ?thesis .
qed

lemma norm_qpochhammer_nonneg_le_qpochhammer:
  fixes q :: "'a :: real_normed_field"
  shows   "norm (qpochhammer (int k) a q) \<le> qpochhammer (int k) (-norm a) (norm q)"
proof -
  have "norm (qpochhammer (int k) a q) = (\<Prod>i<k. norm (1 - a * q ^ i))"
    by (simp add: qpochhammer_nonneg_def prod_norm)
  also have "\<dots> \<le> (\<Prod>i<k. norm (1::'a) + norm (a * q ^ i))"
    by (intro prod_mono conjI norm_ge_zero) norm
  also have "\<dots> = qpochhammer (int k) (-norm a) (norm q)"
    by (simp add: qpochhammer_nonneg_def norm_mult norm_power)
  finally show ?thesis .
qed

lemma norm_qpochhammer_nonneg_ge_qpochhammer:
  fixes q :: "'a :: real_normed_field"
  assumes "norm q \<le> 1" "norm a \<le> 1"
  shows   "norm (qpochhammer (int k) a q) \<ge> qpochhammer (int k) (norm a) (norm q)"
proof -
  have "qpochhammer (int k) (norm a) (norm q) = (\<Prod>i<k. norm (1::'a) - norm (a * q ^ i))"
    by (simp add: qpochhammer_nonneg_def norm_mult norm_power)
  also have "\<dots> \<le> (\<Prod>i<k. norm (1 - a * q ^ i))"
  proof (intro prod_mono conjI norm_ge_zero)
    fix i assume i: "i \<in> {..<k}"
    have "norm a * norm q ^ i \<le> 1 * 1 ^ i"
      by (intro mult_mono power_mono) (use assms in auto)
    thus "0 \<le> norm (1::'a) - norm (a * q ^ i)"
      by (auto simp: norm_mult norm_power)
  qed norm
  also have "\<dots> = norm (qpochhammer (int k) a q)"
    by (simp add: qpochhammer_nonneg_def prod_norm)
  finally show ?thesis .
qed

lemma qpochhammer_nonneg: 
  assumes "a \<le> 1" "0 \<le> q" "q \<le> 1"
  shows   "qpochhammer (int n) a (q::real) \<ge> 0"
proof -
  have "a * q ^ i \<le> 1" for i
  proof -
    have "a * q ^ i \<le> 1 * 1 ^ i"
      by (intro mult_mono power_mono) (use assms in auto)
    thus ?thesis
      by simp
  qed
  thus ?thesis
    unfolding qpochhammer_nonneg_def by (intro prod_nonneg) auto
qed

lemma qpochhammer_pos: 
  assumes "a < 1" "0 \<le> q" "q \<le> 1"
  shows   "qpochhammer (int n) a (q::real) > 0"
proof -
  have "a * q ^ i < 1" for i
  proof (cases "a \<ge> 0")
    case True
    have "a * q ^ i \<le> a * 1 ^ i"
      by (intro mult_left_mono power_mono) (use assms True in auto)
    thus ?thesis
      using assms by auto
  next
    case False
    hence "a * q ^ i \<le> 0"
      by (intro mult_nonpos_nonneg) (use assms in auto)
    also have "\<dots> < 1"
      by simp
    finally show ?thesis
      by simp
  qed
  thus ?thesis
    unfolding qpochhammer_nonneg_def by (intro prod_pos) auto
qed


lemma holomorphic_qpochhammer [holomorphic_intros]:
  fixes f g :: "complex \<Rightarrow> complex"
  assumes [holomorphic_intros]: "f holomorphic_on A" "g holomorphic_on A"
  assumes "\<And>x k. x \<in> A \<Longrightarrow> int k \<in> {0<..-n} \<Longrightarrow> f x ^ k \<noteq> g x" "\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 0"
  shows   "(\<lambda>x. qpochhammer n (g x) (f x)) holomorphic_on A"
  unfolding qpochhammer_def using assms(3,4)
  by (cases "n \<ge> 0")
     (force intro!: holomorphic_intros simp: Suc_le_eq not_le eq_commute[of _ "g x" for x])+

lemma analytic_qpochhammer [analytic_intros]:
  fixes f g :: "complex \<Rightarrow> complex"
  assumes [analytic_intros]: "f analytic_on A" "g analytic_on A"
  assumes "\<And>x k. x \<in> A \<Longrightarrow> int k \<in> {0<..-n} \<Longrightarrow> f x ^ k \<noteq> g x" "\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 0"
  shows   "(\<lambda>x. qpochhammer n (g x) (f x)) analytic_on A"
  unfolding qpochhammer_def using assms(3,4)
  by (cases "n \<ge> 0")
     (force intro!: analytic_intros simp: Suc_le_eq not_le eq_commute[of _ "g x" for x])+

lemma meromorphic_qpochhammer [meromorphic_intros]:
  fixes f g :: "complex \<Rightarrow> complex"
  assumes [meromorphic_intros]: "f meromorphic_on A" "g meromorphic_on A"
  shows   "(\<lambda>x. qpochhammer n (g x) (f x)) meromorphic_on A"
  unfolding qpochhammer_def by (cases "n \<ge> 0") (auto intro!: meromorphic_intros)

lemma continuous_on_qpochhammer [continuous_intros]:
  fixes f g :: "'a :: topological_space \<Rightarrow> 'b :: {real_normed_field}"
  assumes [continuous_intros]: "continuous_on A f" "continuous_on A g"
  assumes "\<And>x k. x \<in> A \<Longrightarrow> int k \<in> {0<..-n} \<Longrightarrow> f x ^ k \<noteq> g x" "\<And>x. x \<in> A \<Longrightarrow> f x \<noteq> 0"
  shows   "continuous_on A (\<lambda>x. qpochhammer n (g x) (f x))"
  unfolding qpochhammer_def using assms(3,4)
  by (cases "n \<ge> 0")
     (force intro!: continuous_intros simp: Suc_le_eq not_le eq_commute[of _ "g x" for x])+

lemma continuous_qpochhammer [continuous_intros]:
  fixes f g :: "'a :: t2_space \<Rightarrow> 'b :: {real_normed_field}"
  assumes [continuous_intros]: "continuous (at x within A) f" "continuous (at x within A) g"
  assumes "\<And>k. int k \<in> {0<..-n} \<Longrightarrow> f x ^ k \<noteq> g x" "f x \<noteq> 0"
  shows   "continuous (at x within A) (\<lambda>x. qpochhammer n (g x) (f x))"
  unfolding qpochhammer_def using assms(3,4)
  by (cases "n \<ge> 0")
     (force intro!: continuous_intros simp: Suc_le_eq not_le eq_commute[of _ "g x" for x])+

lemma tendsto_qpochhammer [tendsto_intros]:
  fixes f g :: "'a \<Rightarrow> 'b :: {real_normed_field}"
  assumes [tendsto_intros]: "(f \<longlongrightarrow> q) F" "(g \<longlongrightarrow> a) F"
  assumes "\<And>k. int k \<in> {0<..-n} \<Longrightarrow> q ^ k \<noteq> a" "q \<noteq> 0"
  shows   "((\<lambda>x. qpochhammer n (g x) (f x)) \<longlongrightarrow> qpochhammer n a q) F"
proof (cases "n \<ge> 0")
  case True
  have "((\<lambda>x. \<Prod>k<nat n. 1 - g x * f x ^ k) \<longlongrightarrow> (\<Prod>k<nat n. 1 - a * q ^ k)) F"
    by (intro tendsto_intros)
  thus ?thesis
    using True by (simp add: qpochhammer_def [abs_def])
next
  case False
  have " ((\<lambda>x. \<Prod>k=1..nat (- n). 1 / (1 - g x / f x ^ k)) \<longlongrightarrow>
            (\<Prod>k=1..nat (- n). 1 / (1 - a / q ^ k))) F"
    by (intro tendsto_intros; use assms False in \<open>force simp: Suc_le_eq\<close>)
  thus ?thesis
    using False by (simp add: qpochhammer_def [abs_def])
qed

end