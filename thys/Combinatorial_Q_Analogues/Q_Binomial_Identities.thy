section \<open>$q$-binomial identities\<close>
theory Q_Binomial_Identities
  imports Q_Pochhammer_Infinite
begin

subsection \<open>The $q$-binomial theorem\<close>

text \<open>
  Recall the binomial theorem:
  \[(1 + t)^n = \sum_{k=0}^n \binom{n}{k} t^n\]
  The $q$-binomial numbers satisfy an analogous theorem:
  \[\prod_{k=0}^{n-1} \big(1 + t q^k\big) = \sum_{k=0}^n q^{k(k-1)/2} \binom{n}{k}_{\!\!q} t^k\]
  It can be seen easily that letting $q\to 1$ would give us the ``normal'' binomial theorem.
\<close>
theorem qbinomial_theorem:
  "qpochhammer (int n) (-t) q = (\<Sum>k\<le>n. qbinomial q n k * q ^ (k choose 2) * t ^ k)"
proof (induction n arbitrary: t)
  case (Suc n)
  have *: "{..Suc n} = insert 0 {1..Suc n}"
    by auto
  have "(\<Sum>k\<le>Suc n. qbinomial q (Suc n) k * q ^ (k choose 2) * t ^ k) =
        1 + (\<Sum>k=1..Suc n. qbinomial q (Suc n) k * q ^ (k choose 2) * t ^ k)"
    unfolding * by (subst sum.insert) (auto simp: binomial_eq_0)
  also have "(\<Sum>k=1..Suc n. qbinomial q (Suc n) k * q ^ (k choose 2) * t ^ k) =
             (\<Sum>k\<le>n. q ^ (Suc k choose 2) * qbinomial q (Suc n) (Suc k) * t ^ Suc k)"
    by (intro sum.reindex_bij_witness[of _ "Suc" "\<lambda>k. k - 1"]) auto
  also have "\<dots> = (\<Sum>k\<le>n. q ^ (Suc (Suc k) choose 2) * qbinomial q n (Suc k) * t ^ Suc k) +
                  (\<Sum>k\<le>n. q ^ (Suc k choose 2) * qbinomial q n k * t ^ Suc k)"
    by (simp add: qbinomial_Suc_Suc ring_distribs sum.distrib power_add mult_ac numeral_2_eq_2)
  also have "(\<Sum>k\<le>n. q ^ (Suc (Suc k) choose 2) * qbinomial q n (Suc k) * t ^ Suc k) =
             (\<Sum>k=1..Suc n. q ^ (Suc k choose 2) * qbinomial q n k * t ^ k)"
    by (intro sum.reindex_bij_witness[of _ "\<lambda>k. k - 1" "Suc"]) auto
  also have "\<dots> = (\<Sum>k\<in>insert 0 {1..Suc n}. q ^ (Suc k choose 2) * qbinomial q n k * t ^ k) - 1"
    by (subst sum.insert) (auto simp: numeral_2_eq_2)
  also have "(\<Sum>k\<in>insert 0 {1..Suc n}. q ^ (Suc k choose 2) * qbinomial q n k * t ^ k) 
           = (\<Sum>k\<le>n. q ^ (Suc k choose 2) * qbinomial q n k * t ^ k)"
    by (intro sum.mono_neutral_right) auto
  also have "1 + ((\<Sum>k\<le>n. q ^ (Suc k choose 2) * qbinomial q n k * t ^ k) -
               1 + (\<Sum>k\<le>n. q ^ (Suc k choose 2) * qbinomial q n k * t ^ Suc k)) =
             (\<Sum>k\<le>n. q ^ (Suc k choose 2) * qbinomial q n k * (t ^ Suc k + t ^ k))"
    unfolding ring_distribs sum.distrib by simp
  also have "\<dots> = (\<Sum>k\<le>n. qbinomial q n k * q ^ (k choose 2) * (q * t)^k) * (1 + t)"
    by (simp add: sum_distrib_left sum_distrib_right algebra_simps numeral_2_eq_2 power_add)
  also have "\<dots> = qpochhammer (int n) (-q * t) q  * (1 + t)"
    by (subst Suc.IH [symmetric]) (simp_all add: algebra_simps)
  also have "qpochhammer (int n) (-q * t) q = (\<Prod>k<n. 1 + t * q ^ Suc k)"
    by (simp add: qpochhammer_def mult_ac)
  also have "\<dots> = (\<Prod>k=1..<Suc n. 1 + t * q ^ k)"
    by (intro prod.reindex_bij_witness[of _ "\<lambda>k. k - 1" Suc]) auto
  also have "\<dots> * (1 + t) = (\<Prod>k\<in>insert 0 {1..<Suc n}. 1 + t * q ^ k)"
    by (subst prod.insert) auto
  also have "insert 0 {1..<Suc n} = {..<Suc n}"
    by auto
  also have "(\<Prod>k<Suc n. 1 + t * q ^ k) = qpochhammer (int (Suc n)) (- t) q"
    unfolding qpochhammer_def by (subst nat_int) auto
  finally show ?case ..
qed (auto simp: binomial_eq_0)

lemma qbinomial_theorem':
  "qpochhammer (int n) t q = (\<Sum>k\<le>n. qbinomial q n k * q ^ (k choose 2) * (-t) ^ k)"
  using qbinomial_theorem[of n "-t" q] by simp


subsection \<open>The infinite $q$-binomial theorem\<close>

text \<open>
  Taking the limit $n \to \infty$ in the $q$-binomial theorem and interchanging the limits
  with Tannery's Theorem, we obtain, for any $q$ with $|q| < 1$:
  \[\sum_{k=0}^\infty \frac{t^k q^{k(k-1)/2}}{[k]_q! (1-q)^k} =
    \prod_{k=0}^\infty \big(1+ tq^k\big) = (-t; q)_\infty\]
\<close>
theorem qbinomial_theorem_inf:
  fixes q t :: "'a :: {real_normed_field, banach, heine_borel}"
  assumes q: "q \<in> ball 0 1"
  defines "S \<equiv> (\<lambda>k. (q ^ (k choose 2) * t ^ k) / (qfact q (int k) * (1 - q) ^ k))"
  shows   "summable (\<lambda>k. norm (S k))" and "(\<Sum>k. S k) = qpochhammer_inf (-t) q"
proof -
  have q': "norm q < 1"
    using q by auto
  from q have [simp]: "q \<noteq> 1"
    by auto
  have "(\<lambda>n. qpochhammer (int n) (-t) q) \<longlonglongrightarrow> qpochhammer_inf (-t) q"
    by (rule qpochhammer_tendsto_qpochhammer_inf) (use q in auto)
  also have "(\<lambda>n. qpochhammer (int n) (-t) q) = (\<lambda>n. (\<Sum>k\<le>n. qbinomial q n k * q ^ (k choose 2) * t ^ k))"
    by (simp only: qbinomial_theorem)
  finally have "(\<lambda>n. \<Sum>k\<le>n. q ^ (k choose 2) * qbinomial q n k * t ^ k)
                   \<longlonglongrightarrow> qpochhammer_inf (- t) q" by (simp only: mult_ac)
  also have "(\<lambda>n. \<Sum>k\<le>n. q ^ (k choose 2) * qbinomial q n k * t ^ k) = 
             (\<lambda>n. \<Sum>k\<le>n. qfact q n / qfact q (n - k) * (q ^ (k choose 2) * t ^ k / qfact q k))"
    by (intro ext sum.cong refl, subst qbinomial_qfact') (use q in \<open>auto simp: field_simps\<close>)
  also have "\<dots> = (\<lambda>n. \<Sum>k\<le>n. (\<Prod>i<k. qbracket q (n - int i)) * (q ^ (k choose 2) * t ^ k / qfact q k))"
  proof (intro ext sum.cong refl, goal_cases)
    case (1 n k)
    have "(\<Prod>i<k. qbracket q (n - int i)) = (\<Prod>i\<in>{n-k<..n}. qbracket q (int i))"
      by (rule prod.reindex_bij_witness[of _ "\<lambda>i. n - i" "\<lambda>i. n - i"]) (use 1 in \<open>auto simp: of_nat_diff\<close>)
    also have "\<dots> = (\<Prod>i\<in>{1..n}-{1..n-k}. qbracket q (int i))"
      by (intro prod.cong refl) auto
    also have "\<dots> = qfact q n / qfact q (n - k)"
      using q by (subst prod_diff) (auto simp: qbracket_def qfact_int_def dest: power_eq_1_iff)
    finally show ?case
      using 1 by (simp add: of_nat_diff)
  qed
  also have "\<dots> = (\<lambda>n. \<Sum>k\<le>n. (\<Prod>i<k. 1 - q ^ (n - i)) * S k)"
    by (simp add: qbracket_def prod_dividef mult_ac S_def flip: of_nat_diff)
  finally have lim1: "(\<lambda>n. \<Sum>k\<le>n. (\<Prod>i<k. 1 - q ^ (n - i)) * S k) \<longlonglongrightarrow> qpochhammer_inf (- t) q" .

  define g where "g = (\<lambda>k. 2 ^ k * (norm q ^ (k choose 2) * norm t ^ k / (1 - norm q) ^ k))"
  have g_altdef: "g k = 2 ^ k * norm q powr (k * (k - 1) / 2) * norm t ^ k / (1 - norm q) ^ k" 
    if [simp]: "q \<noteq> 0" for k
  proof -
    have "norm q ^ (k choose 2) = norm q powr real (k choose 2)"
      by (auto simp: powr_realpow)
    also have "real (k choose 2) = real k * (real k - 1) / 2"
      unfolding choose_two by (subst real_of_nat_div) (auto simp: )
    finally show ?thesis
      by (simp add: g_def)
  qed

  have lim2: "eventually (\<lambda>n. summable (\<lambda>k. norm ((\<Prod>i<k. 1 - q ^ (n - i)) * S k))) at_top \<and>
              summable (\<lambda>n. norm (S n)) \<and>
              (\<lambda>n. \<Sum>k. (\<Prod>i<k. 1 - q ^ (n - i)) * S k) \<longlonglongrightarrow> suminf S"
  proof (rule tannerys_theorem)
    show "(\<lambda>n. (\<Prod>i<k. 1 - q ^ (n - i)) * S k) \<longlonglongrightarrow> S k" for k
      by (rule tendsto_eq_intros tendsto_power_zero filterlim_minus_const_nat_at_top refl q')+ simp
  next
    show "\<forall>\<^sub>F (k, n) in at_top \<times>\<^sub>F at_top. norm ((\<Prod>i<k. 1 - q ^ (n - i)) * S k) \<le> g k"
    proof (intro always_eventually, safe)
      fix k n :: nat
      have "norm ((\<Prod>i<k. 1 - q ^ (n - i)) * S k) = (\<Prod>i<k. norm (1 - q ^ (n - i))) * norm (S k)"
        by (simp add: norm_mult flip: prod_norm)
      also have "\<dots> \<le> 2 ^ k * (norm q ^ (k choose 2) * norm t ^ k / (1 - norm q) ^ k)"
      proof (rule mult_mono)
        have "(\<Prod>i<k. norm (1 - q ^ (n - i))) \<le> (\<Prod>i<k. 2)"
        proof (intro prod_mono conjI)
          fix i :: nat assume i: "i \<in> {..<k}"
          have "norm (1 - q ^ (n - i)) \<le> norm (1 :: 'a) + norm (q ^ (n - i))"
            by norm
          also have "norm (q ^ (n - i)) \<le> norm (q ^ 0)"
            using q i unfolding norm_power by (intro power_decreasing) auto
          finally show "norm (1 - q ^ (n - i)) \<le> 2"
            by simp
        qed auto
        thus "(\<Prod>i<k. norm (1 - q ^ (n - i))) \<le> 2 ^ k"
          by simp
      next
        have "norm (S k) = norm q ^ (k choose 2) * norm t ^ k / (norm (qfact q (int k) * (1 - q) ^ k))"
          by (simp add: S_def norm_divide norm_mult norm_power)
        also have "qfact q (int k) * (1 - q) ^ k = (\<Prod>k = 1..int k. 1 - q powi k)"
          by (simp add: qfact_altdef power_int_minus field_simps)
        also have "\<dots> = (\<Prod>k = 1..k. 1 - q ^ k)"
          by (intro prod.reindex_bij_witness[of _ int nat]) (auto simp: power_int_def)
        also have "norm \<dots> = (\<Prod>k=1..k. norm (1 - q ^ k))"
          by (simp add: prod_norm)
        also have "1 - norm q \<le> norm (1 - q ^ i)" if "i > 0" for i
        proof -
          have "norm (1 - q ^ i) \<ge> norm (1 :: 'a) - norm (q ^ i)"
            by norm
          moreover have "norm q ^ i \<le> norm q ^ 1"
            using q that by (intro power_decreasing) auto
          ultimately show ?thesis
            by (simp add: norm_power)
        qed
        hence "norm q ^ (k choose 2) * norm t ^ k / (\<Prod>k = 1..k. norm (1 - q ^ k)) \<le>
               norm q ^ (k choose 2) * norm t ^ k / (\<Prod>i = 1..k. 1 - norm q)"
          using q
          by (intro divide_left_mono prod_mono mult_pos_pos prod_pos)
             (auto intro: power_le_one simp: power_less_one_iff dest: power_eq_1_iff)
        finally show "norm (S k) \<le> norm q ^ (k choose 2) * norm t ^ k / (1 - norm q) ^ k"
          by simp
      qed auto
      also have "\<dots> = g k"
        by (simp add: g_def)
      finally show "norm ((\<Prod>i<k. 1 - q ^ (n - i)) * S k) \<le> g k" .
    qed
  next
    show "summable g"
    proof (rule summable_comparison_test_bigo)
      show "g \<in> O(\<lambda>k. (1/2) ^ k)"
      proof (cases "q = 0 \<or> t = 0")
        case True
        have "eventually (\<lambda>k. g k = 0) at_top"
          using eventually_gt_at_top[of 2] by eventually_elim (use True in \<open>auto simp: g_def\<close>)
        from landau_o.big.in_cong[OF this] show ?thesis
          by simp
      next
        case False
        hence "q \<noteq> 0"
          by auto
        have 1: "1 + norm q > 0"
          using q by (auto intro: add_pos_nonneg)
        have 2: "ln (norm q) / 2 < 0"
          using 1 False q by (auto simp: field_simps)
        show ?thesis
          unfolding g_altdef[OF \<open>q \<noteq> 0\<close>] using False 1 2 by real_asymp
      qed
    next
      show "summable (\<lambda>n. norm ((1 / 2) ^ n :: real))"
        by (simp add: norm_power)
    qed
  qed auto

  from lim2 show "summable (\<lambda>k. norm (S k))"
    by blast

  note lim2
  also have "(\<lambda>n. \<Sum>k. (\<Prod>i<k. 1 - q ^ (n - i)) * S k) = (\<lambda>n. \<Sum>k\<le>n. (\<Prod>i<k. 1 - q ^ (n - i)) * S k)"
  proof (intro ext suminf_finite)
    fix n k :: nat assume k: "k \<notin> {..n}"
    hence "n \<in> {..<k}" "q ^ (n - n) = 1"
      by auto
    hence "\<exists>a\<in>{..<k}. q ^ (n - a) = 1"
      by blast
    thus "(\<Prod>i<k. 1 - q ^ (n - i)) * S k = 0"
      by auto
  qed auto
  finally have "(\<lambda>n. \<Sum>k\<le>n. (\<Prod>i<k. 1 - q ^ (n - i)) * S k) \<longlonglongrightarrow> (\<Sum>a. S a)"
    by blast
  with lim1 show "(\<Sum>a. S a) = qpochhammer_inf (-t) q"
    using LIMSEQ_unique by blast
qed


subsection \<open>The $q$-Vandermonde identity\<close>

text \<open>
  The following is the $q$-analog of Vandermonde's identity
  \[\binom{m+n}{r} = \sum_{i=0}^r \binom{m}{i} \binom{n}{r-i}\ ,\]
  namely:
  \[\binom{m+n}{r}_{\!\!q} = 
    \sum_{i=0}^r \binom{m}{i}_{\!\!q} \binom{n}{r-i}_{\!\!q} q^{(m-i)(r-i)}\]
\<close>
theorem qvandermonde:
  fixes m n :: nat and q :: "'a :: real_normed_field"
  assumes "norm q \<noteq> 1"
  shows "qbinomial q (m + n) r =
           (\<Sum>i\<le>r. qbinomial q m i * qbinomial q n (r - i) * q ^ ((m - i) * (r - i)))"
proof (cases "q = 0")
  case [simp]: False
  define Q where "Q = fls_const q"
  define X where "X = (fls_X :: 'a fls)"
  have [simp]: "qbinomial (fls_const q) n k = fls_const (qbinomial q n k)" for n k
    by (induction q n k rule: qbinomial.induct)
       (simp_all add: qbinomial_Suc_Suc fls_plus_const fls_const_mult_const flip: fls_const_power)
  define F where
    "F = Abs_fps (\<lambda>k. if k \<le> m + n then qbinomial q (m + n) k * q ^ (k choose 2) else 0)"
  define G where
    "G = Abs_fps (\<lambda>k. if k \<le> m then qbinomial q m k * q ^ (k choose 2) else 0)"
  define H where
    "H = Abs_fps (\<lambda>k. if k \<le> n then qbinomial q n k * q ^ (k choose 2) * q ^ (m * k) else 0)"
  have two_times_choose_two: "2 * int (n choose 2) = n * (n - 1)" for n
  proof -
    have "2 * int (n choose 2) = int (2 * (n choose 2))"
      by simp
    also have "2 * (n choose 2) = n * (n - 1)"
      unfolding choose_two by (simp add: algebra_simps)
    finally show ?thesis
      by simp
  qed

  have *: "(\<Sum>k\<in>A. if x = int k then f k else 0) = (if x \<ge> 0 \<and> nat x \<in> A then f (nat x) else 0)"
    if "finite A" for A :: "nat set" and f :: "nat \<Rightarrow> 'a" and x
  proof -
    have "(\<Sum>k\<in>A. if x = int k then f k else 0) =
             (\<Sum>k\<in>(if x \<ge> 0 \<and> nat x \<in> A then {nat x} else {}).  if x = int k then f k else 0)"
      using that by (intro sum.mono_neutral_right) auto
    thus ?thesis
      by auto
  qed

  have "0 = qpochhammer (m + n) (-X) Q - qpochhammer m (-X) Q * qpochhammer n (Q ^ m * (-X)) Q"
    unfolding of_nat_add by (subst qpochhammer_nat_add) auto
  also have "\<dots> = (\<Sum>k\<le>m + n. qbinomial Q (m + n) k * Q ^ (k choose 2) * X ^ k) -
                  (\<Sum>k\<le>m. qbinomial Q m k * Q ^ (k choose 2) * X ^ k) *
                  (\<Sum>k\<le>n. qbinomial Q n k * Q ^ (k choose 2) * Q ^ (m * k) * X ^ k)"
    by (subst (1 2 3) qbinomial_theorem') (simp add: power_mult_distrib mult_ac flip: power_mult)
  also have "(\<Sum>k\<le>m + n. qbinomial Q (m + n) k * Q ^ (k choose 2) * X ^ k) = fps_to_fls F"
    by (rule fls_eqI)
       (auto simp: F_def Q_def X_def fls_nth_sum fls_X_power_times_conv_shift *
             simp flip: fls_const_power)
  also have "(\<Sum>k\<le>m. qbinomial Q m k * Q ^ (k choose 2) * X ^ k) = fps_to_fls G"
    by (rule fls_eqI)
       (auto simp: G_def Q_def X_def fls_nth_sum fls_X_power_times_conv_shift *
             simp flip: fls_const_power)
  also have "(\<Sum>k\<le>n. qbinomial Q n k * Q ^ (k choose 2) * Q ^ (m * k) * X ^ k) = fps_to_fls H"
    by (rule fls_eqI)
       (auto simp: H_def Q_def X_def fls_nth_sum fls_X_power_times_conv_shift *
             simp flip: fls_const_power)
  also have "fls_nth (fps_to_fls F - fps_to_fls G * fps_to_fls H) (int r) =
               fps_nth F r - fps_nth (G * H) r"
    by (simp flip: fls_times_fps_to_fls)
  finally have eq: "fps_nth F r = fps_nth (G * H) r"
    by simp
  
  show "qbinomial q (m + n) r =
           (\<Sum>i\<le>r. qbinomial q m i * qbinomial q n (r - i) * q ^ ((m - i) * (r - i)))"
  proof (cases "r \<le> m + n")
    case True
    have "qbinomial q (m + n) r * q ^ (r choose 2) =
            (\<Sum>i\<le>r. qbinomial q m i * q ^ (i choose 2) * qbinomial q n (r - i) * 
                      q ^ ((r - i) choose 2) * q ^ (m * (r - i)))"
      using eq True
      by (auto simp: F_def G_def H_def fps_mult_nth atLeast0AtMost intro!: sum.cong)
    also have "\<dots> = (\<Sum>i\<le>r. qbinomial q m i * qbinomial q n (r - i) * q ^ 
                              ((i choose 2) + ((r - i) choose 2) + m * (r - i)))"
      by (subst power_add)+ (simp add: mult_ac)
    also have "\<dots> = (\<Sum>i\<le>r. qbinomial q m i * qbinomial q n (r - i) * 
                              q ^ ((r choose 2) + (m - i) * (r - i)))"
    proof (intro sum.cong refl, goal_cases)
      case (1 k)
      have eq: "(k choose 2) + (r - k choose 2) + m * (r - k) = (r choose 2) + (m - k) * (r - k)"
        if "k \<le> m" "k \<le> r"
      proof -
        have "2 * (int (k choose 2) + int (r - k choose 2) + m * (int r - int k)) =
              2 * ((r choose 2) + (int m - int k) * (int r - int k))"
          unfolding ring_distribs two_times_choose_two using that
          apply (cases "k = 0"; cases "r = 0"; cases "r = k")
                 apply (simp_all add: of_nat_diff)
          apply (simp_all add: algebra_simps)?
          done
        hence "nat (2 * (int (k choose 2) + int (r - k choose 2) + m * (int r - int k))) =
              nat (2 * ((r choose 2) + (int m - int k) * (int r - int k)))" by simp
        hence "2 * ((k choose 2) + (r - k choose 2) + m * (r - k)) =
                 2 * ((r choose 2) + (m - k) * (r - k))"
          using that by (simp add: nat_plus_as_int of_nat_diff)
        thus ?thesis
          by simp
      qed
      show ?case
      proof (cases "k \<le> m")
        case True
        thus ?thesis using 1
          by (subst eq) auto
      next
        case False
        thus ?thesis using True
          by (auto simp: not_le choose_two)
      qed
    qed
    also have "\<dots> = (\<Sum>i\<le>r. qbinomial q m i * qbinomial q n (r - i) * 
                      q ^ ((m - i) * (r - i))) * q ^ (r choose 2)"
      by (simp add: sum_distrib_right sum_distrib_left power_add mult_ac)
    finally show ?thesis
      by simp
  next
    case False
    hence "i > m \<or> r - i > n" if "i \<le> r" for i
      using that by linarith
    have "(\<Sum>i\<le>r. qbinomial q m i * qbinomial q n (r - i) * q ^ ((m - i) * (r - i))) = 0"
    proof (intro sum.neutral ballI, goal_cases)
      case (1 i)
      hence "i \<le> r"
        by simp
      hence "i > m \<or> r - i > n"
        using False by linarith
      thus ?case
        by auto
    qed
    thus ?thesis using False
      by simp
  qed
next
  case [simp]: True
  have "(\<Sum>i\<le>r. qbinomial q m i * qbinomial q n (r - i) * q ^ ((m - i) * (r - i))) =
        (\<Sum>i \<in> (if r \<le> m + n then {min m r} else {}). 1)"
    using True by (intro sum.mono_neutral_cong_right)
                  (auto simp: qbinomial_0_left min_def split: if_splits)
  also have "\<dots> = qbinomial q (m + n) r"
    by auto
  finally show ?thesis ..
qed

text \<open>
  We therefore also get the following identity for the central $q$-binomial coefficient:
\<close>
corollary qbinomial_square_sum:
  fixes q :: "'a :: real_normed_field"
  assumes q: "norm q \<noteq> 1"
  shows   "(\<Sum>k\<le>n. qbinomial q n k ^ 2 * q ^ (k ^ 2)) = qbinomial q (2 * n) n"
proof -
  have "qbinomial q (2 * n) n = (\<Sum>k\<le>n. qbinomial q n k ^ 2 * q ^ ((n - k)^2))"
    using qvandermonde[of q n n n] q
    by (auto simp: power2_eq_square qbinomial_symmetric simp flip: mult_2 intro!: sum.cong)
  also have "\<dots> = (\<Sum>k\<le>n. qbinomial q n k ^ 2 * q ^ (k^2))"
    using q
    by (intro sum.reindex_bij_witness[of _ "\<lambda>k. n - k" "\<lambda>k. n - k"])
       (auto simp: qbinomial_symmetric)
  finally show ?thesis ..
qed

end