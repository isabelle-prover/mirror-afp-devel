section \<open>Some Abel-Style Summation Tests\<close>
theory Summation_Tests_More
  imports "HOL-Analysis.Analysis" "HOL-Library.Landau_Symbols" Lambert_Series_Library
begin

text \<open>
  The following five summation tests are taking from Chapter 10 of Knopp's textbook~\cite{knopp22}.
  He introduces a strong variant of Abel's summation test and then deduces from it four
  summation test named after Abel, Dirichlet, du Bois-Reymond, and Dedekind.
\<close>
lemma abel_partial_summation:
  fixes f g :: "nat \<Rightarrow> 'a :: comm_ring_1"
  defines "F \<equiv> (\<lambda>n. \<Sum>k\<le>n. f k)"
  shows   "(\<Sum>r=n+1..n+k. f r * g r) =
             (\<Sum>r=n+1..n+k. F r * (g r - g (Suc r))) - 
             F n * g (Suc n) + F (n + k) * g (n + k + 1)"
  by (induction k) (auto simp: F_def algebra_simps)

theorem abel_summation_test_strong:
  fixes f g :: "nat \<Rightarrow> 'a :: {real_normed_field, banach}"
  defines "F \<equiv> (\<lambda>n. \<Sum>k\<le>n. f k)"
  assumes "summable (\<lambda>r. F r * (g r - g (Suc r)))"
  assumes "convergent (\<lambda>r. F r * g (Suc r))"
  shows   "summable (\<lambda>r. f r * g r)"
  unfolding summable_iff_convergent'
proof (rule Cauchy_convergent)
  show "Cauchy (\<lambda>n. \<Sum>r\<le>n. f r * g r)"
    unfolding Cauchy_def
  proof safe
    fix \<epsilon> :: real assume \<epsilon>: "\<epsilon> > 0"
    let ?A = "\<lambda>n. (\<Sum>r\<le>n. F r * (g r - g (Suc r)))"
    from assms(2) have "Cauchy (\<lambda>n. \<Sum>r\<le>n. F r * (g r - g (Suc r)))"
      unfolding summable_iff_convergent' using convergent_Cauchy by blast
    moreover have "\<epsilon> / 2 > 0"
      using \<epsilon> by auto
    ultimately obtain M1 where M1: "dist (?A m) (?A n) < \<epsilon> / 2" if "m \<ge> M1" "n \<ge> M1" for m n
      unfolding Cauchy_def by fast
    have M1': "norm (\<Sum>r=m..n. F r * (g r - g (Suc r))) < \<epsilon> / 2" if "M1 < m" "m \<le> Suc n" for m n
    proof -
      have "dist (?A n) (?A (m - 1)) < \<epsilon> / 2"
        by (rule M1) (use that in auto)
      also have "dist (?A n) (?A (m - 1)) = norm (\<Sum>r\<in>{..n}-{..m - 1}. F r * (g r - g (Suc r)))"
        unfolding dist_norm using that by (subst Groups_Big.sum_diff) auto
      also have "{..n} - {..m - 1} = {m..n}"
        using that by auto
      finally show ?thesis .
    qed

    from \<epsilon> have "\<epsilon> / 4 > 0"
      by auto
    from assms(3) obtain c where "(\<lambda>r. F r * g (Suc r)) \<longlonglongrightarrow> c"
      by (auto simp: convergent_def)
    with \<open>\<epsilon> / 4 > 0\<close> have "eventually (\<lambda>r. dist (F r * g (Suc r)) c < \<epsilon> / 4) sequentially"
      using tendstoD by blast
    then obtain M2 where M2: "dist (F r * g (Suc r)) c < \<epsilon> / 4" if "r \<ge> M2" for r
      unfolding eventually_at_top_linorder by blast

    show "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (\<Sum>r\<le>m. f r * g r) (\<Sum>r\<le>n. f r * g r) < \<epsilon>"
    proof (rule exI[of _ "max M1 M2"], safe)
      fix m n :: nat assume "m \<ge> max M1 M2" "n \<ge> max M1 M2"
      thus "dist (\<Sum>r\<le>m. f r * g r) (\<Sum>r\<le>n. f r * g r) < \<epsilon>"
      proof (induction m n rule: linorder_wlog)
        case (le m n)
        define k where "k = n - m"
        from le have n_eq: "n = m + k"
          by (auto simp: k_def)
        have "dist (\<Sum>r\<le>m. f r * g r) (\<Sum>r\<le>n. f r * g r) =
              norm ((\<Sum>r\<le>n. f r * g r) - (\<Sum>r\<le>m. f r * g r))"
          by (simp add: dist_norm norm_minus_commute)
        also have "(\<Sum>r\<le>n. f r * g r) - (\<Sum>r\<le>m. f r * g r) = (\<Sum>r\<in>{..n}-{..m}. f r * g r)"
          using le by (subst Groups_Big.sum_diff) auto
        also have "{..n} - {..m} = {m+1..m+k}"
          by (auto simp: n_eq)
        also have "(\<Sum>r=m+1..m+k. f r * g r) =
                     (\<Sum>r=m+1..m+k. F r * (g r - g (Suc r))) - 
                      F m * g (Suc m) + F (m + k) * g (Suc (m + k))"
          unfolding F_def by (subst abel_partial_summation) simp_all
        also have "norm \<dots> \<le> norm (\<Sum>r=m+1..m+k. F r * (g r - g (Suc r))) +
                     dist (F m * g (Suc m)) c + dist (F (m + k) * g (Suc (m + k))) c"
          by norm
        also have "\<dots> < \<epsilon> / 2 + \<epsilon> / 4 + \<epsilon> / 4"
          using le by (intro add_strict_mono M1' M2) auto
        also have "\<dots> = \<epsilon>"
          by simp
        finally show "dist (\<Sum>r\<le>m. f r * g r) (\<Sum>r\<le>n. f r * g r) < \<epsilon>" .
      qed (simp add: dist_commute max.commute)
    qed
  qed
qed

corollary abel_summation_test:
  fixes f g :: "nat \<Rightarrow> real"
  assumes "summable f"
  assumes "incseq g" "g \<in> O(\<lambda>_. 1)"
  shows   "summable (\<lambda>r. f r * g r)"
proof (rule abel_summation_test_strong)
  have "convergent g"
    by (rule incseq_convergent') fact+
  thus "convergent (\<lambda>n. (\<Sum>k\<le>n. f k) * g (Suc n))" using assms(1)
    by (intro convergent_mult) (simp_all add: convergent_Suc_iff summable_iff_convergent')
  show "summable (\<lambda>n. (\<Sum>k\<le>n. f k) * (g n - g (Suc n)))"
  proof (subst mult.commute, rule summable_norm_cancel, rule norm_summable_mult_bounded)
    have "summable (\<lambda>n. g (Suc n) - g n)"
      using \<open>convergent g\<close> by (simp add: telescope_summable_iff)
    also have "(\<lambda>n. g (Suc n) - g n) = (\<lambda>n. norm (g n - g (Suc n)))"
      using \<open>incseq g\<close> by (auto simp: incseq_def fun_eq_iff)
    finally show "summable (\<lambda>n. norm (g n - g (Suc n)))" .
  next
    have "bounded (range (\<lambda>n. \<Sum>k<n. f k))"
      by (rule summable_imp_sums_bounded) fact
    hence "(\<lambda>n. \<Sum>k<n. f k) \<in> O(\<lambda>_. 1)"
      by (simp add: seq_bigo_1_iff)
    hence "(\<lambda>n. \<Sum>k<Suc n. f k) \<in> O(\<lambda>_. 1)"
      by (rule landau_o.big.compose) (rule filterlim_Suc)
    also have "(\<lambda>n. {..<Suc n}) = (\<lambda>n. {..n})"
      by auto
    finally show "(\<lambda>n. \<Sum>k\<le>n. f k) \<in> O(\<lambda>_. 1)" .
  qed
qed

corollary dirichlet_summation_test:
  fixes f g :: "nat \<Rightarrow> real"
  assumes "(\<lambda>n. \<Sum>r\<le>n. f r) \<in> O(\<lambda>_. 1)"
  assumes "decseq g" "g \<in> o(\<lambda>_. 1)"
  shows   "summable (\<lambda>r. f r * g r)"
proof (rule abel_summation_test_strong)
  have "(\<lambda>x. g (Suc x)) \<in> o(\<lambda>x. 1)"
    using assms(3) by (rule landau_o.small.compose) (rule filterlim_Suc)
  have "(\<lambda>n. (\<Sum>r\<le>n. f r) * g (Suc n)) \<in> o(\<lambda>_. 1 * 1)"
    by (rule landau_o.big_small_mult) fact+
  thus "convergent (\<lambda>r. sum f {..r} * g (Suc r))"
    by (auto dest!: smalloD_tendsto simp: convergent_def)
next
  have "g \<longlonglongrightarrow> 0"
    using assms(3) by (auto dest!: smalloD_tendsto simp: convergent_def)
  hence "convergent g"
    by (auto simp: convergent_def)
  show "summable (\<lambda>n. (\<Sum>k\<le>n. f k) * (g n - g (Suc n)))"
  proof (subst mult.commute, rule summable_norm_cancel, rule norm_summable_mult_bounded)
    have "summable (\<lambda>n. g n - g (Suc n))"
      using \<open>convergent g\<close> by (simp add: telescope_summable_iff')
    also have "(\<lambda>n. g n - g (Suc n)) = (\<lambda>n. norm (g n - g (Suc n)))"
      using \<open>decseq g\<close> by (auto simp: decseq_Suc_iff fun_eq_iff)
    finally show "summable (\<lambda>n. norm (g n - g (Suc n)))" .
  qed fact
qed

corollary dubois_reymond_summation_test:
  fixes f g :: "nat \<Rightarrow> 'a :: {real_normed_field, banach}"
  assumes "summable f"
  assumes "summable (\<lambda>r. norm (g r - g (Suc r)))"
  shows   "summable (\<lambda>r. f r * g r)"
proof (rule abel_summation_test_strong)
  have "summable (\<lambda>r. g r - g (Suc r))"
    using assms(2) by (rule summable_norm_cancel)
  hence "convergent g"
    by (subst (asm) telescope_summable_iff')
  show "convergent (\<lambda>r. sum f {..r} * g (Suc r))"
    using assms(1) \<open>convergent g\<close>
    by (intro convergent_mult) (auto simp: convergent_Suc_iff summable_iff_convergent')

  show "summable (\<lambda>n. (\<Sum>k\<le>n. f k) * (g n - g (Suc n)))"
  proof (subst mult.commute, rule summable_norm_cancel, rule norm_summable_mult_bounded)
    have "bounded (range (\<lambda>n. \<Sum>k<n. f k))"
      by (rule summable_imp_sums_bounded) fact
    hence "(\<lambda>n. \<Sum>k<n. f k) \<in> O(\<lambda>_. 1)"
      by (simp add: seq_bigo_1_iff)
    hence "(\<lambda>n. \<Sum>k<Suc n. f k) \<in> O(\<lambda>_. 1)"
      by (rule landau_o.big.compose) (rule filterlim_Suc)
    also have "(\<lambda>n. {..<Suc n}) = (\<lambda>n. {..n})"
      by auto
    finally show "(\<lambda>n. \<Sum>k\<le>n. f k) \<in> O(\<lambda>_. 1)" .
  qed fact
qed

corollary dedekind_summation_test:
  fixes f g :: "nat \<Rightarrow> 'a :: {real_normed_field, banach}"
  assumes "(\<lambda>n. \<Sum>k\<le>n. f k) \<in> O(\<lambda>_. 1)"
  assumes "summable (\<lambda>r. norm (g r - g (Suc r)))"
  assumes "g \<in> o(\<lambda>_. 1)"
  shows   "summable (\<lambda>r. f r * g r)"
proof (rule abel_summation_test_strong)
  have "(\<lambda>x. g (Suc x)) \<in> o(\<lambda>x. 1)"
    using assms(3) by (rule landau_o.small.compose) (rule filterlim_Suc)
  have "(\<lambda>n. (\<Sum>r\<le>n. f r) * g (Suc n)) \<in> o(\<lambda>_. 1 * 1)"
    by (rule landau_o.big_small_mult) fact+
  thus "convergent (\<lambda>r. sum f {..r} * g (Suc r))"
    by (auto dest!: smalloD_tendsto simp: convergent_def)
  show "summable (\<lambda>n. (\<Sum>k\<le>n. f k) * (g n - g (Suc n)))"
    by (subst mult.commute, rule summable_norm_cancel, rule norm_summable_mult_bounded) fact+
qed

end