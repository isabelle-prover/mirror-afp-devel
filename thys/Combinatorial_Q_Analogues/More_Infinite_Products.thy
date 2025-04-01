subsection \<open>Additional facts about infinite products\<close>
theory More_Infinite_Products
  imports "HOL-Analysis.Analysis"
begin

(*
  grouping factors into chunks of the same size

  Only one direction; other direction requires "real_normed_field" (see below).
  Not sure if real_normed_field is really necessary, but I don't see how else to do it.
*)
lemma has_prod_group_nonzero: 
  fixes f :: "nat \<Rightarrow> 'a :: {semidom, t2_space}"
  assumes "f has_prod P" "k > 0" "P \<noteq> 0"
  shows   "(\<lambda>n. (\<Prod>i\<in>{n*k..<n*k+k}. f i)) has_prod P"
proof -
  have "(\<lambda>n. \<Prod>k<n. f k) \<longlonglongrightarrow> P"
    using assms(1) by (intro has_prod_imp_tendsto')
  hence "(\<lambda>n. \<Prod>k<n*k. f k) \<longlonglongrightarrow> P"
    by (rule filterlim_compose) (use \<open>k > 0\<close> in real_asymp)
  also have "(\<lambda>n. \<Prod>k<n*k. f k) = (\<lambda>n. \<Prod>m<n. prod f {m*k..<m*k+k})"
    by (subst prod.nat_group [symmetric]) auto
  finally have "(\<lambda>n. \<Prod>m\<le>n. prod f {m*k..<m*k+k}) \<longlonglongrightarrow> P"
    by (subst (asm) LIMSEQ_lessThan_iff_atMost)
  hence "raw_has_prod (\<lambda>n. prod f {n*k..<n*k+k}) 0 P"
    using \<open>P \<noteq> 0\<close> by (auto simp: raw_has_prod_def)
  thus ?thesis
    by (auto simp: has_prod_def)
qed

lemma has_prod_group:
  fixes f :: "nat \<Rightarrow> 'a :: real_normed_field"
  assumes "f has_prod P" "k > 0"
  shows   "(\<lambda>n. (\<Prod>i\<in>{n*k..<n*k+k}. f i)) has_prod P"
proof (rule convergent_prod_tendsto_imp_has_prod)
  have "(\<lambda>n. \<Prod>k<n. f k) \<longlonglongrightarrow> P"
    using assms(1) by (intro has_prod_imp_tendsto')
  hence "(\<lambda>n. \<Prod>k<n*k. f k) \<longlonglongrightarrow> P"
    by (rule filterlim_compose) (use \<open>k > 0\<close> in real_asymp)
  also have "(\<lambda>n. \<Prod>k<n*k. f k) = (\<lambda>n. \<Prod>m<n. prod f {m*k..<m*k+k})"
    by (subst prod.nat_group [symmetric]) auto
  finally show "(\<lambda>n. \<Prod>m\<le>n. prod f {m*k..<m*k+k}) \<longlonglongrightarrow> P"
    by (subst (asm) LIMSEQ_lessThan_iff_atMost)
next
  from assms obtain N P' where prod1: "raw_has_prod f N P'"
    by (auto simp: has_prod_def)
  define N' where "N' = nat \<lceil>real N / real k\<rceil>"
  have "k * N' \<ge> N"
  proof -
    have "(real N / real k * real k) \<le> real (N' * k)"
      unfolding N'_def of_nat_mult by (intro mult_right_mono) (use \<open>k > 0\<close> in auto)
    also have "real N / real k * real k = real N"
      using \<open>k > 0\<close> by simp
    finally show ?thesis
      by (simp only: mult.commute of_nat_le_iff)
  qed

  obtain P'' where prod2: "raw_has_prod f (k * N') P''"
    using prod1 \<open>k * N' \<ge> N\<close> by (rule raw_has_prod_ignore_initial_segment)
  hence "P'' \<noteq> 0"
    by (auto simp: raw_has_prod_def)
  from prod2 have "raw_has_prod (\<lambda>n. f (n + k * N')) 0 P''"
    by (simp add: raw_has_prod_def)
  hence "(\<lambda>n. f (n + k * N')) has_prod P''"
    by (auto simp: has_prod_def)
  hence "(\<lambda>n. \<Prod>i=n*k..<n*k+k. f (i + k * N')) has_prod P''"
    by (rule has_prod_group_nonzero) fact+
  hence "convergent_prod (\<lambda>n. \<Prod>i=n*k..<n*k+k. f (i + k * N'))"
    using has_prod_iff by blast
  also have "(\<lambda>n. \<Prod>i=n*k..<n*k+k. f (i + k * N')) = (\<lambda>n. \<Prod>i=(n+N')*k..<(n+N')*k+k. f i)"
  proof
    fix n :: nat
    show "(\<Prod>i=n*k..<n*k+k. f (i + k * N')) = (\<Prod>i=(n+N')*k..<(n+N')*k+k. f i)"
      by (rule prod.reindex_bij_witness[of _ "\<lambda>n. n - k*N'" "\<lambda>n. n + k*N'"])
         (auto simp: algebra_simps)
  qed
  also have "convergent_prod \<dots> \<longleftrightarrow> convergent_prod (\<lambda>n. (\<Prod>i=n*k..<n*k+k. f i))"
    by (rule convergent_prod_iff_shift)
  finally show "convergent_prod (\<lambda>n. prod f {n * k..<n * k + k})" .
qed

end