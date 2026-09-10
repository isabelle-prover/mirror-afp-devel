theory Abstract_Descent
  imports "HOL-Analysis.Analysis"
begin

section \<open>Abstract descent and telescoping lemmas\<close>

text \<open>
This theory contains abstract sequence and finite-sum lemmas used in descent
analyses.  These results are independent of gradients, projections, and
particular optimization algorithms.
\<close>

subsection \<open>Finite-sum telescoping\<close>

text \<open>
If each local progress term is bounded by the decrease of a potential, then
the sum of all progress terms is bounded by the total decrease of the
potential.
\<close>

lemma sum_progress_le_initial_gap:
  fixes a c :: "nat \<Rightarrow> real"
  assumes step: "\<And>n. n < N \<Longrightarrow> c n \<le> a n - a (Suc n)"
  shows "sum c {..<N} \<le> a 0 - a N"
  using step
proof (induction N)
  case 0
  show ?case by simp
next
  case (Suc N)
  have IH: "sum c {..<N} \<le> a 0 - a N"
  proof (rule Suc.IH)
    fix n
    assume n_lt: "n < N"
    then show "c n \<le> a n - a (Suc n)"
      using Suc.prems by simp
  qed

  have last: "c N \<le> a N - a (Suc N)"
    using Suc.prems by simp

  have "sum c {..<Suc N} = sum c {..<N} + c N"
    by simp
  also have "... \<le> (a 0 - a N) + (a N - a (Suc N))"
    using IH last by linarith
  also have "... = a 0 - a (Suc N)"
    by simp
  finally show ?case .
qed

text \<open>
A version in which the terminal value of the potential is replaced by a lower
bound.
\<close>

lemma sum_progress_le_initial_minus_lower_bound:
  fixes a c :: "nat \<Rightarrow> real"
  assumes step: "\<And>n. n < N \<Longrightarrow> c n \<le> a n - a (Suc n)"
  assumes lower: "B \<le> a N"
  shows "sum c {..<N} \<le> a 0 - B"
proof -
  have "sum c {..<N} \<le> a 0 - a N"
    using step by (rule sum_progress_le_initial_gap)
  also have "... \<le> a 0 - B"
    using lower by linarith
  finally show ?thesis .
qed

subsection \<open>Average bounds\<close>

text \<open>
If a finite sum is bounded above, then at least one term is bounded by the
corresponding average.
\<close>

lemma exists_le_average_of_sum_bound:
  fixes a :: "nat \<Rightarrow> real"
  assumes N_pos: "N > 0"
  assumes nonneg: "\<And>n. n < N \<Longrightarrow> 0 \<le> a n"
  assumes sum_bound: "sum a {..<N} \<le> B"
  shows "\<exists>n<N. a n \<le> B / real N"
proof (rule ccontr)
  assume not_exists: "\<not> (\<exists>n<N. a n \<le> B / real N)"

  have gt: "\<And>n. n < N \<Longrightarrow> B / real N < a n"
  proof -
    fix n
    assume n_lt: "n < N"
    have "\<not> a n \<le> B / real N"
      using not_exists n_lt by auto
    then show "B / real N < a n"
      by simp
  qed

  have const_sum: "sum (\<lambda>n. B / real N) {..<N} = B"
    using N_pos by simp

  have strict_sum: "sum (\<lambda>n. B / real N) {..<N} < sum a {..<N}"
    using N_pos gt by (intro sum_strict_mono) auto

  have "B < sum a {..<N}"
    using const_sum strict_sum by simp
  then show False
    using sum_bound by linarith
qed

lemma exists_le_average_of_nonnegative_sum:
  fixes a :: "nat \<Rightarrow> real"
  assumes N_pos: "N > 0"
  assumes nonneg: "\<And>n. n < N \<Longrightarrow> 0 \<le> a n"
  shows "\<exists>n<N. a n \<le> sum a {..<N} / real N"
proof -
  have sum_bound: "sum a {..<N} \<le> sum a {..<N}"
    by simp
  show ?thesis
    using exists_le_average_of_sum_bound[OF N_pos nonneg sum_bound] .
qed

subsection \<open>Linear recurrences\<close>

text \<open>
A one-step linear recurrence can be iterated to obtain a geometric bound.
\<close>

lemma sequence_linear_rate_from_step:
  fixes a :: "nat \<Rightarrow> real"
  assumes q_nonneg: "0 \<le> q"
  assumes step: "\<And>n. a (Suc n) \<le> q * a n"
  shows "a n \<le> q ^ n * a 0"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have "a (Suc n) \<le> q * a n"
    by (rule step)
  also have "... \<le> q * (q ^ n * a 0)"
  proof (rule mult_left_mono)
    show "a n \<le> q ^ n * a 0"
      using Suc.IH .
    show "0 \<le> q"
      using q_nonneg .
  qed
  also have "... = q ^ Suc n * a 0"
    by (simp add: algebra_simps)
  finally show ?case .
qed

end