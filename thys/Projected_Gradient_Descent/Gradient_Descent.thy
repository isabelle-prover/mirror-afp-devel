theory Gradient_Descent
  imports Smooth_Convex
begin

section \<open>Gradient descent sequences\<close>

text \<open>
This theory lifts the one-step descent estimates from @{text \<open>Smooth_Convex\<close>} to
gradient descent sequences.

The purpose of this file is deliberately modest: it packages the recurrence

  x (Suc n) = @{text \<open>gradient_step\<close>} alpha G (x n)

and proves the basic monotonicity consequences that follow from the smooth
upper-bound interface.
\<close>


subsection \<open>Gradient descent recurrence\<close>

definition gradient_descent_iterates ::
  "real \<Rightarrow> ('a::real_vector \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "gradient_descent_iterates alpha G x \<longleftrightarrow>
     (\<forall>n. x (Suc n) = gradient_step alpha G (x n))"

lemma gradient_descent_iteratesI:
  assumes "\<And>n. x (Suc n) = gradient_step alpha G (x n)"
  shows "gradient_descent_iterates alpha G x"
  using assms
  unfolding gradient_descent_iterates_def
  by auto

lemma gradient_descent_iteratesD:
  assumes "gradient_descent_iterates alpha G x"
  shows "x (Suc n) = gradient_step alpha G (x n)"
  using assms
  unfolding gradient_descent_iterates_def
  by auto

lemma gradient_descent_iteratesE:
  assumes "gradient_descent_iterates alpha G x"
  obtains "x (Suc n) = gradient_step alpha G (x n)"
  using gradient_descent_iteratesD[OF assms, of n]
  by auto


subsection \<open>Feasible iterates\<close>

definition feasible_iterates ::
  "'a set \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool"
where
  "feasible_iterates S x \<longleftrightarrow> (\<forall>n. x n \<in> S)"

lemma feasible_iteratesI:
  assumes "\<And>n. x n \<in> S"
  shows "feasible_iterates S x"
  using assms
  unfolding feasible_iterates_def
  by auto

lemma feasible_iteratesD:
  assumes "feasible_iterates S x"
  shows "x n \<in> S"
  using assms
  unfolding feasible_iterates_def
  by auto

lemma feasible_iterates_subset:
  assumes "feasible_iterates S x"
    and "S \<subseteq> T"
  shows "feasible_iterates T x"
proof (rule feasible_iteratesI)
  fix n
  have "x n \<in> S"
    using assms(1)
    by (rule feasible_iteratesD)
  then show "x n \<in> T"
    using assms(2)
    by auto
qed

lemma gradient_descent_step_mem:
  assumes gd: "gradient_descent_iterates alpha G x"
    and feasible: "feasible_iterates S x"
  shows "gradient_step alpha G (x n) \<in> S"
proof -
  have next_mem: "x (Suc n) \<in> S"
    using feasible
    by (rule feasible_iteratesD)

  have step_eq: "x (Suc n) = gradient_step alpha G (x n)"
    using gd
    by (rule gradient_descent_iteratesD)

  show ?thesis
    using next_mem step_eq
    by simp
qed


subsection \<open>Objective value sequences\<close>

definition objective_values ::
  "('a \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> real"
where
  "objective_values f x n = f (x n)"

lemma objective_values_simp [simp]:
  "objective_values f x n = f (x n)"
  unfolding objective_values_def
  by simp

definition nonincreasing_sequence ::
  "(nat \<Rightarrow> real) \<Rightarrow> bool"
where
  "nonincreasing_sequence a \<longleftrightarrow> (\<forall>n. a (Suc n) \<le> a n)"

lemma nonincreasing_sequenceI:
  assumes "\<And>n. a (Suc n) \<le> a n"
  shows "nonincreasing_sequence a"
  using assms
  unfolding nonincreasing_sequence_def
  by auto

lemma nonincreasing_sequenceD:
  assumes "nonincreasing_sequence a"
  shows "a (Suc n) \<le> a n"
  using assms
  unfolding nonincreasing_sequence_def
  by auto


subsection \<open>One-step estimates along gradient descent iterates\<close>

lemma gradient_descent_one_step_bound:
  assumes smooth: "smooth_upper_bound_on L S f G"
    and gd: "gradient_descent_iterates alpha G x"
    and feasible: "feasible_iterates S x"
  shows
    "f (x (Suc n))
      \<le> f (x n) - alpha * norm (G (x n)) ^ 2
          + (L / 2) * alpha ^ 2 * norm (G (x n)) ^ 2"
proof -
  have xn_mem: "x n \<in> S"
    using feasible
    by (rule feasible_iteratesD)

  have step_mem: "gradient_step alpha G (x n) \<in> S"
    using gd feasible
    by (rule gradient_descent_step_mem)

  have step_eq: "x (Suc n) = gradient_step alpha G (x n)"
    using gd
    by (rule gradient_descent_iteratesD)

  have bound:
    "f (gradient_step alpha G (x n))
      \<le> f (x n) - alpha * norm (G (x n)) ^ 2
          + (L / 2) * alpha ^ 2 * norm (G (x n)) ^ 2"
    using smooth_upper_bound_gradient_step[OF smooth xn_mem step_mem] .

  show ?thesis
    using bound step_eq
    by simp
qed

lemma gradient_descent_one_step_decrease:
  assumes smooth: "smooth_upper_bound_on L S f G"
    and gd: "gradient_descent_iterates alpha G x"
    and feasible: "feasible_iterates S x"
    and alpha_nonneg: "0 \<le> alpha"
    and step_size: "alpha * L \<le> 1"
  shows
    "f (x (Suc n))
      \<le> f (x n) - (alpha / 2) * norm (G (x n)) ^ 2"
proof -
  have xn_mem: "x n \<in> S"
    using feasible
    by (rule feasible_iteratesD)

  have step_mem: "gradient_step alpha G (x n) \<in> S"
    using gd feasible
    by (rule gradient_descent_step_mem)

  have step_eq: "x (Suc n) = gradient_step alpha G (x n)"
    using gd
    by (rule gradient_descent_iteratesD)

  have decrease:
    "f (gradient_step alpha G (x n))
      \<le> f (x n) - (alpha / 2) * norm (G (x n)) ^ 2"
    using smooth_upper_bound_gradient_step_decrease[
      OF smooth xn_mem step_mem alpha_nonneg step_size] .

  show ?thesis
    using decrease step_eq
    by simp
qed

lemma gradient_descent_objective_mono_step:
  assumes smooth: "smooth_upper_bound_on L S f G"
    and gd: "gradient_descent_iterates alpha G x"
    and feasible: "feasible_iterates S x"
    and alpha_nonneg: "0 \<le> alpha"
    and step_size: "alpha * L \<le> 1"
  shows "f (x (Suc n)) \<le> f (x n)"
proof -
  have decrease:
    "f (x (Suc n))
      \<le> f (x n) - (alpha / 2) * norm (G (x n)) ^ 2"
    using gradient_descent_one_step_decrease[
      OF smooth gd feasible alpha_nonneg step_size] .

  have nonneg:
    "0 \<le> (alpha / 2) * norm (G (x n)) ^ 2"
  proof -
    have "0 \<le> alpha / 2"
      using alpha_nonneg
      by simp

    moreover have "0 \<le> norm (G (x n)) ^ 2"
      by simp

    ultimately show ?thesis
      by (rule mult_nonneg_nonneg)
  qed

  show ?thesis
    using decrease nonneg
    by linarith
qed

lemma gradient_descent_objective_nonincreasing:
  assumes smooth: "smooth_upper_bound_on L S f G"
    and gd: "gradient_descent_iterates alpha G x"
    and feasible: "feasible_iterates S x"
    and alpha_nonneg: "0 \<le> alpha"
    and step_size: "alpha * L \<le> 1"
  shows "nonincreasing_sequence (objective_values f x)"
proof (rule nonincreasing_sequenceI)
  fix n
  show "objective_values f x (Suc n) \<le> objective_values f x n"
    using gradient_descent_objective_mono_step[
      OF smooth gd feasible alpha_nonneg step_size, of n]
    by simp
qed

lemma gradient_descent_step_progress:
  assumes smooth: "smooth_upper_bound_on L S f G"
    and gd: "gradient_descent_iterates alpha G x"
    and feasible: "feasible_iterates S x"
    and alpha_nonneg: "0 \<le> alpha"
    and step_size: "alpha * L \<le> 1"
  shows
    "(alpha / 2) * norm (G (x n)) ^ 2
      \<le> f (x n) - f (x (Suc n))"
proof -
  have decrease:
    "f (x (Suc n))
      \<le> f (x n) - (alpha / 2) * norm (G (x n)) ^ 2"
    using gradient_descent_one_step_decrease[
      OF smooth gd feasible alpha_nonneg step_size] .

  show ?thesis
    using decrease
    by linarith
qed


subsection \<open>Locale form\<close>

locale gradient_descent =
  smooth_convex S f G L
  for S :: "'a::real_inner set"
    and f :: "'a \<Rightarrow> real"
    and G :: "'a \<Rightarrow> 'a"
    and L :: real +
  fixes alpha :: real
    and x :: "nat \<Rightarrow> 'a"
  assumes iterates: "gradient_descent_iterates alpha G x"
    and feasible: "feasible_iterates S x"
    and alpha_nonneg: "0 \<le> alpha"
    and step_size: "alpha * L \<le> 1"
begin

lemma iterate:
  "x (Suc n) = gradient_step alpha G (x n)"
  using iterates
  by (rule gradient_descent_iteratesD)

lemma iterate_mem:
  "x n \<in> S"
  using feasible
  by (rule feasible_iteratesD)

lemma step_mem:
  "gradient_step alpha G (x n) \<in> S"
  using iterates feasible
  by (rule gradient_descent_step_mem)

lemma one_step_bound:
  "f (x (Suc n))
    \<le> f (x n) - alpha * norm (G (x n)) ^ 2
        + (L / 2) * alpha ^ 2 * norm (G (x n)) ^ 2"
  using gradient_descent_one_step_bound[OF smooth_bound iterates feasible] .

lemma one_step_decrease:
  "f (x (Suc n))
    \<le> f (x n) - (alpha / 2) * norm (G (x n)) ^ 2"
  using gradient_descent_one_step_decrease[
    OF smooth_bound iterates feasible alpha_nonneg step_size] .

lemma objective_mono_step:
  "f (x (Suc n)) \<le> f (x n)"
  using gradient_descent_objective_mono_step[
    OF smooth_bound iterates feasible alpha_nonneg step_size] .

lemma objective_nonincreasing:
  "nonincreasing_sequence (objective_values f x)"
  using gradient_descent_objective_nonincreasing[
    OF smooth_bound iterates feasible alpha_nonneg step_size] .

lemma step_progress:
  "(alpha / 2) * norm (G (x n)) ^ 2
    \<le> f (x n) - f (x (Suc n))"
  using gradient_descent_step_progress[
    OF smooth_bound iterates feasible alpha_nonneg step_size] .

end

text \<open>
This file turns the pointwise gradient-step descent estimates into sequence
statements for gradient descent.

The main consequence is that, under the smooth upper-bound assumption and the
standard step-size condition that alpha * L is at most one, the objective values along a
feasible gradient descent sequence form a nonincreasing sequence.
\<close>

end