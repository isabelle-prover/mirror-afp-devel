theory Busy_Beaver_Base
  imports Main
begin

section \<open>The Busy Beaver Upper-Bound Principle\<close>

text \<open>
  Radó's Busy Beaver function measures the largest halting time among machines
  of bounded size \<^cite>\<open>Rado1962\<close>.  This theory formalizes the Busy Beaver
  upper-bound principle over a model-parametric notion of programs with a finite
  size measure and unique exact halting times.

  The base locale defines the Busy Beaver time function for zero-input runs and
  proves that any total upper bound for it decides the corresponding fixed-input
  halting predicate.  A second locale adds a generic computability interface:
  noncomputability follows from an assumed absence of computable fixed-input
  halting deciders, and eventual domination is derived under an explicit witness
  assumption that packages the usual input-to-program compilation argument.  A
  separate theory instantiates the base locale with AFP's Turing machines and,
  by treating program/input pairs as Busy Beaver objects, obtains a concrete
  upper-bound decider for AFP's two-argument halting problem together with an
  explicit Turing-noncomputability consequence for the induced characteristic
  functions.
\<close>


subsection \<open>Base model and Busy Beaver time\<close>

locale busy_beaver_base =
  fixes size :: "'prog \<Rightarrow> nat"
    and halts_in :: "'prog \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  assumes finite_size_le: "finite {p. size p \<le> n}"
    and halting_time_unique:
      "halts_in p x t \<Longrightarrow> halts_in p x u \<Longrightarrow> t = u"
begin

definition halts :: "'prog \<Rightarrow> nat \<Rightarrow> bool" where
  "halts p x \<longleftrightarrow> (\<exists>t. halts_in p x t)"

definition halting_time :: "'prog \<Rightarrow> nat \<Rightarrow> nat" where
  "halting_time p x = (THE t. halts_in p x t)"

definition time_set :: "nat \<Rightarrow> nat set" where
  "time_set n = {t. \<exists>p. size p \<le> n \<and> halts_in p 0 t}"

definition BB_time :: "nat \<Rightarrow> nat" where
  "BB_time n = Max (insert 0 (time_set n))"

definition upper_bound_for_BB :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "upper_bound_for_BB b \<longleftrightarrow> (\<forall>n. BB_time n \<le> b n)"

definition halting_decider_from :: "(nat \<Rightarrow> nat) \<Rightarrow> 'prog \<Rightarrow> nat \<Rightarrow> bool" where
  "halting_decider_from b p x \<longleftrightarrow> (\<exists>t\<le>b (size p). halts_in p x t)"

lemma halting_time_eq:
  assumes "halts_in p x t"
  shows "halting_time p x = t"
  unfolding halting_time_def
  using assms halting_time_unique by blast

lemma finite_time_set [simp]: "finite (time_set n)"
proof -
  let ?A = "{p. size p \<le> n \<and> halts p 0}"
  have A_finite: "finite ?A"
    by (simp add: finite_size_le)
  have "time_set n \<subseteq> (\<lambda>p. halting_time p 0) ` ?A"
  proof
    fix t
    assume "t \<in> time_set n"
    then obtain p where p: "size p \<le> n" and t: "halts_in p 0 t"
      by (auto simp: time_set_def)
    have "halts p 0"
      using t by (auto simp: halts_def)
    moreover have "halting_time p 0 = t"
      using halting_time_eq[OF t] .
    ultimately show "t \<in> (\<lambda>p. halting_time p 0) ` ?A"
      using p by auto
  qed
  moreover have "finite ((\<lambda>p. halting_time p 0) ` ?A)"
    using A_finite by simp
  ultimately show ?thesis
    by (rule finite_subset)
qed

lemma finite_insert_time_set [simp]: "finite (insert 0 (time_set n))"
  by simp

lemma BB_time_ge_time:
  assumes "size p \<le> n"
    and "halts_in p 0 t"
  shows "t \<le> BB_time n"
proof -
  have fin: "finite (insert 0 (time_set n))"
    by simp
  have mem: "t \<in> insert 0 (time_set n)"
    using assms by (auto simp: time_set_def)
  show ?thesis
    unfolding BB_time_def using Max_ge[OF fin mem] .
qed

lemma BB_time_upper_bound:
  assumes "\<And>p t. size p \<le> n \<Longrightarrow> halts_in p 0 t \<Longrightarrow> t \<le> B"
  shows "BB_time n \<le> B"
proof -
  have fin: "finite (insert 0 (time_set n))"
    by simp
  have nonempty: "insert 0 (time_set n) \<noteq> {}"
    by simp
  have bound: "\<And>t. t \<in> insert 0 (time_set n) \<Longrightarrow> t \<le> B"
    using assms by (auto simp: time_set_def)
  show ?thesis
    by (simp add: BB_time_def bound)
qed

lemma halting_decider_from_sound:
  assumes "halting_decider_from b p x"
  shows "halts p x"
  using assms by (auto simp: halting_decider_from_def halts_def)

lemma halting_decider_from_complete_0:
  assumes ub: "upper_bound_for_BB b"
  assumes "halts p 0"
  shows "halting_decider_from b p 0"
proof -
  obtain t where t: "halts_in p 0 t"
    using assms by (auto simp: halts_def)
  have "t \<le> BB_time (size p)"
    using BB_time_ge_time[of p "size p" t] t by simp
  also have "\<dots> \<le> b (size p)"
    using ub by (simp add: upper_bound_for_BB_def)
  finally show ?thesis
    using t by (auto simp: halting_decider_from_def)
qed

theorem halting_decider_from_correct_0:
  assumes "upper_bound_for_BB b"
  shows "halting_decider_from b p 0 \<longleftrightarrow> halts p 0"
  using halting_decider_from_sound halting_decider_from_complete_0[OF assms]
  by blast

lemma BB_time_is_upper_bound: "upper_bound_for_BB BB_time"
  by (simp add: upper_bound_for_BB_def)

end


subsection \<open>Computability consequences\<close>

text \<open>
  The following locale deliberately keeps computability assumptions explicit.
  In particular, eventual domination is not derived from finite size classes and
  exact halting times alone; the assumption \<open>computable_has_busy_witness\<close>
  states the compilation witness needed to turn values of a computed function
  into sufficiently long zero-input halting computations.
\<close>

locale busy_beaver_model = busy_beaver_base size halts_in
  for size :: "'prog \<Rightarrow> nat"
    and halts_in :: "'prog \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" +
  fixes computes :: "'prog \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool"
  assumes compute_halts:
      "computes p f \<Longrightarrow> \<exists>t. halts_in p x t"
    and computable_has_busy_witness:
      "computes p f \<Longrightarrow> \<exists>N. \<forall>n\<ge>N.
        \<exists>q t. size q \<le> n \<and> halts_in q 0 t \<and> f n \<le> t"
begin

definition computable :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "computable f \<longleftrightarrow> (\<exists>p. computes p f)"

definition eventually_dominates :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "eventually_dominates g f \<longleftrightarrow> (\<exists>N. \<forall>n\<ge>N. f n \<le> g n)"

lemma no_computable_upper_bound_if_halting_undecidable:
  assumes no_decider:
    "\<And>b. computable b \<Longrightarrow>
      \<not> (\<forall>p. halting_decider_from b p 0 \<longleftrightarrow> halts p 0)"
  shows "\<not> (\<exists>b. computable b \<and> upper_bound_for_BB b)"
  using halting_decider_from_correct_0 no_decider by blast

theorem BB_time_not_computable_if_halting_undecidable:
  assumes no_decider:
    "\<And>b. computable b \<Longrightarrow>
      \<not> (\<forall>p. halting_decider_from b p 0 \<longleftrightarrow> halts p 0)"
  shows "\<not> computable BB_time"
  using BB_time_is_upper_bound no_computable_upper_bound_if_halting_undecidable no_decider
  by blast

lemma BB_time_dominates_computed_function_from_size:
  assumes comp: "computes p f"
  shows "eventually_dominates BB_time f"
proof -
  obtain N where "\<forall>n\<ge>N. \<exists>q t. size q \<le> n \<and> halts_in q 0 t \<and> f n \<le> t"
    using computable_has_busy_witness[OF comp] by blast
  then have "\<forall>n\<ge>N. f n \<le> BB_time n"
    by (meson BB_time_ge_time order.trans)
  then show ?thesis
    by (auto simp: eventually_dominates_def)
qed

theorem BB_time_eventually_dominates_computable:
  assumes "computable f"
  shows "eventually_dominates BB_time f"
  using assms BB_time_dominates_computed_function_from_size
  by (auto simp: computable_def)

end

end
