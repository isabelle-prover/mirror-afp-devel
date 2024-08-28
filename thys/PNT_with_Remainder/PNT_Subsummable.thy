theory PNT_Subsummable
imports
  "PNT_Remainder_Library"
begin
unbundle pnt_notation

definition has_subsum where "has_subsum f S x \<equiv> (\<lambda>n. if n \<in> S then f n else 0) sums x"
definition subsum where "subsum f S \<equiv> \<Sum>n. if n \<in> S then f n else 0"
definition subsummable (infix "subsummable" 50)
  where "f subsummable S \<equiv> summable (\<lambda>n. if n \<in> S then f n else 0)"

syntax "_subsum" :: "pttrn \<Rightarrow> nat set \<Rightarrow> 'a \<Rightarrow> 'a"
  ("(2\<Sum>`_ \<in> (_)./ _)" [0, 0, 10] 10)
syntax_consts "_subsum" == subsum
translations
  "\<Sum>` x\<in>S. t" => "CONST subsum (\<lambda>x. t) S"

syntax "_subsum_prop" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a"
  ("(2\<Sum>`_ | (_)./ _)" [0, 0, 10] 10)
syntax_consts "_subsum_prop" == subsum
translations
  "\<Sum>` x|P. t" => "CONST subsum (\<lambda>x. t) {x. P}"

syntax "_subsum_ge" :: "pttrn \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a"
  ("(2\<Sum>`_ \<ge> _./ _)" [0, 0, 10] 10)
syntax_consts "_subsum_ge" == subsum
translations
  "\<Sum>` x\<ge>n. t" => "CONST subsum (\<lambda>x. t) {n..}"

lemma has_subsum_finite:
  "finite F \<Longrightarrow> has_subsum f F (sum f F)"
  unfolding has_subsum_def by (rule sums_If_finite_set)

lemma has_subsum_If_finite_set:
  assumes "finite F"
  shows "has_subsum (\<lambda>n. if n \<in> F then f n else 0) A (sum f (F \<inter> A))"
proof -
  have "F \<inter> A = {x. x \<in> A \<and> x \<in> F}" by auto
  thus ?thesis unfolding has_subsum_def using assms
    by (auto simp add: if_if_eq_conj intro!: sums_If_finite)
qed

lemma has_subsum_If_finite:
  assumes "finite {n \<in> A. p n}"
  shows "has_subsum (\<lambda>n. if p n then f n else 0) A (sum f {n \<in> A. p n})"
unfolding has_subsum_def using assms
  by (auto simp add: if_if_eq_conj intro!: sums_If_finite)

lemma has_subsum_univ:
  "f sums v \<Longrightarrow> has_subsum f UNIV v" 
  unfolding has_subsum_def by auto

lemma subsumI:
  fixes f :: "nat \<Rightarrow> 'a :: {t2_space, comm_monoid_add}"
  shows "has_subsum f A x \<Longrightarrow> x = subsum f A"
  unfolding has_subsum_def subsum_def by (intro sums_unique)

lemma has_subsum_summable:
  "has_subsum f A x \<Longrightarrow> f subsummable A"
  unfolding has_subsum_def subsummable_def by (rule sums_summable)

lemma subsummable_sums:
  fixes f :: "nat \<Rightarrow> 'a :: {comm_monoid_add, t2_space}"
  shows "f subsummable S \<Longrightarrow> has_subsum f S (subsum f S)"
  unfolding subsummable_def has_subsum_def subsum_def by (intro summable_sums)

lemma has_subsum_diff_finite:
  fixes S :: "'a :: {topological_ab_group_add, t2_space}"
  assumes "finite F" "has_subsum f A S" "F \<subseteq> A"
  shows "has_subsum f (A - F) (S - sum f F)"
proof -
  define p where "p n \<equiv> if n \<in> F then 0 else (if n \<in> A then f n else 0)" for n
  define q where "q n \<equiv> if n \<in> A - F then f n else 0" for n
  have "F \<inter> A = F" using assms(3) by auto
  hence "p sums (S - sum f F)"
    using assms unfolding p_def has_subsum_def
    by (auto intro: sums_If_finite_set' [where ?S = S]
             simp: sum_negf sum.inter_restrict [symmetric])
  moreover have "p = q" unfolding p_def q_def by auto
  finally show ?thesis unfolding q_def has_subsum_def by auto
qed

lemma subsum_split:
  fixes f :: "nat \<Rightarrow> 'a :: {topological_ab_group_add, t2_space}"
  assumes "f subsummable A" "finite F" "F \<subseteq> A"
  shows "subsum f A = sum f F + subsum f (A - F)"
proof -
  from assms(1) have "has_subsum f A (subsum f A)" by (intro subsummable_sums)
  hence "has_subsum f (A - F) (subsum f A - sum f F)"
    using assms by (intro has_subsum_diff_finite)
  hence "subsum f A - sum f F = subsum f (A - F)" by (rule subsumI)
  thus ?thesis by (auto simp add: algebra_simps)
qed

lemma has_subsum_zero [simp]: "has_subsum (\<lambda>n. 0) A 0" unfolding has_subsum_def by auto
lemma zero_subsummable [simp]: "(\<lambda>n. 0) subsummable A" unfolding subsummable_def by auto
lemma zero_subsum [simp]: "(\<Sum>`n\<in>A. 0 :: 'a :: {comm_monoid_add, t2_space}) = 0" unfolding subsum_def by auto

lemma has_subsum_minus:
  fixes f :: "nat \<Rightarrow> 'a :: real_normed_vector"
  assumes "has_subsum f A a" "has_subsum g A b"
  shows "has_subsum (\<lambda>n. f n - g n) A (a - b)"
proof -
  define p where "p n = (if n \<in> A then f n else 0)" for n
  define q where "q n = (if n \<in> A then g n else 0)" for n
  have "(\<lambda>n. p n - q n) sums (a - b)"
    using assms unfolding p_def q_def has_subsum_def by (intro sums_diff)
  moreover have "(if n \<in> A then f n - g n else 0) = p n - q n" for n
    unfolding p_def q_def by auto
  ultimately show ?thesis unfolding has_subsum_def by auto
qed

lemma subsum_minus:
  assumes "f subsummable A" "g subsummable A"
  shows "subsum f A - subsum g A = (\<Sum>`n\<in>A. f n - g n :: 'a :: real_normed_vector)"
  by (intro subsumI has_subsum_minus subsummable_sums assms)

lemma subsummable_minus:
  assumes "f subsummable A" "g subsummable A"
  shows "(\<lambda>n. f n - g n :: 'a :: real_normed_vector) subsummable A"
  by (auto intro: has_subsum_summable has_subsum_minus subsummable_sums assms)

lemma has_subsum_uminus:
  assumes "has_subsum f A a"
  shows "has_subsum (\<lambda>n. - f n :: 'a :: real_normed_vector) A (- a)"
proof -
  have "has_subsum (\<lambda>n. 0 - f n) A (0 - a)"
    by (intro has_subsum_minus) (use assms in auto)
  thus ?thesis by auto
qed

lemma subsum_uminus:
  "f subsummable A \<Longrightarrow> - subsum f A = (\<Sum>`n\<in>A. - f n :: 'a :: real_normed_vector)"
  by (intro subsumI has_subsum_uminus subsummable_sums)

lemma subsummable_uminus:
  "f subsummable A \<Longrightarrow> (\<lambda>n. - f n :: 'a :: real_normed_vector) subsummable A"
  by (auto intro: has_subsum_summable has_subsum_uminus subsummable_sums)

lemma has_subsum_add:
  fixes f :: "nat \<Rightarrow> 'a :: real_normed_vector"
  assumes "has_subsum f A a" "has_subsum g A b"
  shows "has_subsum (\<lambda>n. f n + g n) A (a + b)"
proof -
  have "has_subsum (\<lambda>n. f n - - g n) A (a - - b)"
    by (intro has_subsum_minus has_subsum_uminus assms)
  thus ?thesis by auto
qed

lemma subsum_add:
  assumes "f subsummable A" "g subsummable A"
  shows "subsum f A + subsum g A = (\<Sum>`n\<in>A. f n + g n :: 'a :: real_normed_vector)"
  by (intro subsumI has_subsum_add subsummable_sums assms)

lemma subsummable_add:
  assumes "f subsummable A" "g subsummable A"
  shows "(\<lambda>n. f n + g n :: 'a :: real_normed_vector) subsummable A"
  by (auto intro: has_subsum_summable has_subsum_add subsummable_sums assms)

lemma subsum_cong:
  "(\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> subsum f A = subsum g A"
  unfolding subsum_def by (intro suminf_cong) auto

lemma subsummable_cong:
  fixes f :: "nat \<Rightarrow> 'a :: real_normed_vector"
  shows "(\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> (f subsummable A) = (g subsummable A)"
  unfolding subsummable_def by (intro summable_cong) auto

lemma subsum_norm_bound:
  fixes f :: "nat \<Rightarrow> 'a :: banach"
  assumes "g subsummable A" "\<And>n. n \<in> A \<Longrightarrow> \<parallel>f n\<parallel> \<le> g n"
  shows "\<parallel>subsum f A\<parallel> \<le> subsum g A"
  using assms unfolding subsummable_def subsum_def
  by (intro suminf_norm_bound) auto

lemma eval_fds_subsum:
  fixes f :: "'a :: {nat_power, banach, real_normed_field} fds"
  assumes "fds_converges f s"
  shows "has_subsum (\<lambda>n. fds_nth f n / nat_power n s) {1..} (eval_fds f s)"
proof -
  let ?f = "\<lambda>n. fds_nth f n / nat_power n s"
  let ?v = "eval_fds f s"
  have "has_subsum (\<lambda>n. ?f n) UNIV ?v"
    by (intro has_subsum_univ fds_converges_iff [THEN iffD1] assms)
  hence "has_subsum ?f (UNIV - {0}) (?v - sum ?f {0})"
    by (intro has_subsum_diff_finite) auto
  moreover have "UNIV - {0 :: nat} = {1..}" by auto
  ultimately show ?thesis by auto
qed

lemma fds_abs_subsummable:
  fixes f :: "'a :: {nat_power, banach, real_normed_field} fds"
  assumes "fds_abs_converges f s"
  shows "(\<lambda>n. \<parallel>fds_nth f n / nat_power n s\<parallel>) subsummable {1..}"
proof -
  have "summable (\<lambda>n. \<parallel>fds_nth f n / nat_power n s\<parallel>)"
    by (subst fds_abs_converges_def [symmetric]) (rule assms)
  moreover have "\<parallel>fds_nth f n / nat_power n s\<parallel> = 0" when "\<not> 1 \<le> n" for n
  proof -
    have "n = 0" using that by auto
    thus ?thesis by auto
  qed
  hence "(\<lambda>n. if 1 \<le> n then \<parallel>fds_nth f n / nat_power n s\<parallel> else 0)
       = (\<lambda>n. \<parallel>fds_nth f n / nat_power n s\<parallel>)" by auto
  ultimately show ?thesis unfolding subsummable_def by auto
qed

lemma subsum_mult2:
  fixes f :: "nat \<Rightarrow> 'a :: real_normed_algebra"
  shows "f subsummable A \<Longrightarrow> (\<Sum>`x\<in>A. f x * c) = subsum f A * c"
unfolding subsum_def subsummable_def
  by (subst suminf_mult2) (auto intro: suminf_cong)

lemma subsummable_mult2:
  fixes f :: "nat \<Rightarrow> 'a :: real_normed_algebra"
  assumes "f subsummable A"
  shows "(\<lambda>x. f x * c) subsummable A"
proof -
  have "summable (\<lambda>n. (if n \<in> A then f n else 0) * c)" (is ?P)
    using assms unfolding subsummable_def by (intro summable_mult2)
  moreover have "?P = ?thesis"
    unfolding subsummable_def by (rule summable_cong) auto
  ultimately show ?thesis by auto
qed

lemma subsum_ge_limit:
  "lim (\<lambda>N. \<Sum>n = m..N. f n) = (\<Sum>`n \<ge> m. f n)"
proof -
  define g where "g n \<equiv> if n \<in> {m..} then f n else 0" for n
  have "(\<Sum>n. g n) = lim (\<lambda>N. \<Sum>n<N. g n)" by (rule suminf_eq_lim)
  also have "\<dots> = lim (\<lambda>N. \<Sum>n<N + 1. g n)"
    unfolding lim_def using LIMSEQ_ignore_initial_segment LIMSEQ_offset
    by (intro The_cong iffI) blast
  also have "\<dots> = lim (\<lambda>N. \<Sum>n = m..N. f n)"
  proof -
    have "{x. x < N + 1 \<and> m \<le> x} = {m..N}" for N by auto
    thus ?thesis unfolding g_def by (subst sum.inter_filter [symmetric]) auto
  qed
  finally show ?thesis unfolding subsum_def g_def by auto
qed

lemma has_subsum_ge_limit:
  fixes f :: "nat \<Rightarrow> 'a :: {t2_space, comm_monoid_add, topological_space}"
  assumes "((\<lambda>N. \<Sum>n = m..N. f n) \<longlongrightarrow> l) at_top"
  shows "has_subsum f {m..} l"
proof -
  define g where "g n \<equiv> if n \<in> {m..} then f n else 0" for n
  have "((\<lambda>N. \<Sum>n<N + 1. g n) \<longlongrightarrow> l) at_top"
  proof -
    have "{x. x < N + 1 \<and> m \<le> x} = {m..N}" for N by auto
    with assms show ?thesis
      unfolding g_def by (subst sum.inter_filter [symmetric]) auto
  qed
  hence "((\<lambda>N. \<Sum>n<N. g n) \<longlongrightarrow> l) at_top" by (rule LIMSEQ_offset)
  thus ?thesis unfolding has_subsum_def sums_def g_def by auto
qed

lemma eval_fds_complex:
  fixes f :: "complex fds"
  assumes "fds_converges f s"
  shows "has_subsum (\<lambda>n. fds_nth f n / n nat_powr s) {1..} (eval_fds f s)"
proof -
  have "has_subsum (\<lambda>n. fds_nth f n / nat_power n s) {1..} (eval_fds f s)"
    by (intro eval_fds_subsum assms)
  thus ?thesis unfolding nat_power_complex_def .
qed

lemma eval_fds_complex_subsum:
  fixes f :: "complex fds"
  assumes "fds_converges f s"
  shows "eval_fds f s = (\<Sum>`n \<ge> 1. fds_nth f n / n nat_powr s)"
        "(\<lambda>n. fds_nth f n / n nat_powr s) subsummable {1..}"
proof (goal_cases)
  case 1 show ?case by (intro subsumI eval_fds_complex assms)
  case 2 show ?case by (intro has_subsum_summable) (rule eval_fds_complex assms)+
qed

lemma has_sum_imp_has_subsum:
  fixes x :: "'a :: {comm_monoid_add, t2_space}"
  assumes "(f has_sum x) A"
  shows "has_subsum f A x"
proof -
  have "(\<forall>\<^sub>F x in at_top. sum f ({..<x} \<inter> A) \<in> S)"
    when "open S" "x \<in> S" for S
  proof -
    have "\<forall>S. open S \<longrightarrow> x \<in> S \<longrightarrow> (\<forall>\<^sub>F x in finite_subsets_at_top A. sum f x \<in> S)"
      using assms unfolding has_sum_def tendsto_def .
    hence "\<forall>\<^sub>F x in finite_subsets_at_top A. sum f x \<in> S" using that by auto
    then obtain X where hX: "finite X" "X \<subseteq> A"
      and hY: "\<And>Y. finite Y \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> Y \<subseteq> A \<Longrightarrow> sum f Y \<in> S"
      unfolding eventually_finite_subsets_at_top by metis
    define n where "n \<equiv> Max X + 1"
    show ?thesis
    proof (subst eventually_sequentially, standard, safe)
      fix m assume Hm: "n \<le> m"
      moreover have "x \<in> X \<Longrightarrow> x < n" for x
        unfolding n_def using Max_ge [OF hX(1), of x] by auto
      ultimately show "sum f ({..<m} \<inter> A) \<in> S"
        using hX(2) by (intro hY, auto) (metis order.strict_trans2)
    qed
  qed
  thus ?thesis unfolding has_subsum_def sums_def tendsto_def
    by (simp add: sum.inter_restrict [symmetric])
qed

unbundle no_pnt_notation
end
