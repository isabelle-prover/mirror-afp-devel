section \<open>Preliminary Results\<close>

text \<open>This section contains various short preliminary results used in the sections below.\<close>

theory Distributed_Distinct_Elements_Preliminary
  imports
    Frequency_Moments.Frequency_Moments_Preliminary_Results
    Frequency_Moments.Product_PMF_Ext
    Median_Method.Median
    Expander_Graphs.Extra_Congruence_Method
    Expander_Graphs.Constructive_Chernoff_Bound
    Frequency_Moments.Landau_Ext
    Stirling_Formula.Stirling_Formula
begin

unbundle intro_cong_syntax

text \<open>Simplified versions of measure theoretic results for pmfs:\<close>

lemma measure_pmf_cong:
  assumes "\<And>x. x \<in> set_pmf p \<Longrightarrow> x \<in> P \<longleftrightarrow> x \<in> Q"
  shows "measure (measure_pmf p) P = measure (measure_pmf p)  Q"
  using assms
  by (intro finite_measure.finite_measure_eq_AE AE_pmfI) auto

lemma pmf_mono:
  assumes "\<And>x. x \<in> set_pmf p \<Longrightarrow> x \<in> P \<Longrightarrow> x \<in> Q"
  shows "measure (measure_pmf p) P \<le> measure (measure_pmf p) Q"
proof -
  have "measure (measure_pmf p) P = measure (measure_pmf p) (P \<inter> (set_pmf p))"
    by (intro measure_pmf_cong) auto
  also have "... \<le> measure (measure_pmf p) Q"
    using assms by (intro finite_measure.finite_measure_mono) auto
  finally show ?thesis by simp
qed

lemma pmf_rev_mono:
  assumes "\<And>x. x \<in> set_pmf p \<Longrightarrow> x \<notin> Q \<Longrightarrow> x \<notin> P"
  shows "measure p P \<le> measure p Q"
  using assms by (intro pmf_mono) blast

lemma pmf_exp_mono:
  fixes f g :: "'a \<Rightarrow> real"
  assumes "integrable (measure_pmf p) f" "integrable (measure_pmf p) g"
  assumes "\<And>x. x \<in> set_pmf p \<Longrightarrow> f x \<le> g x"
  shows "integral\<^sup>L (measure_pmf p) f \<le> integral\<^sup>L (measure_pmf p) g"
  using assms  by (intro integral_mono_AE AE_pmfI) auto

lemma pmf_markov:
  assumes "integrable (measure_pmf p) f" "c > 0"
  assumes "\<And>x. x \<in> set_pmf p \<Longrightarrow> f x \<ge> 0"
  shows "measure p {\<omega>. f \<omega> \<ge> c} \<le> (\<integral>\<omega>. f \<omega> \<partial>p)/ c" (is "?L \<le> ?R")
proof -
  have a:"AE \<omega> in (measure_pmf p). 0 \<le> f \<omega>"
    by (intro AE_pmfI assms(3))
  have b:"{} \<in> measure_pmf.events p"
    unfolding assms(1) by simp

  have "?L = \<P>(\<omega> in (measure_pmf p). f \<omega> \<ge> c)"
    using assms(1) by simp
  also have "... \<le>  ?R"
    by (intro  integral_Markov_inequality_measure[OF _ b] assms a)
  finally show ?thesis by simp
qed

lemma pmf_add:
  assumes  "\<And>x. x \<in> P \<Longrightarrow> x \<in> set_pmf p \<Longrightarrow> x \<in> Q \<or> x \<in> R"
  shows "measure p P \<le> measure p Q + measure p R"
proof -
  have "measure p P \<le> measure p (Q \<union> R)"
    using assms by (intro pmf_mono) blast
  also have "... \<le> measure p Q + measure p R"
    by (rule measure_subadditive, auto)
  finally show ?thesis by simp
qed

lemma pair_pmf_prob_left:
  "measure_pmf.prob (pair_pmf A B) {\<omega>. P (fst \<omega>)} = measure_pmf.prob A {\<omega>. P \<omega>}" (is "?L = ?R")
proof -
  have "?L = measure_pmf.prob (map_pmf fst (pair_pmf A B)) {\<omega>. P \<omega>}"
    by (subst measure_map_pmf) simp
  also have "... = ?R"
    by (subst map_fst_pair_pmf) simp
  finally show ?thesis by simp
qed

lemma pmf_exp_of_fin_function:
  assumes "finite A" "g ` set_pmf p \<subseteq> A"
  shows "(\<integral>\<omega>. f (g \<omega>) \<partial>p) = (\<Sum>y \<in> A. f y * measure p {\<omega>. g \<omega> = y})"
    (is "?L = ?R")
proof -
  have "?L = integral\<^sup>L (map_pmf g p) f"
    using integral_map_pmf assms by simp
  also have "... = (\<Sum>a\<in>A. f a * pmf (map_pmf g p) a)"
    using assms
    by (intro integral_measure_pmf_real) auto
  also have " ... = (\<Sum>y \<in> A. f y * measure p (g -` {y}))"
    unfolding assms(1) by (intro_cong "[\<sigma>\<^sub>2 (*)]" more:sum.cong pmf_map)
  also have "... = ?R"
    by (intro sum.cong) (auto simp add: vimage_def)
  finally show ?thesis by simp
qed

text \<open>Cardinality rules for distinct/ordered pairs of a set without the finiteness constraint - to
use in simplification:\<close>

lemma card_distinct_pairs:
  "card {x \<in> B \<times> B. fst x \<noteq> snd x} = card B^2 - card B" (is "card ?L = ?R")
proof (cases "finite B")
  case True
  include intro_cong_syntax
  have "card ?L = card (B \<times> B - (\<lambda>x. (x,x)) ` B)"
    by (intro arg_cong[where f="card"]) auto
  also have "... = card (B \<times> B) - card ((\<lambda>x. (x,x)) ` B)"
    by (intro card_Diff_subset finite_imageI True image_subsetI) auto
  also have "... = ?R"
    using True by (intro_cong "[\<sigma>\<^sub>2 (-)]" more: card_image)
      (auto simp add:power2_eq_square inj_on_def)
  finally show ?thesis by simp
next
  case False
  then obtain p where p_in: "p \<in> B" by fastforce
  have "False" if "finite ?L"
  proof -
    have "(\<lambda>x. (p,x)) ` (B - {p}) \<subseteq> ?L"
      using p_in by (intro image_subsetI) auto
    hence "finite ((\<lambda>x. (p,x)) ` (B - {p}))"
      using finite_subset that by auto
    hence "finite (B - {p})"
      by (rule finite_imageD) (simp add:inj_on_def)
    hence "finite B"
      by simp
    thus "False" using False by simp
  qed
  hence "infinite ?L" by auto
  hence "card ?L = 0" by simp
  also have "... = ?R"
    using False by simp
  finally show ?thesis by simp
qed

lemma card_ordered_pairs':
  fixes M :: "('a ::linorder) set"
  shows "card {(x,y) \<in> M \<times> M. x < y} = card M * (card M - 1) / 2"
proof (cases "finite M")
  case True
  show ?thesis using card_ordered_pairs[OF True] by linarith
next
  case False
  then obtain p where p_in: "p \<in> M" by fastforce
  let ?f= "(\<lambda>x. if x < p then (x,p) else (p,x))"
  have "False" if "finite {(x,y) \<in> M \<times> M. x < y}" (is "finite ?X")
  proof -
    have "?f ` (M-{p}) \<subseteq> ?X"
      using p_in by (intro image_subsetI) auto
    hence "finite (?f ` (M-{p}))" using that finite_subset by auto
    moreover have "inj_on ?f (M-{p})"
      by (intro inj_onI) (metis Pair_inject)
    ultimately have "finite (M - {p})"
      using finite_imageD by blast
    hence "finite M"
      using finite_insert[where a="p" and A="M-{p}"] by simp
    thus "False" using False by simp
  qed
  hence "infinite ?X" by auto
  then show ?thesis using False by simp
qed

text \<open>The following are versions of the mean value theorem, where the interval endpoints may be
reversed.\<close>

lemma MVT_symmetric:
  assumes "\<And>x. \<lbrakk>min a b \<le> x; x \<le> max a b\<rbrakk> \<Longrightarrow> DERIV f x :> f' x"
  shows "\<exists>z::real. min a b \<le> z \<and> z \<le> max a b \<and> (f b - f a = (b - a) * f' z)"
proof -
  consider (a) "a < b" | (b) "a = b" | (c) "a > b"
    by argo
  then show ?thesis
  proof (cases)
    case a
    then obtain z :: real where r: "a < z" "z < b" "f b - f a = (b - a) * f' z"
      using assms MVT2[where a="a" and b="b" and f="f" and f'="f'"] by auto
    have "a \<le> z" "z \<le> b" using r(1,2) by auto
    thus ?thesis using a r(3) by auto
  next
    case b
    then show ?thesis by auto
  next
    case c
    then obtain z :: real where r: "b < z" "z < a" "f a - f b = (a - b) * f' z"
      using assms MVT2[where a="b" and b="a" and f="f" and f'="f'"] by auto
    have "f b - f a = (b-a) * f' z" using r by argo
    moreover have "b \<le> z" "z \<le> a" using r(1,2) by auto
    ultimately show ?thesis using c by auto
  qed
qed

lemma MVT_interval:
  fixes I :: "real set"
  assumes "interval I" "a \<in> I" "b \<in> I"
  assumes "\<And>x. x \<in> I \<Longrightarrow> DERIV f x :> f' x"
  shows "\<exists>z. z \<in> I \<and> (f b - f a = (b - a) * f' z)"
proof -
  have a:"min a b \<in> I"
    using assms(2,3) by (cases "a < b") auto
  have b:"max a b \<in> I"
    using assms(2,3) by (cases "a < b") auto
  have c:"x \<in> {min a b..max a b} \<Longrightarrow> x \<in> I" for x
    using interval_def assms(1) a b by auto
  have "\<lbrakk>min a b \<le> x; x \<le> max a b\<rbrakk> \<Longrightarrow> DERIV f x :> f' x" for x
    using c assms(4) by auto
  then obtain z where z:"z \<ge> min a b" "z \<le> max a b" "f b - f a = (b-a) * f' z"
    using MVT_symmetric by blast
  have "z \<in> I"
    using c z(1,2) by auto
  thus ?thesis using z(3) by auto
qed

text \<open>Ln is monotone on the positive numbers and thus commutes with min and max:\<close>
lemma ln_min_swap:
  "x > (0::real) \<Longrightarrow> (y > 0) \<Longrightarrow> ln (min x y) = min (ln x) (ln y)"
  using ln_less_cancel_iff by fastforce

lemma ln_max_swap:
  "x > (0::real) \<Longrightarrow> (y > 0) \<Longrightarrow> ln (max x y) = max (ln x) (ln y)"
  using ln_le_cancel_iff by fastforce

text \<open>Loose lower bounds for the factorial fuction:.\<close>

lemma fact_lower_bound:
  "sqrt(2*pi*n)*(n/exp(1))^n \<le> fact n" (is "?L \<le> ?R")
proof (cases "n > 0")
  case True
  have "ln ?L = ln (2*pi*n)/2 + n * ln n - n"
    using True by (simp add: ln_mult ln_sqrt ln_realpow ln_div algebra_simps)
  also have "... \<le> ln ?R"
    by (intro Stirling_Formula.ln_fact_bounds True)
  finally show ?thesis
    using iffD1[OF ln_le_cancel_iff] True by simp
next
  case False
  then show ?thesis by simp
qed

lemma fact_lower_bound_1:
  assumes "n > 0"
  shows "(n/exp 1)^n \<le> fact n" (is "?L \<le> ?R")
proof -
  have "2 * pi \<ge> 1" using pi_ge_two by auto
  moreover have "n \<ge> 1" using assms by simp
  ultimately have "2 * pi * n \<ge> 1*1"
    by (intro mult_mono) auto
  hence a:"2 * pi * n \<ge> 1" by simp

  have "?L = 1 * ?L" by simp
  also have "... \<le> sqrt(2 * pi * n) * ?L"
    using a by (intro mult_right_mono) auto
  also have "... \<le> ?R"
    using fact_lower_bound by simp
  finally show ?thesis by simp
qed

text \<open>Rules to handle O-notation with multiple variables, where some filters may be towards zero:\<close>

lemma real_inv_at_right_0_inf:
  "\<forall>\<^sub>F x in at_right (0::real). c \<le> 1 / x"
proof -
  have "c \<le> 1 /  x" if b:" x \<in> {0<..<1 / (max c 1)}" for x
  proof -
    have "c * x \<le> (max c 1) * x"
      using b by (intro mult_right_mono, linarith, auto)
    also have "... \<le> (max c 1)  * (1 / (max c 1))"
      using b by (intro mult_left_mono) auto
    also have "... \<le> 1"
      by (simp add:of_rat_divide)
    finally have "c * x \<le> 1" by simp
    moreover have "0 < x"
      using b by simp
    ultimately show ?thesis by (subst pos_le_divide_eq, auto)
  qed
  thus ?thesis
    by (intro eventually_at_rightI[where b="1/(max c 1)"], simp_all)
qed

lemma bigo_prod_1:
  assumes "(\<lambda>x. f x) \<in> O[F](\<lambda>x. g x)" "G \<noteq> bot"
  shows "(\<lambda>x. f (fst x)) \<in> O[F \<times>\<^sub>F G](\<lambda>x. g (fst x))"
proof -
  obtain c where a: "\<forall>\<^sub>F x in F. norm (f x) \<le> c * norm (g x)" and c_gt_0: "c > 0"
    using assms unfolding bigo_def by auto

  have "\<exists>c>0. \<forall>\<^sub>F x in F \<times>\<^sub>F G. norm (f (fst x)) \<le> c * norm (g (fst x))"
    by (intro exI[where x="c"] conjI c_gt_0  eventually_prod1' a assms(2))
  thus ?thesis
    unfolding bigo_def by simp
qed

lemma bigo_prod_2:
  assumes "(\<lambda>x. f x) \<in> O[G](\<lambda>x. g x)" "F \<noteq> bot"
  shows "(\<lambda>x. f (snd x)) \<in> O[F \<times>\<^sub>F G](\<lambda>x. g (snd x))"
proof -
  obtain c where a: "\<forall>\<^sub>F x in G. norm (f x) \<le> c * norm (g x)" and c_gt_0: "c > 0"
    using assms unfolding bigo_def by auto

  have "\<exists>c>0. \<forall>\<^sub>F x in F \<times>\<^sub>F G. norm (f (snd x)) \<le> c * norm (g (snd x))"
    by (intro exI[where x="c"] conjI c_gt_0  eventually_prod2' a assms(2))
  thus ?thesis
    unfolding bigo_def by simp
qed

lemma eventually_inv:
  fixes P :: "real \<Rightarrow> bool"
  assumes "eventually (\<lambda>x. P (1/x)) at_top "
  shows "eventually (\<lambda>x. P x) (at_right 0)"
proof -
  obtain N where c:"n \<ge> N \<Longrightarrow> P (1/n)" for n
    using assms unfolding eventually_at_top_linorder by auto

  define q where "q = max 1 N"
  have d: "0 < 1 / q" "q > 0"
    unfolding q_def by auto

  have "P x" if "x \<in> {0<..<1 / q}" for x
  proof -
    define n where "n = 1/x"
    have x_eq: "x = 1 / n"
      unfolding n_def using that by simp

    have "N \<le> q" unfolding q_def by simp
    also have "... \<le> n"
      unfolding n_def using that d by (simp add:divide_simps ac_simps)
    finally have "N \<le> n" by simp
    thus ?thesis
      unfolding x_eq by (intro c)
  qed

  thus ?thesis
    by (intro eventually_at_rightI[where b="1/q"] d)
qed

lemma bigo_inv:
  fixes f g :: "real \<Rightarrow> real"
  assumes "(\<lambda>x. f (1/x)) \<in> O(\<lambda>x. g (1/x))"
  shows "f \<in> O[at_right 0](g)"
  using assms eventually_inv unfolding bigo_def by auto

unbundle no_intro_cong_syntax

end