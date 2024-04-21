section \<open>Tutorial on the use of Pseudorandom-Objects\<close>

theory Tutorial_Pseudorandom_Objects
  imports
    Universal_Hash_Families.Pseudorandom_Objects_Hash_Families
    Expander_Graphs.Pseudorandom_Objects_Expander_Walks
    Equivalence_Relation_Enumeration.Equivalence_Relation_Enumeration
    Median_Method.Median
    Concentration_Inequalities.Bienaymes_Identity
    Frequency_Moments.Frequency_Moments
begin

text \<open>This section is a tutorial for the use of pseudorandom objects. Starting from the
approximation algorithm for the second frequency moment by Alon et al.~\cite{alon1999}, we will
improve the solution until we achieve a space complexity of
$\mathcal O(\ln n + \varepsilon^{-2} \ln(\delta^{-1}) \ln m)$, where $n$ denotes the range of the
stream elements, $m$ denotes the length of the stream, $\varepsilon$ denotes the desired accuracy
and $\delta$ denotes the desired failure probability.

The construction relies on a combination of pseudorandom object, in particular an expander walk
and two chained hash families.\<close>

hide_const (open) topological_space_class.discrete
hide_const (open) Abstract_Rewriting.restrict
hide_fact (open) Abstract_Rewriting.restrict_def
hide_fact (open) Henstock_Kurzweil_Integration.integral_cong
hide_fact (open) Henstock_Kurzweil_Integration.integral_mult_right
hide_fact (open) Henstock_Kurzweil_Integration.integral_diff

text \<open>The following lemmas show a one-side and two-sided Chernoff-bound for $\{0,1\}$-valued
independent identically distributed random variables. This to show the similarity with expander
walks, for which similar bounds can be established:
@{thm [source] expander_chernoff_bound_one_sided} and @{thm [source] expander_chernoff_bound}.\<close>

lemma classic_chernoff_bound_one_sided:
  fixes l :: nat
  assumes "AE x in measure_pmf p. f x \<in> {0,1::real}"
  assumes "(\<integral>x. f x \<partial>p) \<le> \<mu>" "l > 0" "\<gamma> \<ge> 0"
  shows "measure (prod_pmf {0..<l} (\<lambda>_. p)) {w. (\<Sum>i<l. f (w i))/l-\<mu>\<ge>\<gamma>} \<le> exp (- 2 * real l * \<gamma>^2)"
    (is "?L \<le> ?R")
proof -
  define \<nu>  where "\<nu> = real l*(\<integral>x. f x \<partial>p)"
  let ?p = "prod_pmf {0..<l} (\<lambda>_. p)"

  have 1: "prob_space.indep_vars (measure_pmf ?p) (\<lambda>_. borel) (\<lambda>i x. f (x i)) {0..<l}"
    by (intro prob_space.indep_vars_compose2[OF _ indep_vars_Pi_pmf] prob_space_measure_pmf) auto

  have "f (y i) \<in> {0..1}" if "y \<in> {0..<l} \<rightarrow>\<^sub>E set_pmf p" "i \<in> {0..<l}" for y i
  proof -
    have "y i \<in> set_pmf p" using that by auto
    thus ?thesis using assms(1) unfolding AE_measure_pmf_iff by auto
  qed
  hence 2: "AE x in measure_pmf ?p. f (x i) \<in> {0..1}"
    if "i \<in> {0..<l}" for i
    using that by (intro AE_pmfI) (auto simp: set_prod_pmf)

  have "(\<Sum>i=0..<l. (\<integral>x. f (x i) \<partial>?p)) = (\<Sum>i<l. (\<integral>x. f x \<partial>map_pmf (\<lambda>x. x i) ?p))"
    by (auto simp:atLeast0LessThan)
  also have "... = (\<Sum>i<l. (\<integral>x. f x \<partial>p))" by (subst Pi_pmf_component) auto
  also have "... = \<nu>" unfolding \<nu>_def by simp
  finally have 3: "(\<Sum>i=0..<l. (\<integral>x. f (x i) \<partial>prod_pmf {0..<l} (\<lambda>_. p))) = \<nu>" by simp

  have 4: "\<nu> \<le> real l * \<mu>" unfolding \<nu>_def using assms(2) by (simp add: mult_le_cancel_left)

  interpret Hoeffding_ineq "measure_pmf ?p" "{0..<l}" "\<lambda>i x. f (x i)" "(\<lambda>_. 0)" "(\<lambda>_. 1)" \<nu>
    using 1 2 unfolding 3 by unfold_locales auto

  have "?L \<le> measure ?p {x. (\<Sum>i=0..<l. f (x i)) \<ge> real l*\<mu> + real l*\<gamma>}"
    using assms(3) by (intro pmf_mono) (auto simp:field_simps atLeast0LessThan)
  also have "... \<le> measure ?p {x \<in> space ?p. (\<Sum>i=0..<l. f (x i)) \<ge> \<nu> + real l*\<gamma>}"
    using 4 by (intro pmf_mono) auto
  also have "... \<le> exp (- 2 * (real l * \<gamma>)^2 / (\<Sum>i=0..<l. (1 - 0)\<^sup>2))"
    using assms(3,4) by (intro Hoeffding_ineq_ge) auto
  also have "... = ?R" using assms(3) by (simp add:power2_eq_square)
  finally show ?thesis by simp
qed

lemma classic_chernoff_bound:
  assumes "AE x in measure_pmf p. f x \<in> {0,1::real}" "l > (0::nat)" "\<gamma> \<ge> 0"
  defines "\<mu> \<equiv> (\<integral>x. f x \<partial>p)"
  shows "measure (prod_pmf {0..<l} (\<lambda>_. p)) {w. \<bar>(\<Sum>i<l. f (w i))/l-\<mu>\<bar>\<ge>\<gamma>} \<le> 2*exp (-2*real l*\<gamma>^2)"
    (is "?L \<le> ?R")
proof -
  have [simp]:"integrable p f" using assms(1) unfolding AE_measure_pmf_iff
    by (intro integrable_bounded_pmf boundedI[where B="1"]) auto
  let ?w = "prod_pmf {0..<l} (\<lambda>_. p)"
  have "?L \<le> measure ?w {w. (\<Sum>i<l. f (w i))/l-\<mu>\<ge>\<gamma>} + measure ?w {w. (\<Sum>i<l. f (w i))/l-\<mu>\<le>-(\<gamma>)}"
    by (intro pmf_add) auto
  also have "... \<le> exp (-2*real l*\<gamma>^2) + measure ?w {w. -((\<Sum>i<l. f (w i))/l-\<mu>)\<ge>\<gamma>}"
    using assms by (intro add_mono classic_chernoff_bound_one_sided) (auto simp:algebra_simps)
  also have "... \<le> exp (-2*real l*\<gamma>^2) + measure ?w {w. ((\<Sum>i<l. 1-f (w i))/l-(1-\<mu>))\<ge>\<gamma>}"
    using assms(2) by (auto simp: sum_subtractf field_simps)
  also have "... \<le> exp (-2*real l*\<gamma>^2) + exp (-2*real l*\<gamma>^2)"
    using assms by (intro add_mono classic_chernoff_bound_one_sided) auto
  also have "... = ?R" by simp
  finally show ?thesis by simp
qed

text \<open>Definition of the second frequency moment of a stream.\<close>

definition F2 :: "'a list \<Rightarrow> real" where
  "F2 xs = (\<Sum> x \<in> set xs. (of_nat (count_list xs x)^2))"

lemma prime_power_ls: "is_prime_power (pro_size (\<L> [- 1, 1]))"
proof -
  have "is_prime_power ((2::nat)^1)" by (intro is_prime_powerI) auto
  thus "is_prime_power (pro_size (\<L> [- 1, 1]))" by (auto simp:list_pro_size numeral_eq_Suc)
qed

lemma prime_power_h2: "is_prime_power (pro_size (\<H> 4 n (\<L> [- 1, 1::real])))"
  by (intro hash_pro_size_prime_power prime_power_ls) auto

abbreviation \<Psi> where "\<Psi> \<equiv> pmf_of_set {-1,1::real}"

lemma f2_exp:
  assumes "finite (set_pmf p)"
  assumes "\<And>I. I \<subseteq> {0..<n} \<Longrightarrow> card I \<le> 4 \<Longrightarrow> map_pmf (\<lambda>x. (\<lambda>i\<in>I. x i)) p = prod_pmf I (\<lambda>_. \<Psi>)"
  assumes "set xs \<subseteq> {0..<n::nat}"
  shows "(\<integral>h. (\<Sum>x \<leftarrow> xs. h x)^2 \<partial>p) = F2 xs" (is "?L = ?R")
proof -
  let ?c = "(\<lambda>x. real (count_list xs x))"

  have [simp]: "integrable (measure_pmf p) f" for f :: "_ \<Rightarrow> real"
    by (intro integrable_measure_pmf_finite assms)

  have 0:"(\<integral>h. h x * h y \<partial>p) = of_bool (x = y)"
    (is "?L1 = ?R1") if "x \<in> set xs" "y \<in> set xs" for x y
  proof -
    have xy_lt_n: "x < n" "y < n"  using assms that by auto
    have card_xy: "card {x,y} \<le> 4" by (cases "x = y") auto

    have "?L1 = (\<integral>h. (h x * h y) \<partial>map_pmf (\<lambda>f. restrict f {x,y}) p)"
      by simp
    also have "... = (\<integral>h. (h x * h y) \<partial>prod_pmf {x,y} (\<lambda>_. \<Psi>))"
      using xy_lt_n card_xy by (intro integral_cong assms(2) arg_cong[where f="measure_pmf"]) auto
    also have "... = of_bool (x = y)" (is "?L2 = ?R2")
    proof (cases "x = y")
      case True
      hence "?L2 = (\<integral>h. (h x ^2) \<partial>prod_pmf {x} (\<lambda>_. pmf_of_set {-1,1}))"
        unfolding power2_eq_square by simp
      also have "... = (\<integral>x. x^2 \<partial>pmf_of_set {-1,1})"
        unfolding Pi_pmf_singleton by simp
      also have "... = 1" by (subst integral_pmf_of_set) auto
      also have "... = ?R2" using True by simp
      finally show ?thesis by simp
    next
      case False
      hence "?L2 = (\<integral>h. (\<Prod>i\<in>{x,y}. h i) \<partial>prod_pmf {x,y} (\<lambda>_. pmf_of_set {-1,1}))" by simp
      also have "... = (\<Prod>i\<in>{x,y}. (\<integral>x. x \<partial>pmf_of_set {-1,1}))"
        by (intro expectation_prod_Pi_pmf integrable_measure_pmf_finite) auto
      also have "... = 0" using False by (subst integral_pmf_of_set) auto
      also have "... = ?R2" using False by simp
      finally show ?thesis by simp
    qed
    finally show ?thesis by simp
  qed

  have "?L = (\<integral>h. (\<Sum>x \<in> set xs. real (count_list xs x) * h x)^2 \<partial>p)"
    unfolding sum_list_eval by simp
  also have "... = (\<integral>h. (\<Sum>x \<in> set xs. (\<Sum>y \<in> set xs. (?c x * ?c y) * h x * h y)) \<partial>p)"
    unfolding power2_eq_square sum_distrib_left sum_distrib_right by (simp add:ac_simps)
  also have "... = (\<Sum>x \<in> set xs. (\<Sum>y \<in> set xs. (\<integral>h. (?c x * ?c y) * h x * h y \<partial>p)))" by simp
  also have "... = (\<Sum>x \<in> set xs. (\<Sum>y \<in> set xs. ?c x * ?c y * (\<integral>h. h x * h y \<partial>p)))"
    by (subst integral_mult_right[symmetric]) (simp_all add:ac_simps)
  also have "... = (\<Sum>x \<in> set xs. (\<Sum>y \<in> set xs. ?c x * ?c y * of_bool (x = y)))"
    by (intro sum.cong refl) (simp add: 0)
  also have "... = (\<Sum>x \<in> set xs. ?c x^2) "
    unfolding of_bool_def by (simp add:if_distrib if_distribR sum.If_cases power2_eq_square)
  also have "... = F2 xs" unfolding F2_def by simp
  finally show ?thesis by simp
qed

lemma f2_exp_sq:
  assumes "finite (set_pmf p)"
  assumes "\<And>I. I \<subseteq> {0..<n} \<Longrightarrow> card I \<le> 4 \<Longrightarrow> map_pmf (\<lambda>x. (\<lambda>i\<in>I. x i)) p = prod_pmf I (\<lambda>_. \<Psi>)"
  assumes "set xs \<subseteq> {0..<n::nat}"
  shows "(\<integral>h. ((\<Sum>x\<leftarrow>xs. h x)^2)^2 \<partial>p) \<le> 3 * F2 xs^2" (is "?L \<le> ?R")
proof -
  let ?c = "(\<lambda>x. real (count_list xs x))"

  have [simp]: "integrable (measure_pmf p) f" for f :: "_ \<Rightarrow> real"
    by (intro integrable_measure_pmf_finite assms)

  define S where "S = set xs"

  have a: "finite S" unfolding S_def by simp

  define Q :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> real"
    where "Q a b c d =
      of_bool(a=b\<and>c=d\<and>a\<noteq>c) + of_bool(a=c\<and>b=d\<and>a\<noteq>b) +
      of_bool(a=d\<and>b=c\<and>a\<noteq>b) + of_bool(a=b\<and>b=c\<and>c=d)" for a b c d

  have cases: "(\<integral>h. h a*h b*h c*h d \<partial>p) = Q a b c d" (is "?L1 = ?R1")
    if "a \<in> S" "b\<in>S" "c \<in> S" "d \<in> S" for a b c d
  proof -
    have "card {a,b,c,d} = card (set [a,b,c,d])" by (intro arg_cong[where f="card"]) auto
    also have "... \<le> length [a,b,c,d]" by (intro card_length)
    finally have card: "card {a, b, c, d} \<le> 4" by simp

    have "?L1 = (\<integral>h. h a*h b*h c*h d \<partial>map_pmf (\<lambda>f. restrict f {a,b,c,d}) p)" by simp
    also have "... = (\<integral>h. h a*h b*h c*h d \<partial>prod_pmf {a,b,c,d} (\<lambda>_. \<Psi>))" using that assms(3)
      by (intro integral_cong arg_cong[where f="measure_pmf"] assms(2) card) (auto simp:S_def)
    also have "... = (\<integral>h. (\<Prod>i \<leftarrow>[a,b,c,d]. h i) \<partial>prod_pmf {a,b,c,d} (\<lambda>_. \<Psi>))" by (simp add:ac_simps)
    also have "... = (\<integral>h. (\<Prod>i \<in>{a,b,c,d}. h i^count_list [a,b,c,d] i) \<partial>prod_pmf {a,b,c,d} (\<lambda>_. \<Psi>))"
      by (subst prod_list_eval) auto
    also have "... = (\<Prod>i \<in> {a,b,c,d}. (\<integral>x. x^count_list [a,b,c,d] i \<partial>\<Psi>))"
      by (intro expectation_prod_Pi_pmf integrable_measure_pmf_finite) auto
    also have "... = (\<Prod>i \<in> {a,b,c,d}. of_bool (even (count_list [a,b,c,d] i)))"
      by (intro prod.cong refl) (auto simp:integral_pmf_of_set)
    also have "... = (\<Prod>i \<in> set (remdups [a,b,c,d]). of_bool (even (count_list [a,b,c,d] i)))"
      by (intro prod.cong refl) auto
    also have "... = (\<Prod>i \<leftarrow> remdups [a,b,c,d]. of_bool (even (count_list [a,b,c,d] i)))"
      by (intro prod.distinct_set_conv_list) auto
    also have "... = Q a b c d" unfolding Q_def by simp
    finally show ?thesis by simp
  qed

  have "?L = (\<integral>h. (\<Sum>x \<in> S. real (count_list xs x) * h x)^4 \<partial>p)"
    unfolding S_def sum_list_eval by simp
  also have "... = (\<integral>h. (\<Sum>a\<in>S. (\<Sum>b\<in>S.(\<Sum>c\<in>S.(\<Sum>d\<in>S.(?c a*?c b*?c c*?c d)*h a*h b*h c*h d)))) \<partial>p)"
    unfolding power4_eq_xxxx sum_distrib_left sum_distrib_right by (simp add:ac_simps)
  also have "... = (\<Sum>a\<in>S.(\<Sum>b\<in>S.(\<Sum>c\<in>S.(\<Sum>d\<in>S.(\<integral>h. (?c a*?c b*?c c*?c d)*h a*h b*h c*h d \<partial>p)))))"
    by simp
  also have "... = (\<Sum>a\<in>S.(\<Sum>b\<in>S.(\<Sum>c\<in>S.(\<Sum>d\<in>S. (?c a*?c b*?c c*?c d)*(\<integral>h. h a*h b*h c*h d \<partial>p)))))"
    by (subst integral_mult_right[symmetric]) (simp_all add:ac_simps)
  also have "... = (\<Sum>a\<in>S.(\<Sum>b\<in>S.(\<Sum>c\<in>S.(\<Sum>d\<in>S. (?c a*?c b*?c c*?c d)*(Q a b c d)))))"
    by (intro sum.cong refl) (simp add:cases)
  also have "... = 1*(\<Sum>a\<in>S. ?c a^4) + 3*(\<Sum>a\<in>S. (\<Sum>b\<in>S. ?c a^2 * ?c b^2 * of_bool(a\<noteq>b)))"
    unfolding Q_def
    by (simp add: sum.distrib distrib_left sum_collapse[OF a] ac_simps sum_distrib_left[symmetric]
        power2_eq_square power4_eq_xxxx)
  also have "... \<le> 3*(\<Sum>a\<in>S. ?c a^4) + 3*(\<Sum>a\<in>S. (\<Sum>b\<in>S. ?c a^2 * ?c b^2 * of_bool(a\<noteq>b)))"
    by (intro add_mono mult_right_mono sum_nonneg) auto
  also have "... = 3*(\<Sum>a\<in>S. (\<Sum>b\<in>S. ?c a^2 * ?c b^2 * (of_bool (a=b) + of_bool(a\<noteq>b))))"
    using a by (simp add: sum.distrib distrib_left)
  also have "... = 3*(\<Sum>a\<in>S. (\<Sum>b\<in>S. ?c a^2 * ?c b^2 * 1))"
    by (intro sum.cong arg_cong2[where f="(*)"] refl) auto
  also have "... = 3 * F2 xs^2" unfolding F2_def power2_eq_square
    by (simp add: S_def sum_distrib_left sum_distrib_right ac_simps)
  finally show "?L \<le> 3 * F2 xs^2" by simp
qed

lemma f2_var:
  assumes "finite (set_pmf p)"
  assumes "\<And>I. I \<subseteq> {0..<n} \<Longrightarrow> card I \<le> 4 \<Longrightarrow> map_pmf (\<lambda>x. (\<lambda>i\<in>I. x i)) p = prod_pmf I (\<lambda>_. \<Psi>)"
  assumes "set xs \<subseteq> {0..<n::nat}"
  shows "measure_pmf.variance p (\<lambda>h. (\<Sum>x\<leftarrow>xs. h x)^2) \<le> 2* F2 xs^2"
    (is "?L \<le> ?R")
proof -
  have [simp]: "integrable (measure_pmf p) f" for f :: "_ \<Rightarrow> real"
    by (intro integrable_measure_pmf_finite assms)

  have "?L = (\<integral>h. ((\<Sum>x\<leftarrow>xs. h x)^2)^2 \<partial>p) - F2 xs^2"
    by (subst measure_pmf.variance_eq) (simp_all add:f2_exp[OF assms(1-3)])
  also have "... \<le> 3 * F2 xs^2 - F2 xs^2"
    by (intro diff_mono f2_exp_sq[OF assms]) auto
  finally show ?thesis by simp
qed

lemma
  assumes "s \<in> set_pmf (\<H>\<^sub>P 4 n (\<L> [-1,1]))"
  assumes "set xs \<subseteq> {0..<n}"
  shows f2_exp_hp: "(\<integral>h. (\<Sum>x \<leftarrow> xs. h x)^2 \<partial>sample_pro s) = F2 xs" (is "?T1")
    and f2_exp_sq_hp: "(\<integral>h. ((\<Sum>x \<leftarrow> xs. h x)^2)^2 \<partial>sample_pro s) \<le> 3* F2 xs^2" (is "?T2")
    and f2_var_hp: "measure_pmf.variance s (\<lambda>h. (\<Sum>x \<leftarrow> xs. h x)^2) \<le> 2* F2 xs^2"  (is "?T3")
proof -
  have 0:"map_pmf (\<lambda>x. restrict x I) (sample_pro s) = prod_pmf I (\<lambda>_. \<Psi>)" (is "?L = _")
    if "I \<subseteq> {0..<n}" "card I \<le> 4" for I
  proof -
    have "?L = prod_pmf I (\<lambda>_. sample_pro (\<L> [- 1, 1]))"
      using that by (intro hash_pro_pmf_distr[OF _ assms(1)] prime_power_ls) auto
    also have "... = prod_pmf I (\<lambda>_. \<Psi>)" by (subst list_pro_2) auto
    finally show ?thesis by simp
  qed

  show ?T1 by (intro f2_exp[OF _ _ assms(2)] finite_pro_set 0) simp
  show ?T2 by (intro f2_exp_sq[OF _ _ assms(2)] finite_pro_set 0) simp
  show ?T3 by (intro f2_var[OF _ _ assms(2)] finite_pro_set 0) simp
qed

lemmas f2_exp_h = f2_exp_hp[OF hash_pro_in_hash_pro_pmf[OF prime_power_ls]]
lemmas f2_var_h = f2_var_hp[OF hash_pro_in_hash_pro_pmf[OF prime_power_ls]]

lemma F2_definite:
  assumes "xs \<noteq> []"
  shows "F2 xs > 0"
proof -
  have "0 < real (card (set xs))" using assms by (simp add: card_gt_0_iff)
  also have "... = (\<Sum>x \<in> set xs. 1)" by simp
  also have "... \<le> F2 xs" using count_list_gr_1 unfolding F2_def by (intro sum_mono) force
  finally show ?thesis by simp
qed

text \<open>The following algorithm uses a completely random function, accordingly it requires
a lot of space: $\mathcal O(n + \ln m)$.\<close>

fun example_1 :: "nat \<Rightarrow> nat list \<Rightarrow> real pmf"
  where "example_1 n xs =
    do {
      h \<leftarrow> prod_pmf {0..<n} (\<lambda>_. pmf_of_set {-1,1::real});
      return_pmf ((\<Sum>x \<leftarrow> xs. h x)^2)
    }"

lemma example_1_correct:
  assumes "set xs \<subseteq> {0..<n}"
  shows
    "measure_pmf.expectation (example_1 n xs) id = F2 xs" (is "?L1 = ?R1")
    "measure_pmf.variance (example_1 n xs) id \<le> 2 * F2 xs^2" (is "?L2 \<le> ?R2")
proof -
  have "?L1 = (\<integral>h. (\<Sum>x \<leftarrow> xs. h x)^2 \<partial>prod_pmf {0..<n} (\<lambda>_. \<Psi>))"
    by (simp add:map_pmf_def[symmetric])
  also have "... = ?R1" using assms by (intro f2_exp)
      (auto intro: Pi_pmf_subset[symmetric] simp add:restrict_def set_Pi_pmf)
  finally show "?L1 = ?R1" by simp

  have "?L2 = measure_pmf.variance (prod_pmf {0..<n} (\<lambda>_. \<Psi>)) (\<lambda>h. (\<Sum>x \<leftarrow> xs. h x)^2)"
    by (simp add:map_pmf_def[symmetric] atLeast0LessThan)
  also have "... \<le> ?R2"
    using assms by (intro f2_var)
      (auto intro: Pi_pmf_subset[symmetric] simp add:restrict_def set_Pi_pmf)
  finally show "?L2 \<le> ?R2" by simp
qed

text \<open>This version replaces a the use of completely random function with a pseudorandom object,
it requires a lot less space: $\mathcal O(\ln n + \ln m)$.\<close>

fun example_2 :: "nat \<Rightarrow> nat list \<Rightarrow> real pmf"
  where "example_2 n xs =
    do {
      h \<leftarrow> sample_pro (\<H> 4 n (\<L> [-1,1]));
      return_pmf ((\<Sum>x \<leftarrow> xs. h x)^2)
    }"

lemma example_2_correct:
  assumes "set xs \<subseteq> {0..<n}"
  shows
    "measure_pmf.expectation (example_2 n xs) id = F2 xs" (is "?L1 = ?R1")
    "measure_pmf.variance (example_2 n xs) id \<le> 2 * F2 xs^2" (is "?L2 \<le> ?R2")
proof -
  have "?L1 = (\<integral>h. (\<Sum>x \<leftarrow> xs. h x)^2 \<partial>sample_pro (\<H> 4 n (\<L> [-1,1])))"
    by (simp add:map_pmf_def[symmetric])
  also have "... = ?R1"
    using assms by (intro f2_exp_h) auto
  finally show "?L1 = ?R1" by simp

  have "?L2 = measure_pmf.variance (sample_pro (\<H> 4 n (\<L> [-1,1]))) (\<lambda>h. (\<Sum>x \<leftarrow> xs. h x)^2)"
    by (simp add:map_pmf_def[symmetric])
  also have "... \<le> ?R2"
    using assms by (intro f2_var_h) auto
  finally show "?L2 \<le> ?R2" by simp
qed

text \<open>The following version replaces the deterministic construction of the pseudorandom object
with a randomized one. This algorithm is much faster, but the correctness proof is more difficult.\<close>

fun example_3 :: "nat \<Rightarrow> nat list \<Rightarrow> real pmf"
  where "example_3 n xs =
    do {
      h \<leftarrow> sample_pro =<< \<H>\<^sub>P 4 n (\<L> [-1,1]);
      return_pmf ((\<Sum>x \<leftarrow> xs. h x)^2)
    }"

lemma
  assumes "set xs \<subseteq> {0..<n}"
  shows
    "measure_pmf.expectation (example_3 n xs) id = F2 xs" (is "?L1 = ?R1")
    "measure_pmf.variance (example_3 n xs) id \<le> 2 * F2 xs^2" (is "?L2 \<le> ?R2")
proof -
  let ?p = "\<H>\<^sub>P 4 n (\<L> [-1,1::real])"
  let ?q = "bind_pmf ?p sample_pro"

  have "\<bar>h x\<bar> \<le> 1" if that1: "M \<in> set_pmf ?p" "h \<in> pro_set M" "x \<in> set xs" for h M x
  proof -
    obtain i where 1:"h = pro_select M i"
      using that1(2) unfolding set_sample_pro[of "M"] by auto
    have "h x \<in> pro_set (\<L> [-1,1::real])"
      unfolding 1 using that(1) by (intro hash_pro_pmf_range[OF prime_power_ls])  auto
    thus ?thesis by (auto simp: list_pro_set)
  qed

  hence 0: "bounded ((\<lambda>xa. xa x) ` set_pmf ?q)" if "x \<in> set xs" for x
    using that by (intro boundedI[where B="1"]) auto

  have "(\<integral>h. (\<Sum>x \<leftarrow> xs. h x)^2 \<partial>?q) = (\<integral>s. (\<integral>h. (\<Sum>x \<leftarrow> xs. h x)^2 \<partial>sample_pro s) \<partial>?p)"
    by (intro integral_bind_pmf bounded_pow bounded_sum_list 0)
  also have "... = (\<integral>s. F2 xs \<partial>?p)"
    by (intro integral_cong_AE AE_pmfI f2_exp_hp[OF _ assms]) simp_all
  also have "... = ?R1" by simp
  finally have a:"(\<integral>h. (\<Sum>x \<leftarrow> xs. h x)^2 \<partial>?q) = ?R1" by simp
  thus "?L1 = ?R1" by (simp add:map_pmf_def[symmetric])

  have "?L2 = measure_pmf.variance ?q (\<lambda>h. (\<Sum>x \<leftarrow> xs. h x)^2)"
    by (simp add:map_pmf_def[symmetric])
  also have "... = (\<integral>h. ((\<Sum>x \<leftarrow> xs. h x)^2)^2 \<partial>?q) -  (\<integral>h. (\<Sum>x \<leftarrow> xs. h x)^2 \<partial>?q)^2"
    by (intro measure_pmf.variance_eq integrable_bounded_pmf bounded_pow bounded_sum_list 0)
  also have "... = (\<integral>s. (\<integral>h. ((\<Sum>x \<leftarrow> xs. h x)^2)^2 \<partial>sample_pro s) \<partial>?p)- (F2 xs)\<^sup>2"
    unfolding a
    by (intro arg_cong2[where f="(-)"] integral_bind_pmf refl bounded_pow bounded_sum_list 0)
  also have "... \<le> (\<integral>s. 3*F2 xs^2  \<partial>?p) - (F2 xs)^2"
    by (intro diff_mono integral_mono_AE' AE_pmfI f2_exp_sq_hp[OF _ assms]) simp_all
  also have "... = ?R2" by simp
  finally show "?L2 \<le> ?R2" by simp
qed

context
  fixes \<epsilon> \<delta> :: real
  assumes \<epsilon>_gt_0: "\<epsilon> > 0"
  assumes \<delta>_range: "\<delta> \<in> {0<..<1}"
begin

text \<open>By using the mean of many independent parallel estimates the following algorithm
achieves a relative accuracy of $\varepsilon$, with probability $\frac{3}{4}$.
It requires $\mathcal O(\varepsilon^{-2} (\ln n + \ln m))$ bits of space.\<close>

fun example_4 :: "nat \<Rightarrow> nat list \<Rightarrow> real pmf"
  where "example_4 n xs =
    do {
      let s = nat \<lceil>8 / \<epsilon>^2\<rceil>;
      h \<leftarrow> prod_pmf {0..<s} (\<lambda>_. sample_pro (\<H> 4 n (\<L> [-1,1])));
      return_pmf ((\<Sum>j < s. (\<Sum>x \<leftarrow> xs. h j x)^2)/s)
    }"

lemma example_4_correct_aux:
  assumes "set xs \<subseteq> {0..<n}"
  defines "s \<equiv> nat \<lceil>8 / \<epsilon>^2\<rceil>"
  defines "R \<equiv> (\<lambda>h :: nat \<Rightarrow> nat \<Rightarrow> real. (\<Sum>j<s. (\<Sum>x\<leftarrow>xs. h j x)^2)/real s)"
  assumes fin: "finite (set_pmf p)"
  assumes indep: "prob_space.k_wise_indep_vars (measure_pmf p) 2 (\<lambda>_. discrete) (\<lambda>i x. x i) {..<s}"
  assumes comp: "\<And>i. i < s \<Longrightarrow> map_pmf (\<lambda>x. x i) p = sample_pro (\<H> 4 n (\<L> [-1,1]))"
  shows "measure p {h. \<bar>R h - F2 xs\<bar> > \<epsilon> * F2 xs} \<le> 1/4" (is "?L \<le> ?R")
proof (cases "xs = []")
  case True thus ?thesis by (simp add:R_def F2_def)
next
  case False
  note f2_gt_0 = F2_definite[OF False]
  let ?p = "sample_pro (\<H> 4 n (\<L> [-1,1::real]))"

  have [simp]: "integrable (measure_pmf p) f" for f :: "_ \<Rightarrow> real"
    by (intro integrable_measure_pmf_finite fin)

  have "8 / \<epsilon>\<^sup>2 > 0" using \<epsilon>_gt_0 by (intro divide_pos_pos) auto
  hence 0:"\<lceil>8 / \<epsilon>\<^sup>2\<rceil> > 0" by simp
  hence 1: "s > 0" unfolding s_def by simp

  have "(\<integral>h. R h \<partial>p) = (\<Sum>j<s. (\<integral>h. (\<Sum>x\<leftarrow>xs. h j x)^2 \<partial>p))/real s" unfolding R_def by simp
  also have "... = (\<Sum>j<s. (\<integral>h. (\<Sum>x\<leftarrow>xs. h x)^2 \<partial>(map_pmf(\<lambda>h. h j)p)))/real s" by simp
  also have "... = (\<Sum>j<s. (\<integral>h. (\<Sum>x\<leftarrow>xs. h x)^2 \<partial>?p))/real s"
    by (intro sum.cong arg_cong2[where f="(/)"] refl) (simp add: comp)
  also have "... = F2 xs" using 1 unfolding f2_exp_h[OF assms(1)] by simp
  finally have exp_R: "(\<integral>h. R h \<partial>p) = F2 xs" by simp

  have "measure_pmf.variance p R = measure_pmf.variance p (\<lambda>h. (\<Sum>j<s. (\<Sum>x\<leftarrow>xs. h j x)^2))/s^2"
    unfolding R_def by (subst measure_pmf.variance_divide) simp_all
  also have "... = (\<Sum>j<s. measure_pmf.variance p (\<lambda>h. (\<Sum>x\<leftarrow>xs. h j x)^2))/real s^2"
    by (intro arg_cong2[where f="(/)"] refl measure_pmf.bienaymes_identity_pairwise_indep_2
        prob_space.indep_vars_compose2[OF _ prob_space.k_wise_indep_vars_subset[OF _ indep]]
        prob_space_measure_pmf) (auto intro:finite_subset)
  also have "... = (\<Sum>j<s. measure_pmf.variance(map_pmf(\<lambda>h. h j)p)(\<lambda>h. (\<Sum>x\<leftarrow>xs. h x)^2))/real s^2"
    by simp
  also have "... = (\<Sum>j<s. measure_pmf.variance ?p (\<lambda>h. (\<Sum>x\<leftarrow>xs. h x)^2))/ real s^2"
    by (intro sum.cong arg_cong2[where f="(/)"] refl) (simp add: comp)
  also have "... \<le> (\<Sum>j<s. 2 * F2 xs^2)/real s^2"
    by (intro divide_right_mono sum_mono f2_var_h[OF assms(1)]) simp
  also have "... = 2 * F2 xs^2/real s" by (simp add:power2_eq_square divide_simps)
  also have "... = 2 * F2 xs^2/ \<lceil>8/\<epsilon>^2\<rceil>"
    using less_imp_le[OF 0] unfolding s_def by (subst of_nat_nat) auto
  also have "... \<le> 2 * F2 xs^2 / (8/ \<epsilon>^2)"
    using \<epsilon>_gt_0 by (intro divide_left_mono mult_pos_pos) simp_all
  also have "... = \<epsilon>^2 * F2 xs^2/4" by simp
  finally have var_R: "measure_pmf.variance p R \<le> \<epsilon>^2 * F2 xs^2/4" by simp

  have "(\<integral>h. R h \<partial>p) = (\<Sum>j<s. (\<integral>h. (\<Sum>x\<leftarrow>xs. h j x)^2 \<partial>p))/real s" unfolding R_def by simp
  also have "... = (\<Sum>j<s. (\<integral>h. (\<Sum>x\<leftarrow>xs. h x)^2 \<partial>(map_pmf(\<lambda>h. h j)p)))/real s" by simp
  also have "... = (\<Sum>j<s. (\<integral>h. (\<Sum>x\<leftarrow>xs. h x)^2 \<partial>?p))/real s"
    by (intro sum.cong arg_cong2[where f="(/)"] refl) (simp add:comp)
  also have "... = F2 xs" using 1 unfolding f2_exp_h[OF assms(1)] by simp
  finally have exp_R: "(\<integral>h. R h \<partial>p) = F2 xs" by simp

  have "?L \<le> measure p {h. \<bar>R h - F2 xs\<bar> \<ge> \<epsilon> * F2 xs}" by (intro pmf_mono) auto
  also have "... \<le> \<P>(h in p. \<bar>R h - (\<integral>h. R h \<partial>p)\<bar> \<ge> \<epsilon> * F2 xs)" unfolding exp_R by simp
  also have "... \<le> measure_pmf.variance p R / (\<epsilon> * F2 xs)^2"
    using f2_gt_0 \<epsilon>_gt_0 by (intro measure_pmf.Chebyshev_inequality) simp_all
  also have "... \<le> (\<epsilon>^2 * F2 xs^2/4) /  (\<epsilon> * F2 xs)^2"
    by (intro divide_right_mono var_R) simp
  also have "... = 1/4" using \<epsilon>_gt_0 f2_gt_0 by (simp add:divide_simps)
  finally show ?thesis by simp
qed

lemma example_4_correct:
  assumes "set xs \<subseteq> {0..<n}"
  shows "\<P>(\<omega> in example_4 n xs. \<bar>\<omega> - F2 xs\<bar> > \<epsilon> * F2 xs) \<le> 1/4" (is "?L \<le> ?R")
proof -
  define s :: nat where "s = nat \<lceil>8 / \<epsilon>^2\<rceil>"
  define R where "R h = (\<Sum>j<s. (\<Sum>x\<leftarrow>xs. h j x)^2)/s" for h :: "nat \<Rightarrow> nat \<Rightarrow> real"

  let ?p = "sample_pro (\<H> 4 n (\<L> [-1,1::real]))"
  let ?q = "prod_pmf {..<s} (\<lambda>_. ?p)"

  have "?L = (\<integral>h. indicator {h. \<bar>R h - F2 xs\<bar> > \<epsilon> * F2 xs} h \<partial> ?q)"
    by (simp add:Let_def measure_bind_pmf R_def s_def indicator_def atLeast0LessThan)
  also have "... = measure ?q {h. \<bar>R h - F2 xs\<bar> > \<epsilon> * F2 xs}" by simp
  also have "... \<le> ?R" unfolding R_def s_def
    by (intro example_4_correct_aux[OF assms] prob_space.k_wise_indep_vars_triv
        prob_space_measure_pmf indep_vars_Pi_pmf)
     (auto intro: finite_pro_set simp add:Pi_pmf_component set_Pi_pmf)
  finally show ?thesis by simp
qed

text \<open>Instead of independent samples, we can choose the seeds using a second
pair-wise independent pseudorandom object. This algorithm requires only
$\mathcal O(\ln n + \varepsilon^{-2} \ln m)$ bits of space.\<close>

fun example_5 :: "nat \<Rightarrow> nat list \<Rightarrow> real pmf"
  where "example_5 n xs =
    do {
      let s = nat \<lceil>8 / \<epsilon>^2\<rceil>;
      h \<leftarrow> sample_pro (\<H> 2 s (\<H> 4 n (\<L> [-1,1])));
      return_pmf ((\<Sum>j < s. (\<Sum>x \<leftarrow> xs. h j x)^2)/s)
    }"

lemma example_5_correct_aux:
  assumes "set xs \<subseteq> {0..<n}"
  defines "s \<equiv> nat \<lceil>8 / \<epsilon>^2\<rceil>"
  defines "R \<equiv> (\<lambda>h :: nat \<Rightarrow> nat \<Rightarrow> real. (\<Sum>j<s. (\<Sum>x\<leftarrow>xs. h j x)^2)/real s)"
  shows "measure (sample_pro (\<H> 2 s (\<H> 4 n (\<L> [-1,1])))) {h. \<bar>R h - F2 xs\<bar> > \<epsilon> * F2 xs} \<le> 1/4"
proof -
  let ?p = "sample_pro (\<H> 2 s (\<H> 4 n (\<L> [-1,1::real])))"

  have "prob_space.k_wise_indep_vars ?p 2 (\<lambda>_. discrete) (\<lambda>i x. x i) {..<s}"
    using hash_pro_indep[OF prime_power_h2]
    by (simp add: prob_space.k_wise_indep_vars_def[OF prob_space_measure_pmf])

  thus ?thesis unfolding R_def s_def
    by (intro example_4_correct_aux[OF assms(1)] finite_pro_set)
      (simp_all add:hash_pro_component[OF prime_power_h2])
qed

lemma example_5_correct:
  assumes "set xs \<subseteq> {0..<n}"
  shows "\<P>(\<omega> in example_5 n xs. \<bar>\<omega> - F2 xs\<bar> > \<epsilon> * F2 xs) \<le> 1/4" (is "?L \<le> ?R")
proof -
  define s :: nat where "s = nat \<lceil>8 / \<epsilon>^2\<rceil>"
  define R where "R h = (\<Sum>j<s. (\<Sum>x\<leftarrow>xs. h j x)^2)/s" for h :: "nat \<Rightarrow> nat \<Rightarrow> real"

  let ?p = "sample_pro (\<H> 2 s (\<H> 4 n (\<L> [-1,1::real])))"

  have "?L = (\<integral>h. indicator {h. \<bar>R h - F2 xs\<bar> > \<epsilon> * F2 xs} h \<partial> ?p)"
    by (simp add:Let_def measure_bind_pmf R_def s_def indicator_def)
  also have "... = measure ?p {h. \<bar>R h - F2 xs\<bar> > \<epsilon> * F2 xs}" by simp
  also have "... \<le> ?R" unfolding R_def s_def by (intro example_5_correct_aux[OF assms])
  finally show ?thesis by simp
qed

text \<open>The following algorithm improves on the previous one, by achieving a success probability
of $\delta$. This works by taking the median of $\mathcal O(\ln(\delta^{-1}))$ parallel independent
samples. It requires $\mathcal O(\ln(\delta^{-1}) (\ln n + \varepsilon^{-2} \ln m))$ bits of space.\<close>

fun example_6 :: "nat \<Rightarrow> nat list \<Rightarrow> real pmf"
  where "example_6 n xs =
    do {
      let s = nat \<lceil>8 / \<epsilon>^2\<rceil>; let t = nat \<lceil>8 * ln (1/\<delta>)\<rceil>;
      h \<leftarrow> prod_pmf {0..<t} (\<lambda>_. sample_pro (\<H> 2 s (\<H> 4 n (\<L> [-1,1]))));
      return_pmf (median t (\<lambda>i. ((\<Sum>j < s. (\<Sum>x \<leftarrow> xs. h i j x)^2)/ s)))
    }"

lemma example_6_correct:
  assumes "set xs \<subseteq> {0..<n}"
  shows "\<P>(\<omega> in example_6 n xs. \<bar>\<omega> - F2 xs\<bar> > \<epsilon> * F2 xs) \<le> \<delta>" (is "?L \<le> ?R")
proof -
  define s where "s = nat \<lceil>8 / \<epsilon>^2\<rceil>"
  define t where "t = nat \<lceil>8 * ln(1/\<delta>)\<rceil>"
  define R where "R h = (\<Sum>j<s. (\<Sum>x\<leftarrow>xs. h j x)^2)/s" for h :: "nat \<Rightarrow> nat \<Rightarrow> real"
  define I where "I = {w. \<bar>w - F2 xs\<bar> \<le> \<epsilon>*F2 xs}"

  have "8 * ln (1 / \<delta>) > 0" using \<delta>_range by (intro mult_pos_pos ln_gt_zero) auto
  hence t_gt_0: "t > 0" unfolding t_def by simp
  have int_I: "interval I" unfolding interval_def I_def by auto

  let ?p = "sample_pro (\<H> 2 s (\<H> 4 n (\<L> [-1,1::real])))"
  let ?q = "prod_pmf {0..<t} (\<lambda>_. ?p)"

  have "(\<integral>h. (of_bool (R h \<notin> I)::real) \<partial>?p) = (\<integral>h. indicator {h. R h \<notin> I} h \<partial>?p)"
    unfolding of_bool_def indicator_def by simp
  also have "... = measure ?p {h. R h \<notin> I}" by simp
  also have "... \<le> 1/4"
    using example_5_correct_aux[OF assms] unfolding R_def s_def I_def by (simp add:not_le)
  finally have 0: "(\<integral>h. (of_bool (R h \<notin> I)::real) \<partial>?p) \<le> 1/4" by simp

  have "?L =  (\<integral>h. indicator {h. \<bar>median t (\<lambda>i. R (h i)) - F2 xs\<bar> > \<epsilon> * F2 xs} h \<partial> ?q)"
    by (simp add:Let_def measure_bind_pmf R_def s_def indicator_def t_def)
  also have "... = measure ?q {h. median t (\<lambda>i. R (h i)) \<notin> I}"
    unfolding I_def by (simp add:not_le)
  also have "... \<le> measure ?q {h. t \<le> 2 * card {k. k < t \<and> R (h k) \<notin> I}}"
    using median_est_rev[OF int_I] by (intro pmf_mono) auto
  also have "... = measure ?q {h. (\<Sum>k<t. of_bool(R (h k) \<notin> I))/real t - 1/4 \<ge> (1/4)}"
    using t_gt_0 by (intro arg_cong2[where f="measure"]) (auto simp:Int_def divide_simps)
  also have "... \<le> exp ( - 2 * real t * (1/4)^2)"
    by (intro classic_chernoff_bound_one_sided t_gt_0 AE_pmfI 0) auto
  also have "... = exp (- (real t / 8))" using t_gt_0 by (simp add:power2_eq_square)
  also have "... \<le> exp (- of_int \<lceil>8 * ln (1 / \<delta>)\<rceil> / 8)" unfolding t_def
    by (intro iffD2[OF exp_le_cancel_iff] divide_right_mono iffD2[OF neg_le_iff_le]) auto
  also have "... \<le> exp (- (8 * ln (1 / \<delta>)) / 8)"
    by (intro iffD2[OF exp_le_cancel_iff] divide_right_mono iffD2[OF neg_le_iff_le]) auto
  also have "... = exp (- ln (1 / \<delta>))" by simp
  also have "... = \<delta>" using \<delta>_range by (subst ln_div) auto
  finally show ?thesis by simp
qed

text \<open>The following algorithm uses an expander random walk, instead of independent samples.
It requires only $\mathcal O(\ln n + \ln(\delta^{-1}) \varepsilon^{-2} \ln m)$ bits of space.\<close>

fun example_7 :: "nat \<Rightarrow> nat list \<Rightarrow> real pmf"
  where "example_7 n xs =
    do {
      let s = nat \<lceil>8 / \<epsilon>^2\<rceil>; let t = nat \<lceil>32 * ln (1/\<delta>)\<rceil>;
      h \<leftarrow> sample_pro (\<E> t (1/8) (\<H> 2 s (\<H> 4 n (\<L> [-1,1]))));
      return_pmf (median t (\<lambda>i. ((\<Sum>j < s. (\<Sum>x \<leftarrow> xs. h i j x)^2)/ s)))
    }"

lemma example_7_correct:
  assumes "set xs \<subseteq> {0..<n}"
  shows "\<P>(\<omega> in example_7 n xs. \<bar>\<omega> - F2 xs\<bar> > \<epsilon> * F2 xs) \<le> \<delta>" (is "?L \<le> ?R")
proof -
  define s t where s_def: "s = nat \<lceil>8 / \<epsilon>^2\<rceil>" and t_def: "t = nat \<lceil>32 * ln(1/\<delta>)\<rceil>"
  define R where "R h = (\<Sum>j<s. (\<Sum>x\<leftarrow>xs. h j x)^2)/s" for h :: "nat \<Rightarrow> nat \<Rightarrow> real"
  define I where "I = {w. \<bar>w - F2 xs\<bar> \<le> \<epsilon>*F2 xs}"

  have "8 * ln (1 / \<delta>) > 0" using \<delta>_range by (intro mult_pos_pos ln_gt_zero) auto
  hence t_gt_0: "t > 0" unfolding t_def by simp
  have int_I: "interval I" unfolding interval_def I_def by auto

  let ?p = "sample_pro (\<H> 2 s (\<H> 4 n (\<L> [-1,1::real])))"
  let ?q = "sample_pro (\<E> t (1/8) (\<H> 2 s (\<H> 4 n (\<L> [-1,1]))))"

  have "(\<integral>h. (of_bool (R h \<notin> I)::real) \<partial>?p) = (\<integral>h. indicator {h. R h \<notin> I} h \<partial>?p)"
    by (simp add:of_bool_def indicator_def)
  also have "... = measure ?p {h. R h \<notin> I}" by simp
  also have "... \<le> 1/4"
    using example_5_correct_aux[OF assms] unfolding R_def s_def I_def by (simp add:not_le)
  finally have *: "(\<integral>h. (of_bool (R h \<notin> I)::real) \<partial>?p) \<le> 1/4" by simp

  have "?L =  (\<integral>h. indicator {h. \<bar>median t (\<lambda>i. R (h i)) - F2 xs\<bar> > \<epsilon> * F2 xs} h \<partial> ?q)"
    by (simp add:Let_def measure_bind_pmf R_def s_def indicator_def t_def)
  also have "... = measure ?q {h. median t (\<lambda>i. R (h i)) \<notin> I}"
    unfolding I_def by (simp add:not_le)
  also have "... \<le> measure ?q {h. t \<le> 2 * card {k. k < t \<and> R (h k) \<notin> I}}"
    using median_est_rev[OF int_I] by (intro pmf_mono) auto
  also have "... = measure ?q {h. 1/8 + 1/8 \<le> (\<Sum>k<t. of_bool(R (h k) \<notin> I))/real t - 1/4}"
    using t_gt_0 by (intro arg_cong2[where f="measure"] Collect_cong refl)
     (auto simp add:of_bool_def sum.If_cases Int_def field_simps)
  also have "... \<le> exp (- 2 * real t * (1/8)\<^sup>2)"
    by (intro expander_chernoff_bound_one_sided t_gt_0 *) auto
  also have "... = exp (- (real t / 32))" using t_gt_0 by (simp add:power2_eq_square)
  also have "... \<le> exp (- of_int \<lceil>32 * ln (1 / \<delta>)\<rceil> / 32)" unfolding t_def
    by (intro iffD2[OF exp_le_cancel_iff] divide_right_mono iffD2[OF neg_le_iff_le]) auto
  also have "... \<le> exp (- (32 * ln (1 / \<delta>)) / 32)"
    by (intro iffD2[OF exp_le_cancel_iff] divide_right_mono iffD2[OF neg_le_iff_le]) auto
  also have "... = exp (- ln (1 / \<delta>))" by simp
  also have "... = \<delta>" using \<delta>_range by (subst ln_div) auto
  finally show ?thesis by simp
qed

end

end
