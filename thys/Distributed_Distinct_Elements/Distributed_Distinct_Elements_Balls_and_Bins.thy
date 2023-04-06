section \<open>Balls and Bins\<close>

text \<open>The balls and bins model describes the probability space of throwing r balls into b
bins. This section derives the expected number of bins hit by at least one ball, as well as the
variance in the case that each ball is thrown independently. Further, using an approximation
argument it is then possible to derive bounds for the same measures in the case when the balls
are being thrown only $k$-wise independently. The proofs follow the reasoning described in
\cite[\S A.1]{kane2010} but improve on the constants, as well as constraints.\<close>

theory Distributed_Distinct_Elements_Balls_and_Bins
  imports
    Distributed_Distinct_Elements_Preliminary
    Discrete_Summation.Factorials
    "HOL-Combinatorics.Stirling"
    "HOL-Computational_Algebra.Polynomial"
    "HOL-Decision_Procs.Approximation"
begin

hide_fact "Henstock_Kurzweil_Integration.integral_sum"
hide_fact "Henstock_Kurzweil_Integration.integral_mult_right"
hide_fact "Henstock_Kurzweil_Integration.integral_nonneg"
hide_fact "Henstock_Kurzweil_Integration.integral_cong"
unbundle intro_cong_syntax

lemma sum_power_distrib:
  fixes f :: "'a \<Rightarrow> real"
  assumes "finite R"
  shows "(\<Sum>i\<in>R. f i) ^ s = (\<Sum>xs | set xs \<subseteq> R \<and> length xs = s. (\<Prod>x \<leftarrow> xs. f x))"
proof (induction s)
  case 0
  have "{xs. xs = [] \<and> set xs \<subseteq> R} = {[]}"
    by (auto simp add:set_eq_iff)
  then show ?case by simp
next
  case (Suc s)
  have a:
    "(\<Union>i\<in>R. (#) i ` {xs. set xs \<subseteq> R \<and> length xs = s}) = {xs. set xs \<subseteq> R \<and> length xs = Suc s}"
    by (subst lists_length_Suc_eq)  auto
  have "sum f R ^ Suc s = (sum f R) * (sum f R)^s"
    by simp
  also have "... = (sum f R) * (\<Sum>xs | set xs \<subseteq> R \<and> length xs = s. (\<Prod>x \<leftarrow> xs. f x))"
    using Suc by simp
  also have "... = (\<Sum>i \<in> R. (\<Sum>xs | set xs \<subseteq> R \<and> length xs = s. (\<Prod>x \<leftarrow> i#xs. f x)))"
    by (subst sum_product) simp
  also have "... =
    (\<Sum>i \<in> R. (\<Sum>xs \<in> (\<lambda>xs. i#xs) ` {xs. set xs \<subseteq> R \<and> length xs = s}. (\<Prod>x \<leftarrow> xs. f x)))"
    by (subst sum.reindex) (auto)
  also have "... =  (\<Sum>xs\<in>(\<Union>i\<in>R. (#) i ` {xs. set xs \<subseteq> R \<and> length xs = s}). (\<Prod>x \<leftarrow> xs. f x))"
    by (intro sum.UNION_disjoint[symmetric] assms ballI finite_imageI finite_lists_length_eq)
    auto
  also have "... = (\<Sum>xs| set xs \<subseteq> R \<and> length xs = Suc s. (\<Prod>x \<leftarrow> xs. f x))"
    by (intro sum.cong a) auto
  finally show ?case by simp
qed

lemma sum_telescope_eq:
  fixes f :: "nat \<Rightarrow> 'a :: {comm_ring_1}"
  shows "(\<Sum>k\<in>{Suc m..n}. f k - f (k - 1)) = of_bool(m \<le> n) *(f n - f m)"
  by (cases "m \<le> n", subst sum_telescope'', auto)

text \<open>An improved version of @{thm [source] diff_power_eq_sum}.\<close>
lemma power_diff_sum:
  fixes a b :: "'a :: {comm_ring_1,power}"
  shows "a^k - b^k = (a-b) * (\<Sum>i = 0..<k. a ^ i * b ^ (k - 1 - i))"
proof (cases "k")
  case 0
  then show ?thesis by simp
next
  case (Suc nat)
  then show ?thesis
    unfolding Suc diff_power_eq_sum
    using atLeast0LessThan diff_Suc_1 by presburger
qed

lemma power_diff_est:
  assumes "(a :: real) \<ge> b"
  assumes "b \<ge> 0"
  shows "a^k - b^k \<le> (a-b) * k * a^(k-1)"
proof -
  have "a^k - b^k = (a-b) * (\<Sum>i = 0..<k. a ^ i * b ^ (k - 1 - i))"
    by (rule power_diff_sum)
  also have "... \<le> (a-b) * (\<Sum>i = 0..<k. a^i * a^(k-1-i))"
    using assms by (intro mult_left_mono sum_mono mult_right_mono power_mono, auto)
  also have "... = (a-b) * (k * a^(k-1))"
    by (simp add:power_add[symmetric])
  finally show ?thesis by simp
qed

lemma power_diff_est_2:
  assumes "(a :: real) \<ge> b"
  assumes "b \<ge> 0"
  shows "a^k - b^k \<ge> (a-b) * k * b^(k-1)"
proof -
  have "(a-b) * k * b^(k-1) = (a-b) * (\<Sum>i=0..<k. b^i * b^(k-1-i))"
    by (simp add:power_add[symmetric])
  also have "... \<le>  (a-b)* (\<Sum>i=0..<k. a^i * b^(k-1-i))"
    using assms
    by (intro mult_left_mono sum_mono mult_right_mono power_mono) auto
  also have "... = a^k - b^k"
    by (rule power_diff_sum[symmetric])
  finally show ?thesis by simp
qed

lemma of_bool_prod:
  assumes "finite R"
  shows "(\<Prod> j \<in> R. of_bool(f j)) = (of_bool(\<forall>j \<in> R. f j) :: real)"
  using assms by (induction R rule:finite_induct) auto

text \<open>Additional results about falling factorials:\<close>

lemma ffact_nonneg:
  fixes x :: real
  assumes "k - 1 \<le> x"
  shows "ffact k x \<ge> 0"
  using assms unfolding prod_ffact[symmetric]
  by (intro prod_nonneg ballI) simp

lemma ffact_pos:
  fixes x :: real
  assumes "k - 1 < x"
  shows "ffact k x > 0"
  using assms unfolding prod_ffact[symmetric]
  by (intro prod_pos ballI) simp

lemma ffact_mono:
  fixes x y :: real
  assumes "k-1 \<le> x" "x \<le> y"
  shows "ffact k x \<le> ffact k y"
  using assms
  unfolding prod_ffact[symmetric]
  by (intro prod_mono) auto

lemma ffact_of_nat_nonneg:
  fixes x :: "'a :: {comm_ring_1, linordered_nonzero_semiring}"
  assumes "x \<in> \<nat>"
  shows "ffact k x \<ge> 0"
proof -
  obtain y where y_def: "x = of_nat y"
    using assms(1) Nats_cases by auto
  have "(0::'a) \<le> of_nat (ffact k y)"
    by simp
  also have "... = ffact k x"
    by (simp add:of_nat_ffact y_def)
  finally show ?thesis by simp
qed

lemma ffact_suc_diff:
  fixes x :: "('a :: comm_ring_1)"
  shows "ffact k x - ffact k (x-1) = of_nat k * ffact (k-1) (x-1)" (is "?L = ?R")
proof (cases "k")
  case 0
  then show ?thesis by simp
next
  case (Suc n)
  hence "?L = ffact (Suc n) x - ffact (Suc n) (x-1)" by simp
  also have "... =  x * ffact n (x-1) - ((x-1)-of_nat n) * ffact n (x-1)"
    by (subst (1) ffact_Suc, simp add: ffact_Suc_rev)
  also have "... = of_nat (Suc n)  * ffact n (x-1)"
    by (simp add:algebra_simps)
  also have "... = of_nat k * ffact (k-1) (x-1)" using Suc by simp
  finally show ?thesis by simp
qed

lemma ffact_bound:
  "ffact k (n::nat) \<le> n^k"
proof -
  have "ffact k n = (\<Prod>i=0..<k. (n-i))"
    unfolding prod_ffact_nat[symmetric]
    by simp
  also have "... \<le> (\<Prod>i=0..<k. n)"
    by (intro prod_mono) auto
  also have "... = n^k"
    by simp
  finally show ?thesis by simp
qed

lemma fact_moment_binomial:
  fixes n :: nat and \<alpha> :: real
  assumes "\<alpha> \<in> {0..1}"
  defines "p \<equiv> binomial_pmf n \<alpha>"
  shows "(\<integral>\<omega>. ffact s (real \<omega>) \<partial>p) = ffact s (real n) * \<alpha>^s" (is "?L = ?R")
proof (cases "s \<le> n")
  case True
  have "?L =  (\<Sum>k\<le>n. (real (n choose k) * \<alpha> ^ k * (1 - \<alpha>) ^ (n - k)) * real (ffact s k))"
    unfolding p_def using assms by (subst expectation_binomial_pmf') (auto simp add:of_nat_ffact)
  also have "... = (\<Sum>k \<in> {0+s..(n-s)+s}. (real (n choose k) * \<alpha> ^ k * (1 - \<alpha>) ^ (n - k)) * ffact s k)"
    using True ffact_nat_triv by (intro sum.mono_neutral_cong_right) auto
  also have "... = (\<Sum>k=0..n-s. \<alpha>^s * real (n choose (k+s)) * \<alpha>^k * (1-\<alpha>)^(n-(k+s)) *ffact s (k+s))"
    by (subst sum.atLeastAtMost_shift_bounds, simp add:algebra_simps power_add)
  also have "... = \<alpha>^s * (\<Sum>k\<le>n-s. real (n choose (k+s))*ffact s (k+s)*\<alpha>^k*(1-\<alpha>)^((n-s)-k))"
    using atMost_atLeast0 by (simp add: sum_distrib_left algebra_simps cong:sum.cong)
  also have "... = \<alpha>^s * (\<Sum>k\<le>n-s. real (n choose (k+s))*fact (k+s) / fact k * \<alpha>^k*(1-\<alpha>)^((n-s)-k))"
    using real_of_nat_div[OF fact_dvd[OF le_add1]]
    by (subst fact_div_fact_ffact_nat[symmetric], auto)
  also have "... = \<alpha>^s * (\<Sum>k\<le>n-s.
    (fact n / fact (n-s)) * fact (n-s) / (fact ((n-s)-k) * fact k) * \<alpha>^k*(1-\<alpha>)^((n-s)-k))"
    using True by (intro arg_cong2[where f="(*)"] sum.cong)
     (auto simp add: binomial_fact algebra_simps)
  also have "... = \<alpha>^s * (fact n / fact (n - s)) *
    (\<Sum>k\<le>n-s. fact (n-s) / (fact ((n-s)-k) * fact k) * \<alpha>^k*(1-\<alpha>)^((n-s)-k))"
    by (simp add:sum_distrib_left algebra_simps)
  also have "... = \<alpha>^s * (fact n / fact (n - s)) * (\<Sum>k\<le>n-s. ((n-s) choose k) * \<alpha>^k*(1-\<alpha>)^((n-s)-k))"
    using True by (intro_cong "[\<sigma>\<^sub>2(*)]" more: sum.cong) (auto simp add: binomial_fact)
  also have "... = \<alpha>^s * real (fact n div fact (n - s)) * (\<alpha>+(1-\<alpha>))^(n-s)"
    using True real_of_nat_div[OF fact_dvd] by (subst binomial_ring, simp)
  also have "... = \<alpha>^s * real (ffact s n)"
    by (subst fact_div_fact_ffact_nat[OF True], simp)
  also have "... = ?R"
    by (subst of_nat_ffact, simp)
  finally show ?thesis by simp
next
  case False
  have "?L =  (\<Sum>k\<le>n. (real (n choose k) * \<alpha> ^ k * (1 - \<alpha>) ^ (n - k)) * real (ffact s k))"
    unfolding p_def using assms by (subst expectation_binomial_pmf') (auto simp add:of_nat_ffact)
  also have "... = (\<Sum>k\<le>n. (real (n choose k) * \<alpha> ^ k * (1 - \<alpha>) ^ (n - k)) * real 0)"
    using False
    by (intro_cong "[\<sigma>\<^sub>2(*),\<sigma>\<^sub>1 of_nat]" more: sum.cong ffact_nat_triv) auto
  also have "... = 0" by simp
  also have "... = real (ffact s n) * \<alpha>^s"
    using False by (subst ffact_nat_triv, auto)
  also have "... = ?R"
    by (subst of_nat_ffact, simp)
  finally show ?thesis by simp
qed

text \<open>The following describes polynomials of a given maximal degree as a subset of the functions,
similar to the subsets @{term "\<int>"} or @{term "\<rat>"} as subsets of larger number classes.\<close>

definition Polynomials ("\<bbbP>")
  where "Polynomials k = {f. \<exists>p. f = poly p \<and> degree p \<le> k}"

lemma Polynomials_mono:
  assumes "s \<le> t"
  shows "\<bbbP> s \<subseteq> \<bbbP> t"
  using assms unfolding Polynomials_def by auto

lemma Polynomials_addI:
  assumes "f \<in> \<bbbP> k" "g \<in> \<bbbP> k"
  shows "(\<lambda>\<omega>. f \<omega> + g \<omega>) \<in> \<bbbP> k"
proof -
  obtain pf pg where fg_def: "f = poly pf" "degree pf  \<le> k" "g = poly pg" "degree pg \<le> k"
    using assms unfolding Polynomials_def by blast
  hence "degree (pf + pg) \<le> k" "(\<lambda>x. f x + g x) = poly (pf + pg)"
    using degree_add_le by auto
  thus ?thesis unfolding Polynomials_def by auto
qed

lemma Polynomials_diffI:
  fixes f g :: "'a :: comm_ring \<Rightarrow> 'a"
  assumes "f \<in> \<bbbP> k" "g \<in> \<bbbP> k"
  shows "(\<lambda>x. f x - g x) \<in> \<bbbP> k"
proof -
  obtain pf pg where fg_def: "f = poly pf" "degree pf  \<le> k" "g = poly pg" "degree pg \<le> k"
    using assms unfolding Polynomials_def by blast
  hence "degree (pf - pg) \<le> k" "(\<lambda>x. f x - g x) = poly (pf - pg)"
    using degree_diff_le by auto
  thus ?thesis unfolding Polynomials_def by auto
qed

lemma Polynomials_idI:
  "(\<lambda>x. x) \<in> (\<bbbP> 1 :: ('a::comm_ring_1 \<Rightarrow> 'a) set)"
proof -
  have "(\<lambda>x. x) = poly [: 0,(1::'a) :]"
    by (intro ext, auto)
  also have "... \<in> \<bbbP> 1"
    unfolding Polynomials_def by auto
  finally show ?thesis by simp
qed

lemma Polynomials_constI:
  "(\<lambda>x. c) \<in> \<bbbP> k"
proof -
  have "(\<lambda>x. c) = poly [: c :]"
    by (intro ext, simp)
  also have "... \<in> \<bbbP> k"
    unfolding Polynomials_def by auto
  finally show ?thesis by simp
qed

lemma Polynomials_multI:
  fixes f g :: "'a :: {comm_ring} \<Rightarrow> 'a"
  assumes "f \<in> \<bbbP> s" "g \<in> \<bbbP> t"
  shows "(\<lambda>x. f x * g x) \<in> \<bbbP> (s+t)"
proof -
  obtain pf pg where xy_def: "f = poly pf" "degree pf \<le> s" "g = poly pg" "degree pg \<le> t"
    using assms unfolding Polynomials_def by blast

  have "degree (pf * pg) \<le> degree pf + degree pg"
    by (intro degree_mult_le)
  also have "... \<le> s + t"
    using xy_def by (intro add_mono) auto
  finally have "degree (pf * pg) \<le> s+t" by simp
  moreover have "(\<lambda>x. f x * g x) = poly (pf * pg)"
    using xy_def by auto
  ultimately show ?thesis unfolding Polynomials_def by auto
qed

lemma Polynomials_composeI:
  fixes f g :: "'a :: {comm_semiring_0, semiring_no_zero_divisors} \<Rightarrow> 'a"
  assumes "f \<in> \<bbbP> s" "g \<in> \<bbbP> t"
  shows "(\<lambda>x. f (g x)) \<in> \<bbbP> (s*t)"
proof -
  obtain pf pg where xy_def: "f = poly pf" "degree pf \<le> s" "g = poly pg" "degree pg \<le> t"
    using assms unfolding Polynomials_def by blast
  have "degree (pf \<circ>\<^sub>p pg) = degree pf * degree pg"
    by (intro degree_pcompose)
  also have "... \<le> s * t"
    using xy_def by (intro mult_mono) auto
  finally have "degree (pf \<circ>\<^sub>p pg) \<le> s * t"
    by simp
  moreover have "(\<lambda>x. f (g x)) = poly (pf \<circ>\<^sub>p pg)"
    unfolding xy_def
    by (intro ext poly_pcompose[symmetric])
  ultimately show ?thesis unfolding Polynomials_def by auto
qed

lemma Polynomials_const_left_multI:
  fixes c :: "'a :: {comm_ring}"
  assumes "f \<in> \<bbbP> k"
  shows "(\<lambda>x. c * f x) \<in> \<bbbP> k"
proof -
  have "(\<lambda>x. c * f x) \<in> \<bbbP> (0+k)"
    by (intro Polynomials_multI Polynomials_constI assms)
  thus ?thesis by simp
qed

lemma Polynomials_const_right_multI:
  fixes c :: "'a :: {comm_ring}"
  assumes "f \<in> \<bbbP> k"
  shows "(\<lambda>x. f x * c) \<in> \<bbbP> k"
proof -
  have "(\<lambda>x. f x * c) \<in> \<bbbP> (k+0)"
    by (intro Polynomials_multI Polynomials_constI assms)
  thus ?thesis by simp
qed

lemma Polynomials_const_divI:
  fixes c :: "'a :: {field}"
  assumes "f \<in> \<bbbP> k"
  shows "(\<lambda>x. f x / c) \<in> \<bbbP> k"
proof -
  have "(\<lambda>x. f x * (1/c)) \<in> \<bbbP> (k+0)"
    by (intro Polynomials_multI Polynomials_constI assms)
  thus ?thesis by simp
qed

lemma Polynomials_ffact: "(\<lambda>x. ffact s (x - y))  \<in> (\<bbbP> s :: ('a :: comm_ring_1  \<Rightarrow> 'a) set)"
proof (induction s arbitrary: y)
  case 0
  then show ?case
    using Polynomials_constI[where c="1"] by simp
next
  case (Suc s)
  have "(\<lambda>(x :: 'a). ffact (Suc s) (x-y)) = (\<lambda>x. (x-y) * ffact s (x - (y+1)))"
    by (simp add: ffact_Suc algebra_simps)
  also have "... \<in> \<bbbP> (1+s)"
    by (intro Polynomials_multI Suc Polynomials_diffI Polynomials_idI Polynomials_constI)
  finally show ?case by simp
qed

lemmas Polynomials_intros =
  Polynomials_const_divI
  Polynomials_composeI
  Polynomials_const_left_multI
  Polynomials_const_right_multI
  Polynomials_multI
  Polynomials_addI
  Polynomials_diffI
  Polynomials_idI
  Polynomials_constI
  Polynomials_ffact

definition C\<^sub>2 :: real where "C\<^sub>2 = 7.5"
definition C\<^sub>3 :: real where "C\<^sub>3 = 16"

text \<open>A locale fixing the sets of balls and bins\<close>

locale balls_and_bins_abs =
  fixes R :: "'a set" and B :: "'b set"
  assumes fin_B: "finite B" and B_ne: "B \<noteq> {}"
  assumes fin_R: "finite R"
begin

text \<open>Independent balls and bins space:\<close>
definition \<Omega>
  where "\<Omega> = prod_pmf R (\<lambda>_. pmf_of_set B)"

lemma set_pmf_\<Omega>: "set_pmf \<Omega> = R \<rightarrow>\<^sub>E B"
  unfolding \<Omega>_def set_prod_pmf[OF fin_R]
  by  (simp add:comp_def set_pmf_of_set[OF B_ne fin_B])

lemma card_B_gt_0: "card B > 0"
  using B_ne fin_B by auto

lemma card_B_ge_1: "card B \<ge> 1"
  using card_B_gt_0 by simp

definition "Z j \<omega> = real (card {i. i \<in> R \<and> \<omega> i = (j::'b)})"
definition "Y \<omega> = real (card (\<omega> ` R))"
definition "\<mu> = real (card B) * (1 - (1-1/real (card B))^card R)"

text \<open>Factorial moments for the random variable describing the number of times a bin will be hit:\<close>

lemma fact_moment_balls_and_bins:
  assumes "J \<subseteq> B" "J \<noteq> {}"
  shows "(\<integral>\<omega>. ffact s (\<Sum>j \<in> J. Z j \<omega>) \<partial>\<Omega>) =
    ffact s (real (card R)) * (real (card J) / real (card B))^s"
    (is "?L = ?R")
proof -
  let ?\<alpha> = "real (card J) / real (card B)"
  let ?q = "binomial_pmf (card R) ?\<alpha>"
  let ?Y = "(\<lambda>\<omega>. card {r \<in> R. \<omega> r \<in> J})"

  have fin_J: "finite J"
    using finite_subset assms(1) fin_B by auto

  have Z_sum_eq: "(\<Sum>j \<in> J. Z j \<omega>) = real (?Y \<omega>)" for \<omega>
  proof -
    have "?Y \<omega> = card (\<Union>j \<in> J. {r \<in> R. \<omega> r= j})"
      by (intro arg_cong[where f="card"]) auto
    also have "... =  (\<Sum>i\<in>J. card {r \<in> R. \<omega> r = i})"
      using fin_R fin_J by (intro card_UN_disjoint) auto
    finally have "?Y \<omega> = (\<Sum>j \<in> J. card {r \<in> R. \<omega> r  = j})" by simp
    thus ?thesis
    unfolding Z_def of_nat_sum[symmetric] by simp
  qed

  have card_J: "card J \<le> card B"
    using assms(1) fin_B card_mono by auto
  have \<alpha>_range: "?\<alpha> \<ge> 0" "?\<alpha> \<le> 1"
    using card_J card_B_gt_0 by auto

  have "pmf (map_pmf (\<lambda>\<omega>. \<omega> \<in> J) (pmf_of_set B)) x = pmf (bernoulli_pmf ?\<alpha>) x"
    (is "?L1=?R1") for x
  proof -
    have "?L1 = real (card (B \<inter> {\<omega>. (\<omega> \<in> J) = x})) / real (card B)"
      using B_ne fin_B
      by (simp add:pmf_map measure_pmf_of_set vimage_def)
    also have "... = (if x then (card J) else (card (B - J))) / real (card B)"
      using Int_absorb1[OF assms(1)] by (auto simp add:Diff_eq Int_def)
    also have "... = (if x then (card J) / card B else (real (card B) - card J) / real (card B))"
      using card_J fin_J assms(1) by (simp add: of_nat_diff card_Diff_subset)
    also have "... = (if x then ?\<alpha> else (1 - ?\<alpha>))"
      using card_B_gt_0 by (simp add:divide_simps)
    also have "... = ?R1"
      using \<alpha>_range by auto
    finally show ?thesis by simp
  qed
  hence c:"map_pmf (\<lambda>\<omega>. \<omega> \<in> J) (pmf_of_set B) = bernoulli_pmf ?\<alpha>"
    by (intro pmf_eqI) simp

  have "map_pmf (\<lambda>\<omega>. \<lambda>r \<in> R. \<omega> r \<in> J) \<Omega> = prod_pmf R (\<lambda>_. (map_pmf (\<lambda>\<omega>. \<omega> \<in> J) (pmf_of_set B)))"
    unfolding map_pmf_def \<Omega>_def restrict_def using fin_R
    by (subst Pi_pmf_bind[where d'="undefined"]) auto
  also have "... = prod_pmf R (\<lambda>_. bernoulli_pmf ?\<alpha>)"
    unfolding c by simp
  finally have b:"map_pmf (\<lambda>\<omega>. \<lambda>r \<in> R. \<omega> r \<in> J) \<Omega>  =  prod_pmf R (\<lambda>_. bernoulli_pmf ?\<alpha>)"
    by simp

  have "map_pmf ?Y \<Omega> = map_pmf ((\<lambda>\<omega>. card {r \<in> R. \<omega> r}) \<circ> (\<lambda>\<omega>. \<lambda>r\<in>R. \<omega> r \<in> J)) \<Omega>"
    unfolding comp_def
    by (intro map_pmf_cong arg_cong[where f="card"]) (auto simp add:comp_def)
  also have "... = (map_pmf (\<lambda>\<omega>. card {r \<in> R. \<omega> r}) \<circ> map_pmf (\<lambda>\<omega>. \<lambda>r \<in> R. \<omega> r \<in> J)) \<Omega>"
    by (subst map_pmf_compose[symmetric]) auto
  also have "... = map_pmf (\<lambda>\<omega>. card {r \<in> R. \<omega> r}) (prod_pmf R (\<lambda>_. (bernoulli_pmf ?\<alpha>)))"
    unfolding comp_def b by simp
  also have "... = ?q"
    using \<alpha>_range by (intro binomial_pmf_altdef'[symmetric] fin_R) auto
  finally have a:"map_pmf ?Y \<Omega> =?q"
    by simp

  have "?L = (\<integral>\<omega>. ffact s (real (?Y \<omega>)) \<partial>\<Omega>)"
    unfolding Z_sum_eq by simp
  also have "... = (\<integral>\<omega>. ffact s (real \<omega>) \<partial>(map_pmf ?Y \<Omega>))"
    by simp
  also have "... = (\<integral>\<omega>. ffact s (real \<omega>) \<partial>?q)"
    unfolding a by simp
  also have "... = ?R"
    using \<alpha>_range by (subst fact_moment_binomial, auto)
  finally show ?thesis by simp
qed

text \<open>Expectation and variance for the number of distinct bins that are hit by at least one ball
in the fully independent model. The result for the variance is improved by a factor of $4$ w.r.t.
the paper.\<close>

lemma
  shows exp_balls_and_bins: "measure_pmf.expectation \<Omega> Y = \<mu>" (is "?AL = ?AR")
    and var_balls_and_bins: "measure_pmf.variance \<Omega> Y \<le> card R * (real (card R) - 1) / card B"
      (is "?BL \<le> ?BR")
proof -
  let ?b = "real (card B)"
  let ?r = "card R"
  define Z :: "'b \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> real"
    where "Z = (\<lambda>i \<omega>. of_bool(i \<notin> \<omega> ` R))"
  define \<alpha> where "\<alpha> = (1 - 1 / ?b)^?r"
  define \<beta> where "\<beta> = (1 - 2 / ?b)^?r"

  have "card (B \<times> B \<inter> {x. fst x = snd x}) = card ((\<lambda>x. (x,x)) ` B)"
    by (intro arg_cong[where f="card"]) auto
  also have "... = card B"
    by (intro card_image, simp add:inj_on_def)
  finally have d: "card (B \<times> B \<inter> {x. fst x = snd x}) = card B"
    by simp
  hence count_1: "real (card (B \<times> B \<inter> {x. fst x = snd x})) = card B"
    by simp

  have "card B + card (B \<times> B \<inter> -{x. fst x = snd x}) =
    card (B \<times> B \<inter> {x. fst x = snd x}) + card (B \<times> B \<inter> -{x. fst x = snd x})"
    by (subst d) simp
  also have "... = card ((B \<times> B \<inter> {x. fst x = snd x}) \<union> (B \<times> B \<inter> -{x. fst x = snd x}))"
    using finite_subset[OF _ finite_cartesian_product[OF fin_B fin_B]]
    by (intro card_Un_disjoint[symmetric]) auto
  also have "... = card (B \<times> B)"
    by (intro arg_cong[where f="card"]) auto
  also have "... = card B^2"
    unfolding card_cartesian_product by (simp add:power2_eq_square)
  finally have "card B + card (B \<times> B \<inter> -{x. fst x = snd x}) = card B^2" by simp

  hence count_2: "real (card (B \<times> B \<inter> -{x. fst x = snd x})) = real (card B)^2 - card B"
    by (simp add:algebra_simps flip: of_nat_add of_nat_power)

  hence "finite (set_pmf \<Omega>)"
    unfolding set_pmf_\<Omega>
    using fin_R fin_B by (auto intro!:finite_PiE)
  hence int: "integrable (measure_pmf \<Omega>) f"
    for f :: "('a \<Rightarrow> 'b) \<Rightarrow> real"
    by (intro integrable_measure_pmf_finite) simp

  have a:"prob_space.indep_vars (measure_pmf \<Omega>) (\<lambda>i. discrete) (\<lambda>x \<omega>. \<omega> x) R"
    unfolding \<Omega>_def using indep_vars_Pi_pmf[OF fin_R] by metis
  have b: "(\<integral>\<omega>. of_bool (\<omega> ` R \<subseteq> A) \<partial>\<Omega>) = (real (card (B \<inter> A)) / real (card B))^card R"
    (is "?L = ?R") for A
  proof -
    have "?L = (\<integral>\<omega>. (\<Prod> j \<in> R. of_bool(\<omega> j \<in> A)) \<partial>\<Omega>)"
      by (intro Bochner_Integration.integral_cong ext)
        (auto simp add: of_bool_prod[OF fin_R])
    also have "... = (\<Prod> j \<in> R. (\<integral>\<omega>. of_bool(\<omega> j \<in> A) \<partial>\<Omega>))"
      using fin_R
      by (intro prob_space.indep_vars_lebesgue_integral[OF prob_space_measure_pmf] int
          prob_space.indep_vars_compose2[OF prob_space_measure_pmf a]) auto
    also have "... = (\<Prod> j \<in> R. (\<integral>\<omega>. of_bool(\<omega> \<in> A) \<partial>(map_pmf (\<lambda>\<omega>. \<omega> j) \<Omega>)))"
      by simp
    also have "... = (\<Prod> j \<in> R. (\<integral>\<omega>. of_bool(\<omega> \<in> A) \<partial>(pmf_of_set B)))"
      unfolding \<Omega>_def by (subst Pi_pmf_component[OF fin_R]) simp
    also have "... = ((\<Sum>\<omega>\<in>B. of_bool (\<omega> \<in> A)) / real (card B)) ^ card R"
      by (simp add: integral_pmf_of_set[OF B_ne fin_B])
    also have "... = ?R"
      unfolding of_bool_def sum.If_cases[OF fin_B] by simp
    finally show ?thesis by simp
  qed

  have Z_exp: "(\<integral>\<omega>. Z i \<omega> \<partial>\<Omega>) = \<alpha>" if "i \<in> B" for i
  proof -
    have "real (card (B \<inter> -{i})) = real (card (B - {i}))"
      by (intro_cong "[\<sigma>\<^sub>1 card,\<sigma>\<^sub>1 of_nat]") auto
    also have "... = real (card B - card {i})"
      using that by (subst card_Diff_subset)  auto
    also have "... = real (card B) - real (card {i})"
      using fin_B that by (intro of_nat_diff card_mono) auto
    finally have c: "real (card (B \<inter> -{i})) = real (card B) - 1"
      by simp

    have "(\<integral>\<omega>. Z i \<omega> \<partial>\<Omega>) = (\<integral>\<omega>. of_bool(\<omega> ` R \<subseteq> - {i}) \<partial>\<Omega>)"
      unfolding Z_def by simp
    also have "... = (real (card (B \<inter> -{i})) / real (card B))^card R"
      by (intro b)
    also have "... = ((real (card B) -1) / real (card B))^card R"
      by (subst c) simp
    also have "... = \<alpha>"
      unfolding \<alpha>_def using card_B_gt_0
      by (simp add:divide_eq_eq diff_divide_distrib)
    finally show ?thesis
      by simp
  qed

  have Z_prod_exp: "(\<integral>\<omega>. Z i \<omega> * Z j \<omega> \<partial>\<Omega>) = (if i = j then \<alpha> else \<beta>)"
    if "i \<in> B" "j \<in> B" for i j
  proof -
    have "real (card (B \<inter> -{i,j})) = real (card (B - {i,j}))"
      by (intro_cong "[\<sigma>\<^sub>1 card,\<sigma>\<^sub>1 of_nat]") auto
    also have "... = real (card B - card {i,j})"
      using that by (subst card_Diff_subset)  auto
    also have "... = real (card B) - real (card {i,j})"
      using fin_B that by (intro of_nat_diff card_mono) auto
    finally have c: "real (card (B \<inter> -{i,j})) = real (card B) - card {i,j}"
      by simp

    have "(\<integral>\<omega>. Z i \<omega> * Z j \<omega> \<partial>\<Omega>) = (\<integral>\<omega>. of_bool(\<omega> ` R \<subseteq> - {i,j}) \<partial>\<Omega>)"
      unfolding Z_def of_bool_conj[symmetric]
      by (intro integral_cong ext) auto
    also have "... = (real (card (B \<inter> -{i,j})) / real (card B))^card R"
      by (intro b)
    also have "... = ((real (card B) - card {i,j}) / real (card B))^card R"
      by (subst c) simp
    also have "... = (if i = j then \<alpha> else \<beta>)"
      unfolding \<alpha>_def \<beta>_def using card_B_gt_0
      by (simp add:divide_eq_eq diff_divide_distrib)
    finally show ?thesis by simp
  qed

  have Y_eq: "Y \<omega> = (\<Sum>i \<in> B. 1 - Z i \<omega>)" if "\<omega> \<in> set_pmf \<Omega>" for \<omega>
  proof -
    have "set_pmf \<Omega> \<subseteq> Pi R (\<lambda>_. B)"
      using set_pmf_\<Omega> by (simp add:PiE_def)
    hence "\<omega> ` R \<subseteq> B"
      using that by auto
    hence "Y \<omega> = card (B \<inter> \<omega> ` R)"
      unfolding Y_def using Int_absorb1 by metis
    also have "... = (\<Sum> i \<in> B. of_bool(i \<in> \<omega> ` R))"
      unfolding of_bool_def sum.If_cases[OF fin_B] by(simp)
    also have "... = (\<Sum> i \<in> B. 1 - Z i \<omega>)"
      unfolding Z_def by (intro sum.cong) (auto simp add:of_bool_def)
    finally show "Y \<omega> = (\<Sum>i \<in> B. 1 - Z i \<omega>)" by simp
  qed

  have Y_sq_eq: "(Y \<omega>)\<^sup>2 = (\<Sum>(i,j) \<in> B \<times> B. 1 - Z i \<omega> - Z j \<omega> + Z i \<omega> * Z j \<omega>)"
    if "\<omega> \<in> set_pmf \<Omega>" for \<omega>
    unfolding Y_eq[OF that] power2_eq_square sum_product sum.cartesian_product
    by (intro sum.cong) (auto simp add:algebra_simps)

  have "measure_pmf.expectation \<Omega> Y = (\<integral>\<omega>. (\<Sum>i \<in> B. 1 - Z i \<omega>) \<partial>\<Omega>)"
    using Y_eq by (intro integral_cong_AE AE_pmfI) auto
  also have "... = (\<Sum>i \<in> B. 1 - (\<integral>\<omega>. Z i \<omega> \<partial>\<Omega>))"
    using int by simp
  also have "... = ?b * (1 - \<alpha>)"
    using Z_exp by simp
  also have "... = ?AR"
    unfolding \<alpha>_def \<mu>_def by simp
  finally show "?AL = ?AR" by simp

  have "measure_pmf.variance \<Omega> Y = (\<integral>\<omega>. Y \<omega>^2 \<partial>\<Omega>) - (\<integral>\<omega>. Y \<omega> \<partial>\<Omega>)^2"
    using int by (subst measure_pmf.variance_eq) auto
  also have "... =
    (\<integral>\<omega>. (\<Sum>i \<in> B \<times> B. 1 - Z (fst i) \<omega> - Z (snd i) \<omega> + Z (fst i) \<omega> * Z (snd i) \<omega>) \<partial>\<Omega>) -
    (\<integral>\<omega>. (\<Sum>i \<in> B. 1 - Z i \<omega>) \<partial>\<Omega>)^2"
    using Y_eq Y_sq_eq
    by (intro_cong "[\<sigma>\<^sub>2(-),\<sigma>\<^sub>2 power]" more: integral_cong_AE AE_pmfI) (auto simp add:case_prod_beta)
  also have "... =
    (\<Sum>i \<in> B \<times> B. (\<integral>\<omega>. (1 - Z (fst i) \<omega> - Z (snd i) \<omega> + Z (fst i) \<omega> * Z (snd i) \<omega>) \<partial>\<Omega>)) -
    (\<Sum>i \<in> B. (\<integral>\<omega>. (1 - Z i \<omega>) \<partial>\<Omega>))^2"
    by (intro_cong "[\<sigma>\<^sub>2 (-), \<sigma>\<^sub>2 power]" more: integral_sum int)
  also have "... =
    (\<Sum>i \<in> B \<times> B. (\<integral>\<omega>. (1 - Z (fst i) \<omega> - Z (snd i) \<omega> + Z (fst i) \<omega> * Z (snd i) \<omega>) \<partial>\<Omega>)) -
    (\<Sum>i \<in> B \<times> B. (\<integral>\<omega>. (1 - Z (fst i) \<omega>) \<partial>\<Omega>) * (\<integral>\<omega>. (1 - Z (snd i) \<omega>) \<partial>\<Omega>))"
    unfolding power2_eq_square sum_product sum.cartesian_product
    by (simp add:case_prod_beta)
  also have "... = (\<Sum>(i,j) \<in> B \<times> B. (\<integral>\<omega>. (1 - Z i \<omega> - Z j \<omega> + Z i \<omega> * Z j \<omega>) \<partial>\<Omega>) -
    (\<integral>\<omega>. (1 - Z i \<omega>) \<partial>\<Omega>) * (\<integral>\<omega>. (1 - Z j \<omega>) \<partial>\<Omega>))"
    by (subst sum_subtractf[symmetric], simp add:case_prod_beta)
  also have "... = (\<Sum>(i,j) \<in> B \<times> B. (\<integral>\<omega>. Z i \<omega> * Z j \<omega> \<partial>\<Omega>) -(\<integral>\<omega>. Z i \<omega> \<partial>\<Omega>) * (\<integral> \<omega>. Z j \<omega> \<partial>\<Omega>))"
    using int by (intro sum.cong refl) (simp add:algebra_simps case_prod_beta)
  also have "... = (\<Sum>i \<in> B \<times> B. (if fst i = snd i then \<alpha> - \<alpha>^2 else \<beta> - \<alpha>^2))"
    by (intro sum.cong refl)
      (simp add:Z_exp Z_prod_exp mem_Times_iff case_prod_beta power2_eq_square)
  also have "... = ?b * (\<alpha> - \<alpha>\<^sup>2) + (?b^2 - card B) * (\<beta> - \<alpha>\<^sup>2)"
    using count_1 count_2 finite_cartesian_product fin_B by (subst sum.If_cases) auto
  also have "... = ?b^2 * (\<beta> - \<alpha>\<^sup>2) + ?b * (\<alpha> - \<beta>)"
    by (simp add:algebra_simps)
  also have "... = ?b * ((1-1/?b)^?r - (1-2/?b)^?r) - ?b^2 * (((1-1/?b)^2)^?r - (1-2/?b)^?r)"
    unfolding \<beta>_def \<alpha>_def
    by (simp add: power_mult[symmetric] algebra_simps)
  also have "... \<le> card R * (real (card R) - 1)/ card B" (is "?L \<le> ?R")
  proof (cases "?b \<ge> 2")
    case True
    have "?L \<le>
    ?b * (((1 - 1 /?b) - (1-2 /?b)) * ?r * (1-1/?b)^(?r - 1)) -
    ?b^2 * ((((1-1 /?b)^2) - ((1 - 2 /?b))) * ?r * ((1-2/?b))^(?r - 1))"
    using True
    by (intro diff_mono mult_left_mono power_diff_est_2 power_diff_est divide_right_mono)
      (auto simp add:power2_eq_square algebra_simps)
    also have "... = ?b * ((1/?b) * ?r * (1-1/?b)^(?r-1)) - ?b^2*((1/?b^2)*?r*((1-2/?b))^(?r-1))"
      by (intro arg_cong2[where f="(-)"] arg_cong2[where f="(*)"] refl)
        (auto simp add:algebra_simps power2_eq_square)
    also have "... = ?r * ((1-1/?b)^(?r - 1) - ((1-2/?b))^(?r - 1))"
      by (simp add:algebra_simps)
    also have "... \<le> ?r * (((1-1/?b) - (1-2/?b)) * (?r - 1) * (1-1/?b)^(?r -1 -1))"
      using True by (intro mult_left_mono power_diff_est) (auto simp add:algebra_simps)
    also have "... \<le> ?r * ((1/?b) * (?r - 1) * 1^(?r - 1-1))"
      using True by (intro mult_left_mono mult_mono power_mono) auto
    also have "... =  ?R"
      using card_B_gt_0 by auto
    finally show "?L \<le> ?R" by simp
  next
    case False
    hence "?b = 1" using card_B_ge_1 by simp
    thus "?L \<le> ?R"
      by (cases "card R =0") auto
  qed
  finally show "measure_pmf.variance \<Omega> Y \<le> card R * (real (card R) - 1)/ card B"
    by simp
qed

definition "lim_balls_and_bins k p = (
   prob_space.k_wise_indep_vars (measure_pmf p) k (\<lambda>_. discrete) (\<lambda>x \<omega>. \<omega> x) R \<and>
  (\<forall>x. x \<in> R \<longrightarrow> map_pmf (\<lambda>\<omega>. \<omega> x) p = pmf_of_set B))"

lemma indep:
  assumes "lim_balls_and_bins k p"
  shows "prob_space.k_wise_indep_vars (measure_pmf p) k (\<lambda>_. discrete) (\<lambda>x \<omega>. \<omega> x) R"
  using assms lim_balls_and_bins_def by simp

lemma ran:
  assumes "lim_balls_and_bins k p" "x \<in> R"
  shows "map_pmf (\<lambda>\<omega>. \<omega> x) p = pmf_of_set B"
  using assms lim_balls_and_bins_def by simp

lemma Z_integrable:
  fixes f :: "real \<Rightarrow> real"
  assumes "lim_balls_and_bins k p"
  shows "integrable p (\<lambda>\<omega>. f (Z i \<omega>) )"
  unfolding Z_def using fin_R card_mono
  by (intro integrable_pmf_iff_bounded[where C="Max (abs ` f ` real ` {..card R})"])
   fastforce+

lemma Z_any_integrable_2:
 fixes f :: "real \<Rightarrow> real"
  assumes "lim_balls_and_bins k p"
  shows "integrable p (\<lambda>\<omega>. f (Z i \<omega> + Z j \<omega>))"
proof -
  have q:"real (card A) + real (card B) \<in> real ` {..2 * card R}" if "A \<subseteq> R" "B \<subseteq> R" for A B
  proof -
    have "card A + card B \<le> card R + card R"
      by (intro add_mono card_mono fin_R that)
    also have "... = 2 * card R" by simp
    finally show ?thesis by force
  qed

  thus ?thesis
    unfolding Z_def using fin_R card_mono abs_triangle_ineq
    by (intro integrable_pmf_iff_bounded[where C="Max (abs ` f ` real ` {..2*card R})"] Max_ge
        finite_imageI imageI) auto
qed

lemma hit_count_prod_exp:
  assumes "j1 \<in> B" "j2 \<in> B" "s+t \<le> k"
  assumes "lim_balls_and_bins k p"
  defines "L \<equiv> {(xs,ys). set xs \<subseteq> R \<and> set ys \<subseteq> R \<and>
    (set xs \<inter> set ys = {} \<or> j1 = j2) \<and> length xs = s \<and> length ys = t}"
  shows "(\<integral>\<omega>. Z j1 \<omega>^s * Z j2 \<omega>^t \<partial>p) =
    (\<Sum>(xs,ys) \<in> L. (1/real (card B))^(card (set xs \<union> set ys)))"
    (is "?L = ?R")
proof -
  define W1 :: "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> real"
    where "W1 = (\<lambda>i \<omega>. of_bool (\<omega> i = j1) :: real)"
  define W2 :: "'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> real"
    where "W2 = (\<lambda>i \<omega>. of_bool (\<omega> i = j2) :: real)"
  define \<tau> :: "'a list \<times> 'a list \<Rightarrow> 'a \<Rightarrow> 'b"
    where "\<tau> = (\<lambda>l x. if x \<in> set (fst l) then j1 else j2)"

  have \<tau>_check_1: "\<tau> l x = j1" if "x \<in> set (fst l)" and "l \<in> L" for x l
    using that unfolding \<tau>_def L_def by auto
  have \<tau>_check_2: "\<tau> l x = j2" if "x \<in> set (snd l)" and "l \<in> L" for x l
    using that unfolding \<tau>_def L_def by auto
  have \<tau>_check_3: "\<tau> l x \<in> B" for x l
    using assms(1,2) unfolding \<tau>_def by simp

  have Z1_eq: "Z j1 \<omega> = (\<Sum>i \<in> R. W1 i \<omega>)" for \<omega>
    using fin_R unfolding Z_def W1_def
    by (simp add:of_bool_def sum.If_cases Int_def)

  have Z2_eq: "Z j2 \<omega> = (\<Sum>i \<in> R. W2 i \<omega>)" for \<omega>
    using fin_R unfolding Z_def W2_def
    by (simp add:of_bool_def sum.If_cases Int_def)

  define \<alpha> where "\<alpha> = 1 / real (card B)"

  have a: "(\<integral>\<omega>. (\<Prod>x\<leftarrow>a. W1 x \<omega>) * (\<Prod>y\<leftarrow>b. W2 y \<omega>) \<partial>p) = 0" (is "?L1 = 0")
    if "x \<in> set a \<inter> set b" "j1 \<noteq> j2" "length a = s" "length b = t" for x a b
  proof -
    have  "(\<Prod>x\<leftarrow>a. W1 x \<omega>) * (\<Prod>y\<leftarrow>b. W2 y \<omega>) = 0" for \<omega>
    proof -
      have "W1 x \<omega> = 0 \<or> W2 x \<omega> = 0"
        unfolding W1_def W2_def using that by simp
      hence "(\<Prod>x\<leftarrow>a. W1 x \<omega>) = 0 \<or> (\<Prod>y\<leftarrow>b. W2 y \<omega>) = 0"
        unfolding prod_list_zero_iff using that(1) by auto
      thus ?thesis by simp
    qed
    hence "?L1 = (\<integral>\<omega>. 0 \<partial>p)"
      by (intro arg_cong2[where f="measure_pmf.expectation"]) auto
    also have "... = 0"
      by simp
    finally show ?thesis by simp
  qed

  have b: "prob_space.indep_vars p (\<lambda>_. discrete) (\<lambda>i \<omega>. \<omega> i) (set (fst x) \<union> set (snd x))"
    if "x \<in> L" for x
  proof -
    have "card (set (fst x) \<union> set (snd x)) \<le> card (set (fst x)) + card (set (snd x))"
      by (intro card_Un_le)
    also have "... \<le> length (fst x) + length (snd x)"
      by (intro add_mono card_length)
    also have "... = s + t"
      using that L_def by auto
    also have "... \<le> k" using assms(3) by simp
    finally have "card (set (fst x) \<union> set (snd x)) \<le> k" by simp
    moreover have "set (fst x) \<union> set (snd x) \<subseteq> R"
      using that L_def by auto
    ultimately show ?thesis
      by (intro prob_space.k_wise_indep_vars_subset[OF prob_space_measure_pmf indep[OF assms(4)]])
       auto
  qed

  have c: "(\<integral>\<omega>. of_bool (\<omega> x = z) \<partial>p) = \<alpha>" (is "?L1 = _")
    if "z \<in> B" "x \<in> R" for x z
  proof -
    have "?L1 = (\<integral>\<omega>. indicator {\<omega>. \<omega> x = z} \<omega> \<partial>p)"
      unfolding indicator_def by simp
    also have "... = measure p {\<omega>. \<omega> x = z}"
      by simp
    also have "... = measure (map_pmf (\<lambda>\<omega>. \<omega> x) p) {z}"
      by (subst measure_map_pmf) (simp add:vimage_def)
    also have "... = measure (pmf_of_set B) {z}"
      using that by (subst ran[OF assms(4)]) auto
    also have "... = 1/card B"
      using fin_B that by (subst measure_pmf_of_set) auto
    also have "... = \<alpha>"
      unfolding \<alpha>_def by simp
    finally show ?thesis by simp
  qed

  have d: "abs x \<le> 1 \<Longrightarrow> abs y \<le> 1 \<Longrightarrow> abs (x*y) \<le> 1" for x y :: real
    by (simp add:abs_mult mult_le_one)
  have e:"(\<And>x. x \<in> set xs \<Longrightarrow> abs x \<le>1) \<Longrightarrow> abs(prod_list xs) \<le> 1 " for xs :: "real list"
    using d by (induction xs, simp, simp)

  have "?L = (\<integral>\<omega>. (\<Sum>j \<in> R. W1 j \<omega>)^s * (\<Sum>j \<in> R. W2 j \<omega>)^t \<partial>p)"
    unfolding Z1_eq Z2_eq by simp
  also have "... = (\<integral>\<omega>. (\<Sum>xs | set xs \<subseteq> R \<and> length xs = s. (\<Prod>x \<leftarrow> xs. W1 x \<omega>)) *
                        (\<Sum>ys | set ys \<subseteq> R \<and> length ys = t. (\<Prod>y \<leftarrow> ys. W2 y \<omega>)) \<partial>p)"
    unfolding sum_power_distrib[OF fin_R] by simp
  also have "... = (\<integral>\<omega>.
    (\<Sum>l\<in>{xs. set xs \<subseteq> R \<and> length xs = s} \<times> {ys. set ys \<subseteq> R \<and> length ys = t}.
      (\<Prod>x\<leftarrow>fst l. W1 x \<omega>) * (\<Prod>y\<leftarrow>snd l. W2 y \<omega>)) \<partial>p)"
    by (intro arg_cong[where f="integral\<^sup>L p"])
      (simp add: sum_product sum.cartesian_product case_prod_beta)
  also have "... = (\<Sum>l\<in>{xs. set xs \<subseteq> R \<and> length xs = s} \<times> {ys. set ys \<subseteq> R \<and> length ys = t}.
    (\<integral>\<omega>. (\<Prod>x\<leftarrow>fst l. W1 x \<omega>) * (\<Prod>y\<leftarrow>snd l. W2 y \<omega>) \<partial>p))"
    unfolding W1_def W2_def
    by (intro integral_sum integrable_pmf_iff_bounded[where C="1"] d e) auto
  also have "... = (\<Sum>l\<in> L. (\<integral>\<omega>. (\<Prod>x\<leftarrow>fst l. W1 x \<omega>) * (\<Prod>y\<leftarrow>snd l. W2 y \<omega>) \<partial>p))"
    unfolding L_def using a by (intro sum.mono_neutral_right finite_cartesian_product
        finite_lists_length_eq fin_R) auto
  also have "... = (\<Sum>l\<in> L. (\<integral>\<omega>. (\<Prod>x\<leftarrow>fst l.
    of_bool(\<omega> x = \<tau> l x)) * (\<Prod>y\<leftarrow>snd l. of_bool(\<omega> y = \<tau> l y)) \<partial>p))"
    unfolding W1_def W2_def using \<tau>_check_1 \<tau>_check_2
    by (intro sum.cong arg_cong[where f="integral\<^sup>L p"] ext arg_cong2[where f="(*)"]
        arg_cong[where f="prod_list"]) auto
  also have "... = (\<Sum>l\<in> L. (\<integral>\<omega>. (\<Prod>x\<leftarrow>(fst l@snd l). of_bool(\<omega> x = \<tau> l x))\<partial> p))"
    by simp
  also have "... = (\<Sum>l\<in> L. (\<integral>\<omega>. (\<Prod>x \<in> set (fst l@snd l).
    of_bool(\<omega> x = \<tau> l x)^count_list (fst l@snd l) x) \<partial> p))"
    unfolding prod_list_eval by simp
  also have "... = (\<Sum>l\<in> L. (\<integral>\<omega>. (\<Prod>x \<in> set (fst l) \<union> set (snd l).
    of_bool(\<omega> x = \<tau> l x)^count_list (fst l@snd l) x) \<partial> p))"
    by simp
  also have "... = (\<Sum>l\<in> L. (\<integral>\<omega>. (\<Prod>x \<in> set (fst l) \<union> set (snd l). of_bool(\<omega> x = \<tau> l x)) \<partial> p))"
    using count_list_gr_1
    by (intro sum.cong arg_cong[where f="integral\<^sup>L p"] ext prod.cong) force+
  also have "... = (\<Sum>l\<in> L. (\<Prod>x \<in> set (fst l) \<union> set (snd l). (\<integral>\<omega>. of_bool(\<omega> x = \<tau> l x) \<partial> p)))"
    by (intro sum.cong prob_space.indep_vars_lebesgue_integral[OF prob_space_measure_pmf]
        integrable_pmf_iff_bounded[where C="1"]
        prob_space.indep_vars_compose2[OF prob_space_measure_pmf b]) auto
  also have "... = (\<Sum>l\<in> L. (\<Prod>x \<in> set (fst l) \<union> set (snd l). \<alpha>))"
    using \<tau>_check_3 unfolding L_def by (intro sum.cong prod.cong c) auto
  also have "... = (\<Sum>l \<in> L. \<alpha>^(card (set (fst l) \<union> set (snd l))))"
    by simp
  also have "... = ?R"
    unfolding L_def \<alpha>_def by (simp add:case_prod_beta)
  finally show ?thesis by simp
qed

lemma hit_count_prod_pow_eq:
  assumes "i \<in> B" "j \<in> B"
  assumes "lim_balls_and_bins k p"
  assumes "lim_balls_and_bins k q"
  assumes "s+t \<le> k"
  shows "(\<integral>\<omega>. (Z i \<omega>)^s * (Z j \<omega>)^t \<partial>p) = (\<integral>\<omega>. (Z i \<omega>)^s * (Z j \<omega>)^t \<partial>q)"
    unfolding hit_count_prod_exp[OF assms(1,2,5,3)]
    unfolding hit_count_prod_exp[OF assms(1,2,5,4)]
    by simp

lemma hit_count_sum_pow_eq:
  assumes "i \<in> B" "j \<in> B"
  assumes "lim_balls_and_bins k p"
  assumes "lim_balls_and_bins k q"
  assumes "s \<le> k"
  shows "(\<integral>\<omega>. (Z i \<omega> + Z j \<omega>)^s \<partial>p) = (\<integral>\<omega>. (Z i \<omega> + Z j \<omega>)^s \<partial>q)"
    (is "?L = ?R")
proof -
  have q2: "\<bar>Z i x ^ l * Z j x ^ (s - l)\<bar> \<le> real (card R ^ s)"
    if "l \<in> {..s}" for s i j l x
  proof -
    have "\<bar>Z i x ^ l * Z j x ^ (s - l)\<bar> \<le> Z i x ^ l * Z j x ^ (s - l)"
      unfolding Z_def by auto
    also have "... \<le> real (card R) ^ l * real (card R) ^ (s-l)"
      unfolding Z_def
      by (intro mult_mono power_mono of_nat_mono card_mono fin_R) auto
    also have "... = real (card R)^s" using that
      by (subst power_add[symmetric]) simp
    also have "... = real (card R^s)"
      by simp
    finally show ?thesis by simp
  qed

  have "?L = (\<integral>\<omega>. (\<Sum>l\<le>s. real (s choose l) * (Z i \<omega>^l * Z j \<omega>^(s-l))) \<partial>p)"
    by (subst binomial_ring) (simp add:algebra_simps)
  also have "... = (\<Sum>l\<le>s. (\<integral>\<omega>. real (s choose l) * (Z i \<omega>^l * Z j \<omega>^(s-l)) \<partial>p))"
    by (intro integral_sum integrable_mult_right
        integrable_pmf_iff_bounded[where C="card R^s"] q2) auto
  also have "... = (\<Sum>l\<le>s. real (s choose l) * (\<integral>\<omega>. (Z i \<omega>^l * Z j \<omega>^(s-l)) \<partial>p))"
    by (intro sum.cong integral_mult_right
        integrable_pmf_iff_bounded[where C="card R^s"] q2) auto
  also have "... = (\<Sum>l\<le>s. real (s choose l) * (\<integral>\<omega>. (Z i \<omega>^l * Z j \<omega>^(s-l)) \<partial>q))"
    using assms(5)
    by (intro_cong "[\<sigma>\<^sub>2 (*)]" more: sum.cong hit_count_prod_pow_eq[OF assms(1-4)])
       auto
  also have "... = (\<Sum>l\<le>s. (\<integral>\<omega>. real (s choose l) * (Z i \<omega>^l * Z j \<omega>^(s-l)) \<partial>q))"
    by (intro sum.cong integral_mult_right[symmetric]
        integrable_pmf_iff_bounded[where C="card R^s"] q2) auto
  also have "... = (\<integral>\<omega>. (\<Sum>l\<le>s. real (s choose l) * (Z i \<omega>^l * Z j \<omega>^(s-l))) \<partial>q)"
    by (intro integral_sum[symmetric] integrable_mult_right
        integrable_pmf_iff_bounded[where C="card R^s"] q2) auto
  also have "... = ?R"
    by (subst binomial_ring) (simp add:algebra_simps)
  finally show ?thesis by simp
qed

lemma hit_count_sum_poly_eq:
  assumes "i \<in> B" "j \<in> B"
  assumes "lim_balls_and_bins k p"
  assumes "lim_balls_and_bins k q"
  assumes "f \<in> \<bbbP> k"
  shows "(\<integral>\<omega>. f (Z i \<omega> + Z j \<omega>) \<partial>p) = (\<integral>\<omega>. f (Z i \<omega> + Z j \<omega>) \<partial>q)"
    (is "?L = ?R")
proof -
  obtain fp where f_def: "f = poly fp" "degree fp \<le> k"
    using assms(5) unfolding Polynomials_def by auto

  have "?L = (\<Sum>d\<le>degree fp. (\<integral>\<omega>. poly.coeff fp d * (Z i \<omega> + Z j \<omega>) ^ d \<partial>p))"
    unfolding f_def poly_altdef
    by (intro integral_sum integrable_mult_right Z_any_integrable_2[OF assms(3)])
  also have "... = (\<Sum>d\<le>degree fp. poly.coeff fp d * (\<integral>\<omega>. (Z i \<omega> + Z j \<omega>) ^ d \<partial>p))"
    by (intro sum.cong integral_mult_right Z_any_integrable_2[OF assms(3)])
     simp
  also have "... = (\<Sum>d\<le>degree fp. poly.coeff fp d *(\<integral>\<omega>. (Z i \<omega> + Z j \<omega>) ^ d \<partial>q))"
    using f_def
    by (intro sum.cong arg_cong2[where f="(*)"] hit_count_sum_pow_eq[OF assms(1-4)]) auto
  also have "... = (\<Sum>d\<le>degree fp. (\<integral>\<omega>. poly.coeff fp d * (Z i \<omega> + Z j \<omega>) ^ d \<partial>q))"
    by (intro sum.cong) auto
  also have "... = ?R"
    unfolding f_def poly_altdef by (intro integral_sum[symmetric]
        integrable_mult_right Z_any_integrable_2[OF assms(4)])
  finally show ?thesis by simp
qed

lemma hit_count_poly_eq:
  assumes "b \<in> B"
  assumes "lim_balls_and_bins k p"
  assumes "lim_balls_and_bins k q"
  assumes "f \<in> \<bbbP> k"
  shows "(\<integral>\<omega>. f (Z b \<omega>) \<partial>p) = (\<integral>\<omega>. f (Z b \<omega>) \<partial>q)" (is "?L = ?R")
proof -
  have a:"(\<lambda>a. f (a / 2)) \<in> \<bbbP> (k*1)"
    by (intro Polynomials_composeI[OF assms(4)] Polynomials_intros)
  have "?L = \<integral>\<omega>. f ((Z b \<omega> + Z b \<omega>)/2) \<partial>p"
    by simp
  also have "... = \<integral>\<omega>. f ((Z b \<omega> + Z b \<omega>)/2) \<partial>q"
    using a by (intro hit_count_sum_poly_eq[OF assms(1,1,2,3)]) simp
  also have "... = ?R" by simp
  finally show ?thesis by simp
qed

lemma lim_balls_and_bins_from_ind_balls_and_bins:
  "lim_balls_and_bins k \<Omega>"
proof -
  have "prob_space.indep_vars (measure_pmf \<Omega>) (\<lambda>_. discrete) (\<lambda>x \<omega>. \<omega> x) R"
    unfolding \<Omega>_def using indep_vars_Pi_pmf[OF fin_R] by metis
  hence "prob_space.indep_vars (measure_pmf \<Omega>) (\<lambda>_. discrete) (\<lambda>x \<omega>. \<omega> x) J" if "J \<subseteq> R" for J
    using prob_space.indep_vars_subset[OF prob_space_measure_pmf _ that] by auto
  hence a:"prob_space.k_wise_indep_vars (measure_pmf \<Omega>) k (\<lambda>_. discrete) (\<lambda>x \<omega>. \<omega> x) R"
    by (simp add:prob_space.k_wise_indep_vars_def[OF prob_space_measure_pmf])

  have b: "map_pmf (\<lambda>\<omega>. \<omega> x) \<Omega> = pmf_of_set B" if "x \<in> R" for x
    using that unfolding \<Omega>_def Pi_pmf_component[OF fin_R] by simp

  show ?thesis
    using a b fin_R fin_B unfolding lim_balls_and_bins_def by auto
qed

lemma hit_count_factorial_moments:
  assumes a:"j \<in> B"
  assumes "s \<le> k"
  assumes "lim_balls_and_bins k p"
  shows "(\<integral>\<omega>. ffact s (Z j \<omega>) \<partial>p) = ffact s (real (card R)) * (1 / real (card B))^s"
    (is "?L = ?R")
proof -
  have "(\<lambda>x. ffact s (x-0::real)) \<in> \<bbbP> s"
    by (intro Polynomials_intros)
  hence b: "ffact s \<in> (\<bbbP> k :: (real \<Rightarrow> real) set)"
    using Polynomials_mono[OF assms(2)] by auto

  have "?L = (\<integral>\<omega>. ffact s (Z j \<omega>) \<partial>\<Omega>)"
    by (intro hit_count_poly_eq[OF a assms(3) lim_balls_and_bins_from_ind_balls_and_bins] b)
  also have "... = (\<integral>\<omega>. ffact s (\<Sum>i \<in> {j}. Z i \<omega>) \<partial>\<Omega>)"
    by simp
  also have "... = ffact s (real (card R)) * (real (card {j}) / real (card B)) ^ s "
    using assms(1)
    by (intro fact_moment_balls_and_bins fin_R fin_B) auto
  also have "... = ?R"
    by simp
  finally show ?thesis by simp
qed

lemma hit_count_factorial_moments_2:
  assumes a:"i \<in> B" "j \<in> B"
  assumes "i \<noteq> j" "s \<le> k" "card R \<le> card B"
  assumes "lim_balls_and_bins k p"
  shows "(\<integral>\<omega>. ffact s (Z i \<omega> + Z j \<omega>) \<partial>p) \<le> 2^s"
    (is "?L \<le> ?R")
proof -
  have "(\<lambda>x. ffact s (x-0::real)) \<in> \<bbbP> s"
    by (intro Polynomials_intros)
  hence b: "ffact s \<in> (\<bbbP> k :: (real \<Rightarrow> real) set)"
    using Polynomials_mono[OF assms(4)] by auto

  have or_distrib: "(a \<and> b) \<or> (a \<and> c) \<longleftrightarrow> a \<and> (b \<or> c)" for a b c
    by auto
  have "?L = (\<integral>\<omega>. ffact s  (Z i \<omega> + Z j \<omega>) \<partial>\<Omega>)"
    by (intro hit_count_sum_poly_eq[OF a assms(6) lim_balls_and_bins_from_ind_balls_and_bins] b)
  also have "... = (\<integral>\<omega>. ffact s ((\<Sum>t \<in> {i,j}. Z t \<omega>)) \<partial>\<Omega>)"
    using assms(3) by simp
  also have "... = ffact s (real (card R)) * (real (card {i,j}) / real (card B)) ^ s "
    using assms(1,2)
    by (intro fact_moment_balls_and_bins fin_R fin_B) auto
  also have "... = real (ffact s (card R)) * (real (card {i,j}) / real (card B)) ^ s "
    by (simp add:of_nat_ffact)
  also have "... \<le> (card R)^s * (real (card {i,j}) / real (card B)) ^ s "
    by (intro mult_mono of_nat_mono ffact_bound, simp_all)
  also have "... \<le> (card B)^s * (real (2) / real (card B)) ^ s "
    using assms(3)
    by (intro mult_mono of_nat_mono power_mono assms(5), simp_all)
  also have "... = ?R"
    using card_B_gt_0 by (simp add:divide_simps)
  finally show ?thesis by simp
qed

lemma balls_and_bins_approx_helper:
  fixes x :: real
  assumes "x \<ge> 2"
  assumes "real k \<ge> 5*x / ln x"
  shows "k \<ge> 2"
    and "2^(k+3) / fact k \<le> (1/exp x)^2"
    and "2 / fact k \<le> 1 / (exp 1 * exp x)"
proof -
  have ln_inv: "ln x = - ln (1/ x)"  if "x > 0" for x :: real
    using that by (subst ln_div, auto)

  have apx:
    "exp 1 \<le> (5::real)"
    "4 * ln 4 \<le>  (2 - 2*exp 1/5)*ln (450::real)"
    "ln 8 * 2 \<le> (450::real)"
    "4 / 5 * 2 * exp 1 + ln (5 / 4) * exp 1 \<le> (5::real)"
    "exp 1 \<le> (2::real)^4"
    by (approximation 10)+

  have "2 \<le> 5 * (x / (x-1))"
    using assms(1) by (simp add:divide_simps)
  also have "... \<le> 5 * (x / ln x)"
    using assms(1)
    by (intro mult_left_mono divide_left_mono ln_le_minus_one mult_pos_pos) auto
  also have "... \<le> k" using assms(2) by simp
  finally show k_ge_2: "k \<ge> 2" by simp

  have "ln x * (2 * exp 1) = ln (((4/5) * x)*(5/4)) * (2 * exp 1)"
    by simp
  also have "... = ln ((4/5) * x) * (2 * exp 1) + ln((5/4))*(2 * exp 1)"
    using assms(1) by (subst ln_mult, simp_all add:algebra_simps)
  also have "... < (4/5)* x * (2 * exp 1) + ln (5/4) * (x * exp 1)"
    using assms(1) by (intro add_less_le_mono mult_strict_right_mono ln_less_self
        mult_left_mono mult_right_mono)  (auto simp add:algebra_simps)
  also have "... = ((4/5) * 2 * exp 1 + ln(5/4) * exp 1) * x"
    by (simp add:algebra_simps)
  also have "... \<le> 5 * x"
    using assms(1) apx(4) by (intro mult_right_mono, simp_all)
  finally have 1: "ln x * (2 * exp 1) \<le> 5 * x" by simp

  have "ln 8 \<le> 3 * x - 5 * x * ln(2*exp 1 /5 * ln x) / ln x"
  proof (cases "x \<in> {2..450}")
    case True
    then show ?thesis by (approximation 10 splitting: x=10)
  next
    case False
    hence x_ge_450: "x \<ge> 450" using assms(1) by simp

    have "4 * ln 4 \<le>  (2 - 2*exp 1/5)*ln (450::real)"
      using apx(2) by (simp)
    also have "... \<le> (2 - 2*exp 1/5)* ln x"
      using x_ge_450 apx(1)
      by (intro mult_left_mono iffD2[OF ln_le_cancel_iff], simp_all)
    finally have "(2 - 2*exp 1/5) * ln x \<ge> 4 * ln 4" by simp
    hence "2*exp 1/5 * ln x + 0 \<le> 2 * exp 1 / 5 * ln x + ((2 - 2*exp 1/5) * ln x - 4 * ln 4)"
      by (intro add_mono) auto
    also have "... = 4 * (1/2) * ln x - 4 * ln 4"
      by (simp add:algebra_simps)
    also have "... = 4 * (ln (x powr (1/2)) - ln 4)"
      using x_ge_450 by (subst ln_powr, auto)
    also have "... = 4 * (ln (x powr (1/2)/4))"
      using x_ge_450 by (subst ln_div) auto
    also have "... < 4 * (x powr (1/2)/4)"
      using x_ge_450 by (intro mult_strict_left_mono ln_less_self) auto
    also have "... = x powr (1/2)" by simp
    finally have "2* exp 1/ 5 * ln x \<le> x powr (1/2)" by simp
    hence "ln(2* exp 1/ 5 * ln x) \<le> ln (x powr (1/2))"
      using x_ge_450 ln_le_cancel_iff by simp
    hence 0:"ln(2* exp 1/ 5 * ln x) / ln x \<le> 1/2"
      using x_ge_450 by (subst (asm) ln_powr, auto)
    have "ln 8 \<le> 3 * x - 5 * x * (1/2)"
      using x_ge_450 apx(3) by simp
    also have "... \<le> 3 * x - 5 * x * (ln(2* exp 1/ 5 * ln x) / ln x)"
      using x_ge_450 by (intro diff_left_mono mult_left_mono 0) auto
    finally show ?thesis by simp
  qed

  hence "2 * x + ln 8 \<le> 2 * x + (3 * x - 5 * x * ln(2*exp 1 /5 * ln x) / ln x)"
    by (intro add_mono, auto)
  also have "... = 5 * x + 5 * x * ln(5 / (2*exp 1*ln x)) / ln x"
    using assms(1) by (subst ln_inv) (auto simp add:algebra_simps)
  also have "... = 5 * x * (ln x + ln(5 / (2*exp 1*ln x))) / ln x"
    using assms(1) by (simp add:algebra_simps add_divide_distrib)
  also have "... = 5 * x * (ln (5 * x / (2 * exp 1 * ln x))) / ln x"
    using assms(1) by (subst ln_mult[symmetric], auto)
  also have "... = (5 * x / ln x) * ln ((5 * x / ln x) / (2 * exp 1))"
    by (simp add:algebra_simps)
  also have "... \<le> k * ln (k / (2*exp 1))"
    using assms(1,2) 1 k_ge_2
    by (intro mult_mono iffD2[OF ln_le_cancel_iff] divide_right_mono)
     auto
  finally have "k * ln (k/(2*exp 1)) \<ge> 2*x + ln 8" by simp
  hence "k * ln(2*exp 1/k) \<le> -2*x - ln 8"
    using k_ge_2 by (subst ln_inv, auto)
  hence "ln ((2*exp 1/k) powr k) \<le> ln(exp(-2*x)) - ln 8"
    using k_ge_2 by (subst ln_powr, auto)
  also have "... = ln(exp(-2*x)/8)"
    by (simp add:ln_div)
  finally have "ln ((2*exp 1/k) powr k) \<le>  ln (exp(-2*x)/8)" by simp
  hence 1: "(2*exp 1/k) powr k \<le>  exp(-2*x)/8"
    using k_ge_2 assms(1) by (subst (asm) ln_le_cancel_iff) auto
  have "2^(k+3)/fact k \<le> 2^(k+3)/(k / exp 1)^k"
    using k_ge_2 by (intro divide_left_mono fact_lower_bound_1) auto
  also have "... = 8 * 2^k * (exp 1 / k)^k"
    by (simp add:power_add algebra_simps power_divide)
  also have "... = 8 * (2*exp 1/k) powr k"
    using k_ge_2 powr_realpow
    by (simp add:power_mult_distrib[symmetric])
  also have "... \<le> 8 * (exp(-2*x)/8)"
    by (intro mult_left_mono 1) auto
  also have "... = exp((-x)*2)"
    by simp
  also have "... = exp(-x)^2"
    by (subst exp_powr[symmetric], simp)
  also have "... = (1/exp x)^2"
    by (simp add: exp_minus inverse_eq_divide)
  finally show 2:"2^(k+3)/fact k \<le> (1/exp x)^2" by simp

  have "(2::real)/fact k = (2^(k+3)/fact k)/(2^(k+2))"
    by (simp add:divide_simps power_add)
  also have "... \<le> (1/exp x)^2/(2^(k+2))"
    by (intro divide_right_mono 2, simp)
  also have "... \<le> (1/exp x)^1/(2^(k+2))"
    using assms(1) by (intro divide_right_mono power_decreasing) auto
  also have "... \<le> (1/exp x)^1/(2^4)"
    using k_ge_2 by (intro divide_left_mono power_increasing) auto
  also have "... \<le> (1/exp x)^1/exp(1)"
    using k_ge_2 apx(5) by (intro divide_left_mono) auto
  also have "... = 1/(exp 1 * exp x)" by simp
  finally show "(2::real)/fact k \<le> 1/(exp 1 * exp x)" by simp
qed

text \<open>Bounds on the expectation and variance in the k-wise independent case. Here the indepedence
assumption is improved by a factor of two compared to the result in the paper.\<close>

lemma
  assumes "card R \<le> card B"
  assumes "\<And>c. lim_balls_and_bins (k+1) (p c)"
  assumes "\<epsilon> \<in> {0<..1/exp(2)}"
  assumes "k \<ge> 5 * ln (card B / \<epsilon>) / ln (ln (card B / \<epsilon>))"
  shows
    exp_approx: "\<bar>measure_pmf.expectation (p True) Y - measure_pmf.expectation (p False) Y\<bar> \<le>
      \<epsilon> * real (card R)" (is "?A") and
    var_approx: "\<bar>measure_pmf.variance (p True) Y - measure_pmf.variance (p False) Y\<bar> \<le> \<epsilon>\<^sup>2"
      (is "?B")
proof -
  let ?p1 = "p False"
  let ?p2 = "p True"

  have "exp (2::real) = 1/ (1/exp 2)" by simp
  also have "... \<le> 1/ \<epsilon>"
    using assms(3) by (intro divide_left_mono) auto
  also have "... \<le> real (card B)/ \<epsilon>"
    using assms(3) card_B_gt_0 by (intro divide_right_mono) auto
  finally have "exp 2 \<le> real (card B) / \<epsilon>" by simp
  hence k_condition_h: "2 \<le> ln (card B / \<epsilon>)"
    using assms(3) card_B_gt_0 by (subst ln_ge_iff) auto
  have k_condition_h_2: "0 < real (card B) / \<epsilon>"
    using assms(3) card_B_gt_0 by (intro divide_pos_pos) auto

  note k_condition = balls_and_bins_approx_helper[OF k_condition_h assms(4)]

  define \<phi> :: "real \<Rightarrow> real" where "\<phi> = (\<lambda>x. min x 1)"

  define f where "f = (\<lambda>x. 1 -  (-1)^k / real (fact k) * ffact k (x-1))"
  define g where "g = (\<lambda>x. \<phi> x - f x)"
  have \<phi>_exp: "\<phi> x = f x + g x" for x
    unfolding g_def by simp

  have k_ge_2: "k \<ge> 2"
    using k_condition(1) by simp

  define \<gamma> where "\<gamma> = 1 / real (fact k)"
  have \<gamma>_nonneg: "\<gamma> \<ge> 0"
    unfolding \<gamma>_def by simp

  have k_le_k_plus_1: "k \<le> k+1"
    by simp

  have "f \<in> \<bbbP> k"
    unfolding f_def by (intro Polynomials_intros)
  hence f_poly: "f \<in> \<bbbP> (k+1)"
    using Polynomials_mono[OF k_le_k_plus_1] by auto

  have g_diff: "\<bar>g x - g (x-1)\<bar> = ffact (k-1) (x-2) / fact (k-1)"
    if "x \<ge> k" for x :: real
  proof -
    have "x \<ge> 2" using k_ge_2 that by simp
    hence "\<phi> x = \<phi> (x- 1)"
      unfolding \<phi>_def by simp
    hence "\<bar>g x - g (x-1)\<bar> = \<bar>f (x-1) - f x\<bar>"
      unfolding g_def by (simp add:algebra_simps)
    also have "... = \<bar>(-1)^k / real (fact k) * (ffact k (x-2) - ffact k (x-1))\<bar>"
      unfolding f_def by (simp add:algebra_simps)
    also have "... = 1 / real (fact k) * \<bar>ffact k (x-1) - ffact k ((x-1)-1)\<bar>"
      by (simp add:abs_mult)
    also have "... = 1 / real (fact k) * real k * \<bar>ffact (k-1) (x-2)\<bar>"
      by (subst ffact_suc_diff, simp add:abs_mult)
    also have "... = \<bar>ffact (k-1) (x-2)\<bar> / fact (k-1)"
      using k_ge_2 by (subst fact_reduce) auto
    also have "... = ffact (k-1) (x-2) / fact (k-1)"
      unfolding ffact_eq_fact_mult_binomial using that k_ge_2
      by (intro arg_cong2[where f="(/)"] abs_of_nonneg ffact_nonneg) auto
    finally show ?thesis by simp
  qed


  have f_approx_\<phi>: "f x = \<phi> x" if f_approx_\<phi>_1: "x \<in> real ` {0..k}" for x
  proof (cases "x = 0")
    case True
    hence "f x  =  1 - (-1)^k / real (fact k) * (\<Prod>i = 0..<k. - (real i+1))"
      unfolding f_def prod_ffact[symmetric] by (simp add:algebra_simps)
    also have "... = 1 - (-1)^k / real (fact k) * ((\<Prod>i = 0..<k. (- 1)::real) * (\<Prod>i = 0..<k. real i+1))"
      by (subst prod.distrib[symmetric]) simp
    also have "... = 1 - (-1)^k / real (fact k) * ((-1)^k * (\<Prod>i \<in> (\<lambda>x. x + 1) ` {0..<k}. real i))"
      by (subst prod.reindex, auto simp add:inj_on_def comp_def algebra_simps)
    also have "... = 1 - (-1)^k / real (fact k) * ((-1)^k * (\<Prod>i \<in> {1..k}. real i))"
      by (intro arg_cong2[where f="(-)"] arg_cong2[where f="(*)"] prod.cong refl) auto
    also have "... = 0"
      unfolding fact_prod by simp
    also have "... = \<phi> x"
      using True \<phi>_def by simp
    finally show ?thesis by simp
  next
    case False
    hence a: " x \<ge> 1" using that by auto
    obtain x' where x'_def: "x' \<in> {0..k}" "x = real x'"
      using f_approx_\<phi>_1 by auto
    hence "x' - 1 \<in> {0..<k}" using k_ge_2 by simp
    moreover have "x- real 1 = real (x'-1)"
      using False x'_def(2) by simp
    ultimately have b: "x - 1 = real (x' - 1)" "x' - 1 < k"
      by auto

    have "f x =  1 - (- 1) ^ k / real (fact k) * real (ffact k (x' - 1))"
      unfolding f_def b of_nat_ffact by simp
    also have "... = 1"
      using b by (subst ffact_nat_triv, auto)
    also have "... = \<phi> x"
      unfolding \<phi>_def using a by auto
    finally show ?thesis by simp
  qed

  have q2: "\<bar>Z i x ^ l * Z j x ^ (s - l)\<bar> \<le> real (card R ^ s)"
    if "l \<in> {..s}" for s i j l x
  proof -
    have "\<bar>Z i x ^ l * Z j x ^ (s - l)\<bar> \<le> Z i x ^ l * Z j x ^ (s - l)"
      unfolding Z_def by auto
    also have "... \<le> real (card R) ^ l * real (card R) ^ (s-l)"
      unfolding Z_def
      by (intro mult_mono power_mono of_nat_mono card_mono fin_R) auto
    also have "... = real (card R)^s" using that
      by (subst power_add[symmetric]) simp
    also have "... = real (card R^s)"
      by simp
    finally show ?thesis by simp
  qed

  have q:"real (card A) + real (card B) \<in> real ` {..2 * card R}" if "A \<subseteq> R" "B \<subseteq> R" for A B
  proof -
    have "card A + card B \<le> card R + card R"
      by (intro add_mono card_mono fin_R that)
    also have "... = 2 * card R" by simp
    finally show ?thesis by force
  qed

  have g_eq_0_iff_2: "abs (g x) * y = 0" if "x \<in> \<int>" "x \<ge> 0" "x \<le> k" for x y :: real
  proof -
    have "\<exists>x'. x = real_of_int x' \<and> x' \<le> k \<and> x' \<ge> 0"
      using that Ints_def by fastforce
    hence "\<exists>x'. x = real x' \<and> x' \<le> k"
      by (metis nat_le_iff of_nat_nat)
    hence "x \<in> real ` {0..k}"
      by auto
    hence "g x = 0"
      unfolding g_def using f_approx_\<phi> by simp
    thus ?thesis by simp
  qed

  have g_bound_abs: "\<bar>\<integral>\<omega>. g (f \<omega>) \<partial>p\<bar> \<le> (\<integral>\<omega>. ffact (k+1) (f \<omega>) \<partial>p) * \<gamma>"
    (is "?L \<le> ?R")
    if "range f \<subseteq> real ` {..m}" for m and p :: "('a \<Rightarrow> 'b) pmf" and f :: "('a \<Rightarrow> 'b) \<Rightarrow> real"
  proof -
    have f_any_integrable:
      "integrable p (\<lambda>\<omega>. h (f \<omega>))" for h :: "real \<Rightarrow> real"
      using that
      by (intro integrable_pmf_iff_bounded[where C="Max (abs ` h` real ` {..m})"]
          Max_ge finite_imageI imageI) auto

    have f_val: "f \<omega> \<in> real ` {..m}" for \<omega> using  that by auto
    hence f_nat: "f \<omega> \<in> \<nat>" for \<omega>
      unfolding Nats_def by auto

    have f_int: "f \<omega> \<ge> real y + 1" if "f \<omega> > real y" for y \<omega>
    proof -
      obtain x where x_def: "f \<omega> = real x" "x \<le> m" using f_val by auto
      hence "y < x" using that by simp
      hence "y + 1 \<le> x" by simp
      then show ?thesis using x_def by simp
    qed

    have f_nonneg: "f \<omega> \<ge> 0" for \<omega>
    proof -
      obtain x where x_def: "f \<omega> = real x" "x \<le> m" using f_val by auto
      hence "x \<ge> 0" by simp
      then show ?thesis using x_def by simp
    qed

    have "\<not>(real x \<le> f \<omega>)" if "x > m" for x \<omega>
    proof -
      obtain x where x_def: "f \<omega> = real x" "x \<le> m" using f_val by auto
      then show ?thesis using x_def that by simp
    qed

    hence max_Z1: "measure p {\<omega>. real x \<le> f \<omega>} = 0" if "x > m" for x
      using that by auto

    have "?L \<le> (\<integral>\<omega>. \<bar>g (f \<omega>)\<bar> \<partial>p)"
      by (intro integral_abs_bound)
    also have "... = (\<Sum>y\<in>real ` {..m}. \<bar>g y\<bar> * measure p {\<omega>. f \<omega> = y})"
      using that by (intro pmf_exp_of_fin_function) auto
    also have "... = (\<Sum>y\<in>{..m}. \<bar>g (real y)\<bar> * measure p {\<omega>. f \<omega> = real y})"
      by (subst sum.reindex) (auto simp add:comp_def)
    also have "... = (\<Sum>y\<in>{..m}. \<bar>g (real y)\<bar> *
      (measure p ({\<omega>. f \<omega> = real y} \<union> {\<omega>. f \<omega> > y}) - measure p {\<omega>. f \<omega> > y}))"
      by (subst measure_Union) auto
    also have "... = (\<Sum>y\<in>{..m}. \<bar>g (real y)\<bar> * (measure p {\<omega>. f \<omega> \<ge> y} - measure p {\<omega>. f \<omega> > y}))"
      by (intro sum.cong arg_cong2[where f="(*)"] arg_cong2[where f="(-)"]
          arg_cong[where f="measure p"]) auto
    also have "... = (\<Sum>y\<in>{..m}. \<bar>g (real y)\<bar> * measure p {\<omega>. f \<omega> \<ge> y}) -
      (\<Sum>y\<in>{..m}. \<bar>g (real y)\<bar> * measure p {\<omega>. f \<omega> > y})"
      by (simp add:algebra_simps sum_subtractf)
    also have "... = (\<Sum>y\<in>{..m}. \<bar>g (real y)\<bar> * measure p {\<omega>. f \<omega> \<ge> y}) -
                     (\<Sum>y\<in>{..m}. \<bar>g (real y)\<bar> * measure p {\<omega>. f \<omega> \<ge> real (y+1)})"
      using f_int
      by (intro sum.cong arg_cong2[where f="(-)"] arg_cong2[where f="(*)"]
          arg_cong[where f="measure p"]) fastforce+
    also have "... = (\<Sum>y\<in>{..m}. \<bar>g (real y)    \<bar> * measure p {\<omega>. f \<omega> \<ge> real y}) -
               (\<Sum>y\<in>Suc ` {..m}. \<bar>g (real y - 1)\<bar> * measure p {\<omega>. f \<omega> \<ge> real y})"
      by (subst sum.reindex) (auto simp add:comp_def)
    also have "... = (\<Sum>y\<in>{..m}. \<bar>g (real y)    \<bar> * measure p {\<omega>. f \<omega> \<ge> real y}) -
                    (\<Sum>y\<in>{1..m}. \<bar>g (real y - 1)\<bar> * measure p {\<omega>. f \<omega> \<ge> real y})"
      using max_Z1 image_Suc_atMost
      by (intro arg_cong2[where f="(-)"] sum.mono_neutral_cong) auto
    also have "... = (\<Sum>y\<in>{k+1..m}. \<bar>g (real y)    \<bar> * measure p {\<omega>. f \<omega> \<ge> y}) -
                     (\<Sum>y\<in>{k+1..m}. \<bar>g (real y - 1)\<bar> * measure p {\<omega>. f \<omega> \<ge> y})"
      using k_ge_2
      by (intro arg_cong2[where f="(-)"] sum.mono_neutral_cong_right ballI g_eq_0_iff_2)
        auto
    also have "... = (\<Sum>y\<in>{k+1..m}. (\<bar>g (real y)\<bar> - \<bar>g (real y-1)\<bar>) * measure p {\<omega>. f \<omega> \<ge> y})"
      by (simp add:algebra_simps sum_subtractf)
    also have "... \<le> (\<Sum>y\<in>{k+1..m}. \<bar>g (real y)- g (real y-1)\<bar> *
      measure p {\<omega>. ffact (k+1) (f \<omega>) \<ge> ffact (k+1) (real y)})"
      using ffact_mono by (intro sum_mono mult_mono measure_pmf.pmf_mono[OF refl]) auto
    also have "... = (\<Sum>y\<in>{k+1..m}. (ffact (k-1) (real y-2) / fact (k-1)) *
      measure p {\<omega>. ffact (k+1) (f \<omega>) \<ge> ffact (k+1) (real y)})"
      by (intro sum.cong, simp_all add: g_diff)
    also have "... \<le> (\<Sum>y\<in>{k+1..m}. (ffact (k-1) (real y-2) / fact (k-1)) *
      ((\<integral>\<omega>. ffact (k+1) (f \<omega>)\<partial>p) / ffact (k+1) (real y)))"
      using k_ge_2 f_nat
      by (intro sum_mono mult_left_mono pmf_markov f_any_integrable
          divide_nonneg_pos ffact_of_nat_nonneg ffact_pos) auto
    also have "... = (\<integral>\<omega>. ffact (k+1) (f \<omega>) \<partial>p) / fact (k-1) * (\<Sum>y\<in>{k+1..m}.
       ffact (k-1) (real y - 2) / ffact (Suc (Suc (k-1))) (real y))"
      using k_ge_2 by (simp add:algebra_simps sum_distrib_left)
    also have "... = (\<integral>\<omega>. ffact (k+1) (f \<omega>) \<partial>p) / fact (k-1) * (\<Sum>y\<in>{k+1..m}.
       ffact (k-1) (real y - 2) / (real y * (real y - 1) * ffact (k-1) (real y - 2)))"
      by (subst ffact_Suc, subst ffact_Suc, simp)
    also have "... = (\<integral>\<omega>. ffact (k+1) (f \<omega>) \<partial>p) / fact (k-1) *
      (\<Sum>y\<in>{k+1..m}. 1 / (real y * (real y - 1)))"
      using order.strict_implies_not_eq[OF ffact_pos] k_ge_2
      by (intro arg_cong2[where f="(*)"] sum.cong) auto
    also have "... = (\<integral>\<omega>. ffact (k+1) (f \<omega>) \<partial>p) / fact (k-1) *
      (\<Sum>y\<in>{Suc k..m}. 1 / (real y - 1) - 1/(real y))"
      using k_ge_2 by (intro arg_cong2[where f="(*)"] sum.cong) (auto simp add: divide_simps)
    also have "... = (\<integral>\<omega>. ffact (k+1) (f \<omega>) \<partial>p) / fact (k-1) *
      (\<Sum>y\<in>{Suc k..m}.  (-1/(real y)) - (-1 / (real (y - 1))))"
      using k_ge_2 by (intro arg_cong2[where f="(*)"] sum.cong) (auto)
    also have "... =  (\<integral>\<omega>. ffact (k+1) (f \<omega>) \<partial>p) / fact (k-1) *
      (of_bool (k \<le> m) * (1/real k-1/real m))"
      by (subst sum_telescope_eq, auto)
    also have "... \<le>  (\<integral>\<omega>. ffact (k+1) (f \<omega>) \<partial>p) / fact (k-1) * (1 / real k)"
      using k_ge_2 f_nat
      by (intro mult_left_mono divide_nonneg_nonneg integral_nonneg
          ffact_of_nat_nonneg) auto
    also have "... = ?R"
      using k_ge_2 unfolding \<gamma>_def by (cases k) (auto simp add:algebra_simps)
    finally show ?thesis by simp
  qed

  have z1_g_bound: "\<bar>\<integral>\<omega>. g (Z i \<omega>) \<partial>p c\<bar> \<le> (real (card R) / real (card B)) * \<gamma>"
    (is "?L1 \<le> ?R1") if "i \<in> B" for i c
  proof -

    have "?L1 \<le> (\<integral>\<omega>. ffact (k+1) (Z i \<omega>) \<partial>p c) * \<gamma>"
      unfolding Z_def using fin_R
      by (intro g_bound_abs[where m1="card R"]) (auto intro!:imageI card_mono)
    also have "... = ffact (k+1) (real (card R)) * (1 / real (card B))^(k+1) * \<gamma>"
      using that by (subst hit_count_factorial_moments[OF _ _ assms(2)], simp_all)
    also have "... = real (ffact (k+1) (card R)) * (1 / real (card B))^(k+1) * \<gamma>"
      by (simp add:of_nat_ffact)
    also have "... \<le> real (card R^(k+1)) * (1 / real (card B))^(k+1) * \<gamma>"
      using \<gamma>_nonneg
      by (intro mult_right_mono of_nat_mono ffact_bound, simp_all)
    also have "... \<le> (real (card R) / real (card B))^(k+1) * \<gamma>"
      by (simp add:divide_simps)
    also have "... \<le> (real (card R) / real (card B))^1 * \<gamma>"
      using assms(1) card_B_gt_0 \<gamma>_nonneg by (intro mult_right_mono power_decreasing) auto
    also have "... = ?R1" by simp
    finally show ?thesis by simp
  qed

  have g_add_bound: "\<bar>\<integral>\<omega>. g (Z i \<omega> + Z j \<omega>) \<partial>p c\<bar> \<le> 2^(k+1) * \<gamma>"
    (is "?L1 \<le> ?R1") if ij_in_B: "i \<in> B" "j \<in> B" "i \<noteq> j" for i j c
  proof -
    have "?L1 \<le> (\<integral>\<omega>. ffact (k+1) (Z i \<omega> + Z j \<omega>) \<partial>p c) * \<gamma>"
      unfolding Z_def using assms(1)
      by (intro g_bound_abs[where m1="2*card R"]) (auto intro!:imageI q)
    also have "... \<le> 2^(k+1) * \<gamma>"
      by (intro \<gamma>_nonneg mult_right_mono hit_count_factorial_moments_2[OF that(1,2,3) _ assms(1,2)])
        auto
    finally show ?thesis by simp
  qed

  have Z_poly_diff:
    "\<bar>(\<integral>\<omega>. \<phi> (Z i \<omega>) \<partial>?p1) - (\<integral>\<omega>. \<phi> (Z i \<omega>) \<partial>?p2)\<bar> \<le> 2 * ((real (card R) / card B) * \<gamma>)"
    (is "?L \<le> 2 * ?R") if "i \<in> B" for i
  proof -
    note Z_poly_eq =
      hit_count_poly_eq[OF that assms(2)[of "True"] assms(2)[of "False"] f_poly]

    have "?L = \<bar>(\<integral>\<omega>. f (Z i \<omega>) \<partial>?p1) + (\<integral>\<omega>. g (Z i \<omega>) \<partial>?p1) -
      (\<integral>\<omega>. f (Z i \<omega>) \<partial>?p2) - (\<integral>\<omega>. g (Z i \<omega>) \<partial>?p2)\<bar>"
      using Z_integrable[OF assms(2)] unfolding \<phi>_exp by simp
    also have "... = \<bar>(\<integral>\<omega>. g (Z i \<omega>) \<partial>?p1) + (- (\<integral>\<omega>. g (Z i \<omega>) \<partial>?p2))\<bar>"
      by (subst Z_poly_eq) auto
    also have "... \<le> \<bar>(\<integral>\<omega>. g (Z i \<omega>) \<partial>?p1)\<bar> + \<bar>(\<integral>\<omega>. g (Z i \<omega>) \<partial>?p2)\<bar>"
      by simp
    also have "... \<le> ?R + ?R"
      by (intro add_mono z1_g_bound that)
    also have "... = 2 * ?R"
      by (simp add:algebra_simps)
    finally show ?thesis by simp
  qed

  have Z_poly_diff_2: "\<bar>(\<integral>\<omega>. \<phi> (Z i \<omega>) \<partial>?p1) - (\<integral>\<omega>. \<phi> (Z i \<omega>) \<partial>?p2)\<bar> \<le> 2 * \<gamma>"
    (is "?L \<le> ?R") if "i \<in> B" for i
  proof -
    have "?L \<le> 2 * ((real (card R) / real (card B)) * \<gamma>)"
      by (intro Z_poly_diff that)
    also have "... \<le> 2 * (1 * \<gamma>)"
      using assms fin_B that \<gamma>_nonneg card_gt_0_iff
      by (intro mult_mono that iffD2[OF pos_divide_le_eq]) auto
    also have "... = ?R" by simp
    finally show ?thesis by simp
  qed

  have Z_poly_diff_3: "\<bar>(\<integral>\<omega>. \<phi> (Z i \<omega> + Z j \<omega>) \<partial>?p2) - (\<integral>\<omega>. \<phi> (Z i \<omega> + Z j \<omega>) \<partial>?p1)\<bar> \<le> 2^(k+2)*\<gamma>"
    (is "?L \<le> ?R") if "i \<in> B" "j \<in> B" "i \<noteq> j" for i j
  proof -
    note Z_poly_eq_2 =
      hit_count_sum_poly_eq[OF that(1,2) assms(2)[of "True"] assms(2)[of "False"] f_poly]

    have "?L = \<bar>(\<integral>\<omega>. f (Z i \<omega> + Z j \<omega>) \<partial>?p2) + (\<integral>\<omega>. g (Z i \<omega> + Z j \<omega>) \<partial>?p2) -
      (\<integral>\<omega>. f (Z i \<omega> + Z j \<omega>) \<partial>?p1) - (\<integral>\<omega>. g (Z i \<omega> + Z j \<omega>) \<partial>?p1)\<bar>"
      using Z_any_integrable_2[OF assms(2)] unfolding \<phi>_exp by simp
    also have "... = \<bar>(\<integral>\<omega>. g (Z i \<omega> + Z j \<omega>) \<partial>?p2) + (- (\<integral>\<omega>. g (Z i \<omega> + Z j \<omega>) \<partial>?p1))\<bar>"
      by (subst Z_poly_eq_2) auto
    also have "... \<le> \<bar>(\<integral>\<omega>. g (Z i \<omega> + Z j \<omega>) \<partial>?p1)\<bar> + \<bar>(\<integral>\<omega>. g (Z i \<omega> + Z j \<omega>) \<partial>?p2)\<bar>"
      by simp
    also have "... \<le> 2^(k+1)*\<gamma> + 2^(k+1)*\<gamma>"
      by (intro add_mono g_add_bound that)
    also have "... = ?R"
      by (simp add:algebra_simps)
    finally show ?thesis by simp
  qed


  have Y_eq: "Y \<omega> = (\<Sum>i \<in> B. \<phi> (Z i \<omega>))" if "\<omega> \<in> set_pmf (p c)" for c \<omega>
  proof -
    have "\<omega> ` R \<subseteq> B"
    proof (rule image_subsetI)
      fix x assume a:"x \<in> R"
      have "\<omega> x \<in> set_pmf (map_pmf (\<lambda>\<omega>. \<omega> x) (p c))"
        using that by (subst set_map_pmf) simp
      also have "... = set_pmf (pmf_of_set B)"
        by (intro arg_cong[where f="set_pmf"] assms ran[OF assms(2)] a)
      also have "... = B"
        by (intro set_pmf_of_set fin_B B_ne)
      finally show "\<omega> x \<in> B" by simp
    qed
    hence "(\<omega> ` R) = B \<inter> \<omega> ` R"
      by auto
    hence "Y \<omega> = card (B \<inter> \<omega> ` R)"
      unfolding Y_def by auto
    also have  "... = (\<Sum>i \<in> B. of_bool (i \<in> \<omega> ` R))"
      unfolding of_bool_def using fin_B by (subst sum.If_cases) auto
    also have  "... = (\<Sum>i \<in> B. of_bool (card {r \<in> R.  \<omega> r = i} > 0))"
      using fin_R by (intro sum.cong arg_cong[where f="of_bool"])
        (auto simp add:card_gt_0_iff)
    also have "... = (\<Sum>i \<in> B. \<phi>(Z i \<omega>))"
      unfolding \<phi>_def Z_def by (intro sum.cong) (auto simp add:of_bool_def)
    finally show ?thesis by simp
  qed

  let ?\<phi>2 = "(\<lambda>x y. \<phi> x + \<phi> y - \<phi> (x+y))"
  let ?Bd = "{x \<in> B \<times> B. fst x \<noteq> snd x}"

  have Y_sq_eq': "Y \<omega>^ 2 = (\<Sum>i \<in> ?Bd. ?\<phi>2 (Z (fst i) \<omega>) (Z (snd i) \<omega>)) + Y \<omega>"
    (is "?L = ?R") if "\<omega> \<in> set_pmf (p c)" for c \<omega>
  proof -
    have a: "\<phi> (Z x \<omega>) = of_bool(card {r \<in> R. \<omega> r = x} > 0)" for x
      unfolding \<phi>_def Z_def by auto
    have b: "\<phi> (Z x \<omega> + Z y \<omega>) =
      of_bool( card {r \<in> R. \<omega> r = x} > 0 \<or> card {r \<in> R. \<omega> r = y} > 0)" for x y
      unfolding \<phi>_def Z_def by auto
    have c: "\<phi> (Z x \<omega>) * \<phi>(Z y \<omega>) = ?\<phi>2 (Z x \<omega>) (Z y \<omega>)"  for x y
      unfolding a b of_bool_def by auto
    have d: "\<phi> (Z x \<omega>) * \<phi>(Z x \<omega>) = \<phi> (Z x \<omega>)"  for x
      unfolding a of_bool_def by auto

    have "?L = (\<Sum>i\<in>B \<times> B. \<phi> (Z (fst i) \<omega>) * \<phi> (Z (snd i) \<omega>))"
      unfolding Y_eq[OF that] power2_eq_square sum_product sum.cartesian_product
      by (simp add:case_prod_beta)
    also have "... = (\<Sum>i\<in>?Bd \<union> {x \<in> B \<times> B. fst x = snd x}. \<phi> (Z (fst i) \<omega>) * \<phi> (Z (snd i) \<omega>))"
      by (intro sum.cong refl) auto
    also have "... = (\<Sum>i\<in>?Bd. \<phi> (Z (fst i) \<omega>) * \<phi> (Z (snd i) \<omega>)) +
      (\<Sum>i\<in>{x \<in> B \<times> B. fst x = snd x}. \<phi> (Z (fst i) \<omega>) * \<phi> (Z (snd i) \<omega>))"
      using assms fin_B  by (intro sum.union_disjoint, auto)
    also have "... = (\<Sum>i\<in>?Bd. ?\<phi>2 (Z (fst i) \<omega>) (Z (snd i) \<omega>)) +
      (\<Sum>i\<in>{x \<in> B \<times> B. fst x = snd x}. \<phi> (Z (fst i) \<omega>) * \<phi> (Z (fst i) \<omega>))"
      unfolding c by (intro arg_cong2[where f="(+)"] sum.cong) auto
    also have "... = (\<Sum>i\<in>?Bd. ?\<phi>2 (Z (fst i) \<omega>) (Z (snd i) \<omega>)) +
      (\<Sum>i\<in>fst ` {x \<in> B \<times> B. fst x = snd x}. \<phi> (Z i \<omega>) * \<phi> (Z i \<omega>))"
      by (subst sum.reindex, auto simp add:inj_on_def)
    also have "... = (\<Sum>i\<in>?Bd. ?\<phi>2 (Z (fst i) \<omega>) (Z (snd i) \<omega>)) + (\<Sum>i \<in> B. \<phi> (Z i \<omega>))"
      using d by (intro arg_cong2[where f="(+)"] sum.cong refl d) (auto simp add:image_iff)
    also have "... = ?R"
      unfolding Y_eq[OF that] by simp
    finally show ?thesis by simp
  qed

  have "\<bar>integral\<^sup>L ?p1 Y - integral\<^sup>L ?p2 Y\<bar> =
    \<bar>(\<integral>\<omega>. (\<Sum>i \<in> B. \<phi>(Z i \<omega>)) \<partial>?p1) - (\<integral>\<omega>. (\<Sum>i \<in> B. \<phi>(Z i \<omega>)) \<partial>?p2)\<bar>"
    by (intro arg_cong[where f="abs"] arg_cong2[where f="(-)"]
        integral_cong_AE AE_pmfI Y_eq) auto
  also have "... =
    \<bar>(\<Sum>i \<in> B. (\<integral>\<omega>. \<phi>(Z i \<omega>) \<partial>?p1)) - (\<Sum>i \<in> B. (\<integral>\<omega>. \<phi>(Z i \<omega>) \<partial>?p2))\<bar>"
    by (intro arg_cong[where f="abs"] arg_cong2[where f="(-)"]
        integral_sum Z_integrable[OF assms(2)])
  also have "... = \<bar>(\<Sum>i \<in> B. (\<integral>\<omega>. \<phi>(Z i \<omega>) \<partial>?p1) - (\<integral>\<omega>. \<phi>(Z i \<omega>) \<partial>?p2))\<bar>"
    by (subst sum_subtractf) simp
  also have "... \<le> (\<Sum>i \<in> B. \<bar>(\<integral>\<omega>. \<phi>(Z i \<omega>) \<partial>?p1) - (\<integral>\<omega>. \<phi>(Z i \<omega>) \<partial>?p2)\<bar>)"
    by simp
  also have "... \<le> (\<Sum>i \<in> B. 2 * ((real (card R) / real (card B)) *\<gamma>))"
    by (intro sum_mono Z_poly_diff)
  also have "... \<le> 2 * real (card R) *\<gamma>"
    using \<gamma>_nonneg by (simp)
  finally have Y_exp_diff_1: "\<bar>integral\<^sup>L ?p1 Y - integral\<^sup>L ?p2 Y\<bar> \<le> 2 * real (card R) *\<gamma>"
    by simp

  have "\<bar>integral\<^sup>L ?p1 Y - integral\<^sup>L ?p2 Y\<bar> \<le> (2 / fact k) * real (card R)"
    using Y_exp_diff_1 by (simp add:algebra_simps \<gamma>_def)
  also have "... \<le>  1 / (exp 1 * (real (card B) / \<epsilon>)) * card R"
    using k_condition(3) k_condition_h_2 by (intro mult_right_mono) auto
  also have "... =  \<epsilon> / (exp 1 * real (card B)) * card R"
    by simp
  also have "... \<le> \<epsilon> / (1 * 1) * card R"
    using assms(3) card_B_gt_0
    by (intro mult_right_mono divide_left_mono mult_mono) auto
  also have "... = \<epsilon> * card R"
    by simp
  finally show ?A
    by simp

  have "\<bar>integral\<^sup>L ?p1 Y - integral\<^sup>L ?p2 Y\<bar> \<le>  2 * real (card R) *\<gamma>"
    using Y_exp_diff_1 by simp
  also have "... \<le> 2 * real (card B) *\<gamma>"
    by (intro mult_mono of_nat_mono assms \<gamma>_nonneg) auto
  finally have Y_exp_diff_2:
    "\<bar>integral\<^sup>L ?p1 Y - integral\<^sup>L ?p2 Y\<bar> \<le> 2 *\<gamma> * real (card B)"
    by (simp add:algebra_simps)

  have int_Y: "integrable (measure_pmf (p c)) Y" for c
    using fin_R card_image_le unfolding Y_def
    by (intro integrable_pmf_iff_bounded[where C="card R"])  auto

  have int_Y_sq: "integrable (measure_pmf (p c)) (\<lambda>\<omega>. Y \<omega>^2)" for c
    using fin_R card_image_le unfolding Y_def
    by (intro integrable_pmf_iff_bounded[where C="real (card R)^2"]) auto

  have "\<bar>(\<integral>\<omega>. (\<Sum>i \<in> ?Bd. ?\<phi>2 (Z (fst i) \<omega>) (Z (snd i) \<omega>)) \<partial>?p1) -
     (\<integral>\<omega>. (\<Sum>i \<in> ?Bd. ?\<phi>2 (Z (fst i) \<omega>) (Z (snd i) \<omega>)) \<partial>?p2)\<bar>
    \<le> \<bar>(\<Sum>i \<in> ?Bd.
    (\<integral>\<omega>. \<phi> (Z (fst i) \<omega>) \<partial>?p1) + (\<integral>\<omega>. \<phi>(Z (snd i) \<omega>) \<partial>?p1) -
    (\<integral>\<omega>. \<phi> (Z (fst i) \<omega> + Z (snd i) \<omega>) \<partial>?p1) - ( (\<integral>\<omega>. \<phi>(Z (fst i) \<omega>) \<partial>?p2) +
    (\<integral>\<omega>. \<phi> (Z (snd i) \<omega>) \<partial>?p2) - (\<integral>\<omega>. \<phi>(Z (fst i) \<omega> + Z (snd i) \<omega>) \<partial>?p2)))\<bar>" (is "?R3 \<le> _ ")
    using Z_integrable[OF assms(2)] Z_any_integrable_2[OF assms(2)]
    by (simp add:integral_sum sum_subtractf)
  also have "... = \<bar>(\<Sum>i \<in> ?Bd.
    ((\<integral>\<omega>. \<phi> (Z (fst i) \<omega>) \<partial>?p1) - (\<integral>\<omega>. \<phi>(Z (fst i) \<omega>) \<partial>?p2)) +
    ((\<integral>\<omega>. \<phi> (Z (snd i) \<omega>) \<partial>?p1) - (\<integral>\<omega>. \<phi>(Z (snd i) \<omega>) \<partial>?p2)) +
    ((\<integral>\<omega>. \<phi> (Z (fst i) \<omega> + Z (snd i) \<omega>) \<partial>?p2) - (\<integral>\<omega>. \<phi>(Z (fst i) \<omega> + Z (snd i) \<omega>) \<partial>?p1)))\<bar>"
    by (intro arg_cong[where f="abs"] sum.cong) auto
  also have "... \<le> (\<Sum>i \<in> ?Bd. \<bar>
    ((\<integral>\<omega>. \<phi> (Z (fst i) \<omega>) \<partial>?p1) - (\<integral>\<omega>. \<phi>(Z (fst i) \<omega>) \<partial>?p2)) +
    ((\<integral>\<omega>. \<phi> (Z (snd i) \<omega>) \<partial>?p1) - (\<integral>\<omega>. \<phi>(Z (snd i) \<omega>) \<partial>?p2)) +
    ((\<integral>\<omega>. \<phi> (Z (fst i) \<omega> + Z (snd i) \<omega>) \<partial>?p2) - (\<integral>\<omega>. \<phi>(Z (fst i) \<omega> + Z (snd i) \<omega>) \<partial>?p1))\<bar>)"
    by (intro sum_abs)
  also have "... \<le> (\<Sum>i \<in> ?Bd.
    \<bar>(\<integral>\<omega>. \<phi> (Z (fst i) \<omega>) \<partial>?p1) - (\<integral>\<omega>. \<phi>(Z (fst i) \<omega>) \<partial>?p2)\<bar> +
    \<bar>(\<integral>\<omega>. \<phi> (Z (snd i) \<omega>) \<partial>?p1) - (\<integral>\<omega>. \<phi>(Z (snd i) \<omega>) \<partial>?p2)\<bar> +
    \<bar>(\<integral>\<omega>. \<phi> (Z (fst i) \<omega> + Z (snd i) \<omega>) \<partial>?p2) - (\<integral>\<omega>. \<phi>(Z (fst i) \<omega> + Z (snd i) \<omega>) \<partial>?p1)\<bar>)"
    by (intro sum_mono) auto
  also have "... \<le> (\<Sum>i \<in> ?Bd. 2*\<gamma> + 2 *\<gamma> + 2^(k+2)*\<gamma>)"
    by (intro sum_mono add_mono Z_poly_diff_2 Z_poly_diff_3) auto
  also have "... = (2^(k+2)+4) *\<gamma> * real (card ?Bd)"
    by (simp add:algebra_simps)
  finally have Y_sq_exp_diff_1:"?R3 \<le> (2^(k+2)+4) *\<gamma> * real (card ?Bd)"
    by simp

  have "\<bar>(\<integral>\<omega>. Y \<omega> ^2 \<partial>?p1) - (\<integral>\<omega>. Y \<omega>^2 \<partial>?p2)\<bar> =
    \<bar>(\<integral>\<omega>. (\<Sum>i \<in> ?Bd. ?\<phi>2 (Z (fst i) \<omega>) (Z (snd i) \<omega>)) + Y \<omega> \<partial>?p1) -
     (\<integral>\<omega>. (\<Sum>i \<in> ?Bd. ?\<phi>2 (Z (fst i) \<omega>) (Z (snd i) \<omega>)) + Y \<omega> \<partial>?p2)\<bar>"
    by (intro_cong "[\<sigma>\<^sub>2 (-), \<sigma>\<^sub>1 abs]" more:  integral_cong_AE AE_pmfI Y_sq_eq') auto
  also have "... \<le> \<bar>(\<integral>\<omega>. Y \<omega> \<partial>?p1) - (\<integral>\<omega>. Y \<omega> \<partial>?p2)\<bar> +
    \<bar>(\<integral>\<omega>. (\<Sum>i \<in> ?Bd. ?\<phi>2 (Z (fst i) \<omega>) (Z (snd i) \<omega>)) \<partial>?p1) -
    (\<integral>\<omega>. (\<Sum>i \<in> ?Bd. ?\<phi>2 (Z (fst i) \<omega>) (Z (snd i) \<omega>)) \<partial>?p2)\<bar>"
    using Z_integrable[OF assms(2)] Z_any_integrable_2[OF assms(2)] int_Y by simp
  also have "... \<le>  2 *\<gamma> * real (card B) + ?R3"
    by (intro add_mono Y_exp_diff_2, simp)
  also have "... \<le> (2^(k+2)+4) *\<gamma> * real (card B) + (2^(k+2)+4) *\<gamma> * real (card ?Bd)"
    using  \<gamma>_nonneg by (intro add_mono Y_sq_exp_diff_1 mult_right_mono) auto
  also have "... = (2^(k+2)+4) *\<gamma> * (real (card B) + real (card ?Bd))"
    by (simp add:algebra_simps)
  also have "... = (2^(k+2)+4) * \<gamma> * real (card B)^2"
    using power2_nat_le_imp_le
    by (simp add:card_distinct_pairs of_nat_diff)
  finally have Y_sq_exp_diff:
    "\<bar>(\<integral>\<omega>. Y \<omega> ^2 \<partial>?p1) - (\<integral>\<omega>. Y \<omega>^2 \<partial>?p2)\<bar> \<le> (2^(k+2)+4) *\<gamma> * real (card B)^2" by simp

  have Y_exp_rough_bound: "\<bar>integral\<^sup>L (p c) Y\<bar> \<le> card B" (is "?L \<le> ?R") for c
  proof -
    have "?L \<le> (\<integral>\<omega>. \<bar>Y \<omega>\<bar> \<partial>(p c))"
      by (intro integral_abs_bound)
    also have "... \<le> (\<integral>\<omega>. real (card R)  \<partial>(p c))"
      unfolding Y_def using card_image_le[OF fin_R]
      by (intro integral_mono integrable_pmf_iff_bounded[where C="card R"])
       auto
    also have "... = card R" by simp
    also have "... \<le> card B" using assms by simp
    finally show ?thesis by simp
  qed

  have "\<bar>measure_pmf.variance ?p1 Y - measure_pmf.variance ?p2 Y\<bar> =
    \<bar>(\<integral>\<omega>. Y \<omega> ^2 \<partial>?p1) - (\<integral>\<omega>. Y \<omega> \<partial> ?p1)^2 - ((\<integral>\<omega>. Y \<omega> ^2 \<partial>?p2) - (\<integral>\<omega>. Y \<omega> \<partial> ?p2)^2)\<bar>"
    by (intro_cong "[\<sigma>\<^sub>2 (-), \<sigma>\<^sub>1 abs]" more: measure_pmf.variance_eq int_Y int_Y_sq)
  also have "... \<le> \<bar>(\<integral>\<omega>. Y \<omega>^2 \<partial>?p1) - (\<integral>\<omega>. Y \<omega>^2 \<partial>?p2)\<bar> + \<bar>(\<integral>\<omega>. Y \<omega> \<partial> ?p1)\<^sup>2 - (\<integral>\<omega>. Y \<omega> \<partial> ?p2)\<^sup>2\<bar>"
    by simp
  also have "... = \<bar>(\<integral>\<omega>. Y \<omega>^2 \<partial>?p1) - (\<integral>\<omega>. Y \<omega>^2 \<partial>?p2)\<bar> +
    \<bar>(\<integral>\<omega>. Y \<omega> \<partial> ?p1) - (\<integral>\<omega>. Y \<omega> \<partial> ?p2)\<bar>*\<bar>(\<integral>\<omega>. Y \<omega> \<partial> ?p1) + (\<integral>\<omega>. Y \<omega> \<partial> ?p2)\<bar>"
    by (simp add:power2_eq_square algebra_simps abs_mult[symmetric])
  also have "... \<le> (2^(k+2)+4) *\<gamma> * real (card B)^2 + (2*\<gamma> *real (card B)) *
    (\<bar>\<integral>\<omega>. Y \<omega> \<partial>?p1\<bar> + \<bar>\<integral>\<omega>. Y \<omega> \<partial> ?p2\<bar>)"
    using \<gamma>_nonneg
    by (intro add_mono mult_mono divide_left_mono Y_sq_exp_diff Y_exp_diff_2) auto
  also have "... \<le> (2^(k+2)+4)*\<gamma> * real (card B)^2 + (2*\<gamma> * real (card B)) *
    (real (card B) + real (card B))"
    using \<gamma>_nonneg by (intro add_mono mult_left_mono Y_exp_rough_bound) auto
  also have "... = (2^(k+2)+2^3) * \<gamma> * real (card B)^2"
    by (simp add:algebra_simps power2_eq_square)
  also have "... \<le> (2^(k+2)+2^(k+2)) * \<gamma> * real (card B)^2"
    using k_ge_2 \<gamma>_nonneg
    by (intro mult_right_mono add_mono power_increasing, simp_all)
  also have "... = (2^(k+3) / fact k) * card B^2"
    by (simp add:power_add \<gamma>_def)
  also have "... \<le> (1 / (real (card B) / \<epsilon>))^2 * card B^2"
    using k_condition(2) k_condition_h_2
    by (intro mult_right_mono) auto
  also have "... = \<epsilon>^2"
    using card_B_gt_0 by (simp add:divide_simps)
  finally show ?B
    by simp
qed

lemma
  assumes "card R \<le> card B"
  assumes "lim_balls_and_bins (k+1) p"
  assumes "k \<ge> 7.5 * (ln (card B) + 2)"
  shows exp_approx_2: "\<bar>measure_pmf.expectation p Y - \<mu>\<bar> \<le> card R / sqrt (card B)"
      (is "?AL \<le> ?AR")
    and var_approx_2: "measure_pmf.variance p Y  \<le> real (card R)^2 / card B"
      (is "?BL \<le> ?BR")
proof -
  define q where "q = (\<lambda>c. if c then \<Omega> else p)"

  have q_altdef: "q True = \<Omega>" "q False = p"
    unfolding q_def by auto

  have a:"lim_balls_and_bins (k+1) (q c)" for c
    unfolding q_def using assms lim_balls_and_bins_from_ind_balls_and_bins by auto

  define \<epsilon> :: real where "\<epsilon> = min (sqrt (1/card B)) (1 / exp 2)"

  have c: "\<epsilon> \<in> {0<..1 / exp 2}"
    using card_B_gt_0 unfolding \<epsilon>_def by auto

  have b: "5 * ln (card B / \<epsilon>) / ln (ln (card B / \<epsilon>)) \<le> real k"
  proof (cases "card B \<ge> exp 4")
    case True
    hence "sqrt(1/card B) \<le> sqrt(1/exp 4)"
      using card_B_gt_0 by (intro real_sqrt_le_mono divide_left_mono) auto
    also have "... = (1/exp 2)"
      by (subst powr_half_sqrt[symmetric]) (auto simp add:powr_divide exp_powr)
    finally have "sqrt(1/card B) \<le> (1 / exp 2)" by simp
    hence \<epsilon>_eq: "\<epsilon> = sqrt(1 /card B)"
      unfolding \<epsilon>_def by simp

    have "exp (6::real) = (exp 4) powr (3/2)"
      by (simp add:exp_powr)
    also have "...\<le> card B powr (3/2)"
      by (intro powr_mono2 True) auto
    finally have q4:"exp 6 \<le> card B powr (3/2)" by simp

    have "(2::real) \<le> exp 6"
      by (approximation 5)
    hence q1: "2 \<le> real (card B) powr (3 / 2)"
      using q4 by argo
    have "(1::real) < ln(exp 6)"
      by (approximation 5)
    also have "... \<le> ln (card B powr (3 / 2))"
      using card_B_gt_0 by (intro iffD2[OF ln_le_cancel_iff] q4) auto
    finally have q2: "1 < ln (card B powr (3 / 2))" by simp
    have "exp (exp (1::real)) \<le> exp 6"
      by (approximation 5)
    also have "... \<le> card B powr (3/2)" using q4 by simp
    finally have "exp (exp 1) \<le> card B powr (3/2)"
      by simp
    hence q3: "1\<le>ln(ln (card B powr (3/2)))"
      using card_B_gt_0 q1 by (intro iffD2[OF ln_ge_iff] ln_gt_zero, auto)

    have "5 * ln (card B / \<epsilon>) / ln (ln (card B / \<epsilon>)) =
      5 * ln (card B powr (1+1/2)) / ln(ln (card B powr (1+1/2)))"
      unfolding powr_add by (simp add:real_sqrt_divide  powr_half_sqrt[symmetric] \<epsilon>_eq)
    also have "... \<le> 5 * ln (card B powr (1+1/2)) / 1"
      using True q1 q2 q3 by (intro divide_left_mono mult_nonneg_nonneg mult_pos_pos
          ln_ge_zero ln_gt_zero) auto
    also have "... = 5 * (1+1/2) * ln(card B)"
      using card_B_gt_0 by (subst ln_powr) auto
    also have "... = 7.5 * ln(card B)" by simp
    also have "... \<le> k" using assms(3) by simp
    finally show ?thesis by simp
  next
    case False
    have "(1::real) / exp 2 \<le> sqrt(1 / exp 4)"
      by (simp add:real_sqrt_divide powr_half_sqrt[symmetric] exp_powr)
    also have "...\<le> sqrt(1 /card B)"
      using False card_B_gt_0
      by (intro real_sqrt_le_mono divide_left_mono mult_pos_pos) auto
    finally have "1 / exp 2 \<le> sqrt(1/card B)"
      by simp
    hence \<epsilon>_eq: "\<epsilon> = 1/ exp 2"
      unfolding \<epsilon>_def by simp

    have q2:"5 * (ln x + 2) / ln (ln x + 2) \<le> 7.5 * (ln x + 2)"
      if "x \<in> {1..exp 4}" for x:: real
      using that by (approximation 10 splitting: x=10)

    have "5 * ln (card B / \<epsilon>) / ln (ln (card B / \<epsilon>)) =
          5 * (ln (card B) +2) / ln (ln (card B) + 2)"
      using card_B_gt_0 unfolding \<epsilon>_eq by (simp add:ln_mult)
    also have "... \<le> 7.5 * (ln (card B) + 2)"
      using False card_B_gt_0 by (intro q2) auto
    also have "... \<le> k" using assms(3) by simp
    finally show ?thesis by simp
  qed

  have "?AL = \<bar>(\<integral>\<omega>. Y \<omega> \<partial>(q True)) - (\<integral>\<omega>. Y \<omega> \<partial>(q False))\<bar>"
    using exp_balls_and_bins unfolding q_def by simp
  also have "... \<le> \<epsilon> * card R"
    by (intro exp_approx[OF assms(1) a c b])
  also have "... \<le> sqrt (1 / card B) * card R"
    unfolding \<epsilon>_def by (intro mult_right_mono) auto
  also have "... = ?AR" using real_sqrt_divide by simp
  finally show "?AL \<le> ?AR" by simp

  show "?BL \<le> ?BR"
  proof (cases "R= {}")
    case True
    then show ?thesis unfolding Y_def by simp
  next
    case "False"
    hence "card R > 0" using fin_R by auto
    hence card_R_ge_1: "real (card R) \<ge> 1" by simp

    have "?BL \<le> measure_pmf.variance (q True) Y +
      \<bar>measure_pmf.variance (q True) Y - measure_pmf.variance (q False) Y\<bar>"
      unfolding q_def by auto
    also have "... \<le> measure_pmf.variance (q True) Y + \<epsilon>^2"
      by (intro add_mono var_approx[OF assms(1) a c b]) auto
    also have "... \<le> measure_pmf.variance (q True) Y + sqrt(1 / card B)^2"
      unfolding \<epsilon>_def by (intro add_mono power_mono) auto
    also have "... \<le> card R * (real (card R) - 1) / card B + sqrt(1 / card B)^2"
      unfolding q_altdef  by (intro add_mono var_balls_and_bins) auto
    also have "... = card R * (real (card R) - 1) / card B + 1 / card B"
      by (auto simp add:power_divide real_sqrt_divide)
    also have "... \<le> card R * (real (card R) - 1) / card B + card R / card B"
      by (intro add_mono divide_right_mono card_R_ge_1) auto
    also have "... = (card R * (real (card R) - 1) + card R) / card B"
      by argo
    also have "... = ?BR"
      by (simp add:algebra_simps power2_eq_square)
    finally show "?BL \<le> ?BR" by simp
  qed
qed

lemma devitation_bound:
  assumes "card R \<le> card B"
  assumes "lim_balls_and_bins k p"
  assumes "real k \<ge> C\<^sub>2 * ln (real (card B)) + C\<^sub>3"
  shows "measure p {\<omega>. \<bar>Y \<omega> - \<mu>\<bar> > 9 * real (card R) / sqrt (real (card B))} \<le> 1 / 2^6"
    (is "?L \<le> ?R")
proof (cases "card R > 0")
  case True

  define k' :: nat where "k' = k - 1"
  have "(1::real) \<le> 7.5 * 0 + 16" by simp
  also have "... \<le> 7.5 * ln (real (card B)) + 16"
    using card_B_ge_1 by (intro add_mono mult_left_mono ln_ge_zero) auto
  also have "... \<le> k"  using assms(3) unfolding C\<^sub>2_def C\<^sub>3_def by simp
  finally have k_ge_1: "k \<ge> 1" by simp
  have lim: "lim_balls_and_bins (k'+1) p"
    using k_ge_1 assms(2) unfolding  k'_def by simp

  have k'_min: "real k' \<ge> 7.5 * (ln (real (card B)) + 2)"
    using k_ge_1 assms(3) unfolding C\<^sub>2_def C\<^sub>3_def k'_def by simp

  let ?r = "real (card R)"
  let ?b = "real (card B)"
  have a: "integrable p (\<lambda>\<omega>. (Y \<omega>)\<^sup>2)"
    unfolding Y_def
    by (intro integrable_pmf_iff_bounded[where C="real (card R)^2"])
     (auto intro!: card_image_le[OF fin_R])

  have "?L \<le> \<P>(\<omega> in measure_pmf p. \<bar>Y \<omega>- (\<integral>\<omega>. Y \<omega> \<partial>p)\<bar> \<ge> 8*?r / sqrt ?b)"
  proof (rule measure_pmf.pmf_mono[OF refl])
    fix \<omega> assume "\<omega> \<in> set_pmf p"
    assume a:"\<omega> \<in> {\<omega>. 9 * real (card R) / sqrt (real (card B)) < \<bar>Y \<omega> - \<mu>\<bar>}"
    have "8 * ?r / sqrt ?b = 9 * ?r / sqrt ?b - ?r / sqrt ?b"
      by simp
    also have "... \<le>  \<bar>Y \<omega> - \<mu>\<bar> - \<bar> (\<integral>\<omega>. Y \<omega> \<partial>p) - \<mu>\<bar>"
      using a by (intro diff_mono exp_approx_2[OF assms(1) lim k'_min]) simp
    also have "... \<le> \<bar>Y \<omega> - (\<integral>\<omega>. Y \<omega> \<partial>p)\<bar>"
      by simp
    finally have "8 * ?r / sqrt ?b \<le> \<bar>Y \<omega> - (\<integral>\<omega>. Y \<omega> \<partial>p)\<bar>" by simp
    thus "\<omega> \<in> {\<omega> \<in> space (measure_pmf p). 8 * ?r / sqrt ?b \<le> \<bar>Y \<omega> - (\<integral>\<omega>. Y \<omega> \<partial>p)\<bar>}"
      by simp
  qed
  also have "... \<le> measure_pmf.variance p Y / (8*?r / sqrt ?b)^2"
    using True card_B_gt_0 a
    by (intro measure_pmf.Chebyshev_inequality) auto
  also have "... \<le> (?r^2 / ?b) / (8*?r / sqrt ?b)^2"
    by (intro divide_right_mono var_approx_2[OF assms(1) lim k'_min]) simp
  also have "... = 1/2^6"
    using card_B_gt_0 True
    by (simp add:power2_eq_square)
  finally show ?thesis by simp
next
  case False
  hence "R = {}" "card R = 0" using fin_R by auto
  thus ?thesis
    unfolding Y_def \<mu>_def by simp
qed

end

unbundle no_intro_cong_syntax

end