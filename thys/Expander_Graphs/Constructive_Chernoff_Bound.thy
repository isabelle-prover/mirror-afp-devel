subsection \<open>Constructive Chernoff Bound\label{sec:constructive_chernoff_bound}\<close>

text \<open>This section formalizes Theorem~5 by Impagliazzo and Kabanets~\cite{impagliazzo2010}. It is
a general result with which Chernoff-type tail bounds for various kinds of weakly dependent random 
variables can be obtained. The results here are general and will be applied in
Section~\ref{sec:random_walks} to random walks in expander graphs.\<close>

theory Constructive_Chernoff_Bound
  imports 
    "HOL-Probability.Probability_Measure" 
    Frequency_Moments.Product_PMF_Ext
    Weighted_Arithmetic_Geometric_Mean.Weighted_Arithmetic_Geometric_Mean
begin

lemma powr_mono_rev:
  fixes x :: real
  assumes "a \<le> b" and  "x > 0" "x \<le> 1"
  shows "x powr b \<le> x powr a"
proof -
  have "x powr b = (1/x) powr (-b)"
    using assms by (simp add: powr_divide powr_minus_divide)
  also have "... \<le> (1/x) powr (-a)"
    using assms by (intro powr_mono) auto
  also have "... = x powr a"
    using assms by (simp add: powr_divide powr_minus_divide)
  finally show ?thesis by simp
qed

lemma exp_powr: "(exp x) powr y = exp (x*y)" for x :: real
  unfolding powr_def by simp

lemma integrable_pmf_iff_bounded:
  fixes f :: "'a \<Rightarrow> real"
  assumes "\<And>x. x \<in> set_pmf p \<Longrightarrow> abs (f x) \<le> C"
  shows "integrable (measure_pmf p) f"
proof -
  obtain x where "x \<in> set_pmf p"
    using set_pmf_not_empty by fast
  hence "C \<ge> 0" using assms(1) by fastforce
  hence " (\<integral>\<^sup>+ x. ennreal (abs (f x)) \<partial>measure_pmf p) \<le> (\<integral>\<^sup>+ x. C \<partial>measure_pmf p)" 
    using assms ennreal_le_iff
    by (intro nn_integral_mono_AE AE_pmfI) auto
  also have "... = C"
    by simp
  also have "... < Orderings.top"
    by simp
  finally have "(\<integral>\<^sup>+ x. ennreal (abs (f x)) \<partial>measure_pmf p) < Orderings.top" by simp
  thus ?thesis 
    by (intro iffD2[OF integrable_iff_bounded]) auto
qed

lemma split_pair_pmf: 
  "measure_pmf.prob (pair_pmf A B) S = integral\<^sup>L A (\<lambda>a. measure_pmf.prob B {b. (a,b) \<in> S})" 
  (is "?L = ?R")
proof -
  have a:"integrable (measure_pmf A) (\<lambda>x. measure_pmf.prob B {b. (x, b) \<in> S})"
    by (intro integrable_pmf_iff_bounded[where C="1"]) simp

  have "?L = (\<integral>\<^sup>+x. indicator S x \<partial>(measure_pmf (pair_pmf A B)))"
    by (simp add: measure_pmf.emeasure_eq_measure)
  also have "... = (\<integral>\<^sup>+x. (\<integral>\<^sup>+y. indicator S (x,y) \<partial>B) \<partial>A)"
    by (simp add: nn_integral_pair_pmf')  
  also have "... = (\<integral>\<^sup>+x. (\<integral>\<^sup>+y. indicator {b. (x,b) \<in> S} y \<partial>B) \<partial>A)"
    by (simp add:indicator_def)
  also have "... = (\<integral>\<^sup>+x. (measure_pmf.prob B {b. (x,b) \<in> S}) \<partial>A)"
    by (simp add: measure_pmf.emeasure_eq_measure)
  also have "... = ?R"
    using a
    by (subst nn_integral_eq_integral) auto
  finally show ?thesis by simp
qed

lemma split_pair_pmf_2: 
  "measure(pair_pmf A B) S = integral\<^sup>L B (\<lambda>a. measure_pmf.prob A {b. (b,a) \<in> S})" 
  (is "?L = ?R")
proof -
  have "?L = measure (pair_pmf B A) {\<omega>. (snd \<omega>, fst \<omega>) \<in> S}"
    by (subst pair_commute_pmf) (simp add:vimage_def case_prod_beta)
  also have "... = ?R"
    unfolding split_pair_pmf by simp
  finally show ?thesis by simp
qed

definition KL_div :: "real \<Rightarrow> real \<Rightarrow> real" 
  where "KL_div p q = p * ln (p/q) + (1-p) * ln ((1-p)/(1-q))"

theorem impagliazzo_kabanets_pmf:
  fixes Y :: "nat \<Rightarrow> 'a \<Rightarrow> bool" 
  fixes p :: "'a pmf"
  assumes "n > 0"
  assumes "\<And>i. i \<in> {..<n} \<Longrightarrow> \<delta> i \<in> {0..1}"
  assumes "\<And>S. S \<subseteq> {..<n} \<Longrightarrow> measure p {\<omega>. (\<forall>i \<in> S. Y i \<omega>)} \<le> (\<Prod>i \<in> S. \<delta> i)"
  defines "\<delta>_avg \<equiv> (\<Sum>i\<in> {..<n}. \<delta> i)/n"
  assumes "\<gamma> \<in> {\<delta>_avg..1}"
  assumes "\<delta>_avg > 0" 
  shows "measure p {\<omega>. real (card {i \<in> {..<n}. Y i \<omega>}) \<ge> \<gamma> * n} \<le> exp (-real n * KL_div \<gamma> \<delta>_avg)" 
    (is "?L \<le> ?R")
proof -
  let ?n = "real n"
  define q :: real where "q = (if \<gamma> = 1 then 1 else (\<gamma>-\<delta>_avg)/(\<gamma>*(1-\<delta>_avg)))"

  define g where "g \<omega> = card {i. i < n \<and> \<not>Y i \<omega>}" for \<omega>
  let ?E = "(\<lambda>\<omega>. real (card {i. i < n \<and> Y i \<omega>}) \<ge> \<gamma> * n)"
  let ?\<Xi> = "prod_pmf {..<n} (\<lambda>_. bernoulli_pmf q)"

  have q_range:"q \<in>{0..1}" 
  proof (cases "\<gamma> < 1")
    case True
    then show ?thesis 
      using assms(5,6)
      unfolding q_def by (auto intro!:divide_nonneg_pos simp add:algebra_simps)
  next
    case False
    hence "\<gamma> = 1" using assms(5) by simp
    then show ?thesis unfolding q_def by simp
  qed

  have abs_pos_le_1I: "abs x \<le> 1" if "x \<ge> 0" "x \<le> 1" for x :: real
    using that by auto

  have \<gamma>_n_nonneg: "\<gamma>*?n \<ge> 0" 
    using assms(1,5,6) by simp 
  define r where "r = n - nat \<lceil>\<gamma>*n\<rceil>"

  have 2:"(1-q) ^ r \<le> (1-q)^ g \<omega>" if "?E \<omega>" for \<omega>
  proof -
    have "g \<omega> = card ({i. i < n} - {i. i < n \<and> Y i \<omega>})"
      unfolding g_def by (intro arg_cong[where f="\<lambda>x. card x"]) auto
    also have "... = card {i. i < n} - card {i. i < n \<and> Y i \<omega>}"
      by (subst card_Diff_subset, auto)
    also have "... \<le> card {i. i < n} - nat \<lceil>\<gamma>*n\<rceil>"
      using that \<gamma>_n_nonneg by (intro diff_le_mono2) simp
    also have "... = r"
      unfolding r_def by simp
    finally have "g \<omega> \<le> r" by simp
    thus "(1-q) ^ r \<le> (1-q) ^ (g \<omega>)"
      using q_range by (intro power_decreasing) auto
  qed

  have \<gamma>_gt_0: "\<gamma> > 0"
    using assms(5,6) by simp

  have q_lt_1: "q < 1" if "\<gamma> < 1"
  proof -
    have "\<delta>_avg < 1" using assms(5) that by simp
    hence "(\<gamma> - \<delta>_avg) / (\<gamma> * (1 - \<delta>_avg)) < 1" 
      using \<gamma>_gt_0 assms(6) that
      by (subst pos_divide_less_eq) (auto simp add:algebra_simps)
    thus "q < 1"
      unfolding q_def using that by simp
  qed

  have 5: "(\<delta>_avg * q + (1-q)) / (1-q) powr (1-\<gamma>) = exp (- KL_div \<gamma> \<delta>_avg)" (is "?L1 = ?R1")
    if "\<gamma> < 1" 
  proof -
    have \<delta>_avg_range: "\<delta>_avg \<in> {0<..<1}" 
      using that assms(5,6)  by simp

    have "?L1 = (1 - (1-\<delta>_avg) * q) / (1-q) powr (1-\<gamma>)"
      by (simp add:algebra_simps)
    also have "... = (1 - (\<gamma>-\<delta>_avg) / \<gamma> ) / (1-q) powr (1-\<gamma>)"
      unfolding q_def using that \<gamma>_gt_0 \<delta>_avg_range by simp
    also have "... = (\<delta>_avg / \<gamma>) / (1-q) powr (1-\<gamma>)"
      using \<gamma>_gt_0 by (simp add:divide_simps)
    also have "... = (\<delta>_avg / \<gamma>) * (1/(1-q)) powr (1-\<gamma>)"
      using q_lt_1[OF that] by (subst powr_divide, simp_all)
    also have "... = (\<delta>_avg / \<gamma>) * (1/((\<gamma>*(1-\<delta>_avg)-(\<gamma>-\<delta>_avg))/(\<gamma>*(1-\<delta>_avg)))) powr (1-\<gamma>)"
      using \<gamma>_gt_0 \<delta>_avg_range unfolding q_def by (simp add:divide_simps)
    also have "... = (\<delta>_avg / \<gamma>) * ((\<gamma> / \<delta>_avg) *((1-\<delta>_avg)/(1-\<gamma>))) powr (1-\<gamma>)"
      by (simp add:algebra_simps)
    also have "... = (\<delta>_avg / \<gamma>) * (\<gamma> / \<delta>_avg) powr (1-\<gamma>) *((1-\<delta>_avg)/(1-\<gamma>)) powr (1-\<gamma>)"
      using \<gamma>_gt_0  \<delta>_avg_range that by (subst powr_mult, auto)
    also have "... = (\<delta>_avg / \<gamma>) powr 1 * (\<delta>_avg / \<gamma>) powr -(1-\<gamma>) *((1-\<delta>_avg)/(1-\<gamma>)) powr (1-\<gamma>)"
      using \<gamma>_gt_0 \<delta>_avg_range that unfolding powr_minus_divide by (simp add:powr_divide)
    also have "... = (\<delta>_avg / \<gamma>) powr \<gamma> *((1-\<delta>_avg)/(1-\<gamma>)) powr (1-\<gamma>)"
      by (subst powr_add[symmetric]) simp
    also have "... = exp ( ln ((\<delta>_avg / \<gamma>) powr \<gamma> *((1-\<delta>_avg)/(1-\<gamma>)) powr (1-\<gamma>)))"
      using \<gamma>_gt_0 \<delta>_avg_range that by (intro exp_ln[symmetric] mult_pos_pos) auto
    also have "... =  exp ((ln ((\<delta>_avg / \<gamma>) powr \<gamma>) + ln (((1 - \<delta>_avg) / (1 - \<gamma>)) powr (1-\<gamma>))))" 
      using \<gamma>_gt_0 \<delta>_avg_range that by (subst ln_mult) auto
    also have "... =  exp ((\<gamma> * ln (\<delta>_avg / \<gamma>) + (1 - \<gamma>) * ln ((1 - \<delta>_avg) / (1 - \<gamma>))))" 
      using \<gamma>_gt_0 \<delta>_avg_range that by (simp add:ln_powr algebra_simps)
    also have "... =  exp (- (\<gamma> * ln (\<gamma> / \<delta>_avg) + (1 - \<gamma>) * ln ((1 - \<gamma>) / (1 - \<delta>_avg))))" 
      using \<gamma>_gt_0 \<delta>_avg_range that by (simp add: ln_div algebra_simps)
    also have "... = ?R1"
      unfolding KL_div_def by simp

    finally show ?thesis by simp
  qed

  have 3: "(\<delta>_avg * q + (1-q)) ^ n / (1-q) ^ r \<le> exp (- ?n* KL_div \<gamma> \<delta>_avg)" (is "?L1 \<le> ?R1")
  proof (cases "\<gamma> < 1")
    case True
    have "\<gamma> * real n \<le> 1 * real n" 
      using True by (intro mult_right_mono) auto
    hence "r = real n - real (nat \<lceil>\<gamma> * real n\<rceil>)"
      unfolding r_def by (subst of_nat_diff) auto
    also have "... = real n - \<lceil>\<gamma> * real n\<rceil>"
      using \<gamma>_n_nonneg by (subst of_nat_nat, auto)
    also have "... \<le> ?n - \<gamma> * ?n"
      by (intro diff_mono) auto
    also have "... = (1-\<gamma>) *?n" by (simp add:algebra_simps)
    finally have r_bound: "r \<le> (1-\<gamma>)*n" by simp

    have "?L1 = (\<delta>_avg * q + (1-q)) ^ n / (1-q) powr r"
      using q_lt_1[OF True] assms(1) by (simp add: powr_realpow)
    also have "... = (\<delta>_avg * q + (1-q)) powr n / (1-q) powr r"
      using q_lt_1[OF True] assms(6) q_range
      by (subst powr_realpow[symmetric], auto intro!:add_nonneg_pos)
    also have "... \<le> (\<delta>_avg * q + (1-q)) powr n / (1-q) powr ((1-\<gamma>)*n)"
      using q_range q_lt_1[OF True] by (intro divide_left_mono powr_mono_rev r_bound) auto
    also have "... = (\<delta>_avg * q + (1-q)) powr n / ((1-q) powr (1-\<gamma>)) powr n"
      unfolding powr_powr by simp
    also have "... = ((\<delta>_avg * q + (1-q)) / (1-q) powr (1-\<gamma>)) powr n"
      using assms(6) q_range by (subst powr_divide) auto
    also have "... = exp (- KL_div \<gamma> \<delta>_avg) powr real n"
      unfolding 5[OF True] by simp
    also have "... = ?R1" 
      unfolding exp_powr by simp
    finally show ?thesis by simp
  next
    case False
    hence \<gamma>_eq_1: "\<gamma>=1" using assms(5) by simp
    have "?L1 = \<delta>_avg ^ n"
      using \<gamma>_eq_1 r_def q_def by simp
    also have "... = exp( - KL_div 1 \<delta>_avg) ^ n"
      unfolding KL_div_def using assms(6) by (simp add:ln_div) 
    also have "... = ?R1" 
      using \<gamma>_eq_1 by (simp add: powr_realpow[symmetric] exp_powr)
    finally show ?thesis by simp
  qed

  have 4: "(1 - q) ^ r > 0" 
  proof (cases "\<gamma> < 1")
    case True
    then show ?thesis using q_lt_1[OF True] by simp
  next
    case False
    hence "\<gamma>=1" using assms(5) by simp
    hence "r=0" unfolding r_def by simp
    then show ?thesis by simp
  qed

  have "(1-q) ^ r * ?L = (\<integral>\<omega>. indicator {\<omega>. ?E \<omega>} \<omega> * (1-q) ^ r \<partial>p)"
    by simp
  also have "... \<le> (\<integral>\<omega>. indicator {\<omega>. ?E \<omega>} \<omega> * (1-q) ^ g \<omega> \<partial>p)"
    using q_range 2 by (intro integral_mono_AE integrable_pmf_iff_bounded[where C="1"] 
        abs_pos_le_1I mult_le_one power_le_one AE_pmfI) (simp_all split:split_indicator) 
  also have "... = (\<integral>\<omega>. indicator {\<omega>. ?E \<omega>} \<omega> * (\<Prod>i \<in> {i. i < n \<and> \<not>Y i \<omega>}. (1-q)) \<partial>p)"
    unfolding g_def using q_range
    by (intro integral_cong_AE AE_pmfI, simp_all add:powr_realpow)
  also have "... = (\<integral>\<omega>. indicator {\<omega>. ?E \<omega>} \<omega> * measure ?\<Xi> ({j. j < n \<and> \<not>Y j \<omega>} \<rightarrow> {False}) \<partial>p)"
    using q_range by (subst prob_prod_pmf') (auto simp add:measure_pmf_single)
  also have "... = (\<integral>\<omega>. measure ?\<Xi> {\<xi>. ?E \<omega> \<and> (\<forall>i\<in>{j. j < n \<and> \<not>Y j \<omega>}. \<not>\<xi> i)} \<partial>p)"
    by (intro integral_cong_AE AE_pmfI, simp_all add:Pi_def split:split_indicator)
  also have "... = (\<integral>\<omega>. measure ?\<Xi> {\<xi>. ?E \<omega> \<and> (\<forall>i\<in>{..<n}. \<xi> i \<longrightarrow> Y i \<omega>)} \<partial>p)"
    by (intro integral_cong_AE AE_pmfI measure_eq_AE) auto
  also have "... = measure (pair_pmf p ?\<Xi>) {\<phi>.?E (fst \<phi>)\<and>(\<forall>i \<in> {..<n}. snd \<phi> i \<longrightarrow> Y i (fst \<phi>))}" 
    unfolding split_pair_pmf by simp
  also have "... \<le> measure (pair_pmf p ?\<Xi>) {\<phi>. (\<forall>i \<in> {j. j < n \<and> snd \<phi> j}. Y i (fst \<phi>))}"
    by (intro measure_pmf.pmf_mono[OF refl], auto)
  also have "... = (\<integral>\<xi>. measure p {\<omega>. \<forall>i\<in>{j. j< n \<and> \<xi> j}. Y i \<omega>} \<partial> ?\<Xi>)"
    unfolding split_pair_pmf_2 by simp
  also have "... \<le> (\<integral>a. (\<Prod>i \<in> {j. j < n \<and> a j}. \<delta> i) \<partial> ?\<Xi>)"
    using assms(2) by (intro integral_mono_AE AE_pmfI assms(3) subsetI  prod_le_1 prod_nonneg 
        integrable_pmf_iff_bounded[where C="1"] abs_pos_le_1I) auto
  also have "... = (\<integral>a. (\<Prod>i \<in> {..<n}. \<delta> i^ of_bool(a i)) \<partial> ?\<Xi>)"
    unfolding of_bool_def by (intro integral_cong_AE AE_pmfI) 
      (auto simp add:if_distrib prod.If_cases Int_def)
  also have "... = (\<Prod>i<n. (\<integral>a. (\<delta> i ^ of_bool a) \<partial>(bernoulli_pmf q)))"
    using assms(2) by (intro expectation_prod_Pi_pmf integrable_pmf_iff_bounded[where C="1"]) auto
  also have "... = (\<Prod>i<n. \<delta> i * q + (1-q))"
    using q_range by simp
  also have "... = (root (card {..<n}) (\<Prod>i<n. \<delta> i * q + (1-q))) ^ (card {..<n})"
    using assms(1,2) q_range by (intro real_root_pow_pos2[symmetric] prod_nonneg) auto
  also have "... \<le> ((\<Sum>i<n. \<delta> i * q + (1-q))/card{..<n})^(card {..<n})"
    using assms(1,2) q_range by (intro power_mono arithmetic_geometric_mean) 
      (auto intro: prod_nonneg)
  also have "... = ((\<Sum>i<n. \<delta> i * q)/n + (1-q))^n"
    using assms(1) by (simp add:sum.distrib divide_simps mult.commute)
  also have "... = (\<delta>_avg * q + (1-q))^n"
    unfolding \<delta>_avg_def by (simp add: sum_distrib_right[symmetric])
  finally have "(1-q) ^ r * ?L \<le> (\<delta>_avg * q + (1-q)) ^ n" by simp
  hence "?L \<le> (\<delta>_avg * q + (1-q)) ^ n / (1-q) ^ r"
    using 4 by (subst pos_le_divide_eq) (auto simp add:algebra_simps)
  also have "... \<le> ?R"
    by (intro 3) 
  finally show ?thesis by simp
qed

text \<open>The distribution of a random variable with a countable range is a discrete probability space, 
i.e., induces a PMF. Using this it is possible to generalize the previous result to arbitrary
probability spaces.\<close>

lemma (in prob_space) establish_pmf:
  fixes f :: "'a \<Rightarrow> 'b"
  assumes rv: "random_variable discrete f"
  assumes "countable (f ` space M)"
  shows "distr M discrete f \<in> {M. prob_space M \<and> sets M = UNIV \<and> (AE x in M. measure M {x} \<noteq> 0)}"
proof -
  define N where "N = {x \<in> space M.\<not> prob (f -` {f x} \<inter> space M) \<noteq> 0}"
  define I where "I = {z \<in> (f ` space M). prob (f -` {z}  \<inter> space M) = 0}"

  have countable_I: " countable I" 
    unfolding I_def by (intro countable_subset[OF _ assms(2)]) auto

  have disj: "disjoint_family_on (\<lambda>y. f -` {y} \<inter> space M) I" 
    unfolding disjoint_family_on_def by auto

  have N_alt_def: "N = (\<Union>y \<in> I. f -` {y} \<inter> space M)"
    unfolding N_def I_def by (auto simp add:set_eq_iff)
  have "emeasure M N = \<integral>\<^sup>+ y. emeasure M (f -` {y} \<inter> space M) \<partial>count_space I"
    using rv countable_I unfolding N_alt_def 
    by (subst emeasure_UN_countable) (auto simp add:disjoint_family_on_def) 
  also have "... =  \<integral>\<^sup>+ y. 0 \<partial>count_space I"
    unfolding I_def using emeasure_eq_measure ennreal_0
    by (intro nn_integral_cong) auto 
  also have "... = 0" by simp
  finally have 0:"emeasure M N = 0" by simp

  have 1:"N \<in> events" 
    unfolding N_alt_def using rv
    by (intro  sets.countable_UN'' countable_I) simp

  have " AE x in M. prob (f -` {f x} \<inter> space M) \<noteq> 0"
    using 0 1 by (subst AE_iff_measurable[OF _ N_def[symmetric]])  
  hence " AE x in M. measure (distr M discrete f) {f x} \<noteq> 0"
    by (subst measure_distr[OF rv], auto)
  hence "AE x in distr M discrete f. measure (distr M discrete f) {x} \<noteq> 0"
    by (subst AE_distr_iff[OF rv], auto)
  thus ?thesis 
    using prob_space_distr rv by auto
qed

lemma singletons_image_eq:
  "(\<lambda>x. {x}) ` T \<subseteq> Pow T"
  by auto

theorem (in prob_space) impagliazzo_kabanets:
  fixes Y :: "nat \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "n > 0"
  assumes "\<And>i. i \<in> {..<n} \<Longrightarrow> random_variable discrete (Y i)"
  assumes "\<And>i. i \<in> {..<n} \<Longrightarrow> \<delta> i \<in> {0..1}"
  assumes "\<And>S. S \<subseteq> {..<n} \<Longrightarrow> \<P>(\<omega> in M. (\<forall>i \<in> S. Y i \<omega>)) \<le> (\<Prod>i \<in> S. \<delta> i)"
  defines "\<delta>_avg \<equiv> (\<Sum>i\<in> {..<n}. \<delta> i)/n" 
  assumes "\<gamma> \<in> {\<delta>_avg..1}" "\<delta>_avg > 0"
  shows "\<P>(\<omega> in M. real (card {i \<in> {..<n}. Y i \<omega>}) \<ge> \<gamma> * n) \<le> exp (-real n * KL_div \<gamma> \<delta>_avg)" 
    (is "?L \<le> ?R")
proof -
  define f where "f = (\<lambda>\<omega> i. if i < n then Y i \<omega> else False)"
  define g where "g = (\<lambda>\<omega> i. if i < n then \<omega> i else False)"
  define T where "T = {\<omega>. (\<forall>i. \<omega> i \<longrightarrow> i < n)}"

  have g_idem: "g \<circ> f = f" unfolding f_def g_def by (simp add:comp_def)

  have f_range: " f \<in> space M \<rightarrow> T" 
    unfolding T_def f_def by simp

  have "T = PiE_dflt {..<n} False (\<lambda>_. UNIV)"
    unfolding T_def PiE_dflt_def by auto
  hence "finite T" 
    using finite_PiE_dflt by auto
  hence countable_T: "countable T" 
    by (intro countable_finite)
  moreover have "f ` space M \<subseteq> T" 
    using f_range by auto
  ultimately have countable_f: "countable (f ` space M)"
    using countable_subset by auto

  have "f -` y \<inter> space M \<in> events" if t:"y \<in> (\<lambda>x. {x}) ` T" for y
  proof -
    obtain t where "y = {t}" and t_range: "t \<in> T" using t by auto
    hence "f -` y \<inter> space M = {\<omega> \<in> space M. f \<omega> = t}" 
      by (auto simp add:vimage_def)
    also have "... = {\<omega> \<in> space M. (\<forall>i < n. Y i \<omega> = t i)}"
      using t_range unfolding f_def T_def by auto
    also have "... = (\<Inter>i \<in> {..<n}. {\<omega> \<in> space M. Y i \<omega> = t i})"
      using assms(1) by auto
    also have "... \<in> events"
      using assms(1,2)
      by (intro sets.countable_INT) auto
    finally show ?thesis by simp
  qed

  hence "random_variable (count_space T) f"
    using sigma_sets_singletons[OF countable_T] singletons_image_eq f_range
    by (intro measurable_sigma_sets[where \<Omega>="T" and A=" (\<lambda>x. {x}) ` T"]) simp_all
  moreover have "g \<in> measurable discrete (count_space T)"
    unfolding g_def T_def by simp
  ultimately have "random_variable discrete (g \<circ> f)"
    by simp
  hence rv:"random_variable discrete f"
    unfolding g_idem by simp
  
  define M' :: "(nat \<Rightarrow> bool) measure"
    where "M' = distr M discrete f" 

  define \<Omega> where "\<Omega> = Abs_pmf M'"
  have a:"measure_pmf (Abs_pmf M') = M'"
    unfolding M'_def
    by (intro Abs_pmf_inverse[OF establish_pmf] rv countable_f)

  have b:"{i. (i < n \<longrightarrow> Y i x) \<and> i < n} = {i. i < n \<and> Y i x}" for x
    by auto

  have c: "measure \<Omega> {\<omega>. \<forall>i\<in>S. \<omega> i} \<le> prod \<delta> S" (is "?L1 \<le> ?R1") if "S \<subseteq> {..<n}" for S
  proof -
    have d: "i \<in> S \<Longrightarrow> i < n" for i 
      using that by auto
    have "?L1 = measure M' {\<omega>. \<forall>i\<in>S. \<omega> i}"
      unfolding \<Omega>_def a by simp
    also have "... = \<P>(\<omega> in M. (\<forall>i \<in> S. Y i \<omega>))"
      unfolding M'_def using that d
      by (subst measure_distr[OF rv]) (auto simp add:f_def Int_commute Int_def)
    also have "... \<le> ?R1"
      using that assms(4) by simp
    finally show ?thesis by simp
  qed

  have "?L = measure M' {\<omega>. real (card {i. i < n \<and> \<omega> i}) \<ge> \<gamma> * n}"
    unfolding M'_def by (subst measure_distr[OF rv]) 
      (auto simp add:f_def algebra_simps Int_commute Int_def b)
  also have "... = measure_pmf.prob \<Omega> {\<omega>. real (card {i \<in> {..<n}. \<omega> i}) \<ge> \<gamma> * n}"
    unfolding \<Omega>_def a by simp
  also have "... \<le> ?R"
    using assms(1,3,6,7) c unfolding \<delta>_avg_def
    by (intro impagliazzo_kabanets_pmf) auto
  finally show ?thesis by simp
qed

end