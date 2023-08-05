section \<open>Outer Algorithm\label{sec:outer_algorithm}\<close>

text \<open>This section introduces the final solution with optimal size space usage. Internally it relies
on the inner algorithm described in Section~\ref{sec:inner_algorithm}, dependending on the
paramaters $n$, $\varepsilon$ and $\delta$ it either uses the inner algorithm directly or if
$\varepsilon^{-1}$ is larger than $\ln n$ it runs $\frac{\varepsilon^{-1}}{\ln \ln n}$ copies of the
inner algorithm (with the modified failure probability $\frac{1}{\ln n}$) using an expander to
select its seeds. The theorems below verify that the probability that the relative
accuracy of the median of the copies is too large is below $\varepsilon$.\<close>

theory Distributed_Distinct_Elements_Outer_Algorithm
  imports
    Distributed_Distinct_Elements_Accuracy
    Prefix_Free_Code_Combinators.Prefix_Free_Code_Combinators
    Frequency_Moments.Landau_Ext
    Landau_Symbols.Landau_More
begin

unbundle intro_cong_syntax

text \<open>The following are non-asymptotic hard bounds on the space usage for the sketches and seeds
repsectively. The end of this section contains a proof that the sum is asymptotically in
$\mathcal O(\ln( \varepsilon^{-1}) \delta^{-1} + \ln n)$.\<close>

definition "state_space_usage = (\<lambda>(n,\<epsilon>,\<delta>). 2^40 * (ln(1/\<delta>)+1)/ \<epsilon>^2 + log 2 (log 2 n + 3))"
definition "seed_space_usage = (\<lambda>(n,\<epsilon>,\<delta>). 2^30+2^23*ln n+48*(log 2(1/\<epsilon>)+16)\<^sup>2+336*ln (1/\<delta>))"

locale outer_algorithm =
  fixes n :: nat
  fixes \<delta> :: real
  fixes \<epsilon> :: real
  assumes n_gt_0: "n > 0"
  assumes \<delta>_gt_0: "\<delta> > 0" and \<delta>_lt_1: "\<delta> < 1"
  assumes \<epsilon>_gt_0: "\<epsilon> > 0" and \<epsilon>_lt_1: "\<epsilon> < 1"
begin

definition n\<^sub>0 where "n\<^sub>0 = max (real n) (exp (exp 5))"
definition stage_two where "stage_two = (\<delta> < (1/ln n\<^sub>0))"
definition \<delta>\<^sub>i :: real where "\<delta>\<^sub>i = (if stage_two then (1/ln n\<^sub>0) else \<delta>)"
definition m :: nat where "m = (if stage_two then nat \<lceil>4 * ln (1/ \<delta>)/ln (ln n\<^sub>0)\<rceil> else 1)"
definition \<alpha> where "\<alpha> = (if stage_two then (1/ln n\<^sub>0) else 1)"

lemma m_lbound:
  assumes "stage_two"
  shows "m \<ge> 4 * ln (1/ \<delta>)/ln(ln n\<^sub>0)"
proof -
  have "m = real (nat \<lceil>4 * ln (1 / \<delta>) / ln (ln n\<^sub>0)\<rceil>)"
    using assms unfolding m_def by simp
  also have "... \<ge> 4 * ln (1 / \<delta>) / ln (ln n\<^sub>0)"
    by linarith
  finally show ?thesis by simp
qed

lemma n_lbound:
  "n\<^sub>0 \<ge> exp (exp 5)" "ln n\<^sub>0 \<ge> exp 5" "5 \<le> ln (ln n\<^sub>0)" "ln n\<^sub>0 > 1" "n\<^sub>0 > 1"
proof -
  show 0:"n\<^sub>0 \<ge> exp (exp 5)"
    unfolding n\<^sub>0_def by simp
  have "(1::real) \<le> exp (exp 5)"
    by (approximation 5)
  hence "n\<^sub>0 \<ge> 1"
    using 0 by argo
  thus 1:"ln n\<^sub>0 \<ge> exp 5"
    using 0 by (intro iffD2[OF ln_ge_iff]) auto
  moreover have "1 < exp (5::real)"
    by (approximation 5)
  ultimately show 2:"ln n\<^sub>0 > 1"
    by argo
  show "5 \<le> ln (ln n\<^sub>0)"
    using 1 2 by (subst ln_ge_iff) simp
  have "(1::real) < exp (exp 5)"
    by (approximation 5)
  thus "n\<^sub>0 > 1"
    using 0 by argo
qed

lemma \<delta>1_gt_0: "0 < \<delta>\<^sub>i"
  using n_lbound(4) \<delta>_gt_0 unfolding \<delta>\<^sub>i_def
  by (cases "stage_two") simp_all

lemma \<delta>1_lt_1: "\<delta>\<^sub>i < 1"
  using n_lbound(4) \<delta>_lt_1 unfolding \<delta>\<^sub>i_def
  by (cases "stage_two") simp_all

lemma m_gt_0_aux:
  assumes "stage_two"
  shows "1 \<le> ln (1 / \<delta>) / ln (ln n\<^sub>0)"
proof -
  have "ln n\<^sub>0 \<le> 1 / \<delta>"
    using n_lbound(4)
    using assms unfolding pos_le_divide_eq[OF \<delta>_gt_0] stage_two_def
    by (simp add:divide_simps ac_simps)
  hence "ln (ln n\<^sub>0) \<le> ln (1 / \<delta>)"
    using n_lbound(4) \<delta>_gt_0 by (intro iffD2[OF ln_le_cancel_iff] divide_pos_pos) auto
  thus "1 \<le> ln (1 / \<delta>) / ln (ln n\<^sub>0)"
    using n_lbound(3)
    by (subst pos_le_divide_eq) auto
qed

lemma m_gt_0: "m > 0"
proof (cases "stage_two")
  case True
  have "0 < 4 * ln (1/ \<delta>)/ln(ln n\<^sub>0)"
    using m_gt_0_aux[OF True] by simp
  also have "... \<le> m"
    using m_lbound[OF True] by simp
  finally have "0 < real m"
    by simp
  then show ?thesis by simp
next
  case False
  then show ?thesis unfolding m_def by simp
qed

lemma \<alpha>_gt_0: "\<alpha> > 0"
  using n_lbound(4) unfolding \<alpha>_def
  by (cases "stage_two") auto

lemma \<alpha>_le_1: "\<alpha> \<le> 1"
  using n_lbound(4) unfolding \<alpha>_def
  by (cases "stage_two") simp_all

sublocale I: inner_algorithm "n" "\<delta>\<^sub>i" "\<epsilon>"
  unfolding inner_algorithm_def using n_gt_0 \<epsilon>_gt_0 \<epsilon>_lt_1 \<delta>1_gt_0 \<delta>1_lt_1 by auto

abbreviation \<Theta> where "\<Theta> \<equiv> \<E> m \<alpha> I.\<Omega>"

sublocale \<Theta>: expander_sample_space m \<alpha> I.\<Omega>
  unfolding expander_sample_space_def using I.\<Omega>.sample_space \<alpha>_gt_0 m_gt_0 by auto

type_synonym state = "inner_algorithm.state list"

fun single :: "nat \<Rightarrow> nat \<Rightarrow> state" where
  "single \<theta> x = map (\<lambda>j. I.single (select \<Theta> \<theta> j) x) [0..<m]"

fun merge :: "state \<Rightarrow> state \<Rightarrow> state" where
  "merge x y = map (\<lambda>(x,y). I.merge x y) (zip x y)"

fun estimate :: "state \<Rightarrow> real" where
  "estimate x = median m (\<lambda>i. I.estimate (x ! i))"

definition \<nu> :: "nat \<Rightarrow> nat set \<Rightarrow> state"
  where "\<nu> \<theta> A = map (\<lambda>i. I.\<tau> (select \<Theta> \<theta> i) A) [0..<m]"

text \<open>The following three theorems verify the correctness of the algorithm. The term @{term "\<tau>"}
is a mathematical description of the sketch for a given subset, while @{term "single"},
@{term "merge"} are the actual functions that compute the sketches.\<close>

theorem merge_result: "merge (\<nu> \<omega> A) (\<nu> \<omega> B) = \<nu> \<omega> (A \<union> B)" (is "?L = ?R")
proof -
  have 0: "zip [0..<m] [0..<m] = map (\<lambda>x. (x,x)) [0..<m]" for m
    by (induction m, auto)

  have "?L = map (\<lambda>x. I.merge (I.\<tau> (select \<Theta> \<omega> x) A) (I.\<tau> (select \<Theta> \<omega> x) B)) [0..<m]"
    unfolding \<nu>_def
    by (simp add:zip_map_map 0 comp_def case_prod_beta)
  also have "... = map (\<lambda>x.  I.\<tau> (select \<Theta> \<omega> x) (A \<union> B)) [0..<m]"
    by (intro map_cong I.merge_result \<Theta>.range) auto
  also have "... = ?R"
    unfolding \<nu>_def by simp
  finally show ?thesis by simp
qed

theorem single_result: "single \<omega> x = \<nu> \<omega> {x}" (is "?L = ?R")
proof -
  have "?L = map (\<lambda>j. I.single (select \<Theta> \<omega> j) x) [0..<m]"
    by (simp del:I.single.simps)
  also have "... = ?R"
    unfolding \<nu>_def by (intro map_cong I.single_result \<Theta>.range) auto
  finally show ?thesis by simp
qed

theorem estimate_result:
  assumes "A \<subseteq> {..<n}" "A \<noteq> {}"
  defines "p \<equiv> (pmf_of_set {..<size \<Theta>})"
  shows "measure p {\<omega>. \<bar>estimate (\<nu> \<omega> A)- real (card A)\<bar> > \<epsilon> * real (card A)} \<le> \<delta>" (is "?L \<le> ?R")
proof (cases "stage_two")
  case True
  define I where "I = {x. \<bar>x - real (card A)\<bar> \<le> \<epsilon> * real (card A)}"
  have int_I: "interval I"
    unfolding interval_def I_def by auto

  define \<mu> where "\<mu> = measure I.\<Omega> {\<omega>. I.estimate (I.\<tau> \<omega> A) \<notin> I}"

  have 0:"\<mu> + \<alpha> > 0"
    unfolding \<mu>_def
    by (intro add_nonneg_pos \<alpha>_gt_0) auto

  have "\<mu> \<le> \<delta>\<^sub>i"
    unfolding \<mu>_def I_def using I.estimate_result[OF assms(1,2)]
    by (simp add: not_le del:I.estimate.simps)
  also have "... = 1/ln n\<^sub>0"
    using True unfolding \<delta>\<^sub>i_def by simp
  finally have "\<mu> \<le> 1/ln n\<^sub>0" by simp
  hence "\<mu> + \<alpha> \<le> 1/ln n\<^sub>0 + 1/ln n\<^sub>0"
    unfolding \<alpha>_def using True by (intro add_mono) auto
  also have "... = 2/ln n\<^sub>0"
    by simp
  finally have 1:"\<mu> + \<alpha> \<le> 2 / ln n\<^sub>0"
    by simp
  hence 2:"ln n\<^sub>0 \<le> 2 / (\<mu> + \<alpha>)"
    using 0 n_lbound by (simp add:field_simps)

  have "\<mu> + \<alpha> \<le> 2/ln n\<^sub>0"
    by (intro 1)
  also have "... \<le> 2/exp 5"
    using n_lbound by (intro divide_left_mono) simp_all
  also have "... \<le> 1/2"
    by (approximation 5)
  finally have 3:"\<mu> + \<alpha> \<le> 1/2" by simp

  have 4: "2 * ln 2 + 8 * exp (- 1) \<le> (5::real)"
    by (approximation 5)

  have "?L = measure p {\<omega>. median m (\<lambda>i. I.estimate (\<nu> \<omega> A  ! i)) \<notin> I}"
    unfolding I_def by (simp add:not_le)
  also have "... \<le>
    measure p {\<theta>. real (card {i \<in> {..<m}. I.estimate (I.\<tau> (select \<Theta> \<theta> i) A) \<notin> I})\<ge> real m/2}"
  proof (rule pmf_mono)
    fix \<theta> assume "\<theta> \<in> set_pmf p"
    assume a:"\<theta> \<in> {\<omega>. median m (\<lambda>i. I.estimate (\<nu> \<omega> A ! i)) \<notin> I}"
    have "real m = 2 * real m - real m"
      by simp
    also have "... \<le> 2 * real m - 2 * card {i. i < m \<and> I.estimate (\<nu> \<theta> A ! i) \<in> I}"
      using median_est[OF int_I, where n="m"] a
      by (intro diff_left_mono Nat.of_nat_mono)
       (auto simp add:not_less[symmetric] simp del:I.estimate.simps)
    also have "... = 2 * (real (card {..<m}) - card {i. i < m \<and> I.estimate (\<nu> \<theta> A ! i) \<in> I})"
      by (simp del:I.estimate.simps)
    also have "... = 2 * real (card {..<m} - card {i. i < m \<and> I.estimate (\<nu> \<theta> A ! i) \<in> I})"
      by (intro_cong "[\<sigma>\<^sub>2 (*)]" more:of_nat_diff[symmetric] card_mono)
        (auto simp del:I.estimate.simps)
    also have "... = 2 * real (card ({..<m} - {i. i < m \<and> I.estimate (\<nu> \<theta> A ! i) \<in> I}))"
      by (intro_cong "[\<sigma>\<^sub>2 (*), \<sigma>\<^sub>1 of_nat]" more:card_Diff_subset[symmetric])
        (auto simp del:I.estimate.simps)
    also have "... = 2 * real (card {i\<in>{..<m}. I.estimate (\<nu> \<theta> A ! i) \<notin> I})"
      by (intro_cong "[\<sigma>\<^sub>2 (*), \<sigma>\<^sub>1 of_nat, \<sigma>\<^sub>1 card]") (auto simp del:I.estimate.simps)
    also have "... = 2 * real (card {i \<in> {..<m}. I.estimate (I.\<tau> (select \<Theta> \<theta> i) A) \<notin> I})"
      unfolding \<nu>_def by (intro_cong "[\<sigma>\<^sub>2 (*), \<sigma>\<^sub>1 of_nat, \<sigma>\<^sub>1 card]" more:restr_Collect_cong)
       (simp del:I.estimate.simps)
    finally have "real m \<le> 2 * real (card {i \<in> {..<m}. I.estimate (I.\<tau> (select \<Theta> \<theta> i) A) \<notin> I})"
      by simp
    thus "\<theta> \<in> {\<theta>. real m / 2 \<le> real (card {i \<in> {..<m}. I.estimate (I.\<tau> (select \<Theta> \<theta> i) A) \<notin> I})}"
      by simp
  qed
  also have "...=measure \<Theta>{\<theta>. real(card {i \<in> {..<m}. I.estimate (I.\<tau> (\<theta> i) A) \<notin> I})\<ge>(1/2)*real m}"
    unfolding sample_pmf_alt[OF \<Theta>.sample_space] p_def by (simp del:I.estimate.simps)
  also have "... \<le> exp (-real m * ((1/2) * ln (1/ (\<mu> + \<alpha>)) - 2*exp (-1)))"
    using 3 m_gt_0 \<alpha>_gt_0 unfolding \<mu>_def by (intro \<Theta>.tail_bound) force+
  also have "... \<le> exp (-real m * ((1/2) * ln (ln n\<^sub>0 / 2) - 2*exp (-1)))"
    using 0 2 3 n_lbound
    by (intro iffD2[OF exp_le_cancel_iff] mult_right_mono mult_left_mono_neg[where c="-real m"]
        diff_mono mult_left_mono iffD2[OF ln_le_cancel_iff]) (simp_all)
  also have "... = exp (-real m * (ln (ln n\<^sub>0) / 2 - (ln 2/2 + 2*exp (-1))))"
    using n_lbound by (subst ln_div) (simp_all add:algebra_simps)
  also have "... \<le> exp (-real m * (ln (ln n\<^sub>0) / 2 - (ln (ln (exp(exp 5))) / 4)))"
    using 4
    by (intro iffD2[OF exp_le_cancel_iff] mult_left_mono_neg[where c="-real m"] diff_mono) simp_all
  also have "... \<le> exp (-real m * (ln (ln n\<^sub>0) / 2 - (ln (ln n\<^sub>0) / 4)))"
    using n_lbound
    by (intro iffD2[OF exp_le_cancel_iff] mult_left_mono_neg[where c="-real m"] diff_mono) simp_all
  also have "... = exp (- real m * (ln (ln n\<^sub>0)/ 4) )"
    by (simp add:algebra_simps)
  also have "... \<le> exp (- (4 * ln (1/ \<delta>)/ln(ln n\<^sub>0)) * (ln (ln n\<^sub>0)/4))"
    using m_lbound[OF True] n_lbound
    by (intro iffD2[OF exp_le_cancel_iff] mult_right_mono divide_nonneg_pos) simp_all
  also have "... = exp (- ln (1/ \<delta>))"
    using n_lbound by simp
  also have "... = \<delta>"
    using \<delta>_gt_0 by (subst ln_inverse[symmetric]) auto
  finally show ?thesis by simp
next
  case False
  have m_eq: "m = 1"
    unfolding m_def using False by simp
  hence "?L = measure p {\<omega>. \<epsilon> * real (card A) < \<bar>I.estimate (\<nu> \<omega> A ! 0) - real (card A)\<bar>}"
    unfolding estimate.simps m_eq median_def by simp
  also have "... =  measure p {\<omega>. \<epsilon>*real(card A)<\<bar>I.estimate (I.\<tau> (select \<Theta> \<omega> 0) A)-real(card A)\<bar>}"
    unfolding \<nu>_def m_eq by (simp del: I.estimate.simps)
  also have "... = measure \<Theta> {\<omega>. \<epsilon>*real(card A) < \<bar>I.estimate (I.\<tau> (\<omega> 0) A)-real(card A)\<bar>}"
    unfolding sample_pmf_alt[OF \<Theta>.sample_space] p_def by (simp del:I.estimate.simps)
  also have "...=
    measure (map_pmf (\<lambda>\<theta>. \<theta> 0) \<Theta>) {\<omega>. \<epsilon>*real(card A) < \<bar>I.estimate (I.\<tau> \<omega> A)-real(card A)\<bar>}"
    by simp
  also have "... = measure I.\<Omega> {\<omega>. \<epsilon>*real(card A) < \<bar>I.estimate (I.\<tau> \<omega> A)-real(card A)\<bar>}"
    using m_eq by (subst \<Theta>.uniform_property) auto
  also have "... \<le> \<delta>\<^sub>i"
    by (intro I.estimate_result[OF assms(1,2)])
  also have "... = ?R"
    unfolding \<delta>\<^sub>i_def using False by simp
  finally show ?thesis
    by simp
qed

text \<open>The function @{term "encode_state"} can represent states as bit strings.
This enables verification of the space usage.\<close>

definition encode_state
  where "encode_state = Lf\<^sub>e I.encode_state m"

lemma encode_state: "is_encoding encode_state"
  unfolding encode_state_def
  by (intro fixed_list_encoding I.encode_state)

lemma state_bit_count:
  "bit_count (encode_state (\<nu> \<omega> A)) \<le> state_space_usage (real n, \<epsilon>, \<delta>)"
    (is "?L \<le> ?R")
proof -
  have 0: "length (\<nu> \<omega> A) = m"
    unfolding \<nu>_def by simp
  have "?L = (\<Sum>x\<leftarrow>\<nu> \<omega> A. bit_count (I.encode_state x))"
    using 0 unfolding encode_state_def fixed_list_bit_count by simp
  also have "... = (\<Sum>x\<leftarrow>[0..<m]. bit_count (I.encode_state (I.\<tau> (select \<Theta> \<omega> x) A)))"
    unfolding \<nu>_def by (simp add:comp_def)
  also have "... \<le> (\<Sum>x\<leftarrow>[0..<m]. ereal (2^36 *(ln (1/\<delta>\<^sub>i)+ 1)/\<epsilon>\<^sup>2 + log 2 (log 2 (real n) + 3)))"
    using I.state_bit_count by (intro sum_list_mono I.state_bit_count \<Theta>.range)
  also have "... = ereal ( real m * (2^36 *(ln (1/\<delta>\<^sub>i)+ 1)/\<epsilon>\<^sup>2 + log 2 (log 2 (real n) + 3)))"
    unfolding sum_list_triv_ereal by simp
  also have "... \<le> 2^40 * (ln(1/\<delta>)+1)/ \<epsilon>^2 + log 2 (log 2 n + 3)" (is "?L1 \<le> ?R1")
  proof (cases "stage_two")
    case True
    have "\<lceil>4*ln (1/\<delta>)/ln(ln n\<^sub>0)\<rceil> \<le> 4*ln (1/\<delta>)/ln(ln n\<^sub>0) + 1"
      by simp
    also have "... \<le> 4*ln (1/\<delta>)/ln(ln n\<^sub>0) + ln (1/\<delta>)/ln(ln n\<^sub>0)"
      using m_gt_0_aux[OF True] by (intro add_mono) auto
    also have "... = 5 * ln (1/\<delta>)/ln(ln n\<^sub>0)" by simp
    finally have 3: "\<lceil>4*ln (1/\<delta>)/ln(ln n\<^sub>0)\<rceil> \<le> 5 * ln (1/\<delta>)/ln(ln n\<^sub>0)"
      by simp

    have 4: "0 \<le> log 2 (log 2 (real n) + 3)"
      using n_gt_0
      by (intro iffD2[OF zero_le_log_cancel_iff] add_nonneg_pos) auto

    have 5: "1 / ln 2 + 3 / exp 5 \<le> exp (1::real)"  "1.2 / ln 2 \<le> (2::real)"
      by (approximation 5)+

    have "log 2(log 2 (real n)+3) \<le> log 2 (log 2 n\<^sub>0 + 3)"
      using n_gt_0 by (intro iffD2[OF log_le_cancel_iff] add_mono add_nonneg_pos
          iffD2[OF zero_le_log_cancel_iff]) (simp_all add:n\<^sub>0_def)
    also have "... = ln (ln n\<^sub>0 / ln 2 + 3) / ln 2"
      unfolding log_def by simp
    also have "... \<le> ln (ln n\<^sub>0/ln 2 + (3 / exp 5) * ln n\<^sub>0) / ln 2"
      using n_lbound by (intro divide_right_mono iffD2[OF ln_le_cancel_iff] add_mono add_nonneg_pos)
       (simp_all add:divide_simps)
    also have "... = ln ( ln n\<^sub>0 * (1 /ln 2 + 3/exp 5)) / ln 2"
      by (simp add:algebra_simps)
    also have "... \<le> ln ( ln n\<^sub>0 * exp 1) / ln 2"
      using n_lbound by (intro divide_right_mono iffD2[OF ln_le_cancel_iff] add_mono
          mult_left_mono 5 Rings.mult_pos_pos add_pos_nonneg) auto
    also have "... = (ln (ln n\<^sub>0) + 1) / ln 2"
      using n_lbound by (subst ln_mult) simp_all
    also have "... \<le> (ln (ln n\<^sub>0) + 0.2 * ln (ln n\<^sub>0)) / ln 2"
      using n_lbound by (intro divide_right_mono add_mono) auto
    also have "... = (1.2/ ln 2) * ln (ln n\<^sub>0)"
      by simp
    also have "... \<le> 2 * ln (ln n\<^sub>0)"
      using n_lbound by (intro mult_right_mono 5) simp
    finally have "log 2(log 2 (real n)+3) \<le> 2 * ln (ln n\<^sub>0)"
      by simp
    hence 6: "log 2(log 2 (real n)+3)/ln(ln n\<^sub>0) \<le> 2"
      using n_lbound by (subst pos_divide_le_eq) simp_all

    have "?L1 = real(nat \<lceil>4*ln (1/\<delta>)/ln(ln n\<^sub>0)\<rceil>)*(2^36*(ln (ln n\<^sub>0)+1)/\<epsilon>^2+log 2(log 2 (real n)+3))"
      using True unfolding m_def \<delta>\<^sub>i_def by simp
    also have "... = \<lceil>4*ln (1/\<delta>)/ln(ln n\<^sub>0)\<rceil>*(2^36*(ln (ln n\<^sub>0)+1)/\<epsilon>^2+log 2(log 2 (real n)+3))"
      using m_gt_0_aux[OF True] by (subst of_nat_nat) simp_all
    also have "... \<le> (5*ln (1/\<delta>)/ln(ln n\<^sub>0)) *(2^36*(ln (ln n\<^sub>0)+1)/\<epsilon>^2+log 2(log 2 (real n)+3))"
      using n_lbound(3) \<epsilon>_gt_0  4 by (intro ereal_mono mult_right_mono
          add_nonneg_nonneg divide_nonneg_pos mult_nonneg_nonneg 3) simp_all
    also have "... \<le> (5 * ln (1/\<delta>)/ln(ln n\<^sub>0))*((2^36+2^36)*ln (ln n\<^sub>0)/\<epsilon>^2+log 2(log 2 (real n)+3))"
      using n_lbound \<delta>_gt_0 \<delta>_lt_1
      by (intro ereal_mono mult_left_mono add_mono divide_right_mono divide_nonneg_pos) auto
    also have "... = 5*(2^37)* ln (1/\<delta>)/ \<epsilon>^2 + (5*ln (1/\<delta>)) * (log 2(log 2 (real n)+3)/ln(ln n\<^sub>0))"
      using n_lbound by (simp add:algebra_simps)
    also have "... \<le> 5*(2^37)* ln (1/\<delta>)/ \<epsilon>^2 + (5*ln(1/ \<delta>)) * 2"
      using \<delta>_gt_0 \<delta>_lt_1 by (intro add_mono ereal_mono order.refl mult_left_mono 6) auto
    also have "... = 5*(2^37)* ln (1/\<delta>)/ \<epsilon>^2 + 5*2*ln(1/ \<delta>) / 1"
      by simp
    also have "... \<le> 5*(2^37)* ln (1/\<delta>)/ \<epsilon>^2 + 5*2*ln(1/ \<delta>) / \<epsilon>^2"
      using \<epsilon>_gt_0 \<epsilon>_lt_1 \<delta>_gt_0 \<delta>_lt_1
      by (intro add_mono ereal_mono divide_left_mono Rings.mult_pos_pos power_le_one) auto
    also have "... = (5*(2^37+2))* (ln (1/\<delta>)+0)/ \<epsilon>^2 + 0"
      by (simp add:algebra_simps)
    also have "... \<le> 2^40 * (ln (1 / \<delta>)+1) / \<epsilon>^2 +  log 2 (log 2 (real n) + 3)"
      using \<epsilon>_gt_0 \<epsilon>_lt_1 \<delta>_gt_0 \<delta>_lt_1 n_gt_0 by (intro add_mono ereal_mono divide_right_mono
          mult_right_mono iffD2[OF zero_le_log_cancel_iff] add_nonneg_pos) auto
    finally show ?thesis by simp
  next
    case False
    have "?L1 = 2^36 *(ln (1/\<delta>)+ 1)/\<epsilon>\<^sup>2 + log 2 (log 2 (real n) + 3)"
      using False unfolding \<delta>\<^sub>i_def m_def by simp
    also have "... \<le> ?R1"
      using \<epsilon>_gt_0 \<epsilon>_lt_1 \<delta>_gt_0 \<delta>_lt_1
      by (intro ereal_mono add_mono divide_right_mono mult_right_mono add_nonneg_nonneg) auto
    finally show ?thesis by simp
  qed
  finally show ?thesis
    unfolding state_space_usage_def by simp
qed

text \<open>Encoding function for the seeds which are just natural numbers smaller than
@{term "size \<Theta>"}.\<close>

definition encode_seed
  where "encode_seed = Nb\<^sub>e (size \<Theta>)"

lemma encode_seed:
  "is_encoding encode_seed"
  unfolding encode_seed_def by (intro bounded_nat_encoding)

lemma random_bit_count:
  assumes "\<omega> < size \<Theta>"
  shows "bit_count (encode_seed \<omega>) \<le> seed_space_usage (real n, \<epsilon>, \<delta>)"
    (is "?L \<le> ?R")
proof -
  have 0: "size \<Theta> > 0"
    using \<Theta>.sample_space unfolding sample_space_def by simp
  have 1: "size I.\<Omega> > 0"
    using I.\<Omega>.sample_space unfolding sample_space_def by simp

  have "(55+60*ln (ln n\<^sub>0))^3 \<le> (180+60*ln (ln n\<^sub>0))^3"
    using n_lbound by (intro power_mono add_mono) auto
  also have "... = 180^3 * (1+ln (ln n\<^sub>0)/real 3)^3"
    unfolding power_mult_distrib[symmetric] by simp
  also have "... \<le> 180^3 * exp (ln (ln n\<^sub>0))"
    using n_lbound by (intro mult_left_mono exp_ge_one_plus_x_over_n_power_n) auto
  also have "... = 180^3 * ln n\<^sub>0"
    using n_lbound by (subst exp_ln) auto
  also have "... \<le> 180^3 * max (ln n) (ln (exp (exp 5)))"
    using n_gt_0 unfolding n\<^sub>0_def by (subst ln_max_swap) auto
  also have "... \<le> 180^3 * (ln n + exp 5)"
    using n_gt_0 unfolding ln_exp by (intro mult_left_mono) auto
  finally have 2:"(55+60*ln (ln n\<^sub>0))^3 \<le> 180^3 * ln n + 180^3*exp 5"
    by simp

  have 3:"(1::real)+180^3*exp 5 \<le> 2^30" "(4::real)/ln 2 + 180^3 \<le> 2^23"
    by (approximation 10)+

  have "?L = ereal (real (floorlog 2 (size \<Theta> - 1)))"
    using assms unfolding encode_seed_def bounded_nat_bit_count by simp
  also have "... \<le> ereal (real (floorlog 2 (size \<Theta>)))"
    by (intro ereal_mono Nat.of_nat_mono floorlog_mono) auto
  also have "... = ereal (1 + of_int \<lfloor>log 2 (real (sample_space.size \<Theta>))\<rfloor>)"
    using 0 unfolding floorlog_def by simp
  also have "... \<le> ereal (1 + log 2 (real (size \<Theta>)))"
    by (intro add_mono ereal_mono) auto
  also have "... = 1 + log 2 (real (size I.\<Omega>) * (2^4) ^ ((m - 1) * nat \<lceil>ln \<alpha> / ln 0.95\<rceil>))"
    unfolding \<Theta>.size by simp
  also have "... = 1 + log 2 (real (size I.\<Omega>) * 2^ (4 * (m - 1) * nat \<lceil>ln \<alpha> / ln 0.95\<rceil>))"
    unfolding power_mult by simp
  also have "... = 1 + log 2 (real (size I.\<Omega>)) + (4*(m-1)* nat\<lceil>ln \<alpha> / ln 0.95\<rceil>)"
    using 1 by (subst log_mult) simp_all
  also have "... \<le> 1+log 2(2 powr (4*log 2 n + 48 * (log 2 (1/\<epsilon>)+16)\<^sup>2+ (55+60*ln (1/\<delta>\<^sub>i))^3))+
    (4*(m-1)* nat\<lceil>ln \<alpha> / ln 0.95\<rceil>)"
    using 1 by (intro ereal_mono add_mono iffD2[OF log_le_cancel_iff] I.random_bit_count) auto
  also have "...=1+4*log 2 n+48*(log 2(1/\<epsilon>)+16)\<^sup>2+(55+60*ln (1/\<delta>\<^sub>i))^3+(4*(m-1)*nat\<lceil>ln \<alpha>/ln 0.95\<rceil>)"
    by (subst log_powr_cancel) auto
  also have "... \<le> 2^30 + 2^23*ln n+48*(log 2(1/\<epsilon>)+16)\<^sup>2 + 336*ln (1/\<delta>)" (is "?L1 \<le> ?R1")
  proof (cases "stage_two")
    case True

    have "-1 < (0::real)" by simp
    also have "... \<le> ln \<alpha> / ln 0.95"
      using \<alpha>_gt_0 \<alpha>_le_1 by (intro divide_nonpos_neg) auto
    finally have 4: "- 1 < ln \<alpha> / ln 0.95" by simp

    have 5: "- 1 / ln 0.95 \<le> (20::real)"
      by (approximation 10)

    have "(4*(m-1)*nat\<lceil>ln \<alpha>/ln 0.95\<rceil>) = 4 * (real m-1) * of_int \<lceil>ln \<alpha>/ln 0.95\<rceil>"
      using 4 m_gt_0 unfolding of_nat_mult by (subst of_nat_nat) auto
    also have "... \<le> 4 * (real m-1) * (ln \<alpha>/ln 0.95 + 1)"
      using m_gt_0 by (intro mult_left_mono) auto
    also have "... = 4 * (real m-1) * (-ln (ln n\<^sub>0)/ln 0.95 + 1)"
      using n_lbound True unfolding \<alpha>_def
      by (subst ln_inverse[symmetric]) (simp_all add:inverse_eq_divide)
    also have "... = 4 * (real m - 1 ) * (ln (ln n\<^sub>0) * (-1/ln 0.95) + 1)"
      by simp
    also have "... \<le> 4 * (real m - 1 ) * (ln (ln n\<^sub>0) * 20 + 1)"
      using n_lbound m_gt_0 by (intro mult_left_mono add_mono 5) auto
    also have "... = 4 * (real (nat \<lceil>4 * ln (1 / \<delta>) / ln (ln n\<^sub>0)\<rceil>)-1) *  (ln (ln n\<^sub>0) * 20 + 1)"
      using True unfolding m_def by simp
    also have "... = 4 * (real_of_int \<lceil>4 * ln (1 / \<delta>) / ln (ln n\<^sub>0)\<rceil>-1) *  (ln (ln n\<^sub>0) * 20 + 1)"
      using m_gt_0_aux[OF True] by (subst of_nat_nat) simp_all
    also have "... \<le> 4 * (4 * ln (1 / \<delta>) / ln (ln n\<^sub>0)) * (ln (ln n\<^sub>0) * 20 + 1)"
      using n_lbound by (intro mult_left_mono mult_right_mono) auto
    also have "... \<le> 4 * (4 * ln (1 / \<delta>) / ln (ln n\<^sub>0)) * (ln (ln n\<^sub>0) * 20 + ln (ln n\<^sub>0))"
      using \<delta>_gt_0 \<delta>_lt_1 n_lbound
      by (intro mult_left_mono mult_right_mono add_mono divide_nonneg_pos Rings.mult_nonneg_nonneg)
       simp_all
    also have "... = 336 * ln (1  / \<delta>)"
      using n_lbound by simp
    finally have 6: "4 * (m-1) * nat \<lceil>ln \<alpha>/ln 0.95\<rceil> \<le> 336 * ln (1/\<delta>)"
      by simp

    have "?L1 =1+4*log 2 n+48*(log 2(1/\<epsilon>)+16)\<^sup>2+(55+60*ln (ln n\<^sub>0))^3+(4*(m-1)*nat\<lceil>ln \<alpha>/ln 0.95\<rceil>)"
      using True unfolding \<delta>\<^sub>i_def by simp
    also have "... \<le> 1+4*log 2 n+48*(log 2(1/\<epsilon>)+16)\<^sup>2+(180^3 * ln n + 180^3*exp 5) + 336 * ln (1/\<delta>)"
      by (intro add_mono 6 2 ereal_mono order.refl)
    also have "... = (1+180^3*exp 5)+ (4/ln 2 + 180^3)*ln n+48*(log 2(1/\<epsilon>)+16)\<^sup>2+ 336 * ln (1/\<delta>)"
      by (simp add:log_def algebra_simps)
    also have "... \<le> 2^30 + 2^23*ln n+48*(log 2(1/\<epsilon>)+16)\<^sup>2+ 336 * ln (1/\<delta>)"
      using n_gt_0 by (intro add_mono ereal_mono 3 order.refl mult_right_mono) auto
    finally show ?thesis by simp
  next
    case False
    hence "1 / \<delta> \<le> ln n\<^sub>0"
      using \<delta>_gt_0 n_lbound
      unfolding stage_two_def not_less by (simp add:divide_simps ac_simps)
    hence 7: "ln (1 / \<delta>) \<le> ln (ln n\<^sub>0)"
      using n_lbound \<delta>_gt_0 \<delta>_lt_1
      by (intro iffD2[OF ln_le_cancel_iff]) auto

    have 8: "0 \<le> 336*ln (1/\<delta>) "
      using \<delta>_gt_0 \<delta>_lt_1 by auto

    have "?L1 = 1 + 4 * log 2 (real n) + 48 * (log 2 (1 / \<epsilon>) + 16)\<^sup>2 + (55 + 60 * ln (1 / \<delta>)) ^ 3"
      using False unfolding \<delta>\<^sub>i_def m_def by simp
    also have "... \<le> 1 + 4 * log 2 (real n) + 48 * (log 2 (1 / \<epsilon>) + 16)\<^sup>2 + (55 + 60 * ln (ln n\<^sub>0))^3"
      using \<delta>_gt_0 \<delta>_lt_1
      by (intro add_mono order.refl ereal_mono power_mono mult_left_mono add_nonneg_nonneg 7) auto
    also have "... \<le> 1+4*log 2(real n)+48*(log 2 (1 / \<epsilon>)+16)\<^sup>2+(180^3*ln (real n) + 180 ^ 3 * exp 5)"
      by (intro add_mono ereal_mono 2 order.refl)
    also have "... = (1+180^3*exp 5)+ (4/ln 2 + 180^3)*ln n+48*(log 2(1/\<epsilon>)+16)\<^sup>2+ 0"
      by (simp add:log_def algebra_simps)
    also have "... \<le> 2^30 + 2^23*ln n+48*(log 2(1/\<epsilon>)+16)\<^sup>2 + 336*ln (1/\<delta>)"
      using n_gt_0 by (intro add_mono ereal_mono 3 order.refl mult_right_mono 8) auto
    finally show ?thesis by simp
  qed
  also have "... = seed_space_usage (real n, \<epsilon>, \<delta>)"
    unfolding seed_space_usage_def by simp
  finally show ?thesis by simp
qed

text \<open>The following is an alternative form expressing the correctness and space usage theorems.
If @{term "x"} is expression formed by @{term "single"} and @{term "merge"} operations. Then
@{term "x"} requires @{term "state_space_usage (real n, \<epsilon>, \<delta>)"} bits to encode and
@{term "estimate x"} approximates the count of the distinct universe elements in the expression.

For example:

@{term "estimate (merge (single \<omega> 1) (merge (single \<omega> 5) (single \<omega> 1)))"} approximates the
cardinality of @{term "{1::nat, 5, 1}"} i.e. $2$.\<close>

datatype sketch_tree = Single nat | Merge sketch_tree sketch_tree

fun eval :: "nat \<Rightarrow> sketch_tree \<Rightarrow> state"
  where
    "eval \<omega> (Single x) = single \<omega> x" |
    "eval \<omega> (Merge x y) = merge (eval \<omega> x) (eval \<omega> y)"

fun sketch_tree_set :: "sketch_tree \<Rightarrow> nat set"
  where
    "sketch_tree_set (Single x) = {x}" |
    "sketch_tree_set (Merge x y) = sketch_tree_set x \<union> sketch_tree_set y"

theorem correctness:
  fixes X
  assumes "sketch_tree_set t \<subseteq> {..<n}"
  defines "p \<equiv> pmf_of_set {..<size \<Theta>}"
  defines "X \<equiv> real (card (sketch_tree_set t))"
  shows "measure p {\<omega>. \<bar>estimate (eval \<omega> t) - X\<bar> > \<epsilon> * X} \<le> \<delta>" (is "?L \<le> ?R")
proof -
  define A where "A = sketch_tree_set t"
  have X_eq: "X = real (card A)"
    unfolding X_def A_def by simp

  have 0:"eval \<omega> t = \<nu> \<omega> A" for \<omega>
    unfolding A_def using single_result merge_result
    by (induction t) (auto simp del:merge.simps single.simps)

  have 1: "A \<subseteq> {..<n}"
    using assms(1) unfolding A_def by blast

  have 2: "A \<noteq> {}"
    unfolding A_def by (induction t) auto

  show ?thesis
    unfolding 0 X_eq p_def by (intro estimate_result 1 2)
qed

theorem space_usage:
  assumes "\<omega> < size \<Theta>"
  shows
    "bit_count (encode_state (eval \<omega> t)) \<le> state_space_usage (real n, \<epsilon>, \<delta>)" (is "?A")
    "bit_count (encode_seed \<omega>) \<le> seed_space_usage (real n, \<epsilon>, \<delta>)" (is "?B")
proof-
  define A where "A = sketch_tree_set t"

  have 0:"eval \<omega> t = \<nu> \<omega> A" for \<omega>
    unfolding A_def using single_result merge_result
    by (induction t) (auto simp del:merge.simps single.simps)

  show ?A
    unfolding 0 by (intro state_bit_count)
  show ?B
    using random_bit_count[OF assms] by simp
qed

end

text \<open>The functions @{term "state_space_usage"} and @{term "seed_space_usage"} are exact bounds
on the space usage for the state and the seed. The following establishes asymptotic bounds
with respect to the limit $n, \delta^{-1}, \varepsilon^{-1} \rightarrow \infty$.\<close>

context
begin

text \<open>Some local notation to ease proofs about the asymptotic space usage of the algorithm:\<close>

private definition n_of :: "real \<times> real \<times> real \<Rightarrow> real" where "n_of = (\<lambda>(n, \<epsilon>, \<delta>). n)"
private definition \<delta>_of :: "real \<times> real \<times> real \<Rightarrow> real" where "\<delta>_of = (\<lambda>(n, \<epsilon>, \<delta>). \<delta>)"
private definition \<epsilon>_of :: "real \<times> real \<times> real \<Rightarrow> real" where "\<epsilon>_of = (\<lambda>(n, \<epsilon>, \<delta>). \<epsilon>)"

private abbreviation F :: "(real \<times> real \<times> real) filter"
  where "F \<equiv> (at_top \<times>\<^sub>F at_right 0 \<times>\<^sub>F at_right 0)"

private lemma var_simps:
  "n_of = fst"
  "\<epsilon>_of = (\<lambda>x. fst (snd x))"
  "\<delta>_of = (\<lambda>x. snd (snd x))"
  unfolding n_of_def \<epsilon>_of_def \<delta>_of_def by (auto simp add:case_prod_beta)

private lemma evt_n: "eventually (\<lambda>x. n_of x \<ge> n) F"
  unfolding var_simps by (intro eventually_prod1' eventually_prod2' eventually_ge_at_top)
      (simp add:prod_filter_eq_bot)

private lemma evt_n_1: "\<forall>\<^sub>F x in F. 0 \<le> ln (n_of x)"
  by (intro eventually_mono[OF evt_n[of "1"]] ln_ge_zero) simp

private lemma evt_n_2: "\<forall>\<^sub>F x in F. 0 \<le> ln (ln (n_of x))"
  using order_less_le_trans[OF exp_gt_zero]
  by (intro eventually_mono[OF evt_n[of "exp 1"]] ln_ge_zero iffD2[OF ln_ge_iff]) auto

private lemma evt_\<epsilon>: "eventually (\<lambda>x. 1/\<epsilon>_of x \<ge> \<epsilon> \<and> \<epsilon>_of x > 0) F"
  unfolding var_simps by (intro eventually_prod1' eventually_prod2' eventually_conj
      real_inv_at_right_0_inf eventually_at_right_less) (simp_all add:prod_filter_eq_bot)

private lemma evt_\<delta>: "eventually (\<lambda>x. 1/\<delta>_of x \<ge> \<delta> \<and> \<delta>_of x > 0) F"
  unfolding var_simps by (intro eventually_prod1' eventually_prod2' eventually_conj
      real_inv_at_right_0_inf eventually_at_right_less) (simp_all add:prod_filter_eq_bot)

private lemma evt_\<delta>_1: "\<forall>\<^sub>F x in F. 0 \<le> ln (1 / \<delta>_of x)"
  by (intro eventually_mono[OF evt_\<delta>[of "1"]] ln_ge_zero) simp

theorem asymptotic_state_space_complexity:
  "state_space_usage \<in> O[F](\<lambda>(n, \<epsilon>, \<delta>). ln (1/\<delta>)/\<epsilon>^2 + ln (ln n))"
  (is "_ \<in> O[?F](?rhs)")
proof -
  have 0:"(\<lambda>x. 1) \<in> O[?F](\<lambda>x. ln (1 / \<delta>_of x))"
    using order_less_le_trans[OF exp_gt_zero]
    by (intro landau_o.big_mono eventually_mono[OF evt_\<delta>[of "exp 1"]])
      (auto intro!: iffD2[OF ln_ge_iff] simp add:abs_ge_iff)

  have 1:"(\<lambda>x. 1) \<in> O[?F](\<lambda>x. ln (n_of x))"
    using order_less_le_trans[OF exp_gt_zero]
    by (intro landau_o.big_mono eventually_mono[OF evt_n[of "exp 1"]])
      (auto intro!:iffD2[OF ln_ge_iff] simp add:abs_ge_iff)

  have "(\<lambda>x. ((ln (1/\<delta>_of x)+1)* (1/\<epsilon>_of x)\<^sup>2))\<in> O[?F](\<lambda>x. ln(1/\<delta>_of x)* (1/\<epsilon>_of x)\<^sup>2)"
    by (intro landau_o.mult sum_in_bigo 0) simp_all
  hence 2: "(\<lambda>x. 2^40*((ln (1/\<delta>_of x)+1)* (1/\<epsilon>_of x)\<^sup>2))\<in> O[?F](\<lambda>x. ln(1/\<delta>_of x)* (1/\<epsilon>_of x)\<^sup>2)"
    unfolding cmult_in_bigo_iff by simp

  have 3: "(1::real) \<le> exp 2"
    by (approximation 5)

  have "(\<lambda>x. ln (n_of x) / ln 2 + 3) \<in> O[?F](\<lambda>x. ln (n_of x))"
    using 1 by (intro sum_in_bigo) simp_all
  hence "(\<lambda>x. ln (ln (n_of x) / ln 2 + 3)) \<in> O[?F](\<lambda>x. ln (ln (n_of x)))"
    using order_less_le_trans[OF exp_gt_zero] order_trans[OF 3]
    by (intro landau_ln_2[where a="2"] eventually_mono[OF evt_n[of "exp 2"]])
     (auto intro!:iffD2[OF ln_ge_iff] add_nonneg_nonneg divide_nonneg_pos)
  hence 4: "(\<lambda>x. log 2 (log 2 (n_of x) + 3))\<in> O[?F](\<lambda>x. ln(ln(n_of x)))"
    unfolding log_def by simp

  have 5: "\<forall>\<^sub>F x in ?F. 0 \<le> ln (1 / \<delta>_of x) * (1 / \<epsilon>_of x)\<^sup>2"
    by (intro eventually_mono[OF eventually_conj[OF evt_\<delta>_1 evt_\<epsilon>[of "1"]]]) auto

  have "state_space_usage = (\<lambda>x. state_space_usage (n_of x, \<epsilon>_of x, \<delta>_of x))"
    by (simp add:case_prod_beta' n_of_def \<delta>_of_def \<epsilon>_of_def)
  also have "... = (\<lambda>x. 2 ^ 40 * ((ln (1 / (\<delta>_of x)) + 1)* (1/\<epsilon>_of x)\<^sup>2) + log 2 (log 2 (n_of x)+3))"
    unfolding state_space_usage_def by (simp add:divide_simps)
  also have "... \<in> O[?F](\<lambda>x. ln (1/\<delta>_of x)* (1/\<epsilon>_of x)\<^sup>2 + ln (ln (n_of x)))"
    by (intro landau_sum 2 4 5 evt_n_2)
  also have "... = O[?F](?rhs)"
    by (simp add:case_prod_beta' n_of_def \<delta>_of_def \<epsilon>_of_def divide_simps)
  finally show ?thesis by simp
qed

theorem asymptotic_seed_space_complexity:
  "seed_space_usage \<in> O[F](\<lambda>(n, \<epsilon>, \<delta>). ln (1/\<delta>)+ln (1/\<epsilon>)^2 + ln n)"
  (is "_ \<in> O[?F](?rhs)")
proof -
  have 0: "\<forall>\<^sub>F x in ?F. 0 \<le> (ln (1 / \<epsilon>_of x))\<^sup>2"
    by simp

  have 1: "\<forall>\<^sub>F x in ?F. 0 \<le> ln (1 / \<delta>_of x) + (ln (1 / \<epsilon>_of x))\<^sup>2"
    by (intro eventually_mono[OF eventually_conj[OF evt_\<delta>_1 0]] add_nonneg_nonneg) auto

  have 2: "(\<lambda>x. 1) \<in> O[?F](\<lambda>x. ln (1 / \<epsilon>_of x))"
    using order_less_le_trans[OF exp_gt_zero]
    by (intro landau_o.big_mono eventually_mono[OF evt_\<epsilon>[of "exp 1"]])
      (auto intro!:iffD2[OF ln_ge_iff] simp add:abs_ge_iff)

  have "(\<lambda>x. 1) \<in> O[at_top \<times>\<^sub>F at_right 0 \<times>\<^sub>F at_right 0](\<lambda>x. ln (n_of x))"
    using order_less_le_trans[OF exp_gt_zero]
    by (intro landau_o.big_mono eventually_mono[OF evt_n[of "exp 1"]])
      (auto intro!:iffD2[OF ln_ge_iff] simp add:abs_ge_iff)
  hence 3: "(\<lambda>x. 1) \<in> O[?F](\<lambda>x. ln (1 / \<delta>_of x) + (ln (1 / \<epsilon>_of x))\<^sup>2 + ln (n_of x))"
    by (intro landau_sum_2 1 evt_n_1 0 evt_\<delta>_1) simp
  have 4: "(\<lambda>x. ln (n_of x)) \<in> O[?F](\<lambda>x. ln (1 / \<delta>_of x) + (ln (1 / \<epsilon>_of x))\<^sup>2 + ln (n_of x))"
    by (intro landau_sum_2 1 evt_n_1) simp
  have "(\<lambda>x. log 2 (1 / \<epsilon>_of x) + 16) \<in> O[?F](\<lambda>x. ln (1 / \<epsilon>_of x))"
    using 2 unfolding log_def by (intro sum_in_bigo) simp_all
  hence 5: "(\<lambda>x. (log 2 (1 / \<epsilon>_of x) + 16)\<^sup>2) \<in> O[?F](\<lambda>x. ln (1/\<delta>_of x)+(ln (1/\<epsilon>_of x))\<^sup>2)"
    using 0 unfolding power2_eq_square by (intro landau_sum_2 landau_o.mult evt_\<delta>_1) simp_all
  have 6: "(\<lambda>x. (log 2 (1 / \<epsilon>_of x) + 16)\<^sup>2) \<in> O[?F](\<lambda>x. ln (1/\<delta>_of x)+(ln (1/\<epsilon>_of x))\<^sup>2+ln (n_of x))"
    by (intro landau_sum_1[OF _ _ 5] 1 evt_n_1)
  have 7: "(\<lambda>x. ln (1/\<delta>_of x)) \<in> O[?F](\<lambda>x. ln (1/\<delta>_of x)+(ln (1/\<epsilon>_of x))\<^sup>2+ln (n_of x))"
    by (intro landau_sum_1 1 evt_\<delta>_1 0 evt_n_1) simp

  have "seed_space_usage = (\<lambda>x. seed_space_usage (n_of x, \<epsilon>_of x, \<delta>_of x))"
    by (simp add:case_prod_beta' n_of_def \<delta>_of_def \<epsilon>_of_def)
  also have "... = (\<lambda>x. 2^30+2^23*ln (n_of x)+48*(log 2 (1/(\<epsilon>_of x))+16)\<^sup>2 + 336 * ln (1 / \<delta>_of x))"
    unfolding seed_space_usage_def by (simp add:divide_simps)
  also have "... \<in> O[?F](\<lambda>x. ln (1/\<delta>_of x)+ln (1/\<epsilon>_of x)^2 + ln (n_of x))"
    using 3 4 6 7 by (intro sum_in_bigo) simp_all
  also have "... = O[?F](?rhs)"
    by (simp add:case_prod_beta' n_of_def \<delta>_of_def \<epsilon>_of_def)
  finally show ?thesis by simp
qed

definition "space_usage x = state_space_usage x + seed_space_usage x"

theorem asymptotic_space_complexity:
  "space_usage \<in> O[at_top \<times>\<^sub>F at_right 0 \<times>\<^sub>F at_right 0](\<lambda>(n, \<epsilon>, \<delta>). ln (1/\<delta>)/\<epsilon>^2 + ln n)"
proof -
  let ?f1 = "(\<lambda>x. ln (1/\<delta>_of x)*(1/\<epsilon>_of x^2)+ln (ln (n_of x)))"
  let ?f2 = "(\<lambda>x. ln(1/\<delta>_of x)+ln(1/\<epsilon>_of x)^2+ln (n_of x))"

  have 0: "\<forall>\<^sub>F x in F. 0 \<le> (1 / (\<epsilon>_of x)\<^sup>2)"
    unfolding var_simps by (intro eventually_prod1' eventually_prod2' eventually_inv)
      (simp_all add:prod_filter_eq_bot eventually_nonzero_simps)

  have 1: "\<forall>\<^sub>F x in F. 0 \<le> ln (1 / \<delta>_of x) * (1 / (\<epsilon>_of x)\<^sup>2)"
    by (intro eventually_mono[OF eventually_conj[OF evt_\<delta>_1 0]] mult_nonneg_nonneg) auto

  have 2: "\<forall>\<^sub>F x in F. 0 \<le> ln (1 / \<delta>_of x) * (1 / (\<epsilon>_of x)\<^sup>2) + ln (ln (n_of x))"
    by (intro eventually_mono[OF eventually_conj[OF 1 evt_n_2]] add_nonneg_nonneg) auto

  have 3: "\<forall>\<^sub>F x in F. 0 \<le> ln (1 / (\<epsilon>_of x)\<^sup>2)"
    unfolding power_one_over[symmetric]
    by (intro eventually_mono[OF evt_\<epsilon>[of "1"]] ln_ge_zero) simp

  have 4: "\<forall>\<^sub>F x in F. 0 \<le> ln (1 / \<delta>_of x) + (ln (1 / \<epsilon>_of x))\<^sup>2 + ln (n_of x)"
    by (intro eventually_mono[OF eventually_conj[OF evt_n_1 eventually_conj[OF evt_\<delta>_1 3]]]
        add_nonneg_nonneg) auto

  have 5: "(\<lambda>_. 1) \<in> O[F](\<lambda>x. 1 / (\<epsilon>_of x)\<^sup>2)"
    unfolding var_simps by (intro bigo_prod_1 bigo_prod_2 bigo_inv)
      (simp_all add:power_divide prod_filter_eq_bot)

  have 6: "(\<lambda>_. 1) \<in> O[F](\<lambda>x. ln (1 / \<delta>_of x))"
    unfolding var_simps
    by (intro bigo_prod_1 bigo_prod_2 bigo_inv) (simp_all add:prod_filter_eq_bot)

  have 7: "state_space_usage \<in> O[F](\<lambda>x. ln (1 / \<delta>_of x) * (1 / (\<epsilon>_of x)\<^sup>2) + ln (ln (n_of x)))"
    using asymptotic_state_space_complexity unfolding \<delta>_of_def \<epsilon>_of_def n_of_def
    by (simp add:case_prod_beta')

  have 8: "seed_space_usage \<in> O[F](\<lambda>x. ln (1 / \<delta>_of x) + (ln (1 / \<epsilon>_of x))\<^sup>2 + ln (n_of x))"
    using asymptotic_seed_space_complexity unfolding \<delta>_of_def \<epsilon>_of_def n_of_def
    by (simp add:case_prod_beta')

  have 9: "(\<lambda>x. ln (n_of x)) \<in> O[F](\<lambda>x. ln (1 / \<delta>_of x) * (1 / (\<epsilon>_of x)\<^sup>2) + ln (n_of x))"
    by (intro landau_sum_2 evt_n_1 1) simp

  have "(\<lambda>x. (ln (1 / \<epsilon>_of x))\<^sup>2) \<in> O[F](\<lambda>x. 1 / \<epsilon>_of x^2)"
    unfolding var_simps
    by (intro bigo_prod_1 bigo_prod_2 bigo_inv) (simp_all add:power_divide prod_filter_eq_bot)
  hence 10: "(\<lambda>x. (ln (1 / \<epsilon>_of x))\<^sup>2) \<in> O[F](\<lambda>x. ln (1 / \<delta>_of x) * (1 / \<epsilon>_of x^2) + ln (n_of x))"
    by (intro landau_sum_1 evt_n_1 1 landau_o.big_mult_1' 6)
  have 11: "(\<lambda>x. ln (1 / \<delta>_of x)) \<in> O[F](\<lambda>x. ln (1 / \<delta>_of x) * (1 / \<epsilon>_of x^2) + ln (n_of x))"
    by (intro landau_sum_1 evt_n_1 1 landau_o.big_mult_1 5) simp
  have 12: "(\<lambda>x. ln (1/\<delta>_of x) * (1/\<epsilon>_of x^2)) \<in> O[F](\<lambda>x. ln (1/\<delta>_of x)*(1/\<epsilon>_of x^2)+ln (n_of x))"
    by (intro landau_sum_1 1 evt_n_1) simp

  have "(\<lambda>x. ln (ln (n_of x))) \<in> O[F](\<lambda>x. ln (n_of x))"
    unfolding var_simps by (intro bigo_prod_1 bigo_prod_2) (simp_all add:prod_filter_eq_bot)
  hence 13: "(\<lambda>x. ln (ln (n_of x))) \<in> O[F](\<lambda>x. ln (1 / \<delta>_of x) * (1 / \<epsilon>_of x^2) + ln (n_of x))"
    by (intro landau_sum_2 evt_n_1 1)

  have "space_usage = (\<lambda>x. state_space_usage x + seed_space_usage x)"
    unfolding space_usage_def by simp
  also have "... \<in> O[F](\<lambda>x. ?f1 x + ?f2 x)"
    by (intro landau_sum 2 4 7 8)
  also have "... \<subseteq> O[F](\<lambda>x. ln (1 / \<delta>_of x) * (1/\<epsilon>_of x^2) + ln (n_of x))"
    by (intro landau_o.big.subsetI sum_in_bigo 9 10 11 12 13)
  also have "... = O[F](\<lambda>(n, \<epsilon>, \<delta>). ln (1/\<delta>)/\<epsilon>^2 + ln n)"
    unfolding \<delta>_of_def \<epsilon>_of_def n_of_def
    by (simp add:case_prod_beta')
  finally show ?thesis by simp
qed

end

unbundle no_intro_cong_syntax

end
