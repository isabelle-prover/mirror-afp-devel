section \<open>Cutoff Level\<close>

text \<open>This section verifies that the cutoff will be below @{term "q_max"} with high probability.
The result will be needed in Section~\ref{sec:accuracy}, where it is shown that the estimates
will be accurate for any cutoff below @{term "q_max"}.\<close>

theory Distributed_Distinct_Elements_Cutoff_Level
  imports
    Distributed_Distinct_Elements_Accuracy_Without_Cutoff
    Distributed_Distinct_Elements_Tail_Bounds
begin

hide_const Quantum.Z

unbundle intro_cong_syntax

lemma mono_real_of_int: "mono real_of_int"
  unfolding mono_def by auto

lemma Max_le_Sum:
  fixes f :: "'a \<Rightarrow> int"
  assumes "finite A"
  assumes "\<And>a. a \<in> A \<Longrightarrow> f a \<ge> 0"
  shows "Max (insert 0 (f ` A)) \<le> (\<Sum>a \<in>A .f a)" (is "?L \<le> ?R")
proof (cases "A\<noteq>{}")
  case True

  have 0: "f a \<le> (\<Sum>a \<in>A .f a)" if "a \<in> A" for a
    using that assms by (intro member_le_sum) auto

  have "?L = max 0 (Max (f ` A))"
    using True assms(1) by (subst Max_insert) auto
  also have "... = Max (max 0 ` f ` A)"
    using assms True by (intro mono_Max_commute monoI) auto
  also have "... = Max (f ` A)"
    unfolding image_image using assms
    by (intro arg_cong[where f="Max"] image_cong) auto
  also have "... \<le> ?R"
    using 0 True assms(1)
    by (intro iffD2[OF Max_le_iff]) auto
  finally show ?thesis by simp
next
  case False
  hence "A = {}" by simp
  then show ?thesis by simp
qed

context inner_algorithm_fix_A
begin

text \<open>The following inequality is true for base e on the entire domain ($x > 0$). It is
shown in @{thm [source] ln_add_one_self_le_self}. In the following it is established for base
$2$, where it holds for $x \geq 1$.\<close>

lemma log_2_estimate:
  assumes "x \<ge> (1::real)"
  shows "log 2 (1+x) \<le> x"
proof -
  define f where "f x = x - log 2 (1+ x)" for x :: real
  define f' where "f' x = 1 - 1/((x+1)*ln 2)" for x :: real

  have 0:"(f has_real_derivative (f' x)) (at x)" if "x > 0" for x
    unfolding f_def f'_def using that
    by (auto intro!: derivative_eq_intros)

  have "f' x \<ge> 0" if "1 \<le> x" for x :: real
  proof -
    have "(1::real) \<le> 2*ln 2"
      by (approximation 5)
    also have "... \<le> (x+1)*ln 2"
      using that by (intro mult_right_mono) auto
    finally have "1 \<le> (x+1)*ln 2" by simp
    hence "1/((x+1)*ln 2) \<le> 1"
      by simp
    thus ?thesis
      unfolding f'_def by simp
  qed

  hence "\<exists>y. (f has_real_derivative y) (at x) \<and> 0 \<le> y" if "x \<ge> 1" for x :: real
    using that order_less_le_trans[OF exp_gt_zero]
    by (intro exI[where x="f' x"] conjI 0) auto
  hence "f 1 \<le> f x"
    by (intro DERIV_nonneg_imp_nondecreasing[OF assms]) auto
  thus "?thesis"
    unfolding f_def by simp
qed

lemma cutoff_eq_7:
  "real X * 2 powr (-real q_max) / b \<le> 1"
proof -
  have "real X = 2 powr (log 2 X)"
    using X_ge_1 by (intro powr_log_cancel[symmetric]) auto
  also have "... \<le> 2 powr (nat \<lceil>log 2 X\<rceil>)"
    by (intro powr_mono) linarith+
  also have "... = 2 ^ (nat \<lceil>log 2 X\<rceil>)"
    by (subst powr_realpow) auto
  also have "... = real (2 ^ (nat \<lceil>log 2 (real X)\<rceil>))"
    by simp
  also have "... \<le> real (2 ^ (b_exp + nat (\<lceil>log 2 (real X)\<rceil> - int b_exp)))"
    by (intro Nat.of_nat_mono power_increasing) linarith+
  also have "... = b * 2^q_max"
    unfolding q_max_def b_def by (simp add: power_add)

  finally have "real X \<le> b * 2 ^ q_max" by simp
  thus ?thesis
    using b_min
    unfolding powr_minus inverse_eq_divide
    by (simp add:field_simps powr_realpow)
qed

lemma cutoff_eq_6:
  fixes k
  assumes "a \<in> A"
  shows " (\<integral>f. real_of_int (max 0 (int (f a) - int k)) \<partial>\<Psi>\<^sub>1) \<le> 2 powr (-real k)" (is "?L \<le> ?R")
proof (cases "k \<le> n_exp - 1")
  case True
  have a_le_n: "a < n"
    using assms A_range by auto

  have "?L = (\<integral>x. real_of_int (max 0 (int x - k)) \<partial>map_pmf (\<lambda>x. x a) \<Psi>\<^sub>1)"
    by simp
  also have "... = (\<integral>x. real_of_int (max 0 (int x - k)) \<partial>(\<G> n_exp))"
    unfolding \<Psi>\<^sub>1.single[OF a_le_n] by simp
  also have "... = (\<integral>x. max 0 (real x - real k) \<partial>(\<G> n_exp))"
    unfolding max_of_mono[OF mono_real_of_int,symmetric] by simp
  also have "... = (\<Sum>x\<le>n_exp.  max 0 (real x - real k) * pmf (\<G> n_exp) x)"
    using \<G>_range unfolding sample_space_alt[OF \<G>_sample_space]
    by (intro integral_measure_pmf_real) auto
  also have "... = (\<Sum>x=k+1..n_exp. (real x - real k) * pmf (\<G> n_exp) x)"
    by (intro sum.mono_neutral_cong_right) auto
  also have "... = (\<Sum>x=k+1..n_exp. (real x - real k) * measure (\<G> n_exp) {x})"
    unfolding measure_pmf_single by simp
  also have "... = (\<Sum>x=k+1..n_exp. (real x-real k)*(measure (\<G> n_exp) ({\<omega>. \<omega>\<ge>x}-{\<omega>. \<omega>\<ge>(x+1)})))"
    by (intro sum.cong arg_cong2[where f="(*)"] measure_pmf_cong) auto
  also have "... = (\<Sum>x=k+1..n_exp. (real x-real k)*
    (measure (\<G> n_exp) {\<omega>. \<omega>\<ge>x} - measure (\<G> n_exp) {\<omega>. \<omega>\<ge>(x+1)}))"
    by (intro sum.cong arg_cong2[where f="(*)"] measure_Diff) auto
  also have "... = (\<Sum>x=k+1..n_exp. (real x - real k) * (1/2^x - of_bool(x+1\<le>n_exp)/2^(x+1)))"
    unfolding \<G>_prob by (intro_cong "[\<sigma>\<^sub>2 (*), \<sigma>\<^sub>2 (-), \<sigma>\<^sub>2 (/)]" more:sum.cong) auto
  also have "... =
    (\<Sum>x=k+1..n_exp. (real x-k)/2^x) - (\<Sum>x=k+1..n_exp. (real x-k)* of_bool(x+1\<le>n_exp)/2^(x+1))"
    by (simp add:algebra_simps sum_subtractf)
  also have "...=(\<Sum>x=k+1..n_exp. (real x-k)/2^x)-(\<Sum>x=k+1..n_exp-1. (real x-k)/2^(x+1))"
    by (intro arg_cong2[where f="(-)"] refl sum.mono_neutral_cong_right) auto
  also have "...=(\<Sum>x=k+1..(n_exp-1)+1. (real x-k)/2^x)-(\<Sum>x=k+1..n_exp-1. (real x-k)/2^(x+1))"
    using n_exp_gt_0 by (intro arg_cong2[where f="(-)"] refl sum.cong) auto
  also have "...= (\<Sum>x\<in>insert k {k+1..n_exp-1}. (real (x+1)-k)/2^(x+1))-
    (\<Sum>x=k+1..n_exp-1. (real x-k)/2^(x+1))"
    unfolding sum.shift_bounds_cl_nat_ivl using True
    by (intro arg_cong2[where f="(-)"] sum.cong) auto
  also have "... = 1/2^(k+1)+(\<Sum>x=k+1..n_exp-1. (real (x+1)-k)/2^(x+1)- (real x-k)/2^(x+1))"
    by (subst sum.insert) (auto simp add:sum_subtractf)
  also have "... = 1/2^(k+1)+(\<Sum>x=k+1..n_exp-1. (1/2^(x+1)))"
    by (intro arg_cong2[where f="(+)"] sum.cong refl) (simp add:field_simps)
  also have "... = (\<Sum>x\<in>insert k {k+1..n_exp-1}. (1/2^(x+1)))"
    by (subst sum.insert) auto
  also have "... = (\<Sum>x=0+k..(n_exp-1-k)+k. 1/2^(x+1))"
    using True by (intro sum.cong) auto
  also have "... = (\<Sum>x<n_exp-k. 1/2^(x+k+1))"
    unfolding sum.shift_bounds_cl_nat_ivl using True n_exp_gt_0 by (intro sum.cong) auto
  also have "... = (1/2)^(k+1) * (\<Sum>x<n_exp-k. (1/2)^x)"
    unfolding  sum_distrib_left power_add[symmetric] by (simp add:power_divide ac_simps)
  also have "... = (1/2)^(k+1) * 2 * (1-(1 / 2) ^ (n_exp - k))"
    by (subst geometric_sum) auto
  also have "... \<le> (1/2)^(k+1) * 2 * (1-0)"
    by (intro mult_left_mono diff_mono) auto
  also have "... = (1/2)^k"
    unfolding power_add by simp
  also have "... = ?R"
    unfolding powr_minus by (simp add:powr_realpow inverse_eq_divide power_divide)
  finally show ?thesis
    by simp
next
  case False
  hence k_ge_n_exp: "k \<ge> n_exp"
    by simp
  have a_lt_n: "a < n"
    using assms A_range by auto

  have "?L = (\<integral>x. real_of_int (max 0 (int x - k)) \<partial>map_pmf (\<lambda>x. x a) \<Psi>\<^sub>1)"
    by simp
  also have "... = (\<integral>x. real_of_int (max 0 (int x - k)) \<partial>(\<G> n_exp))"
    unfolding \<Psi>\<^sub>1.single[OF a_lt_n] by simp
  also have "... = (\<integral>x. real_of_int 0 \<partial>(\<G> n_exp))"
    using \<G>_range k_ge_n_exp unfolding sample_space_alt[OF \<G>_sample_space]
    by (intro integral_cong_AE AE_pmfI iffD2[OF of_int_eq_iff] max_absorb1) force+
  also have "... = 0" by simp
  finally show ?thesis by simp
qed

lemma cutoff_eq_5:
  assumes "x \<ge> (-1 :: real)"
  shows "real_of_int \<lfloor>log 2 (x+2)\<rfloor> \<le> (real c+2) + max (x - 2^c) 0" (is "?L \<le> ?R")
proof -
  have 0: "1 \<le> 2 ^ 1 * ln (2::real)"
    by (approximation 5)

  consider (a) "c = 0 \<and> x \<ge> 2^c+1" | (b) "c > 0 \<and> x \<ge> 2^c+1" | (c) "x \<le> 2^c+1"
    by linarith
  hence "log 2 (x+2) \<le> ?R"
  proof (cases)
    case a
    have "log 2 (x+2) = log 2 (1+(x+1))"
      by (simp add:algebra_simps)
    also have "... \<le> x+1"
      using a by (intro log_2_estimate) auto
    also have "... = ?R"
      using a by auto
    finally show ?thesis by simp
  next
    case b
    have "0 < 0 + (1::real)"
      by simp
    also have "... \<le> 2^c+(1::real)"
      by (intro add_mono) auto
    also have "... \<le> x"
      using b by simp
    finally have x_gt_0: "x > 0"
      by simp

    have "log 2 (x+2) = log 2 ((x+2)/2^c) + c"
      using x_gt_0 by (subst log_divide) auto
    also have "... = log 2 (1+(x+2-2^c)/2^c) + c"
      by (simp add:divide_simps)
    also have "... \<le> (x+2-2^c)/2^c / ln 2 + c"
      using b unfolding log_def
      by (intro add_mono divide_right_mono ln_add_one_self_le_self divide_nonneg_pos) auto
    also have "... = (x+2-2^c)/(2^c*ln 2) + c"
      by simp
    also have "... \<le> (x+2-2^c)/(2^1*ln 2)+c"
      using b by (intro add_mono divide_left_mono mult_right_mono power_increasing) simp_all
    also have "... \<le> (x+2-2^c)/1 + c"
      using b by (intro add_mono divide_left_mono 0) auto
    also have "... \<le> (c+2) + max (x - 2^c) 0"
      using b by simp
    finally show ?thesis by simp
  next
    case c
    hence "log 2 (x+2) \<le> log 2 ((2^c+1)+2)"
      using assms by (intro log_mono add_mono) auto
    also have "... = log 2 (2^c*(1+3/2^c))"
      by (simp add:algebra_simps)
    also have "... = c + log 2 (1+3/2^c)"
      by (subst log_mult) (auto intro:add_pos_nonneg)
    also have "... \<le> c + log 2 (1+3/2^0)"
      by (intro add_mono log_mono divide_left_mono power_increasing add_pos_nonneg) auto
    also have "... = c + log 2 (2*2)"
      by simp
    also have "... = real c + 2"
      by (subst log_mult) auto
    also have "... \<le> (c+2) + max (x - 2^c) 0"
      by simp
    finally show ?thesis
      by simp
  qed
  moreover have "\<lfloor>log 2 (x+2)\<rfloor> \<le> log 2 (x+2)"
      by simp
  ultimately show ?thesis using order_trans by blast
qed

lemma cutoff_level:
  "measure \<Omega> {\<omega>. q \<omega> A > q_max} \<le> \<delta>/2" (is "?L \<le> ?R")
proof -
  have C\<^sub>1_est: "C\<^sub>1 * l \<le> 30 * real l"
    unfolding C\<^sub>1_def
    by (intro mult_right_mono of_nat_0_le_iff) (approximation 10)

  define Z where "Z \<omega> = (\<Sum>j<b. real_of_int \<lfloor>log 2 (of_int (max (\<tau>\<^sub>1 \<omega> A q_max j) (-1)) + 2)\<rfloor>)" for \<omega>
  define V where "V \<omega> = Z \<omega> / real b - 3" for \<omega>

  have 2:"Z \<psi> \<le> real b*(real c+2) + of_int (\<Sum>a\<in>A. max 0 (int (fst \<psi> a) - q_max -2^c))"
    (is "?L1 \<le> ?R1") if "\<psi> \<in> sample_set \<Psi>" for c \<psi>
  proof -
    obtain f g h where \<psi>_def: "\<psi> = (f,g,h)"
      using prod_cases3 by blast

    have \<psi>_range: "(f,g,h) \<in> sample_set \<Psi>"
      using that unfolding \<psi>_def by simp

    have "- 1 - 2^c \<le> -1-(1::real)"
      by (intro diff_mono) auto
    also have "... \<le> 0" by simp
    finally have "- 1 - 2 ^ c \<le> (0::real)" by simp
    hence aux3: "max (-1-2^c) 0 = (0::real)"
      by (intro max_absorb2)

    have "- 1 - int q_max - 2 ^ c \<le> -1 - 0 - 1"
      by (intro diff_mono) auto
    also have "... \<le> 0" by simp
    finally have "- 1 - int q_max - 2 ^ c \<le> 0" by simp
    hence aux3_2: "max 0 (- 1 - int q_max - 2 ^ c) = 0"
      by (intro max_absorb1)

    have "?L1 \<le> (\<Sum>j<b. (real c+2) + max (real_of_int (max (\<tau>\<^sub>1 \<psi> A q_max j) (- 1)) - 2^c) 0)"
      unfolding Z_def by (intro sum_mono cutoff_eq_5) auto
    also have "... = (\<Sum>j<b. (real c+2)+max (\<tau>\<^sub>0 \<psi> A j - q_max - 2^c) 0)"
      unfolding \<tau>\<^sub>1_def max_of_mono[OF mono_real_of_int,symmetric]
      by (intro_cong "[\<sigma>\<^sub>2 (+)]" more:sum.cong) (simp add:max_diff_distrib_left max.assoc aux3)
    also have "... = real b * (real c + 2) +
      of_int (\<Sum>j<b. (max 0 (Max (insert (- 1) {int (f a) |a. a \<in> A \<and> h (g a) = j})-q_max - 2^c)))"
      unfolding \<psi>_def by (simp add:max.commute)
    also have "... = real b * (real c + 2) +
      of_int (\<Sum>j<b. max 0 (Max ((\<lambda>x. x-q_max-2^c)`(insert(-1){int (f a) |a. a \<in> A\<and>h(g a)=j}))))"
      using fin_A
      by (intro_cong "[\<sigma>\<^sub>2 (+), \<sigma>\<^sub>1 of_int, \<sigma>\<^sub>2 max]" more:sum.cong mono_Max_commute) (auto simp:monoI)
    also have "... = real b * (real c + 2) +
      of_int(\<Sum>j<b. max 0(Max(insert(-1-q_max-2^c){int (f a)-q_max-2^c |a. a \<in> A \<and> h (g a) = j})))"
      by (intro_cong "[\<sigma>\<^sub>2 (+), \<sigma>\<^sub>1 of_int, \<sigma>\<^sub>2 max, \<sigma>\<^sub>1 Max]" more:sum.cong)  auto
    also have "... = real b * (real c + 2) + of_int
      (\<Sum>j<b. Max ((max 0) `(insert(-1-q_max-2^c){int (f a)-q_max-2^c |a. a \<in> A \<and> h (g a) = j})))"
      using fin_A by (intro_cong "[\<sigma>\<^sub>2 (+), \<sigma>\<^sub>1 of_int]" more:sum.cong mono_Max_commute)
        (auto simp add:monoI setcompr_eq_image)
    also have "... = real b * (real c + 2) +
      of_int (\<Sum>j<b. Max (insert 0 {max 0 (int (f a)-q_max-2^c) |a. a \<in> A \<and> h (g a) = j}))"
      using aux3_2 by (intro_cong "[\<sigma>\<^sub>2 (+), \<sigma>\<^sub>1 of_int, \<sigma>\<^sub>1 Max]" more:sum.cong)
        (simp add:setcompr_eq_image image_image)
    also have "... \<le> b*(real c+2)+ of_int(\<Sum>j<b. (\<Sum>a|a\<in>A\<and>h(g(a))=j. max 0(int(f a)-q_max-2^c)))"
      using fin_A Max_le_Sum unfolding setcompr_eq_image
      by (intro add_mono iffD2[OF of_int_le_iff] sum_mono Max_le_Sum) (simp_all)
    also have "... = real b*(real c+2)+
      of_int(\<Sum>a\<in>(\<Union>j\<in>{..<b}. {a. a\<in>A\<and> h(g(a)) = j}). max 0(int(f a)-q_max-2^c))"
      using fin_A
      by (intro_cong "[\<sigma>\<^sub>2 (+), \<sigma>\<^sub>1 of_int]" more:sum.UNION_disjoint[symmetric]) auto
    also have "... = real b*(real c+2) + of_int(\<Sum>a\<in>A. max 0(int(f a)-q_max-2^c))"
      using h_range[OF \<psi>_range] by (intro_cong "[\<sigma>\<^sub>2 (+), \<sigma>\<^sub>1 of_int]" more:sum.cong) auto
    also have "... = ?R1"
      unfolding \<psi>_def by simp
    finally show ?thesis
      by simp
  qed

  have 1: "measure \<Psi> {\<psi>. real c \<le> V \<psi>} \<le> 2 powr (- (2^c))" (is "?L1 \<le> ?R1") for c
  proof -
    have "?L1 = measure \<Psi> {\<psi>. real b * (real c + 3) \<le> Z \<psi>}"
      unfolding V_def using b_min by (intro measure_pmf_cong) (simp add:field_simps)
    also have "... \<le> measure \<Psi>
      {\<psi>. real b*(real c+3)\<le> real b*(real c+2)+ of_int (\<Sum>a\<in>A. max 0 (int (fst \<psi> a)-q_max -2^c))}"
      using 2 order_trans unfolding sample_space_alt[OF sample_space_\<Psi>]
      by (intro pmf_mono) blast
    also have "... = measure \<Psi> {\<psi>. real b \<le> (\<Sum>a\<in>A. of_int (max 0 (int (fst \<psi> a) -q_max -2^c)))}"
      by (intro measure_pmf_cong) (simp add:algebra_simps)
    also have "... \<le> (\<integral>\<psi>. (\<Sum>a\<in>A. of_int (max 0 (int (fst \<psi> a) -q_max -2^c))) \<partial>\<Psi>)/real b"
      using b_min sample_space_\<Psi> by (intro pmf_markov sum_nonneg) simp_all
    also have "... = (\<Sum>a\<in>A. (\<integral>\<psi>.  of_int (max 0 (int (fst \<psi> a) -q_max -2^c)) \<partial>\<Psi>))/real b"
      using sample_space_\<Psi> by (intro_cong "[\<sigma>\<^sub>2(/)]" more:Bochner_Integration.integral_sum) simp
    also have "... = (\<Sum>a\<in>A. (\<integral>f.  of_int (max 0 (int (f a)-q_max -2^c)) \<partial>(map_pmf fst \<Psi>)))/real b"
      by simp
    also have "... = (\<Sum>a\<in>A. (\<integral>f. of_int (max 0 (int (f a) - (q_max +2^c))) \<partial>\<Psi>\<^sub>1))/real b"
      unfolding sample_pmf_\<Psi> map_fst_pair_pmf by (simp add:algebra_simps)
    also have "... \<le> (\<Sum>a\<in>A. 2 powr -real (q_max + 2^c))/real b"
      using b_min by (intro sum_mono divide_right_mono cutoff_eq_6) auto
    also have "... = real X * 2 powr (- real q_max + (- (2 ^ c))) / real b"
      unfolding X_def by simp
    also have "... = (real X * 2 powr (-real q_max) / b) * 2 powr (-(2^c))"
      unfolding powr_add by (simp add:algebra_simps)
    also have "... \<le> 1 * 2 powr (-(2^c))"
      using cutoff_eq_7 by (intro mult_right_mono) auto
    finally show ?thesis
      by simp
  qed

  have 0: "measure \<Psi> {\<psi>. x \<le> V \<psi>} \<le> exp (- x * ln x ^ 3)"  (is "?L1 \<le> ?R1") if "x \<ge> 20" for x
  proof -
    define c where "c = nat \<lfloor>x\<rfloor>"

    have "x * ln x^3 \<le> exp (x * ln 2) * ln 2/2" if "x \<ge> 150" for x::real
    proof -
      have aux_aux_0: "x^4 \<ge> 0"
        by simp

      have "x * ln x^3 \<le> x * x^3"
        using that by (intro mult_left_mono power_mono ln_bound) auto
      also have "... = x^4 * 1"
        by (simp add:numeral_eq_Suc)
      also have "... \<le> x^4  * ((ln 2 / 10)^4 * (150 * (ln 2 / 10))^6  * (ln 2/2))"
        by (intro mult_left_mono aux_aux_0) (approximation 8)
      also have "... = (x * (ln 2 / 10))^4 * (150 * (ln 2 / 10))^6  * (ln 2/2)"
        unfolding power_mult_distrib by (simp add:algebra_simps)
      also have "... \<le> (x * (ln 2 / 10))^4 * (x * (ln 2 / 10))^6  * (ln 2/2)"
        by (intro mult_right_mono mult_left_mono power_mono that) auto
      also have "... = (0+x * (ln 2 / 10))^10 * (ln 2/2)"
        unfolding power_add[symmetric] by simp
      also have "... \<le> (1+x * ln 2 / 10)^10 * (ln 2/2)"
        using that by (intro mult_right_mono power_mono add_mono) auto
      also have "... \<le> exp (x * ln 2 / 10)^10 * (ln 2/2)"
        using that by (intro mult_right_mono power_mono exp_ge_add_one_self) auto
      also have "... = exp (x * ln 2) * (ln 2/2)"
        unfolding exp_of_nat_mult[symmetric] by simp
      finally show ?thesis by simp
    qed
    moreover have "x * ln x^3 \<le> exp (x * ln 2) * ln 2/2" if "x \<in> {20..150}"
      using that by (approximation 10 splitting: x=1)

    ultimately have "x * ln x^3 \<le> exp (x * ln 2) * ln 2/2"
      using that by fastforce
    also have "... = 2 powr (x-1) * ln 2"
      unfolding powr_diff unfolding powr_def by simp
    also have "... \<le> 2 powr c * ln 2"
      unfolding c_def using that
      by (intro mult_right_mono powr_mono) auto
    also have "... = 2^c * ln 2"
      using powr_realpow by simp
    finally have aux0: "x * ln x^3 \<le> 2^c * ln 2"
      by simp
    have "real c \<le> x"
      using that unfolding c_def by linarith
    hence "?L1 \<le> measure \<Psi> {\<psi>. real c \<le> V \<psi>}"
      by (intro pmf_mono) auto
    also have "... \<le> 2 powr (-(2^c))"
      by (intro 1)
    also have "... = exp (- (2 ^ c * ln 2))"
      by (simp add:powr_def)
    also have "... \<le> exp (- (x *ln x^3))"
      using aux0 by (intro iffD2[OF exp_le_cancel_iff]) auto
    also have "... = ?R1"
      by simp
    finally show ?thesis
      by simp
  qed

  have "?L \<le> measure \<Omega> {\<omega>. is_too_large (\<tau>\<^sub>2 \<omega> A q_max)}"
    using lt_s_too_large
    by (intro pmf_mono) (simp del:is_too_large.simps)
  also have "... = measure \<Omega>
    {\<omega>. (\<Sum>(i,j)\<in>{..<l}\<times>{..<b}. \<lfloor>log 2 (of_int (max (\<tau>\<^sub>2 \<omega> A q_max i j) (-1)) + 2)\<rfloor>) > C\<^sub>5 * b *l}"
    by simp
  also have "... = measure \<Omega> {\<omega>. real_of_int (\<Sum>(i,j)\<in>{..<l}\<times>{..<b}.
    \<lfloor>log 2 (of_int (max (\<tau>\<^sub>2 \<omega> A q_max i j) (-1)) + 2)\<rfloor>) > of_int (C\<^sub>5 * b * l)}"
    unfolding  of_int_less_iff by simp
  also have "... = measure \<Omega> {\<omega>. real_of_int C\<^sub>5 * real b * real l < of_int (\<Sum>x\<in>{..<l} \<times> {..<b}.
    \<lfloor>log 2 (real_of_int (\<tau>\<^sub>1 (\<omega> (fst x)) A q_max (snd x)) + 2)\<rfloor>)}"
    by (intro_cong "[\<sigma>\<^sub>2 measure, \<sigma>\<^sub>1 Collect, \<sigma>\<^sub>1 of_int, \<sigma>\<^sub>2 (<)]" more:ext sum.cong)
     (auto simp add:case_prod_beta \<tau>\<^sub>2_def \<tau>\<^sub>1_def)

  also have "... = measure \<Omega> {\<omega>. (\<Sum>i<l. Z (\<omega> i)) > of_int C\<^sub>5 * real b * real l}"
    unfolding Z_def sum.cartesian_product \<tau>\<^sub>1_def by (simp add:case_prod_beta)
  also have "... = measure \<Omega> {\<omega>. (\<Sum>i<l. V (\<omega> i) + 3) > of_int C\<^sub>5 * real l}"
    unfolding V_def using b_min
    by (intro measure_pmf_cong) (simp add:sum_divide_distrib[symmetric] field_simps sum.distrib)
  also have "... = measure \<Omega> {\<omega>. (\<Sum>i<l. V (\<omega> i)) > of_int (C\<^sub>5-3) * real l}"
    by (simp add:sum.distrib algebra_simps)
  also have "... \<le> measure \<Omega> {\<omega>. (\<Sum>i<l. V (\<omega> i)) \<ge> C\<^sub>1 * real l}"
    unfolding C\<^sub>5_def using C\<^sub>1_est by (intro pmf_mono) auto
  also have "... \<le> exp (- real l)"
    by (intro \<Omega>.deviation_bound l_gt_0 0) (simp_all add: \<Lambda>_def)
  also have "... \<le> exp (- (C\<^sub>6 * ln (2 / \<delta>)))"
    using l_lbound by (intro iffD2[OF exp_le_cancel_iff]) auto
  also have "... \<le> exp (- (1 * ln (2 / \<delta>)))"
    unfolding C\<^sub>6_def using \<delta>_gt_0 \<delta>_lt_1
    by (intro iffD2[OF exp_le_cancel_iff] le_imp_neg_le mult_right_mono ln_ge_zero) auto
  also have "... = exp ( ln ( \<delta> / 2))"
    using \<delta>_gt_0 by (simp add: ln_div)
  also have "... =  \<delta>/2"
    using \<delta>_gt_0 by simp
  finally show ?thesis
    by simp
qed

end

unbundle no_intro_cong_syntax

end