section \<open>Accuracy without cutoff\label{sec:accuracy_wo_cutoff}\<close>

text \<open>This section verifies that each of the $l$ estimate have the required accuracy with high
probability assuming that there was no cut-off, i.e., that $s=0$. Section~\ref{sec:accuracy} will
then show that this remains true as long as the cut-off is below @{term "t f"} the subsampling
threshold.\<close>

theory Distributed_Distinct_Elements_Accuracy_Without_Cutoff
  imports
    Distributed_Distinct_Elements_Inner_Algorithm
    Distributed_Distinct_Elements_Balls_and_Bins
begin

no_notation Polynomials.var ("X\<index>")

locale inner_algorithm_fix_A = inner_algorithm +
  fixes A
  assumes A_range: "A \<subseteq> {..<n}"
  assumes A_nonempty: "{} \<noteq> A"
begin

definition X :: nat where "X = card A"

definition q_max where "q_max = nat (\<lceil>log 2 X\<rceil> - b_exp)"

definition t :: "(nat \<Rightarrow> nat) \<Rightarrow> int"
  where "t f = int (Max (f ` A)) - b_exp + 9"

definition s :: "(nat \<Rightarrow> nat) \<Rightarrow> nat"
  where "s f = nat (t f)"

definition R :: "(nat \<Rightarrow> nat) \<Rightarrow> nat set"
  where "R f = {a. a \<in> A \<and> f a \<ge> s f}"

definition r :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat"
  where "r x f = card {a. a \<in> A \<and> f a \<ge> x}"

definition p where "p = (\<lambda>(f,g,h). card {j\<in> {..<b}. \<tau>\<^sub>1 (f,g,h) A 0 j \<ge> s f})"

definition Y where "Y = (\<lambda>(f,g,h). 2 ^ s f * \<rho>_inv (p (f,g,h)))"

lemma fin_A: "finite A"
  using A_range finite_nat_iff_bounded by auto

lemma X_le_n: "X \<le> n"
proof -
  have "card A \<le> card {..<n}"
    by (intro card_mono A_range) simp
  thus ?thesis
    unfolding X_def by simp
qed

lemma X_ge_1: "X \<ge> 1"
  unfolding X_def
  using fin_A A_nonempty by (simp add: leI)

lemma of_bool_square: "(of_bool x)\<^sup>2 = ((of_bool x)::real)"
  by (cases x, auto)

lemma r_eq: "r x f = (\<Sum> a \<in> A.( of_bool( x \<le> f a) :: real))"
  unfolding r_def of_bool_def sum.If_cases[OF fin_A]
  by (simp add: Collect_conj_eq)

lemma
  shows
    r_exp: "(\<integral>\<omega>. real (r x \<omega>) \<partial> \<Psi>\<^sub>1) = real X * (of_bool (x \<le> max (nat \<lceil>log 2 n\<rceil>) 1) / 2^x)" and
    r_var: "measure_pmf.variance \<Psi>\<^sub>1 (\<lambda>\<omega>. real (r x \<omega>)) \<le> (\<integral>\<omega>. real (r x \<omega>) \<partial> \<Psi>\<^sub>1)"
proof -
  define V :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> real" where "V = (\<lambda>a f. of_bool (x \<le> f a))"

  have V_exp: "(\<integral>\<omega>. V a \<omega> \<partial>\<Psi>\<^sub>1) = of_bool (x \<le> max (nat \<lceil>log 2 n\<rceil>) 1)/2^x"
    (is "?L = ?R") if "a \<in> A" for a
  proof -
    have a_le_n: "a < n"
      using that A_range by auto

    have "?L = (\<integral>\<omega>. indicator {f. x \<le> f a} \<omega> \<partial> \<Psi>\<^sub>1)"
      unfolding V_def by (intro integral_cong_AE) auto
    also have "... = measure (map_pmf (\<lambda>\<omega>. \<omega> a) (sample_pmf \<Psi>\<^sub>1)) {f. x \<le> f}"
      by simp
    also have "... = measure (\<G> n_exp) {f. x \<le> f}"
      unfolding \<Psi>\<^sub>1.single[OF a_le_n] by simp
    also have "... = of_bool (x \<le> max (nat \<lceil>log 2 n\<rceil>) 1)/2^x"
      unfolding \<G>_prob n_exp_def by simp
    finally show ?thesis by simp
  qed

  have b:"(\<integral>\<omega>. real (r x \<omega>) \<partial> \<Psi>\<^sub>1) = (\<Sum> a \<in> A. (\<integral>\<omega>. V a \<omega> \<partial>\<Psi>\<^sub>1))"
    unfolding r_eq V_def  using \<Psi>\<^sub>1.sample_space
    by (intro Bochner_Integration.integral_sum) auto
  also have "... = (\<Sum> a \<in> A.  of_bool (x \<le> max (nat \<lceil>log 2 n\<rceil>) 1)/2^x)"
    using V_exp by (intro sum.cong) auto
  also have "... = X * (of_bool (x \<le> max (nat \<lceil>log 2 n\<rceil>) 1) / 2^x)"
    using X_def by simp
  finally show "(\<integral>\<omega>. real (r x \<omega>) \<partial> \<Psi>\<^sub>1) = real X * (of_bool (x \<le> max (nat \<lceil>log 2 n\<rceil>) 1)/ 2^x)"
    by simp

  have "(\<integral>\<omega>. (V a \<omega>)^2 \<partial> \<Psi>\<^sub>1) = (\<integral>\<omega>. V a \<omega> \<partial> \<Psi>\<^sub>1)" for a
    unfolding V_def of_bool_square by simp

  hence a:"measure_pmf.variance \<Psi>\<^sub>1 (V a) \<le> measure_pmf.expectation \<Psi>\<^sub>1 (V a)"  for a
    using \<Psi>\<^sub>1.sample_space by (subst measure_pmf.variance_eq) auto

  have "J \<subseteq> A \<Longrightarrow> card J = 2 \<Longrightarrow> prob_space.indep_vars \<Psi>\<^sub>1 (\<lambda>_. borel) V J" for J
    unfolding V_def using A_range finite_subset[OF _ fin_A]
    by (intro prob_space.indep_vars_compose2[where Y="\<lambda>i y. of_bool(x \<le> y)" and M'="\<lambda>_. discrete"]
        prob_space.k_wise_indep_vars_subset[OF _ \<Psi>\<^sub>1.indep]) (auto simp:prob_space_measure_pmf)
  hence "measure_pmf.variance \<Psi>\<^sub>1 (\<lambda>\<omega>. real (r x \<omega>)) = (\<Sum> a \<in> A. measure_pmf.variance \<Psi>\<^sub>1 (V a))"
    unfolding r_eq V_def using \<Psi>\<^sub>1.sample_space
    by (intro measure_pmf.var_sum_pairwise_indep_2 fin_A) (simp_all)
  also have "... \<le> (\<Sum> a \<in> A. (\<integral>\<omega>. V a \<omega> \<partial> \<Psi>\<^sub>1))"
    by (intro sum_mono a)
  also have "... = (\<integral>\<omega>. real (r x \<omega>) \<partial> \<Psi>\<^sub>1)"
    unfolding b by simp
  finally show "measure_pmf.variance \<Psi>\<^sub>1 (\<lambda>\<omega>. real (r x \<omega>)) \<le> (\<integral>\<omega>. real (r x \<omega>) \<partial> \<Psi>\<^sub>1)" by simp
qed

definition E\<^sub>1 where "E\<^sub>1 = (\<lambda>(f,g,h). 2 powr (-t f) * X \<in> {b/2^16..b/2})"

lemma t_low:
  "measure \<Psi>\<^sub>1 {f. of_int (t f) < log 2 (real X) + 1 - b_exp} \<le> 1/2^7" (is "?L \<le> ?R")
proof (cases "log 2 (real X) \<ge> 8")
  case True
  define Z :: "(nat \<Rightarrow> nat) \<Rightarrow> real" where "Z = r (nat \<lceil>log 2 (real X) - 8\<rceil>)"

  have "log 2 (real X) \<le> log 2 (real n)"
    using X_le_n X_ge_1 by (intro log_mono) auto
  hence "nat \<lceil>log 2 (real X) - 8\<rceil> \<le> nat \<lceil>log 2 (real n)\<rceil>"
    by (intro nat_mono ceiling_mono) simp
  hence a:"(nat \<lceil>log 2 (real X) - 8\<rceil> \<le> max (nat \<lceil>log 2 (real n)\<rceil>) 1)"
    by simp

  have b:"real (nat (\<lceil>log 2 (real X)\<rceil> - 8)) \<le> log 2 (real X) - 7"
    using True by linarith

  have "2 ^ 7 = real X / (2 powr (log 2 X) * 2 powr (-7))"
    using X_ge_1 by simp
  also have "... = real X / (2 powr (log 2 X - 7))"
    by (subst powr_add[symmetric]) simp
  also have "... \<le> real X / (2 powr (real (nat \<lceil>log 2 (real X) - 8\<rceil>)))"
    using b by (intro divide_left_mono powr_mono) auto
  also have "... = real X / 2 ^ nat \<lceil>log 2 (real X) - 8\<rceil>"
    by (subst powr_realpow) auto
  finally have "2 ^ 7 \<le> real X / 2 ^ nat \<lceil>log 2 (real X) - 8\<rceil>"
    by simp
  hence exp_Z_gt_2_7: "(\<integral>\<omega>. Z \<omega> \<partial>\<Psi>\<^sub>1) \<ge> 2^7"
    using a unfolding Z_def r_exp by simp

  have var_Z_le_exp_Z: "measure_pmf.variance \<Psi>\<^sub>1 Z \<le> (\<integral>\<omega>. Z \<omega> \<partial>\<Psi>\<^sub>1)"
    unfolding Z_def by (intro r_var)

  have "?L \<le> measure \<Psi>\<^sub>1 {f. of_nat (Max (f ` A)) < log 2 (real X) - 8}"
    unfolding t_def by (intro pmf_mono) (auto simp add:int_of_nat_def)
  also have "... \<le> measure \<Psi>\<^sub>1 {f \<in> space \<Psi>\<^sub>1.  (\<integral>\<omega>. Z \<omega> \<partial>\<Psi>\<^sub>1) \<le> \<bar>Z f - (\<integral>\<omega>. Z \<omega> \<partial>\<Psi>\<^sub>1) \<bar>}"
  proof (rule pmf_mono)
    fix f assume "f \<in> set_pmf (sample_pmf \<Psi>\<^sub>1)"
    have fin_f_A: "finite (f ` A)" using fin_A finite_imageI by blast
    assume " f \<in> {f. real (Max (f ` A)) < log 2 (real X) - 8}"
    hence "real (Max (f ` A)) < log 2 (real X) - 8" by auto
    hence "real (f a) < log 2 (real X) - 8" if "a \<in> A" for a
      using Max_ge[OF fin_f_A] imageI[OF that]  order_less_le_trans by fastforce
    hence "of_nat (f a) < \<lceil>log 2 (real X) - 8\<rceil>" if "a \<in> A" for a
      using that by (subst less_ceiling_iff) auto
    hence "f a < nat \<lceil>log 2 (real X) - 8\<rceil>" if "a \<in> A" for a
      using that True by fastforce
    hence "r (nat \<lceil>log 2 (real X) - 8\<rceil>) f = 0"
      unfolding r_def card_eq_0_iff using not_less by auto
    hence "Z f = 0"
      unfolding Z_def by simp
    thus "f \<in> {f \<in> space \<Psi>\<^sub>1.  (\<integral>\<omega>. Z \<omega> \<partial>\<Psi>\<^sub>1) \<le> \<bar>Z f - (\<integral>\<omega>. Z \<omega> \<partial>\<Psi>\<^sub>1)\<bar>}"
      by auto
  qed
  also have "... \<le> measure_pmf.variance \<Psi>\<^sub>1 Z / (\<integral>\<omega>. Z \<omega> \<partial>\<Psi>\<^sub>1)^2"
    using exp_Z_gt_2_7 \<Psi>\<^sub>1.sample_space by (intro measure_pmf.second_moment_method) simp_all
  also have "... \<le> (\<integral>\<omega>. Z \<omega> \<partial>\<Psi>\<^sub>1) / (\<integral>\<omega>. Z \<omega> \<partial>\<Psi>\<^sub>1)^2"
    by (intro divide_right_mono var_Z_le_exp_Z) simp
  also have "... = 1 / (\<integral>\<omega>. Z \<omega> \<partial>\<Psi>\<^sub>1)"
    using exp_Z_gt_2_7 by (simp add:power2_eq_square)
  also have "... \<le> ?R"
    using exp_Z_gt_2_7 by (intro divide_left_mono) auto
  finally show ?thesis by simp
next
  case "False"
  have "?L \<le> measure \<Psi>\<^sub>1 {f. of_nat (Max (f ` A)) < log 2 (real X) - 8}"
    unfolding t_def by (intro pmf_mono) (auto simp add:int_of_nat_def)
  also have "... \<le> measure \<Psi>\<^sub>1 {}"
    using False by (intro pmf_mono) simp
  also have "... = 0"
    by simp
  also have "... \<le> ?R" by simp
  finally show ?thesis by simp
qed

lemma t_high:
  "measure \<Psi>\<^sub>1 {f. of_int (t f) > log 2 (real X) + 16 - b_exp} \<le> 1/2^7" (is "?L \<le> ?R")
proof -
  define Z :: "(nat \<Rightarrow> nat) \<Rightarrow> real" where "Z = r (nat \<lfloor>log 2 (real X) + 8\<rfloor>)"

  have Z_nonneg: "Z f \<ge> 0" for f
    unfolding Z_def r_def by simp

  have "(\<integral>\<omega>. Z \<omega> \<partial>\<Psi>\<^sub>1) \<le> real X / (2 ^ nat \<lfloor>log 2 (real X) + 8\<rfloor>)"
    unfolding Z_def r_exp by simp
  also have "... \<le> real X / (2 powr (real (nat \<lfloor>log 2 (real X) + 8\<rfloor>)))"
    by (subst powr_realpow) auto
  also have "... \<le> real X / (2 powr \<lfloor>log 2 (real X) + 8\<rfloor>)"
    by (intro divide_left_mono powr_mono) auto
  also have "... \<le> real X / (2 powr (log 2 (real X) + 7))"
    by (intro divide_left_mono powr_mono, linarith) auto
  also have "... = real X / 2 powr (log 2 (real X)) / 2 powr 7"
    by (subst powr_add) simp
  also have "... \<le> 1/2 powr 7"
    using X_ge_1 by (subst powr_log_cancel) auto
  finally have Z_exp: "(\<integral>\<omega>. Z \<omega> \<partial>\<Psi>\<^sub>1) \<le> 1/2^7"
    by simp

  have "?L \<le> measure \<Psi>\<^sub>1 {f. of_nat (Max (f ` A)) > log 2 (real X) + 7}"
    unfolding t_def  by (intro pmf_mono) (auto simp add:int_of_nat_def)
  also have "... \<le> measure \<Psi>\<^sub>1 {f. Z f \<ge> 1}"
  proof (rule pmf_mono)
    fix f assume "f \<in> set_pmf (sample_pmf \<Psi>\<^sub>1)"
    assume " f \<in> {f. real (Max (f ` A)) > log 2 (real X) + 7}"
    hence "real (Max (f ` A)) > log 2 (real X) + 7" by simp
    hence "int (Max (f ` A)) \<ge> \<lfloor>log 2 (real X) + 8\<rfloor>"
      by linarith
    hence "Max (f ` A) \<ge> nat \<lfloor>log 2 (real X) + 8\<rfloor>"
      by simp
    moreover have "f ` A \<noteq> {}" "finite (f ` A)"
      using fin_A finite_imageI A_nonempty by auto
    ultimately obtain fa where "fa \<in> f ` A" " fa \<ge>  nat \<lfloor>log 2 (real X) + 8\<rfloor>"
      using Max_in by auto
    then obtain ae where ae_def: "ae \<in> A" "nat \<lfloor>log 2 (real X) + 8\<rfloor> \<le> f ae"
      by auto
    hence "r (nat \<lfloor>log 2 (real X) + 8\<rfloor>) f > 0"
      unfolding r_def card_gt_0_iff using fin_A by auto
    hence "Z f \<ge> 1"
      unfolding Z_def by simp
    thus "f \<in> {f. 1 \<le> Z f}" by simp
  qed
  also have "... \<le> (\<integral>\<omega>. Z \<omega> \<partial>\<Psi>\<^sub>1) / 1"
    using Z_nonneg using \<Psi>\<^sub>1.sample_space by (intro pmf_markov) auto
  also have "... \<le> ?R"
    using Z_exp by simp
  finally show ?thesis by simp
qed

lemma e_1: "measure \<Psi> {\<psi>. \<not>E\<^sub>1 \<psi>} \<le> 1/2^6"
proof -
  have "measure \<Psi>\<^sub>1 {f. 2 powr (of_int (-t f)) * real X \<notin> {real b/2^16..real b/2}} \<le>
    measure \<Psi>\<^sub>1 {f. 2 powr (of_int (-t f)) * real X < real b/2^16} +
    measure \<Psi>\<^sub>1 {f. 2 powr (of_int (-t f)) * real X > real b/2}"
    by (intro pmf_add) auto
  also have "... \<le> measure \<Psi>\<^sub>1 {f. of_int (t f) > log 2 X + 16 - b_exp} +
                   measure \<Psi>\<^sub>1 {f. of_int (t f) < log 2 X + 1 - b_exp}"
  proof (rule add_mono)
    show "measure \<Psi>\<^sub>1 {f. 2 powr (of_int (-t f)) * real X < real b/2^16} \<le>
    measure \<Psi>\<^sub>1 {f. of_int (t f) > log 2 X + 16 - b_exp}"
    proof (rule pmf_mono)
      fix f assume "f \<in> {f. 2 powr real_of_int (-t f) * real X < real b / 2 ^ 16}"
      hence "2 powr real_of_int (-t f) * real X < real b / 2 ^ 16"
        by simp
      hence "log 2 (2 powr of_int (-t f) * real X) < log 2 (real b / 2^16)"
        using b_min X_ge_1 by (intro iffD2[OF log_less_cancel_iff]) auto
      hence "of_int (-t f) + log  2 (real X) < log 2 (real b / 2^16)"
        using X_ge_1 by (subst (asm) log_mult) auto
      also have  "... = real b_exp - log 2 (2 powr 16)"
        unfolding b_def by (subst log_divide) auto
      also have "... = real b_exp - 16"
        by (subst log_powr_cancel) auto
      finally have "of_int (-t f) + log 2 (real X) < real b_exp - 16" by simp
      thus "f \<in> {f. of_int (t f) > log 2 (real X) + 16 - b_exp}"
        by simp
    qed
  next
    show "measure \<Psi>\<^sub>1 {f. 2 powr of_int (-t f) * real X > real b/2} \<le>
      measure \<Psi>\<^sub>1 {f. of_int (t f) < log 2 X + 1 - b_exp}"
    proof (rule pmf_mono)
      fix f assume "f \<in> {f. 2 powr real_of_int (-t f) * real X > real b / 2}"
      hence "2 powr real_of_int (-t f) * real X > real b / 2"
        by simp
      hence "log 2 (2 powr of_int (-t f) * real X) > log 2 (real b / 2)"
        using b_min X_ge_1 by (intro iffD2[OF log_less_cancel_iff]) auto
      hence "of_int (-t f) + log  2 (real X) > log 2 (real b / 2)"
        using X_ge_1 by (subst (asm) log_mult) auto
      hence  "of_int (-t f) + log  2 (real X) > real b_exp - 1"
        unfolding b_def by (subst (asm) log_divide) auto
      hence "of_int (t f) < log 2 (real X) + 1 - b_exp"
        by simp
      thus "f \<in> {f. of_int (t f) < log 2 (real X) + 1 - b_exp}"
        by simp
    qed
  qed
  also have "... \<le> 1/2^7 + 1/2^7"
    by (intro add_mono t_low t_high)
  also have "... = 1/2^6" by simp
  finally have "measure \<Psi>\<^sub>1 {f. 2 powr of_int (-t f) * real X \<notin> {real b/2^16..real b/2}} \<le> 1/2^6"
    by simp

  thus ?thesis
    unfolding sample_pmf_\<Psi> E\<^sub>1_def case_prod_beta
    by (subst pair_pmf_prob_left)
qed

definition E\<^sub>2 where "E\<^sub>2 = (\<lambda>(f,g,h). \<bar>card (R f) - X / 2^(s f)\<bar> \<le> \<epsilon>/3 * X / 2^(s f))"

lemma e_2: "measure \<Psi> {\<psi>. E\<^sub>1 \<psi> \<and> \<not>E\<^sub>2 \<psi>} \<le> 1/2^6" (is "?L \<le> ?R")
proof -
  define t\<^sub>m :: int where "t\<^sub>m = \<lfloor>log 2 (real X)\<rfloor> + 16 - b_exp"

  have t_m_bound: "t\<^sub>m \<le> \<lfloor>log 2 (real X)\<rfloor> - 10"
    unfolding t\<^sub>m_def using b_exp_ge_26 by simp

  have "real b / 2^16 = (real X * (1/ X)) * (real b / 2^16)"
    using X_ge_1 by simp
  also have "... = (real X * 2 powr (-log 2 X)) * (real b / 2^16)"
    using X_ge_1 by (subst powr_minus_divide) simp
  also have "... \<le> (real X * 2 powr (- \<lfloor>log 2 (real X)\<rfloor>)) * (2 powr b_exp / 2^16)"
    unfolding b_def using powr_realpow
    by (intro mult_mono powr_mono) auto
  also have "... = real X * (2 powr (- \<lfloor>log 2 (real X)\<rfloor>) * 2 powr(real b_exp-16))"
    by (subst powr_diff) simp
  also have "... = real X * 2 powr (- \<lfloor>log 2 (real X)\<rfloor> + (int b_exp - 16))"
    by (subst powr_add[symmetric]) simp
  also have "... = real X * 2 powr (-t\<^sub>m)"
    unfolding t\<^sub>m_def by (simp add:algebra_simps)
  finally have c:"real b / 2^16 \<le> real X * 2 powr (-t\<^sub>m)" by simp

  define T :: "nat set" where "T = {x. (real X / 2^x \<ge> real b / 2^16)}"

  have "x \<in> T \<longleftrightarrow> int x \<le> t\<^sub>m" for x
  proof -
    have "x \<in> T \<longleftrightarrow> 2^ x \<le> real X * 2^16 / b"
      using b_min by (simp add: field_simps T_def)
    also have "... \<longleftrightarrow> log 2 (2^x) \<le> log 2 (real X * 2^16 / b)"
      using X_ge_1 b_min by (intro log_le_cancel_iff[symmetric] divide_pos_pos) auto
    also have "... \<longleftrightarrow> x \<le> log 2 (real X * 2^16) - log 2 b"
      using X_ge_1 b_min by (subst log_divide) auto
    also have "... \<longleftrightarrow> x \<le> log 2 (real X) + log 2 (2 powr 16) - b_exp"
      unfolding b_def using X_ge_1 by (subst log_mult) auto
    also have "... \<longleftrightarrow> x \<le> \<lfloor>log 2 (real X) + log 2 (2 powr 16) - b_exp\<rfloor>"
      by linarith
    also have "... \<longleftrightarrow> x \<le> \<lfloor>log 2 (real X) + 16 - real_of_int (int b_exp)\<rfloor>"
      by (subst log_powr_cancel) auto
    also have "... \<longleftrightarrow> x \<le> t\<^sub>m"
      unfolding t\<^sub>m_def by linarith
    finally show ?thesis by simp
  qed
  hence T_eq: "T = {x. int x \<le> t\<^sub>m}" by auto

  have "T = {x. int x < t\<^sub>m+1}"
    unfolding T_eq by simp
  also have "... = {x. x < nat (t\<^sub>m + 1)}"
    unfolding zless_nat_eq_int_zless by simp
  finally have T_eq_2: "T = {x. x < nat (t\<^sub>m + 1)}"
    by simp

  have inj_1: "inj_on ((-) (nat t\<^sub>m)) T"
    unfolding T_eq by (intro inj_onI) simp
  have fin_T: "finite T"
    unfolding T_eq_2 by simp

  have r_exp: "(\<integral>\<omega>. real (r t \<omega>) \<partial>\<Psi>\<^sub>1) = real X / 2^t" if "t \<in> T" for t
  proof -
    have "t \<le> t\<^sub>m"
      using that unfolding T_eq by simp
    also have "... \<le> \<lfloor>log 2 (real X)\<rfloor> - 10"
      using t_m_bound by simp
    also have "... \<le> \<lfloor>log 2 (real X)\<rfloor>"
      by simp
    also have "... \<le> \<lfloor>log 2 (real n)\<rfloor>"
      using X_le_n X_ge_1 by (intro floor_mono log_mono) auto
    also have "... \<le> \<lceil>log 2 (real n)\<rceil>"
      by simp
    finally have "t \<le> \<lceil>log 2 (real n)\<rceil>" by simp
    hence "t \<le> max (nat \<lceil>log 2 (real n)\<rceil>) 1"by simp
    thus ?thesis
      unfolding r_exp by simp
  qed

  have r_var: "measure_pmf.variance \<Psi>\<^sub>1 (\<lambda>\<omega>. real (r t \<omega>)) \<le> real X / 2^t" if "t \<in> T" for t
    using r_exp[OF that] r_var by metis

  have "9 = C\<^sub>4 / \<epsilon>\<^sup>2 * \<epsilon>^2/2^23"
    using \<epsilon>_gt_0 by (simp add:C\<^sub>4_def)
  also have "... = 2 powr (log 2 (C\<^sub>4 /  \<epsilon>\<^sup>2)) *  \<epsilon>^2/2^23"
    using \<epsilon>_gt_0 C\<^sub>4_def by (subst powr_log_cancel) auto
  also have "... \<le> 2 powr b_exp * \<epsilon>^2/2^23"
    unfolding b_exp_def
    by (intro divide_right_mono mult_right_mono powr_mono, linarith) auto
  also have "... = b * \<epsilon>^2/2^23"
    using powr_realpow unfolding b_def by simp
  also have "... = (b/2^16) * (\<epsilon>^2/2^7)"
    by simp
  also have "... \<le> (X * 2 powr (-t\<^sub>m)) * (\<epsilon>^2/2^7)"
    by (intro mult_mono c) auto
  also have "... = X * (2 powr (-t\<^sub>m) * 2 powr (-7)) * \<epsilon>^2"
    using powr_realpow by simp
  also have "... = 2 powr (-t\<^sub>m-7) * (\<epsilon>^2 * X)"
    by (subst powr_add[symmetric]) (simp )
  finally have "9 \<le> 2 powr (-t\<^sub>m-7) * (\<epsilon>^2 * X)" by simp
  hence b: "9/ (\<epsilon>^2 * X) \<le> 2 powr (-t\<^sub>m -7)"
    using \<epsilon>_gt_0 X_ge_1
    by (subst pos_divide_le_eq) auto

  have a: "measure \<Psi>\<^sub>1 {f.\<bar>real (r t f)-real X/2^t\<bar>> \<epsilon>/3 *real X/2^t} \<le> 2 powr (real t-t\<^sub>m-7)"
    (is"?L1 \<le> ?R1") if "t \<in> T" for t
  proof -
    have "?L1 \<le> \<P>(f in \<Psi>\<^sub>1. \<bar>real (r t f) - real X / 2^t\<bar> \<ge>  \<epsilon>/3 * real X / 2^t)"
      by (intro pmf_mono) auto
    also have "... = \<P>(f in \<Psi>\<^sub>1. \<bar>real (r t f)-(\<integral>\<omega>. real (r t \<omega>) \<partial> \<Psi>\<^sub>1)\<bar> \<ge> \<epsilon>/3 * real X/2^t)"
      by (simp add: r_exp[OF that])
    also have "... \<le> measure_pmf.variance \<Psi>\<^sub>1 (\<lambda>\<omega>. real (r t \<omega>)) / (\<epsilon>/3 * real X / 2^t)^2"
      using X_ge_1 \<epsilon>_gt_0 \<Psi>\<^sub>1.sample_space
      by (intro measure_pmf.Chebyshev_inequality divide_pos_pos mult_pos_pos) auto
    also have "... \<le> (X / 2^t) / (\<epsilon>/3 * X / 2^t)^2"
      by (intro divide_right_mono r_var[OF that]) simp
    also have "... = 2^t*(9/ ( \<epsilon>^2 * X))"
      by (simp add:power2_eq_square algebra_simps)
    also have "... \<le> 2^t*(2 powr (-t\<^sub>m-7))"
      by (intro mult_left_mono b) simp
    also have "... = 2 powr t * 2 powr (-t\<^sub>m-7)"
      by (subst powr_realpow[symmetric]) auto
    also have "... = ?R1"
      by (subst powr_add[symmetric]) (simp add:algebra_simps)
    finally show "?L1 \<le> ?R1" by simp
  qed

  have "\<exists>y<nat (t\<^sub>m + 1). x = nat t\<^sub>m - y" if "x < nat (t\<^sub>m+1)" for x
    using that by (intro exI[where x="nat t\<^sub>m - x"]) simp
  hence T_reindex: "(-) (nat t\<^sub>m) ` {x. x < nat (t\<^sub>m + 1)} = {..<nat (t\<^sub>m + 1)}"
    by (auto simp add: set_eq_iff image_iff)

  have "?L \<le> measure \<Psi> {\<psi>. (\<exists>t \<in> T. \<bar>real (r t (fst \<psi>))-real X/2^t\<bar> > \<epsilon>/3 * real X / 2^t)}"
  proof (rule pmf_mono)
    fix \<psi>
    assume "\<psi> \<in> set_pmf (sample_pmf \<Psi>)"
    obtain f g h where \<psi>_def: "\<psi> = (f,g,h)" by (metis prod_cases3)
    assume "\<psi> \<in> {\<psi>. E\<^sub>1 \<psi> \<and> \<not> E\<^sub>2 \<psi>}"
    hence a:"2 powr ( -real_of_int (t f)) * real X \<in> {real b/2^16..real b/2}" and
      b:"\<bar>card (R f) - real X / 2^(s f)\<bar> >  \<epsilon>/3 * X / 2^(s f)"
      unfolding E\<^sub>1_def E\<^sub>2_def by (auto simp add:\<psi>_def)
    have "\<bar>card (R f) - X / 2^(s f)\<bar> = 0" if "s f= 0"
      using that by (simp add:R_def X_def)
    moreover have "( \<epsilon>/3) * (X / 2^s f) \<ge> 0"
      using \<epsilon>_gt_0 X_ge_1 by (intro mult_nonneg_nonneg) auto
    ultimately have "False" if "s f = 0"
      using b that by simp
    hence "s f > 0" by auto
    hence "t f = s f" unfolding s_def by simp
    hence "2 powr (-real (s f)) * X \<ge> b / 2^16"
      using a by simp
    hence "X / 2 powr (real (s f)) \<ge> b / 2^16"
      by (simp add: divide_powr_uminus mult.commute)
    hence "real X / 2 ^ (s f) \<ge> b / 2^16"
      by (subst (asm) powr_realpow, auto)
    hence "s f \<in> T" unfolding T_def by simp
    moreover have "\<bar>r (s f) f - X / 2^s f\<bar> >  \<epsilon>/3 * X / 2^s f"
      using R_def r_def b by simp
    ultimately have "\<exists>t \<in> T. \<bar>r t (fst \<psi>) - X / 2^t\<bar> >  \<epsilon>/3 * X / 2^t"
      using \<psi>_def by (intro bexI[where x="s f"]) simp
    thus "\<psi> \<in> {\<psi>. (\<exists>t \<in> T. \<bar>r t (fst \<psi>) - X / 2^t\<bar> >  \<epsilon>/3 * X / 2^t)}" by simp
  qed
  also have "... = measure \<Psi>\<^sub>1 {f. (\<exists>t \<in> T. \<bar>real (r t f)-real X / 2^t\<bar> > \<epsilon>/3 * real X/2^t)}"
    unfolding sample_pmf_\<Psi> by (intro pair_pmf_prob_left)
  also have "... = measure \<Psi>\<^sub>1 (\<Union>t \<in> T. {f. \<bar>real (r t f)-real X / 2^t\<bar> > \<epsilon>/3 * real X/2^t})"
    by (intro measure_pmf_cong) auto
  also have "... \<le> (\<Sum>t \<in> T. measure \<Psi>\<^sub>1 {f.\<bar>real (r t f)-real X / 2^t\<bar> > \<epsilon>/3 * real X/2^t})"
    by (intro measure_UNION_le fin_T) (simp)
  also have "... \<le> (\<Sum>t \<in> T.  2 powr (real t - of_int t\<^sub>m - 7))"
    by (intro sum_mono a)
  also have "... = (\<Sum>t \<in> T.  2 powr (-int (nat t\<^sub>m-t) - 7))"
    unfolding T_eq
    by (intro sum.cong refl arg_cong2[where f="(powr)"]) simp
  also have "... = (\<Sum>x \<in> (\<lambda>x. nat t\<^sub>m - x) ` T. 2 powr (-real x - 7))"
    by (subst sum.reindex[OF inj_1]) simp
  also have "... = (\<Sum>x \<in> (\<lambda>x. nat t\<^sub>m - x) ` T. 2 powr (-7) * 2 powr (-real x))"
    by (subst powr_add[symmetric]) (simp add:algebra_simps)
  also have "... = 1/2^7 * (\<Sum>x \<in> (\<lambda>x. nat t\<^sub>m - x) ` T. 2 powr (-real x))"
    by (subst sum_distrib_left) simp
  also have "... = 1/2^7 * (\<Sum>x <nat (t\<^sub>m+1). 2 powr (-real x))"
    unfolding T_eq_2 T_reindex
    by (intro arg_cong2[where f="(*)"] sum.cong) auto
  also have "... = 1/2^7 * (\<Sum>x <nat (t\<^sub>m+1). (2 powr (-1)) powr (real x))"
    by (subst powr_powr) simp
  also have "... = 1/2^7 * (\<Sum>x <nat (t\<^sub>m+1). (1/2)^x)"
    using powr_realpow by simp
  also have "... \<le> 1/2^7 * 2"
    by(subst geometric_sum) auto
  also have "... = 1/2^6" by simp
  finally show ?thesis by simp
qed

definition E\<^sub>3 where "E\<^sub>3 = (\<lambda>(f,g,h). inj_on g (R f))"

lemma R_bound:
  fixes f g h
  assumes "E\<^sub>1 (f,g,h)"
  assumes "E\<^sub>2 (f,g,h)"
  shows "card (R f) \<le> 2/3 * b"
proof -
  have "real (card (R f)) \<le> ( \<epsilon> / 3) * (real X / 2 ^ s f) + real X / 2 ^ s f"
    using assms(2) unfolding E\<^sub>2_def by simp
  also have "... \<le> (1/3) * (real X / 2 ^ s f) + real X / 2 ^ s f"
    using \<epsilon>_lt_1 by (intro add_mono mult_right_mono) auto
  also have "... = (4/3) * (real X / 2 powr s f)"
    using powr_realpow by simp
  also have "... \<le> (4/3) * (real X / 2 powr t f)"
    unfolding s_def
    by (intro mult_left_mono divide_left_mono powr_mono) auto
  also have "... = (4/3) * (2 powr (-(of_int (t f))) * real X)"
    by (subst powr_minus_divide) simp
  also have "... = (4/3) * (2 powr (- t f) * real X)"
    by simp
  also have "... \<le> (4/3) * (b/2)"
    using assms(1) unfolding E\<^sub>1_def
    by (intro mult_left_mono) auto
  also have "... \<le> (2/3) * b" by simp
  finally show ?thesis by simp
qed

lemma e_3: "measure \<Psi> {\<psi>. E\<^sub>1 \<psi> \<and> E\<^sub>2 \<psi> \<and> \<not>E\<^sub>3 \<psi>} \<le> 1/2^6" (is "?L \<le> ?R")
proof -
  let ?\<alpha> = "(\<lambda>(z,x,y) f. z < C\<^sub>7*b^2 \<and> x \<in> R f \<and> y \<in> R f \<and> x < y)"
  let ?\<beta> = "(\<lambda>(z,x,y) g. g x = z \<and> g y = z)"

  have \<beta>_prob: "measure \<Psi>\<^sub>2 {g. ?\<beta> \<omega> g} \<le> (1/real (C\<^sub>7*b^2)^2)"
    if "?\<alpha> \<omega> f" for \<omega> f
  proof -
    obtain x y z where \<omega>_def: "\<omega> = (z,x,y)" by (metis prod_cases3)
    have a:"prob_space.k_wise_indep_vars \<Psi>\<^sub>2 2 (\<lambda>i. discrete) (\<lambda>x \<omega>. \<omega> x = z) {..<n}"
      by (intro prob_space.k_wise_indep_vars_compose[OF _ \<Psi>\<^sub>2.indep])
       (simp_all add:prob_space_measure_pmf)

    have "u \<in> R f \<Longrightarrow> u < n" for u
      unfolding R_def using A_range by auto
    hence b: "x < n" "y < n" "card {x, y} = 2"
      using that \<omega>_def by auto
    have c: "z < C\<^sub>7*b\<^sup>2" using \<omega>_def that by simp

    have "measure \<Psi>\<^sub>2 {g. ?\<beta> \<omega> g} = measure \<Psi>\<^sub>2 {g. (\<forall>\<xi> \<in> {x,y}. g \<xi> = z)}"
      by (simp add:\<omega>_def)
    also have "... = (\<Prod>\<xi> \<in> {x,y}. measure \<Psi>\<^sub>2 {g. g \<xi> = z})"
      using b by (intro measure_pmf.split_indep_events[OF refl, where I="{x,y}"]
          prob_space.k_wise_indep_vars_subset[OF _ a]) (simp_all add:prob_space_measure_pmf)
    also have "... = (\<Prod>\<xi> \<in> {x,y}. measure (map_pmf (\<lambda>\<omega>. \<omega> \<xi>) (sample_pmf \<Psi>\<^sub>2)) {g. g = z}) "
      by (simp add:vimage_def)
    also have "... = (\<Prod>\<xi> \<in> {x,y}. measure [C\<^sub>7 * b\<^sup>2]\<^sub>S {g. g=z})"
      using b \<Psi>\<^sub>2.single by (intro prod.cong) fastforce+
    also have "... = (\<Prod>\<xi> \<in> {x,y}. measure (pmf_of_set {..<C\<^sub>7 * b\<^sup>2}) {z})"
      by (subst nat_sample_pmf) simp
    also have "... = (measure (pmf_of_set {..<C\<^sub>7 * b\<^sup>2}) {z})^2"
      using b by simp
    also have "... \<le> (1 /(C\<^sub>7*b\<^sup>2))^2"
      using c by (subst measure_pmf_of_set) auto
    also have "... = (1 /(C\<^sub>7*b\<^sup>2)^2)"
      by (simp add:algebra_simps power2_eq_square)
    finally show ?thesis by simp
  qed

  have \<alpha>_card: "card {\<omega>. ?\<alpha> \<omega> f} \<le> (C\<^sub>7*b^2) * (card (R f) * (card (R f)-1)/2)"
    (is "?TL \<le> ?TR") and fin_\<alpha>: "finite {\<omega>. ?\<alpha> \<omega> f}" (is "?T2") for f
  proof -
    have t1: "{\<omega>. ?\<alpha> \<omega> f} \<subseteq> {..<C\<^sub>7*b^2} \<times> {(x,y) \<in> R f \<times> R f. x < y}"
      by (intro subsetI) auto
    moreover have "card ({..<C\<^sub>7*b^2} \<times> {(x,y) \<in> R f \<times> R f. x < y}) = ?TR"
      using  card_ordered_pairs'[where M="R f"]
      by (simp add: card_cartesian_product)
    moreover have "finite (R f)"
      unfolding R_def using fin_A finite_subset by simp
    hence "finite {(x, y). (x, y) \<in> R f \<times> R f \<and> x < y}"
      by (intro finite_subset[where B="R f \<times> R f", OF _ finite_cartesian_product]) auto
    hence t2: "finite ({..<C\<^sub>7*b^2} \<times> {(x,y) \<in> R f \<times> R f. x < y})"
      by (intro finite_cartesian_product) auto
    ultimately show "?TL \<le> ?TR"
      using card_mono of_nat_le_iff by (metis (no_types, lifting))
    show ?T2
      using finite_subset[OF t1 t2] by simp
  qed

  have "?L \<le> measure \<Psi> {(f,g,h). card (R f) \<le> b \<and> (\<exists> x y z. ?\<alpha> (x,y,z) f \<and> ?\<beta> (x,y,z) g)}"
  proof (rule pmf_mono)
    fix \<psi> assume b:"\<psi> \<in> set_pmf (sample_pmf \<Psi>)"
    obtain f g h where \<psi>_def:"\<psi> = (f,g,h)" by (metis prod_cases3)
    have "(f,g,h) \<in> sample_set \<Psi>"
      using sample_space_alt[OF sample_space_\<Psi>] b \<psi>_def by simp
    hence c:"g x < C\<^sub>7*b^2" for x
      using g_range by simp

    assume a:"\<psi> \<in> {\<psi>. E\<^sub>1 \<psi> \<and> E\<^sub>2 \<psi> \<and> \<not> E\<^sub>3 \<psi>}"
    hence "card (R f) \<le> 2/3 * b"
      using R_bound \<psi>_def by force
    moreover have "\<exists>a b. a \<in> R f \<and> b \<in> R f \<and> a \<noteq> b \<and> g a = g b"
      using a unfolding \<psi>_def E\<^sub>3_def inj_on_def by auto
    hence "\<exists>x y. x \<in> R f \<and> y \<in> R f \<and> x < y \<and> g x = g y"
      by (metis not_less_iff_gr_or_eq)
    hence "\<exists>x y z. ?\<alpha> (x,y,z) f \<and> ?\<beta> (x,y,z) g"
      using c by blast
    ultimately show "\<psi> \<in> {(f, g, h). card (R f) \<le> b \<and> (\<exists> x y z. ?\<alpha> (x,y,z) f \<and> ?\<beta> (x,y,z) g)}"
      unfolding \<psi>_def by auto
  qed
  also have "... = (\<integral>f. measure (pair_pmf \<Psi>\<^sub>2 \<Psi>\<^sub>3)
     {g. card (R f) \<le> b \<and> (\<exists>x y z. ?\<alpha> (x,y,z) f \<and> ?\<beta> (x,y,z) (fst g))} \<partial>\<Psi>\<^sub>1)"
    unfolding sample_pmf_\<Psi> split_pair_pmf by (simp add: case_prod_beta)
  also have
    "... = (\<integral>f. measure \<Psi>\<^sub>2 {g. card (R f) \<le> b \<and> (\<exists>x y z. ?\<alpha> (x,y,z) f \<and> ?\<beta> (x,y,z) g)} \<partial>\<Psi>\<^sub>1)"
    by (subst pair_pmf_prob_left) simp
  also have "... \<le> (\<integral>f. 1/real (2*C\<^sub>7) \<partial>\<Psi>\<^sub>1)"
  proof (rule pmf_exp_mono[OF integrable_sample_pmf[OF \<Psi>\<^sub>1.sample_space]
          integrable_sample_pmf[OF \<Psi>\<^sub>1.sample_space]])
    fix f assume "f \<in> set_pmf (sample_pmf \<Psi>\<^sub>1)"
    show "measure \<Psi>\<^sub>2 {g. card (R f) \<le> b \<and> (\<exists>x y z. ?\<alpha> (x,y,z) f \<and> ?\<beta> (x,y,z) g)} \<le> 1 / real (2 * C\<^sub>7)"
      (is "?L1 \<le> ?R1")
    proof (cases "card (R f) \<le> b")
      case True
      have "?L1 \<le> measure \<Psi>\<^sub>2 (\<Union> \<omega> \<in> {\<omega>. ?\<alpha> \<omega> f}. {g. ?\<beta> \<omega> g})"
        by (intro pmf_mono) auto
      also have "... \<le> (\<Sum>\<omega> \<in> {\<omega>. ?\<alpha> \<omega> f}. measure \<Psi>\<^sub>2 {g. ?\<beta> \<omega> g})"
        by (intro measure_UNION_le fin_\<alpha>) auto
      also have "... \<le> (\<Sum>\<omega> \<in> {\<omega>. ?\<alpha> \<omega> f}. (1/real (C\<^sub>7*b^2)^2))"
        by (intro sum_mono \<beta>_prob) auto
      also have "... = card {\<omega>. ?\<alpha> \<omega> f} /(C\<^sub>7*b^2)^2"
        by simp
      also have "... \<le> (C\<^sub>7*b^2) * (card (R f) * (card (R f)-1)/2) / (C\<^sub>7*b^2)^2"
        by (intro \<alpha>_card divide_right_mono) simp
      also have "... \<le> (C\<^sub>7*b^2) * (b * b / 2)  / (C\<^sub>7*b^2)^2"
        unfolding C\<^sub>7_def using True
        by (intro divide_right_mono Nat.of_nat_mono mult_mono) auto
      also have "... = 1/(2*C\<^sub>7)"
        using b_min by (simp add:algebra_simps power2_eq_square)
      finally show ?thesis by simp
    next
      case False
      then show ?thesis by simp
    qed
  qed
  also have "... \<le> 1/2^6"
    unfolding C\<^sub>7_def by simp
  finally show ?thesis by simp
qed

definition E\<^sub>4 where "E\<^sub>4 = (\<lambda>(f,g,h). \<bar>p (f,g,h) - \<rho> (card (R f))\<bar> \<le>  \<epsilon>/12 * card (R f))"

lemma e_4_h: "9 / sqrt b \<le> \<epsilon> / 12"
proof -
  have "108 \<le> sqrt (C\<^sub>4)"
    unfolding C\<^sub>4_def by (approximation 5)
  also have "... \<le> sqrt( \<epsilon>^2 * real b)"
    using b_lower_bound \<epsilon>_gt_0
    by (intro real_sqrt_le_mono) (simp add: pos_divide_le_eq algebra_simps)
  also have "... =  \<epsilon> * sqrt b"
    using \<epsilon>_gt_0 by (simp add:real_sqrt_mult)
  finally have "108 \<le>  \<epsilon> * sqrt b"  by simp
  thus ?thesis
    using b_min by (simp add:pos_divide_le_eq)
qed

lemma e_4: "measure \<Psi> {\<psi>. E\<^sub>1 \<psi> \<and> E\<^sub>2 \<psi> \<and> E\<^sub>3 \<psi> \<and> \<not>E\<^sub>4 \<psi>} \<le> 1/2^6" (is "?L \<le> ?R")
proof -
  have a: "measure \<Psi>\<^sub>3 {h. E\<^sub>1 (f,g,h) \<and> E\<^sub>2 (f,g,h) \<and> E\<^sub>3 (f,g,h) \<and> \<not>E\<^sub>4 (f,g,h)} \<le> 1/2^6"
    (is "?L1 \<le> ?R1") if "f \<in> set_pmf (sample_pmf \<Psi>\<^sub>1)" "g \<in> set_pmf(sample_pmf \<Psi>\<^sub>2)"
    for f g
  proof (cases "card (R f) \<le> b \<and> inj_on g (R f)")
    case True

    have g_inj: "inj_on g (R f)"
      using True by simp

    have fin_R: "finite (g ` R f)"
      unfolding R_def using fin_A
      by (intro finite_imageI) simp

    interpret B:balls_and_bins_abs "g ` R f" "{..<b}"
      using fin_R b_ne by unfold_locales auto

    have "range g \<subseteq> {..<C\<^sub>7 * b\<^sup>2}"
      using g_range_1 that(2) unfolding sample_space_alt[OF \<Psi>\<^sub>2.sample_space] by auto
    hence g_ran: "g ` R f \<subseteq> {..<C\<^sub>7 * b\<^sup>2}"
      by auto

    have "sample_pmf [b]\<^sub>S = pmf_of_set {..<b}"
      unfolding sample_pmf_def nat_sample_space_def by simp
    hence " map_pmf (\<lambda>\<omega>. \<omega> x) (sample_pmf (\<H> k (C\<^sub>7 * b\<^sup>2) [b]\<^sub>S)) = pmf_of_set {..<b}"
      if "x \<in> g ` R f" for x
      using g_ran \<Psi>\<^sub>3.single that by auto
    moreover have "prob_space.k_wise_indep_vars \<Psi>\<^sub>3 k (\<lambda>_. discrete) (\<lambda>x \<omega>. \<omega> x) (g ` R f)"
      by (intro prob_space.k_wise_indep_subset[OF _ _ \<Psi>\<^sub>3.indep] g_ran prob_space_measure_pmf)
    ultimately have lim_balls_and_bins: "B.lim_balls_and_bins k (sample_pmf (\<H> k (C\<^sub>7 * b\<^sup>2) [b]\<^sub>S))"
      unfolding B.lim_balls_and_bins_def by auto

    have card_g_R: "card (g ` R f) = card (R f)"
      using True card_image by auto
    hence b_mu: "\<rho> (card (R f)) = B.\<mu>"
      unfolding B.\<mu>_def \<rho>_def using b_min by (simp add:powr_realpow)

    have card_g_le_b: "card (g ` R f) \<le> card {..<b}"
      unfolding card_g_R using True by simp

    have "?L1 \<le> measure \<Psi>\<^sub>3 {h. \<bar>B.Y h - B.\<mu>\<bar> > 9 * real (card (g ` R f)) / sqrt (card {..<b})}"
    proof (rule pmf_mono)
      fix h assume "h \<in> {h. E\<^sub>1 (f,g,h) \<and> E\<^sub>2 (f,g,h) \<and> E\<^sub>3 (f,g,h) \<and> \<not>E\<^sub>4 (f,g,h)}"
      hence b: "\<bar>p (f,g,h) -\<rho> (card (R f))\<bar> >  \<epsilon>/12 * card (R f)"
        unfolding E\<^sub>4_def by simp
      assume "h \<in> set_pmf (sample_pmf \<Psi>\<^sub>3)"
      hence h_range: "h x < b" for x
        unfolding sample_space_alt[OF \<Psi>\<^sub>3.sample_space,symmetric] using h_range_1 by simp

      have "{j \<in> {..<b}. int (s f) \<le> \<tau>\<^sub>1 (f, g, h) A 0 j} =
        {j \<in> {..<b}. int (s f) \<le> max (Max ({int (f a) |a. a \<in> A \<and> h (g a) = j} \<union> {-1})) (- 1)}"
        unfolding \<tau>\<^sub>1_def by simp
      also have "... = {j \<in> {..<b}. int (s f) \<le> Max ({int (f a) |a. a \<in> A \<and> h (g a) = j} \<union> {-1})}"
        using fin_A by (subst max_absorb1) (auto intro: Max_ge)
      also have "... = {j \<in> {..<b}. (\<exists>a \<in> R f. h (g a) = j)}"
        unfolding R_def using fin_A by (subst Max_ge_iff) auto
      also have "... = {j. \<exists>a \<in> R f. h (g a) = j}"
        using h_range by auto
      also have "... = (h \<circ> g) ` (R f)"
        by (auto simp add:set_eq_iff image_iff)
      also have "... = h ` (g ` (R f))"
        by (simp add:image_image)
      finally have c:"{j \<in> {..<b}. int (s f) \<le> \<tau>\<^sub>1 (f, g, h) A 0 j} = h ` (g ` R f)"
        by simp
      have "9 * real (card (g ` R f)) / sqrt (card {..<b}) = 9/ sqrt b * real (card (R f))"
        using card_image[OF g_inj] by simp
      also have "... \<le>  \<epsilon>/12 * card (R f)"
        by (intro mult_right_mono e_4_h) simp
      also have "... < \<bar>B.Y h - B.\<mu>\<bar>"
        using b c unfolding B.Y_def p_def b_mu by simp
      finally show "h \<in> {h. \<bar>B.Y h - B.\<mu>\<bar> >  9 * real (card (g ` R f)) / sqrt (card {..<b})}"
        by simp
    qed
    also have "... \<le> 1/2^6"
      using k_min
      by (intro B.devitation_bound[OF card_g_le_b lim_balls_and_bins]) auto
    finally show ?thesis by simp
  next
    case False
    have "?L1 \<le> measure \<Psi>\<^sub>3 {}"
    proof (rule pmf_mono)
      fix h assume b:"h \<in> {h. E\<^sub>1 (f, g, h) \<and> E\<^sub>2 (f, g, h) \<and> E\<^sub>3 (f, g, h) \<and> \<not> E\<^sub>4 (f, g, h)}"
      hence "card (R f) \<le> (2/3)*b"
        by (auto intro!: R_bound[simplified])
      hence "card (R f) \<le> b"
        by simp
      moreover have "inj_on g (R f)"
        using b by (simp add:E\<^sub>3_def)
      ultimately have "False" using False by simp
      thus "h \<in> {}" by simp
    qed
    also have "... = 0" by simp
    finally show ?thesis by simp
  qed

  have "?L = (\<integral>f. (\<integral>g.
    measure \<Psi>\<^sub>3 {h. E\<^sub>1 (f,g,h) \<and> E\<^sub>2 (f,g,h) \<and> E\<^sub>3 (f,g,h) \<and> \<not>E\<^sub>4 (f,g,h)} \<partial>\<Psi>\<^sub>2) \<partial>\<Psi>\<^sub>1)"
    unfolding sample_pmf_\<Psi> split_pair_pmf by simp
  also have "... \<le> (\<integral>f. (\<integral>g.  1/2^6  \<partial>\<Psi>\<^sub>2) \<partial>\<Psi>\<^sub>1)"
    using a \<Psi>\<^sub>1.sample_space \<Psi>\<^sub>2.sample_space
    by (intro integral_mono_AE AE_pmfI) simp_all
  also have "... = 1/2^6"
    by simp
  finally show ?thesis by simp
qed

lemma \<rho>_inverse: "\<rho>_inv (\<rho> x) = x"
proof -
  have a:"1-1/b \<noteq> 0"
    using b_min by simp

  have "\<rho> x = b * (1-(1-1/b) powr x)"
    unfolding \<rho>_def by simp
  hence "\<rho> x / real b = 1-(1-1/b) powr x" by simp
  hence "ln (1 - \<rho> x / real b) = ln ((1-1/b) powr x)" by simp
  also have "... = x * ln (1 - 1/ b)"
    using a by (intro ln_powr)
  finally have "ln (1 - \<rho> x / real b) = x * ln (1- 1/ b)"
    by simp
  moreover have "ln (1-1/b) < 0"
    using b_min by (subst ln_less_zero_iff) auto
  ultimately show ?thesis
    using \<rho>_inv_def by simp
qed

lemma rho_mono:
  assumes "x \<le> y"
  shows "\<rho> x \<le> \<rho> y"
proof-
  have "(1 - 1 / real b) powr y \<le> (1 - 1 / real b) powr x"
    using b_min
    by (intro powr_mono_rev assms) auto
  thus ?thesis
    unfolding \<rho>_def by (intro mult_left_mono) auto
qed

lemma rho_two_thirds: "\<rho> (2/3 * b) \<le> 3/5 *b"
proof -
  have "1/3 \<le> exp ( - 13 / 12::real )"
    by (approximation 8)
  also have "... \<le> exp ( - 1 - 2 / real b )"
    using b_min by (intro iffD2[OF exp_le_cancel_iff]) (simp add:algebra_simps)
  also have "... \<le> exp ( b * (-(1/real b)-2*(1/real b)^2))"
    using b_min by (simp add:algebra_simps power2_eq_square)
  also have  "... \<le> exp ( b * ln (1-1/real b))"
    using b_min
    by (intro iffD2[OF exp_le_cancel_iff] mult_left_mono ln_one_minus_pos_lower_bound) auto
  also have "... = exp ( ln ( (1-1/real b) powr b))"
    using b_min by (subst ln_powr) auto
  also have "... = (1-1/real b) powr b"
    using b_min by (subst exp_ln) auto
  finally have a:"1/3 \<le> (1-1/real b) powr b" by simp

  have "2/5 \<le> (1/3) powr (2/3::real)"
    by (approximation 5)
  also have "... \<le> ((1-1/real b) powr b) powr (2/3)"
    by (intro powr_mono2 a) auto
  also have "... = (1-1/real b) powr (2/3 * real b)"
    by (subst powr_powr) (simp add:algebra_simps)
  finally have "2/5 \<le> (1 - 1 / real b) powr (2 / 3 * real b)" by simp
  hence "1 - (1 - 1 / real b) powr (2 / 3 * real b) \<le> 3/5"
    by simp
  hence "\<rho> (2/3 * b) \<le> b * (3/5)"
    unfolding \<rho>_def by (intro mult_left_mono) auto
  thus ?thesis
    by simp
qed

definition \<rho>_inv' :: "real \<Rightarrow> real"
  where "\<rho>_inv' x = -1 / (real b * (1-x / real b) * ln (1 - 1 / real b))"

lemma \<rho>_inv'_bound:
  assumes "x \<ge> 0"
  assumes "x \<le> 59/90*b"
  shows "\<bar>\<rho>_inv' x\<bar> \<le> 4"
proof -
  have c:"ln (1 - 1 / real b) < 0"
    using b_min
    by (subst ln_less_zero_iff) auto
  hence d:"real b * (1 - x / real b) * ln (1 - 1 / real b) < 0"
    using b_min assms by (intro Rings.mult_pos_neg) auto

  have "(1::real) \<le> 31/30" by simp
  also have "... \<le> (31/30) * (b * -(- 1 / real b))"
    using b_min by simp
  also have "... \<le> (31/30) * (b * -ln (1 + (- 1 / real b)))"
    using b_min
    by (intro mult_left_mono le_imp_neg_le  ln_add_one_self_le_self2) auto
  also have "... \<le> 3 * (31/90) * (- b * ln (1 - 1 / real b))"
    by simp
  also have "... \<le> 3 * (1 - x / real b) * (- b * ln (1 - 1 / real b))"
    using assms b_min pos_divide_le_eq[where c="b"] c
    by (intro mult_right_mono mult_left_mono mult_nonpos_nonpos) auto
  also have "... \<le> 3 * (real b * (1 - x / real b) * (-ln (1 - 1 / real b)))"
    by (simp add:algebra_simps)
  finally have "3 * (real b * (1 - x / real b) * (-ln (1 - 1 / real b))) \<ge> 1" by simp
  hence "3 * (real b * (1 - x / real b) * ln (1 - 1 / real b)) \<le> -1" by simp
  hence "\<rho>_inv' x \<le> 3"
    unfolding \<rho>_inv'_def using d
    by (subst neg_divide_le_eq) auto
  moreover have "\<rho>_inv' x > 0"
    unfolding \<rho>_inv'_def using d by (intro divide_neg_neg) auto
  ultimately show ?thesis by simp
qed

lemma \<rho>_inv':
  fixes x :: real
  assumes "x < b"
  shows "DERIV \<rho>_inv x :> \<rho>_inv' x"
proof -
  have "DERIV (ln \<circ> (\<lambda>x. (1 - x / real b))) x :> 1 / (1-x / real b) * (0 -1/b)"
    using assms b_min
    by (intro DERIV_chain DERIV_ln_divide DERIV_cdivide derivative_intros) auto
  hence "DERIV \<rho>_inv x :> (1 / (1-x / real b) * (-1/b)) / ln (1-1/real b)"
    unfolding comp_def \<rho>_inv_def by (intro DERIV_cdivide) auto
  thus ?thesis
    by (simp add:\<rho>_inv'_def algebra_simps)
qed

lemma accuracy_without_cutoff:
  "measure \<Psi> {(f,g,h). \<bar>Y (f,g,h) - real X\<bar> > \<epsilon> * X \<or> s f < q_max} \<le> 1/2^4"
  (is "?L \<le> ?R")
proof -
  have "?L \<le> measure \<Psi> {\<psi>. \<not>E\<^sub>1 \<psi> \<or>  \<not>E\<^sub>2 \<psi> \<or>  \<not>E\<^sub>3 \<psi> \<or>  \<not>E\<^sub>4 \<psi>}"
  proof (rule pmf_rev_mono)
    fix \<psi> assume "\<psi> \<in> set_pmf (sample_pmf \<Psi>)"
    obtain f g h where \<psi>_def: "\<psi> = (f,g,h)" by (metis prod_cases3)

    assume "\<psi> \<notin> {\<psi>. \<not> E\<^sub>1 \<psi> \<or> \<not> E\<^sub>2 \<psi> \<or> \<not> E\<^sub>3 \<psi> \<or> \<not> E\<^sub>4 \<psi>}"
    hence assms: "E\<^sub>1 (f,g,h)" "E\<^sub>2 (f,g,h)" "E\<^sub>3 (f,g,h)" "E\<^sub>4 (f,g,h)"
      unfolding \<psi>_def by auto

    define I :: "real set" where "I = {0..59/90*b}"

    have "p (f,g,h) \<le> \<rho> (card (R f)) + \<epsilon>/12 * card (R f)"
      using assms(4) E\<^sub>4_def unfolding abs_le_iff by simp
    also have "... \<le> \<rho>(2/3*b) + 1/12* (2/3*b)"
      using \<epsilon>_lt_1 R_bound[OF assms(1,2)]
      by (intro add_mono rho_mono mult_mono) auto
    also have "... \<le> 3/5 * b + 1/18*b"
      by (intro add_mono rho_two_thirds) auto
    also have "... \<le> 59/90 * b"
       by simp
    finally have "p (f,g,h) \<le> 59/90 * b" by simp
    hence p_in_I: "p (f,g,h) \<in> I"
      unfolding I_def by simp

    have "\<rho> (card (R f)) \<le> \<rho>(2/3 * b)"
      using  R_bound[OF assms(1,2)]
      by (intro rho_mono) auto
    also have "... \<le> 3/5 * b"
      using rho_two_thirds by simp
    also have "... \<le> b * 59/90" by simp
    finally have "\<rho> (card (R f)) \<le> b * 59/90" by simp
    moreover have "(1 - 1 / real b) powr (real (card (R f))) \<le> 1 powr (real (card (R f)))"
      using b_min by (intro powr_mono2) auto
    hence "\<rho> (card (R f)) \<ge> 0"
      unfolding \<rho>_def by (intro mult_nonneg_nonneg) auto
    ultimately have "\<rho> (card (R f)) \<in> I"
      unfolding I_def by simp

    moreover have "interval I"
      unfolding I_def interval_def by simp
    moreover have "59 / 90 * b < b"
      using b_min by simp
    hence "DERIV \<rho>_inv x :> \<rho>_inv' x" if "x \<in> I" for x
      using that I_def by (intro \<rho>_inv') simp
    ultimately obtain \<xi> :: real where \<xi>_def: "\<xi> \<in> I"
      "\<rho>_inv (p(f,g,h)) - \<rho>_inv (\<rho> (card (R f))) = (p (f,g,h) - \<rho>(card (R f))) * \<rho>_inv' \<xi>"
      using p_in_I MVT_interval by blast

    have "\<bar>\<rho>_inv(p (f,g,h)) - card (R f)\<bar> = \<bar>\<rho>_inv(p (f,g,h)) - \<rho>_inv(\<rho>(card (R f)))\<bar>"
      by (subst \<rho>_inverse) simp
    also have "... = \<bar>(p (f,g,h) - \<rho> (card (R f)))\<bar> * \<bar>\<rho>_inv' \<xi> \<bar>"
      using \<xi>_def(2) abs_mult by simp
    also have "... \<le> \<bar>p (f,g,h) - \<rho> (card (R f))\<bar> * 4"
      using \<xi>_def(1) I_def
      by (intro mult_left_mono \<rho>_inv'_bound) auto
    also have "... \<le> ( \<epsilon>/12 * card (R f)) * 4"
      using assms(4) E\<^sub>4_def by (intro mult_right_mono) auto
    also have "... = \<epsilon>/3 * card (R f)" by simp
    finally have b: "\<bar>\<rho>_inv(p (f,g,h)) - card (R f)\<bar> \<le> \<epsilon>/3 * card (R f)"  by simp

    have "\<bar>\<rho>_inv(p (f,g,h)) - X / 2 ^ (s f)\<bar> \<le>
      \<bar>\<rho>_inv(p (f,g,h)) - card (R f)\<bar> + \<bar>card (R f) - X / 2 ^ (s f)\<bar>"
      by simp
    also have "... \<le> \<epsilon>/3 * card (R f) + \<bar>card (R f) - X / 2 ^ (s f)\<bar>"
      by (intro add_mono b) auto
    also have "... =  \<epsilon>/3 * \<bar>X / 2 ^ (s f) + (card (R f) - X / 2 ^ (s f))\<bar> +
      \<bar>card (R f) - X / 2 ^ (s f)\<bar>" by simp
    also have "... \<le>  \<epsilon>/3 * (\<bar>X / 2 ^ (s f)\<bar> + \<bar>card (R f) - X / 2 ^ (s f)\<bar>) +
      \<bar>card (R f) - X / 2 ^ (s f)\<bar>"
      using \<epsilon>_gt_0 by (intro mult_left_mono add_mono abs_triangle_ineq) auto
    also have "... \<le>  \<epsilon>/3 * \<bar>X / 2 ^ (s f)\<bar> + (1+  \<epsilon>/3) * \<bar>card (R f) - X / 2 ^ (s f)\<bar>"
      using \<epsilon>_gt_0 \<epsilon>_lt_1 by (simp add:algebra_simps)
    also have "... \<le>  \<epsilon>/3 * \<bar>X / 2 ^ s f\<bar> + (4/3) * ( \<epsilon> / 3 * real X / 2 ^ s f)"
      using assms(2) \<epsilon>_gt_0 \<epsilon>_lt_1
      unfolding E\<^sub>2_def by (intro add_mono mult_mono) auto
    also have "... = (7/9) * \<epsilon> * real X / 2^s f"
      using X_ge_1 by (subst abs_of_nonneg) auto
    also have "... \<le> 1 * \<epsilon> * real X / 2^s f"
      using \<epsilon>_gt_0 by (intro mult_mono divide_right_mono) auto
    also have "... =  \<epsilon> * real X / 2^s f" by simp
    finally have a:"\<bar>\<rho>_inv(p (f,g,h)) - X / 2 ^ (s f)\<bar> \<le> \<epsilon> * X / 2 ^ (s f)"
      by simp

    have "\<bar>Y (f, g, h) - real X\<bar> = \<bar>2 ^ (s f)\<bar> * \<bar>\<rho>_inv(p (f,g,h)) - real X / 2 ^ (s f)\<bar>"
      unfolding Y_def by (subst abs_mult[symmetric]) (simp add:algebra_simps powr_add[symmetric])
    also have "... \<le> 2 ^ (s f) * (\<epsilon> * X / 2 ^ (s f))"
      by (intro mult_mono a) auto
    also have "... = \<epsilon> * X"
      by (simp add:algebra_simps powr_add[symmetric])
    finally have "\<bar>Y (f, g, h) - real X\<bar> \<le> \<epsilon> * X" by simp
    moreover have "2 powr (\<lceil>log 2 (real X)\<rceil> - t f) \<le> 2 powr b_exp" (is "?L1 \<le> ?R1")
    proof -
      have "?L1 \<le> 2 powr (1 + log 2 (real X)- t f)"
        by (intro powr_mono, linarith) auto
      also have "... = 2 powr 1 * 2 powr (log 2 (real X)) * 2 powr (- t f)"
        unfolding powr_add[symmetric] by simp
      also have "... = 2 * (2 powr (-t f) * X)"
        using X_ge_1 by simp
      also have "... \<le> 2 * (b/2)"
        using assms(1) unfolding E\<^sub>1_def by (intro mult_left_mono) auto
      also have "... = b" by simp
      also have "... = ?R1"
        unfolding b_def by (simp add: powr_realpow)
      finally show ?thesis by simp
    qed
    hence "\<lceil>log 2 (real X)\<rceil> - t f \<le> real b_exp"
      unfolding not_less[symmetric] using powr_less_mono[where x="2"] by simp
    hence "s f \<ge> q_max" unfolding s_def q_max_def by (intro nat_mono) auto
    ultimately show "\<psi> \<notin> {(f, g, h). \<epsilon> * X < \<bar>Y (f, g, h) - real X\<bar> \<or> s f < q_max}"
      unfolding \<psi>_def by auto
  qed
  also have "... \<le>
    measure \<Psi> {\<psi>. \<not>E\<^sub>1 \<psi> \<or> \<not>E\<^sub>2 \<psi> \<or> \<not>E\<^sub>3 \<psi>} + measure \<Psi> {\<psi>. E\<^sub>1 \<psi> \<and> E\<^sub>2 \<psi> \<and> E\<^sub>3 \<psi> \<and> \<not>E\<^sub>4 \<psi>}"
    by (intro pmf_add) auto
  also have "... \<le> (measure \<Psi> {\<psi>. \<not>E\<^sub>1 \<psi> \<or> \<not>E\<^sub>2 \<psi>} + measure \<Psi> {\<psi>. E\<^sub>1 \<psi> \<and> E\<^sub>2 \<psi> \<and> \<not>E\<^sub>3 \<psi>}) + 1/2^6"
    by (intro add_mono e_4 pmf_add) auto
  also have "... \<le> ((measure \<Psi> {\<psi>. \<not>E\<^sub>1 \<psi>} + measure \<Psi> {\<psi>. E\<^sub>1 \<psi> \<and> \<not>E\<^sub>2 \<psi>}) + 1/2^6) + 1/2^6"
    by (intro add_mono e_3 pmf_add) auto
  also have "... \<le> ((1/2^6 + 1/2^6) + 1/2^6) + 1/2^6"
    by (intro add_mono e_2 e_1) auto
  also have "... = ?R" by simp
  finally show ?thesis by simp
qed

end

end
