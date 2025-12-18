theory Discrete_UCB_Step3
  imports Discrete_UCB_Step2

begin


locale bandit_policy = bandit_problem + prob_space +
  fixes
    \<Omega> :: "'b set"
    and \<F> :: "'b set set"
    and \<pi> :: "nat \<Rightarrow> 'b \<Rightarrow> 'a"
    and N_n :: "nat \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> nat"
    and Z :: "nat \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> real"
    and \<delta> :: real
    and q :: real
  assumes  fin_A: "finite A"
    and "\<omega> \<in> \<Omega>"
    and a_in_A: "a \<in> A" 
    and measurable_policy: "\<forall>t. \<pi> t \<in> measurable M (count_space A)" 
    and N_n_def: "\<forall>n a \<omega>. N_n n a \<omega> = card {t \<in> {0..<n}. \<pi> (t+1) \<omega> = a}"
    and count_assm_pointwise: "\<forall>n \<omega>. (\<Sum>a \<in> A. real (N_n n a \<omega>)) = real n" 
    and delta_pos: "0 < \<delta>"
    and delta_less1: "\<delta> < 1"
    and q_pos: "q > 0" 

begin

definition sample_mean_Z :: "nat \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> real" where
  "sample_mean_Z n a \<omega> = (1 / real n) * (\<Sum>i<n. Z i a \<omega>)"

definition M_fun :: "nat \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> real" where
  "M_fun t a \<omega> = (if N_n (t+1) a \<omega> = 0 then 0
             else (\<Sum> s < t. (if \<pi> s \<omega> = a then Z s a \<omega> else 0)) / real (N_n t a \<omega>))"

definition U :: "nat \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> real" where
  "U t a \<omega> = M_fun t a \<omega> + q * sqrt (ln (1 / \<delta>) / (2 * real (max 1 (N_n t a \<omega>))))"

definition A_t_plus_1 :: "nat \<Rightarrow> 'b \<Rightarrow> 'a" where
  "A_t_plus_1 t \<omega> = (SOME a. a \<in> A \<and> (\<forall>a'. a' \<in> A \<longrightarrow> U t a \<omega> \<ge> U t a' \<omega>))"

definition prob_eq_Ex :: "'b set \<Rightarrow> bool" where
  "prob_eq_Ex E \<equiv> prob E = expectation (\<lambda>\<omega>. indicator E \<omega>)"


theorem proposition_15_7:
  assumes
    a_in_A: "a \<in> A"
    and "\<omega> \<in> \<Omega>"
    and subopt_gap: "\<Delta> a > 0"
    and a_not_opt: "\<exists> a' \<in> A. \<Delta> a' > 0"
    and delta_a: "\<forall> a \<in> A. \<Delta> a = \<mu> a_star - \<mu> a"
    and "k \<le> n"
    and from_UCB_step1: "\<forall> a \<in> A. expectation (\<lambda>\<omega>. real (N_n n a \<omega>)) \<le>
       s n + expectation (\<lambda>\<omega>. (\<Sum> t = k..<n. if \<pi> (t+1) \<omega> = a \<and> s t \<le> real (N_n t a \<omega>) then 1 else 0))"
    and from_UCB_step2: "\<forall> a \<in> A.  \<forall> t \<in> {k..<n}. prob ({\<omega> \<in> \<Omega>. A_t_plus_1 t \<omega> = a} \<inter>
                            {\<omega> \<in> \<Omega>. N_n t a \<omega> \<ge> (2 * ln (1 / \<delta>)) / (\<Delta> a)^2}) \<le> 2 * \<delta>"
    and eps_pos: "\<epsilon> > 0"
    and t_gt0: "\<forall> t \<in> {k..<n}. t > 0"
    and choice_delta: "\<forall> t \<in> {k..<n}. \<delta> = 1 / (real t powr \<epsilon>)"
    and s_form: "\<forall> a \<in> A. \<forall> u. s u = (2 * \<epsilon> * ln (real u)) / ((\<Delta> a)^2)"
    and subset_meas:"\<forall> a \<in> A. \<forall>t \<in> {k..<n}. \<forall>\<omega> \<in> \<Omega>. {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t)/(\<Delta> a)^2 \<le> N_n t a \<omega>} \<subseteq> \<Omega>"
    and  prob_eq_E_assm: "\<forall> a \<in> A. \<forall>t \<in> {k..<n}. prob {\<omega>. \<pi> (Suc t) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)} =
                   prob ({\<omega>. \<pi> (Suc t) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)} \<inter> space M)"
    and finiteness: "\<forall>t\<in>{k..<n}. \<forall>a\<in>A. emeasure M {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2*\<epsilon>*ln(real t)/(\<Delta> a)^2 \<le> real (N_n t a \<omega>)} < \<infinity>" 
    and measurable_set: "\<forall>t\<in>{k..<n}. \<forall>a\<in>A. {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2*\<epsilon>*ln(real t)/(\<Delta> a)^2 \<le> real (N_n t a \<omega>)} \<in> sets M"

    and eq_sets_optimum:
         "\<forall> a \<in> A. \<forall> t \<in> {k..<n}. {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)} =
                  {\<omega> \<in> \<Omega>. A_t_plus_1 t \<omega> = a} \<inter> {\<omega> \<in> \<Omega>. N_n t a \<omega> \<ge> (2 * \<epsilon> * ln (real t)) / (\<Delta> a)^2}"

shows
  "\<forall> a \<in> A.  expectation (\<lambda>\<omega>. real (N_n n a \<omega>)) \<le> s n + (\<Sum> t = k..<n. 2 / (real t powr \<epsilon>))"

proof -

  have def_sn: "\<forall> a \<in> A. s n = (2 * \<epsilon> * ln (real n)) / ((\<Delta> a)^2)"
    using s_form by simp

  have def_st: "\<forall> a \<in> A. s t =  (2 * \<epsilon> * ln (real t)) / ((\<Delta> a)^2)" 
    using s_form by simp

  then have expression:  "\<forall> a \<in> A. expectation (\<lambda>\<omega>. real (N_n n a \<omega>)) \<le> 
    (2 * \<epsilon> * ln (real n)) / ((\<Delta> a)^2) + expectation (\<lambda>\<omega>. (\<Sum>t = k..<n.  if \<pi> (t+1) \<omega> = a \<and> 
 (2 * \<epsilon> * ln (real t)) / ((\<Delta> a)^2) \<le> real (N_n t a \<omega>) then 1 else 0))" 
    using assms def_sn def_st by simp

  have eq_if_of_bool:
    "\<forall> a \<in> A. expectation (\<lambda>\<omega>. \<Sum> t = k..<n.
     (if \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>) then 1 else 0))
  = expectation (\<lambda>\<omega>. \<Sum> t = k..<n.
      of_bool (\<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)))"
    by (simp add: of_bool_def)

  have eq_indic_bool:
    "\<forall> a \<in> A. expectation (\<lambda>\<omega>. \<Sum> t = k..<n.
      of_bool (\<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)))
   = expectation (\<lambda>\<omega>. \<Sum> t = k..<n.
       indicat_real {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)} \<omega>)"
    by (simp add: indicator_def of_bool_def)

  have expression_1: 
    "\<forall> a \<in> A. expectation (\<lambda>\<omega>. \<Sum> t = k..<n.
      (if \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>) then 1 else 0)) = 
   expectation (\<lambda>\<omega>. \<Sum> t = k..<n.
      indicat_real {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)} \<omega>)"
  proof
    fix a assume "a \<in> A"
    from eq_if_of_bool[rule_format, OF `a \<in> A`] 
    have eq1: "expectation (\<lambda>\<omega>. \<Sum> t = k..<n.
         (if \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>) then 1 else 0)) =
       expectation (\<lambda>\<omega>. \<Sum> t = k..<n.
         of_bool (\<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)))"
      by simp

    from eq_indic_bool[rule_format, OF `a \<in> A`] 
    have eq2: "expectation (\<lambda>\<omega>. \<Sum> t = k..<n.
         of_bool (\<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>))) =
       expectation (\<lambda>\<omega>. \<Sum> t = k..<n.
         indicat_real {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)} \<omega>)"
      by simp

    from eq1 eq2 show 
      "expectation (\<lambda>\<omega>. \<Sum> t = k..<n.
        (if \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>) then 1 else 0)) =
     expectation (\<lambda>\<omega>. \<Sum> t = k..<n.
        indicat_real {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)} \<omega>)"
      by (rule trans)
  qed

  have res:"\<forall> a \<in> A. \<forall>t \<in> {k..<n}. prob_eq_Ex {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)}"
    using assms prob_eq_Ex_def by auto

  have lin_of_expect_indicators:
    "\<forall> a \<in> A. \<forall>t \<in> {k..<n}.  prob {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)} =
   expectation (\<lambda>\<omega>. (indicat_real {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)} \<omega>))"
    using  prob_eq_Ex_def res by simp

  then have key_result_1: "\<forall> a \<in> A. (\<Sum>t = k..<n. 
expectation (\<lambda>\<omega>. (indicat_real {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)} \<omega>)))
 = (\<Sum>t = k..<n. prob {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)})"
    using  lin_of_expect_indicators by simp

  have expression_follow_up: "\<forall> a \<in> A. 
  expectation (\<lambda>\<omega>. \<Sum> t = k..<n. (if \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>) then 1 else 0)) =
  (\<Sum> t = k..<n. prob {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)})"
  proof -
    have res1: "\<forall> a \<in> A. 
  expectation (\<lambda>\<omega>. \<Sum> t = k..<n. (if \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>) then 1 else 0)) = 
 expectation (\<lambda>\<omega>. \<Sum> t = k..<n.
      of_bool (\<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)))"
      using eq_if_of_bool by simp

    have res2:"\<forall> a \<in> A. 
  expectation (\<lambda>\<omega>. \<Sum> t = k..<n. (if \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>) then 1 else 0)) = 
expectation (\<lambda>\<omega>. \<Sum> t = k..<n. indicat_real {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)} \<omega>)" 
      using expression_1 by simp

    have res3: "\<forall> a \<in> A. 
  expectation (\<lambda>\<omega>. \<Sum> t = k..<n. (if \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>) then 1 else 0)) = 
( \<Sum> t = k..<n. expectation (\<lambda>\<omega>. indicat_real {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)} \<omega>))" 
    proof -

      have "\<forall> a \<in> A. 
  expectation (\<lambda>\<omega>. \<Sum> t = k..<n. (if \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>) then 1 else 0)) = 
expectation (\<lambda>\<omega>. \<Sum> t = k..<n. indicat_real {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)} \<omega>)" 
        using res2 by blast
      then have "\<forall> a \<in> A.  expectation (\<lambda>\<omega>. \<Sum> t = k..<n. indicat_real {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)} \<omega>) = 
integral\<^sup>L M (\<lambda>\<omega>. \<Sum> t = k..<n. indicat_real {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)} \<omega>)"
        by simp
      then have result_intermed:"\<forall> a \<in> A.  expectation (\<lambda>\<omega>. \<Sum> t = k..<n. indicat_real {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)} \<omega>) = 
( \<Sum> t = k..<n. integral\<^sup>L M (\<lambda>\<omega>. indicat_real {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)} \<omega>))"
        using assms integral_sum by simp

      have result: "\<forall> a \<in> A.  expectation (\<lambda>\<omega>. \<Sum> t = k..<n. indicat_real {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> *
ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)} \<omega>) = 
( \<Sum> t = k..<n. expectation (\<lambda>\<omega>. indicat_real {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)} \<omega>))"
        using result_intermed by auto
      have "\<forall> a \<in> A. 
  expectation (\<lambda>\<omega>. \<Sum> t = k..<n. (if \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>) then 1 else 0)) = 
expectation (\<lambda>\<omega>. \<Sum> t = k..<n. indicat_real {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)} \<omega>)" 
        using res2 by simp
      then have linearity_expectation: "\<forall> a \<in> A. 
  expectation (\<lambda>\<omega>. \<Sum> t = k..<n. (if \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>) then 1 else 0)) = 
( \<Sum> t = k..<n. expectation (\<lambda>\<omega>. indicat_real {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)} \<omega>))" 
        using result by simp

      then show ?thesis using linearity_expectation by simp
    qed

    have  final_linearity:"\<forall> a \<in> A. 
  expectation (\<lambda>\<omega>. \<Sum> t = k..<n. (if \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>) then 1 else 0)) = 
  (\<Sum>t = k..<n. prob {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)})"
      using res1 res2 res3 key_result_1 by simp
    then show ?thesis using final_linearity by simp
  qed

  have intermed_result: "\<forall> a \<in> A. 
  expectation (\<lambda>\<omega>. real (N_n n a \<omega>)) \<le> 
    (2 * \<epsilon> * ln (real n)) / (\<Delta> a)^2 + 
    (\<Sum> t = k..<n. prob {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)})"
    using expression_follow_up expression by simp

  then have follow_up_result: "\<forall> a \<in> A. \<forall> t \<in> {k..<n}. 
  prob {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)} =
  prob ({\<omega> \<in> \<Omega>. A_t_plus_1 t \<omega> = a} \<inter> {\<omega> \<in> \<Omega>. N_n t a \<omega> \<ge> (2 * \<epsilon> * ln (real t)) / (\<Delta> a)^2})"
    using expression_follow_up expression eq_sets_optimum intermed_result by simp 

  have next_result_sum_prob: "\<forall> a \<in> A. 
  (\<Sum> t = k..<n. prob {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)}) =
  (\<Sum> t = k..<n. prob ({\<omega> \<in> \<Omega>. A_t_plus_1 t \<omega> = a} \<inter> {\<omega> \<in> \<Omega>. N_n t a \<omega> \<ge> (2 * \<epsilon> * ln (real t)) / (\<Delta> a)^2}))"
    using assms follow_up_result by simp

  then have next_result_fin: "\<forall> a \<in> A. 
  expectation (\<lambda>\<omega>. real (N_n n a \<omega>)) \<le> 
    (2 * \<epsilon> * ln (real n)) / (\<Delta> a)^2 + 
    (\<Sum> t = k..<n. prob ({\<omega> \<in> \<Omega>. A_t_plus_1 t \<omega> = a} \<inter> {\<omega> \<in> \<Omega>. N_n t a \<omega> \<ge> (2 * \<epsilon> * ln (real t)) / (\<Delta> a)^2}))"
    using expression_follow_up next_result_sum_prob expression by fastforce

  have generalized_bound:
    "\<forall> a \<in> A. \<forall> t \<in> {k..<n}. prob ({\<omega> \<in> \<Omega>. A_t_plus_1 t \<omega> = a} \<inter>
                        {\<omega> \<in> \<Omega>. N_n t a \<omega> \<ge> (2 * \<epsilon> * ln (real t)) / (\<Delta> a)^2}) \<le> 2 / (real t powr \<epsilon>)"
  proof
    fix a
    assume a_in: "a \<in> A"
    show "\<forall> t \<in> {k..<n}. prob ({\<omega> \<in> \<Omega>. A_t_plus_1 t \<omega> = a} \<inter> {\<omega> \<in> \<Omega>. N_n t a \<omega> \<ge> (2 * \<epsilon> * ln (real t)) / (\<Delta> a)^2}) \<le> 2 / (real t powr \<epsilon>)"
    proof
      fix t
      assume t_in: "t \<in> {k..<n}"
      have Hprob:
        "prob ({\<omega> \<in> \<Omega>. A_t_plus_1 t \<omega> = a} \<inter>
         {\<omega> \<in> \<Omega>. N_n t a \<omega> \<ge> (2 * ln (1 / \<delta>)) / (\<Delta> a)^2}) \<le> 2 * \<delta>"
        using from_UCB_step2[rule_format, OF a_in t_in] by blast

      have ln_eq: "ln (1 / \<delta>) = \<epsilon> * ln (real t)"
        using choice_delta[rule_format, OF t_in] eps_pos by simp

      hence threshold_eq:
        "(2 * ln (1 / \<delta>)) / (\<Delta> a)^2 = (2 * \<epsilon> * ln (real t)) / (\<Delta> a)^2"
        by simp

      hence set_eq:
        "{\<omega> \<in> \<Omega>. N_n t a \<omega> \<ge> (2 * ln (1 / \<delta>)) / (\<Delta> a)^2} =
       {\<omega> \<in> \<Omega>. N_n t a \<omega> \<ge> (2 * \<epsilon> * ln (real t)) / (\<Delta> a)^2}"
        by auto

      from Hprob set_eq have
        "prob ({\<omega> \<in> \<Omega>. A_t_plus_1 t \<omega> = a} \<inter>
            {\<omega> \<in> \<Omega>. N_n t a \<omega> \<ge> (2 * \<epsilon> * ln (real t)) / (\<Delta> a)^2}) \<le> 2 * \<delta>"
        by simp

      moreover from choice_delta[rule_format, OF t_in] have "2 * \<delta> = 2 / (real t powr \<epsilon>)"
        by simp

      ultimately show
        "prob ({\<omega> \<in> \<Omega>. A_t_plus_1 t \<omega> = a} \<inter>
            {\<omega> \<in> \<Omega>. N_n t a \<omega> \<ge> (2 * \<epsilon> * ln (real t)) / (\<Delta> a)^2}) \<le> 2 / (real t powr \<epsilon>)"
        by simp
    qed
  qed

  have sum_mono_expression:
    "\<forall> a \<in> A. (\<Sum> t = k..<n. prob ({\<omega> \<in> \<Omega>. A_t_plus_1 t \<omega> = a} \<inter>
                       {\<omega> \<in> \<Omega>. N_n t a \<omega> \<ge> (2 * \<epsilon> * ln (real t)) / (\<Delta> a)^2})) 
   \<le> (\<Sum> t = k..<n. 2 / (real t powr \<epsilon>))"
  proof
    fix a
    assume a_in: "a \<in> A"
    show "(\<Sum> t = k..<n. prob ({\<omega> \<in> \<Omega>. A_t_plus_1 t \<omega> = a} \<inter> {\<omega> \<in> \<Omega>. N_n t a \<omega> \<ge> (2 * \<epsilon> * ln (real t)) / (\<Delta> a)^2})) 
   \<le> (\<Sum> t = k..<n. 2 / (real t powr \<epsilon>))"
      using generalized_bound a_in by (intro sum_mono) auto
  qed

  have final_result:
    "\<forall> a \<in> A. expectation (\<lambda>\<omega>. real (N_n n a \<omega>))
         \<le> (2 * \<epsilon> * ln (real n)) / ((\<Delta> a)^2) + (\<Sum> t = k..<n. 2 / (real t powr \<epsilon>))"
  proof
    fix a
    assume a_in: "a \<in> A"
    from next_result_fin[rule_format, OF a_in]
    have bound1:
      "expectation (\<lambda>\<omega>. real (N_n n a \<omega>))
       \<le> (2 * \<epsilon> * ln (real n)) / ((\<Delta> a)^2)
           + (\<Sum> t = k..<n. prob ({\<omega> \<in> \<Omega>. A_t_plus_1 t \<omega> = a}
                                   \<inter> {\<omega> \<in> \<Omega>. N_n t a \<omega> \<ge> (2 * \<epsilon> * ln (real t)) / ((\<Delta> a)^2)}))"
      by simp
    moreover from sum_mono_expression[rule_format, OF a_in]
    have bound2:
      "(\<Sum> t = k..<n. prob ({\<omega> \<in> \<Omega>. A_t_plus_1 t \<omega> = a}
                           \<inter> {\<omega> \<in> \<Omega>. N_n t a \<omega> \<ge> (2 * \<epsilon> * ln (real t)) / ((\<Delta> a)^2)}))
     \<le> (\<Sum> t = k..<n. 2 / (real t powr \<epsilon>))"
      by simp
    ultimately show
      "expectation (\<lambda>\<omega>. real (N_n n a \<omega>))
       \<le> (2 * \<epsilon> * ln (real n)) / ((\<Delta> a)^2) + (\<Sum> t = k..<n. 2 / (real t powr \<epsilon>))"
      by auto
  qed

  show ?thesis using assms final_result by simp

qed

theorem theorem_15_4:
  assumes
    a_in_A: "a \<in> A"
    and "finite A"  and  "\<forall>a \<in> A. integrable M (\<lambda>\<omega>. real (N_n n a \<omega>))"
    and \<omega>_in_\<Omega>: "\<omega> \<in> \<Omega>"
    and subopt_gap: "\<forall> a \<in> A. \<Delta> a > 0"
    and a_not_opt: "\<exists> a' \<in> A. \<Delta> a' > 0"
    and delta_a: "\<forall> a \<in> A. \<Delta> a = \<mu> a_star - \<mu> a"
    and "k \<le> n"
    and n_count_assm_pointwise: "(\<Sum>a\<in>A. real (N_n n a \<omega>)) = real n"
    and expected_regret_prop_15_1: "expectation (\<lambda>\<omega>. R_n n \<omega>) = (\<Sum>a\<in>A. \<Delta> a * expectation (\<lambda>\<omega>. real (N_n n a \<omega>)))"
    and from_UCB_step1: "\<forall> a \<in> A. expectation (\<lambda>\<omega>. real (N_n n a \<omega>)) \<le>
       s n + expectation (\<lambda>\<omega>. (\<Sum> t = k..<n. if \<pi> (t+1) \<omega> = a \<and> s t \<le> real (N_n t a \<omega>) then 1 else 0))"
    and from_UCB_step2: "\<forall> a \<in> A.  \<forall> t \<in> {k..<n}. prob ({\<omega> \<in> \<Omega>. A_t_plus_1 t \<omega> = a} \<inter>
                            {\<omega> \<in> \<Omega>. N_n t a \<omega> \<ge> (2 * ln (1 / \<delta>)) / (\<Delta> a)^2}) \<le> 2 * \<delta>"
    and eps_pos: "\<epsilon> > 0"
    and t_gt0: "\<forall> t \<in> {k..<n}. t > 0"
    and choice_delta: "\<forall> t \<in> {k..<n}. \<delta> = 1 / (real t powr \<epsilon>)"
    and s_form: "\<forall> a \<in> A. \<forall> u. s u = (2 * \<epsilon> * ln (real u)) / ((\<Delta> a)^2)"
    and subset_meas:"\<forall> a \<in> A. \<forall>t \<in> {k..<n}. \<forall>\<omega> \<in> \<Omega>. {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t)/(\<Delta> a)^2 \<le> N_n t a \<omega>} \<subseteq> \<Omega>"
    and  prob_eq_E_assm: "\<forall> a \<in> A. \<forall>t \<in> {k..<n}. prob {\<omega>. \<pi> (Suc t) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)} =
                   prob ({\<omega>. \<pi> (Suc t) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)} \<inter> space M)"
    and finiteness: "\<forall>t\<in>{k..<n}. \<forall>a\<in>A. emeasure M {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2*\<epsilon>*ln(real t)/(\<Delta> a)^2 \<le> real (N_n t a \<omega>)} < \<infinity>" 
    and measurable_set: "\<forall>t\<in>{k..<n}. \<forall>a\<in>A. {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2*\<epsilon>*ln(real t)/(\<Delta> a)^2 \<le> real (N_n t a \<omega>)} \<in> sets M"

and eq_sets_optimum:
"\<forall> a \<in> A. \<forall> t \<in> {k..<n}. {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)} =
                  {\<omega> \<in> \<Omega>. A_t_plus_1 t \<omega> = a} \<inter> {\<omega> \<in> \<Omega>. N_n t a \<omega> \<ge> (2 * \<epsilon> * ln (real t)) / (\<Delta> a)^2}"
and assms_lin_expect: "\<forall> a \<in> A. expectation (\<lambda>\<omega>. \<Sum> t = k..<n.
        (if \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>) then 1 else 0)) =
      (\<Sum> t = k..<n. expectation (\<lambda>\<omega>. indicat_real {\<omega>. \<pi> (t+1) \<omega> = a \<and> 2 * \<epsilon> * ln (real t) / (\<Delta> a)^2 \<le> real (N_n t a \<omega>)} \<omega>))"
and mono_sum_sets:
" (\<forall>a \<in> A. \<Delta> a * expectation (\<lambda>\<omega>. real (N_n n a \<omega>)) \<le> \<Delta> a * (s n + (\<Sum> t = k..<n. 2 / (real t powr \<epsilon>)))) 
    \<Longrightarrow> (\<Sum>a \<in> A. \<Delta> a * expectation (\<lambda>\<omega>. real (N_n n a \<omega>))) \<le> 
(\<Sum>a \<in> A. \<Delta> a * (s n + (\<Sum> t = k..<n. 2 / (real t powr \<epsilon>))))"

shows "expectation (\<lambda>\<omega>. R_n n \<omega>) \<le> (\<Sum>a\<in>A. \<Delta> a * ((2 * \<epsilon> * ln (real n)) / 
((\<Delta> a)^2)+ (\<Sum> t = k..<n. 2 / (real t powr \<epsilon>))))" 
proof - 
  have exp_regret_eq:
    "expectation (\<lambda>\<omega>. R_n n \<omega>) = (\<Sum>a\<in>A. \<Delta> a * expectation (\<lambda>\<omega>. real (N_n n a \<omega>)))"
    using assms by fastforce

  have result_2: "\<forall> a \<in> A. expectation (\<lambda>\<omega>. real (N_n n a \<omega>)) 
                   \<le> s n + (\<Sum> t = k..<n. 2 / (real t powr \<epsilon>))"
    using assms proposition_15_7  by (smt (verit, ccfv_threshold) a_star_in_A)

  have intermed_step: "\<forall>a \<in> A. \<Delta> a * expectation (\<lambda>\<omega>. real (N_n n a \<omega>)) \<le> \<Delta> a * (s n + (\<Sum> t = k..<n. 2 / (real t powr \<epsilon>)))"
  proof
    fix a assume "a \<in> A"
    then have "expectation (\<lambda>\<omega>. real (N_n n a \<omega>)) \<le> s n + (\<Sum> t = k..<n. 2 / (real t powr \<epsilon>))"
      using result_2 by auto
    moreover have "0 < \<Delta> a"
      using assms subopt_gap \<open>a \<in> A\<close> by blast
    ultimately show "\<Delta> a * expectation (\<lambda>\<omega>. real (N_n n a \<omega>)) \<le> \<Delta> a * (s n + (\<Sum> t = k..<n. 2 / (real t powr \<epsilon>)))"
      using mult_left_mono by simp
  qed

  have intermed_step_2:"(\<Sum>a\<in>A. \<Delta> a * expectation (\<lambda>\<omega>. real (N_n n a \<omega>))) \<le> (\<Sum>a\<in>A. \<Delta> a * (s n + (\<Sum> t = k..<n. 2 / (real t powr \<epsilon>))))"
  proof -
    have res:"\<forall>a\<in>A. \<Delta> a * expectation (\<lambda>\<omega>. real (N_n n a \<omega>)) \<le> \<Delta> a * (s n + (\<Sum> t = k..<n. 2 / (real t powr \<epsilon>)))"
      using intermed_step by auto
    have res2:" (\<forall>a \<in> A. \<Delta> a * expectation (\<lambda>\<omega>. real (N_n n a \<omega>)) \<le> \<Delta> a * (s n + (\<Sum> t = k..<n. 2 / (real t powr \<epsilon>)))) 
  \<Longrightarrow> (\<Sum>a \<in> A. \<Delta> a * expectation (\<lambda>\<omega>. real (N_n n a \<omega>))) \<le> (\<Sum>a \<in> A. \<Delta> a * (s n + (\<Sum> t = k..<n. 2 / (real t powr \<epsilon>))))"
      using res assms by fastforce
    then have intermed_step: "(\<Sum>a\<in>A. \<Delta> a * expectation (\<lambda>\<omega>. real (N_n n a \<omega>))) \<le> (\<Sum>a\<in>A. \<Delta> a * (s n + (\<Sum> t = k..<n. 2 / (real t powr \<epsilon>))))"
      using res res2 by auto

    then show ?thesis using intermed_step by simp
  qed

  then have "expectation (\<lambda>\<omega>. R_n n \<omega>) \<le> (\<Sum>a\<in>A. \<Delta> a * (s n + (\<Sum> t = k..<n. 2 / (real t powr \<epsilon>))))" 
    using assms intermed_step_2 by linarith

  have "\<forall>a \<in> A. s n = (2 * \<epsilon> * ln (real n)) / ((\<Delta> a)^2)"
    using s_form by auto

  then have "expectation (\<lambda>\<omega>. R_n n \<omega>) \<le> (\<Sum>a\<in>A. \<Delta> a * ((2 * \<epsilon> * ln (real n)) / 
((\<Delta> a)^2)+ (\<Sum> t = k..<n. 2 / (real t powr \<epsilon>))))" 
    using assms intermed_step_2 by (metis a_star_in_A less_irrefl verit_minus_simplify(1)) 

  then show ?thesis by simp

qed


end 
end