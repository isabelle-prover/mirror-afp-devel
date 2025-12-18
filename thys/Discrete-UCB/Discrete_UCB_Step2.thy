theory Discrete_UCB_Step2
  imports "Discrete_UCB_Step1"

begin

locale bandit_policy = bandit_problem + prob_space  +
  fixes \<Omega> :: "'b set"
    and \<F> :: "'b set set"
    and \<omega> :: 'b 
  fixes  \<pi> :: "nat \<Rightarrow> 'b \<Rightarrow> 'a"
    and N_n :: "nat \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> nat"
    and Z :: "nat \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> real"
    and \<delta> :: real
    and q :: real
  assumes finite_A: "finite A"
    and a_in_A: "a \<in> A"
    and measurable_policy: "\<forall>t. \<pi> t \<in> measurable M (count_space A)"
    and N_n_def: "\<forall>n a b. N_n n a b = card {t \<in> {0..<n}. \<pi> (t+1) b = a}"
    and \<delta>_pos: "0 < \<delta>"
    and \<delta>_less1: "\<delta> < 1"
    and q_pos: "q > 0"

begin



definition sample_mean_Z :: "nat \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> real" where
  "sample_mean_Z n a b \<equiv> (1 / real n) * (\<Sum> i<n. Z i a b)"

definition M_val :: "nat \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> real" where
  "M_val t a b \<equiv> (if N_n (t+1) a b = 0 then 0
             else (\<Sum> s < t. if \<pi> s b = a then Z s a b else 0) / real (N_n t a b))"

definition U :: "nat \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> real" where
  "U t a b \<equiv> M_val t a b + q * sqrt (ln (1 / \<delta>) / (2 * real (max 1 (N_n t a b))))"


definition A_t_plus_1 :: "nat \<Rightarrow> 'b \<Rightarrow> 'a" where
  "A_t_plus_1 t b \<equiv> (SOME a. a \<in> A \<and> (\<forall>a'. a' \<in> A \<longrightarrow> U t a b \<ge> U t a' b))"

lemma (in finite_measure) finite_measure_mono:
  assumes "A \<subseteq> B" "B \<in>sets M" shows "measure M A \<le> measure M B"
  using emeasure_mono[OF assms] emeasure_real[of A] emeasure_real[of B] by (auto simp: measure_def)

theorem union_bound:
  fixes E F G :: "'b set"
  assumes "E \<subseteq> F \<union> G"
    and "E \<in> events" "F \<in> events" "G \<in> events"
  shows "prob E \<le> prob F + prob G"
proof -
  have "F \<union> G \<in> events"
    using assms(3,4) sets.Un by blast
  have "prob E \<le> prob (F \<union> G)"
    using assms local.finite_measure_mono by auto
  also have "prob (F \<union> G) \<le> prob F + prob G"
    using assms local.finite_measure_subadditive by blast
  finally show ?thesis .
qed

theorem hoeffding_iid_bound_ge_general:
  fixes a :: 'a and n :: nat and \<epsilon> :: real and \<mu>_hat :: real and l u :: real
  assumes a_in: "a \<in> A"
    and eps_pos: "\<epsilon> \<ge> 0"
    and bounds: "\<forall>i < n. \<forall>\<omega> \<in> \<Omega>. l \<le> Z i a \<omega> \<and> Z i a \<omega> \<le> u"
    and mu_def: "\<mu>_hat = (\<Sum> i < n. expectation (\<lambda>\<omega>. Z i a \<omega>))"
    and "u - l \<noteq> 0"
    and n_pos:  "n > 0" 
    and space_M: "space M = \<Omega>"
    and sets_M:  "sets M  = \<F>"
    and indep: "indep_vars (\<lambda>_. borel) (\<lambda>i. (\<lambda>\<omega>. Z i a \<omega>)) {i. i < n}"
    and rv: "\<forall>i<n. random_variable borel (\<lambda>\<omega>. Z i a \<omega>)"

shows "prob {\<omega> \<in> \<Omega>. (\<Sum> i < n. Z i a \<omega>) \<ge> \<mu>_hat + \<epsilon>}
         \<le> exp (- 2 * \<epsilon>^2 / (real n * (u - l)^2))"
proof -
  let ?I = "{i. i < n}"
  let ?X = "\<lambda>i. (\<lambda>\<omega>. Z i a \<omega>)"
  let ?a = "\<lambda>i. l"
  let ?b = "\<lambda>i. u"

  have finite_I: "finite ?I" by simp

(* AE bounds needed by Hoeffding *)
  have AE_bounds: "\<forall>i\<in>?I. AE \<omega> in M. ?a i \<le> ?X i \<omega> \<and> ?X i \<omega> \<le> ?b i"
  proof
    fix i assume iI: "i \<in> ?I"
    have "\<forall>\<omega>\<in>\<Omega>. l \<le> Z i a \<omega> \<and> Z i a \<omega> \<le> u" using bounds iI by simp
    thus "AE \<omega> in M. ?a i \<le> ?X i \<omega> \<and> ?X i \<omega> \<le> ?b i" 
      using assms by auto
  qed

(* Independence & boundedness setup for Hoeffding *)
  have indep_loc: "indep_interval_bounded_random_variables M ?I ?X ?a ?b" 
    by (standard; use finite_I indep AE_bounds in auto)

  from indep_loc
  have H: "Hoeffding_ineq M ?I ?X ?a ?b"
    by (rule Hoeffding_ineq.intro)

(* Widths squared sum *)
  have widths: "(\<Sum> i \<in> ?I. (?b i - ?a i)^2) = real n * (u - l)^2"
    by simp
  have widths_pos: "0 < (\<Sum> i \<in> ?I. (?b i - ?a i)^2)"
    using \<open>u - l \<noteq> 0\<close> n_pos by simp
  have sum_expectations_eq_integrals:
    "(\<Sum> i < n. expectation (\<lambda>\<omega>. Z i a \<omega>)) = (\<Sum> i\<in>?I. integral\<^sup>L M (?X i))"
  proof -
    have eq1: "\<forall>i<n. expectation (\<lambda>\<omega>. Z i a \<omega>) = integral\<^sup>L M (?X i)"
      using rv space_M sets_M by simp
    moreover have  sum_eq: "(\<Sum> i<n. integral\<^sup>L M (?X i)) = (\<Sum> i\<in>?I. integral\<^sup>L M (?X i))"
      by (simp add: lessThan_def)
    ultimately show ?thesis
      by simp
  qed

(* Rewrite sum of expectations as integrals *)
  have sum_integrals_eq: "(\<Sum> i\<in>?I. integral\<^sup>L M (?X i)) = \<mu>_hat"
    using mu_def by (simp add: sum_expectations_eq_integrals) 

(* Apply Hoeffding inequality *)
  have tail:
    "prob {\<omega> \<in> \<Omega>. (\<Sum> i\<in>?I. ?X i \<omega>) - (\<Sum> i\<in>?I. integral\<^sup>L M (?X i)) \<ge> \<epsilon>} 
     \<le> exp (- 2 * \<epsilon>^2 / (\<Sum> i\<in>?I. (?b i - ?a i)^2))"
    using Hoeffding_ineq.Hoeffding_ineq_ge[OF H eps_pos widths_pos]
    by (smt (verit, best) Collect_cong assms(7))

(* Rewrite LHS and RHS to original statement *)
  have lhs_rewrite: "{\<omega> \<in> \<Omega>. (\<Sum> i < n. Z i a \<omega>) \<ge> \<mu>_hat + \<epsilon>} 
                     = {\<omega> \<in> \<Omega>. (\<Sum> i\<in>?I. ?X i \<omega>) - (\<Sum> i\<in>?I. integral\<^sup>L M (?X i)) \<ge> \<epsilon>}"
    by (simp add: add.commute le_diff_eq lessThan_def sum_integrals_eq) 

  have rhs_rewrite: "exp (- 2 * \<epsilon>^2 / (\<Sum> i\<in>?I. (?b i - ?a i)^2)) 
                     = exp (- 2 * \<epsilon>^2 / (real n * (u - l)^2))"
    using widths by simp

  show ?thesis
    using tail lhs_rewrite rhs_rewrite by simp
qed

theorem hoeffding_iid_bound_le_general:
  fixes a :: 'a and n :: nat and \<epsilon> :: real and \<mu>_hat :: real and l u :: real
  assumes a_in: "a \<in> A"
    and eps_pos: "\<epsilon> \<ge> 0"
    and bounds: "\<forall>i < n. \<forall>\<omega> \<in> \<Omega>. l \<le> Z i a \<omega> \<and> Z i a \<omega> \<le> u"
    and mu_def: "\<mu>_hat = (\<Sum> i < n. expectation (\<lambda>\<omega>. Z i a \<omega>))"
    and "u - l \<noteq> 0"
    and n_pos:  "n > 0" 
    and space_M: "space M = \<Omega>"
    and sets_M:  "sets M  = \<F>"
    and indep: "indep_vars (\<lambda>_. borel) (\<lambda>i. (\<lambda>\<omega>. Z i a \<omega>)) {i. i < n}"
    and rv: "\<forall>i<n. random_variable borel (\<lambda>\<omega>. Z i a \<omega>)"
  shows "prob {\<omega> \<in> \<Omega>. (\<Sum> i < n. Z i a \<omega>) \<le> \<mu>_hat - \<epsilon>} 
         \<le> exp (- 2 * \<epsilon>^2 / (real n * (u - l)^2))"
proof -
  let ?I = "{i. i < n}"
  let ?X = "\<lambda>i. (\<lambda>\<omega>. Z i a \<omega>)"
  let ?a = "\<lambda>i. l"
  let ?b = "\<lambda>i. u"

  have finite_I: "finite ?I" by simp

(* AE bounds *)
  have AE_bounds: "\<forall>i\<in>?I. AE \<omega> in M. ?a i \<le> ?X i \<omega> \<and> ?X i \<omega> \<le> ?b i"
  proof
    fix i assume iI: "i \<in> ?I"
    have "\<forall>\<omega>\<in>\<Omega>. l \<le> Z i a \<omega> \<and> Z i a \<omega> \<le> u" using bounds iI by simp
    thus "AE \<omega> in M. ?a i \<le> ?X i \<omega> \<and> ?X i \<omega> \<le> ?b i" 
      using assms by auto
  qed

(* Independence & boundedness *)
  have indep_loc: "indep_interval_bounded_random_variables M ?I ?X ?a ?b"
    by (standard; use finite_I indep AE_bounds in auto)

  from indep_loc
  have H: "Hoeffding_ineq M ?I ?X ?a ?b"
    by (rule Hoeffding_ineq.intro)

(* Widths sum *)
  have widths: "(\<Sum> i \<in> ?I. (?b i - ?a i)^2) = real n * (u - l)^2" by simp
  have widths_pos: "0 < (\<Sum> i \<in> ?I. (?b i - ?a i)^2)" using \<open>u - l \<noteq> 0\<close> n_pos by simp

(* Sum of expectations = sum of integrals *)
  have sum_expectations_eq_integrals:
    "(\<Sum> i < n. expectation (\<lambda>\<omega>. Z i a \<omega>)) = (\<Sum> i\<in>?I. integral\<^sup>L M (?X i))"
  proof -
    have eq1: "\<forall>i<n. expectation (\<lambda>\<omega>. Z i a \<omega>) = integral\<^sup>L M (?X i)" using rv space_M sets_M by simp
    moreover have sum_eq: "(\<Sum> i<n. integral\<^sup>L M (?X i)) = (\<Sum> i\<in>?I. integral\<^sup>L M (?X i))" by (simp add: lessThan_def)
    ultimately show ?thesis by simp
  qed

  have sum_integrals_eq: "(\<Sum> i\<in>?I. integral\<^sup>L M (?X i)) = \<mu>_hat"
    using mu_def by (simp add: sum_expectations_eq_integrals)

(* Apply Hoeffding inequality for \<le> *)
  have tail:
    "prob {\<omega> \<in> \<Omega>. (\<Sum> i\<in>?I. ?X i \<omega>) - (\<Sum> i\<in>?I. integral\<^sup>L M (?X i)) \<le> - \<epsilon>} 
     \<le> exp (- 2 * \<epsilon>^2 / (\<Sum> i\<in>?I. (?b i - ?a i)^2))"
    using Hoeffding_ineq.Hoeffding_ineq_le[OF H eps_pos widths_pos]
    by (smt (verit, best) Collect_cong assms(7)) 

(* Rewrite LHS and RHS *)
  have lhs_rewrite: "{\<omega> \<in> \<Omega>. (\<Sum> i < n. Z i a \<omega>) \<le> \<mu>_hat - \<epsilon>} 
                     = {\<omega> \<in> \<Omega>. (\<Sum> i\<in>?I. ?X i \<omega>) - (\<Sum> i\<in>?I. integral\<^sup>L M (?X i)) \<le> -\<epsilon>}"
    using add.inverse_inverse[of \<epsilon>] add.inverse_inverse[of \<mu>_hat] assms(4)
      cancel_ab_semigroup_add_class.diff_right_commute[of \<mu>_hat \<mu>_hat "\<Sum>uuc<n. Z uuc a _"]
      cancel_ab_semigroup_add_class.diff_right_commute[of "- \<mu>_hat" "- \<mu>_hat" "\<epsilon> - \<mu>_hat"]
      cancel_ab_semigroup_add_class.diff_right_commute[of "\<epsilon> - \<mu>_hat" "\<epsilon> - \<mu>_hat" \<epsilon>]
      cancel_ab_semigroup_add_class.diff_right_commute[of \<epsilon> \<epsilon> \<mu>_hat]
      cancel_ab_semigroup_add_class.diff_right_commute[of "0" "- \<mu>_hat" \<epsilon>]
      cancel_ab_semigroup_add_class.diff_right_commute[of \<mu>_hat \<mu>_hat \<epsilon>]
      cancel_ab_semigroup_add_class.diff_right_commute[of "- \<mu>_hat" "- \<mu>_hat" "(\<Sum>uuc<n. Z uuc a _) - \<mu>_hat"]
      cancel_ab_semigroup_add_class.diff_right_commute[of "(\<Sum>uuc<n. Z uuc a _) - \<mu>_hat" "(\<Sum>uuc<n. Z uuc a _) - \<mu>_hat"
        "\<Sum>uuc<n. Z uuc a _"]
      cancel_ab_semigroup_add_class.diff_right_commute[of "\<Sum>uuc<n. Z uuc a _" "\<Sum>uuc<n. Z uuc a _" \<mu>_hat]
      cancel_ab_semigroup_add_class.diff_right_commute[of "0" "- \<mu>_hat" "\<Sum>uuc<n. Z uuc a _"]
      cancel_comm_monoid_add_class.diff_cancel[of "\<epsilon> - \<mu>_hat"] cancel_comm_monoid_add_class.diff_cancel[of \<epsilon>]
      cancel_comm_monoid_add_class.diff_cancel[of \<mu>_hat] cancel_comm_monoid_add_class.diff_cancel[of "- \<mu>_hat"]
      cancel_comm_monoid_add_class.diff_cancel[of "(\<Sum>uuc<n. Z uuc a _) - \<mu>_hat"]
      cancel_comm_monoid_add_class.diff_cancel[of "\<Sum>uuc<n. Z uuc a _"] diff_0
      diff_right_mono[of \<epsilon> "\<mu>_hat - (\<Sum>uuc<n. Z uuc a _)" \<mu>_hat] diff_right_mono[of "\<Sum>uuc<n. Z uuc a _" "\<mu>_hat - \<epsilon>" \<mu>_hat]
      lessThan_def[of n] more_arith_simps(1)[of "- \<epsilon>" "(\<Sum>uuc<n. Z uuc a _) - \<mu>_hat"] by force 

  have rhs_rewrite: "exp (- 2 * \<epsilon>^2 / (\<Sum> i\<in>?I. (?b i - ?a i)^2)) = exp (- 2 * \<epsilon>^2 / (real n * (u - l)^2))"
    using widths by simp

  show ?thesis using tail lhs_rewrite rhs_rewrite by simp
qed

theorem hoeffding_iid_ge_delta_bound:
  fixes a :: 'a and n :: nat and \<delta>_hat :: real and \<mu>_hat :: real and l u :: real
  assumes a_in: "a \<in> A"
    and delta_bound: "0 < \<delta>_hat" "\<delta>_hat \<le> 1"
    and bounds: "\<forall>i<n. \<forall>\<omega>\<in>\<Omega>. l \<le> Z i a \<omega> \<and> Z i a \<omega> \<le> u"
    and mu_def: "\<mu>_hat = (\<Sum>i<n. expectation (\<lambda>\<omega>. Z i a \<omega>))"
    and n_pos: "n > 0"
    and eps_pos: "\<epsilon> \<ge> 0"
    and u_minus_l_nonzero: "u - l \<noteq> 0"
    and space_M: "space M = \<Omega>"
    and sets_M:  "sets M  = \<F>"
    and indep: "indep_vars (\<lambda>_. borel) (\<lambda>i. (\<lambda>\<omega>. Z i a \<omega>)) {i. i < n}"
    and rv: "\<forall>i<n. random_variable borel (\<lambda>\<omega>. Z i a \<omega>)"
    and eps_expression: "\<epsilon> = sqrt ((real n * (u - l)^2 * ln (1 / \<delta>_hat)) / 2)"
  shows "prob {\<omega> \<in> \<Omega>. (\<Sum>i<n. Z i a \<omega>) \<ge> \<mu>_hat + \<epsilon>} \<le> \<delta>_hat \<and>
         prob {\<omega> \<in> \<Omega>. (\<Sum>i<n. Z i a \<omega>) \<le> \<mu>_hat - \<epsilon>} \<le> \<delta>_hat"
proof -
  have eps_pos: "\<epsilon> \<ge> 0" 
    using assms(7) by auto 
  have eps_squared: "\<epsilon>^2 = (real n * (u - l)^2 * ln (1 / \<delta>_hat)) / 2"
    using eps_expression by (simp add: assms(3) delta_bound(1))

  have exp_eq: "exp (- 2 * \<epsilon>^2 / (real n * (u - l)^2)) = \<delta>_hat"
  proof -
    have "- 2 * \<epsilon>^2 / (real n * (u - l)^2) = - ln (1 / \<delta>_hat)"
    proof -
      have "\<epsilon>^2 /( real n * (u - l)^2 ) = ( ln (1 / \<delta>_hat)) / 2"
        using assms(6,8) eps_squared by fastforce
      then show ?thesis  by linarith 
    qed
    also have "... = ln \<delta>_hat"
      using delta_bound(1) by (simp add: ln_div)
    finally show ?thesis
      using delta_bound(1) by simp
  qed

  have ge_bound:
    "prob {\<omega> \<in> \<Omega>. (\<Sum>i<n. Z i a \<omega>) \<ge> \<mu>_hat + \<epsilon>} \<le> \<delta>_hat"
    using hoeffding_iid_bound_ge_general[OF a_in eps_pos bounds mu_def u_minus_l_nonzero 
        n_pos space_M sets_M indep rv] exp_eq by simp

  have le_bound:
    "prob {\<omega> \<in> \<Omega>. (\<Sum>i<n. Z i a \<omega>) \<le> \<mu>_hat - \<epsilon>} \<le> \<delta>_hat"
    using hoeffding_iid_bound_le_general[OF a_in eps_pos bounds mu_def u_minus_l_nonzero 
        n_pos space_M sets_M indep rv] exp_eq by simp

  show ?thesis
    using ge_bound le_bound by simp
qed

lemma add_le_iff:
  fixes x y z :: real
  shows "x \<le> y - z \<longleftrightarrow> x - y \<le> -z"
  by auto
lemma max_Suc_0_eq_1: "max (Suc 0) x = max 1 x"
  by simp


theorem ucb_suboptimal_bound_set:
  fixes t :: nat           (* current time step *)
    and a :: "'a"           (* a chosen action *)
    and \<Delta> :: "'a \<Rightarrow> real"    (* suboptimality gap function *)
  assumes finite_A: "finite A"                        (* action set is finite *)
    and  a_in_A: "a \<in> A"                             (* action a is in the action set *)
    and a_star_in_A: "a_star \<in> A"                  (* optimal action is in A *)
    and  argmax_exists: "A \<noteq> {}"    
    and subopt_gap: "\<Delta> a > 0"                       (* a is suboptimal *)
    and a_not_opt: "\<exists>a'. a' \<in> A \<and> \<Delta> a > 0"         (* there exists a suboptimal action *)
    and  delta_a: "\<Delta> a = \<mu> a_star - \<mu> a"             (* \<Delta> defined as expected reward difference *)
    and   \<omega>_in_\<Omega>: "\<omega> \<in> \<Omega>"                             (* \<omega> is in sample space *)
    and  asm: " \<omega> \<in> {\<omega> \<in> \<Omega>. A_t_plus_1 t \<omega> = a}"     (* \<omega> is such that A_t_plus_1 selects a *)
    and  setopt: "\<forall>\<omega> \<in> \<Omega>. \<exists>a_max \<in> A. \<forall>b \<in> A. U t b \<omega> \<le> U t a_max \<omega> "(* argmax exists *)
    and A_t_plus_1_maximizes: 
    "\<And>t \<omega> a. A_t_plus_1 t \<omega> = a \<Longrightarrow> a \<in> A \<and> (\<forall>b \<in> A. U t a \<omega> \<ge> U t b \<omega>)" 
  shows "{\<omega> \<in> \<Omega>. A_t_plus_1 t \<omega> = a} \<subseteq> 
         {\<omega> \<in> \<Omega>. U t a_star \<omega> \<le> \<mu> a_star} \<union> {\<omega> \<in> \<Omega>. \<mu> a_star \<le> U t a \<omega>}"
proof -
  have set_result_1:
    "{\<omega> \<in> \<Omega>. A_t_plus_1 t \<omega> = a} \<subseteq> {\<omega> \<in> \<Omega>. \<forall>b \<in> A. U t a \<omega> \<ge> U t b \<omega>}"
  proof
    fix \<omega>
    assume "\<omega> \<in> {\<omega> \<in> \<Omega>. A_t_plus_1 t \<omega> = a}"  (* fix an arbitrary \<omega> *)
    hence "A_t_plus_1 t \<omega> = a" by simp

(* From setopt, there exists a maximizer a_max for this \<omega> *)
    from setopt obtain a_max where
      "a_max \<in> A \<and> (\<forall>b \<in> A. U t b \<omega> \<le> U t a_max \<omega>)" 
      using \<open>\<omega> \<in> {\<omega> \<in> \<Omega>. A_t_plus_1 t \<omega> = a}\<close> by auto

(* Since A_t_plus_1 t \<omega> selects a maximizer, a = a_max *)
    hence "\<forall>b \<in> A. U t a \<omega> \<ge> U t b \<omega>"
      using `A_t_plus_1 t \<omega> = a` A_t_plus_1_maximizes by auto

(* Conclude \<omega> \<in> right-hand set *)
    thus "\<omega> \<in> {\<omega> \<in> \<Omega>. \<forall>b \<in> A. U t a \<omega> \<ge> U t b \<omega>}" 
      using \<open>\<omega> \<in> {\<omega> \<in> \<Omega>. A_t_plus_1 t \<omega> = a}\<close> by blast
  qed


  have set_result_2: "{\<omega> \<in> \<Omega>. \<forall>b \<in> A. U t a \<omega> \<ge> U t b \<omega>} \<subseteq> {\<omega> \<in> \<Omega>. U t a_star \<omega> \<le> U t a \<omega>}"
  proof 
    fix \<omega> assume asm: "\<omega> \<in> {\<omega> \<in> \<Omega>. \<forall>b \<in> A. U t a \<omega> \<ge> U t b \<omega>}"
    hence "\<omega> \<in> \<Omega>" and ub: "\<forall>b \<in> A. U t a \<omega> \<ge> U t b \<omega>" by simp_all
    from a_star_in_A have "U t a \<omega> \<ge> U t a_star \<omega>" using ub by simp
    thus "\<omega> \<in> {\<omega> \<in> \<Omega>. U t a_star \<omega> \<le> U t a \<omega>}" using `\<omega> \<in> \<Omega>` by simp
  qed

  have set_result_3: "{\<omega> \<in> \<Omega>. U t a_star \<omega> \<le> U t a \<omega>} \<subseteq> 
                     {\<omega> \<in> \<Omega>. U t a_star \<omega> \<le> \<mu> a_star} \<union> {\<omega> \<in> \<Omega>. \<mu> a_star \<le> U t a \<omega>}"
  proof 
    fix \<omega> assume asm: "\<omega> \<in> {\<omega> \<in> \<Omega>. U t a_star \<omega> \<le> U t a \<omega>}"
    hence "\<omega> \<in> \<Omega>" and le: "U t a_star \<omega> \<le> U t a \<omega>" by simp_all
    show "\<omega> \<in> {\<omega> \<in> \<Omega>. U t a_star \<omega> \<le> \<mu> a_star} \<union> {\<omega> \<in> \<Omega>. \<mu> a_star \<le> U t a \<omega>}"
    proof (cases "U t a_star \<omega> \<le> \<mu> a_star")
      case True
      then show ?thesis using `\<omega> \<in> \<Omega>` by simp
    next
      case False
      hence "\<mu> a_star < U t a_star \<omega>" by simp
      with le have "\<mu> a_star < U t a \<omega>" by (simp add: less_le_trans)
      then show ?thesis using `\<omega> \<in> \<Omega>` by simp
    qed
  qed

  from set_result_1 set_result_2 set_result_3 show ?thesis by auto
qed



theorem ucb_suboptimal_bound_prob_statement:
  fixes t :: nat and a :: 'a  and \<Delta> :: "'a \<Rightarrow> real"
  assumes finite_A: "finite A"                        (* action set is finite *)
    and a_star_in_A: "a_star \<in> A"                  (* optimal action is in A *)
    and  argmax_exists: "A \<noteq> {}"    
    and subopt_gap: "\<Delta> a > 0"                       (* a is suboptimal *)
    and a_not_opt: "\<exists>a'. a' \<in> A \<and> \<Delta> a > 0"         (* there exists a suboptimal action *)
    and   \<omega>_in_\<Omega>: "\<omega> \<in> \<Omega>"                             (* \<omega> is in sample space *)
    and  asm: " \<omega> \<in> {\<omega> \<in> \<Omega>. A_t_plus_1 t \<omega> = a}"     (* \<omega> is such that A_t_plus_1 selects a *)
    and  setopt: "\<forall>\<omega> \<in> \<Omega>. \<exists>a_max \<in> A. \<forall>b \<in> A. U t b \<omega> \<le> U t a_max \<omega> "(* argmax exists *)
    and A_t_plus_1_maximizes: 
    "\<And>t \<omega> a. A_t_plus_1 t \<omega> = a \<Longrightarrow> a \<in> A \<and> (\<forall>b \<in> A. U t a \<omega> \<ge> U t b \<omega>)" 
    and a_in_A: "a \<in> A"
    and omega_in: "\<omega> \<in> \<Omega>"
    and subopt_gap: "\<Delta> a > 0"
    and delta_a: "\<Delta> a = \<mu> a_star - \<mu> a" (* \<Delta> defined as expected reward difference *)
    and H_def: "H = (2 * ln (1 / \<delta>)) / (\<Delta> a)^2"
    and E_def: "E = {\<omega> \<in> \<Omega>. A_t_plus_1 t \<omega> = a} \<inter> {\<omega> \<in> \<Omega>. H \<le> real (N_n t a \<omega>)}"
    and F_def: "F = {\<omega> \<in> \<Omega>. U t a_star \<omega> \<le> \<mu> a_star} \<inter> {\<omega> \<in> \<Omega>. H \<le> real (N_n t a \<omega>)}"
    and G_def: "G = {\<omega> \<in> \<Omega>. \<mu> a_star \<le> U t a \<omega>} \<inter> {\<omega> \<in> \<Omega>. H \<le> real (N_n t a \<omega>)}"
    and meas_sets: "E \<in> sets M" "F \<in> sets M" "G \<in> sets M"
    and prob_inter: "prob  (F \<inter> G) \<equiv> enn2real (emeasure M (F \<inter> G))"

shows "prob  ({\<omega> \<in> \<Omega>. A_t_plus_1 t \<omega> = a} \<inter> {\<omega> \<in> \<Omega>. H \<le> real (N_n t a \<omega>)}) \<le>
         prob  ({\<omega> \<in> \<Omega>. U t a_star \<omega> \<le> \<mu> a_star} \<inter> {\<omega> \<in> \<Omega>. H \<le> real (N_n t a \<omega>)}) +
         prob  ({\<omega> \<in> \<Omega>. U t a \<omega> \<ge> \<mu> a_star} \<inter> {\<omega> \<in> \<Omega>. H \<le> real (N_n t a \<omega>)})"
proof -

  have subset_result:"E \<subseteq> F \<union> G"
  proof -
    have step1: "{\<omega> \<in> \<Omega>. A_t_plus_1 t \<omega> = a} \<subseteq>
               {\<omega> \<in> \<Omega>. U t a_star \<omega> \<le> \<mu> a_star} \<union> {\<omega> \<in> \<Omega>. \<mu> a_star \<le> U t a \<omega>}"
      using ucb_suboptimal_bound_set assms by blast

    then have step2:
      "{\<omega> \<in> \<Omega>. A_t_plus_1 t \<omega> = a} \<inter> {\<omega> \<in> \<Omega>. H \<le> real (N_n t a \<omega>)} \<subseteq>
     ({\<omega> \<in> \<Omega>. U t a_star \<omega> \<le> \<mu> a_star} \<union> {\<omega> \<in> \<Omega>. \<mu> a_star \<le> U t a \<omega>}) \<inter> {\<omega> \<in> \<Omega>. H \<le> real (N_n t a \<omega>)}"
      by auto

    then have step3:
      "{\<omega> \<in> \<Omega>. A_t_plus_1 t \<omega> = a} \<inter> {\<omega> \<in> \<Omega>. H \<le> real (N_n t a \<omega>)} \<subseteq>
     ({\<omega> \<in> \<Omega>. U t a_star \<omega> \<le> \<mu> a_star} \<inter> {\<omega> \<in> \<Omega>. H \<le> real (N_n t a \<omega>)}) \<union>
     ({\<omega> \<in> \<Omega>. \<mu> a_star \<le> U t a \<omega>} \<inter> {\<omega> \<in> \<Omega>. H \<le> real (N_n t a \<omega>)})"
      by (auto simp add: set_eq_iff)

    then have step4: 
      "E \<subseteq> F \<union> G" using assms by simp
    then show ?thesis
      by (simp add: E_def F_def G_def)
  qed

  have bound: "prob  E \<le> prob  F + prob G"
  proof (rule union_bound)
    show "E \<subseteq> F \<union> G"  by (simp add: subset_result) 
    show "E \<in> sets M" using meas_sets by simp   
    show "F \<in> sets M" using meas_sets by simp
    show "G \<in> sets M " using meas_sets by simp
    have "prob  (F \<inter> G) \<equiv> enn2real (emeasure M (F \<inter> G))" using prob_inter by simp  
    have "prob  E \<le> prob  (F \<union> G)" 
      using assms(18,19,20) increasingD measure_increasing subset_result by blast
    have "prob  (F \<union> G) = prob  F + prob G - prob  (F \<inter> G)" 
      by (simp add: Int_commute assms(19,20) finite_measure_Diff' finite_measure_Union')
  qed

  hence union_bound:
    "prob  ({\<omega> \<in> \<Omega>. A_t_plus_1 t \<omega> = a} \<inter> {\<omega> \<in> \<Omega>. H \<le> real (N_n t a \<omega>)}) \<le>
     prob  ({\<omega> \<in> \<Omega>. U t a_star \<omega> \<le> \<mu> a_star} \<inter> {\<omega> \<in> \<Omega>. H \<le> real (N_n t a \<omega>)}) +
     prob  ({\<omega> \<in> \<Omega>. U t a \<omega> \<ge> \<mu> a_star} \<inter> {\<omega> \<in> \<Omega>. H \<le> real (N_n t a \<omega>)})"
    using bound assms by simp

  show ?thesis
    using union_bound by simp
qed

lemma U_le_\<mu>_pointwise:
  "U t a_star \<omega> \<le> \<mu> a_star \<longleftrightarrow> 
   M_val t a_star \<omega> - \<mu> a_star \<le> 
   - q * sqrt (ln (1 / \<delta>) / (2 * real (max 1 (N_n t a_star \<omega>))))"
  unfolding U_def
  using add_le_iff max_Suc_0_eq_1
  by auto


lemma U_ge_\<mu>_pointwise: 
  assumes  delta_a: "\<Delta> a = \<mu> a_star - \<mu> a"
  shows
    "U t a \<omega> \<ge> \<mu> a_star \<longleftrightarrow>
   M_val t a \<omega> - \<mu> a \<ge> \<Delta> a - q * sqrt (ln (1 / \<delta>) / (2 * real (max 1 (N_n t a \<omega>))))"
proof -
  have delta_plus_mu_eq:
    "\<Delta> a + \<mu> a = \<mu> a_star"
  proof -
    have "\<Delta> a = \<mu> a_star - \<mu> a"
      using  delta_a by simp (* or just assume you have it *)

    hence "\<Delta> a + \<mu> a = (\<mu> a_star - \<mu> a) + \<mu> a"
      by simp

    also have "... = \<mu> a_star"
      by simp

    finally show ?thesis .
  qed
  have U_ge_\<mu>_rewrite:
    "U t a \<omega> \<ge>  \<mu> a_star \<longleftrightarrow> M_val t a \<omega> - \<mu> a \<ge> \<Delta> a  - q * sqrt (ln (1 / \<delta>) / (2 * real (max 1 (N_n t a \<omega>))))"
    unfolding U_def using add_le_iff max_Suc_0_eq_1 delta_plus_mu_eq by auto
  then show ?thesis by simp
qed

theorem hoeffding_iid__bound_le:
  fixes a :: 'a and n :: nat and \<epsilon> :: real and \<mu>_hat :: real and l_hat u_hat :: real
    and I :: "nat set"
    and X_new :: "nat \<Rightarrow> 'b \<Rightarrow> real"
    and a_bound b_bound :: "nat \<Rightarrow> real"
  assumes a_in: "a \<in> A"
    and "b \<in> \<Omega>"
    and eps_pos: "\<epsilon> \<ge> 0"
    and  eps: "\<epsilon> =  abs (u_hat - l_hat) * sqrt (((real n) / 2) * ln (1 / \<delta>))"
    and "\<delta> \<ge> 0 \<and> \<delta> \<le> 1"
    and t_eq_n: "t = n"
    and  "c > 0 " 
    and bounds: "\<forall>j < t. \<forall>\<omega> \<in> \<Omega>. \<forall> a \<in>A. l_hat \<le> Z_hat j a \<omega> \<and> Z_hat j a \<omega> \<le> u_hat"
    and mu_def: "\<mu>_hat = (\<Sum> j < t. expectation (\<lambda>\<omega>. Z_hat j a \<omega>))"
    and "u_hat - l_hat \<noteq> 0"
    and t_pos:  "t > 0" 
    and "\<forall>t<n.  N_n t a_star b > 0"
    and   n_pos:  "n > 0" 
    and "M_val t a_star b \<equiv> (\<Sum> s < t. if \<pi> s b = a_star then Z s a_star b else 0) /
 real (N_n t a_star b)"
    and widths: "(\<Sum> i \<in> I. (b_bound i - a_bound i)^2) = (real n) * (u_hat - l_hat)^2"
    and space_M: "space M = \<Omega>"
    and sets_M:  "sets M  = \<F>"
    and indep: "indep_vars (\<lambda>_. borel) (\<lambda>j. (\<lambda>\<omega>. Z j a \<omega>)) {j. j < t}"
    and rv: "\<forall>j<t. random_variable borel (\<lambda>\<omega>. Z j a \<omega>)"
    and "\<forall>j<t.  Z_hat j a_star \<omega> =  c * (if \<pi> j b = a_star then Z j a_star b else 0) "
    and "indep_interval_bounded_random_variables M I X_new a_bound b_bound"
    and indep_loc: "indep_interval_bounded_random_variables M {j. j < t}
                   (\<lambda>j. (\<lambda>\<omega>. Z_hat j a_star \<omega>))
                   (\<lambda>j. l_hat) (\<lambda>j. u_hat)"
    and H: "Hoeffding_ineq M {j. j < t} 
                     (\<lambda>j. (\<lambda>\<omega>. Z_hat j a_star \<omega>))
                     (\<lambda>j. l_hat) (\<lambda>j. u_hat)"
    and sum_integrals_eq: "(\<Sum> j \<in> {j. j < t}. integral\<^sup>L M (\<lambda>\<omega>. Z_hat j a_star \<omega>)) = \<mu>_hat"
    and rewriting: "prob {\<omega> \<in> \<Omega>. (\<Sum> j < t. Z_hat j a_star \<omega>) - (\<Sum> j < t. expectation (Z_hat j a_star)) \<le> - \<epsilon>} =
      prob {x \<in> space M. (\<Sum> j < t. Z_hat j a_star x) \<le> (\<Sum> j < t. expectation (Z_hat j a_star)) - \<epsilon>}"
  shows "prob {\<omega> \<in> \<Omega>. (\<Sum> j < n. Z_hat j a_star \<omega>) \<le> \<mu>_hat - \<epsilon>}   
         \<le> \<delta>"
proof -

  let ?I = "{j. j < t}"
  let ?X_new = "\<lambda>j. (\<lambda>\<omega>. Z_hat j a_star \<omega>)"
  let ?a_bound = "\<lambda>j. l_hat"
  let ?b_bound = "\<lambda>j. u_hat"

  have
    "M_val t a_star b \<equiv> (\<Sum> s < t. if \<pi> s b = a_star then Z s a_star b else 0) / real (N_n t a_star b)"
    using assms by simp


  have finite_I: "finite ?I" by simp

(* AE bounds *)
  have AE_bounds: "\<forall>j \<in> ?I. AE \<omega> in M. ?a_bound j \<le> ?X_new j \<omega> \<and> ?X_new j \<omega> \<le> ?b_bound j"
  proof
    fix j assume "j \<in> ?I"
    then have "j < t" by simp

    then have bound_j: "\<forall>\<omega> \<in> \<Omega>. l_hat \<le> Z_hat j a_star \<omega> \<and> Z_hat j a_star \<omega> \<le> u_hat"
      using bounds by (simp add: a_in_A)
    then show "AE \<omega> in M. ?a_bound j \<le> ?X_new j \<omega> \<and> ?X_new j \<omega> \<le> ?b_bound j"
      using space_M sets_M by force
  qed


(* Independence & boundedness *)
  have indep_loc: "indep_interval_bounded_random_variables M ?I ?X_new ?a_bound ?b_bound"
    using assms by simp
  have H: "Hoeffding_ineq M ?I ?X_new ?a_bound  ?b_bound" 
    using assms by simp


  have sum_integrals_eq: "(\<Sum> j\<in>?I. integral\<^sup>L M (?X_new j)) = \<mu>_hat"
    using assms by simp
      (* Widths sum *)
  have widths:
    "(\<Sum> j \<in> ?I. (?b_bound j - ?a_bound j)^2) = (real n) * (u_hat - l_hat)^2"
  proof -
    have "(\<Sum> j \<in> ?I. (?b_bound j - ?a_bound j)^2) =
        (\<Sum> j \<in> ?I. (u_hat - l_hat)^2)"
      by simp
    also have "... = card ?I * (u_hat - l_hat)^2"
      by simp
    also have "card ?I = t"
      by simp
    also have "... = n" 
      using \<open>t = n\<close> assms by blast  (* or adjust if you have a lemma/assumption linking t and n *)
    finally show ?thesis 
      using assms by fastforce
  qed

  have widths_pos: "0 < (\<Sum> j \<in> ?I. (?b_bound j - ?a_bound j )^2)"
    using \<open>u_hat - l_hat \<noteq> 0\<close> widths n_pos by auto

  have res: "prob {\<omega> \<in> \<Omega>. (\<Sum> j < t. Z_hat j a_star \<omega>) \<le>  (\<Sum> j < t. expectation (Z_hat j a_star)) - \<epsilon>} =
      prob {x \<in> space M. (\<Sum> j < t. Z_hat j a_star x) \<le> (\<Sum> j < t. expectation (Z_hat j a_star)) - \<epsilon>}"
    using assms by simp


  then have tail: "prob {\<omega> \<in> \<Omega>. (\<Sum> j\<in>?I. ?X_new j \<omega>) \<le>  (\<Sum> j\<in>?I. integral\<^sup>L M (?X_new j)) - \<epsilon>} 
  \<le> exp (- 2 * \<epsilon>^2 / (\<Sum> j\<in>?I. (?b_bound j - ?a_bound j)^2))"
    using Hoeffding_ineq.Hoeffding_ineq_le[OF H eps_pos widths_pos]
    by (smt (verit, best) Collect_cong assms) 

(* Rewrite LHS and RHS *)
  have lhs_rewrite: "{\<omega> \<in> \<Omega>. (\<Sum> j < n. Z_hat j a_star \<omega>) \<le> \<mu>_hat - \<epsilon>} 
                     = {\<omega> \<in> \<Omega>. (\<Sum> j\<in>?I. ?X_new j \<omega>) - (\<Sum> j\<in>?I. integral\<^sup>L M (?X_new j)) \<le> -\<epsilon>}"
    by (metis (mono_tags, lifting) add_le_iff assms(24,6) lessThan_def)
  have rhs_rewrite: "exp (- 2 * \<epsilon>^2 / (\<Sum> j\<in>?I. (?b_bound j - ?a_bound j)^2)) = exp (- 2 * \<epsilon>^2 / (real n * (u_hat - l_hat)^2))"
    using widths by simp

  have lhs_prob:"prob {\<omega> \<in> \<Omega>. (\<Sum> j < n. Z_hat j a_star \<omega>) \<le> \<mu>_hat - \<epsilon>}  
         = prob {\<omega> \<in> \<Omega>. (\<Sum> j\<in>?I. ?X_new j \<omega>) - (\<Sum> j\<in>?I. integral\<^sup>L M (?X_new j)) \<le> -\<epsilon>}"
    using lhs_rewrite by simp

  then have "prob {\<omega> \<in> \<Omega>. (\<Sum> j < n. Z_hat j a_star \<omega>) \<le> \<mu>_hat - \<epsilon>} \<le> 
exp (- 2 * \<epsilon>^2 / (\<Sum> j\<in>?I. (?b_bound j - ?a_bound j)^2))" 
    using lhs_rewrite tail lhs_prob by (smt (verit, ccfv_threshold) Collect_cong)  
  then have "prob {\<omega> \<in> \<Omega>. (\<Sum> j < n. Z_hat j a_star \<omega>) \<le> \<mu>_hat - \<epsilon>} \<le> exp (- 2 * \<epsilon>^2 / (real n * (u_hat - l_hat)^2))"
    using rhs_rewrite by linarith 


  then have "prob {\<omega> \<in> \<Omega>. (\<Sum> j < n. Z_hat j a_star \<omega>) - \<mu>_hat\<le>  - \<epsilon>} =
prob {\<omega> \<in> \<Omega>. (\<Sum> j < n. Z_hat j a_star \<omega>) - \<mu>_hat\<le>  - abs (u_hat - l_hat) * sqrt (((real n) / 2) * ln (1 / \<delta>))} "
    using eps by simp

  have res1: "exp (- 2 * \<epsilon>^2 / (real n * (u_hat - l_hat)^2)) =
             exp (- 2 * (abs (u_hat - l_hat) * sqrt ((real n / 2) * ln (1 / \<delta>)))^2 /
                     (real n * (u_hat - l_hat)^2))"
    using eps by simp

  have "exp (- 2 * (abs (u_hat - l_hat) * sqrt ((real n / 2) * ln (1 / \<delta>)))^2 /
                  (real n * (u_hat - l_hat)^2)) = 
exp (- 2 * (abs (u_hat - l_hat) * sqrt ((real n / 2) * ln (1 / \<delta>)))^2 / (real n * (u_hat - l_hat)^2)) "      
    using eps eps_pos  by blast
  then have "... = 
exp (- 2 * ((abs (u_hat - l_hat))^2 / (real n * (u_hat - l_hat)^2 )) * sqrt (((real n / 2) * ln (1 / \<delta>)))^2 )"
    by (metis (no_types, opaque_lifting) more_arith_simps(11) power_mult_distrib times_divide_eq_left
        times_divide_eq_right) 

  have "... =
exp (- 2 * ((abs (u_hat - l_hat))^2 / (real n * abs ((u_hat - l_hat))^2 )) * sqrt (((real n / 2) * ln (1 / \<delta>)))^2 )"
    by simp
  have "... = exp (- 2 * (1/ ((real n) )) * sqrt (((real n / 2) * ln (1 / \<delta>)))^2 )"
    using assms by simp

  then have "... = exp (-2 * (1/ ((real n) )) *  (((real n / 2) * ln (1 / \<delta>))) )"
    using power2_eq_square by (smt (verit, best)
        arithmetic_simps(51) assms(10) eps eps_pos real_sqrt_ge_0_iff real_sqrt_pow2
        zero_le_mult_iff) 

  then have "... = exp (-1* ln (1 / \<delta>)) "
    using assms by (simp add: field_simps)
  then have fin: "exp (- 2 * \<epsilon>^2 / (real n * (u_hat - l_hat)^2))  =  \<delta> "
    using \<delta>_pos assms
    by (metis (lifting)
        \<open>exp (- 2 * (1 / real n) * (sqrt (real n / 2 * ln (1 / \<delta>)))\<^sup>2) = exp (- 2 * (1 / real n) * (real n / 2 * ln (1 / \<delta>)))\<close>
        \<open>exp (- 2 * (\<bar>u_hat - l_hat\<bar> * sqrt (real n / 2 * ln (1 / \<delta>)))\<^sup>2 / (real n * (u_hat - l_hat)\<^sup>2)) = exp (- 2 * (\<bar>u_hat - l_hat\<bar>\<^sup>2 / (real n * (u_hat - l_hat)\<^sup>2)) * (sqrt (real n / 2 * ln (1 / \<delta>)))\<^sup>2)\<close>
        \<open>exp (- 2 * (\<bar>u_hat - l_hat\<bar>\<^sup>2 / (real n * (u_hat - l_hat)\<^sup>2)) * (sqrt (real n / 2 * ln (1 / \<delta>)))\<^sup>2) = exp (- 2 * (\<bar>u_hat - l_hat\<bar>\<^sup>2 / (real n * \<bar>u_hat - l_hat\<bar>\<^sup>2)) * (sqrt (real n / 2 * ln (1 / \<delta>)))\<^sup>2)\<close>
        \<open>exp (- 2 * (\<bar>u_hat - l_hat\<bar>\<^sup>2 / (real n * \<bar>u_hat - l_hat\<bar>\<^sup>2)) * (sqrt (real n / 2 * ln (1 / \<delta>)))\<^sup>2) = exp (- 2 * (1 / real n) * (sqrt (real n / 2 * ln (1 / \<delta>)))\<^sup>2)\<close>
        arith_simps(56) exp_ln ln_divide_pos ln_one more_arith_simps(10) mult_minus1 of_nat_zero_less_power_iff power_0)

  show ?thesis using assms fin
      \<open>prob {\<omega> \<in> \<Omega>. (\<Sum>j<n. Z_hat j a_star \<omega>) \<le> \<mu>_hat - \<epsilon>} \<le> exp (- 2 * \<epsilon>\<^sup>2 / (real n * (u_hat - l_hat)\<^sup>2))\<close>
    by presburger 


qed

theorem hoeffding_iid__bound_ge:
  fixes a :: 'a and n :: nat and \<epsilon> :: real and \<mu>_hat :: real and l_hat u_hat :: real
    and I :: "nat set"
    and X_new :: "nat \<Rightarrow> 'b \<Rightarrow> real"
    and a_bound b_bound :: "nat \<Rightarrow> real"
  assumes a_in: "a \<in> A"
    and "b \<in> \<Omega>"
    and eps_pos: "\<epsilon> \<ge> 0"
    and  eps: "\<epsilon> =  abs (u_hat - l_hat) * sqrt (((real n) / 2) * ln (1 / \<delta>))"
    and "\<delta> \<ge> 0 \<and> \<delta> \<le> 1"
    and t_eq_n: "t = n"
    and  "c > 0 " 
    and bounds: "\<forall>j < t. \<forall>\<omega> \<in> \<Omega>. \<forall> a \<in>A. l_hat \<le> Z_hat j a \<omega> \<and> Z_hat j a \<omega> \<le> u_hat"
    and mu_def: "\<mu>_hat = (\<Sum> j < t. expectation (\<lambda>\<omega>. Z_hat j a \<omega>))"
    and "u_hat - l_hat \<noteq> 0"
    and t_pos:  "t > 0" 
    and "\<forall>t<n.  N_n t a_star b > 0"
    and   n_pos:  "n > 0" 
    and "M_val t a b \<equiv> (\<Sum> s < t. if \<pi> s b = a then Z s a b else 0) /
 real (N_n t a b)"
    and widths: "(\<Sum> i \<in> I. (b_bound i - a_bound i)^2) = (real n) * (u_hat - l_hat)^2"
    and space_M: "space M = \<Omega>"
    and sets_M:  "sets M  = \<F>"
    and indep: "indep_vars (\<lambda>_. borel) (\<lambda>j. (\<lambda>\<omega>. Z j a \<omega>)) {j. j < t}"
    and rv: "\<forall>j<t. random_variable borel (\<lambda>\<omega>. Z j a \<omega>)"
    and "\<forall>j<t.  Z_hat j a \<omega> =  c * (if \<pi> j b = a then Z j a_star b else 0) "
    and "indep_interval_bounded_random_variables M I X_new a_bound b_bound"
    and indep_loc: "indep_interval_bounded_random_variables M {j. j < t}
                   (\<lambda>j. (\<lambda>\<omega>. Z_hat j a \<omega>))
                   (\<lambda>j. l_hat) (\<lambda>j. u_hat)"
    and H: "Hoeffding_ineq M {j. j < t} 
                     (\<lambda>j. (\<lambda>\<omega>. Z_hat j a  \<omega>))
                     (\<lambda>j. l_hat) (\<lambda>j. u_hat)"
    and sum_integrals_eq: "(\<Sum> j \<in> {j. j < t}. integral\<^sup>L M (\<lambda>\<omega>. Z_hat j a \<omega>)) = \<mu>_hat"
    and rewriting: "prob {\<omega> \<in> \<Omega>. (\<Sum> j < t. Z_hat j a \<omega>) - (\<Sum> j < t. expectation (Z_hat j a)) \<ge>  \<epsilon>} =
      prob {x \<in> space M. (\<Sum> j < t. Z_hat j a x) \<ge> (\<Sum> j < t. expectation (Z_hat j a)) + \<epsilon>}"
  shows "prob {\<omega> \<in> \<Omega>. (\<Sum> j < n. Z_hat j a \<omega>) \<ge> \<mu>_hat + \<epsilon>}  \<le> \<delta>"
proof -

  let ?I = "{j. j < t}"
  let ?X_new = "\<lambda>j. (\<lambda>\<omega>. Z_hat j a \<omega>)"
  let ?a_bound = "\<lambda>j. l_hat"
  let ?b_bound = "\<lambda>j. u_hat"

  have
    "M_val t a b \<equiv> (\<Sum> s < t. if \<pi> s b = a then Z s a b else 0) / real (N_n t a b)"
    using assms by simp


  have finite_I: "finite ?I" by simp

(* AE bounds *)
  have AE_bounds: "\<forall>j \<in> ?I. AE \<omega> in M. ?a_bound j \<le> ?X_new j \<omega> \<and> ?X_new j \<omega> \<le> ?b_bound j"
  proof
    fix j assume "j \<in> ?I"
    then have "j < t" by simp

    then have bound_j: "\<forall>\<omega> \<in> \<Omega>. l_hat \<le> Z_hat j a \<omega> \<and> Z_hat j a \<omega> \<le> u_hat"
      using bounds by (simp add: a_in_A)
    then show "AE \<omega> in M. ?a_bound j \<le> ?X_new j \<omega> \<and> ?X_new j \<omega> \<le> ?b_bound j"
      using space_M sets_M by force
  qed


(* Independence & boundedness *)
  have indep_loc: "indep_interval_bounded_random_variables M ?I ?X_new ?a_bound ?b_bound"
    using assms by simp
  have H: "Hoeffding_ineq M ?I ?X_new ?a_bound  ?b_bound" 
    using assms by simp


  have sum_integrals_eq: "(\<Sum> j\<in>?I. integral\<^sup>L M (?X_new j)) = \<mu>_hat"
    using assms by simp
      (* Widths sum *)
  have widths:
    "(\<Sum> j \<in> ?I. (?b_bound j - ?a_bound j)^2) = (real n) * (u_hat - l_hat)^2"
  proof -
    have "(\<Sum> j \<in> ?I. (?b_bound j - ?a_bound j)^2) =
        (\<Sum> j \<in> ?I. (u_hat - l_hat)^2)"
      by simp
    also have "... = card ?I * (u_hat - l_hat)^2"
      by simp
    also have "card ?I = t"
      by simp
    also have "... = n" 
      using \<open>t = n\<close> assms by blast  (* or adjust if you have a lemma/assumption linking t and n *)
    finally show ?thesis 
      using assms by fastforce
  qed

  have widths_pos: "0 < (\<Sum> j \<in> ?I. (?b_bound j - ?a_bound j )^2)"
    using \<open>u_hat - l_hat \<noteq> 0\<close> widths n_pos by auto

  have res: "prob {\<omega> \<in> \<Omega>. (\<Sum> j < t. Z_hat j a \<omega>) - (\<Sum> j < t. expectation (Z_hat j a)) \<ge> \<epsilon>} =
      prob {x \<in> space M. (\<Sum> j < t. Z_hat j a x) \<ge> (\<Sum> j < t. expectation (Z_hat j a)) + \<epsilon>}"
    using assms by simp


  then have tail: "prob {\<omega> \<in> \<Omega>. (\<Sum> j\<in>?I. ?X_new j \<omega>) \<ge>  (\<Sum> j\<in>?I. integral\<^sup>L M (?X_new j)) + \<epsilon>} 
  \<le> exp (- 2 * \<epsilon>^2 / (\<Sum> j\<in>?I. (?b_bound j - ?a_bound j)^2))"
    using Hoeffding_ineq.Hoeffding_ineq_ge[OF H eps_pos widths_pos]
    by (smt (verit, best) Collect_cong assms) 

(* Rewrite LHS and RHS *)
  have lhs_rewrite: "{\<omega> \<in> \<Omega>. (\<Sum> j < n. Z_hat j a \<omega>) \<ge> \<mu>_hat + \<epsilon>} 
                     = {\<omega> \<in> \<Omega>. (\<Sum> j\<in>?I. ?X_new j \<omega>) - (\<Sum> j\<in>?I. integral\<^sup>L M (?X_new j)) \<ge> \<epsilon>}"
    using assms  by (metis (lifting) ext add.commute le_diff_eq lessThan_def) 
  have rhs_rewrite: "exp (- 2 * \<epsilon>^2 / (\<Sum> j\<in>?I. (?b_bound j - ?a_bound j)^2)) = exp (- 2 * \<epsilon>^2 / (real n * (u_hat - l_hat)^2))"
    using widths by simp

  have lhs_prob:"prob {\<omega> \<in> \<Omega>. (\<Sum> j < n. Z_hat j a \<omega>) \<ge> \<mu>_hat + \<epsilon>} 
                     = prob{\<omega> \<in> \<Omega>. (\<Sum> j\<in>?I. ?X_new j \<omega>) - (\<Sum> j\<in>?I. integral\<^sup>L M (?X_new j)) \<ge> \<epsilon>}"
    using assms lhs_rewrite by presburger

  then have "prob {\<omega> \<in> \<Omega>. (\<Sum> j < n. Z_hat j a \<omega>) \<ge> \<mu>_hat + \<epsilon>} \<le> 
exp (- 2 * \<epsilon>^2 / (\<Sum> j\<in>?I. (?b_bound j - ?a_bound j)^2))" 
    using lhs_rewrite tail lhs_prob by (smt (verit, ccfv_threshold) Collect_cong)  
  then have "prob {\<omega> \<in> \<Omega>. (\<Sum> j < n. Z_hat j a \<omega>) \<ge> \<mu>_hat + \<epsilon>} \<le> exp (- 2 * \<epsilon>^2 / (real n * (u_hat - l_hat)^2))"
    using rhs_rewrite by linarith 


  then have "prob {\<omega> \<in> \<Omega>. (\<Sum> j < n. Z_hat j a \<omega>) - \<mu>_hat \<ge>   \<epsilon>} =
prob {\<omega> \<in> \<Omega>. (\<Sum> j < n. Z_hat j a \<omega>) - \<mu>_hat \<ge>   abs (u_hat - l_hat) * sqrt (((real n) / 2) * ln (1 / \<delta>))} "
    using eps by simp

  have res1: "exp (- 2 * \<epsilon>^2 / (real n * (u_hat - l_hat)^2)) =
             exp (- 2 * (abs (u_hat - l_hat) * sqrt ((real n / 2) * ln (1 / \<delta>)))^2 /
                     (real n * (u_hat - l_hat)^2))"
    using eps by simp

  have "exp (- 2 * (abs (u_hat - l_hat) * sqrt ((real n / 2) * ln (1 / \<delta>)))^2 /
                  (real n * (u_hat - l_hat)^2)) = 
exp (- 2 * (abs (u_hat - l_hat) * sqrt ((real n / 2) * ln (1 / \<delta>)))^2 / (real n * (u_hat - l_hat)^2)) "      
    using eps eps_pos  by blast
  then have "... = exp (- 2 * ((abs (u_hat - l_hat))^2 / (real n * (u_hat - l_hat)^2 )) * sqrt (((real n / 2) * ln (1 / \<delta>)))^2 )"
    by (metis (no_types, opaque_lifting) more_arith_simps(11) power_mult_distrib times_divide_eq_left
        times_divide_eq_right) 

  also have "... = exp (- 2 * ((abs (u_hat - l_hat))^2 / (real n * abs ((u_hat - l_hat))^2 )) * sqrt (((real n / 2) * ln (1 / \<delta>)))^2 )"
    by simp
  have "... = exp (- 2 * (1/ ((real n) )) * sqrt (((real n / 2) * ln (1 / \<delta>)))^2 )"
    using assms by simp

  then have "... = exp (-2 * (1/ ((real n) )) *  (((real n / 2) * ln (1 / \<delta>))) )"
    using power2_eq_square by (smt (verit, best)
        arithmetic_simps(51) assms(10) eps eps_pos real_sqrt_ge_0_iff real_sqrt_pow2
        zero_le_mult_iff) 

  then have "... = exp (-1* ln (1 / \<delta>)) "
    using assms by (simp add: field_simps)
  then have fin: "exp (- 2 * \<epsilon>^2 / (real n * (u_hat - l_hat)^2))  =  \<delta> "
    using \<delta>_pos assms
    by (metis (lifting)
        \<open>exp (- 2 * (1 / real n) * (sqrt (real n / 2 * ln (1 / \<delta>)))\<^sup>2) = exp (- 2 * (1 / real n) * (real n / 2 * ln (1 / \<delta>)))\<close>
        \<open>exp (- 2 * (\<bar>u_hat - l_hat\<bar> * sqrt (real n / 2 * ln (1 / \<delta>)))\<^sup>2 / (real n * (u_hat - l_hat)\<^sup>2)) = exp (- 2 * (\<bar>u_hat - l_hat\<bar>\<^sup>2 / (real n * (u_hat - l_hat)\<^sup>2)) * (sqrt (real n / 2 * ln (1 / \<delta>)))\<^sup>2)\<close>
        \<open>exp (- 2 * (\<bar>u_hat - l_hat\<bar>\<^sup>2 / (real n * (u_hat - l_hat)\<^sup>2)) * (sqrt (real n / 2 * ln (1 / \<delta>)))\<^sup>2) = exp (- 2 * (\<bar>u_hat - l_hat\<bar>\<^sup>2 / (real n * \<bar>u_hat - l_hat\<bar>\<^sup>2)) * (sqrt (real n / 2 * ln (1 / \<delta>)))\<^sup>2)\<close>
        \<open>exp (- 2 * (\<bar>u_hat - l_hat\<bar>\<^sup>2 / (real n * \<bar>u_hat - l_hat\<bar>\<^sup>2)) * (sqrt (real n / 2 * ln (1 / \<delta>)))\<^sup>2) = exp (- 2 * (1 / real n) * (sqrt (real n / 2 * ln (1 / \<delta>)))\<^sup>2)\<close>
        diff_0 exp_ln ln_divide_pos ln_one more_arith_simps(10) mult_minus1 of_nat_zero_less_power_iff power_0)

  show ?thesis using assms fin
    using \<open>prob {\<omega> \<in> \<Omega>. \<mu>_hat + \<epsilon> \<le> (\<Sum>j<n. Z_hat j a \<omega>)} \<le> exp (- 2 * \<epsilon>\<^sup>2 / (real n * (u_hat - l_hat)\<^sup>2))\<close>
    by presburger

qed



end 
end
