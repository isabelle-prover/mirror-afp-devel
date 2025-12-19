theory MSc_Project_Discrete_Prop15_1
  imports
    "HOL-Probability.Probability"

begin


locale bandit_problem = 
  fixes A :: "'a set"  (* Set of arms *)
    and \<mu> :: "'a \<Rightarrow> real"  (* Expected reward for each arm *)
    and a_star :: "'a"  (* Optimal arm *)
  assumes finite_arms: "finite A"
    and a_star_in_A: "a_star \<in> A"
    and optimal_arm: "\<forall>a \<in> A. \<mu> a_star \<ge> \<mu> a"
begin

definition \<Delta> :: "'a \<Rightarrow> real" where
  "\<Delta> a = \<mu> a_star - \<mu> a"
end

locale bandit_policy = bandit_problem +  prob_space  +
  fixes \<Omega> :: "'b set"
    and \<F> :: "'b set set"
    and \<pi> :: "nat \<Rightarrow> 'b \<Rightarrow> 'a"
    and N_n :: "nat \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> nat"  
  assumes  measurable_policy: "\<forall>t. \<pi> t \<in> measurable M (count_space A)"
    and N_n_def: "\<forall>n a \<omega>. N_n n a \<omega> = card {t \<in> {0..<n}. \<pi> (t+1) \<omega> = a}"
    and count_assm_pointwise: "\<forall>n \<omega>. (\<Sum>a \<in> A. real (N_n n a \<omega>)) = real n" 
begin

definition R_n :: "nat \<Rightarrow> 'b \<Rightarrow> real" where
  "R_n n \<omega> = n * \<mu> a_star - (\<Sum>a \<in> A. \<mu> a * real (N_n n a \<omega>))"

lemma regret_decomposition_pointwise:
  fixes n :: nat and \<omega> :: 'b
  assumes n_count_assm_pointwise: "(\<Sum>a\<in>A. real (N_n n a \<omega>)) = real n"
  shows "R_n n \<omega> = (\<Sum>a \<in> A. \<Delta> a * real (N_n n a \<omega>))"
proof -
  have sum_Nn: "(\<Sum>a \<in> A. real (N_n n a \<omega>)) = real n"
    using n_count_assm_pointwise by simp

  have sum_const: "(\<Sum>a \<in> A. \<mu> a_star * real (N_n n a \<omega>)) = \<mu> a_star * (\<Sum>a \<in> A. real (N_n n a \<omega>))"
    by (simp add: Cartesian_Space.vector_space_over_itself.scale_sum_right)

  have eq1: "R_n n \<omega> = real n * \<mu> a_star - (\<Sum>a \<in> A. \<mu> a * real (N_n n a \<omega>))"
    by (simp add: R_n_def)

  also have eq2: "... = (\<Sum>a \<in> A. \<mu> a_star * real (N_n n a \<omega>)) - (\<Sum>a \<in> A. \<mu> a * real (N_n n a \<omega>))"
    using sum_const sum_Nn
    by (subst sum_Nn[symmetric], subst sum_const) simp

  also have eq3: "... = (\<Sum>a \<in> A. (\<mu> a_star * real (N_n n a \<omega>) - \<mu> a * real (N_n n a \<omega>)))"
    by (rule sum_subtractf[symmetric])

  also have eq4: "... = (\<Sum>a \<in> A. (\<mu> a_star - \<mu> a) * real (N_n n a \<omega>))"
    by (simp add: algebra_simps)

  also have "... = (\<Sum>a \<in> A. \<Delta> a * real (N_n n a \<omega>))"
    by (simp add: \<Delta>_def)

  finally show ?thesis .
qed


lemma integrable_const_fun:
  assumes "finite_measure M"
  shows "integrable M (\<lambda>x. c)"
  using assms by (simp add: Bochner_Integration.finite_measure.integrable_const)

lemma expected_regret:
  assumes "finite A"
  and  "\<forall>a \<in> A. integrable M (\<lambda>\<omega>. real (N_n n a \<omega>))"
  shows "expectation (\<lambda>\<omega>. R_n n \<omega>) = (\<Sum>a\<in>A. \<Delta> a * expectation (\<lambda>\<omega>. real (N_n n a \<omega>)))"
proof -

  have integrable_sum: "integrable M (\<lambda>\<omega>. \<Sum>a \<in> A. \<mu> a * real (N_n n a \<omega>))"
  proof -
    have "\<forall>a \<in> A. integrable M (\<lambda>\<omega>. \<mu> a * real (N_n n a \<omega>))"
      using assms integrable_mult_right by blast
    then show ?thesis
      by (simp add: integrable_sum)
  qed

  have pointwise: "\<forall>\<omega>. R_n n \<omega> = (\<Sum>a\<in>A. \<Delta> a * real (N_n n a \<omega>))"
    using regret_decomposition_pointwise count_assm_pointwise by blast

  hence rewrite: "expectation (\<lambda>\<omega>. R_n n \<omega>) = expectation (\<lambda>\<omega>. \<Sum>a\<in>A. \<Delta> a * real (N_n n a \<omega>))"
    by simp
  
  also have "expectation (\<lambda>\<omega>. R_n n \<omega>) = (\<Sum>a\<in>A. \<Delta> a * expectation (\<lambda>\<omega>. real (N_n n a \<omega>)))"
  proof -
    (* show integrability of each summand *)
    have "\<forall>a \<in> A. integrable M (\<lambda>\<omega>. \<Delta> a * real (N_n n a \<omega>))"
    using assms integrable_mult_right by blast
    hence "integrable M (\<lambda>\<omega>. \<Sum>a \<in> A. \<Delta> a * real (N_n n a \<omega>))"
     using integrable_sum by simp

    (* unfold expectation to integral\<^sup>L *)
     have res_1: "expectation (\<lambda>\<omega>. \<Sum>a\<in>A. \<Delta> a * real (N_n n a \<omega>)) = integral\<^sup>L M (\<lambda>\<omega>. \<Sum>a\<in>A. \<Delta> a * real (N_n n a \<omega>))"
       by simp

     also have res_2: "... = (\<Sum>a\<in>A. integral\<^sup>L M (\<lambda>\<omega>. \<Delta> a * real (N_n n a \<omega>)))"
       using \<open>finite A\<close> assms
       by (simp add: integral_sum integrable_sum)

     have res_3: "expectation (\<lambda>\<omega>. R_n n \<omega>) = (\<Sum>a\<in>A. \<Delta> a * expectation (\<lambda>\<omega>. real (N_n n a \<omega>)))"
      using assms rewrite
      by simp

    then show ?thesis using assms res_3 by auto
  qed

  then show ?thesis .
qed



end

end

