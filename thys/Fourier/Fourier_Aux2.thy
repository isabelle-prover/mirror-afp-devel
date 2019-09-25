section\<open>Lemmas possibly destined for future Isabelle releases\<close>

theory Fourier_Aux2
  imports Ergodic_Theory.SG_Library_Complement
begin

lemma has_integral_sin_nx: "((\<lambda>x. sin(real_of_int n * x)) has_integral 0) {-pi..pi}"
proof (cases "n = 0")
  case False
  have "((\<lambda>x. sin (n * x)) has_integral (- cos (n * pi)/n - - cos (n * - pi)/n)) {-pi..pi}"
  proof (rule fundamental_theorem_of_calculus)
    show "((\<lambda>x. - cos (n * x) / n) has_vector_derivative sin (n * a)) (at a within {-pi..pi})"
      if "a \<in> {-pi..pi}" for a :: real
      using that False
      apply (simp only: has_vector_derivative_def)
      apply (rule derivative_eq_intros | force)+
      done
  qed auto
  then show ?thesis
    by simp
qed auto

lemma integral_sin_nx:
   "integral {-pi..pi} (\<lambda>x. sin(x * real_of_int n)) = 0"
  using has_integral_sin_nx [of n] by (force simp: mult.commute)

lemma integral_sin_Z [simp]:
  assumes "n \<in> \<int>"
  shows "integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. sin(x * n)) = 0"
  proof (subst lebesgue_integral_eq_integral)
  show "integrable (lebesgue_on {-pi..pi}) (\<lambda>x. sin (x * n))"
    by (intro continuous_imp_integrable_real continuous_intros)
  show "integral {-pi..pi} (\<lambda>x. sin (x * n)) = 0"
    using assms Ints_cases integral_sin_nx by blast
qed auto

lemma integral_sin_Z' [simp]:
  assumes "n \<in> \<int>"
  shows "integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. sin(n * x)) = 0"
  by (metis assms integral_sin_Z mult_commute_abs)

lemma has_integral_cos_nx:
  "((\<lambda>x. cos(real_of_int n * x)) has_integral (if n = 0 then 2 * pi else 0)) {-pi..pi}"
proof (cases "n = 0")
  case True
  then show ?thesis
    using has_integral_const_real [of "1::real" "-pi" pi] by auto
next
  case False
  have "((\<lambda>x. cos (n * x)) has_integral (sin (n * pi)/n - sin (n * - pi)/n)) {-pi..pi}"
  proof (rule fundamental_theorem_of_calculus)
    show "((\<lambda>x. sin (n * x) / n) has_vector_derivative cos (n * x)) (at x within {-pi..pi})"
      if "x \<in> {-pi..pi}"
      for x :: real
      using that False
      apply (simp only: has_vector_derivative_def)
      apply (rule derivative_eq_intros | force)+
      done
  qed auto
  with False show ?thesis
    by (simp add: mult.commute)
qed

lemma integral_cos_nx:
   "integral {-pi..pi} (\<lambda>x. cos(x * real_of_int n)) = (if n = 0 then 2 * pi else 0)"
  using has_integral_cos_nx [of n] by (force simp: mult.commute)

lemma integral_cos_Z [simp]:
  assumes "n \<in> \<int>"
  shows "integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. cos(x * n)) = (if n = 0 then 2 * pi else 0)"
  proof (subst lebesgue_integral_eq_integral)
  show "integrable (lebesgue_on {-pi..pi}) (\<lambda>x. cos (x * n))"
    by (intro continuous_imp_integrable_real continuous_intros)
  show "integral {-pi..pi} (\<lambda>x. cos (x * n)) = (if n = 0 then 2 * pi else 0)"
    by (metis Ints_cases assms integral_cos_nx of_int_0_eq_iff)
qed auto

lemma integral_cos_Z' [simp]:
  assumes "n \<in> \<int>"
  shows "integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. cos(n * x)) = (if n = 0 then 2 * pi else 0)"
  by (metis assms integral_cos_Z mult_commute_abs)

lemma real_tendsto_zero_mult_right_iff [simp]:
  fixes c::real assumes "c \<noteq> 0" shows "(\<lambda>n. a n * c)\<longlonglongrightarrow> 0 \<longleftrightarrow> a \<longlonglongrightarrow> 0"
  by (metis assms mult_zero_left real_tendsto_mult_right_iff)

lemma real_tendsto_zero_divide_iff [simp]:
  fixes c::real assumes "c \<noteq> 0" shows "(\<lambda>n. a n / c)\<longlonglongrightarrow> 0 \<longleftrightarrow> a \<longlonglongrightarrow> 0"
  using real_tendsto_zero_mult_right_iff [of "1/c" a] assms by (simp add: field_simps)

lemma insert_sets_lebesgue_on:
  assumes "A \<in> sets (lebesgue_on S)" "a \<in> S" "S \<in> sets lebesgue"
  shows "insert a A \<in> sets (lebesgue_on S)"
  by (metis assms borel_singleton insert_subset lborelD sets.Int_space_eq2 sets.empty_sets sets.insert_in_sets sets_completionI_sets sets_restrict_space_iff)

lemma odd_even_cases [case_names 0 odd even]:
  assumes "P 0" and odd: "\<And>n. P(Suc (2 * n))" and even: "\<And>n. P(2 * n + 2)"
  shows "P n"
  by (metis nat_induct2 One_nat_def Suc_1 add_Suc_right assms(1) dvdE even odd oddE)

lemma measure_lebesgue_on_ivl [simp]: "\<lbrakk>{a..b} \<subseteq> S; S \<in> sets lebesgue\<rbrakk> \<Longrightarrow> measure (lebesgue_on S) {a..b} = content {a..b::real}"
  by (simp add: measure_restrict_space)


lemma has_bochner_integral_null [intro]:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "N \<in> null_sets lebesgue"
  shows "has_bochner_integral (lebesgue_on N) f 0"
  unfolding has_bochner_integral_iff
proof
  show "integrable (lebesgue_on N) f"
  proof (subst integrable_restrict_space)
    show "N \<inter> space lebesgue \<in> sets lebesgue"
      using assms by force
    show "integrable lebesgue (\<lambda>x. indicat_real N x *\<^sub>R f x)"
    proof (rule integrable_cong_AE_imp)
      show "integrable lebesgue (\<lambda>x. 0)"
        by simp
      show *: "AE x in lebesgue. 0 = indicat_real N x *\<^sub>R f x"
        using assms
        by (simp add: indicator_def completion.null_sets_iff_AE eventually_mono)
      show "(\<lambda>x. indicat_real N x *\<^sub>R f x) \<in> borel_measurable lebesgue"
        by (auto intro: borel_measurable_AE [OF _ *])
    qed
  qed
  show "integral\<^sup>L (lebesgue_on N) f = 0"
  proof (rule integral_eq_zero_AE)
    show "AE x in lebesgue_on N. f x = 0"
      by (rule AE_I' [where N=N]) (auto simp: assms null_setsD2 null_sets_restrict_space)
  qed
qed

lemma has_bochner_integral_null_eq[simp]:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "N \<in> null_sets lebesgue"
  shows "has_bochner_integral (lebesgue_on N) f i \<longleftrightarrow> i = 0"
  using assms has_bochner_integral_eq by blast

end
