section\<open>Auxiliary probability space results\<close>

(*
  Session : Balog_Szemeredi_Gowers
  Title:   Prob_Space_Lemmas.thy
  Authors: Angeliki Koutsoukou-Argyraki, Mantas Bakšys, and Chelsea Edmonds
  Affiliation: University of Cambridge
  Date: August 2022.
*)

theory Prob_Space_Lemmas
  imports 
    Random_Graph_Subgraph_Threshold.Prob_Lemmas
begin

context prob_space

begin

lemma expectation_uniform_count:
  assumes "M = uniform_count_measure X" and "finite X"
  shows "expectation f = (\<Sum> x \<in> X. f x) / card X"

proof-
  have "expectation f = (\<Sum> x \<in> X. (1 / (card X)) * f x)" 
    using assms uniform_count_measure_def bot_nat_0.extremum of_nat_0 of_nat_le_iff real_scaleR_def
    lebesgue_integral_point_measure_finite[of _ "(\<lambda> x. 1 / card X)" "f"]
    scaleR_sum_right sum_distrib_left zero_le_divide_1_iff by metis
  then show ?thesis using sum_left_div_distrib by fastforce
qed

text \<open>A lemma to obtain a value for x where the inequality is satisfied \<close>
lemma expectation_obtains_ge: 
  fixes f :: "'a \<Rightarrow> real"
  assumes "M = uniform_count_measure X" and "finite X"
  assumes "expectation f \<ge> c"
  obtains x where "x \<in> X" and "f x \<ge> c"

proof -
  have ne: "X \<noteq> {}"
    using assms(1) subprob_not_empty by auto 
  then have ne0: "card X > 0"
    by (simp add: assms(2) card_gt_0_iff) 
  have "\<exists> x \<in> X . f x \<ge> c"
  proof (rule ccontr)
    assume "\<not> (\<exists>x\<in>X. c \<le> f x)"
    then have "\<forall>x\<in>X. c > f x" by auto 
    then have "(\<Sum> x \<in> X. f x) < (\<Sum> x \<in> X. c)"
      by (meson assms(2) ne sum_strict_mono) 
    then have lt: "(\<Sum> x \<in> X. f x) < (card X) * c" by simp 
    have "expectation f = (\<Sum> x \<in> X. f x) / card X" using expectation_uniform_count assms by auto
    then have "(\<Sum> x \<in> X. f x) \<ge> (card X) * c" using ne0 assms
      by (simp add: le_divide_eq mult_of_nat_commute)
    then show False using lt by auto
  qed
  then show ?thesis using that by auto
qed

text \<open>The following is the variation on the Cauchy-Schwarz inequality presented in Gowers's notes 
before Lemma 2.13 \cite{Gowersnotes}.\<close>

lemma cauchy_schwarz_ineq_var:
  fixes X :: "'a \<Rightarrow> real"
  assumes "integrable M (\<lambda>x. (X x)^2)" and "X \<in> borel_measurable M"
  shows "expectation (\<lambda> x. (X x)^2) \<ge> (expectation (\<lambda> x . (X x)))^2"

proof -
  have "expectation (\<lambda> x. (X x)^2) - (expectation (\<lambda> x . (X x)))^2 = expectation (\<lambda>x. (X x - expectation X)^2)"
    using variance_expectation assms(1) assms(2) by presburger 
  then have "expectation (\<lambda> x. (X x)^2) - (expectation (\<lambda> x . (X x)))^2 \<ge> 0" by simp
  thus ?thesis by simp 
qed

lemma integrable_uniform_count_measure_finite: 
  fixes g :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}" 
  shows "finite A \<Longrightarrow> integrable (uniform_count_measure A) g"
  unfolding uniform_count_measure_def by (simp add: integrable_point_measure_finite)

lemma cauchy_schwarz_ineq_var_uniform:
  fixes X :: "'a \<Rightarrow> real"
  assumes "M = uniform_count_measure S"
  assumes "finite S"
  shows "expectation (\<lambda> x. (X x)^2) \<ge> (expectation (\<lambda> x . (X x)))^2"

proof -
  have borel: "X \<in> borel_measurable M" using assms by (simp) 
  have "integrable M X" using assms by (simp add: integrable_uniform_count_measure_finite)
  then have "integrable M (\<lambda> x. (X x)^2)" using assms by (simp add: integrable_uniform_count_measure_finite)
  thus ?thesis using cauchy_schwarz_ineq_var borel by simp 
qed

text \<open>An equation for expectation over a discrete random variables distribution: \<close>

lemma expectation_finite_uniform_space: 
  assumes "M = uniform_count_measure S" and "finite S"
  fixes X :: "'a \<Rightarrow> real"
  shows "expectation X = (\<Sum> y \<in> X ` S . prob {x \<in> S . X x = y} * y)"

proof -
  have "Bochner_Integration.simple_bochner_integrable M X"
  proof (safe intro!: Bochner_Integration.simple_bochner_integrable.intros)
    show "simple_function M X" unfolding simple_function_def using assms 
      by (auto simp add: space_uniform_count_measure)
    show "emeasure M {y \<in> space M. X y \<noteq> 0} = \<infinity> \<Longrightarrow> False"
      using emeasure_subprob_space_less_top by (auto)
  qed
  then have "expectation X = Bochner_Integration.simple_bochner_integral M X" 
    using simple_bochner_integrable_eq_integral by fastforce
  thus ?thesis using Bochner_Integration.simple_bochner_integral_def space_uniform_count_measure
    by (metis (no_types, lifting) Collect_cong assms(1) real_scaleR_def sum.cong) 
qed

lemma expectation_finite_uniform_indicator: 
  assumes "M = uniform_count_measure S" and "finite S"
  shows "expectation (\<lambda> x. indicator (T x) y) = prob {x \<in> S . indicator (T x) y = 1}" (is "expectation ?X = _")

proof -
  have ss: "?X ` S \<subseteq> {0, 1}"  
    by (intro subsetI, auto simp add: indicator_eq_1_iff)
  have diff: "\<And> y'. y' \<in> ({0, 1} - ?X ` S) \<Longrightarrow> prob {x \<in> S . ?X x = y'} = 0"
    by (metis (mono_tags, lifting) DiffD2 empty_Collect_eq image_eqI measure_empty)
  have "expectation ?X = (\<Sum> y \<in> ?X ` S . prob {x \<in> S . ?X x = y} * y)" 
    using expectation_finite_uniform_space assms by auto
  also have "... = (\<Sum> y \<in> ?X ` S . prob {x \<in> S . ?X x = y} * y) + 
    (\<Sum> y \<in> ({0, 1} - ?X ` S) . prob {x \<in> S . ?X x = y} * y)"
    using diff by auto
  also have "... = (\<Sum> y \<in> {0, 1} . prob {x \<in> S . ?X x = y} * y)"
    using sum.subset_diff[of "?X ` S" "{0, 1}" "\<lambda> y. prob {x \<in> S . ?X x = y} * y"] ss by fastforce 
  also have "... = prob {x \<in> S . ?X x = 0} * 0 + prob {x \<in> S. ?X x = 1} * 1" by auto
  finally have "expectation ?X = prob {x \<in> S. ?X x = 1}*1" by auto
  thus ?thesis by (smt (verit) Collect_cong indicator_eq_1_iff) 
qed

end
end