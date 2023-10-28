(* Theory: Prob_Events_Extras
   Author: Chelsea Edmonds *)

section \<open>General Event Lemmas\<close>
text \<open>General lemmas for reasoning on events in probability spaces after different operations \<close>

theory Prob_Events_Extras 
  imports 
    "HOL-Probability.Probability" 
    PiE_Rel_Extras
begin

context prob_space
begin

lemma prob_sum_Union:
  assumes measurable: "finite A" "A \<subseteq> events" "disjoint A"
  shows "prob (\<Union>A ) = (\<Sum>e\<in>A. prob (e))"
proof -
  obtain f where bb: "bij_betw f {0..<card A} A"
    using assms(1) ex_bij_betw_nat_finite by auto
  then have eq: "f ` {0..<card A} = A"
    by (simp add: bij_betw_imp_surj_on)
  moreover have "inj_on f {0..<card A}"
    using bb bij_betw_def by blast
  ultimately have "disjoint_family_on f {0..<card A}" 
    using disjoint_image_disjoint_family_on[of f "{0..<card A}"] assms by auto
  moreover have "(\<Sum>e\<in>A. prob (e)) = (\<Sum>i\<in>{0..<card A}. prob (f i))" using sum.reindex bb
    by (simp add: sum.reindex_bij_betw) 
  ultimately show ?thesis using finite_measure_finite_Union eq assms(1) assms(2)
    by (metis bb bij_betw_finite) 
qed

lemma events_inter: 
  assumes "finite S"
  assumes "S \<noteq> {}"
  shows "(\<And> A. A \<in> S \<Longrightarrow> A \<in> events) \<Longrightarrow> \<Inter>S \<in> events"
using assms proof (induct S rule: finite_ne_induct)
  case (singleton x)
  then show ?case by auto
next
  case (insert x F)
  then show ?case using sets.Int
    by (metis complete_lattice_class.Inf_insert insertCI) 
qed

lemma events_union: 
  assumes "finite S"
  shows "(\<And> A. A \<in> S \<Longrightarrow> A \<in> events) \<Longrightarrow> \<Union>S \<in> events"
using assms(1) proof (induct S rule: finite_induct)
  case empty
  then show ?case by auto
next
  case (insert x F)
  then show ?case using sets.Un
    by (simp add: insertI1) 
qed

lemma prob_inter_set_lt_elem:  "A \<in> events \<Longrightarrow> prob (A \<inter> (\<Inter>AS)) \<le> prob A"
  by (simp add: finite_measure_mono) 

lemma Inter_event_ss: "finite A \<Longrightarrow> A \<subseteq> events \<Longrightarrow> A \<noteq> {} \<Longrightarrow> \<Inter>A \<in> events"
  by (simp add: events_inter subset_iff) 

lemma prob_inter_ss_lt: 
  assumes "finite A"
  assumes "A \<subseteq> events"
  assumes "B \<noteq> {}"
  assumes "B \<subseteq> A"
  shows "prob (\<Inter>A) \<le> prob (\<Inter>B)"
proof (cases "B = A")
  case True
  then show ?thesis by simp
next
  case False
  then obtain C where "C = A - B" and "C \<noteq> {}"
    using assms(4) by auto
  then have "\<Inter> A = \<Inter>C \<inter> \<Inter>B"
    by (metis Inter_Un_distrib Un_Diff_cancel2 assms(4) sup.orderE) 
  moreover have "\<Inter>B \<in> events" using assms(1) assms(3) assms(2) Inter_event_ss
    by (meson assms(2) assms(4) dual_order.trans finite_subset) 
  ultimately show ?thesis using prob_inter_set_lt_elem
    by (simp add: inf_commute) 
qed

lemma prob_inter_ss_lt_index: 
  assumes "finite A"
  assumes "F ` A \<subseteq> events"
  assumes "B \<noteq> {}"
  assumes "B \<subseteq> A"
  shows "prob (\<Inter>(F ` A)) \<le> prob (\<Inter>(F `B))"
using prob_inter_ss_lt[of "F ` A" "F ` B"] assms by auto

lemma space_compl_double: 
  assumes "S \<subseteq> events"
  shows "((-) (space M)) ` (((-) (space M)) ` S) = S"
proof (intro subset_antisym subsetI)
  fix x assume "x \<in> (-) (space M) ` (-) (space M) ` S"
  then obtain x' where xeq: "x = space M - x'" and "x' \<in> (-) (space M) ` S" by blast
  then obtain x'' where "x' = space M - x''" and xin: "x'' \<in> S" by blast
  then have "x'' = x" using xeq assms
    by (simp add: Diff_Diff_Int Set.basic_monos(7)) 
  then show "x \<in> S" using xin by simp
next
  fix x assume "x \<in> S"
  then obtain x' where xeq: "x' = space M - x" and "x' \<in> (-) (space M) ` S" by simp
  then have "space M - x' \<in>(-) (space M) ` (-) (space M) ` S" by auto
  moreover have "space M - x' = x" using xeq assms
    by (simp add: Diff_Diff_Int \<open>x \<in> S\<close> subset_iff)
  ultimately show "x \<in> (-) (space M) ` (-) (space M) ` S" by simp
qed

lemma bij_betw_compl_sets:
  assumes "S \<subseteq> events"
  assumes "S' = ((-) (space M)) ` S"
  shows "bij_betw ((-) (space M)) S' S"
proof (intro bij_betwI')
  show "\<And>x y. x \<in> S' \<Longrightarrow> y \<in> S' \<Longrightarrow> (space M - x = space M - y) = (x = y)"
    using assms(2) by blast
next
  show "\<And>x. x \<in> S' \<Longrightarrow> space M - x \<in> S" using space_compl_double assms by auto
next 
  show "\<And>y. y \<in> S \<Longrightarrow> \<exists>x\<in>S'. y = space M - x" using space_compl_double assms by auto
qed

lemma bij_betw_compl_sets_rev: 
  assumes "S \<subseteq> events"
  assumes "S' = ((-) (space M)) ` S"
  shows "bij_betw ((-) (space M)) S S'"
proof (intro bij_betwI')
  show "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> (space M - x = space M - y) = (x = y)"
    using assms by (metis Diff_Diff_Int sets.Int_space_eq1 subset_eq) 
next
  show "\<And>x. x \<in> S \<Longrightarrow> space M - x \<in> S'" using space_compl_double assms by auto
next 
  show "\<And>y. y \<in> S' \<Longrightarrow> \<exists>x\<in>S. y = space M - x" using space_compl_double assms by auto
qed

lemma prob0_basic_inter:  "A \<in> events \<Longrightarrow> B \<in> events \<Longrightarrow> prob A = 0 \<Longrightarrow> prob (A \<inter> B) = 0"
  by (metis Int_lower1 finite_measure_mono measure_le_0_iff) 

lemma prob0_basic_Inter: "A \<in> events \<Longrightarrow> B \<subseteq> events \<Longrightarrow> prob A = 0 \<Longrightarrow> prob (A \<inter> (\<Inter>B)) = 0"
  by (metis Int_lower1 finite_measure_mono measure_le_0_iff) 

lemma prob1_basic_inter: "A \<in> events \<Longrightarrow> B \<in> events \<Longrightarrow> prob A = 1 \<Longrightarrow> prob (A \<inter> B) = prob B"
  by (metis inf_commute measure_space_inter prob_space) 

lemma prob1_basic_Inter:
  assumes "A \<in> events" "B \<subseteq> events"
  assumes "prob A = 1"
  assumes "B \<noteq> {}"
  assumes "finite B"
  shows "prob (A \<inter> (\<Inter>B)) = prob (\<Inter>B)"
proof -
  have "\<Inter>B \<in> events" using Inter_event_ss assms by auto 
  then show ?thesis  using assms prob1_basic_inter by auto
qed

lemma compl_identity:  "A \<in> events \<Longrightarrow> space M - (space M - A) = A"
  by (simp add: double_diff sets.sets_into_space)

lemma prob_addition_rule: "A \<in> events \<Longrightarrow> B \<in> events \<Longrightarrow> 
    prob (A \<union> B) = prob A + prob B - prob (A \<inter> B)"
  by (simp add: finite_measure_Diff' finite_measure_Union' inf_commute) 

lemma compl_subset_in_events: "S \<subseteq> events \<Longrightarrow> (-) (space M) ` S \<subseteq> events" 
  by auto

lemma prob_compl_diff_inter:  "A \<in> events \<Longrightarrow> B \<in> events \<Longrightarrow> 
    prob (A \<inter> (space M - B)) = prob A - prob (A \<inter> B)"
  by (simp add: Diff_Int_distrib finite_measure_Diff sets.Int)

lemma bij_betw_prod_prob: "bij_betw f A B \<Longrightarrow> (\<Prod>b\<in>B. prob b) = (\<Prod>a\<in>A. prob (f a))"
  by (simp add: prod.reindex_bij_betw) 

definition event_compl :: "'a set \<Rightarrow> 'a set" where
"event_compl A \<equiv> space M - A"

lemma compl_Union:  "A \<noteq> {} \<Longrightarrow> space M - (\<Union>A) = (\<Inter>a \<in> A . (space M - a))"
  by (simp)

lemma compl_Union_fn: "A \<noteq> {} \<Longrightarrow> space M - (\<Union>(F ` A)) = (\<Inter>a \<in> A . (space M - F a))"
  by (simp)

end

text \<open>Reasoning on the probability of function sets \<close>

lemma card_PiE_val_ss_eq: 
  assumes "finite A"
  assumes "b \<in> B"
  assumes "d \<subseteq> A"
  assumes "B \<noteq> {}"
  assumes "finite B"
  shows "card {f \<in> (A \<rightarrow>\<^sub>E B) . (\<forall> v \<in> d .f v = b)}/card (A \<rightarrow>\<^sub>E B)  = 1/((card B) powi (card d))" 
    (is "card {f \<in> ?C . (\<forall> v \<in> d .f v = b)}/card ?C  = 1/((card B) powi (card d))")
proof - 
  have lt: "card d \<le> card A"
    by (simp add: card_mono assms(1) assms(3)) 
  then have scard: "card {f \<in> ?C . \<forall> v \<in> d . f v = b} = (card B) powi ((card A) - card d)"
    using assms(1) card_PiE_filter_range_set_const[of b B d A] assms(3) assms(2) by fastforce 
  have Ccard: "card ?C = (card B) powi (card A)" using card_funcsetE assms(2) assms(1) by auto
  have bgt: "card B \<noteq> 0" using assms(5) assms(4) by auto
  have "card {f \<in> ?C . \<forall> v \<in> d . f v = b}/ (card ?C) = 
      ((card B) powi ((card A) - card d))/((card B) powi (card A))" 
    using Ccard scard by simp
  also have "... = (card B) powi (int (card A - card d) - int (card A))" 
    using bgt by (simp add: power_int_diff)
  also have "... = (card B) powi (int (card A) - int (card d) - int (card A))" 
    using int_ops lt by simp
  also have "... = (card B) powi -(card d)" using assms(1) by (simp add: of_nat_diff)
  also have "... = inverse ((card B) powi (card d))" 
    using power_int_minus[of "card B" "(int (card d))"] by simp
  finally show ?thesis by (simp add: inverse_eq_divide)  
qed  

lemma card_PiE_val_indiv_eq: 
  assumes "finite A"
  assumes "b \<in> B"
  assumes "d \<in> A"
  assumes "B \<noteq> {}"
  assumes "finite B"
  shows "card {f \<in> (A \<rightarrow>\<^sub>E B) . f d = b}/card (A \<rightarrow>\<^sub>E B)  = 1/(card B)" 
    (is "card {f \<in> ?C .f d = b}/card ?C  = 1/(card B)")
proof - 
  have "{d} \<subseteq> A" using assms(3) by simp
  moreover have "\<And> f . f \<in> ?C \<Longrightarrow> f d = b \<longleftrightarrow> (\<forall> d' \<in> {d}. f d' = b)" by auto
  ultimately have "card {f \<in> ?C .f d = b}/card ?C = 1/((card B) powi (card {d}))"
    using card_PiE_val_ss_eq[of A b B "{d}"] assms by auto
  also have "... = 1/((card B) powi 1)" by auto
  finally show ?thesis by simp
qed  

lemma prob_uniform_ex_fun_space: 
  assumes "finite A"
  assumes "b \<in> B"
  assumes "d \<subseteq> A"
  assumes "B \<noteq> {}"
  assumes "A \<noteq> {}"
  assumes "finite B"
  shows "prob_space.prob (uniform_count_measure (A \<rightarrow>\<^sub>E B)) {f \<in> (A \<rightarrow>\<^sub>E B) . (\<forall> v \<in> d .f v = b)} = 
    1/((card B) powi (card d))"
proof - 
  let ?C = "(A \<rightarrow>\<^sub>E B)"
  let ?M = "uniform_count_measure ?C"
  have finC: "finite ?C" using assms(2) assms(6) assms(1)
    by (simp add: finite_PiE) 
  moreover have "?C \<noteq> {}" using assms(4) assms(1)
    by (simp add: PiE_eq_empty_iff) 
  ultimately interpret P: prob_space ?M
    using assms(3)  by (simp add: prob_space_uniform_count_measure)
  have "P.prob {f \<in> ?C . \<forall> v \<in> d . f v = b} = card {f \<in> ?C . \<forall> v \<in> d . f v = b}/ (card ?C)"
    using measure_uniform_count_measure[of ?C "{f \<in> ?C . \<forall> v \<in> d . f v = b} "] finC assms(3) 
    by fastforce  
  then show ?thesis using card_PiE_val_ss_eq assms by (simp)  
qed

proposition integrable_uniform_count_measure_finite:
  fixes g :: "'a \<Rightarrow> 'b::{banach, second_countable_topology}"
  shows "finite A \<Longrightarrow> integrable (uniform_count_measure A) g"
  unfolding uniform_count_measure_def
  using integrable_point_measure_finite by fastforce

end