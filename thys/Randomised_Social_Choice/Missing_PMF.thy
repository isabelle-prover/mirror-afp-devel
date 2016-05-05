(*  
  Title:    Missing_PMF.thy
  Author:   Manuel Eberl, TU München

  Auxiliary facts about PMFs that should go in the library at some point
*)

section \<open>Auxiliary facts about PMFs\<close>

theory Missing_PMF
  imports Complex_Main "~~/src/HOL/Probability/Probability" PMF_Of_List Missing_Multiset
begin

(* TODO: Move? *)
adhoc_overloading Monad_Syntax.bind bind_pmf

lemma pmf_not_neg [simp]: "\<not>pmf p x < 0"
  by (simp add: not_less pmf_nonneg)

lemma set_pmf_eq': "set_pmf p = {x. pmf p x > 0}"
proof safe
  fix x assume "x \<in> set_pmf p"
  hence "pmf p x \<noteq> 0" by (auto simp: set_pmf_eq)
  with pmf_nonneg[of p x] show "pmf p x > 0" by simp
qed (auto simp: set_pmf_eq)

lemma setsum_pmf_eq_1:
  assumes "finite A" "set_pmf p \<subseteq> A"
  shows   "(\<Sum>x\<in>A. pmf p x) = 1"
proof -
  have "(\<Sum>x\<in>A. pmf p x) = measure_pmf.prob p A"
    by (simp add: measure_measure_pmf_finite assms)
  also from assms have "\<dots> = 1"
    by (subst measure_pmf.prob_eq_1) (auto simp: AE_measure_pmf_iff)
  finally show ?thesis .
qed

lemma map_pmf_of_set:
  assumes "finite A" "A \<noteq> {}"
  shows   "map_pmf f (pmf_of_set A) = pmf_of_multiset (image_mset f (mset_set A))" 
    (is "?lhs = ?rhs")
proof (intro pmf_eqI)
  fix x
  from assms have "ereal (pmf ?lhs x) = ereal (pmf ?rhs x)"
    by (subst ereal_pmf_map)
       (simp_all add: emeasure_pmf_of_set mset_set_empty_iff count_image_mset Int_commute)
  thus "pmf ?lhs x = pmf ?rhs x" by simp
qed

lemma pmf_bind_pmf_of_set:
  assumes "A \<noteq> {}" "finite A"
  shows   "pmf (bind_pmf (pmf_of_set A) f) x = 
             (\<Sum>xa\<in>A. pmf (f xa) x) / real_of_nat (card A)" (is "?lhs = ?rhs")
proof -
  from assms have "ereal ?lhs = ereal ?rhs"
    by (subst ereal_pmf_bind) (simp_all add: nn_integral_pmf_of_set max_def pmf_nonneg)
  thus ?thesis by simp
qed


text \<open>The type of lotteries (a probability mass function)\<close>
type_synonym 'alt lottery = "'alt pmf"

definition lotteries_on :: "'a set \<Rightarrow> 'a lottery set" where
  "lotteries_on A = {p. set_pmf p \<subseteq> A}"

lemma pmf_of_set_lottery:
  "A \<noteq> {} \<Longrightarrow> finite A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> pmf_of_set A \<in> lotteries_on B"
  unfolding lotteries_on_def by auto

lemma pmf_of_list_lottery: 
  "pmf_of_list_wf xs \<Longrightarrow> set (map fst xs) \<subseteq> A \<Longrightarrow> pmf_of_list xs \<in> lotteries_on A"
  using set_pmf_of_list[of xs] by (auto simp: lotteries_on_def)

lemma return_pmf_in_lotteries_on [simp,intro]: 
  "x \<in> A \<Longrightarrow> return_pmf x \<in> lotteries_on A"
  by (simp add: lotteries_on_def)

end