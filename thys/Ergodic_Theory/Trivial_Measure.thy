(*
   File:     Trivial_Measure.thy
   Author:   Manuel Eberl, TU München
*)
theory Trivial_Measure
  imports "HOL-Analysis.Analysis"
begin

(* TODO: could be put in the distribution *)

subsection \<open>The trivial measurable space\<close>

text \<open>
  The trivial measurable space is the smallest possible \<open>\<sigma>\<close>-algebra, i.e. only the empty set
  and everything.
\<close>
definition trivial_measure :: "'a set \<Rightarrow> 'a measure" where
  "trivial_measure X = sigma X {{}, X}"

lemma space_trivial_measure [simp]: "space (trivial_measure X) = X"
  by (simp add: trivial_measure_def)

lemma sets_trivial_measure: "sets (trivial_measure X) = {{}, X}"
  by (simp add: trivial_measure_def sigma_algebra_trivial sigma_algebra.sigma_sets_eq)

lemma measurable_trivial_measure:
  assumes "f \<in> space M \<rightarrow> X" and "f -` X \<inter> space M \<in> sets M"
  shows   "f \<in> M \<rightarrow>\<^sub>M trivial_measure X"
  using assms unfolding measurable_def by (auto simp: sets_trivial_measure)

lemma measurable_trivial_measure_iff:
  "f \<in> M \<rightarrow>\<^sub>M trivial_measure X \<longleftrightarrow> f \<in> space M \<rightarrow> X \<and> f -` X \<inter> space M \<in> sets M"
  unfolding measurable_def by (auto simp: sets_trivial_measure)


definition (in sigma_algebra) induced_algebra :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b set \<Rightarrow> 'b set set" where
  "induced_algebra f \<Omega>' = sigma_sets \<Omega>' {f -` A \<inter> \<Omega>' |A. A \<in> M}"

lemma (in sigma_algebra) sigma_algebra_induced: "sigma_algebra \<Omega>' (induced_algebra f \<Omega>')"
  unfolding induced_algebra_def by (rule sigma_algebra_sigma_sets) auto

lemma (in sigma_algebra) in_induced_algebra: "A \<in> M \<Longrightarrow> f -` A \<inter> \<Omega>' \<in> induced_algebra f \<Omega>'"
  unfolding induced_algebra_def by (rule sigma_sets.Basic) auto

end