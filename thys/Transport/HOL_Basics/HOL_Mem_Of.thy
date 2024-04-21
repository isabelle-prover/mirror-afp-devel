\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_Mem_Of
  imports
    HOL.Set
    ML_Unification.ML_Unification_HOL_Setup
begin

definition "mem_of A x \<equiv> x \<in> A"
lemma mem_of_eq: "mem_of = (\<lambda>A x. x \<in> A)" unfolding mem_of_def by simp
lemma mem_of_iff [iff]: "mem_of A x \<longleftrightarrow> x \<in> A" unfolding mem_of_def by simp

lemma mem_of_eq_mem_uhint [uhint]:
  assumes "x \<equiv> x'"
  and "A \<equiv> A'"
  shows "mem_of A x \<equiv> x' \<in> A'"
  using assms by simp

lemma mem_of_UNIV_eq_top [simp]: "mem_of UNIV = \<top>"
  by auto

lemma mem_of_empty_eq_bot [simp]: "mem_of {} = \<bottom>"
  by auto


end