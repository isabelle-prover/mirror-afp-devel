\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory HOL_Mem_Of
  imports
    HOL.Set
begin

definition "mem_of A x \<equiv> x \<in> A"
lemma mem_of_eq [simp]: "mem_of \<equiv> \<lambda>A x. x \<in> A" unfolding mem_of_def by simp
lemma mem_of_iff [iff]: "mem_of A x \<longleftrightarrow> x \<in> A" by simp

end