theory Selection_Function
  imports Ordered_Resolution_Prover.Clausal_Logic
begin

locale selection_function =
  fixes select :: "'a clause \<Rightarrow> 'a clause"
  assumes
    select_subset: "\<And>C. select C \<subseteq># C" and
    select_negative_literals: "\<And>C l. l \<in># select C \<Longrightarrow> is_neg l"

end
