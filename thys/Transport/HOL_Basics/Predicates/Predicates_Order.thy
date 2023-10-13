\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Orders\<close>
theory Predicates_Order
  imports
    HOL.Orderings
begin

lemma le_predI [intro]:
  assumes "\<And>x. P x \<Longrightarrow> Q x"
  shows "P \<le> Q"
  using assms by (rule predicate1I)

lemma le_predD [dest]:
  assumes "P \<le> Q"
  and "P x"
  shows "Q x"
  using assms by (rule predicate1D)

lemma le_predE:
  assumes "P \<le> Q"
  and "P x"
  obtains "Q x"
  using assms by blast


end