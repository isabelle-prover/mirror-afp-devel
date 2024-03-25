\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Order\<close>
theory Binary_Relations_Order_Base
  imports
    Binary_Relation_Functions
    HOL.Orderings
begin

lemma le_relI [intro]:
  assumes "\<And>x y. R x y \<Longrightarrow> S x y"
  shows "R \<le> S"
  using assms by (rule predicate2I)

lemma le_relD [dest]:
  assumes "R \<le> S"
  and "R x y"
  shows "S x y"
  using assms by (rule predicate2D)

lemma le_relE:
  assumes "R \<le> S"
  and "R x y"
  obtains "S x y"
  using assms by blast

end