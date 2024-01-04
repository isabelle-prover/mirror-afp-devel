\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Partial Orders\<close>
theory Partial_Orders
  imports
    Binary_Relations_Antisymmetric
    Preorders
begin

definition "partial_order_on \<equiv> preorder_on \<sqinter> antisymmetric_on"

lemma partial_order_onI [intro]:
  assumes "preorder_on P R"
  and "antisymmetric_on P R"
  shows "partial_order_on P R"
  unfolding partial_order_on_def using assms by auto

lemma partial_order_onE [elim]:
  assumes "partial_order_on P R"
  obtains "preorder_on P R" "antisymmetric_on P R"
  using assms unfolding partial_order_on_def by auto

lemma transitive_if_partial_order_on_in_field:
  assumes "partial_order_on (in_field R) R"
  shows "transitive R"
  using assms by (elim partial_order_onE) (rule transitive_if_preorder_on_in_field)

lemma antisymmetric_if_partial_order_on_in_field:
  assumes "partial_order_on (in_field R) R"
  shows "antisymmetric R"
  using assms by (elim partial_order_onE)
  (rule antisymmetric_if_antisymmetric_on_in_field)

definition "(partial_order :: ('a \<Rightarrow> _) \<Rightarrow> bool) \<equiv> partial_order_on (\<top> :: 'a \<Rightarrow> bool)"

lemma partial_order_eq_partial_order_on:
  "(partial_order :: ('a \<Rightarrow> _) \<Rightarrow> bool) = partial_order_on (\<top> :: 'a \<Rightarrow> bool)"
  unfolding partial_order_def ..

lemma partial_orderI [intro]:
  assumes "preorder R"
  and "antisymmetric R"
  shows "partial_order R"
  unfolding partial_order_eq_partial_order_on using assms
  by (intro partial_order_onI preorder_on_if_preorder antisymmetric_on_if_antisymmetric)

lemma partial_orderE [elim]:
  assumes "partial_order R"
  obtains "preorder R" "antisymmetric R"
  using assms unfolding partial_order_eq_partial_order_on
  by (elim partial_order_onE)
  (simp only: preorder_eq_preorder_on antisymmetric_eq_antisymmetric_on)

lemma partial_order_on_if_partial_order:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> _"
  assumes "partial_order R"
  shows "partial_order_on P R"
  using assms by (elim partial_orderE)
  (intro partial_order_onI preorder_on_if_preorder antisymmetric_on_if_antisymmetric)


end