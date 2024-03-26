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

consts partial_order :: "'a \<Rightarrow> bool"

overloading
  partial_order \<equiv> "partial_order :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "(partial_order :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) \<equiv> partial_order_on (\<top> :: 'a \<Rightarrow> bool)"
end

lemma partial_order_eq_partial_order_on:
  "(partial_order :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) = partial_order_on (\<top> :: 'a \<Rightarrow> bool)"
  unfolding partial_order_def ..

lemma partial_order_eq_partial_order_on_uhint [uhint]:
  assumes "P \<equiv> \<top> :: 'a \<Rightarrow> bool"
  shows "(partial_order :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) \<equiv> partial_order_on P"
  using assms by (simp add: partial_order_eq_partial_order_on)

context
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

lemma partial_orderI [intro]:
  assumes "preorder R"
  and "antisymmetric R"
  shows "partial_order R"
  using assms by (urule partial_order_onI)

lemma partial_orderE [elim]:
  assumes "partial_order R"
  obtains "preorder R" "antisymmetric R"
  using assms by (urule (e) partial_order_onE)

lemma partial_order_on_if_partial_order:
  fixes P :: "'a \<Rightarrow> bool"
  assumes "partial_order R"
  shows "partial_order_on P R"
  using assms by (elim partial_orderE)
  (intro partial_order_onI preorder_on_if_preorder antisymmetric_on_if_antisymmetric)

end

end