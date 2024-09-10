\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Linear Orders\<close>
theory Linear_Orders
  imports
    Binary_Relations_Connected
    Partial_Orders
begin

definition "linear_order_on \<equiv> partial_order_on \<sqinter> connected_on"

lemma linear_order_onI [intro]:
  assumes "partial_order_on P R"
  and "connected_on P R"
  shows "linear_order_on P R"
  using assms unfolding linear_order_on_def by auto

lemma linear_order_onE [elim]:
  assumes "linear_order_on P R"
  obtains "partial_order_on P R" "connected_on P R"
  using assms unfolding linear_order_on_def by auto

consts linear_order :: "'a \<Rightarrow> bool"

overloading
  linear_order \<equiv> "linear_order :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "(linear_order :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) \<equiv> linear_order_on (\<top> :: 'a \<Rightarrow> bool)"
end

lemma linear_order_eq_linear_order_on:
  "(linear_order :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) = linear_order_on (\<top> :: 'a \<Rightarrow> bool)"
  unfolding linear_order_def ..

lemma linear_order_eq_linear_order_on_uhint [uhint]:
  assumes "P \<equiv> \<top> :: 'a \<Rightarrow> bool"
  shows "(linear_order :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) \<equiv> linear_order_on P"
  using assms by (simp add: linear_order_eq_linear_order_on)

context
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

lemma linear_orderI [intro]:
  assumes "partial_order R"
  and "connected R"
  shows "linear_order R"
  using assms by (urule linear_order_onI)

lemma linear_orderE [elim]:
  assumes "linear_order R"
  obtains "partial_order R" "connected R"
  using assms by (urule (e) linear_order_onE)

lemma linear_order_on_if_linear_order:
  fixes P :: "'a \<Rightarrow> bool"
  assumes "linear_order R"
  shows "linear_order_on P R"
  using assms by (elim linear_orderE)
  (intro linear_order_onI partial_order_on_if_partial_order connected_on_if_connected)

end

end