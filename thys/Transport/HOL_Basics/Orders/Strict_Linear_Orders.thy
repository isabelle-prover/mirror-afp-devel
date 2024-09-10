\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Niklas Krofta"\<close>
subsection \<open>Strict Linear Orders\<close>
theory Strict_Linear_Orders
  imports
    Binary_Relations_Connected
    Strict_Partial_Orders
begin

definition "strict_linear_order_on \<equiv> strict_partial_order_on \<sqinter> connected_on"

lemma strict_linear_order_onI [intro]:
  assumes "strict_partial_order_on P R" "connected_on P R"
  shows "strict_linear_order_on P R"
  using assms unfolding strict_linear_order_on_def by auto

lemma strict_linear_order_onE [elim]:
  assumes "strict_linear_order_on P R"
  obtains "strict_partial_order_on P R" "connected_on P R"
  using assms unfolding strict_linear_order_on_def by auto

lemma antimono_strict_linear_order_on:
  "antimono (strict_linear_order_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool)"
  using antimono_strict_partial_order_on antimono_connected_on
  by (intro antimonoI le_predI; elim strict_linear_order_onE) auto

lemma strict_linear_order_on_rel_map_if_injective_on_if_mono_wrt_pred_if_strict_linear_order_on:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "strict_linear_order_on P R"
  and "(Q \<Rightarrow> P) f"
  and "injective_on Q f"
  shows "strict_linear_order_on Q (rel_map f R)"
  using assms by (intro strict_linear_order_onI
    strict_partial_order_on_rel_map_if_mono_wrt_pred_if_strict_partial_order_on
    connected_on_rel_map_if_injective_on_if_mono_wrt_pred_if_connected_on)
  auto

consts strict_linear_order :: "'a \<Rightarrow> bool"

overloading
  strict_linear_order \<equiv> "strict_linear_order :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "(strict_linear_order :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) \<equiv> strict_linear_order_on (\<top> :: 'a \<Rightarrow> bool)"
end

lemma strict_linear_order_eq_strict_linear_order_on:
  "(strict_linear_order :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) = strict_linear_order_on (\<top> :: 'a \<Rightarrow> bool)"
  unfolding strict_linear_order_def ..

lemma strict_linear_order_eq_strict_linear_order_on_uhint [uhint]:
  assumes "P \<equiv> \<top> :: 'a \<Rightarrow> bool"
  shows "(strict_linear_order :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) \<equiv> strict_linear_order_on P"
  using assms by (simp add: strict_linear_order_eq_strict_linear_order_on)

context
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

lemma strict_linear_orderI [intro]:
  assumes "strict_partial_order R"
  and "connected R"
  shows "strict_linear_order R"
  using assms by (urule strict_linear_order_onI)

lemma strict_linear_orderE [elim]:
  assumes "strict_linear_order R"
  obtains "strict_partial_order R" "connected R"
  using assms by (urule (e) strict_linear_order_onE)

lemma strict_linear_order_on_if_strict_linear_order:
  fixes P :: "'a \<Rightarrow> bool"
  assumes "strict_linear_order R"
  shows "strict_linear_order_on P R"
  using assms by (elim strict_linear_orderE)
  (intro strict_linear_order_onI strict_partial_order_on_if_strict_partial_order
    connected_on_if_connected)

end

end