\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Strict Partial Orders\<close>
theory Strict_Partial_Orders
  imports
    Binary_Relations_Asymmetric
    Binary_Relations_Transitive
begin

definition "strict_partial_order_on \<equiv> transitive_on \<sqinter> asymmetric_on"

lemma strict_partial_order_onI [intro]:
  assumes "transitive_on P R"
  and "asymmetric_on P R"
  shows "strict_partial_order_on P R"
  unfolding strict_partial_order_on_def using assms by auto

lemma strict_partial_order_onE [elim]:
  assumes "strict_partial_order_on P R"
  obtains "transitive_on P R" "asymmetric_on P R"
  using assms unfolding strict_partial_order_on_def by auto

lemma transitive_if_strict_partial_order_on_in_field:
  assumes "strict_partial_order_on (in_field R) R"
  shows "transitive R"
  using assms by (elim strict_partial_order_onE) (rule transitive_if_transitive_on_in_field)

lemma asymmetric_if_strict_partial_order_on_in_field:
  assumes "strict_partial_order_on (in_field R) R"
  shows "asymmetric R"
  using assms by (elim strict_partial_order_onE) (rule asymmetric_if_asymmetric_on_in_field)

lemma antimono_strict_partial_order_on:
  "antimono (strict_partial_order_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool)"
  using antimono_transitive_on antimono_asymmetric_on
  by (intro antimonoI le_predI; elim strict_partial_order_onE) auto

lemma strict_partial_order_on_rel_map_if_mono_wrt_pred_if_strict_partial_order_on:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "strict_partial_order_on P R"
  and "(Q \<Rightarrow> P) f"
  shows "strict_partial_order_on Q (rel_map f R)"
  using assms by (intro strict_partial_order_onI
    asymmetric_on_rel_map_if_mono_wrt_pred_if_asymmetric_on
    transitive_on_rel_map_if_mono_wrt_pred_if_transitive_on)
   auto

consts strict_partial_order :: "'a \<Rightarrow> bool"

overloading
  strict_partial_order \<equiv> "strict_partial_order :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "(strict_partial_order :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) \<equiv> strict_partial_order_on (\<top> :: 'a \<Rightarrow> bool)"
end

lemma strict_partial_order_eq_strict_partial_order_on:
  "(strict_partial_order :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) = strict_partial_order_on (\<top> :: 'a \<Rightarrow> bool)"
  unfolding strict_partial_order_def ..

lemma strict_partial_order_eq_strict_partial_order_on_uhint [uhint]:
  assumes "P \<equiv> \<top> :: 'a \<Rightarrow> bool"
  shows "(strict_partial_order :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) \<equiv> strict_partial_order_on P"
  using assms by (simp add: strict_partial_order_eq_strict_partial_order_on)

context
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

lemma strict_partial_orderI [intro]:
  assumes "transitive R"
  and "asymmetric R"
  shows "strict_partial_order R"
  using assms by (urule strict_partial_order_onI)

lemma strict_partial_orderE [elim]:
  assumes "strict_partial_order R"
  obtains "transitive R" "asymmetric R"
  using assms by (urule (e) strict_partial_order_onE)

lemma strict_partial_order_on_if_strict_partial_order:
  fixes P :: "'a \<Rightarrow> bool"
  assumes "strict_partial_order R"
  shows "strict_partial_order_on P R"
  using assms by (elim strict_partial_orderE)
  (intro strict_partial_order_onI transitive_on_if_transitive asymmetric_on_if_asymmetric)

end

end