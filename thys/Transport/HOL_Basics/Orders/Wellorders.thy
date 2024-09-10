\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>creator "Niklas Krofta"\<close>
subsubsection \<open>Well-Orders\<close>
theory Wellorders
  imports
    Binary_Relations_Wellfounded
    Strict_Linear_Orders
begin

definition "wellorder_on \<equiv> strict_linear_order_on \<sqinter> wellfounded_on"

lemma wellorder_onI [intro]:
  assumes "strict_linear_order_on P R" "wellfounded_on P R"
  shows "wellorder_on P R"
  using assms unfolding wellorder_on_def by auto

lemma wellorder_onE [elim]:
  assumes "wellorder_on P R"
  obtains "strict_linear_order_on P R" "wellfounded_on P R"
  using assms unfolding wellorder_on_def by auto

lemma antimono_wellorder_on:
  "antimono (wellorder_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool)"
  using antimono_strict_linear_order_on wellfounded_on_if_le_pred_if_wellfounded_on
  by (intro antimonoI le_predI; elim wellorder_onE) (auto 5 0)

lemma wellorder_on_rel_map_if_injective_on_if_mono_wrt_pred_if_wellorder_on:
  fixes P :: "'a \<Rightarrow> bool"
  assumes "wellorder_on P R" "(Q \<Rightarrow> P) f" "injective_on Q f"
  shows "wellorder_on Q (rel_map f R)"
  using assms
    strict_linear_order_on_rel_map_if_injective_on_if_mono_wrt_pred_if_strict_linear_order_on
    wellfounded_on_rel_map_if_mono_wrt_pred_if_wellfounded_on
  by fastforce


consts wellorder :: "'a \<Rightarrow> bool"

overloading
  wellorder \<equiv> "wellorder :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "(wellorder :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) \<equiv> wellorder_on (\<top> :: 'a \<Rightarrow> bool)"
end

lemma wellorder_eq_wellorder_on:
  "(wellorder :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) = wellorder_on (\<top> :: 'a \<Rightarrow> bool)"
  unfolding wellorder_def ..

lemma wellorder_eq_wellorder_on_uhint [uhint]:
  assumes "P \<equiv> \<top> :: 'a \<Rightarrow> bool"
  shows "(wellorder :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool) \<equiv> wellorder_on P"
  using assms by (simp add: wellorder_eq_wellorder_on)

context
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

lemma wellorderI [intro]:
  assumes "strict_linear_order R"
  and "wellfounded R"
  shows "wellorder R"
  using assms by (urule wellorder_onI)

lemma wellorderE [elim]:
  assumes "wellorder R"
  obtains "strict_linear_order R" "wellfounded R"
  using assms by (urule (e) wellorder_onE)

lemma wellorder_on_if_wellorder:
  fixes P :: "'a \<Rightarrow> bool"
  assumes "wellorder R"
  shows "wellorder_on P R"
  using assms by (elim wellorderE)
  (intro wellorder_onI strict_linear_order_on_if_strict_linear_order wellfounded_on_if_wellfounded)

end


end