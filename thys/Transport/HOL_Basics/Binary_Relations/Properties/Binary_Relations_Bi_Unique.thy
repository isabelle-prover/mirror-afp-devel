\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Bi-Unique\<close>
theory Binary_Relations_Bi_Unique
  imports
    Binary_Relations_Injective
    Binary_Relations_Right_Unique
begin

definition "bi_unique_on \<equiv> right_unique_on \<sqinter> rel_injective_on"

lemma bi_unique_onI [intro]:
  assumes "right_unique_on P R"
  and "rel_injective_on P R"
  shows "bi_unique_on P R"
  unfolding bi_unique_on_def using assms by auto

lemma bi_unique_onE [elim]:
  assumes "bi_unique_on P R"
  obtains "right_unique_on P R" "rel_injective_on P R"
  using assms unfolding bi_unique_on_def by auto

lemma bi_unique_on_rel_inv_if_Fun_Rel_iff_if_bi_unique_on:
  assumes "bi_unique_on P R"
  and "(R \<Rrightarrow> (\<longleftrightarrow>)) P Q"
  shows "bi_unique_on Q R\<inverse>"
  using assms by (intro bi_unique_onI
    rel_injective_on_if_Fun_Rel_imp_if_rel_injective_at
    right_unique_on_if_Fun_Rel_imp_if_right_unique_at)
  (auto 0 3)

definition "bi_unique \<equiv> bi_unique_on (\<top> :: 'a \<Rightarrow> bool) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"

lemma bi_unique_eq_bi_unique_on:
  "bi_unique = (bi_unique_on (\<top> :: 'a \<Rightarrow> bool) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool)"
  unfolding bi_unique_def ..

lemma bi_unique_eq_bi_unique_on_uhint [uhint]:
  assumes "P \<equiv> (\<top> :: 'a \<Rightarrow> bool)"
  shows "bi_unique \<equiv> (bi_unique_on P :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool)"
  using assms by (simp add: bi_unique_eq_bi_unique_on)

lemma bi_uniqueI [intro]:
  assumes "right_unique R"
  and "rel_injective R"
  shows "bi_unique R"
  using assms by (urule bi_unique_onI)

lemma bi_uniqueE [elim]:
  assumes "bi_unique R"
  obtains "right_unique R" "rel_injective R"
  using assms by (urule (e) bi_unique_onE)

end