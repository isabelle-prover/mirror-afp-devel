\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Bi-Total\<close>
theory Binary_Relations_Bi_Total
  imports
    Binary_Relations_Left_Total
    Binary_Relations_Surjective
begin

definition "bi_total_on P Q \<equiv> left_total_on P \<sqinter> rel_surjective_at Q"

lemma bi_total_onI [intro]:
  assumes "left_total_on P R"
  and "rel_surjective_at Q R"
  shows "bi_total_on P Q R"
  unfolding bi_total_on_def using assms by auto

lemma bi_total_onE [elim]:
  assumes "bi_total_on P Q R"
  obtains "left_total_on P R" "rel_surjective_at Q R"
  using assms unfolding bi_total_on_def by auto

definition "bi_total \<equiv> bi_total_on (\<top> :: 'a \<Rightarrow> bool) (\<top> :: 'b \<Rightarrow> bool) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"

lemma bi_total_eq_bi_total_on:
  "(bi_total :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool) = bi_total_on (\<top> :: 'a \<Rightarrow> bool) (\<top> :: 'b \<Rightarrow> bool)"
  unfolding bi_total_def ..

lemma bi_total_eq_bi_total_on_uhint [uhint]:
  assumes "P \<equiv> (\<top> :: 'a \<Rightarrow> bool)"
  and "Q \<equiv> (\<top> :: 'b \<Rightarrow> bool)"
  shows "(bi_total :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool) \<equiv> bi_total_on P Q"
  using assms by (simp add: bi_total_eq_bi_total_on)

lemma bi_totalI [intro]:
  assumes "left_total R"
  and "rel_surjective R"
  shows "bi_total R"
  using assms by (urule bi_total_onI)

lemma bi_totalE [elim]:
  assumes "bi_total R"
  obtains "left_total R" "rel_surjective R"
  using assms by (urule (e) bi_total_onE)

end