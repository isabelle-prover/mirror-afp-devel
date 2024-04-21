\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Right Unique\<close>
theory Binary_Relations_Right_Unique
  imports
    Binary_Relations_Injective
    Binary_Relations_Extend
begin

consts right_unique_on :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

overloading
  right_unique_on_pred \<equiv> "right_unique_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "right_unique_on_pred P R \<equiv> \<forall>x : P. \<forall> y y'. R x y \<and> R x y' \<longrightarrow> y = y'"
end

lemma right_unique_onI [intro]:
  assumes "\<And>x y y'. P x \<Longrightarrow> R x y \<Longrightarrow> R x y' \<Longrightarrow> y = y'"
  shows "right_unique_on P R"
  using assms unfolding right_unique_on_pred_def by blast

lemma right_unique_onD:
  assumes "right_unique_on P R"
  and "P x"
  and "R x y" "R x y'"
  shows "y = y'"
  using assms unfolding right_unique_on_pred_def by blast

lemma antimono_right_unique_on:
  "((\<le>) \<Rrightarrow>\<^sub>m (\<le>) \<Rrightarrow> (\<ge>)) (right_unique_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool)"
  by (fastforce dest: right_unique_onD)

lemma mono_right_unique_on_top_right_unique_on_inf_rel_restrict_left:
  "((R : right_unique_on P) \<Rrightarrow>\<^sub>m (P' : \<top>) \<Rrightarrow>\<^sub>m right_unique_on (P \<sqinter> P')) rel_restrict_left"
  by (fast dest: right_unique_onD)

lemma mono_right_unique_on_comp:
  "((R : right_unique_on P) \<Rrightarrow>\<^sub>m right_unique_on (in_codom (R\<restriction>\<^bsub>P\<^esub>)) \<Rrightarrow>\<^sub>m right_unique_on P) (\<circ>\<circ>)"
  by (fast dest: right_unique_onD)

context
  fixes P :: "'a \<Rightarrow> bool" and \<R> :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
begin

lemma right_unique_on_glue_if_right_unique_on_sup:
  assumes "\<And>R R'. \<R> R \<Longrightarrow> \<R> R' \<Longrightarrow> right_unique_on P (R \<squnion> R')"
  shows "right_unique_on P (glue \<R>)"
  using assms by (fastforce dest: right_unique_onD)

lemma right_unique_on_if_right_unique_on_glue:
  assumes "right_unique_on P (glue \<R>)"
  and "\<R> R"
  shows "right_unique_on P R"
  using assms by (intro right_unique_onI) (auto dest: right_unique_onD)

end

consts right_unique_at :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

overloading
  right_unique_at_pred \<equiv> "right_unique_at :: ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "right_unique_at_pred P R \<equiv> \<forall>x y y'. P y \<and> P y' \<and> R x y \<and> R x y' \<longrightarrow> y = y'"
end

lemma right_unique_atI [intro]:
  assumes "\<And>x y y'. P y \<Longrightarrow> P y' \<Longrightarrow> R x y \<Longrightarrow> R x y' \<Longrightarrow> y = y'"
  shows "right_unique_at P R"
  using assms unfolding right_unique_at_pred_def by blast

lemma right_unique_atD:
  assumes "right_unique_at P R"
  and "P y"
  and "P y'"
  and "R x y" "R x y'"
  shows "y = y'"
  using assms unfolding right_unique_at_pred_def by blast

lemma right_unique_at_rel_inv_iff_rel_injective_on [iff]:
  "right_unique_at (P :: 'a \<Rightarrow> bool) (R\<inverse> :: 'b \<Rightarrow> 'a \<Rightarrow> bool) \<longleftrightarrow> rel_injective_on P R"
  by (blast dest: right_unique_atD rel_injective_onD)

lemma rel_injective_on_rel_inv_iff_right_unique_at [iff]:
  "rel_injective_on (P :: 'a \<Rightarrow> bool) (R\<inverse> :: 'a \<Rightarrow> 'b \<Rightarrow> bool) \<longleftrightarrow> right_unique_at P R"
  by (blast dest: right_unique_atD rel_injective_onD)

lemma right_unique_on_rel_inv_iff_rel_injective_at [iff]:
  "right_unique_on (P :: 'a \<Rightarrow> bool) (R\<inverse> :: 'a \<Rightarrow> 'b \<Rightarrow> bool) \<longleftrightarrow> rel_injective_at P R"
  by (blast dest: right_unique_onD rel_injective_atD)

lemma rel_injective_at_rel_inv_iff_right_unique_on [iff]:
  "rel_injective_at (P :: 'b \<Rightarrow> bool) (R\<inverse> :: 'a \<Rightarrow> 'b \<Rightarrow> bool) \<longleftrightarrow> right_unique_on P R"
  by (blast dest: right_unique_onD rel_injective_atD)

lemma right_unique_on_if_Fun_Rel_imp_if_right_unique_at:
  assumes "right_unique_at (Q :: 'b \<Rightarrow> bool) (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool)"
  and "(R \<Rrightarrow> (\<longrightarrow>)) P Q"
  shows "right_unique_on P R"
  using assms by (intro right_unique_onI) (auto dest: right_unique_atD)

lemma right_unique_at_if_Fun_Rel_rev_imp_if_right_unique_on:
  assumes "right_unique_on (P :: 'a \<Rightarrow> bool) (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool)"
  and "(R \<Rrightarrow> (\<longleftarrow>)) P Q"
  shows "right_unique_at Q R"
  using assms by (intro right_unique_atI) (auto dest: right_unique_onD)


consts right_unique :: "'a \<Rightarrow> bool"

overloading
  right_unique \<equiv> "right_unique :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "(right_unique :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool) \<equiv> right_unique_on (\<top> :: 'a \<Rightarrow> bool)"
end

lemma right_unique_eq_right_unique_on:
  "(right_unique :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> _) = right_unique_on (\<top> :: 'a \<Rightarrow> bool)"
  unfolding right_unique_def ..

lemma right_unique_eq_right_unique_on_uhint [uhint]:
  assumes "P \<equiv> (\<top> :: 'a \<Rightarrow> bool)"
  shows "right_unique :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> _ \<equiv> right_unique_on P"
  using assms by (simp only: right_unique_eq_right_unique_on)

lemma right_uniqueI [intro]:
  assumes "\<And>x y y'. R x y \<Longrightarrow> R x y' \<Longrightarrow> y = y'"
  shows "right_unique R"
  using assms by (urule right_unique_onI)

lemma right_uniqueD:
  assumes "right_unique R"
  and "R x y" "R x y'"
  shows "y = y'"
  using assms by (urule (d) right_unique_onD where chained = insert) simp_all

lemma right_unique_eq_right_unique_at:
  "(right_unique :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool) = right_unique_at (\<top> :: 'b \<Rightarrow> bool)"
  by (intro ext iffI right_uniqueI) (auto dest: right_unique_atD right_uniqueD)

lemma right_unique_eq_right_unique_at_uhint [uhint]:
  assumes "P \<equiv> (\<top> :: 'b \<Rightarrow> bool)"
  shows "right_unique :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> _ \<equiv> right_unique_at P"
  using assms by (simp only: right_unique_eq_right_unique_at)

lemma right_unique_on_if_right_unique:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes "right_unique R"
  shows "right_unique_on P R"
  using assms by (blast dest: right_uniqueD)

lemma right_unique_at_if_right_unique:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'b \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "right_unique R"
  shows "right_unique_at P R"
  using assms by (blast dest: right_uniqueD)

lemma right_unique_if_right_unique_on_in_dom:
  assumes "right_unique_on (in_dom R) R"
  shows "right_unique R"
  using assms by (blast dest: right_unique_onD)

lemma right_unique_if_right_unique_at_in_codom:
  assumes "right_unique_at (in_codom R) R"
  shows "right_unique R"
  using assms by (blast dest: right_unique_atD)

corollary right_unique_on_in_dom_iff_right_unique [iff]:
  "right_unique_on (in_dom R) R \<longleftrightarrow> right_unique R"
  using right_unique_if_right_unique_on_in_dom right_unique_on_if_right_unique
  by blast

corollary right_unique_at_in_codom_iff_right_unique [iff]:
  "right_unique_at (in_codom R) R \<longleftrightarrow> right_unique R"
  using right_unique_if_right_unique_at_in_codom right_unique_at_if_right_unique
  by blast

lemma right_unique_rel_inv_iff_rel_injective [iff]:
  "right_unique R\<inverse> \<longleftrightarrow> rel_injective R"
  by (blast dest: right_uniqueD rel_injectiveD)

lemma rel_injective_rel_inv_iff_right_unique [iff]:
  "rel_injective R\<inverse> \<longleftrightarrow> right_unique R"
  by (blast dest: right_uniqueD rel_injectiveD)


paragraph \<open>Instantiations\<close>

lemma right_unique_eq: "right_unique (=)"
  by (rule right_uniqueI) blast


end