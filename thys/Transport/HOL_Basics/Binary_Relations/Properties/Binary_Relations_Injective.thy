\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Injective\<close>
theory Binary_Relations_Injective
  imports
    Functions_Monotone
    Reverse_Implies
begin

consts rel_injective_on :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

overloading
  rel_injective_on_pred \<equiv> "rel_injective_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "rel_injective_on_pred P R \<equiv> \<forall>x x' : P. \<forall>y. R x y \<and> R x' y \<longrightarrow> x = x'"
end

lemma rel_injective_onI [intro]:
  assumes "\<And>x x' y. P x \<Longrightarrow> P x' \<Longrightarrow> R x y \<Longrightarrow> R x' y \<Longrightarrow> x = x'"
  shows "rel_injective_on P R"
  unfolding rel_injective_on_pred_def using assms by blast

lemma rel_injective_onD:
  assumes "rel_injective_on P R"
  and "P x" "P x'"
  and "R x y" "R x' y"
  shows "x = x'"
  using assms unfolding rel_injective_on_pred_def by blast

lemma antimono_rel_injective_on:
  "((\<le>) \<Rrightarrow>\<^sub>m (\<le>) \<Rrightarrow> (\<ge>)) (rel_injective_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool)"
  by (intro mono_wrt_relI) (auto dest: rel_injective_onD intro!: rel_injective_onI)


consts rel_injective_at :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

overloading
  rel_injective_at_pred \<equiv> "rel_injective_at :: ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "rel_injective_at_pred P R \<equiv> \<forall>x x' y. P y \<and> R x y \<and> R x' y \<longrightarrow> x = x'"
end

lemma rel_injective_atI [intro]:
  assumes "\<And>x x' y. P y \<Longrightarrow> R x y \<Longrightarrow> R x' y \<Longrightarrow> x = x'"
  shows "rel_injective_at P R"
  unfolding rel_injective_at_pred_def using assms by blast

lemma rel_injective_atD:
  assumes "rel_injective_at P R"
  and "P y"
  and "R x y" "R x' y"
  shows "x = x'"
  using assms unfolding rel_injective_at_pred_def by blast

lemma rel_injective_on_if_Fun_Rel_imp_if_rel_injective_at:
  assumes "rel_injective_at (Q :: 'b \<Rightarrow> bool) (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool)"
  and "(R \<Rrightarrow> (\<longrightarrow>)) P Q"
  shows "rel_injective_on P R"
  using assms by (intro rel_injective_onI) (auto dest: rel_injective_atD)

lemma rel_injective_at_if_Fun_Rel_rev_imp_if_rel_injective_on:
  assumes "rel_injective_on (P :: 'a \<Rightarrow> bool) (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool)"
  and "(R \<Rrightarrow> (\<longleftarrow>)) P Q"
  shows "rel_injective_at Q R"
  using assms by (intro rel_injective_atI) (auto dest: rel_injective_onD)


consts rel_injective :: "'a \<Rightarrow> bool"

overloading
  rel_injective \<equiv> "rel_injective :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "(rel_injective :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool) \<equiv> rel_injective_on (\<top> :: 'a \<Rightarrow> bool)"
end

lemma rel_injective_eq_rel_injective_on:
  "(rel_injective :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> _) = rel_injective_on (\<top> :: 'a \<Rightarrow> bool)"
  unfolding rel_injective_def ..

lemma rel_injective_eq_rel_injective_on_uhint [uhint]:
  assumes "P \<equiv> (\<top> :: 'a \<Rightarrow> bool)"
  shows "rel_injective :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> _ \<equiv> rel_injective_on P"
  using assms by (simp add: rel_injective_eq_rel_injective_on)

lemma rel_injectiveI [intro]:
  assumes "\<And>x x' y. R x y \<Longrightarrow> R x' y \<Longrightarrow> x = x'"
  shows "rel_injective R"
  using assms by (urule rel_injective_onI)

lemma rel_injectiveD:
  assumes "rel_injective R"
  and "R x y" "R x' y"
  shows "x = x'"
  using assms by (urule (d) rel_injective_onD where chained = insert) simp_all

lemma rel_injective_eq_rel_injective_at:
  "(rel_injective :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool) = rel_injective_at (\<top> :: 'b \<Rightarrow> bool)"
  by (intro ext iffI rel_injectiveI) (auto dest: rel_injective_atD rel_injectiveD)

lemma rel_injective_eq_rel_injective_at_uhint [uhint]:
  assumes "P \<equiv> (\<top> :: 'b \<Rightarrow> bool)"
  shows "rel_injective :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool \<equiv> rel_injective_at P"
  using assms by (simp add: rel_injective_eq_rel_injective_at)

lemma rel_injective_on_if_rel_injective:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes "rel_injective R"
  shows "rel_injective_on P R"
  using assms by (blast dest: rel_injectiveD)

lemma rel_injective_at_if_rel_injective:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'b \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "rel_injective R"
  shows "rel_injective_at P R"
  using assms by (blast dest: rel_injectiveD)

lemma rel_injective_if_rel_injective_on_in_dom:
  assumes "rel_injective_on (in_dom R) R"
  shows "rel_injective R"
  using assms by (blast dest: rel_injective_onD)

lemma rel_injective_if_rel_injective_at_in_codom:
  assumes "rel_injective_at (in_codom R) R"
  shows "rel_injective R"
  using assms by (blast dest: rel_injective_atD)

corollary rel_injective_on_in_dom_iff_rel_injective [simp]:
  "rel_injective_on (in_dom R) R \<longleftrightarrow> rel_injective R"
  using rel_injective_if_rel_injective_on_in_dom rel_injective_on_if_rel_injective
  by blast

corollary rel_injective_at_in_codom_iff_rel_injective [iff]:
  "rel_injective_at (in_codom R) R \<longleftrightarrow> rel_injective R"
  using rel_injective_if_rel_injective_at_in_codom rel_injective_at_if_rel_injective
  by blast

lemma rel_injective_on_compI:
  fixes P :: "'a \<Rightarrow> bool"
  assumes "rel_injective (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool)"
  and "rel_injective_on (in_codom R \<sqinter> in_dom S) (S :: 'b \<Rightarrow> 'c \<Rightarrow> bool)"
  shows "rel_injective_on P (R \<circ>\<circ> S)"
proof (rule rel_injective_onI)
  fix x x' y
  assume "P x" "P x'" "(R \<circ>\<circ> S) x y" "(R \<circ>\<circ> S) x' y"
  then obtain z z' where "R x z" "S z y" "R x' z'" "S z' y" by blast
  with assms have "z = z'" by (auto dest: rel_injective_onD)
  with \<open>R x z\<close> \<open>R x' z'\<close> assms show "x = x'" by (auto dest: rel_injectiveD)
qed


end