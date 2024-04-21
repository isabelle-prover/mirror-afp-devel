\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsubsection \<open>Surjective\<close>
theory Binary_Relations_Surjective
  imports
    Binary_Relations_Left_Total
    HOL_Syntax_Bundles_Lattices
begin

consts rel_surjective_at :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

overloading
  rel_surjective_at_pred \<equiv> "rel_surjective_at :: ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "rel_surjective_at_pred P R \<equiv> \<forall>y : P. in_codom R y"
end

lemma rel_surjective_atI [intro]:
  assumes "\<And>y. P y \<Longrightarrow> in_codom R y"
  shows "rel_surjective_at P R"
  unfolding rel_surjective_at_pred_def using assms by blast

lemma rel_surjective_atE [elim]:
  assumes "rel_surjective_at P R"
  and "P y"
  obtains x where "R x y"
  using assms unfolding rel_surjective_at_pred_def by blast

lemma in_codom_if_rel_surjective_at:
  assumes "rel_surjective_at P R"
  and "P y"
  shows "in_codom R y"
  using assms by blast

lemma rel_surjective_at_rel_inv_iff_left_total_on [iff]:
  "rel_surjective_at (P :: 'a \<Rightarrow> bool) (R\<inverse> :: 'b \<Rightarrow> 'a \<Rightarrow> bool) \<longleftrightarrow> left_total_on P R"
  by fast

lemma left_total_on_rel_inv_iff_rel_surjective_at [iff]:
  "left_total_on (P :: 'a \<Rightarrow> bool) (R\<inverse> :: 'a \<Rightarrow> 'b \<Rightarrow> bool) \<longleftrightarrow> rel_surjective_at P R"
  by fast

lemma mono_rel_surjective_at:
  "((\<ge>) \<Rrightarrow>\<^sub>m (\<le>) \<Rrightarrow> (\<le>)) (rel_surjective_at :: ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool)"
  by fastforce

lemma rel_surjective_at_iff_le_codom:
  "rel_surjective_at (P :: 'b \<Rightarrow> bool) (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) \<longleftrightarrow> P \<le> in_codom R"
  by force

lemma rel_surjective_at_compI:
  fixes P :: "'c \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and S :: "'b \<Rightarrow> 'c \<Rightarrow> bool"
  assumes surj_R: "rel_surjective_at (in_dom S) R"
  and surj_S: "rel_surjective_at P S"
  shows "rel_surjective_at P (R \<circ>\<circ> S)"
proof (rule rel_surjective_atI)
  fix y assume "P y"
  then obtain x where "S x y" using surj_S by auto
  moreover then have "in_dom S x" by auto
  moreover then obtain z where "R z x" using surj_R by auto
  ultimately show "in_codom (R \<circ>\<circ> S) y" by blast
qed

consts rel_surjective :: "'a \<Rightarrow> bool"

overloading
  rel_surjective \<equiv> "rel_surjective :: ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
begin
  definition "(rel_surjective :: ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _) \<equiv> rel_surjective_at (\<top> :: 'a \<Rightarrow> bool)"
end

lemma rel_surjective_eq_rel_surjective_at:
  "(rel_surjective :: ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _) = rel_surjective_at (\<top> :: 'a \<Rightarrow> bool)"
  unfolding rel_surjective_def ..

lemma rel_surjective_eq_rel_surjective_at_uhint [uhint]:
  assumes "P \<equiv> (\<top> :: 'a \<Rightarrow> bool)"
  shows "(rel_surjective :: ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _) \<equiv> rel_surjective_at P"
  using assms by (simp add: rel_surjective_eq_rel_surjective_at)

lemma rel_surjectiveI:
  assumes "\<And>y. in_codom R y"
  shows "rel_surjective R"
  using assms by (urule rel_surjective_atI)

lemma rel_surjectiveE:
  assumes "rel_surjective R"
  obtains x where "R x y"
  using assms by (urule (e) rel_surjective_atE where chained = insert) simp

lemma in_codom_if_rel_surjective:
  assumes "rel_surjective R"
  shows "in_codom R y"
  using assms by (blast elim: rel_surjectiveE)

lemma rel_surjective_rel_inv_iff_left_total [iff]: "rel_surjective R\<inverse> \<longleftrightarrow> left_total R"
  by (urule rel_surjective_at_rel_inv_iff_left_total_on)

lemma left_total_rel_inv_iff_rel_surjective [iff]: "left_total R\<inverse> \<longleftrightarrow> rel_surjective R"
  by (urule left_total_on_rel_inv_iff_rel_surjective_at)

lemma rel_surjective_at_if_surjective:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'b \<Rightarrow> 'a \<Rightarrow> bool"
  assumes "rel_surjective R"
  shows "rel_surjective_at P R"
  using assms by (intro rel_surjective_atI) (blast dest: in_codom_if_rel_surjective)


end