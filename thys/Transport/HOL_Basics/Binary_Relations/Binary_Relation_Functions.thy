\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Binary Relations\<close>
subsection \<open>Basic Functions\<close>
theory Binary_Relation_Functions
  imports
    HOL_Basics_Base
begin

paragraph \<open>Summary\<close>
text \<open>Basic functions on binary relations.\<close>

definition "rel_comp R S x y \<equiv> \<exists>z. R x z \<and> S z y"

bundle rel_comp_syntax begin notation rel_comp (infixl "\<circ>\<circ>" 55) end
bundle no_rel_comp_syntax begin no_notation rel_comp (infixl "\<circ>\<circ>" 55) end
unbundle rel_comp_syntax

lemma rel_compI [intro]:
  assumes "R x y"
  and "S y z"
  shows "(R \<circ>\<circ> S) x z"
  using assms unfolding rel_comp_def by blast

lemma rel_compE [elim]:
  assumes "(R \<circ>\<circ> S) x y"
  obtains z where "R x z" "S z y"
  using assms unfolding rel_comp_def by blast

lemma rel_comp_assoc: "R \<circ>\<circ> (S \<circ>\<circ> T) = (R \<circ>\<circ> S) \<circ>\<circ> T"
  by (intro ext) blast

definition rel_inv :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool"
  where "rel_inv R x y \<equiv> R y x"

bundle rel_inv_syntax begin notation rel_inv ("(_\<inverse>)" [1000]) end
bundle no_rel_inv_syntax begin no_notation rel_inv ("(_\<inverse>)" [1000]) end
unbundle rel_inv_syntax

lemma rel_invI [intro]:
  assumes "R x y"
  shows "R\<inverse> y x"
  using assms unfolding rel_inv_def .

lemma rel_invD [dest]:
  assumes "R\<inverse> x y"
  shows "R y x"
  using assms unfolding rel_inv_def .

lemma rel_inv_iff_rel [simp]: "R\<inverse> x y \<longleftrightarrow> R y x"
  by blast

lemma rel_inv_comp_eq [simp]: "(R \<circ>\<circ> S)\<inverse> = S\<inverse> \<circ>\<circ> R\<inverse>"
  by (intro ext) blast

lemma rel_inv_inv_eq_self [simp]: "R\<inverse>\<inverse> = R"
  by blast

lemma rel_inv_eq_iff_eq [iff]: "R\<inverse> = S\<inverse> \<longleftrightarrow> R = S"
  by (blast dest: fun_cong)

definition "in_dom R x \<equiv> \<exists>y. R x y"

lemma in_domI [intro]:
  assumes "R x y"
  shows "in_dom R x"
  using assms unfolding in_dom_def by blast

lemma in_domE [elim]:
  assumes "in_dom R x"
  obtains y where "R x y"
  using assms unfolding in_dom_def by blast

lemma in_dom_if_in_dom_rel_comp:
  assumes "in_dom (R \<circ>\<circ> S) x"
  shows "in_dom R x"
  using assms by blast

definition "in_codom R y \<equiv> \<exists>x. R x y"

lemma in_codomI [intro]:
  assumes "R x y"
  shows "in_codom R y"
  using assms unfolding in_codom_def by blast

lemma in_codomE [elim]:
  assumes "in_codom R y"
  obtains x where "R x y"
  using assms unfolding in_codom_def by blast

lemma in_codom_if_in_codom_rel_comp:
  assumes "in_codom (R \<circ>\<circ> S) y"
  shows "in_codom S y"
  using assms by blast

lemma in_codom_rel_inv_eq_in_dom [simp]: "in_codom (R\<inverse>) = in_dom R"
  by (intro ext) blast

lemma in_dom_rel_inv_eq_in_codom [simp]: "in_dom (R\<inverse>) = in_codom R"
  by (intro ext) blast

definition "in_field R x \<equiv> in_dom R x \<or> in_codom R x"

lemma in_field_if_in_dom:
  assumes "in_dom R x"
  shows "in_field R x"
  unfolding in_field_def using assms by blast

lemma in_field_if_in_codom:
  assumes "in_codom R x"
  shows "in_field R x"
  unfolding in_field_def using assms by blast

lemma in_fieldE [elim]:
  assumes "in_field R x"
  obtains (in_dom) x' where "R x x'" | (in_codom) x' where "R x' x"
  using assms unfolding in_field_def by blast

lemma in_fieldE':
  assumes "in_field R x"
  obtains (in_dom) "in_dom R x" | (in_codom) "in_codom R x"
  using assms by blast

lemma in_fieldI [intro]:
  assumes "R x y"
  shows "in_field R x" "in_field R y"
  using assms by (auto intro: in_field_if_in_dom in_field_if_in_codom)

lemma in_field_iff_in_dom_or_in_codom:
  "in_field L x \<longleftrightarrow> in_dom L x \<or> in_codom L x"
  by blast

lemma in_field_rel_inv_eq [simp]: "in_field R\<inverse> = in_field R"
  by (intro ext) auto

lemma in_field_compE [elim]:
  assumes "in_field (R \<circ>\<circ> S) x"
  obtains (in_dom) "in_dom R x" | (in_codom) "in_codom S x"
  using assms by blast

lemma in_field_eq_in_dom_if_in_codom_eq_in_dom:
  assumes "in_codom R = in_dom R"
  shows "in_field R = in_dom R"
  using assms by (intro ext) (auto elim: in_fieldE')

definition "rel_if B R x y \<equiv> B \<longrightarrow> R x y"

bundle rel_if_syntax begin notation (output) rel_if (infixl "\<longrightarrow>" 50) end
bundle no_rel_if_syntax begin no_notation (output) rel_if (infixl "\<longrightarrow>" 50) end
unbundle rel_if_syntax

lemma rel_if_eq_rel_if_pred [simp]:
  assumes "B"
  shows "(rel_if B R) = R"
  unfolding rel_if_def using assms by blast

lemma rel_if_eq_top_if_not_pred [simp]:
  assumes "\<not>B"
  shows "(rel_if B R) = (\<lambda>_ _. True)"
  unfolding rel_if_def using assms by blast

lemma rel_if_if_impI [intro]:
  assumes "B \<Longrightarrow> R x y"
  shows "(rel_if B R) x y"
  unfolding rel_if_def using assms by blast

lemma rel_ifE [elim]:
  assumes "(rel_if B R) x y"
  obtains "\<not>B" | "B" "R x y"
  using assms unfolding rel_if_def by blast

lemma rel_ifD:
  assumes "(rel_if B R) x y"
  and "B"
  shows "R x y"
  using assms by blast

consts restrict_left :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'c \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"

definition "restrict_right R P \<equiv> (restrict_left R\<inverse> P)\<inverse>"

overloading
  restrict_left_pred \<equiv> "restrict_left :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
begin
  definition "restrict_left_pred R P x y \<equiv> P x \<and> R x y"
end

bundle restrict_syntax
begin
notation restrict_left ("(_)\<restriction>(\<^bsub>_\<^esub>)" [1000])
notation restrict_right ("(_)\<upharpoonleft>(\<^bsub>_\<^esub>)" [1000])
end
bundle no_restrict_syntax
begin
no_notation restrict_left ("(_)\<restriction>(\<^bsub>_\<^esub>)" [1000])
no_notation restrict_right ("(_)\<upharpoonleft>(\<^bsub>_\<^esub>)" [1000])
end
unbundle restrict_syntax

lemma restrict_leftI [intro]:
  assumes "R x y"
  and "P x"
  shows "R\<restriction>\<^bsub>P\<^esub> x y"
  using assms unfolding restrict_left_pred_def by blast

lemma restrict_leftE [elim]:
  assumes "R\<restriction>\<^bsub>P\<^esub> x y"
  obtains "P x" "R x y"
  using assms unfolding restrict_left_pred_def by blast

lemma restrict_right_eq: "R\<upharpoonleft>\<^bsub>P\<^esub> = ((R\<inverse>)\<restriction>\<^bsub>P\<^esub>)\<inverse>"
  unfolding restrict_right_def ..

lemma rel_inv_restrict_right_rel_inv_eq_restrict_left [simp]: "((R\<inverse>)\<upharpoonleft>\<^bsub>P\<^esub>)\<inverse> = R\<restriction>\<^bsub>P\<^esub>"
  by (simp add: restrict_right_eq)

lemma restrict_right_iff_restrict_left: "R\<upharpoonleft>\<^bsub>P\<^esub> x y = (R\<inverse>)\<restriction>\<^bsub>P\<^esub> y x"
  unfolding restrict_right_eq by simp

lemma restrict_rightI [intro]:
  assumes "R x y"
  and "P y"
  shows "R\<upharpoonleft>\<^bsub>P\<^esub> x y"
  using assms by (auto iff: restrict_right_iff_restrict_left)

lemma restrict_rightE [elim]:
  assumes "R\<upharpoonleft>\<^bsub>P\<^esub> x y"
  obtains "P y" "R x y"
  using assms by (auto iff: restrict_right_iff_restrict_left)

lemma rel_inv_restrict_left_inv_restrict_left_eq:
  fixes R :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and P :: "'a \<Rightarrow> bool" and Q :: "'b \<Rightarrow> bool"
  shows "(((R\<restriction>\<^bsub>P\<^esub>)\<inverse>)\<restriction>\<^bsub>Q\<^esub>)\<inverse> = (((R\<inverse>)\<restriction>\<^bsub>Q\<^esub>)\<inverse>)\<restriction>\<^bsub>P\<^esub>"
  by (intro ext iffI restrict_leftI rel_invI) auto

lemma restrict_left_right_eq_restrict_right_left:
  fixes R :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and P :: "'a \<Rightarrow> bool" and Q :: "'b \<Rightarrow> bool"
  shows "R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>Q\<^esub> = R\<upharpoonleft>\<^bsub>Q\<^esub>\<restriction>\<^bsub>P\<^esub>"
  unfolding restrict_right_eq
  by (fact rel_inv_restrict_left_inv_restrict_left_eq)

lemma in_dom_restrict_leftI [intro]:
  assumes "R x y"
  and "P x"
  shows "in_dom R\<restriction>\<^bsub>P\<^esub> x"
  using assms by blast

lemma in_dom_restrict_left_if_in_dom:
  assumes "in_dom R x"
  and "P x"
  shows "in_dom R\<restriction>\<^bsub>P\<^esub> x"
  using assms by blast

lemma in_dom_restrict_leftE [elim]:
  assumes "in_dom R\<restriction>\<^bsub>P\<^esub> x"
  obtains y where "P x" "R x y"
  using assms by blast

lemma in_codom_restrict_leftI [intro]:
  assumes "R x y"
  and "P x"
  shows "in_codom R\<restriction>\<^bsub>P\<^esub> y"
  using assms by blast

lemma in_codom_restrict_leftE [elim]:
  assumes "in_codom R\<restriction>\<^bsub>P\<^esub> y"
  obtains x where "P x" "R x y"
  using assms by blast

definition "rel_bimap f g (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) x y \<equiv> R (f x) (g y)"

lemma rel_bimap_eq [simp]: "rel_bimap f g R x y = R (f x) (g y)"
  unfolding rel_bimap_def by simp

definition "rel_map f R \<equiv> rel_bimap f f R"

lemma rel_bimap_self_eq_rel_map [simp]: "rel_bimap f f R = rel_map f R"
  unfolding rel_map_def by simp

lemma rel_map_eq [simp]: "rel_map f R x y = R (f x) (f y)"
  by (simp only: rel_bimap_self_eq_rel_map[symmetric] rel_bimap_eq)


end