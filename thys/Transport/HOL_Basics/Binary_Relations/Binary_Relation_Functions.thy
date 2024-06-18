\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Binary Relations\<close>
subsection \<open>Basic Functions\<close>
theory Binary_Relation_Functions
  imports
    Bounded_Quantifiers
    ML_Unification.Unify_Resolve_Tactics
begin

paragraph \<open>Summary\<close>
text \<open>Basic functions on binary relations.\<close>

subsubsection \<open>Domain, Codomain, and Field\<close>

definition "in_dom R x \<equiv> \<exists>y. R x y"

lemma in_domI [intro]:
  assumes "R x y"
  shows "in_dom R x"
  using assms unfolding in_dom_def by blast

lemma in_domE [elim]:
  assumes "in_dom R x"
  obtains y where "R x y"
  using assms unfolding in_dom_def by blast

lemma in_dom_bottom_eq_bottom [simp]: "in_dom \<bottom> = \<bottom>" by fastforce
lemma in_dom_top_eq_top [simp]: "in_dom \<top> = \<top>" by fastforce

lemma in_dom_sup_eq_in_dom_sup_in_dom [simp]: "in_dom (R \<squnion> S) = in_dom R \<squnion> in_dom S" by fastforce

consts in_codom_on :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool"

definition "in_codom_on_pred (P :: 'a \<Rightarrow> bool) R y \<equiv> \<exists>x : P. R x y"
adhoc_overloading in_codom_on in_codom_on_pred

lemma in_codom_onI [intro]:
  assumes "R x y"
  and "P x"
  shows "in_codom_on P R y"
  using assms unfolding in_codom_on_pred_def by blast

lemma in_codom_onE [elim]:
  assumes "in_codom_on P R y"
  obtains x where "P x" "R x y"
  using assms unfolding in_codom_on_pred_def by blast

lemma in_codom_on_pred_iff_bex_rel: "in_codom_on P R y \<longleftrightarrow> (\<exists>x : P. R x y)" by blast

lemma in_codom_bottom_pred_eq_bottom [simp]: "in_codom_on \<bottom> = \<bottom>" by fastforce
lemma in_codom_bottom_rel_eq_bottom [simp]: "in_codom_on P \<bottom> = \<bottom>" by fastforce
lemma in_codom_top_top_eq [simp]: "in_codom_on \<top> \<top> = \<top>" by fastforce

lemma in_codom_on_eq_pred_eq [simp]: "in_codom_on ((=) P) R = R P"
  by auto

lemma in_codom_on_sup_pred_eq_in_codom_on_sup_in_codom_on [simp]:
  "in_codom_on (P \<squnion> Q) = in_codom_on P \<squnion> in_codom_on Q"
  by fastforce

lemma in_codom_on_sup_rel_eq_in_codom_on_sup_in_codom_on [simp]:
  "in_codom_on P (R \<squnion> S) = in_codom_on P R \<squnion> in_codom_on P S"
  by fastforce

definition "in_codom \<equiv> in_codom_on (\<top> :: 'a \<Rightarrow> bool)"

lemma in_codom_eq_in_codom_on_top: "in_codom = in_codom_on \<top>" unfolding in_codom_def by auto

lemma in_codom_eq_in_codom_on_top_uhint [uhint]:
  assumes "P \<equiv> (\<top> :: 'a \<Rightarrow> bool)"
  shows "in_codom \<equiv> in_codom_on P"
  using assms by (simp add: in_codom_eq_in_codom_on_top)

lemma in_codomI [intro]:
  assumes "R x y"
  shows "in_codom R y"
  using assms by (urule in_codom_onI) simp

lemma in_codomE [elim]:
  assumes "in_codom R y"
  obtains x where "R x y"
  using assms by (urule (e) in_codom_onE)

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
  "in_field R x \<longleftrightarrow> in_dom R x \<or> in_codom R x"
  by blast

lemma in_field_eq_in_dom_if_in_codom_eq_in_dom:
  assumes "in_codom R = in_dom R"
  shows "in_field R = in_dom R"
  using assms by (intro ext) (auto elim: in_fieldE')

lemma in_field_bottom_eq_bottom [simp]: "in_field \<bottom> = \<bottom>" by fastforce
lemma in_field_top_eq_top [simp]: "in_field \<top> = \<top>" by fastforce

lemma in_field_sup_eq_in_field_sup_in_field [simp]: "in_field (R \<squnion> S) = in_field R \<squnion> in_field S"
  by fastforce

subsubsection \<open>Composition\<close>

consts rel_comp :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"

bundle rel_comp_syntax begin notation rel_comp (infixl "\<circ>\<circ>" 55) end
bundle no_rel_comp_syntax begin no_notation rel_comp (infixl "\<circ>\<circ>" 55) end
unbundle rel_comp_syntax

definition "rel_comp_rel R S x y \<equiv> \<exists>z. R x z \<and> S z y"
adhoc_overloading rel_comp rel_comp_rel

lemma rel_compI [intro]:
  assumes "R x y"
  and "S y z"
  shows "(R \<circ>\<circ> S) x z"
  using assms unfolding rel_comp_rel_def by blast

lemma rel_compE [elim]:
  assumes "(R \<circ>\<circ> S) x y"
  obtains z where "R x z" "S z y"
  using assms unfolding rel_comp_rel_def by blast

lemma rel_comp_assoc: "R \<circ>\<circ> (S \<circ>\<circ> T) = (R \<circ>\<circ> S) \<circ>\<circ> T"
  by (intro ext) blast

lemma in_dom_if_in_dom_rel_comp:
  assumes "in_dom (R \<circ>\<circ> S) x"
  shows "in_dom R x"
  using assms by blast

lemma in_codom_if_in_codom_rel_comp:
  assumes "in_codom (R \<circ>\<circ> S) y"
  shows "in_codom S y"
  using assms by blast

lemma in_field_compE [elim]:
  assumes "in_field (R \<circ>\<circ> S) x"
  obtains (in_dom) "in_dom R x" | (in_codom) "in_codom S x"
  using assms by blast


subsubsection \<open>Inverse\<close>

consts rel_inv :: "'a \<Rightarrow> 'b"

bundle rel_inv_syntax begin notation rel_inv ("(_\<inverse>)" [1000]) end
bundle no_rel_inv_syntax begin no_notation rel_inv ("(_\<inverse>)" [1000]) end
unbundle rel_inv_syntax

definition rel_inv_rel :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool"
  where "rel_inv_rel R x y \<equiv> R y x"
adhoc_overloading rel_inv rel_inv_rel

lemma rel_invI [intro]:
  assumes "R x y"
  shows "R\<inverse> y x"
  using assms unfolding rel_inv_rel_def .

lemma rel_invD [dest]:
  assumes "R\<inverse> x y"
  shows "R y x"
  using assms unfolding rel_inv_rel_def .

lemma rel_inv_iff_rel [simp]: "R\<inverse> x y \<longleftrightarrow> R y x"
  by blast

lemma in_dom_rel_inv_eq_in_codom [simp]: "in_dom R\<inverse> = in_codom R"
  by (intro ext) blast

lemma in_codom_rel_inv_eq_in_dom [simp]: "in_codom R\<inverse> = in_dom R"
  by (intro ext) blast

lemma in_field_rel_inv_eq_in_field [simp]: "in_field R\<inverse> = in_field R"
  by (intro ext) auto

lemma rel_inv_comp_eq [simp]: "(R \<circ>\<circ> S)\<inverse> = S\<inverse> \<circ>\<circ> R\<inverse>"
  by (intro ext) blast

lemma rel_inv_inv_eq_self [simp]: "R\<inverse>\<inverse> = R"
  by blast

lemma rel_inv_eq_iff_eq [iff]: "R\<inverse> = S\<inverse> \<longleftrightarrow> R = S"
  by (blast dest: fun_cong)

lemma rel_inv_le_rel_inv_iff [iff]: "R\<inverse> \<le> S\<inverse> \<longleftrightarrow> R \<le> S"
  by (auto intro: predicate2I dest: predicate2D)

lemma rel_inv_top_eq [simp]: "\<top>\<inverse> = \<top>" by fastforce
lemma rel_inv_bottom_eq [simp]: "\<bottom>\<inverse> = \<bottom>" by fastforce

subsubsection \<open>Restrictions\<close>

consts rel_if :: "bool \<Rightarrow> 'a \<Rightarrow> 'a"

bundle rel_if_syntax begin notation (output) rel_if (infixl "\<longrightarrow>" 50) end
bundle no_rel_if_syntax begin no_notation (output) rel_if (infixl "\<longrightarrow>" 50) end
unbundle rel_if_syntax

definition "rel_if_rel B R x y \<equiv> B \<longrightarrow> R x y"
adhoc_overloading rel_if rel_if_rel

lemma rel_if_eq_rel_if_pred [simp]:
  assumes "B"
  shows "(rel_if B R) = R"
  unfolding rel_if_rel_def using assms by blast

lemma rel_if_eq_top_if_not_pred [simp]:
  assumes "\<not>B"
  shows "(rel_if B R) = (\<lambda>_ _. True)"
  unfolding rel_if_rel_def using assms by blast

lemma rel_if_if_impI [intro]:
  assumes "B \<Longrightarrow> R x y"
  shows "(rel_if B R) x y"
  unfolding rel_if_rel_def using assms by blast

lemma rel_ifE [elim]:
  assumes "(rel_if B R) x y"
  obtains "\<not>B" | "B" "R x y"
  using assms unfolding rel_if_rel_def by blast

lemma rel_ifD:
  assumes "(rel_if B R) x y"
  and "B"
  shows "R x y"
  using assms by blast

consts rel_restrict_left :: "'a \<Rightarrow> 'b \<Rightarrow> 'a"
consts rel_restrict_right :: "'a \<Rightarrow> 'b \<Rightarrow> 'a"

bundle rel_restrict_syntax
begin
notation rel_restrict_left ("(_)\<restriction>(\<^bsub>_\<^esub>)" [1000])
notation rel_restrict_right ("(_)\<upharpoonleft>(\<^bsub>_\<^esub>)" [1000])
end
bundle no_rel_restrict_syntax
begin
no_notation rel_restrict_left ("(_)\<restriction>(\<^bsub>_\<^esub>)" [1000])
no_notation rel_restrict_right ("(_)\<upharpoonleft>(\<^bsub>_\<^esub>)" [1000])
end
unbundle rel_restrict_syntax

definition "rel_restrict_left_pred R P x y \<equiv> P x \<and> R x y"
adhoc_overloading rel_restrict_left rel_restrict_left_pred
definition "rel_restrict_right_pred R P x y \<equiv> P y \<and> R x y"
adhoc_overloading rel_restrict_right rel_restrict_right_pred

lemma rel_restrict_leftI [intro]:
  assumes "R x y"
  and "P x"
  shows "R\<restriction>\<^bsub>P\<^esub> x y"
  using assms unfolding rel_restrict_left_pred_def by blast

lemma rel_restrict_leftE [elim]:
  assumes "R\<restriction>\<^bsub>P\<^esub> x y"
  obtains "P x" "R x y"
  using assms unfolding rel_restrict_left_pred_def by blast

lemma rel_restrict_left_cong:
  assumes "\<And>x. P x \<longleftrightarrow> P' x"
  and "\<And>x y. P' x \<Longrightarrow> R x y \<longleftrightarrow> R' x y"
  shows "R\<restriction>\<^bsub>P\<^esub> = R'\<restriction>\<^bsub>P'\<^esub>"
  using assms by (intro ext iffI) blast+

lemma rel_restrict_left_restrict_left_eq_restrict_left [simp]: "R\<restriction>\<^bsub>P\<^esub>\<restriction>\<^bsub>P\<^esub> = R\<restriction>\<^bsub>P\<^esub>"
  by blast

lemma rel_restrict_left_top_eq [simp]: "(R :: 'a \<Rightarrow> 'b \<Rightarrow> bool)\<restriction>\<^bsub>\<top> :: 'a \<Rightarrow> bool\<^esub> = R"
  by (intro ext rel_restrict_leftI) auto

lemma rel_restrict_left_top_eq_uhint [uhint]:
  assumes "P \<equiv> (\<top> :: 'a \<Rightarrow> bool)"
  shows "(R :: 'a \<Rightarrow> 'b \<Rightarrow> bool)\<restriction>\<^bsub>P\<^esub> \<equiv> R"
  using assms by simp

lemma rel_restrict_left_bottom_eq [simp]: "(R :: 'a \<Rightarrow> 'b \<Rightarrow> bool)\<restriction>\<^bsub>\<bottom> :: 'a \<Rightarrow> bool\<^esub> = \<bottom>"
  by (intro ext rel_restrict_leftI) auto

lemma bottom_restrict_left_eq [simp]: "\<bottom>\<restriction>\<^bsub>P :: 'a \<Rightarrow> bool\<^esub> = \<bottom>"
  by fastforce

lemma rel_restrict_left_le_self: "(R :: 'a \<Rightarrow> 'b \<Rightarrow> bool)\<restriction>\<^bsub>(P :: 'a \<Rightarrow> bool)\<^esub> \<le> R"
  by (auto intro: predicate2I dest: predicate2D)

lemma le_rel_restrict_left_self_if_in_dom_le:
  assumes "in_dom R \<le> P"
  shows "R \<le> (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool)\<restriction>\<^bsub>(P :: 'a \<Rightarrow> bool)\<^esub>"
  using assms by (auto intro: predicate2I dest: predicate2D predicate1D)

corollary rel_restrict_left_eq_self_if_in_dom_le [simp]:
  assumes "in_dom R \<le> P"
  shows "R\<restriction>\<^bsub>P\<^esub> = R"
  using assms rel_restrict_left_le_self le_rel_restrict_left_self_if_in_dom_le by (intro antisym)

lemma ex_rel_restrict_left_iff_in_codom_on [iff]: "(\<exists>x. R\<restriction>\<^bsub>P\<^esub> x y) \<longleftrightarrow> (in_codom_on P R y)" by blast

lemma in_dom_rel_restrict_leftI [intro]:
  assumes "R x y"
  and "P x"
  shows "in_dom R\<restriction>\<^bsub>P\<^esub> x"
  using assms by blast

lemma in_codom_rel_restrict_leftI [intro]:
  assumes "R x y"
  and "P x"
  shows "in_codom R\<restriction>\<^bsub>P\<^esub> y"
  using assms by blast


lemma rel_restrict_rightI [intro]:
  assumes "R x y"
  and "P y"
  shows "R\<upharpoonleft>\<^bsub>P\<^esub> x y"
  using assms unfolding rel_restrict_right_pred_def by blast

lemma rel_restrict_rightE [elim]:
  assumes "R\<upharpoonleft>\<^bsub>P\<^esub> x y"
  obtains "P y" "R x y"
  using assms unfolding rel_restrict_right_pred_def by blast

lemma rel_restrict_right_cong:
  assumes "\<And>y. P y \<longleftrightarrow> P' y"
  and "\<And>x y. P' y \<Longrightarrow> R x y \<longleftrightarrow> R' x y"
  shows "R\<upharpoonleft>\<^bsub>P\<^esub> = R'\<upharpoonleft>\<^bsub>P'\<^esub>"
  using assms by (intro ext iffI) blast+

lemma rel_restrict_right_restrict_right_eq_restrict_right [simp]: "R\<upharpoonleft>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>P\<^esub> = R\<upharpoonleft>\<^bsub>P\<^esub>"
  by blast

lemma rel_restrict_right_top_eq [simp]: "(R :: 'a \<Rightarrow> 'b \<Rightarrow> bool)\<upharpoonleft>\<^bsub>\<top> ::'b \<Rightarrow> bool\<^esub> = R"
  by (intro ext rel_restrict_rightI) auto

lemma rel_restrict_right_top_eq_uhint [uhint]:
  assumes "P \<equiv> (\<top> ::'b \<Rightarrow> bool)"
  shows "(R :: 'a \<Rightarrow> 'b \<Rightarrow> bool)\<upharpoonleft>\<^bsub>P\<^esub> \<equiv> R"
  using assms by simp

lemma rel_restrict_right_bottom_eq [simp]: "(R :: 'a \<Rightarrow> 'b \<Rightarrow> bool)\<upharpoonleft>\<^bsub>\<bottom> :: 'b \<Rightarrow> bool\<^esub> = \<bottom>"
  by (intro ext rel_restrict_rightI) auto

lemma bottom_restrict_right_eq [simp]: "\<bottom>\<upharpoonleft>\<^bsub>P :: 'b \<Rightarrow> bool\<^esub> = \<bottom>"
  by fastforce

lemma rel_restrict_right_le_self: "(R :: 'a \<Rightarrow> 'b \<Rightarrow> bool)\<upharpoonleft>\<^bsub>(P :: 'b \<Rightarrow> bool)\<^esub> \<le> R"
  by (auto intro: predicate2I dest: predicate2D)

lemma le_rel_restrict_right_self_if_in_codom_le:
  assumes "in_codom R \<le> P"
  shows "R \<le> (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool)\<upharpoonleft>\<^bsub>(P :: 'b \<Rightarrow> bool)\<^esub>"
  using assms by (auto intro: predicate2I dest: predicate2D predicate1D)

corollary rel_restrict_right_eq_self_if_in_codom_le [simp]:
  assumes "in_codom R \<le> P"
  shows "R\<upharpoonleft>\<^bsub>P\<^esub> = R"
  using assms rel_restrict_right_le_self le_rel_restrict_right_self_if_in_codom_le
  by (intro antisym)

context
  fixes R :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
begin

lemma rel_restrict_right_eq: "R\<upharpoonleft>\<^bsub>P :: 'b \<Rightarrow> bool\<^esub> = ((R\<inverse>)\<restriction>\<^bsub>P\<^esub>)\<inverse>"
  by blast

lemma rel_inv_restrict_right_rel_inv_eq_restrict_left [simp]: "((R\<inverse>)\<upharpoonleft>\<^bsub>P :: 'a \<Rightarrow> bool\<^esub>)\<inverse> = R\<restriction>\<^bsub>P\<^esub>"
  by blast

lemma rel_restrict_right_iff_restrict_left: "R\<upharpoonleft>\<^bsub>P :: 'b \<Rightarrow> bool\<^esub> x y \<longleftrightarrow> (R\<inverse>)\<restriction>\<^bsub>P\<^esub> y x"
  unfolding rel_restrict_right_eq by simp

end

lemma rel_inv_rel_restrict_left_inv_rel_restrict_left_eq:
  fixes R :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and P :: "'a \<Rightarrow> bool" and Q :: "'b \<Rightarrow> bool"
  shows "(((R\<restriction>\<^bsub>P\<^esub>)\<inverse>)\<restriction>\<^bsub>Q\<^esub>)\<inverse> = (((R\<inverse>)\<restriction>\<^bsub>Q\<^esub>)\<inverse>)\<restriction>\<^bsub>P\<^esub>"
  by (intro ext iffI rel_restrict_leftI rel_invI) auto

lemma rel_restrict_left_right_eq_restrict_right_left:
  fixes R :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and P :: "'a \<Rightarrow> bool" and Q :: "'b \<Rightarrow> bool"
  shows "R\<restriction>\<^bsub>P\<^esub>\<upharpoonleft>\<^bsub>Q\<^esub> = R\<upharpoonleft>\<^bsub>Q\<^esub>\<restriction>\<^bsub>P\<^esub>"
  unfolding rel_restrict_right_eq
  by (fact rel_inv_rel_restrict_left_inv_rel_restrict_left_eq)


subsubsection \<open>Mappers\<close>

definition "rel_bimap f g (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) x y \<equiv> R (f x) (g y)"

lemma rel_bimap_eq [simp]: "rel_bimap f g R x y = R (f x) (g y)"
  unfolding rel_bimap_def by simp

definition "rel_map f R \<equiv> rel_bimap f f R"

lemma rel_bimap_self_eq_rel_map [simp]: "rel_bimap f f R = rel_map f R"
  unfolding rel_map_def by simp

lemma rel_map_eq [simp]: "rel_map f R x y = R (f x) (f y)"
  by (simp only: rel_bimap_self_eq_rel_map[symmetric] rel_bimap_eq)


end