\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Functions On Orders\<close>
subsubsection \<open>Basics\<close>
theory Order_Functions_Base
  imports
    Functions_Monotone
    Restricted_Equality
begin

subparagraph \<open>Bi-Relation\<close>

definition "bi_related R x y \<equiv> R x y \<and> R y x"

(*Note: we are not using (\<equiv>\<index>) as infix here because it would produce an ambiguous
grammar whenever using a of the form "definition c \<equiv> t"*)
bundle bi_related_syntax begin
syntax
  "_bi_related" :: "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" ("(_) \<equiv>\<^bsub>(_)\<^esub> (_)" [51,51,51] 50)
notation bi_related ("'(\<equiv>(\<^bsub>_\<^esub>)')")
end
bundle no_bi_related_syntax begin
no_syntax
  "_bi_related" :: "'a \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" ("(_) \<equiv>\<^bsub>(_)\<^esub> (_)" [51,51,51] 50)
no_notation bi_related ("'(\<equiv>(\<^bsub>_\<^esub>)')")
end
unbundle bi_related_syntax
translations
  "x \<equiv>\<^bsub>R\<^esub> y" \<rightleftharpoons> "CONST bi_related R x y"

lemma bi_relatedI [intro]:
  assumes "R x y"
  and "R y x"
  shows "x \<equiv>\<^bsub>R\<^esub> y"
  unfolding bi_related_def using assms by blast

lemma bi_relatedE [elim]:
  assumes "x \<equiv>\<^bsub>R\<^esub> y"
  obtains "R x y" "R y x"
  using assms unfolding bi_related_def by blast

lemma symmetric_bi_related [iff]: "symmetric (\<equiv>\<^bsub>R\<^esub>)"
  by (intro symmetricI) blast

lemma reflexive_bi_related_if_reflexive [intro]:
  assumes "reflexive R"
  shows "reflexive (\<equiv>\<^bsub>R\<^esub>)"
  using assms by (intro reflexiveI) (blast dest: reflexiveD)

lemma transitive_bi_related_if_transitive [intro]:
  assumes "transitive R"
  shows "transitive (\<equiv>\<^bsub>R\<^esub>)"
  using assms by (intro transitiveI bi_relatedI) auto

lemma mono_bi_related [iff]: "mono bi_related"
  by (intro monoI) blast

lemma bi_related_if_le_rel_if_bi_related:
  assumes "x \<equiv>\<^bsub>R\<^esub> y"
  and "R \<le> S"
  shows "x \<equiv>\<^bsub>S\<^esub> y"
  using assms by blast

lemma eq_if_bi_related_if_antisymmetric_on:
  assumes "antisymmetric_on P R"
  and "x \<equiv>\<^bsub>R\<^esub> y"
  and "P x" "P y"
  shows "x = y"
  using assms by (blast dest: antisymmetric_onD)

lemma eq_if_bi_related_if_in_field_le_if_antisymmetric_on:
  assumes "antisymmetric_on P R"
  and "in_field R \<le> P"
  and "x \<equiv>\<^bsub>R\<^esub> y"
  shows "x = y"
  using assms by (intro eq_if_bi_related_if_antisymmetric_on) blast+

lemma bi_related_le_eq_if_antisymmetric_on_in_field:
  assumes "antisymmetric_on (in_field R) R"
  shows "(\<equiv>\<^bsub>R\<^esub>) \<le> (=)"
  using assms
  by (intro le_relI eq_if_bi_related_if_in_field_le_if_antisymmetric_on) blast+

lemma bi_related_if_all_rel_iff_if_reflexive_on:
  assumes "reflexive_on P R"
  and "\<And>z. P z \<Longrightarrow> R x z \<longleftrightarrow> R y z"
  and "P x" "P y"
  shows "x \<equiv>\<^bsub>R\<^esub> y"
  using assms by blast

lemma bi_related_if_all_rel_iff_if_reflexive_on':
  assumes "reflexive_on P R"
  and "\<And>z. P z \<Longrightarrow> R z x \<longleftrightarrow> R z y"
  and "P x" "P y"
  shows "x \<equiv>\<^bsub>R\<^esub> y"
  using assms by blast

corollary eq_if_all_rel_iff_if_antisymmetric_on_if_reflexive_on:
  assumes "reflexive_on P R" and "antisymmetric_on P R"
  and "\<And>z. P z \<Longrightarrow> R x z \<longleftrightarrow> R y z"
  and "P x" "P y"
  shows "x = y"
  using assms by (blast intro: eq_if_bi_related_if_antisymmetric_on
    bi_related_if_all_rel_iff_if_reflexive_on)

corollary eq_if_all_rel_iff_if_antisymmetric_on_if_reflexive_on':
  assumes "reflexive_on P R" and "antisymmetric_on P R"
  and "\<And>z. P z \<Longrightarrow> R z x \<longleftrightarrow> R z y"
  and "P x" "P y"
  shows "x = y"
  using assms by (blast intro: eq_if_bi_related_if_antisymmetric_on
    bi_related_if_all_rel_iff_if_reflexive_on')


subparagraph \<open>Inflationary\<close>

consts inflationary_on :: "'a \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> bool"

overloading
  inflationary_on_pred \<equiv> "inflationary_on ::
    ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
begin
  text \<open>Often also called "extensive".\<close>
  definition "inflationary_on_pred P (R :: 'a \<Rightarrow> 'a \<Rightarrow> _) f \<equiv> \<forall>x. P x \<longrightarrow> R x (f x)"
end

lemma inflationary_onI [intro]:
  assumes "\<And>x. P x \<Longrightarrow> R x (f x)"
  shows "inflationary_on P R f"
  unfolding inflationary_on_pred_def using assms by blast

lemma inflationary_onD [dest]:
  assumes "inflationary_on P R f"
  and "P x"
  shows "R x (f x)"
  using assms unfolding inflationary_on_pred_def by blast

lemma inflationary_on_eq_dep_mono_wrt_pred: "inflationary_on = dep_mono_wrt_pred"
  by blast

lemma antimono_inflationary_on_pred [iff]:
  "antimono (\<lambda>(P :: 'a \<Rightarrow> bool). inflationary_on P (R :: 'a \<Rightarrow> _))"
  by (intro antimonoI) auto

lemma inflationary_on_if_le_pred_if_inflationary_on:
  fixes P P' :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> _"
  assumes "inflationary_on P R f"
  and "P' \<le> P"
  shows "inflationary_on P' R f"
  using assms by blast

lemma mono_inflationary_on_rel [iff]:
  "mono (\<lambda>(R :: 'a \<Rightarrow> _). inflationary_on (P :: 'a \<Rightarrow> bool) R)"
  by (intro monoI) auto

lemma inflationary_on_if_le_rel_if_inflationary_on:
  assumes "inflationary_on P R f"
  and "\<And>x. P x \<Longrightarrow> R x (f x) \<Longrightarrow> R' x (f x)"
  shows "inflationary_on P R' f"
  using assms by blast

lemma le_in_dom_if_inflationary_on:
  assumes "inflationary_on P R f"
  shows "P \<le> in_dom R"
  using assms by blast

lemma inflationary_on_sup_eq [simp]:
  "(inflationary_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> _) \<Rightarrow> _) ((P :: 'a \<Rightarrow> bool) \<squnion> Q)
  = inflationary_on P \<sqinter> inflationary_on Q"
  by (intro ext iffI inflationary_onI)
    (auto intro: inflationary_on_if_le_pred_if_inflationary_on)


definition "inflationary (R :: 'a \<Rightarrow> _) f \<equiv> inflationary_on (\<top> :: 'a \<Rightarrow> bool) R f"

lemma inflationary_eq_inflationary_on:
  "inflationary (R :: 'a \<Rightarrow> _) f = inflationary_on (\<top> :: 'a \<Rightarrow> bool) R f"
  unfolding inflationary_def ..

lemma inflationaryI [intro]:
  assumes "\<And>x. R x (f x)"
  shows "inflationary R f"
  unfolding inflationary_eq_inflationary_on using assms
  by (intro inflationary_onI)

lemma inflationaryD:
  assumes "inflationary R f"
  shows "R x (f x)"
  using assms unfolding inflationary_eq_inflationary_on by auto

lemma inflationary_on_if_inflationary:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> _"
  assumes "inflationary R f"
  shows "inflationary_on P R f"
  using assms by (intro inflationary_onI) (blast dest: inflationaryD)

lemma inflationary_eq_dep_mono_wrt_pred: "inflationary = dep_mono_wrt_pred \<top>"
  by (intro ext) (fastforce dest: inflationaryD)


subparagraph \<open>Deflationary\<close>

definition "deflationary_on P R \<equiv> inflationary_on P R\<inverse>"

lemma deflationary_on_eq_inflationary_on_rel_inv:
  "deflationary_on P R = inflationary_on P R\<inverse>"
  unfolding deflationary_on_def ..

declare deflationary_on_eq_inflationary_on_rel_inv[symmetric, simp]

corollary deflationary_on_rel_inv_eq_inflationary_on [simp]:
  "deflationary_on P R\<inverse> = inflationary_on P R"
  unfolding deflationary_on_eq_inflationary_on_rel_inv by simp

lemma deflationary_onI [intro]:
  assumes "\<And>x. P x \<Longrightarrow> R (f x) x"
  shows "deflationary_on P R f"
  unfolding deflationary_on_eq_inflationary_on_rel_inv using assms
  by (intro inflationary_onI rel_invI)

lemma deflationary_onD [dest]:
  assumes "deflationary_on P R f"
  and "P x"
  shows "R (f x) x"
  using assms unfolding deflationary_on_eq_inflationary_on_rel_inv by blast

lemma deflationary_on_eq_dep_mono_wrt_pred_rel_inv:
  "deflationary_on P R = ([x \<Colon> P] \<Rrightarrow>\<^sub>m R\<inverse> x)"
  by blast

lemma antimono_deflationary_on_pred [iff]:
  "antimono (\<lambda>(P :: 'a \<Rightarrow> bool). deflationary_on P (R :: 'a \<Rightarrow> _))"
  by (intro antimonoI) auto

lemma deflationary_on_if_le_pred_if_deflationary_on:
  fixes P P' :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> _"
  assumes "deflationary_on P R f"
  and "P' \<le> P"
  shows "deflationary_on P' R f"
  using assms by blast

lemma mono_deflationary_on_rel [iff]:
  "mono (\<lambda>(R :: 'a \<Rightarrow> _). deflationary_on (P :: 'a \<Rightarrow> bool) R)"
  by (intro monoI) auto

lemma deflationary_on_if_le_rel_if_deflationary_on:
  assumes "deflationary_on P R f"
  and "\<And>x. P x \<Longrightarrow> R (f x) x \<Longrightarrow> R' (f x) x"
  shows "deflationary_on P R' f"
  using assms by auto

lemma le_in_dom_if_deflationary_on:
  assumes "deflationary_on P R f"
  shows "P \<le> in_codom R"
  using assms by blast

lemma deflationary_on_sup_eq [simp]:
  "(deflationary_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> _) \<Rightarrow> _) ((P :: 'a \<Rightarrow> bool) \<squnion> Q)
  = deflationary_on P \<sqinter> deflationary_on Q"
  unfolding deflationary_on_eq_inflationary_on_rel_inv by auto

definition "deflationary R (f :: 'a \<Rightarrow> _) \<equiv> deflationary_on (\<top> :: 'a \<Rightarrow> bool) R f"

lemma deflationary_eq_deflationary_on:
  "deflationary R (f :: 'a \<Rightarrow> _) = deflationary_on (\<top> :: 'a \<Rightarrow> bool) R f"
  unfolding deflationary_def ..

lemma deflationaryI [intro]:
  assumes "\<And>x. R (f x) x"
  shows "deflationary R f"
  unfolding deflationary_eq_deflationary_on using assms by (intro deflationary_onI)

lemma deflationaryD:
  assumes "deflationary R f"
  shows "R (f x) x"
  using assms unfolding deflationary_eq_deflationary_on by auto

lemma deflationary_on_if_deflationary:
  fixes P :: "'a \<Rightarrow> bool" and f :: "'a \<Rightarrow> _"
  assumes "deflationary R f"
  shows "deflationary_on P R f"
  using assms by (intro deflationary_onI) (blast dest: deflationaryD)

lemma deflationary_eq_dep_mono_wrt_pred_rel_inv:
  "deflationary R = dep_mono_wrt_pred \<top> R\<inverse>"
  by (intro ext) (fastforce dest: deflationaryD)


subparagraph \<open>Relational Equivalence\<close>

definition "rel_equivalence_on \<equiv> inflationary_on \<sqinter> deflationary_on"

lemma rel_equivalence_on_eq:
  "rel_equivalence_on = inflationary_on \<sqinter> deflationary_on"
  unfolding rel_equivalence_on_def ..

lemma rel_equivalence_onI [intro]:
  assumes "inflationary_on P R f"
  and "deflationary_on P R f"
  shows "rel_equivalence_on P R f"
  unfolding rel_equivalence_on_eq using assms by auto

lemma rel_equivalence_onE [elim]:
  assumes "rel_equivalence_on P R f"
  obtains "inflationary_on P R f" "deflationary_on P R f"
  using assms unfolding rel_equivalence_on_eq by auto

lemma rel_equivalence_on_eq_dep_mono_wrt_pred_inf:
  "rel_equivalence_on P R = dep_mono_wrt_pred P (R \<sqinter> R\<inverse>)"
  by (intro ext) fastforce

lemma bi_related_if_rel_equivalence_on:
  assumes "rel_equivalence_on P R f"
  and "P x"
  shows "x \<equiv>\<^bsub>R\<^esub> f x"
  using assms by (intro bi_relatedI) auto

lemma rel_equivalence_on_if_all_bi_related:
  assumes "\<And>x. P x \<Longrightarrow> x \<equiv>\<^bsub>R\<^esub> f x"
  shows "rel_equivalence_on P R f"
  using assms by auto

corollary rel_equivalence_on_iff_all_bi_related:
  "rel_equivalence_on P R f \<longleftrightarrow> (\<forall>x. P x \<longrightarrow> x \<equiv>\<^bsub>R\<^esub> f x)"
  using rel_equivalence_on_if_all_bi_related bi_related_if_rel_equivalence_on
  by blast

lemma rel_equivalence_onD [dest]:
  assumes "rel_equivalence_on P R f"
  and "P x"
  shows "R x (f x)" "R (f x) x"
  using assms by (auto dest: bi_related_if_rel_equivalence_on)

lemma rel_equivalence_on_rel_inv_eq_rel_equivalence_on [simp]:
  "rel_equivalence_on P R\<inverse> = rel_equivalence_on P R"
  by (intro ext) fastforce

lemma antimono_rel_equivalence_on_pred [iff]:
  "antimono (\<lambda>(P :: 'a \<Rightarrow> bool). rel_equivalence_on P (R :: 'a \<Rightarrow> _))"
  by (intro antimonoI) blast

lemma rel_equivalence_on_if_le_pred_if_rel_equivalence_on:
  fixes P P' :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> _"
  assumes "rel_equivalence_on P R f"
  and "P' \<le> P"
  shows "rel_equivalence_on P' R f"
  using assms by blast

lemma rel_equivalence_on_sup_eq [simp]:
  "(rel_equivalence_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> _) \<Rightarrow> _) ((P :: 'a \<Rightarrow> bool) \<squnion> Q)
  = rel_equivalence_on P \<sqinter> rel_equivalence_on Q"
  unfolding rel_equivalence_on_eq by (simp add: inf_aci)

lemma in_codom_eq_in_dom_if_rel_equivalence_on_in_field:
  assumes "rel_equivalence_on (in_field R) R f"
  shows "in_codom R = in_dom R"
  using assms by (intro ext) blast

lemma reflexive_on_if_transitive_on_if_mon_wrt_pred_if_rel_equivalence_on:
  assumes "rel_equivalence_on P R f"
  and "([P] \<Rrightarrow>\<^sub>m P) f"
  and "transitive_on P R"
  shows "reflexive_on P R"
  using assms by (blast dest: transitive_onD)

lemma inflationary_on_eq_rel_equivalence_on_if_symmetric:
  assumes "symmetric R"
  shows "inflationary_on P R = rel_equivalence_on P R"
  using assms
  by (simp add: rel_equivalence_on_eq deflationary_on_eq_inflationary_on_rel_inv)

lemma deflationary_on_eq_rel_equivalence_on_if_symmetric:
  assumes "symmetric R"
  shows "deflationary_on P R = rel_equivalence_on P R"
  using assms
  by (simp add: deflationary_on_eq_inflationary_on_rel_inv rel_equivalence_on_eq)


definition "rel_equivalence (R :: 'a \<Rightarrow> _) f \<equiv> rel_equivalence_on (\<top> :: 'a \<Rightarrow> bool) R f"

lemma rel_equivalence_eq_rel_equivalence_on:
  "rel_equivalence (R :: 'a \<Rightarrow> _) f = rel_equivalence_on (\<top> :: 'a \<Rightarrow> bool) R f"
  unfolding rel_equivalence_def ..

lemma rel_equivalenceI [intro]:
  assumes "inflationary R f"
  and "deflationary R f"
  shows "rel_equivalence R f"
  unfolding rel_equivalence_eq_rel_equivalence_on using assms
  by (intro rel_equivalence_onI)
  (auto dest: inflationary_on_if_inflationary deflationary_on_if_deflationary)

lemma rel_equivalenceE [elim]:
  assumes "rel_equivalence R f"
  obtains "inflationary R f" "deflationary R f"
  using assms unfolding rel_equivalence_eq_rel_equivalence_on
  by (elim rel_equivalence_onE)
  (simp only: inflationary_eq_inflationary_on deflationary_eq_deflationary_on)

lemma inflationary_if_rel_equivalence:
  assumes "rel_equivalence R f"
  shows "inflationary R f"
  using assms by (elim rel_equivalenceE)

lemma deflationary_if_rel_equivalence:
  assumes "rel_equivalence R f"
  shows "deflationary R f"
  using assms by (elim rel_equivalenceE)

lemma rel_equivalence_on_if_rel_equivalence:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> _"
  assumes "rel_equivalence R f"
  shows "rel_equivalence_on P R f"
  using assms by (intro rel_equivalence_onI)
  (auto dest: inflationary_on_if_inflationary deflationary_on_if_deflationary)

lemma bi_related_if_rel_equivalence:
  assumes "rel_equivalence R f"
  shows "x \<equiv>\<^bsub>R\<^esub> f x"
  using assms by (intro bi_relatedI) (auto dest: inflationaryD deflationaryD)

lemma rel_equivalence_if_all_bi_related:
  assumes "\<And>x. x \<equiv>\<^bsub>R\<^esub> f x"
  shows "rel_equivalence R f"
  using assms by auto

lemma rel_equivalenceD:
  assumes "rel_equivalence R f"
  shows "R x (f x)" "R (f x) x"
  using assms by (auto dest: bi_related_if_rel_equivalence)

lemma reflexive_on_in_field_if_transitive_if_rel_equivalence_on:
  assumes "rel_equivalence_on (in_field R) R f"
  and "transitive R"
  shows "reflexive_on (in_field R) R"
  using assms by (intro reflexive_onI) blast

corollary preorder_on_in_field_if_transitive_if_rel_equivalence_on:
  assumes "rel_equivalence_on (in_field R) R f"
  and "transitive R"
  shows "preorder_on (in_field R) R"
  using assms reflexive_on_in_field_if_transitive_if_rel_equivalence_on
  using assms by blast


end
