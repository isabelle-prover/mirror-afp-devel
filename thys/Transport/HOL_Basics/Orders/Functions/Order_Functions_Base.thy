\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Functions On Orders\<close>
subsubsection \<open>Basics\<close>
theory Order_Functions_Base
  imports
    Functions_Monotone
    Binary_Relations_Antisymmetric
    Binary_Relations_Symmetric
    Preorders
begin

subparagraph \<open>Bi-Relation\<close>

consts bi_related :: "'a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool"

overloading
  bi_related \<equiv> "bi_related :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
begin
  definition "bi_related (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool) x y \<equiv> R x y \<and> R y x"
end

(*Note: we are not using (\<equiv>\<index>) as infix here because it would produce an ambiguous
grammar whenever using an expression of the form "definition c \<equiv> t"*)
open_bundle bi_related_syntax
begin
syntax
  "_bi_related" :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool" (\<open>(_) \<equiv>\<^bsub>(_)\<^esub> (_)\<close> [51,51,51] 50)
notation bi_related (\<open>'(\<equiv>(\<^bsub>_\<^esub>)')\<close>)
end

syntax_consts
  "_bi_related" \<rightleftharpoons> bi_related
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

context
  fixes P :: "'a \<Rightarrow> bool" and R S :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and x y :: 'a
begin

lemma symmetric_bi_related [iff]: "symmetric ((\<equiv>\<^bsub>R\<^esub>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool)"
  by (intro symmetricI) blast

lemma reflexive_bi_related_if_reflexive [intro]:
  assumes "reflexive R"
  shows "reflexive ((\<equiv>\<^bsub>R\<^esub>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool)"
  using assms by (intro reflexiveI) (blast dest: reflexiveD)

lemma transitive_bi_related_if_transitive [intro]:
  assumes "transitive R"
  shows "transitive ((\<equiv>\<^bsub>R\<^esub>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool)"
  using assms by (intro transitiveI bi_relatedI) auto

lemma mono_bi_related: "mono (bi_related :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool)"
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

end

lemma bi_related_le_eq_if_antisymmetric_on_in_field:
  assumes "antisymmetric_on (in_field R) (R :: 'a \<Rightarrow> 'a \<Rightarrow> bool)"
  shows "((\<equiv>\<^bsub>R\<^esub>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool) \<le> (=)"
  using assms
  by (intro le_relI eq_if_bi_related_if_in_field_le_if_antisymmetric_on) blast+


subparagraph \<open>Inflationary\<close>

consts inflationary_on :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool"

overloading
  inflationary_on_pred \<equiv> "inflationary_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
begin
  text \<open>Often also called "extensive".\<close>
  definition "inflationary_on_pred P (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) (f :: 'a \<Rightarrow> 'b) \<equiv> \<forall>x : P. R x (f x)"
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

lemma inflationary_on_if_le_rel_if_inflationary_on:
  assumes "inflationary_on P R f"
  and "\<And>x. P x \<Longrightarrow> R x (f x) \<Longrightarrow> R' x (f x)"
  shows "inflationary_on P R' f"
  using assms by blast

lemma mono_inflationary_on_rel:
  "((\<ge>) \<Rightarrow> (\<le>) \<Rrightarrow> (\<le>)) (inflationary_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool)"
  by (intro mono_wrt_relI Fun_Rel_relI) auto

context
  fixes P P' :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and f :: "'a \<Rightarrow> 'b"
begin

(*FIXME: should be automatically derivable from above monotonicity lemma*)
lemma inflationary_on_if_le_pred_if_inflationary_on:
  assumes "inflationary_on P R f"
  and "P' \<le> P"
  shows "inflationary_on P' R f"
  using assms by blast

lemma le_in_dom_if_inflationary_on:
  assumes "inflationary_on P R f"
  shows "P \<le> in_dom R"
  using assms by blast
end

lemma inflationary_on_sup_eq [simp]:
  "(inflationary_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool) (P \<squnion> Q)
  = inflationary_on P \<sqinter> inflationary_on Q"
  by (intro ext iffI inflationary_onI)
    (auto intro: inflationary_on_if_le_pred_if_inflationary_on)

consts inflationary :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

overloading
  inflationary \<equiv> "inflationary :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
begin
  definition "(inflationary :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool) \<equiv>
    inflationary_on (\<top> :: 'a \<Rightarrow> bool)"
end

lemma inflationary_eq_inflationary_on:
  "(inflationary :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool) = inflationary_on (\<top> :: 'a \<Rightarrow> bool)"
  unfolding inflationary_def ..

lemma inflationary_eq_inflationary_on_uhint [uhint]:
  assumes "P \<equiv> \<top> :: 'a \<Rightarrow> bool"
  shows "inflationary :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool \<equiv> inflationary_on P"
  using assms by (simp add: inflationary_eq_inflationary_on)

lemma inflationaryI [intro]:
  assumes "\<And>x. R x (f x)"
  shows "inflationary R f"
  using assms by (urule inflationary_onI)

lemma inflationaryD:
  assumes "inflationary R f"
  shows "R x (f x)"
  using assms by (urule (d) inflationary_onD chained: insert) simp

lemma inflationary_on_if_inflationary:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and f :: "'a \<Rightarrow> 'b"
  assumes "inflationary R f"
  shows "inflationary_on P R f"
  using assms by (intro inflationary_onI) (blast dest: inflationaryD)

lemma inflationary_eq_dep_mono_wrt_pred: "inflationary = dep_mono_wrt_pred \<top>"
  by (intro ext) (fastforce dest: inflationaryD)


subparagraph \<open>Deflationary\<close>

consts deflationary_on :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool"

overloading
  deflationary_on_pred \<equiv> "deflationary_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
begin
  definition "deflationary_on_pred (P :: 'a \<Rightarrow> bool) (R :: 'b \<Rightarrow> 'a \<Rightarrow> bool) :: ('a \<Rightarrow> 'b) \<Rightarrow> bool \<equiv>
    inflationary_on P R\<inverse>"
end

context
  fixes P :: "'a \<Rightarrow> bool" and R :: "'b \<Rightarrow> 'a \<Rightarrow> bool" and f :: "'a \<Rightarrow> 'b"
begin

lemma deflationary_on_eq_inflationary_on_rel_inv:
  "(deflationary_on P R :: ('a \<Rightarrow> 'b) \<Rightarrow> bool) = inflationary_on P R\<inverse>"
  unfolding deflationary_on_pred_def ..

declare deflationary_on_eq_inflationary_on_rel_inv[symmetric, simp]

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

end

context
  fixes P P' :: "'a \<Rightarrow> bool" and R :: "'b \<Rightarrow> 'a \<Rightarrow> bool" and f :: "'a \<Rightarrow> 'b"
begin

corollary deflationary_on_rel_inv_eq_inflationary_on [simp]:
  "(deflationary_on P (S :: 'a \<Rightarrow> 'b \<Rightarrow> bool)\<inverse> :: ('a \<Rightarrow> 'b) \<Rightarrow> bool) = inflationary_on P S"
  unfolding deflationary_on_eq_inflationary_on_rel_inv by simp

lemma deflationary_on_eq_dep_mono_wrt_pred_rel_inv:
  "(deflationary_on P R :: ('a \<Rightarrow> 'b) \<Rightarrow> bool) = ((x : P) \<Rightarrow> R\<inverse> x)"
  by blast

lemma deflationary_on_if_le_rel_if_deflationary_on:
  assumes "deflationary_on P R f"
  and "\<And>x. P x \<Longrightarrow> R (f x) x \<Longrightarrow> R' (f x) x"
  shows "deflationary_on P R' f"
  using assms by auto

lemma mono_deflationary_on:
  "((\<ge>) \<Rightarrow> (\<le>) \<Rrightarrow> (\<le>)) (deflationary_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool)"
  by blast

(*FIXME: should be automatically derivable from above monotonicity lemma*)
lemma deflationary_on_if_le_pred_if_deflationary_on:
  assumes "deflationary_on P R f"
  and "P' \<le> P"
  shows "deflationary_on P' R f"
  using assms by blast

lemma le_in_dom_if_deflationary_on:
  assumes "deflationary_on P R f"
  shows "P \<le> in_codom R"
  using assms by blast

lemma deflationary_on_sup_eq [simp]:
  "(deflationary_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool) (P \<squnion> Q)
  = deflationary_on P \<sqinter> deflationary_on Q"
  unfolding deflationary_on_eq_inflationary_on_rel_inv by auto

end

consts deflationary :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

overloading
  deflationary \<equiv> "deflationary :: ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
begin
  definition "(deflationary :: ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool) \<equiv>
    deflationary_on (\<top> :: 'a \<Rightarrow> bool)"
end

lemma deflationary_eq_deflationary_on:
  "(deflationary :: ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool) = deflationary_on (\<top> :: 'a \<Rightarrow> bool)"
  unfolding deflationary_def ..

lemma deflationary_eq_deflationary_on_uhint [uhint]:
  assumes "P \<equiv> \<top> :: 'a \<Rightarrow> bool"
  shows "deflationary :: ('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool \<equiv> deflationary_on P"
  using assms by (simp add: deflationary_eq_deflationary_on)

lemma deflationaryI [intro]:
  assumes "\<And>x. R (f x) x"
  shows "deflationary R f"
  using assms by (urule deflationary_onI)

lemma deflationaryD:
  assumes "deflationary R f"
  shows "R (f x) x"
  using assms by (urule (d) deflationary_onD chained: insert) simp

lemma deflationary_on_if_deflationary:
  fixes P :: "'a \<Rightarrow> bool" and R :: "'b \<Rightarrow> 'a \<Rightarrow> bool" and f :: "'a \<Rightarrow> 'b"
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

context
  fixes P P' :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and f :: "'a \<Rightarrow> 'a"
begin

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
  shows "x \<equiv>\<^bsub>R\<^esub> f x"
  using assms by (auto dest: bi_related_if_rel_equivalence_on)

lemma rel_equivalence_on_rel_inv_eq_rel_equivalence_on [simp]:
  "(rel_equivalence_on P R\<inverse> :: ('a \<Rightarrow> 'a) \<Rightarrow> bool) = rel_equivalence_on P R"
  by (intro ext) fastforce

lemma mono_rel_equivalence_on:
  "((\<ge>) \<Rightarrow> (\<le>) \<Rrightarrow> (\<le>)) (rel_equivalence_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool)"
  by blast

(*FIXME: should be automatically derivable from above monotonicity lemma*)
lemma rel_equivalence_on_if_le_pred_if_rel_equivalence_on:
  assumes "rel_equivalence_on P R f"
  and "P' \<le> P"
  shows "rel_equivalence_on P' R f"
  using assms by blast

lemma rel_equivalence_on_sup_eq [simp]:
  "(rel_equivalence_on :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool) (P \<squnion> Q)
  = rel_equivalence_on P \<sqinter> rel_equivalence_on Q"
  unfolding rel_equivalence_on_eq by (simp add: inf_aci)

lemma in_codom_eq_in_dom_if_rel_equivalence_on_in_field:
  assumes "rel_equivalence_on (in_field R) R f"
  shows "in_codom R = in_dom R"
  using assms by (intro ext) blast

lemma reflexive_on_if_transitive_on_if_mon_wrt_pred_if_rel_equivalence_on:
  assumes "rel_equivalence_on P R f"
  and "(P \<Rightarrow> P) f"
  and "transitive_on P R"
  shows "reflexive_on P R"
  using assms by (blast dest: transitive_onD)

lemma inflationary_on_eq_rel_equivalence_on_if_symmetric:
  assumes "symmetric R"
  shows "(inflationary_on P R :: ('a \<Rightarrow> 'a) \<Rightarrow> bool) = rel_equivalence_on P R"
  using assms
  by (simp add: rel_equivalence_on_eq deflationary_on_eq_inflationary_on_rel_inv)

lemma deflationary_on_eq_rel_equivalence_on_if_symmetric:
  assumes "symmetric R"
  shows "(deflationary_on P R :: ('a \<Rightarrow> 'a) \<Rightarrow> bool) = rel_equivalence_on P R"
  using assms
  by (simp add: deflationary_on_eq_inflationary_on_rel_inv rel_equivalence_on_eq)

end

consts rel_equivalence :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

overloading
  rel_equivalence \<equiv> "rel_equivalence :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
begin
  definition "(rel_equivalence :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool) \<equiv>
    rel_equivalence_on (\<top> :: 'a \<Rightarrow> bool)"
end

lemma rel_equivalence_eq_rel_equivalence_on:
  "(rel_equivalence :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool) = rel_equivalence_on (\<top> :: 'a \<Rightarrow> bool)"
  unfolding rel_equivalence_def ..

lemma rel_equivalence_eq_rel_equivalence_on_uhint [uhint]:
  assumes "P \<equiv> \<top> :: 'a \<Rightarrow> bool"
  shows "rel_equivalence :: ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool \<equiv> rel_equivalence_on P"
  using assms by (simp add: rel_equivalence_eq_rel_equivalence_on)

context
  fixes P :: "'a \<Rightarrow> bool" and R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and f :: "'a \<Rightarrow> 'a"
begin

lemma rel_equivalenceI [intro]:
  assumes "inflationary R f"
  and "deflationary R f"
  shows "rel_equivalence R f"
  using assms by (urule rel_equivalence_onI)

lemma rel_equivalenceE [elim]:
  assumes "rel_equivalence R f"
  obtains "inflationary R f" "deflationary R f"
  using assms by (urule (e) rel_equivalence_onE)

lemma inflationary_if_rel_equivalence:
  assumes "rel_equivalence R f"
  shows "inflationary R f"
  using assms by (rule rel_equivalenceE)

lemma deflationary_if_rel_equivalence:
  assumes "rel_equivalence R f"
  shows "deflationary R f"
  using assms by (rule rel_equivalenceE)

lemma rel_equivalence_on_if_rel_equivalence:
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
  by blast

end

end
