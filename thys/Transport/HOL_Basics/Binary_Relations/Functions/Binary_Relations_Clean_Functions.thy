\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Clean Functions\<close>
theory Binary_Relations_Clean_Functions
  imports
    Binary_Relations_Function_Base
begin

text \<open>Clean relational functions may not contain further elements outside their specification.\<close>

(*TODO: could be generalised to HOL functions (undefined outside domain)*)
consts crel_dep_mono_wrt :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"
consts crel_mono_wrt :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"

bundle crel_mono_wrt_syntax
begin
syntax
  "_crel_mono_wrt" :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool" ("(_) \<rightarrow>\<^sub>c (_)" [51, 50] 50)
  "_crel_dep_mono_wrt" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool" ("'(_/ :/ _') \<rightarrow>\<^sub>c (_)" [51, 50, 50] 50)
end
bundle no_crel_mono_wrt_syntax
begin
no_syntax
  "_crel_mono_wrt" :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool" ("(_) \<rightarrow>\<^sub>c (_)" [51, 50] 50)
  "_crel_dep_mono_wrt" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool" ("'(_/ :/ _') \<rightarrow>\<^sub>c (_)" [51, 50, 50] 50)
end
unbundle crel_mono_wrt_syntax
translations
  "A \<rightarrow>\<^sub>c B" \<rightleftharpoons> "CONST crel_mono_wrt A B"
  "(x : A) \<rightarrow>\<^sub>c B" \<rightleftharpoons> "CONST crel_dep_mono_wrt A (\<lambda>x. B)"

definition "crel_dep_mono_wrt_pred (A :: 'a \<Rightarrow> bool) B R \<equiv> ((x : A) \<rightarrow> B x) R \<and> in_dom R = A"
adhoc_overloading crel_dep_mono_wrt crel_dep_mono_wrt_pred

definition "crel_mono_wrt_pred (A :: 'a \<Rightarrow> bool) B \<equiv> (((_ :: 'a) : A) \<rightarrow>\<^sub>c B)"
adhoc_overloading crel_mono_wrt crel_mono_wrt_pred

lemma crel_mono_wrt_pred_eq_crel_dep_mono_wrt_pred:
  "(((A :: 'a \<Rightarrow> bool) \<rightarrow>\<^sub>c (B :: 'b \<Rightarrow> bool)) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool) = (((_ :: 'a) : A) \<rightarrow>\<^sub>c B)"
  by (simp add: crel_mono_wrt_pred_def)

lemma crel_mono_wrt_pred_eq_crel_dep_mono_wrt_pred_uhint [uhint]:
  assumes "(A :: 'a \<Rightarrow> bool) \<equiv> A'"
  and "\<And>x. B \<equiv> B' x"
  shows "(A \<rightarrow>\<^sub>c B) \<equiv> ((x : A') \<rightarrow>\<^sub>c B' x)"
  using assms by (simp add: crel_mono_wrt_pred_eq_crel_dep_mono_wrt_pred)

lemma crel_mono_wrt_pred_iff_crel_dep_mono_wrt_pred:
  "((A :: 'a \<Rightarrow> bool) \<rightarrow>\<^sub>c (B :: 'b \<Rightarrow> bool)) (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) \<longleftrightarrow> (((_ :: 'a) : A) \<rightarrow>\<^sub>c B) R"
  by (simp add: crel_mono_wrt_pred_def)

lemma crel_dep_mono_wrt_predI [intro]:
  assumes "((x : A) \<rightarrow> B x) R"
  and "in_dom R \<le> A"
  shows "((x : A) \<rightarrow>\<^sub>c B x) R"
  unfolding crel_dep_mono_wrt_pred_def using assms
  by (intro conjI antisym le_in_dom_if_left_total_on) auto

lemma crel_dep_mono_wrt_predI':
  assumes "left_total_on A R"
  and "right_unique_on A R"
  and "({\<Sum>}x : A. B x) R"
  shows "((x : A) \<rightarrow>\<^sub>c B x) R"
proof (intro crel_dep_mono_wrt_predI rel_dep_mono_wrt_predI dep_mono_wrt_predI)
  fix x assume "A x"
  with assms obtain y where "B x y" "R x y" by auto
  moreover with assms have "R`x = y" by (auto intro: eval_eq_if_right_unique_onI)
  ultimately show "B x (R`x)" by simp
qed (use assms in auto)

lemma crel_dep_mono_wrt_predE:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) R"
  obtains "((x : A) \<rightarrow> B x) R" "in_dom R = A"
  using assms unfolding crel_dep_mono_wrt_pred_def by auto

lemma crel_dep_mono_wrt_predE' [elim]:
  notes crel_dep_mono_wrt_predE[elim]
  assumes "((x : A) \<rightarrow>\<^sub>c B x) R"
  obtains "((x : A) \<rightarrow> B x) R" "({\<Sum>}x : A. B x) R"
proof
  show "({\<Sum>}x : A. B x) R"
  proof (rule dep_bin_relI)
    fix x y assume "R x y" "A x"
    with assms have "R`x = y" "B x (R`x)" by auto
    then show "B x y" by simp
  qed (use assms in auto)
qed (use assms in auto)

lemma crel_dep_mono_wrt_pred_cong [cong]:
  assumes "A = A'"
  and "\<And>x y. A' x \<Longrightarrow> B x = B' x"
  shows "((x : A) \<rightarrow>\<^sub>c B x) = ((x : A') \<rightarrow>\<^sub>c B' x)"
  using assms by (intro ext) (auto elim!: crel_dep_mono_wrt_predE)

lemma in_dom_eq_if_crel_dep_mono_wrt_pred [simp]:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) R"
  shows "in_dom R = A"
  using assms by (auto elim: crel_dep_mono_wrt_predE)

lemma in_codom_le_in_codom_on_if_crel_dep_mono_wrt_pred:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) R"
  shows "in_codom R \<le> in_codom_on A B"
  using assms by fast

lemma crel_mono_wrt_predI [intro]:
  assumes "(A \<rightarrow> B) R"
  and "in_dom R \<le> A"
  shows "(A \<rightarrow>\<^sub>c B) R"
  using assms by (urule crel_dep_mono_wrt_predI)

lemma crel_mono_wrt_predI':
  assumes "left_total_on A R"
  and "right_unique_on A R"
  and "(A {\<times>} B) R"
  shows "(A \<rightarrow>\<^sub>c B) R"
  using assms by (urule crel_dep_mono_wrt_predI')

lemma crel_mono_wrt_predE:
  assumes "(A \<rightarrow>\<^sub>c B) R"
  obtains "(A \<rightarrow> B) R" "in_dom R = A"
  using assms by (urule (e) crel_dep_mono_wrt_predE)

lemma crel_mono_wrt_predE' [elim]:
  assumes "(A \<rightarrow>\<^sub>c B) R"
  obtains "(A \<rightarrow> B) R" "(A {\<times>} B) R"
  using assms by (urule (e) crel_dep_mono_wrt_predE')

lemma in_dom_eq_if_crel_mono_wrt_pred [simp]:
  assumes "(A \<rightarrow>\<^sub>c B) R"
  shows "in_dom R = A"
  using assms by (urule in_dom_eq_if_crel_dep_mono_wrt_pred)

lemma eq_if_rel_if_rel_if_crel_dep_mono_wrt_predI:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) R"
  and "R x y" "R x y'"
  shows "y = y'"
  using assms by (auto intro: eq_if_rel_if_rel_if_rel_dep_mono_wrt_predI)

lemma eval_eq_if_rel_if_crel_dep_mono_wrt_predI [simp]:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) R"
  and "R x y"
  shows "R`x = y"
  using assms by (auto intro: eval_eq_if_rel_if_rel_dep_mono_wrt_predI)

lemma crel_dep_mono_wrt_pred_relE:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) R"
  and "R x y"
  obtains "A x" "B x y" "R`x = y"
  using assms by (auto elim: rel_dep_mono_wrt_pred_relE)

lemma crel_dep_mono_wrt_pred_relE':
  assumes "((x : A) \<rightarrow>\<^sub>c B x) R"
  obtains "\<And>x y. R x y \<Longrightarrow> A x \<and> B x y \<and> R`x = y"
  using assms by (auto elim: crel_dep_mono_wrt_pred_relE)

lemma rel_restrict_left_eq_self_if_crel_dep_mono_wrt_pred [simp]:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) R"
  shows "R\<restriction>\<^bsub>A\<^esub> = R"
  using assms by auto

text \<open>Note: clean function relations are not contravariant on their domain.\<close>

lemma crel_dep_mono_wrt_pred_covariant_codom:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) R"
  and "\<And>x. A x \<Longrightarrow> B x (R`x) \<Longrightarrow> B' x (R`x)"
  shows "((x : A) \<rightarrow>\<^sub>c B' x) R"
  using assms by (force intro: rel_dep_mono_wrt_pred_covariant_codom)

lemma eq_comp_eval_restrict_left_le_if_crel_dep_mono_wrt_pred:
  assumes [uhint]: "((x : A) \<rightarrow>\<^sub>c B x) R"
  shows "((=) \<circ> eval R)\<restriction>\<^bsub>A\<^esub> \<le> R"
  supply rel_restrict_left_eq_self_if_crel_dep_mono_wrt_pred[uhint]
  by (urule eq_comp_eval_restrict_left_le_if_rel_dep_mono_wrt_pred) (use assms in auto)

lemma le_eq_comp_eval_restrict_left_if_rel_dep_mono_wrt_pred:
  assumes [uhint]: "((x : A) \<rightarrow>\<^sub>c B x) R"
  shows "R \<le> ((=) \<circ> eval R)\<restriction>\<^bsub>A\<^esub>"
  supply rel_restrict_left_eq_self_if_crel_dep_mono_wrt_pred[uhint]
  by (urule restrict_left_le_eq_comp_eval_restrict_left_if_rel_dep_mono_wrt_pred) (use assms in auto)

corollary restrict_left_eq_eq_comp_eval_if_crel_dep_mono_wrt_pred:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) R"
  shows "R = ((=) \<circ> eval R)\<restriction>\<^bsub>A\<^esub>"
  using assms eq_comp_eval_restrict_left_le_if_crel_dep_mono_wrt_pred
    le_eq_comp_eval_restrict_left_if_rel_dep_mono_wrt_pred
  by (intro antisym) auto

lemma eval_eq_if_crel_dep_mono_wrt_pred_if_rel_dep_mono_wrt_predI:
  fixes R :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes "((x : A) \<rightarrow> B x) R" "((x : A') \<rightarrow>\<^sub>c B' x) R'"
  and "R \<le> R'"
  and "A x"
  shows "R`x = R'`x"
proof -
  from assms have "A' x" by (blast elim: crel_dep_mono_wrt_pred_relE)
  with assms show ?thesis by (blast intro: eval_eq_if_rel_dep_mono_wrt_predI)
qed

lemma crel_dep_mono_wrt_pred_ext:
  assumes "((x : A) \<rightarrow>\<^sub>c B x) R" "((x : A) \<rightarrow>\<^sub>c B' x) R'"
  and "\<And>x. A x \<Longrightarrow> R`x = R'`x"
  shows "R = R'"
  using assms
  by (intro eq_if_rel_agree_on_if_dep_bin_relI[where ?A=A and ?B=B and ?\<R>="(=) R \<squnion> (=) R'"]
    rel_agree_on_if_eval_eq_if_rel_dep_mono_wrt_pred)
  auto

lemma eq_if_le_if_crel_dep_mono_wrt_pred_if_rel_dep_mono_wrt_pred:
  assumes "((x : A) \<rightarrow> B x) R" "((x : A) \<rightarrow>\<^sub>c B' x) R'"
  and "R \<le> R'"
  shows "R = R'"
proof (intro ext iffI)
  fix x y assume "R' x y"
  with assms have "R'`x = y" "A x" by auto
  moreover with assms have "R`x = R'`x" by (blast intro: eval_eq_if_crel_dep_mono_wrt_pred_if_rel_dep_mono_wrt_predI)
  ultimately show "R x y" using assms by (auto intro: rel_if_eval_eq_if_rel_dep_mono_wrt_predI)
qed (use assms in auto)

lemma ex_dom_crel_dep_mono_wrt_pred_iff_crel_dep_mono_wrt_pred_in_dom:
  "(\<exists>(A :: 'a \<Rightarrow> bool). ((x : A) \<rightarrow>\<^sub>c B x) R) \<longleftrightarrow> (((x : in_dom R) \<rightarrow>\<^sub>c B x) R)"
  by auto

lemma crel_mono_wrt_pred_bottom_bottom: "((\<bottom> :: 'a \<Rightarrow> bool) \<rightarrow>\<^sub>c A) (\<bottom> :: 'a \<Rightarrow> 'b \<Rightarrow> bool)"
  by fastforce

lemma crel_dep_mono_wrt_pred_bottom_iff_eq_bottom [iff]: "((x : (\<bottom> :: 'a \<Rightarrow> bool)) \<rightarrow>\<^sub>c B x) R \<longleftrightarrow> R = \<bottom>"
  by fastforce

lemma mono_crel_dep_mono_wrt_pred_top_crel_dep_mono_wrt_pred_inf_rel_restrict_left:
  "(((x : A) \<rightarrow>\<^sub>c B x) \<Rightarrow> (A' : \<top>) \<Rightarrow> (x : A \<sqinter> A') \<rightarrow>\<^sub>c B x) rel_restrict_left"
  by (intro mono_wrt_predI dep_mono_wrt_predI crel_dep_mono_wrt_predI'
    (*TODO: should be solved by some type-checking automation*)
    mono_right_unique_on_top_right_unique_on_inf_rel_restrict_left
      [THEN dep_mono_wrt_predD, THEN dep_mono_wrt_predD]
    mono_left_total_on_top_left_total_on_inf_rel_restrict_left
      [THEN dep_mono_wrt_predD, THEN dep_mono_wrt_predD]
    mono_dep_bin_rel_top_dep_bin_rel_inf_rel_restrict_left
      [THEN mono_wrt_predD, THEN dep_mono_wrt_predD])
  auto

lemma mono_rel_dep_mono_wrt_pred_ge_crel_dep_mono_wrt_pred_rel_restrict_left:
  "(((x : A) \<rightarrow> B x) \<Rightarrow> (A' : (\<ge>) A) \<Rightarrow> (x : A') \<rightarrow>\<^sub>c B x) rel_restrict_left"
proof (intro mono_wrt_predI dep_mono_wrt_predI crel_dep_mono_wrt_predI)
  fix A A' :: "'a \<Rightarrow> bool" and B and R :: "'a \<Rightarrow> 'b \<Rightarrow> bool" assume "((x : A) \<rightarrow> B x) R"
  with mono_rel_dep_mono_wrt_pred_top_rel_dep_mono_wrt_pred_inf_rel_restrict_left
    have "((x : A \<sqinter> A') \<rightarrow> B x) R\<restriction>\<^bsub>A'\<^esub>" by force
  moreover assume "A' \<le> A"
  ultimately show "((x : A') \<rightarrow> B x) R\<restriction>\<^bsub>A'\<^esub>" by (simp only: inf_absorb2)
qed auto

lemma crel_dep_mono_wrt_pred_eq_restrict: "((x : (A :: 'a \<Rightarrow> bool)) \<rightarrow>\<^sub>c (=) x) (=)\<restriction>\<^bsub>A\<^esub>"
  by fastforce

end
