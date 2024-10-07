\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Functions as Binary Relations\<close>
theory Binary_Relations_Function_Base
  imports
    Binary_Relations_Function_Evaluation
    Binary_Relations_Left_Total
begin

text \<open>Relational functions may contain further elements outside their specification.\<close>

consts rel_dep_mono_wrt :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"
consts rel_mono_wrt :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"

open_bundle rel_mono_wrt_syntax
begin
notation "rel_mono_wrt" (infixr "\<rightarrow>" 40)
syntax
  "_rel_dep_mono_wrt_pred" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool" (\<open>'(_/ :/ _') \<rightarrow> (_)\<close> [41, 41, 40] 40)
end
syntax_consts "_rel_dep_mono_wrt_pred" \<rightleftharpoons> rel_dep_mono_wrt
translations
  "(x : A) \<rightarrow> B" \<rightleftharpoons> "CONST rel_dep_mono_wrt A (\<lambda>x. B)"

definition "rel_dep_mono_wrt_pred (A :: 'a \<Rightarrow> bool) (B :: 'a \<Rightarrow> 'b \<Rightarrow> bool) (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) \<equiv>
  left_total_on A R \<and> right_unique_on A R \<and> ((x : A) \<Rightarrow> B x) (eval R)"
adhoc_overloading rel_dep_mono_wrt rel_dep_mono_wrt_pred

definition "rel_mono_wrt_pred (A :: 'a \<Rightarrow> bool) (B :: 'b \<Rightarrow> bool) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool \<equiv>
  rel_dep_mono_wrt_pred A (\<lambda>(_ :: 'a). B)"
adhoc_overloading rel_mono_wrt rel_mono_wrt_pred

lemma rel_mono_wrt_pred_eq_rel_dep_mono_wrt_pred:
  "(((A :: 'a \<Rightarrow> bool) \<rightarrow> (B :: 'b \<Rightarrow> bool)) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool) = (((_ :: 'a) : A) \<rightarrow> B)"
  by (simp add: rel_mono_wrt_pred_def)

lemma rel_mono_wrt_pred_eq_rel_dep_mono_wrt_pred_uhint [uhint]:
  assumes "(A :: 'a \<Rightarrow> bool) \<equiv> A'"
  and "\<And>x. B :: 'b \<Rightarrow> bool \<equiv> B' x"
  shows "(A \<rightarrow> B) \<equiv> ((x : A') \<rightarrow> B' x)"
  using assms by (simp add: rel_mono_wrt_pred_eq_rel_dep_mono_wrt_pred)

lemma rel_mono_wrt_pred_iff_rel_dep_mono_wrt_pred:
  "((A :: 'a \<Rightarrow> bool) \<rightarrow> (B :: 'b \<Rightarrow> bool)) (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) \<longleftrightarrow> (((_ :: 'a) : A) \<rightarrow> B) R"
  by (simp add: rel_mono_wrt_pred_def)

lemma rel_dep_mono_wrt_predI [intro]:
  assumes "left_total_on A R"
  and "right_unique_on A R"
  and "((x : A) \<Rightarrow> B x) (eval R)"
  shows "((x : A) \<rightarrow> B x) R"
  using assms unfolding rel_dep_mono_wrt_pred_def by auto

lemma rel_dep_mono_wrt_predE [elim]:
  assumes "((x : A) \<rightarrow> B x) R"
  obtains "left_total_on A R" "right_unique_on A R" "((x : A) \<Rightarrow> B x) (eval R)"
  using assms unfolding rel_dep_mono_wrt_pred_def by auto

lemma rel_dep_mono_wrt_pred_cong [cong]:
  assumes "A = A'"
  and "\<And>x y. A' x \<Longrightarrow> B x = B' x"
  shows "((x : A) \<rightarrow> B x) = ((x : A') \<rightarrow> B' x)"
  using assms by fastforce

lemma rel_mono_wrt_predI [intro]:
  assumes "left_total_on A R"
  and "right_unique_on A R"
  and "(A \<Rightarrow> B) (eval R)"
  shows "(A \<rightarrow> B) R"
  using assms by (urule rel_dep_mono_wrt_predI)

lemma rel_mono_wrt_predE [elim]:
  assumes "(A \<rightarrow> B) R"
  obtains "left_total_on A R" "right_unique_on A R" "(A \<Rightarrow> B) (eval R)"
  using assms by (urule (e) rel_dep_mono_wrt_predE)

lemma mono_rel_dep_mono_wrt_pred_dep_mono_wrt_pred_eval: "(((x : A) \<rightarrow> B x) \<Rightarrow> (x : A) \<Rightarrow> B x) eval"
  by auto

lemma ex1_rel_right_if_rel_dep_mono_wrt_predI:
  assumes "((x : A) \<rightarrow> B x) R"
  and "A x"
  shows "\<exists>!y. R x y"
  using assms by (blast dest: right_unique_onD)

lemma eq_if_rel_if_rel_if_rel_dep_mono_wrt_predI:
  assumes "((x : A) \<rightarrow> B x) R"
  and "A x"
  and "R x y" "R x y'"
  shows "y = y'"
  using assms by (blast dest: right_unique_onD)

lemma eval_eq_if_rel_if_rel_dep_mono_wrt_predI [simp]:
  assumes "((x : A) \<rightarrow> B x) R"
  and "A x"
  and "R x y"
  shows "R`x = y"
  using assms by (intro eq_if_rel_if_rel_if_rel_dep_mono_wrt_predI[OF assms, symmetric])
  (blast intro!: rel_eval_if_ex1[where ?R=R] ex1_rel_right_if_rel_dep_mono_wrt_predI)

lemma rel_if_eval_eq_if_rel_dep_mono_wrt_predI:
  assumes "((x : A) \<rightarrow> B x) R"
  and "A x"
  and "R`x = y"
  shows "R x y"
  by (rule rel_if_eval_eq_if_in_dom_if_right_unique_on_eq[where ?R=R])
  (use assms in \<open>blast dest: right_unique_onD\<close>)+

corollary rel_eval_if_rel_dep_mono_wrt_predI:
  assumes "((x : A) \<rightarrow> B x) R"
  and "A x"
  shows "R x (R`x)"
  using assms by (rule rel_if_eval_eq_if_rel_dep_mono_wrt_predI) simp

corollary rel_iff_eval_eq_if_rel_dep_mono_wrt_predI:
  assumes "((x : A) \<rightarrow> B x) R"
  and "A x"
  shows "R x y \<longleftrightarrow> R`x = y"
  using assms by (intro iffI; rule eval_eq_if_rel_if_rel_dep_mono_wrt_predI rel_if_eval_eq_if_rel_dep_mono_wrt_predI)

lemma rel_dep_mono_wrt_pred_relE:
  assumes "((x : A) \<rightarrow> B x) R"
  and "A x"
  and "R x y"
  obtains "B x y" "R`x = y"
proof
  from assms show "R`x = y" by simp
  with assms show "B x y" by blast
qed

lemma rel_dep_mono_wrt_pred_relE':
  assumes "((x : A) \<rightarrow> B x) R"
  obtains "\<And>x y. A x \<Longrightarrow> R x y \<Longrightarrow> B x y \<and> R`x = y"
  using assms by (auto elim: rel_dep_mono_wrt_pred_relE)

lemma rel_codom_if_rel_if_pred_if_rel_dep_mono_wrt_pred:
  assumes "((x : A) \<rightarrow> B x) R"
  and "A x"
  and "R x y"
  shows "B x y"
  using assms by (auto elim: rel_dep_mono_wrt_pred_relE)

lemma rel_dep_mono_wrt_pred_contravariant_dom:
  assumes "((x : A) \<rightarrow> B x) R"
  and [dest]: "\<And>x. A' x \<Longrightarrow> A x"
  shows "((x : A') \<rightarrow> B x) R"
  using assms by (fast intro!: rel_dep_mono_wrt_predI dest: right_unique_onD)

lemma rel_dep_mono_wrt_pred_covariant_codom:
  assumes "((x : A) \<rightarrow> B x) R"
  and "\<And>x. A x \<Longrightarrow> B x (R`x) \<Longrightarrow> B' x (R`x)"
  shows "((x : A) \<rightarrow> B' x) R"
  using assms by (fast dest: right_unique_onD)

lemma rel_mono_wrt_pred_in_codom_on_if_rel_dep_mono_wrt_pred:
  assumes "((x : A) \<rightarrow> B x) R"
  shows "(A \<rightarrow> in_codom_on A B) R"
  using assms by fastforce

lemma eq_comp_eval_restrict_left_le_if_rel_dep_mono_wrt_pred:
  assumes "((x : A) \<rightarrow> B x) R"
  shows "((=) \<circ> eval R)\<restriction>\<^bsub>A\<^esub> \<le> R\<restriction>\<^bsub>A\<^esub>"
  using assms by (intro le_relI) (force intro: rel_eval_if_rel_dep_mono_wrt_predI)

lemma restrict_left_le_eq_comp_eval_restrict_left_if_rel_dep_mono_wrt_pred:
  assumes "((x : A) \<rightarrow> B x) R"
  shows "R\<restriction>\<^bsub>A\<^esub> \<le> ((=) \<circ> eval R)\<restriction>\<^bsub>A\<^esub>"
  using assms by (intro le_relI) force

corollary restrict_left_eq_eq_comp_eval_if_rel_dep_mono_wrt_pred:
  assumes "((x : A) \<rightarrow> B x) R"
  shows "R\<restriction>\<^bsub>A\<^esub> = ((=) \<circ> eval R)\<restriction>\<^bsub>A\<^esub>"
  using assms eq_comp_eval_restrict_left_le_if_rel_dep_mono_wrt_pred
    restrict_left_le_eq_comp_eval_restrict_left_if_rel_dep_mono_wrt_pred
  by (intro antisym) auto

lemma eval_eq_if_rel_dep_mono_wrt_predI:
  fixes R :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes "((x : A) \<rightarrow> B x) R" "((x : A') \<rightarrow> B' x) R'"
  and "R \<le> R'"
  and "(A \<sqinter> A') x"
  shows "R`x = R'`x"
proof -
  from assms have "R' x (R`x)" "R' x (R'`x)" by (auto intro: rel_eval_if_rel_dep_mono_wrt_predI)
  with assms show ?thesis by (intro eval_eq_if_rel_if_rel_dep_mono_wrt_predI[symmetric]) force+
qed

lemma rel_agree_on_if_eval_eq_if_rel_dep_mono_wrt_pred:
  assumes rel_dep_mono_wrt_pred: "\<And>R. \<R> R \<Longrightarrow> \<exists>B. ((x : A) \<rightarrow> B x) R"
  and "\<And>R R' x. \<R> R \<Longrightarrow> \<R> R' \<Longrightarrow> A x \<Longrightarrow> R`x = R'`x"
  shows "rel_agree_on A \<R>"
proof (rule rel_agree_onI)
  fix x y R R' assume hyps: "\<R> R" "\<R> R'" "A x" "R x y"
  with rel_dep_mono_wrt_pred have "y = R`x" by fastforce
  also from assms hyps have "... = R'`x" by blast
  finally have "y = R'`x" .
  moreover from rel_dep_mono_wrt_pred[OF \<open>\<R> R'\<close>] obtain B where "((x : A) \<rightarrow> B x) R'" by blast
  ultimately show "R' x y" using \<open>A x\<close> by (auto intro: rel_eval_if_rel_dep_mono_wrt_predI)
qed

lemma mono_rel_dep_mono_wrt_pred_top_rel_dep_mono_wrt_pred_inf_rel_restrict_left:
  "(((x : A) \<rightarrow> B x) \<Rightarrow> (A' : \<top>) \<Rightarrow> ((x : A \<sqinter> A') \<rightarrow> B x)) rel_restrict_left"
  by (intro mono_wrt_predI dep_mono_wrt_predI rel_dep_mono_wrt_predI
    (*TODO: should be solved by some type-checking automation*)
    mono_right_unique_on_top_right_unique_on_inf_rel_restrict_left
      [THEN dep_mono_wrt_predD, THEN dep_mono_wrt_predD]
    mono_left_total_on_top_left_total_on_inf_rel_restrict_left
      [THEN dep_mono_wrt_predD, THEN dep_mono_wrt_predD])
  auto

end
