\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Functions as Binary Relations\<close>
theory Binary_Relations_Function_Base
  imports
    Binary_Relations_Function_Evaluation
    Binary_Relations_Left_Total
begin

text \<open>Relational functions may contain further elements outside their specification.\<close>

consts rel_dep_fun :: "'a \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'd \<Rightarrow> bool"
consts rel_fun :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool"

bundle rel_fun_syntax
begin
syntax
  "_rel_fun" :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool" ("(_) \<rightarrow> (_)" [41, 40] 40)
  "_rel_dep_fun" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool" ("'(_/ :/ _') \<rightarrow> (_)" [41, 41, 40] 40)
end
bundle no_rel_fun_syntax
begin
no_syntax
  "_rel_fun" :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool" ("(_) \<rightarrow> (_)" [41, 40] 40)
  "_rel_dep_fun" :: "idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool" ("'(_/ :/ _') \<rightarrow> (_)" [41, 41, 40] 40)
end
unbundle rel_fun_syntax
translations
  "A \<rightarrow> B" \<rightleftharpoons> "CONST rel_fun A B"
  "(x : A) \<rightarrow> B" \<rightleftharpoons> "CONST rel_dep_fun A (\<lambda>x. B)"

definition "rel_dep_fun_pred (A :: 'a \<Rightarrow> bool) (B :: 'a \<Rightarrow> 'b \<Rightarrow> bool) (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) \<equiv>
  left_total_on A R \<and> right_unique_on A R \<and> ((x : A) \<Rrightarrow>\<^sub>m B x) (eval R)"
adhoc_overloading rel_dep_fun rel_dep_fun_pred

definition "rel_dep_fun_pred' (A :: 'a \<Rightarrow> bool) (B :: 'a \<Rightarrow> 'b \<Rightarrow> bool) (f :: 'a \<Rightarrow> 'b) \<equiv> True"
adhoc_overloading rel_dep_fun rel_dep_fun_pred'


definition "rel_fun_pred (A :: 'a \<Rightarrow> bool) (B :: 'b \<Rightarrow> bool) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool \<equiv>
  rel_dep_fun_pred A (\<lambda>(_ :: 'a). B)"
adhoc_overloading rel_fun rel_fun_pred

lemma rel_fun_eq_rel_dep_fun:
  "(((A :: 'a \<Rightarrow> bool) \<rightarrow> (B :: 'b \<Rightarrow> bool)) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool) = (((_ :: 'a) : A) \<rightarrow> B)"
  by (simp add: rel_fun_pred_def)

lemma rel_fun_eq_rel_dep_fun_uhint [uhint]:
  assumes "(A :: 'a \<Rightarrow> bool) \<equiv> A'"
  and "\<And>x. B :: 'b \<Rightarrow> bool \<equiv> B' x"
  shows "(A \<rightarrow> B) \<equiv> ((x : A') \<rightarrow> B' x)"
  using assms by (simp add: rel_fun_eq_rel_dep_fun)

lemma rel_fun_iff_rel_dep_fun:
  "((A :: 'a \<Rightarrow> bool) \<rightarrow> (B :: 'b \<Rightarrow> bool)) (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) \<longleftrightarrow> (((_ :: 'a) : A) \<rightarrow> B) R"
  by (simp add: rel_fun_pred_def)

lemma rel_dep_funI [intro]:
  assumes "left_total_on A R"
  and "right_unique_on A R"
  and "((x : A) \<Rrightarrow>\<^sub>m B x) (eval R)"
  shows "((x : A) \<rightarrow> B x) R"
  using assms unfolding rel_dep_fun_pred_def by auto

lemma rel_dep_funE [elim]:
  assumes "((x : A) \<rightarrow> B x) R"
  obtains "left_total_on A R" "right_unique_on A R" "((x : A) \<Rrightarrow>\<^sub>m B x) (eval R)"
  using assms unfolding rel_dep_fun_pred_def by auto

lemma rel_dep_fun_cong [cong]:
  assumes "\<And>x. A x \<longleftrightarrow> A' x"
  and "\<And>x y. A' x \<Longrightarrow> B x y \<longleftrightarrow> B' x y"
  shows "((x : A) \<rightarrow> B x) = ((x : A') \<rightarrow> B' x)"
  using assms by (intro ext) (auto intro!: rel_dep_funI left_total_onI
    dep_mono_wrt_predI intro: right_unique_onD elim!: rel_dep_funE)

lemma rel_funI [intro]:
  assumes "left_total_on A R"
  and "right_unique_on A R"
  and "(A \<Rrightarrow>\<^sub>m B) (eval R)"
  shows "(A \<rightarrow> B) R"
  using assms by (urule rel_dep_funI)

lemma rel_funE [elim]:
  assumes "(A \<rightarrow> B) R"
  obtains "left_total_on A R" "right_unique_on A R" "(A \<Rrightarrow>\<^sub>m B) (eval R)"
  using assms by (urule (e) rel_dep_funE)

lemma mono_rel_dep_fun_mono_wrt_pred_eval: "(((x : A) \<rightarrow> B x) \<Rrightarrow>\<^sub>m (x : A) \<Rrightarrow>\<^sub>m B x) eval"
  by auto

lemma ex1_rel_right_if_rel_dep_funI:
  assumes "((x : A) \<rightarrow> B x) R"
  and "A x"
  shows "\<exists>!y. R x y"
  using assms by (blast dest: right_unique_onD)

lemma eq_if_rel_if_rel_if_rel_dep_funI:
  assumes "((x : A) \<rightarrow> B x) R"
  and "A x"
  and "R x y" "R x y'"
  shows "y = y'"
  using assms by (blast dest: right_unique_onD)

lemma eval_eq_if_rel_if_rel_dep_funI [simp]:
  assumes "((x : A) \<rightarrow> B x) R"
  and "A x"
  and "R x y"
  shows "R`x = y"
  using assms by (intro eq_if_rel_if_rel_if_rel_dep_funI[OF assms, symmetric])
  (blast intro!: rel_eval_if_ex1[where ?R=R] ex1_rel_right_if_rel_dep_funI)

lemma rel_if_eval_eq_if_rel_dep_funI:
  assumes "((x : A) \<rightarrow> B x) R"
  and "A x"
  and "R`x = y"
  shows "R x y"
  by (rule rel_if_eval_eq_if_in_dom_if_right_unique_on_eq[where ?R=R])
  (use assms in \<open>blast dest: right_unique_onD\<close>)+

corollary rel_eval_if_rel_dep_funI:
  assumes "((x : A) \<rightarrow> B x) R"
  and "A x"
  shows "R x (R`x)"
  using assms by (rule rel_if_eval_eq_if_rel_dep_funI) simp

corollary rel_iff_eval_eq_if_rel_dep_funI:
  assumes "((x : A) \<rightarrow> B x) R"
  and "A x"
  shows "R x y \<longleftrightarrow> R`x = y"
  using assms by (intro iffI; rule eval_eq_if_rel_if_rel_dep_funI rel_if_eval_eq_if_rel_dep_funI)

lemma rel_dep_fun_relE:
  assumes "((x : A) \<rightarrow> B x) R"
  and "A x"
  and "R x y"
  obtains "B x y" "R`x = y"
proof
  from assms show "R`x = y" by simp
  with assms show "B x y" by blast
qed

lemma rel_dep_fun_relE':
  assumes "((x : A) \<rightarrow> B x) R"
  obtains "\<And>x y. A x \<Longrightarrow> R x y \<Longrightarrow> B x y \<and> R`x = y"
  using assms by (auto elim: rel_dep_fun_relE)

lemma rel_codom_if_rel_if_pred_if_rel_dep_fun:
  assumes "((x : A) \<rightarrow> B x) R"
  and "A x"
  and "R x y"
  shows "B x y"
  using assms by (auto elim: rel_dep_fun_relE)

lemma rel_dep_fun_contravariant_dom:
  assumes "((x : A) \<rightarrow> B x) R"
  and [dest]: "\<And>x. A' x \<Longrightarrow> A x"
  shows "((x : A') \<rightarrow> B x) R"
  using assms by (fast intro!: rel_dep_funI dest: right_unique_onD)

lemma rel_dep_fun_covariant_codom:
  assumes "((x : A) \<rightarrow> B x) R"
  and "\<And>x. A x \<Longrightarrow> B x (R`x) \<Longrightarrow> B' x (R`x)"
  shows "((x : A) \<rightarrow> B' x) R"
  using assms by (fast dest: right_unique_onD)

lemma rel_fun_in_codom_on_if_rel_dep_fun:
  assumes "((x : A) \<rightarrow> B x) R"
  shows "(A \<rightarrow> in_codom_on A B) R"
  using assms by fastforce

lemma comp_eq_eval_restrict_left_le_if_rel_dep_fun:
  assumes "((x : A) \<rightarrow> B x) R"
  shows "((=) \<circ> eval R)\<restriction>\<^bsub>A\<^esub> \<le> R\<restriction>\<^bsub>A\<^esub>"
  using assms by (intro le_relI) (force intro: rel_eval_if_rel_dep_funI)

lemma restrict_left_le_comp_eq_eval_restrict_left_if_rel_dep_fun:
  assumes "((x : A) \<rightarrow> B x) R"
  shows "R\<restriction>\<^bsub>A\<^esub> \<le> ((=) \<circ> eval R)\<restriction>\<^bsub>A\<^esub>"
  using assms by (intro le_relI) force

corollary restrict_left_eq_comp_eq_eval_if_rel_dep_fun:
  assumes "((x : A) \<rightarrow> B x) R"
  shows "R\<restriction>\<^bsub>A\<^esub> = ((=) \<circ> eval R)\<restriction>\<^bsub>A\<^esub>"
  using assms comp_eq_eval_restrict_left_le_if_rel_dep_fun
    restrict_left_le_comp_eq_eval_restrict_left_if_rel_dep_fun
  by (intro antisym) auto

lemma eval_eq_if_rel_dep_funI:
  fixes R :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes "((x : A) \<rightarrow> B x) R" "((x : A') \<rightarrow> B' x) R'"
  and "R \<le> R'"
  and "(A \<sqinter> A') x"
  shows "R`x = R'`x"
proof -
  from assms have "R' x (R`x)" "R' x (R'`x)" by (auto intro: rel_eval_if_rel_dep_funI)
  with assms show ?thesis by (intro eval_eq_if_rel_if_rel_dep_funI[symmetric]) force+
qed

lemma rel_agree_on_if_eval_eq_if_rel_dep_fun:
  assumes crel_dep_fun: "\<And>R. \<R> R \<Longrightarrow> \<exists>B. ((x : A) \<rightarrow> B x) R"
  and "\<And>R R' x. \<R> R \<Longrightarrow> \<R> R' \<Longrightarrow> A x \<Longrightarrow> R`x = R'`x"
  shows "rel_agree_on A \<R>"
proof (rule rel_agree_onI)
  fix x y R R' assume hyps: "\<R> R" "\<R> R'" "A x" "R x y"
  with crel_dep_fun have "y = R`x" by fastforce
  also from assms hyps have "... = R'`x" by blast
  finally have "y = R'`x" .
  moreover from crel_dep_fun[OF \<open>\<R> R'\<close>] obtain B where "((x : A) \<rightarrow> B x) R'" by blast
  ultimately show "R' x y" using \<open>A x\<close> by (auto intro: rel_eval_if_rel_dep_funI)
qed

lemma mono_rel_dep_fun_top_rel_dep_fun_inf_rel_restrict_left:
  "(((x : A) \<rightarrow> B x) \<Rrightarrow>\<^sub>m (A' : \<top>) \<Rrightarrow>\<^sub>m (x : A \<sqinter> A') \<rightarrow> B x) rel_restrict_left"
  by (intro mono_wrt_predI dep_mono_wrt_predI rel_dep_funI
    (*TODO: should be solved by some type-checking automation*)
    mono_right_unique_on_top_right_unique_on_inf_rel_restrict_left
      [THEN dep_mono_wrt_predD, THEN dep_mono_wrt_predD]
    mono_left_total_on_top_left_total_on_inf_rel_restrict_left
      [THEN dep_mono_wrt_predD, THEN dep_mono_wrt_predD])
  auto

end
