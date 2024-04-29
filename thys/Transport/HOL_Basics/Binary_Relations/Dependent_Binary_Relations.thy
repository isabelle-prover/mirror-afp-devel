\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Dependent Binary Relations\<close>
theory Dependent_Binary_Relations
  imports
    Binary_Relations_Agree
begin

consts dep_bin_rel :: "'a \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'd \<Rightarrow> bool"
consts bin_rel :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool"

bundle bin_rel_syntax
begin
syntax "_dep_bin_rel" :: \<open>idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd\<close> ("{\<Sum>}_ : _./ _" [41, 41, 40] 51)
notation bin_rel (infixl "{\<times>}" 51)
end
bundle no_bin_rel_syntax
begin
no_syntax "_dep_bin_rel" :: \<open>idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd\<close> ("{\<Sum>}_ : _./ _" [41, 41, 40] 51)
no_notation bin_rel (infixl "{\<times>}" 51)
end
unbundle bin_rel_syntax
translations
  "{\<Sum>}x : A. B" \<rightleftharpoons> "CONST dep_bin_rel A (\<lambda>x. B)"

definition "dep_bin_rel_pred (A :: 'a \<Rightarrow> bool) (B :: 'a \<Rightarrow> 'b \<Rightarrow> bool) (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool) \<equiv>
  \<forall>x y. R x y \<longrightarrow> A x \<and> B x y"
adhoc_overloading dep_bin_rel dep_bin_rel_pred

definition "bin_rel_pred (A :: 'a \<Rightarrow> bool) (B :: 'b \<Rightarrow> bool) :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool \<equiv>
  {\<Sum>}(_ :: 'a) : A. B"
adhoc_overloading bin_rel bin_rel_pred

lemma bin_rel_pred_eq_dep_bin_rel_pred: "A {\<times>} B = {\<Sum>}_ : A. B"
  unfolding bin_rel_pred_def by auto

lemma bin_rel_pred_eq_dep_bin_rel_pred_uhint [uhint]:
  assumes "A \<equiv> A'"
  and "B' \<equiv> (\<lambda>_. B)"
  shows "A {\<times>} B \<equiv> {\<Sum>}x : A'. B' x"
  using assms by (simp add: bin_rel_pred_eq_dep_bin_rel_pred)

lemma bin_rel_pred_iff_dep_bin_rel_pred: "(A {\<times>} B) R \<longleftrightarrow> ({\<Sum>}_ : A. B) R"
  unfolding bin_rel_pred_eq_dep_bin_rel_pred by auto

lemma dep_bin_relI [intro]:
  assumes "\<And>x y. R x y \<Longrightarrow> A x"
  and "\<And>x y. R x y \<Longrightarrow> A x \<Longrightarrow> B x y"
  shows "({\<Sum>}x : A. B x) R"
  using assms unfolding dep_bin_rel_pred_def by auto

lemma dep_bin_rel_if_bin_rel_and:
  assumes "\<And>x y. R x y \<Longrightarrow> A x \<and> B x y"
  shows "({\<Sum>}x : A. B x) R"
  using assms by auto

lemma dep_bin_relE [elim]:
  assumes "({\<Sum>}x : A. B x) R"
  and "R x y"
  obtains "A x" "B x y"
  using assms unfolding dep_bin_rel_pred_def by auto

lemma dep_bin_relE':
  assumes "({\<Sum>}x : A. B x) R"
  obtains "\<And>x y. R x y \<Longrightarrow> A x \<and> B x y"
  using assms by auto

lemma bin_relI [intro]:
  assumes "\<And>x y. R x y \<Longrightarrow> A x"
  and "\<And>x y. R x y \<Longrightarrow> A x \<Longrightarrow> B y"
  shows "(A {\<times>} B) R"
  using assms by (urule dep_bin_relI where chained = fact)

lemma bin_rel_if_bin_rel_and:
  assumes "\<And>x y. R x y \<Longrightarrow> A x \<and> B y"
  shows "(A {\<times>} B) R"
  using assms by (urule dep_bin_rel_if_bin_rel_and)

lemma bin_relE [elim]:
  assumes "(A {\<times>} B) R"
  and "R x y"
  obtains "A x" "B y"
  using assms by (urule (e) dep_bin_relE)

lemma bin_relE':
  assumes "(A {\<times>} B) R"
  obtains "\<And>x y. R x y \<Longrightarrow> A x \<and> B y"
  using assms by (urule (e) dep_bin_relE')

lemma dep_bin_rel_cong [cong]:
  "\<lbrakk>A = A'; \<And>x. A' x \<Longrightarrow> B x = B' x\<rbrakk> \<Longrightarrow> ({\<Sum>}x : A. B x) = {\<Sum>}x : A'. B' x"
  by (intro ext iffI dep_bin_relI) fastforce+

lemma le_dep_bin_rel_if_le_dom:
  assumes "A \<le> A'"
  shows "({\<Sum>}x : A. B x) \<le> ({\<Sum>}x : A'. B x)"
  using assms by (intro le_predI dep_bin_relI) auto

lemma dep_bin_rel_covariant_codom:
  assumes "({\<Sum>}x : A. B x) R"
  and "\<And>x y. R x y \<Longrightarrow> A x \<Longrightarrow> B x y \<Longrightarrow> B' x y"
  shows "({\<Sum>}x : A. B' x) R"
  using assms by (intro dep_bin_relI) auto

lemma mono_dep_bin_rel: "((\<le>) \<Rightarrow> (\<le>) \<Rrightarrow> (\<ge>) \<Rrightarrow> (\<le>)) dep_bin_rel"
  by (intro mono_wrt_relI Fun_Rel_relI dep_bin_relI) force

lemma mono_bin_rel: "((\<le>) \<Rightarrow> (\<le>) \<Rrightarrow> (\<ge>) \<Rrightarrow> (\<le>)) ({\<times>})"
  by (intro mono_wrt_relI Fun_Rel_relI) auto

lemma in_dom_le_if_dep_bin_rel:
  assumes "({\<Sum>}x : A. B x) R"
  shows "in_dom R \<le> A"
  using assms by auto

lemma in_codom_le_in_codom_on_if_dep_bin_rel:
  assumes "({\<Sum>}x : A. B x) R"
  shows "in_codom R \<le> in_codom_on A B"
  using assms by fast

lemma rel_restrict_left_eq_self_if_dep_bin_rel [simp]:
  assumes "({\<Sum>}x : A. B x) R"
  shows "R\<restriction>\<^bsub>A\<^esub> = R"
  using assms rel_restrict_left_eq_self_if_in_dom_le by auto

lemma dep_bin_rel_bottom_dom_iff_eq_bottom [iff]: "({\<Sum>}x : \<bottom>. B x) R \<longleftrightarrow> R = \<bottom>"
  by fastforce

lemma dep_bin_rel_bottom_codom_iff_eq_bottom [iff]: "({\<Sum>}x : A. \<bottom>) R \<longleftrightarrow> R = \<bottom>"
  by fastforce

lemma mono_bin_rel_dep_bin_rel_bin_rel_rel_comp:
  "(A {\<times>} B \<Rightarrow> ({\<Sum>}x : B. C x) \<Rightarrow> A {\<times>} in_codom_on B C) (\<circ>\<circ>)"
  by fastforce

lemma mono_dep_bin_rel_bin_rel_rel_inv: "(({\<Sum>}x : A. B x) \<Rightarrow> in_codom_on A B {\<times>} A) rel_inv"
  by force

lemma mono_bin_rel_rel_inv: "(A {\<times>} B \<Rightarrow> B {\<times>} A) rel_inv"
  by auto

lemma mono_dep_bin_rel_top_dep_bin_rel_inf_rel_restrict_left:
  "(({\<Sum>}x : A. B x) \<Rightarrow> (P : \<top>) \<Rightarrow> ({\<Sum>}x : A \<sqinter> P. B x)) rel_restrict_left"
  by fast

lemma mono_dep_bin_rel_top_dep_bin_rel_inf_rel_restrict_right:
  "(({\<Sum>}x : A. B x) \<Rightarrow> (P : \<top>) \<Rightarrow> ({\<Sum>}x : A. B x \<sqinter> P)) rel_restrict_right"
  by fast

lemma le_if_rel_agree_on_if_dep_bin_relI:
  assumes "({\<Sum>}x : A. B x) R"
  and "rel_agree_on A \<R>"
  and "\<R> R" "\<R> R'"
  shows "R \<le> R'"
  using assms by (intro le_if_in_dom_le_if_rel_agree_onI in_dom_le_if_dep_bin_rel)

lemma eq_if_rel_agree_on_if_dep_bin_relI:
  assumes "({\<Sum>}x : A. B x) R" "({\<Sum>}x : A. B' x) R'"
  and "rel_agree_on A \<R>"
  and "\<R> R" "\<R> R'"
  shows "R = R'"
  using assms by (intro eq_if_in_dom_le_if_rel_agree_onI in_dom_le_if_dep_bin_rel)


end