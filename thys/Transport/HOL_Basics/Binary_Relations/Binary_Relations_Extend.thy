\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Extensions\<close>
theory Binary_Relations_Extend
  imports
    Dependent_Binary_Relations
begin

consts extend :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'c"

definition "extend_rel x y R x' y' \<equiv> (x = x' \<and> y = y') \<or> R x' y'"
adhoc_overloading extend extend_rel

lemma extend_leftI [iff]: "(extend x y R) x y"
  unfolding extend_rel_def by blast

lemma extend_rightI [intro]:
  assumes "R x' y'"
  shows "(extend x y R) x' y'"
  unfolding extend_rel_def using assms by blast

lemma extendE [elim]:
  assumes "(extend x y R) x' y'"
  obtains "x = x'" "y = y'" | "x \<noteq> x' \<or> y \<noteq> y'" "R x' y'"
  using assms unfolding extend_rel_def by blast

lemma extend_eq_self_if_rel [simp]: "R x y \<Longrightarrow> extend x y R = R"
  by auto

context
  fixes x :: 'a and y :: 'b and R :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
begin

lemma in_dom_extend_eq: "in_dom (extend x y R) = in_dom R \<squnion> (=) x"
  by (intro ext) auto

lemma in_dom_extend_iff: "in_dom (extend x y R) x' \<longleftrightarrow> in_dom R x' \<or> x = x'"
  by (auto simp: in_dom_extend_eq)

lemma codom_extend_eq: "in_codom (extend x y R) = in_codom R \<squnion> (=) y"
  by (intro ext) auto

lemma in_codom_extend_iff: "in_codom (extend x y R) y' \<longleftrightarrow> in_codom R y' \<or> y = y'"
  by (auto simp: codom_extend_eq)

end

lemma in_field_extend_eq: "in_field (extend x y R) = in_field R \<squnion> (=) x \<squnion> (=) y"
  by (intro ext) auto

lemma in_field_extend_iff: "in_field (extend x y R) z \<longleftrightarrow> in_field R z \<or> z = x \<or> z = y"
  by (auto simp: in_field_extend_eq)

lemma mono_extend: "mono (extend x y :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool)"
  by (intro monoI) force

lemma dep_mono_dep_bin_rel_extend:
  "((x : A) \<Rrightarrow>\<^sub>m B x \<Rrightarrow>\<^sub>m ({\<Sum>}x : A'. B' x) \<Rrightarrow>\<^sub>m ({\<Sum>}x : A \<squnion> A'. (B \<squnion> B') x)) extend"
  by fastforce

consts glue :: "'a \<Rightarrow> 'b"

definition "glue_rel (\<R> :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool) x \<equiv> in_codom_on \<R> (\<lambda>R. R x)"
adhoc_overloading glue glue_rel

lemma glue_rel_eq_in_codom_on: "glue \<R> x = in_codom_on \<R> (\<lambda>R. R x)"
  unfolding glue_rel_def by simp

lemma glueI [intro]:
  assumes "\<R> R"
  and "R x y"
  shows "glue \<R> x y"
  using assms unfolding glue_rel_def by blast

lemma glueE [elim!]:
  assumes "glue \<R> x y"
  obtains R where "\<R> R" "R x y"
  using assms unfolding glue_rel_def by blast

lemma glue_bottom_eq [simp]: "glue (\<bottom> :: ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool) = \<bottom>"
  by (intro ext) auto

lemma glue_eq_rel_eq_self [simp]: "glue ((=) R) = (R :: 'a \<Rightarrow> 'b \<Rightarrow> bool)"
  by (intro ext) auto

lemma glue_sup_eq_glue_sup_glue [simp]: "glue (A \<squnion> B) = glue A \<squnion> glue B"
  supply glue_rel_eq_in_codom_on[simp]
  by (rule ext) (urule in_codom_on_sup_pred_eq_in_codom_on_sup_in_codom_on)

lemma mono_glue: "mono (glue :: (('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool))"
  by auto

lemma dep_bin_rel_glueI:
  fixes \<R> defines [simp]: "D \<equiv> in_codom_on \<R> in_dom"
  assumes "\<And>R. \<R> R \<Longrightarrow> \<exists>A. ({\<Sum>}x : A. B x) R"
  shows "({\<Sum>}x : D. B x) (glue \<R>)"
  using assms by (intro dep_bin_relI) auto


end
