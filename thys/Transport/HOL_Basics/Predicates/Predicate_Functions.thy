\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Functions on Predicates\<close>
theory Predicate_Functions
  imports
    Functions_Base
begin

definition "pred_map f (P :: 'a \<Rightarrow> bool) x \<equiv> P (f x)"

lemma pred_map_eq [simp]: "pred_map f P x = P (f x)"
  unfolding pred_map_def by simp

lemma comp_eq_pred_map [simp]: "P \<circ> f = pred_map f P"
  by (intro ext) simp

consts pred_if :: "bool \<Rightarrow> 'a \<Rightarrow> 'a"

bundle pred_if_syntax begin notation (output) pred_if (infixl \<open>\<longrightarrow>\<close> 50) end
bundle no_pred_if_syntax begin no_notation (output) pred_if (infixl \<open>\<longrightarrow>\<close> 50) end
unbundle pred_if_syntax

definition "pred_if_pred B P x \<equiv> B \<longrightarrow> P x"
adhoc_overloading pred_if pred_if_pred

lemma pred_if_eq_pred_if_pred [simp]:
  assumes "B"
  shows "(pred_if B P) = P"
  unfolding pred_if_pred_def using assms by blast

lemma pred_if_eq_top_if_not_pred [simp]:
  assumes "\<not>B"
  shows "(pred_if B P) = (\<lambda>_. True)"
  unfolding pred_if_pred_def using assms by blast

lemma pred_if_if_impI [intro]:
  assumes "B \<Longrightarrow> P x"
  shows "(pred_if B P) x"
  unfolding pred_if_pred_def using assms by blast

lemma pred_ifE [elim]:
  assumes "(pred_if B P) x"
  obtains "\<not>B" | "B" "P x"
  using assms unfolding pred_if_pred_def by blast

lemma pred_ifD:
  assumes "(pred_if B P) x"
  and "B"
  shows "P x"
  using assms by blast


end