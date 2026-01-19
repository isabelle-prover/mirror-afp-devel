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

subsubsection \<open>Collection\<close>

consts pred_collect :: "'a \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'd"

open_bundle pred_collect_syntax
begin
no_notation disj  (infixr \<open>|\<close> 30)
syntax "_pred_collect" :: \<open>idt \<Rightarrow> idt \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'c\<close> ("(\<lparr>_ : _ |/ _\<rparr>)")
syntax_consts "_pred_collect" \<rightleftharpoons> pred_collect
translations
  "\<lparr>x : R | P\<rparr>" \<rightleftharpoons> "CONST pred_collect R (\<lambda>x. P)"
end

definition "pred_collect_pred :: ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool \<equiv> (\<sqinter>)"
adhoc_overloading pred_collect \<rightleftharpoons> pred_collect_pred

lemma pred_collectI [intro]:
  assumes "P x"
  and "P x \<Longrightarrow> Q x"
  shows "\<lparr>x : P | Q x\<rparr> x"
  using assms unfolding pred_collect_pred_def by auto

lemma pred_collectE [elim]:
  assumes "\<lparr>x : P | Q x\<rparr> x"
  obtains "P x" "Q x"
  using assms unfolding pred_collect_pred_def by auto

lemma pred_collect_eq_inf: "pred_collect = (\<sqinter>)"
  by (intro ext) auto

subsubsection \<open>Conditional Predicate\<close>

consts pred_if :: "bool \<Rightarrow> 'a \<Rightarrow> 'a"

open_bundle pred_if_syntax
begin
notation pred_if (infixr \<open>\<longrightarrow>\<^sub>p\<close> 50)
end

definition "pred_if_rel B P x \<equiv> B \<longrightarrow> P x"
adhoc_overloading pred_if \<rightleftharpoons> pred_if_rel

lemma pred_if_eq_pred_if_pred:
  assumes "B"
  shows "(B \<longrightarrow>\<^sub>p P) = P"
  unfolding pred_if_rel_def using assms by blast

lemma pred_if_eq_top_if_not_pred:
  assumes "\<not>B"
  shows "(B \<longrightarrow>\<^sub>p P) = \<top>"
  unfolding pred_if_rel_def using assms by fastforce

corollary pred_if_True_eq_self [simp]: "(True \<longrightarrow>\<^sub>p P) = P"
  by (simp add: pred_if_eq_pred_if_pred)
corollary pred_if_False_eq_top [simp]: "(False \<longrightarrow>\<^sub>p P) = \<top>"
  by (simp add: pred_if_eq_top_if_not_pred)

lemma pred_if_if_impI [intro]:
  assumes "B \<Longrightarrow> P x"
  shows "(B \<longrightarrow>\<^sub>p P) x"
   using assms by (cases B) simp_all

lemma pred_if_if_not_pred:
  assumes "\<not>B"
  shows "(B \<longrightarrow>\<^sub>p P) x"
  using assms by simp

lemma pred_ifE [elim]:
  assumes "(B \<longrightarrow>\<^sub>p P) x"
  obtains "\<not>B" | "B" "P x"
  using assms by (cases B) simp

lemma pred_ifD:
  assumes "(B \<longrightarrow>\<^sub>p P) x"
  and "B"
  shows "P x"
  using assms by blast

end