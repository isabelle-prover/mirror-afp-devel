\<^marker>\<open>creator "Kevin Kappelmann"\<close>
subsection \<open>Graph\<close>
theory Binary_Relations_Graph
  imports
    Functions_Monotone
    Restricted_Equality
begin

paragraph \<open>Summary\<close>
text \<open>Basic functions on binary relations.\<close>

subsubsection \<open>Graph\<close>

consts Graph_on :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"

definition "Graph_on_pred P f \<equiv> \<lambda>x y. P x \<and> y = f x"
adhoc_overloading Graph_on \<rightleftharpoons> Graph_on_pred

lemma Graph_onI:
  assumes "P x"
  shows "Graph_on P f x (f x)"
  using assms unfolding Graph_on_pred_def by auto

lemma Graph_on_if_eq_if_pred [intro]:
  assumes "P x"
  and "y = f x"
  shows "Graph_on P f x y"
  using assms by (auto intro: Graph_onI)

lemma Graph_onE [elim]:
  assumes "Graph_on P f x y"
  obtains "P x" "y = f x"
  using assms unfolding Graph_on_pred_def by auto

lemma in_dom_Graph_on_eq [simp]: "in_dom (Graph_on P f) = P"
  by auto

lemma in_codom_on_Graph_on_eq_has_inverse_on [simp]:
  "in_codom_on P (Graph_on Q f) = has_inverse_on (P \<sqinter> Q) f"
  by fastforce

lemma in_codom_Graph_on_eq_has_inverse_on [simp]: "in_codom (Graph_on P f) = has_inverse_on P f"
  by (urule in_codom_on_Graph_on_eq_has_inverse_on)

lemma mono_Graph_on: "mono Graph_on" by fastforce

lemma Graph_on_eq_Graph_on_if_mono_eq:
  assumes "((P :: _ \<Rightarrow> bool) \<Rrightarrow> (=)) f g"
  shows "Graph_on P f = Graph_on P g"
  using assms by fastforce

lemma Graph_on_id_eq_eq_restrict [simp]: "Graph_on P id = (=\<^bsub>P\<^esub>)"
  by fastforce

consts Graph :: "'a \<Rightarrow> 'b"

definition "Graph_fun \<equiv> Graph_on (\<top> :: 'a \<Rightarrow> bool)"
adhoc_overloading Graph \<rightleftharpoons> Graph_fun

lemma Graph_eq_Graph_on: "Graph = Graph_on \<top>"
  unfolding Graph_fun_def ..

lemma Graph_eq_Graph_on_uhint [uhint]:
  assumes "P \<equiv> (\<top> :: 'a \<Rightarrow> bool)"
  shows "Graph :: ('a \<Rightarrow> _) \<Rightarrow> _ \<equiv> Graph_on P"
  using assms by (simp add: Graph_eq_Graph_on)

lemma GraphI [intro]:
  assumes "y = f x"
  shows "Graph f x y"
  by (urule Graph_on_if_eq_if_pred) (use assms in simp_all)

lemma GraphD [dest]:
  assumes "Graph f x y"
  shows "y = f x"
  using assms by (urule (e) Graph_onE)

lemma in_dom_Graph_eq [simp]: "in_dom (Graph f) = \<top>"
  by (urule in_dom_Graph_on_eq)

lemma in_codom_on_Graph_eq_has_inverse_on [simp]: "in_codom_on P (Graph f) = has_inverse_on P f"
  by (urule in_codom_on_Graph_on_eq_has_inverse_on)

lemma in_codom_Graph_eq_has_inverse [simp]: "in_codom (Graph f) = has_inverse f"
  by (urule in_codom_Graph_on_eq_has_inverse_on)

lemma Graph_eq_eq_comp: "Graph f = (=) \<circ> f"
  by (intro ext) auto

lemma Graph_id_eq_eq [simp]: "Graph id = (=)"
  by (urule Graph_on_id_eq_eq_restrict)


end