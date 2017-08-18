section \<open>Setup\<close>

theory Dict_Construction
imports Automatic_Refinement.Refine_Util
keywords "declassify" :: thy_decl
begin

definition set_of :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b) set" where
"set_of P = {(x, y). P x y}"

lemma wfP_implies_wf_set_of: "wfP P \<Longrightarrow> wf (set_of P)"
unfolding wfP_def set_of_def .

lemma wf_set_of_implies_wfP: "wf (set_of P) \<Longrightarrow> wfP P"
unfolding wfP_def set_of_def .

lemma wf_simulate_simple:
  assumes "wf r"
  assumes "\<And>x y. (x, y) \<in> r' \<Longrightarrow> (g x, g y) \<in> r"
  shows "wf r'"
using assms
by (metis in_inv_image wf_eq_minimal wf_inv_image)

lemma set_ofI: "P x y \<Longrightarrow> (x, y) \<in> set_of P"
unfolding set_of_def by simp

lemma set_ofD: "(x, y) \<in> set_of P \<Longrightarrow> P x y"
unfolding set_of_def by simp

lemma wf_implies_dom: "wf (set_of R) \<Longrightarrow> All (Wellfounded.accp R)"
apply (rule allI)
apply (rule accp_wfPD)
apply (rule wf_set_of_implies_wfP) .

named_theorems dict_construction_specs

ML_file "dict_construction_util.ML"
ML_file "class_graph.ML"
ML_file "dict_construction.ML"

declare [[code drop: "op \<and>"]]
lemma [code]: "True \<and> p \<longleftrightarrow> p" "False \<and> p \<longleftrightarrow> False" by auto

declare [[code drop: "op \<or>"]]
lemma [code]: "True \<or> p \<longleftrightarrow> True" "False \<or> p \<longleftrightarrow> p" by auto

end