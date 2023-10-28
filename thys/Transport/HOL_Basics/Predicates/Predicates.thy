\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Predicates\<close>
theory Predicates
  imports
    Functions_Base
    Predicates_Order
    Predicates_Lattice
begin

paragraph \<open>Summary\<close>
text \<open>Basic concepts on predicates.\<close>


definition "pred_map f (P :: 'a \<Rightarrow> bool) x \<equiv> P (f x)"

lemma pred_map_eq [simp]: "pred_map f P x = P (f x)"
  unfolding pred_map_def by simp

lemma comp_eq_pred_map [simp]: "P \<circ> f = pred_map f P"
  by (intro ext) simp


end