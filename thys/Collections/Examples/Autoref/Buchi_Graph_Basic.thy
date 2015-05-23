theory Buchi_Graph_Basic
imports Main "../../../Automatic_Refinement/Lib/Refine_Lib"
begin

text {* Specification of a reachable accepting cycle: *}
definition "has_acc_cycle E A v0 \<equiv> \<exists>v\<in>A. (v0,v)\<in>E\<^sup>* \<and> (v,v)\<in>E\<^sup>+"

text {* Specification of witness for accepting cycle *}
definition "is_acc_cycle E A v0 v r c 
  \<equiv> v\<in>A \<and> path E v0 r v \<and> path E v c v \<and> c\<noteq>[]"

text {* Specification is compatible with existence of accepting cycle *}
lemma is_acc_cycle_eq:
  "has_acc_cycle E A v0 \<longleftrightarrow> (\<exists>v r c. is_acc_cycle E A v0 v r c)"
  unfolding has_acc_cycle_def is_acc_cycle_def
  by (auto elim!: rtrancl_is_path trancl_is_path
    intro: path_is_rtrancl path_is_trancl)

end
