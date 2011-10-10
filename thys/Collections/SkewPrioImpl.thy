header {*\isaheader{Implementation of Priority Queues by Skew Binomial Heaps}*}

theory SkewPrioImpl
imports "../Binomial-Heaps/SkewBinomialHeap" "PrioSpec"
begin

text {* In this theory, we implement priority queues by skew binomial heaps. *}

subsection "Definitions"
definition skew_\<alpha> where "skew_\<alpha> q \<equiv> SkewBinomialHeap.to_mset q"
definition skew_insert where "skew_insert \<equiv> SkewBinomialHeap.insert"
abbreviation (input) skew_invar where "skew_invar \<equiv> \<lambda>_. True"
definition skew_find where "skew_find \<equiv> SkewBinomialHeap.findMin"
definition skew_delete where "skew_delete \<equiv> SkewBinomialHeap.deleteMin"
definition skew_meld where "skew_meld \<equiv> SkewBinomialHeap.meld"
definition skew_empty where "skew_empty \<equiv> SkewBinomialHeap.empty"
definition skew_isEmpty where "skew_isEmpty = SkewBinomialHeap.isEmpty"

definition "skew_ops == \<lparr>
  prio_op_\<alpha> = skew_\<alpha>,
  prio_op_invar = skew_invar,
  prio_op_empty = skew_empty,
  prio_op_isEmpty = skew_isEmpty,
  prio_op_insert = skew_insert,
  prio_op_find = skew_find,
  prio_op_delete = skew_delete,
  prio_op_meld = skew_meld
\<rparr>"

lemmas skew_defs =
  skew_\<alpha>_def
  skew_insert_def
  skew_find_def
  skew_delete_def
  skew_meld_def
  skew_empty_def
  skew_isEmpty_def

subsection "Correctness"

theorem skew_empty_impl: "prio_empty skew_\<alpha> skew_invar skew_empty"
  by (unfold_locales, auto simp add: skew_defs)

theorem skew_isEmpty_impl: "prio_isEmpty skew_\<alpha> skew_invar skew_isEmpty"
  by unfold_locales 
     (simp add: skew_defs SkewBinomialHeap.isEmpty_correct SkewBinomialHeap.empty_correct)

theorem skew_find_impl: "prio_find skew_\<alpha> skew_invar skew_find"
  apply unfold_locales
  apply (simp add: skew_defs SkewBinomialHeap.empty_correct SkewBinomialHeap.findMin_correct)
  done

lemma skew_insert_impl: "prio_insert skew_\<alpha> skew_invar skew_insert"
  apply(unfold_locales)
  apply(unfold skew_defs) 
  apply (simp_all add: SkewBinomialHeap.insert_correct)
  done

lemma skew_meld_impl: "prio_meld skew_\<alpha> skew_invar skew_meld"
  apply(unfold_locales)
  apply(unfold skew_defs)
  apply(simp_all add: SkewBinomialHeap.meld_correct)
  done
      
lemma skew_delete_impl: 
  "prio_delete skew_\<alpha> skew_invar skew_find skew_delete"
  apply intro_locales
  apply (rule skew_find_impl)
  apply(unfold_locales)
  apply(simp_all add: skew_defs SkewBinomialHeap.empty_correct SkewBinomialHeap.deleteMin_correct)
done 

interpretation skew: prio_empty skew_\<alpha> skew_invar skew_empty 
using skew_empty_impl .
interpretation skew: prio_isEmpty skew_\<alpha> skew_invar skew_isEmpty
using skew_isEmpty_impl .
interpretation skew: prio_insert skew_\<alpha> skew_invar skew_insert
using skew_insert_impl .
interpretation skew: prio_delete skew_\<alpha> skew_invar skew_find skew_delete
using skew_delete_impl .
interpretation skew: prio_meld skew_\<alpha> skew_invar skew_meld
using skew_meld_impl .

interpretation skews: StdPrio skew_ops
  apply (unfold skew_ops_def)
  apply intro_locales
  apply simp_all
  apply unfold_locales
  using prio_delete.delete_correct[OF skew_delete_impl]
  apply auto
  done

lemmas skew_correct = 
  skew.empty_correct
  skew.isEmpty_correct
  skew.insert_correct
  skew.meld_correct
  skew.find_correct
  skew.delete_correct

subsection "Code Generation"
text {* Unfold record definition for code generation*}
lemma [code_unfold]:
  "prio_op_empty skew_ops = skew_empty"
  "prio_op_isEmpty skew_ops = skew_isEmpty"
  "prio_op_insert skew_ops = skew_insert"
  "prio_op_find skew_ops = skew_find"
  "prio_op_delete skew_ops = skew_delete"
  "prio_op_meld skew_ops = skew_meld"
  by (auto simp add: skew_ops_def)


export_code 
  skew_empty
  skew_isEmpty
  skew_insert
  skew_find
  skew_delete
  skew_meld
  in SML
  module_name Skew
  file -

end
