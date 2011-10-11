header {*\isaheader{Implementation of Priority Queues by Binomial Heap}*}

theory BinoPrioImpl
imports "../Binomial-Heaps/BinomialHeap" PrioSpec
begin

text {* In this theory, we implement priority queues by binomial heaps. *}

subsection "Definitions"
definition bino_\<alpha> where "bino_\<alpha> q \<equiv> BinomialHeap.to_mset q"
definition bino_insert where "bino_insert \<equiv> BinomialHeap.insert"
abbreviation (input) bino_invar where "bino_invar \<equiv> \<lambda>_. True"
definition bino_find where "bino_find \<equiv> BinomialHeap.findMin"
definition bino_delete where "bino_delete \<equiv> BinomialHeap.deleteMin"
definition bino_meld where "bino_meld \<equiv> BinomialHeap.meld"
definition bino_empty where "bino_empty \<equiv> BinomialHeap.empty"
definition bino_isEmpty where "bino_isEmpty = BinomialHeap.isEmpty"

definition "bino_ops == \<lparr>
  prio_op_\<alpha> = bino_\<alpha>,
  prio_op_invar = bino_invar,
  prio_op_empty = bino_empty,
  prio_op_isEmpty = bino_isEmpty,
  prio_op_insert = bino_insert,
  prio_op_find = bino_find,
  prio_op_delete = bino_delete,
  prio_op_meld = bino_meld
\<rparr>"

lemmas bino_defs =
  bino_\<alpha>_def
  bino_insert_def
  bino_find_def
  bino_delete_def
  bino_meld_def
  bino_empty_def
  bino_isEmpty_def

subsection "Correctness"

theorem bino_empty_impl: "prio_empty bino_\<alpha> bino_invar bino_empty"
  by (unfold_locales, auto simp add: bino_defs)

theorem bino_isEmpty_impl: "prio_isEmpty bino_\<alpha> bino_invar bino_isEmpty"
  by unfold_locales 
     (simp add: bino_defs BinomialHeap.isEmpty_correct BinomialHeap.empty_correct)

theorem bino_find_impl: "prio_find bino_\<alpha> bino_invar bino_find"
  apply unfold_locales
  apply (simp add: bino_defs BinomialHeap.empty_correct BinomialHeap.findMin_correct)
  done

lemma bino_insert_impl: "prio_insert bino_\<alpha> bino_invar bino_insert"
  apply(unfold_locales)
  apply(unfold bino_defs) 
  apply (simp_all add: BinomialHeap.insert_correct)
  done

lemma bino_meld_impl: "prio_meld bino_\<alpha> bino_invar bino_meld"
  apply(unfold_locales)
  apply(unfold bino_defs)
  apply(simp_all add: BinomialHeap.meld_correct)
  done
      
lemma bino_delete_impl: 
  "prio_delete bino_\<alpha> bino_invar bino_find bino_delete"
  apply intro_locales
  apply (rule bino_find_impl)
  apply(unfold_locales)
  apply(simp_all add: bino_defs BinomialHeap.empty_correct BinomialHeap.deleteMin_correct)
done 

interpretation bino: prio_empty bino_\<alpha> bino_invar bino_empty 
using bino_empty_impl .
interpretation bino: prio_isEmpty bino_\<alpha> bino_invar bino_isEmpty
using bino_isEmpty_impl .
interpretation bino: prio_insert bino_\<alpha> bino_invar bino_insert
using bino_insert_impl .
interpretation bino: prio_delete bino_\<alpha> bino_invar bino_find bino_delete
using bino_delete_impl .
interpretation bino: prio_meld bino_\<alpha> bino_invar bino_meld
using bino_meld_impl .

interpretation binos: StdPrio bino_ops
  apply (unfold bino_ops_def)
  apply intro_locales
  apply simp_all
  apply unfold_locales
  using prio_delete.delete_correct[OF bino_delete_impl]
  apply auto
  done

lemmas bino_correct = 
  bino.empty_correct
  bino.isEmpty_correct
  bino.insert_correct
  bino.meld_correct
  bino.find_correct
  bino.delete_correct

subsection "Code Generation"
text {* Unfold record definition for code generation*}
lemma [code_unfold]:
  "prio_op_empty bino_ops = bino_empty"
  "prio_op_isEmpty bino_ops = bino_isEmpty"
  "prio_op_insert bino_ops = bino_insert"
  "prio_op_find bino_ops = bino_find"
  "prio_op_delete bino_ops = bino_delete"
  "prio_op_meld bino_ops = bino_meld"
  by (auto simp add: bino_ops_def)


export_code 
  bino_empty
  bino_isEmpty
  bino_insert
  bino_find
  bino_delete
  bino_meld
  in SML
  module_name Bino
  file -

end
