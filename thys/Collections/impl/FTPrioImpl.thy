header {*\isaheader{Implementation of Priority Queues by Finger Trees}*}
theory FTPrioImpl
imports FTAnnotatedListImpl 
  "../gen_algo/PrioByAnnotatedList"
begin
(*@impl Prio
  @type ('a,'p::linorder) alprioi
  @abbrv alprioi
  Priority queues based on 2-3 finger trees.
*)

type_synonym ('a,'p) alprioi = "(unit, ('a, 'p) Prio) FingerTree"

subsection "Definitions"
definition alprioi_\<alpha> :: "('a,'p::linorder) alprioi \<Rightarrow> ('a\<times>'p) multiset" where
  "alprioi_\<alpha> = alprio_\<alpha> ft_\<alpha>"
definition alprioi_invar where
  "alprioi_invar = alprio_invar ft_\<alpha> ft_invar"
definition alprioi_empty 
  :: "unit \<Rightarrow> (unit,('a,'b::linorder) Prio) FingerTree" where
  "alprioi_empty = alprio_empty ft_empty"
definition alprioi_isEmpty where
  "alprioi_isEmpty \<equiv> alprio_isEmpty ft_isEmpty"
definition alprioi_insert :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> (unit,('a,'b::linorder) Prio) FingerTree" where
  "alprioi_insert = alprio_insert ft_consl"
definition alprioi_find where
  "alprioi_find = alprio_find ft_annot"
definition alprioi_delete where
  "alprioi_delete = alprio_delete ft_splits ft_annot ft_app"
definition alprioi_meld where
  "alprioi_meld = alprio_meld ft_app"

definition "alprioi_ops == \<lparr>
  prio_op_\<alpha> = alprioi_\<alpha>,
  prio_op_invar = alprioi_invar,
  prio_op_empty = alprioi_empty,
  prio_op_isEmpty = alprioi_isEmpty,
  prio_op_insert = alprioi_insert,
  prio_op_find = alprioi_find,
  prio_op_delete = alprioi_delete,
  prio_op_meld = alprioi_meld
\<rparr>"

subsection "Correctness"
lemmas alprioi_defs =
alprioi_invar_def
alprioi_\<alpha>_def
alprioi_empty_def
alprioi_isEmpty_def
alprioi_insert_def
alprioi_find_def
alprioi_delete_def
alprioi_meld_def

lemmas alprioi_empty_impl = alprio_empty_correct[OF ft_empty_impl, folded alprioi_defs]
lemmas alprioi_isEmpty_impl = alprio_isEmpty_correct[OF ft_isEmpty_impl, folded alprioi_defs]
lemmas alprioi_insert_impl = alprio_insert_correct[OF ft_consl_impl, folded alprioi_defs]
lemmas alprioi_find_impl = alprio_find_correct[OF ft_annot_impl, folded alprioi_defs]
lemmas alprioi_delete_impl = alprio_delete_correct[OF ft_annot_impl ft_splits_impl ft_app_impl, folded alprioi_defs]
lemmas alprioi_meld_impl = alprio_meld_correct[OF ft_app_impl, folded alprioi_defs]

lemmas alprioi_impl =
  alprioi_empty_impl
  alprioi_isEmpty_impl
  alprioi_insert_impl
  alprioi_find_impl
  alprioi_delete_impl
  alprioi_meld_impl

interpretation alprioi: prio_empty alprioi_\<alpha> alprioi_invar alprioi_empty 
  by (rule alprioi_impl)
interpretation alprioi: prio_isEmpty alprioi_\<alpha> alprioi_invar alprioi_isEmpty 
  by (rule alprioi_impl)
interpretation alprioi: prio_insert alprioi_\<alpha> alprioi_invar alprioi_insert
  by (rule alprioi_impl)
interpretation alprioi: prio_find alprioi_\<alpha> alprioi_invar alprioi_find
  by (rule alprioi_impl)
interpretation alprioi: prio_delete alprioi_\<alpha> alprioi_invar alprioi_find alprioi_delete
  by (rule alprioi_impl)
interpretation alprioi: prio_meld alprioi_\<alpha> alprioi_invar alprioi_meld
  by (rule alprioi_impl)

lemmas alprioi_correct = 
  alprioi.empty_correct
  alprioi.isEmpty_correct
  alprioi.insert_correct
  alprioi.meld_correct
  alprioi.find_correct
  alprioi.delete_correct

subsubsection "Record Based Interface"
interpretation alprioir: StdPrio alprioi_ops
  apply (unfold alprioi_ops_def)
  apply intro_locales
  apply (simp_all add: alprioi_impl alprioi_delete_impl[unfolded prio_delete_def])
  done

subsection "Code Generation"
-- "Unfold record definition for code generation"
lemma alprioi_ops_unfold [code_unfold]:  
  "prio_op_\<alpha> alprioi_ops = alprioi_\<alpha>"
  "prio_op_invar alprioi_ops = alprioi_invar"
  "prio_op_empty alprioi_ops = alprioi_empty"
  "prio_op_isEmpty alprioi_ops = alprioi_isEmpty"
  "prio_op_insert alprioi_ops = alprioi_insert"
  "prio_op_find alprioi_ops = alprioi_find"
  "prio_op_delete alprioi_ops = alprioi_delete"
  "prio_op_meld alprioi_ops = alprioi_meld"
  by (auto simp add: alprioi_ops_def)

export_code 
  alprioi_empty
  alprioi_isEmpty
  alprioi_insert
  alprioi_find
  alprioi_delete
  alprioi_meld
  in SML
  module_name ALPRIOI

end

