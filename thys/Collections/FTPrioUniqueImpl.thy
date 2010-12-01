header {*\isaheader{Implementation of Unique Priority Queues by Finger Trees}*}
theory FTPrioUniqueImpl
imports 
  FTAnnotatedListImpl 
  AnnotatedListGAPrioUniqueImpl 
begin
text {* Instantiation of adapter *}

subsection "Definitions"

definition aluprioi_\<alpha> where
  "aluprioi_\<alpha> = aluprio_\<alpha> ft_\<alpha>"
definition aluprioi_invar where
  "aluprioi_invar = aluprio_invar ft_\<alpha> ft_invar"
definition aluprioi_empty :: "(unit,('a::linorder,'b::linorder) LP) FingerTree" where
  "aluprioi_empty = aluprio_empty ft_empty"
definition aluprioi_isEmpty where
  "aluprioi_isEmpty \<equiv> aluprio_isEmpty ft_isEmpty"
definition aluprioi_insert :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> (unit,('a::linorder,'b::linorder) LP) FingerTree" where
  "aluprioi_insert = aluprio_insert ft_splits ft_annot ft_isEmpty ft_app ft_consr"
definition aluprioi_pop where
  "aluprioi_pop = aluprio_pop ft_splits ft_annot ft_app"
definition aluprioi_prio where
  "aluprioi_prio = aluprio_prio ft_splits ft_annot ft_isEmpty"

definition "aluprioi_ops == \<lparr>
  upr_\<alpha> = aluprioi_\<alpha>,
  upr_invar = aluprioi_invar,
  upr_empty = aluprioi_empty,
  upr_isEmpty = aluprioi_isEmpty,
  upr_insert = aluprioi_insert,
  upr_pop = aluprioi_pop,
  upr_prio = aluprioi_prio
\<rparr>"

lemmas aluprioi_defs =
aluprioi_invar_def
aluprioi_\<alpha>_def
aluprioi_empty_def
aluprioi_isEmpty_def
aluprioi_insert_def
aluprioi_pop_def
aluprioi_prio_def


subsection "Correctness"

lemmas aluprioi_finite_impl = aluprio_finite_correct[of ft_\<alpha> ft_invar, folded aluprioi_defs]
lemmas aluprioi_empty_impl = aluprio_empty_correct[OF ft_empty_impl, folded aluprioi_defs]
lemmas aluprioi_isEmpty_impl = aluprio_isEmpty_correct[OF ft_isEmpty_impl, folded aluprioi_defs]
lemmas aluprioi_insert_impl = aluprio_insert_correct[
  OF 
    ft_splits_impl ft_annot_impl ft_isEmpty_impl 
    ft_app_impl ft_consr_impl, 
  folded aluprioi_defs]
lemmas aluprioi_pop_impl = aluprio_pop_correct[OF ft_splits_impl ft_annot_impl ft_app_impl, folded aluprioi_defs]
lemmas aluprioi_prio_impl = aluprio_prio_correct[OF ft_splits_impl ft_annot_impl ft_isEmpty_impl, folded aluprioi_defs]

lemmas aluprioi_impl =
  aluprioi_finite_impl
  aluprioi_empty_impl
  aluprioi_isEmpty_impl
  aluprioi_insert_impl
  aluprioi_pop_impl
  aluprioi_prio_impl

interpretation aluprioi: uprio_finite aluprioi_\<alpha> aluprioi_invar 
  by (rule aluprioi_impl)
interpretation aluprioi: uprio_empty aluprioi_\<alpha> aluprioi_invar aluprioi_empty 
  by (rule aluprioi_impl)
interpretation aluprioi: uprio_isEmpty aluprioi_\<alpha> aluprioi_invar aluprioi_isEmpty 
  by(auto simp add:aluprioi_impl)
interpretation aluprioi: uprio_insert aluprioi_\<alpha> aluprioi_invar aluprioi_insert 
  by (rule aluprioi_impl)
interpretation aluprioi: uprio_pop aluprioi_\<alpha> aluprioi_invar aluprioi_pop 
  by (rule aluprioi_impl)
interpretation aluprioi: uprio_prio aluprioi_\<alpha> aluprioi_invar aluprioi_prio
  by (rule aluprioi_impl)

lemmas aluprioi_correct = 
  aluprioi.finite_correct
  aluprioi.empty_correct
  aluprioi.isEmpty_correct
  aluprioi.insert_correct
  aluprioi.pop_correct
  aluprioi.prio_correct

subsubsection "Record Based Interface"
interpretation aluprioir: StdUprio aluprioi_ops
  apply intro_locales
  apply (unfold aluprioi_ops_def)
  apply (simp_all add: aluprioi_impl)
  done

lemma aluprioi_ops_unfold [code_unfold]:
  "upr_empty aluprioi_ops = aluprioi_empty"
  "upr_isEmpty aluprioi_ops = aluprioi_isEmpty"
  "upr_insert aluprioi_ops = aluprioi_insert"
  "upr_pop aluprioi_ops = aluprioi_pop"
  "upr_prio aluprioi_ops = aluprioi_prio"  
  by (auto simp add: aluprioi_ops_def)

subsection "Code Generation"

export_code 
  aluprioi_empty
  aluprioi_isEmpty
  aluprioi_insert
  aluprioi_pop
  aluprioi_prio
  in SML
  module_name ALUPRIOI

end

