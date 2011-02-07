header {*\isaheader{Implementation of Annotated Lists by 2-3 Finger Trees}*}
theory FTAnnotatedListImpl
imports "../Finger-Trees/FingerTree" AnnotatedListSpec
begin

text {*
  This theory contains the boilerplate code necessary to implement
  the AnnotatedList interface of the Isabelle Collection Framework 
  with 2-3 finger trees.
*}

subsection "Definitions"

definition ft_\<alpha> where
  "ft_\<alpha> \<equiv> FingerTree.toList"
abbreviation (input) ft_invar where 
  "ft_invar \<equiv> \<lambda>_. True"
definition ft_empty where
  "ft_empty \<equiv> FingerTree.empty"
definition ft_isEmpty where
  "ft_isEmpty \<equiv> FingerTree.isEmpty"
definition ft_count where
  "ft_count \<equiv> FingerTree.count"
definition ft_consl where
  "ft_consl e a s = FingerTree.lcons (e,a) s"
definition ft_consr where
  "ft_consr s e a = FingerTree.rcons s (e,a)"
definition ft_head where
  "ft_head \<equiv> FingerTree.head"
definition ft_tail where
  "ft_tail \<equiv> FingerTree.tail"
definition ft_headR where
  "ft_headR \<equiv> FingerTree.headR"
definition ft_tailR where
  "ft_tailR \<equiv> FingerTree.tailR"
definition ft_foldl where
  "ft_foldl \<equiv> FingerTree.foldl"
definition ft_foldr where
  "ft_foldr \<equiv> FingerTree.foldr"
definition ft_app where
  "ft_app \<equiv> FingerTree.app"
definition ft_annot where
  "ft_annot \<equiv> FingerTree.annot"
definition ft_splits where 
  "ft_splits \<equiv> FingerTree.splitTree"

lemmas ft_defs =
  ft_\<alpha>_def
  ft_empty_def
  ft_isEmpty_def
  ft_count_def
  ft_consl_def
  ft_consr_def
  ft_head_def
  ft_tail_def
  ft_headR_def
  ft_tailR_def
  ft_foldl_def
  ft_foldr_def
  ft_app_def
  ft_annot_def
  ft_splits_def

lemma ft_empty_impl: "al_empty ft_\<alpha> ft_invar ft_empty"
  apply unfold_locales
  apply (auto simp add: ft_defs FingerTree.empty_correct)
  done

lemma ft_consl_impl: "al_consl ft_\<alpha> ft_invar ft_consl"
  apply unfold_locales
  apply (auto simp add: ft_defs FingerTree.lcons_correct)
done

lemma ft_consr_impl: "al_consr ft_\<alpha> ft_invar ft_consr"
  apply unfold_locales
  apply (auto simp add: ft_defs FingerTree.rcons_correct)
done

lemma ft_isEmpty_impl: "al_isEmpty ft_\<alpha> ft_invar ft_isEmpty" 
  apply unfold_locales
  apply (auto simp add: ft_defs FingerTree.isEmpty_correct FingerTree.empty_correct)
  done

lemma ft_count_impl: "al_count ft_\<alpha> ft_invar ft_count"
  apply unfold_locales
  apply (auto simp add: ft_defs FingerTree.count_correct)
  done

lemma ft_head_impl: "al_head ft_\<alpha> ft_invar ft_head"
    apply unfold_locales
    apply (auto simp add: ft_defs FingerTree.head_correct FingerTree.empty_correct)
done

lemma ft_tail_impl: "al_tail ft_\<alpha> ft_invar ft_tail"
    apply unfold_locales
    apply (auto simp add: ft_defs FingerTree.tail_correct FingerTree.empty_correct)
done

lemma ft_headR_impl: "al_headR ft_\<alpha> ft_invar ft_headR"
    apply unfold_locales
    apply (auto simp add: ft_defs FingerTree.headR_correct FingerTree.empty_correct)
done

lemma ft_tailR_impl: "al_tailR ft_\<alpha> ft_invar ft_tailR"
    apply unfold_locales
    apply (auto simp add: ft_defs FingerTree.tailR_correct FingerTree.empty_correct)
    done

lemma ft_foldl_impl: "al_foldl ft_\<alpha> ft_invar ft_foldl"
  apply unfold_locales
  apply (auto simp add: ft_defs FingerTree.foldl_correct)
  done 

lemma ft_foldr_impl: "al_foldr ft_\<alpha> ft_invar ft_foldr"
  apply unfold_locales
  apply (auto simp add: ft_defs FingerTree.foldr_correct)
  done 

lemma ft_app_impl: "al_app ft_\<alpha> ft_invar ft_app"
  apply unfold_locales
  apply (auto simp add: ft_defs FingerTree.app_correct)
  done

lemma ft_annot_impl: "al_annot ft_\<alpha> ft_invar ft_annot"
  apply unfold_locales 
  apply (auto simp add: ft_defs FingerTree.annot_correct)
  done

lemma ft_splits_impl: "al_splits ft_\<alpha> ft_invar ft_splits"
  apply unfold_locales
  apply (unfold ft_defs)
  apply (simp only: FingerTree.annot_correct[symmetric])
  apply (frule (3) FingerTree.splitTree_correct(1))
  apply (frule (3) FingerTree.splitTree_correct(2))
  apply (frule (3) FingerTree.splitTree_correct(3))
  apply (simp only: FingerTree.annot_correct[symmetric])
  apply simp
  done

subsection "Interpretations"

interpretation ft: al_empty ft_\<alpha> ft_invar ft_empty using ft_empty_impl .
interpretation ft: al_isEmpty ft_\<alpha> ft_invar ft_isEmpty using ft_isEmpty_impl .
interpretation ft: al_count ft_\<alpha> ft_invar ft_count using ft_count_impl .
interpretation ft: al_consl ft_\<alpha> ft_invar ft_consl using ft_consl_impl .
interpretation ft: al_consr ft_\<alpha> ft_invar ft_consr using ft_consr_impl . 
interpretation ft: al_head ft_\<alpha> ft_invar ft_head using ft_head_impl .
interpretation ft: al_tail ft_\<alpha> ft_invar ft_tail using ft_tail_impl .
interpretation ft: al_headR ft_\<alpha> ft_invar ft_headR using ft_headR_impl .
interpretation ft: al_tailR ft_\<alpha> ft_invar ft_tailR using ft_tailR_impl .
interpretation ft: al_foldl ft_\<alpha> ft_invar ft_foldl using ft_foldl_impl .
interpretation ft: al_foldr ft_\<alpha> ft_invar ft_foldr using ft_foldr_impl .
interpretation ft: al_app ft_\<alpha> ft_invar ft_app using ft_app_impl . 
interpretation ft: al_annot ft_\<alpha> ft_invar ft_annot using ft_annot_impl .
interpretation ft: al_splits ft_\<alpha> ft_invar ft_splits using ft_splits_impl .

lemmas ft_correct =
  ft.empty_correct
  ft.isEmpty_correct
  ft.count_correct
  ft.consl_correct
  ft.consr_correct
  ft.head_correct
  ft.tail_correct
  ft.headR_correct
  ft.tailR_correct
  ft.foldl_correct
  ft.foldr_correct
  ft.app_correct
  ft.annot_correct
  ft.splits_correct

subsubsection "Record Based Implementation"

definition "ft_ops = \<lparr>
  alist_op_\<alpha> = ft_\<alpha>,
  alist_op_invar = ft_invar,
  alist_op_empty = ft_empty,
  alist_op_isEmpty = ft_isEmpty,
  alist_op_count = ft_count,
  alist_op_consl = ft_consl,
  alist_op_consr = ft_consr,
  alist_op_head = ft_head,
  alist_op_tail = ft_tail,
  alist_op_headR = ft_headR,
  alist_op_tailR = ft_tailR,
  alist_op_app = ft_app,
  alist_op_annot = ft_annot,
  alist_op_splits = ft_splits
  \<rparr>"

interpretation ftr!: StdAL ft_ops
  apply (rule StdAL.intro)
  apply (simp_all add: ft_ops_def)
  apply unfold_locales
  done

lemma ft_ops_unfold[code_unfold]:
  "alist_op_\<alpha> ft_ops = ft_\<alpha>"
  "alist_op_invar ft_ops = ft_invar" 
  "alist_op_empty ft_ops = ft_empty" 
  "alist_op_isEmpty ft_ops = ft_isEmpty" 
  "alist_op_count ft_ops = ft_count" 
  "alist_op_consl ft_ops = ft_consl"
  "alist_op_consr ft_ops = ft_consr" 
  "alist_op_head ft_ops = ft_head" 
  "alist_op_tail ft_ops = ft_tail"
  "alist_op_headR ft_ops = ft_headR" 
  "alist_op_tailR ft_ops = ft_tailR"
  "alist_op_app ft_ops = ft_app" 
  "alist_op_annot ft_ops = ft_annot"
  "alist_op_splits ft_ops = ft_splits"
  by (auto simp add: ft_ops_def)

 interpretation ftr!: al_foldl "(alist_op_\<alpha> ft_ops)" "(alist_op_invar ft_ops)" ft_foldl
    using ft_foldl_impl[folded ft_ops_unfold] .
 interpretation ftr!: al_foldr "(alist_op_\<alpha> ft_ops)" "(alist_op_invar ft_ops)" ft_foldr
    using ft_foldr_impl[folded ft_ops_unfold] .

lemmas ft_impl = 
  ft_empty_impl
  ft_isEmpty_impl
  ft_count_impl
  ft_consl_impl
  ft_consr_impl
  ft_head_impl
  ft_tail_impl
  ft_headR_impl
  ft_tailR_impl
  ft_foldl_impl
  ft_foldr_impl
  ft_app_impl
  ft_annot_impl
  ft_splits_impl

subsection "Code Generation"

export_code 
  ft_empty
  ft_isEmpty
  ft_count
  ft_consl
  ft_head
  ft_tail
  ft_headR
  ft_tailR
  ft_foldl
  ft_foldr
  ft_app
  ft_splits
  in SML
  module_name FT

end
