(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header {* \isaheader{Fifo Queue by Pair of Lists} *}
theory Fifo
imports ListGA
begin
text_raw {*\label{thy:Fifo}*}

text {*
  A fifo-queue is implemented by a pair of two lists (stacks). 
  New elements are pushed on the first stack, and elements are popped from 
  the second stack. If the second stack is empty, the first stack is reversed
  and replaces the second stack.

  If list reversal is implemented efficiently (what is the case in Isabelle/HOL, 
  cf @{thm [source] List.rev_conv_fold})
  the amortized time per buffer operation is constant.

  Moreover, this fifo implementation also supports efficient push and pop operations.
*}

subsection {* Definitions *}
type_synonym 'a fifo = "'a list \<times> 'a list"

  -- "The empty fifo"
definition fifo_empty :: "'a fifo" where "fifo_empty == ([],[])"
  -- "True, iff the fifo is empty"
definition fifo_isEmpty :: "'a fifo \<Rightarrow> bool" where "fifo_isEmpty F == F=([],[])"
  -- "Add an element to the fifo"
definition fifo_enqueue :: "'a \<Rightarrow> 'a fifo \<Rightarrow> 'a fifo" 
  where "fifo_enqueue a F == (a#fst F, snd F)"
  -- "Get an element from the fifo"
definition fifo_dequeue :: "'a fifo \<Rightarrow> ('a \<times> 'a fifo)" where 
  "fifo_dequeue F ==
    case snd F of
      (a#l) \<Rightarrow> (a, (fst F, l)) |
      [] \<Rightarrow> let rp=rev (fst F) in
        (hd rp, ([], tl rp))
"

  -- "Stack view on fifo: Pop"
abbreviation "fifo_pop == fifo_dequeue"
  -- "Stack view on fifo: Push"
definition fifo_push :: "'a \<Rightarrow> 'a fifo \<Rightarrow> 'a fifo"
  where "fifo_push x F == case F of (e,d) \<Rightarrow> (e,x#d)"

  -- "Abstraction of the fifo to a list. The next element to be got is at 
      the head of the list, and new elements are appended at the end of the list"
definition fifo_\<alpha> :: "'a fifo \<Rightarrow> 'a list" where "fifo_\<alpha> F == snd F @ rev (fst F)"

  -- "This fifo implementation has no invariants, any pair of lists is a valid fifo"
definition [simp, intro!]: "fifo_invar x = True"

subsection "Correctness"

lemma fifo_empty_impl: "list_empty fifo_\<alpha> fifo_invar fifo_empty"
  apply (unfold_locales)
  by (auto simp add: fifo_\<alpha>_def fifo_empty_def)

lemma fifo_isEmpty_impl: "list_isEmpty fifo_\<alpha> fifo_invar fifo_isEmpty"
  apply (unfold_locales)
  by (case_tac s) (auto simp add: fifo_isEmpty_def fifo_\<alpha>_def)

lemma fifo_enqueue_impl: "list_enqueue fifo_\<alpha> fifo_invar fifo_enqueue"
  apply (unfold_locales)
  by (auto simp add: fifo_enqueue_def fifo_\<alpha>_def)

lemma fifo_dequeue_impl: "list_dequeue fifo_\<alpha> fifo_invar fifo_dequeue"
  apply (unfold_locales)
  apply (case_tac s)
  apply (case_tac b)
  apply (auto simp add: fifo_dequeue_def fifo_\<alpha>_def Let_def) [2]
  apply (case_tac s)
  apply (case_tac "b")
  apply (auto simp add: fifo_dequeue_def fifo_\<alpha>_def Let_def)
  done
  
interpretation fifo: list_empty fifo_\<alpha> fifo_invar fifo_empty using fifo_empty_impl .
interpretation fifo: list_isEmpty fifo_\<alpha> fifo_invar fifo_isEmpty using fifo_isEmpty_impl .
interpretation fifo: list_enqueue fifo_\<alpha> fifo_invar fifo_enqueue using fifo_enqueue_impl .
interpretation fifo: list_dequeue fifo_\<alpha> fifo_invar fifo_dequeue using fifo_dequeue_impl .

lemma fifo_pop_impl: "list_pop fifo_\<alpha> fifo_invar fifo_pop"
  by unfold_locales

lemma fifo_push_impl: "list_push fifo_\<alpha> fifo_invar fifo_push"
  apply unfold_locales
  by (auto simp add: fifo_push_def fifo_\<alpha>_def)

interpretation fifo: list_pop fifo_\<alpha> fifo_invar fifo_pop using fifo_pop_impl .
interpretation fifo: list_push fifo_\<alpha> fifo_invar fifo_push using fifo_push_impl .

lemmas fifo_correct = 
  fifo.empty_correct(1) 
  fifo.isEmpty_correct[simplified] 
  fifo.enqueue_correct(1)[simplified]
  fifo.dequeue_correct(1,2)[simplified]
  fifo.push_correct(1)[simplified]
  fifo.pop_correct(1,2)[simplified]

subsection "Code Generation"
export_code
  fifo_empty fifo_isEmpty fifo_enqueue fifo_dequeue fifo_push fifo_pop
  in SML 
  module_name Fifo
  file - (*"Fifo.ML"*)

end
