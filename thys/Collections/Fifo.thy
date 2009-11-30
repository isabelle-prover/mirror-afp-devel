(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header {* Fifo Queue by Pair of Lists *}
theory Fifo
imports Main
begin
text_raw {*\label{thy:Fifo}*}

text {*
  A fifo-queue is implemented by a pair of two lists (stacks). 
  New elements are pushed on the first stack, and elements are popped from 
  the second stack. If the second stack is empty, the first stack is reversed
  and replaces the second stack.

  If list reversal is implemented efficiently (what is the case in Isabelle/HOL, 
  cf @{thm [source] List.rev_foldl_cons})
  the amortized time per buffer operation is constant.
*}

subsection {* Definitions *}
types 'a fifo = "'a list \<times> 'a list"

  -- "The empty fifo"
definition fifo_empty :: "'a fifo" where "fifo_empty == ([],[])"
  -- "True, iff the fifo is empty"
definition fifo_isEmpty :: "'a fifo \<Rightarrow> bool" where "fifo_isEmpty F == F=([],[])"
  -- "Add an element to the fifo"
definition fifo_put :: "'a \<Rightarrow> 'a fifo \<Rightarrow> 'a fifo" 
  where "fifo_put a F == (a#fst F, snd F)"
  -- "Get an element from the fifo"
definition fifo_get :: "'a fifo \<Rightarrow> ('a \<times> 'a fifo)" where 
  "fifo_get F ==
    case snd F of
      (a#l) \<Rightarrow> (a, (fst F, l)) |
      [] \<Rightarrow> let rp=rev (fst F) in
        (hd rp, ([], tl rp))
"

  -- "Abstraction of the fifo to a list. The next element to be got is at 
      the head of the list, and new elements are appended at the end of the list"
definition fifo_\<alpha> :: "'a fifo \<Rightarrow> 'a list" where "fifo_\<alpha> F == snd F @ rev (fst F)"

subsection "Correctness"
lemma fifo_empty_correct: "fifo_\<alpha> fifo_empty = []" 
  by (auto simp add: fifo_\<alpha>_def fifo_empty_def)

lemma fifo_isEmpty_correct: "fifo_isEmpty F \<longleftrightarrow> fifo_\<alpha> F = []"
  by (cases F) (auto simp add: fifo_isEmpty_def fifo_\<alpha>_def)

lemma fifo_put_correct: "fifo_\<alpha> (fifo_put a F) = fifo_\<alpha> F @ [a]"
  by (auto simp add: fifo_put_def fifo_\<alpha>_def)

lemma fifo_get_correct: 
  "fifo_\<alpha> F \<noteq> [] \<Longrightarrow> fst (fifo_get F) = hd (fifo_\<alpha> F)"
  "fifo_\<alpha> F \<noteq> [] \<Longrightarrow> fifo_\<alpha> (snd (fifo_get F)) = tl (fifo_\<alpha> F)"
  apply (cases F)
  apply (case_tac "b")
  apply (auto simp add: fifo_get_def fifo_\<alpha>_def Let_def) [2]
  apply (cases F)
  apply (case_tac "b")
  apply (auto simp add: fifo_get_def fifo_\<alpha>_def Let_def)
  done

lemmas fifo_correct_basic = 
  fifo_empty_correct fifo_isEmpty_correct fifo_put_correct fifo_get_correct

text {* Do not use the next definitions for generating (efficient) code. 
        They are for simpler reasoning about @{const fifo_get}. *}
  -- "The next element to be got from the fifo"
definition "fifo_hd F == hd (fifo_\<alpha> F)"
  -- "The fifo where the first element is removed"
definition "fifo_tl F = snd (fifo_get F)"

lemma fifo_get_split: "fifo_get F = (fifo_hd F, fifo_tl F)"
  apply (unfold fifo_hd_def fifo_tl_def fifo_get_def fifo_\<alpha>_def)
  apply (auto split: list.split simp add: Let_def)
  done

lemma fifo_tl_correct: "fifo_\<alpha> F \<noteq> [] \<Longrightarrow> fifo_\<alpha> (fifo_tl F) = tl (fifo_\<alpha> F)"
  by (simp add: fifo_tl_def fifo_get_correct)

lemmas fifo_hd_correct = fifo_hd_def
lemmas fifo_get_split_correct = fifo_get_split fifo_hd_correct fifo_tl_correct

subsection "Code Generation"
export_code
  fifo_empty fifo_isEmpty fifo_put fifo_get 
  in SML 
  module_name Fifo
  file - (*"Fifo.ML"*)

end
