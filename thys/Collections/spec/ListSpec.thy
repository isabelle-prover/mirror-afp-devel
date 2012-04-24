header {* \isaheader{Specification of Sequences} *}
theory ListSpec 
imports Main 
  "../common/Misc" 
  "../iterator/SetIteratorOperations" 
  "../iterator/SetIteratorGA"
begin

(*@intf List
  @abstype 'a list
  This interface specifies sequences.
*)

subsection "Definition"
locale list =
  -- "Abstraction to HOL-lists"
  fixes \<alpha> :: "'s \<Rightarrow> 'x list"
  -- "Invariant"
  fixes invar :: "'s \<Rightarrow> bool"

subsection "Functions"

locale list_empty = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes empty :: "unit \<Rightarrow> 's"
  assumes empty_correct:
    "\<alpha> (empty ()) = []"
    "invar (empty ())"


locale list_isEmpty = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes isEmpty :: "'s \<Rightarrow> bool"
  assumes isEmpty_correct:
    "invar s \<Longrightarrow> isEmpty s \<longleftrightarrow> \<alpha> s = []"

locale list_iteratei = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes iteratei :: "'s \<Rightarrow> ('x,'\<sigma>) set_iterator"
  assumes iteratei_correct:
    "invar s \<Longrightarrow> iteratei s = foldli (\<alpha> s)"
begin
  lemma iteratei_no_sel_rule:
    "invar s \<Longrightarrow> distinct (\<alpha> s) \<Longrightarrow> set_iterator (iteratei s) (set (\<alpha> s))"
    by (simp add: iteratei_correct set_iterator_foldli_correct)
end

lemma list_iteratei_iteratei_linord_rule:
  "list_iteratei \<alpha> invar iteratei \<Longrightarrow> invar s \<Longrightarrow> distinct (\<alpha> s) \<Longrightarrow> sorted (\<alpha> s) \<Longrightarrow>
   set_iterator_linord (iteratei s) (set (\<alpha> s))"
  by (simp add: list_iteratei_def set_iterator_linord_foldli_correct)

lemma list_iteratei_iteratei_rev_linord_rule:
  "list_iteratei \<alpha> invar iteratei \<Longrightarrow> invar s \<Longrightarrow> distinct (\<alpha> s) \<Longrightarrow> sorted (rev (\<alpha> s)) \<Longrightarrow>
   set_iterator_rev_linord (iteratei s) (set (\<alpha> s))"
  by (simp add: list_iteratei_def set_iterator_rev_linord_foldli_correct)


locale list_reverse_iteratei = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes reverse_iteratei :: "'s \<Rightarrow> ('x,'\<sigma>) set_iterator"
  assumes reverse_iteratei_correct:
    "invar s \<Longrightarrow> reverse_iteratei s = foldri (\<alpha> s)"
begin
  lemma reverse_iteratei_no_sel_rule:
    "invar s \<Longrightarrow> distinct (\<alpha> s) \<Longrightarrow> set_iterator (reverse_iteratei s) (set (\<alpha> s))"
    by (simp add: reverse_iteratei_correct set_iterator_foldri_correct)
end

lemma list_reverse_iteratei_iteratei_linord_rule:
  "list_reverse_iteratei \<alpha> invar iteratei \<Longrightarrow> invar s \<Longrightarrow> distinct (\<alpha> s) \<Longrightarrow> sorted (rev (\<alpha> s)) \<Longrightarrow>
   set_iterator_linord (iteratei s) (set (\<alpha> s))"
  by (simp add: list_reverse_iteratei_def set_iterator_linord_foldri_correct)

lemma list_reverse_iteratei_iteratei_rev_linord_rule:
  "list_reverse_iteratei \<alpha> invar iteratei \<Longrightarrow> invar s \<Longrightarrow> distinct (\<alpha> s) \<Longrightarrow> sorted (\<alpha> s) \<Longrightarrow>
   set_iterator_rev_linord (iteratei s) (set (\<alpha> s))"
  by (simp add: list_reverse_iteratei_def set_iterator_rev_linord_foldri_correct)


locale list_size = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes size :: "'s \<Rightarrow> nat"
  assumes size_correct:
    "invar s \<Longrightarrow> size s = length (\<alpha> s)"
  
subsubsection "Stack"

locale list_push = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes push :: "'x \<Rightarrow> 's \<Rightarrow> 's"
  assumes push_correct:
    "invar s \<Longrightarrow> \<alpha> (push x s) = x#\<alpha> s"
    "invar s \<Longrightarrow> invar (push x s)"

locale list_pop = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes pop :: "'s \<Rightarrow> ('x \<times> 's)"
  assumes pop_correct:
    "\<lbrakk>invar s; \<alpha> s \<noteq> []\<rbrakk> \<Longrightarrow> fst (pop s) = hd (\<alpha> s)"
    "\<lbrakk>invar s; \<alpha> s \<noteq> []\<rbrakk> \<Longrightarrow> \<alpha> (snd (pop s)) = tl (\<alpha> s)"
    "\<lbrakk>invar s; \<alpha> s \<noteq> []\<rbrakk> \<Longrightarrow> invar (snd (pop s))"
begin
  lemma popE: 
    assumes I: "invar s" "\<alpha> s \<noteq> []" 
    obtains s' where "pop s = (hd (\<alpha> s), s')" "invar s'" "\<alpha> s' = tl (\<alpha> s)"
  proof -
    from pop_correct(1,2,3)[OF I] have 
      C: "fst (pop s) = hd (\<alpha> s)"
         "\<alpha> (snd (pop s)) = tl (\<alpha> s)"
         "invar (snd (pop s))" .
    from that[of "snd (pop s)", OF _ C(3,2), folded C(1)] show thesis
      by simp
  qed

  text {* The following shortcut notations are not meant for generating efficient code,
    but solely to simplify reasoning *}
  definition "head s == fst (pop s)"
  definition "tail s == snd (pop s)"

  lemma tail_correct: "\<lbrakk>invar F; \<alpha> F \<noteq> []\<rbrakk> \<Longrightarrow> \<alpha> (tail F) = tl (\<alpha> F)"
    by (simp add: tail_def pop_correct)

  lemma head_correct: "\<lbrakk>invar F; \<alpha> F \<noteq> []\<rbrakk> \<Longrightarrow> (head F) = hd (\<alpha> F)"
    by (simp add: head_def pop_correct)

  lemma pop_split: "pop F = (head F, tail F)"
    apply (cases "pop F")
    apply (simp add: head_def tail_def)
    done

end

locale list_top = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes top :: "'s \<Rightarrow> 'x"
  assumes top_correct:
    "\<lbrakk>invar s; \<alpha> s \<noteq> []\<rbrakk> \<Longrightarrow> top s = hd (\<alpha> s)"

subsubsection {* Queue *}
locale list_enqueue = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes enqueue :: "'x \<Rightarrow> 's \<Rightarrow> 's"
  assumes enqueue_correct: 
    "invar s \<Longrightarrow> \<alpha> (enqueue x s) = \<alpha> s @ [x]"
    "invar s \<Longrightarrow> invar (enqueue x s)"

  -- "Same specification as pop"
locale list_dequeue = list_pop
begin
  lemmas dequeue_correct = pop_correct
  lemmas dequeueE = popE
  lemmas dequeue_split=pop_split
end

  -- "Same specification as top"
locale list_next = list_top
begin
  lemmas next_correct = top_correct
end

subsubsection "Indexing"
locale list_get = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes get :: "'s \<Rightarrow> nat \<Rightarrow> 'x"
  assumes get_correct:
    "\<lbrakk>invar s; i<length (\<alpha> s)\<rbrakk> \<Longrightarrow> get s i = \<alpha> s ! i"

locale list_set = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes set :: "'s \<Rightarrow> nat \<Rightarrow> 'x \<Rightarrow> 's"
  assumes set_correct:
    "\<lbrakk>invar s; i<length (\<alpha> s)\<rbrakk> \<Longrightarrow> \<alpha> (set s i x) = \<alpha> s [i := x]"
    "\<lbrakk>invar s; i<length (\<alpha> s)\<rbrakk> \<Longrightarrow> invar (set s i x)"

  -- "Same specification as enqueue"
locale list_add = list_enqueue
begin
  lemmas add_correct = enqueue_correct
end

    
end
