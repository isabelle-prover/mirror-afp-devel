(* Author: Tobias Nipkow *)

section \<open>Pairing Heap According to Okasaki\<close>

theory Pairing_Heap_List1
imports "~~/src/HOL/Library/Multiset"
begin

subsection \<open>Definitions\<close>

text
\<open>This implementation follows Okasaki \cite{Okasaki}.
It satisfies the invariant that \<open>Empty\<close> only occurs
at the root of a pairing heap. The functional correctness proof does not
require the invariant but the amortized analysis (elsewhere) makes use of it.\<close>

datatype 'a heap = Empty | Hp 'a "'a heap list"

fun get_min  :: "'a :: linorder heap \<Rightarrow> 'a" where
"get_min (Hp x _) = x"

fun meld :: "'a :: linorder heap \<Rightarrow> 'a heap \<Rightarrow> 'a heap" where
"meld h Empty = h" |
"meld Empty h = h" |
"meld (Hp x lx) (Hp y ly) = 
    (if x < y then Hp x (Hp y ly # lx) else Hp y (Hp x lx # ly))"

hide_const (open) insert

fun insert :: "'a \<Rightarrow> 'a :: linorder heap \<Rightarrow> 'a heap" where
"insert x h = meld (Hp x []) h"

fun pass\<^sub>1 :: "'a :: linorder heap list \<Rightarrow> 'a heap list" where
  "pass\<^sub>1 [] = []"
| "pass\<^sub>1 [h] = [h]" 
| "pass\<^sub>1 (h1#h2#hs) = meld h1 h2 # pass\<^sub>1 hs"

fun pass\<^sub>2 :: "'a :: linorder heap list \<Rightarrow> 'a heap" where
  "pass\<^sub>2 [] = Empty"
| "pass\<^sub>2 (h#hs) = meld h (pass\<^sub>2 hs)"

fun mergepairs :: "'a :: linorder heap list \<Rightarrow> 'a heap" where
  "mergepairs [] = Empty"
| "mergepairs [h] = h" 
| "mergepairs (h1 # h2 # hs) = meld (meld h1 h2) (mergepairs hs)"

fun del_min :: "'a :: linorder heap \<Rightarrow> 'a heap" where
  "del_min Empty = Empty"
| "del_min (Hp x hs) = pass\<^sub>2 (pass\<^sub>1 hs)"


subsection \<open>Correctness Proofs\<close>

text \<open>An optimization:\<close>

lemma mergepairs_pass12: "mergepairs hs = pass\<^sub>2 (pass\<^sub>1 hs)"
by (induction hs rule: mergepairs.induct) (auto split: option.split)

declare mergepairs_pass12[symmetric, code_unfold]


subsubsection \<open>Invariants\<close>

fun pheap :: "'a :: linorder heap \<Rightarrow> bool" where
"pheap Empty = True" |
"pheap (Hp x hs) = (\<forall>h \<in> set hs. (\<forall>y \<in> set_heap h. x \<le> y) \<and> pheap h)"
(*
fun no_Empty :: "'a :: linorder heap \<Rightarrow> bool" where
"no_Empty Empty = False" |
"no_Empty (Hp x hs) = (\<forall>h \<in> set hs. no_Empty h)"

fun is_root :: "'a :: linorder heap \<Rightarrow> bool" where
"is_root Empty = True" |
"is_root (Hp x hs) = (\<forall>h \<in> set hs. no_Empty h)"
*)

lemma pheap_meld: "pheap h1 \<Longrightarrow> pheap h2 \<Longrightarrow> pheap (meld h1 h2)"
by (induction h1 h2 rule: meld.induct) fastforce+

lemma pheap_insert: "pheap h \<Longrightarrow> pheap (insert x h)"
by (auto simp: pheap_meld)

lemma pheap_pass1: "\<forall>h \<in> set hs. pheap h \<Longrightarrow> \<forall>h \<in> set (pass\<^sub>1 hs). pheap h"
by(induction hs rule: pass\<^sub>1.induct) (auto simp: pheap_meld)

lemma pheap_pass2: "\<forall>h \<in> set hs. pheap h \<Longrightarrow> pheap (pass\<^sub>2 hs)"
by (induction hs)(auto simp: pheap_meld)

lemma pheap_del_min: "pheap h \<Longrightarrow> pheap (del_min h)"
by(induction h rule: del_min.induct) (auto intro!: pheap_pass1 pheap_pass2)


subsubsection \<open>Functional Correctness\<close>

fun mset_heap :: "'a heap \<Rightarrow>'a multiset" where
"mset_heap Empty = {#}" |
"mset_heap (Hp x hs) = {#x#} + Union_mset(mset(map mset_heap hs))"

lemma get_min_in: "h \<noteq> Empty \<Longrightarrow> get_min h \<in> set_heap(h)"
by(induction rule: get_min.induct)(auto)

lemma get_min_min: "\<lbrakk> h \<noteq> Empty; pheap h; x \<in> set_heap(h) \<rbrakk> \<Longrightarrow> get_min h \<le> x"
by(induction h rule: get_min.induct)(auto)


lemma mset_meld: "mset_heap (meld h1 h2) = mset_heap h1 + mset_heap h2"
by(induction h1 h2 rule: meld.induct)(auto simp: add_ac)

lemma mset_insert: "mset_heap (insert a h) = {#a#} + mset_heap h"
by(cases h) (auto simp add: mset_meld insert_def add_ac)

lemma mset_pass1:
  "Union_mset(mset(map mset_heap (pass\<^sub>1 hs))) = Union_mset(mset(map mset_heap hs))"
by(induction hs rule: pass\<^sub>1.induct)(auto simp: mset_meld add_ac)

lemma mset_pass2: "mset_heap (pass\<^sub>2 hs) = Union_mset(mset(map mset_heap hs))"
by(induction hs)(auto simp: mset_meld add_ac)

lemma mset_del_min: "h \<noteq> Empty \<Longrightarrow>
  mset_heap (del_min h) = mset_heap h - {#get_min h#}"
by(induction h rule: del_min.induct) (auto simp: mset_pass1 mset_pass2)

end
