(* Author: Tobias Nipkow *)

section \<open>Pairing Heap According to Oksaki (Modified)\<close>

theory Pairing_Heap_List2
imports "~~/src/HOL/Library/Multiset"
begin

subsection \<open>Definitions\<close>

text \<open>This version of pairing heaps is a modified version
of the one by Okasaki \cite{Okasaki} that avoids structural invariants.\<close>

datatype 'a hp = Hp 'a (hps: "'a hp list")

type_synonym 'a heap = "'a hp option"

fun get_min  :: "'a :: linorder heap \<Rightarrow> 'a" where
"get_min (Some(Hp x _)) = x"

fun link :: "'a :: linorder hp \<Rightarrow> 'a hp \<Rightarrow> 'a hp" where
"link (Hp x lx) (Hp y ly) = 
    (if x < y then Hp x (Hp y ly # lx) else Hp y (Hp x lx # ly))"

fun meld :: "'a :: linorder heap \<Rightarrow> 'a heap \<Rightarrow> 'a heap" where
"meld h None = h" |
"meld None h = h" |
"meld (Some h1) (Some h2) = Some(link h1 h2)"

lemma meld_None[simp]: "meld None h = h"
by(cases h)auto

hide_const (open) insert

fun insert :: "'a \<Rightarrow> 'a :: linorder heap \<Rightarrow> 'a heap" where
"insert x None = Some(Hp x [])" |
"insert x (Some h) = Some(link (Hp x []) h)"

fun pass\<^sub>1 :: "'a :: linorder hp list \<Rightarrow> 'a hp list" where
  "pass\<^sub>1 [] = []"
| "pass\<^sub>1 [h] = [h]" 
| "pass\<^sub>1 (h1#h2#hs) = link h1 h2 # pass\<^sub>1 hs"

fun pass\<^sub>2 :: "'a :: linorder hp list \<Rightarrow> 'a heap" where
  "pass\<^sub>2 [] = None"
| "pass\<^sub>2 (h#hs) = Some(case pass\<^sub>2 hs of None \<Rightarrow> h | Some h' \<Rightarrow> link h h')"

fun mergepairs :: "'a :: linorder hp list \<Rightarrow> 'a heap" where
  "mergepairs [] = None"
| "mergepairs [h] = Some h" 
| "mergepairs (h1 # h2 # hs) =
  Some(let h12 = link h1 h2 in case mergepairs hs of None \<Rightarrow> h12 | Some h \<Rightarrow> link h12 h)"

fun del_min :: "'a :: linorder heap \<Rightarrow> 'a heap" where
  "del_min None = None"
| "del_min (Some(Hp x hs)) = pass\<^sub>2 (pass\<^sub>1 hs)"


subsection \<open>Correctness Proofs\<close>

text \<open>An optimization:\<close>

lemma mergepairs_pass12: "mergepairs hs = pass\<^sub>2 (pass\<^sub>1 hs)"
by (induction hs rule: mergepairs.induct) (auto split: option.split)

declare mergepairs_pass12[symmetric, code_unfold]


subsubsection \<open>Invariants\<close>

fun php :: "'a :: linorder hp \<Rightarrow> bool" where
"php (Hp x hs) = (\<forall>h \<in> set hs. (\<forall>y \<in> set_hp h. x \<le> y) \<and> php h)"

definition invar :: "'a :: linorder heap \<Rightarrow> bool" where
"invar ho = (case ho of None \<Rightarrow> True | Some h \<Rightarrow> php h)"


lemma php_link: "php h1 \<Longrightarrow> php h2 \<Longrightarrow> php (link h1 h2)"
by (induction h1 h2 rule: link.induct) fastforce+

lemma invar_meld:
  "\<lbrakk> invar h1; invar h2 \<rbrakk> \<Longrightarrow> invar (meld h1 h2)"
by (auto simp: php_link invar_def split: option.splits)

lemma invar_insert: "invar h \<Longrightarrow> invar (insert x h)"
by (auto simp: php_link invar_def split: option.splits)

lemma invar_pass1: "\<forall>h \<in> set hs. php h \<Longrightarrow> \<forall>h \<in> set (pass\<^sub>1 hs). php h"
by(induction hs rule: pass\<^sub>1.induct) (auto simp: php_link)

lemma invar_pass2: "\<forall>h \<in> set hs. php h \<Longrightarrow> invar (pass\<^sub>2 hs)"
by (induction hs)(auto simp: php_link invar_def split: option.splits)

lemma invar_Some: "invar(Some h) = php h"
by(simp add: invar_def)

lemma invar_del_min: "invar h \<Longrightarrow> invar (del_min h)"
by(induction h rule: del_min.induct)
  (auto simp: invar_Some intro!: invar_pass1 invar_pass2)


subsubsection \<open>Functional Correctness\<close>

fun mset_hp :: "'a hp \<Rightarrow>'a multiset" where
"mset_hp (Hp x hs) = {#x#} + Union_mset(mset(map mset_hp hs))"

definition mset_heap :: "'a heap \<Rightarrow>'a multiset" where
"mset_heap ho = (case ho of None \<Rightarrow> {#} | Some h \<Rightarrow> mset_hp h)"

lemma mset_heap_Some: "mset_heap(Some hp) = mset_hp hp"
by(simp add: mset_heap_def)

lemma get_min_in:
  "h \<noteq> None \<Longrightarrow> get_min h \<in> set_hp(the h)"
by(induction rule: get_min.induct)(auto)

lemma get_min_min: "\<lbrakk> h \<noteq> None; invar h; x \<in> set_hp(the h) \<rbrakk> \<Longrightarrow> get_min h \<le> x"
by(induction h rule: get_min.induct)(auto simp: invar_def)


lemma mset_link: "mset_hp (link h1 h2) = mset_hp h1 + mset_hp h2"
by(induction h1 h2 rule: link.induct)(auto simp: add_ac)

lemma mset_meld: "mset_heap (meld h1 h2) = mset_heap h1 + mset_heap h2"
by (induction h1 h2 rule: meld.induct)
   (auto simp add: mset_heap_def mset_link ac_simps)

lemma mset_insert: "mset_heap (insert a h) = {#a#} + mset_heap h"
by(cases h) (auto simp add: mset_link mset_heap_def insert_def)

lemma mset_pass1:
  "Union_mset(image_mset mset_hp (mset (pass\<^sub>1 hs))) = Union_mset(image_mset mset_hp (mset hs))"
by(induction hs rule: pass\<^sub>1.induct)(auto simp: mset_link add_ac)

lemma mset_pass2: "mset_heap (pass\<^sub>2 hs) = Union_mset(image_mset mset_hp(mset hs))"
by(induction hs)(auto simp: mset_link mset_heap_def add_ac split: option.splits)

lemma mset_del_min: "h \<noteq> None \<Longrightarrow>
  mset_heap (del_min h) = mset_heap h - {#get_min h#}"
by(induction h rule: del_min.induct)
  (auto simp: mset_heap_Some mset_pass1 mset_pass2)

end
