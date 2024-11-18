(* Author: Tobias Nipkow *)

section \<open>Pairing Heap According to Oksaki (Modified)\<close>

theory Pairing_Heap_List2
imports
  "HOL-Library.Multiset"
  "HOL-Data_Structures.Priority_Queue_Specs"
begin

subsection \<open>Definitions\<close>

text \<open>This version of pairing heaps is a modified version
of the one by Okasaki \<^cite>\<open>"Okasaki"\<close> that avoids structural invariants.\<close>

datatype 'a hp = Hp 'a (hps: "'a hp list")

type_synonym 'a heap = "'a hp option"

hide_const (open) insert

fun get_min  :: "'a heap \<Rightarrow> 'a" where
"get_min (Some(Hp x _)) = x"


fun link :: "('a::linorder) hp \<Rightarrow> 'a hp \<Rightarrow> 'a hp" where
"link (Hp x1 hs1) (Hp x2 hs2) = 
    (if x1 < x2 then Hp x1 (Hp x2 hs2 # hs1) else Hp x2 (Hp x1 hs1 # hs2))"

fun merge :: "('a::linorder) heap \<Rightarrow> 'a heap \<Rightarrow> 'a heap" where
"merge ho None = ho" |
"merge None ho = ho" |
"merge (Some h1) (Some h2) = Some(link h1 h2)"

lemma merge_None[simp]: "merge None ho = ho"
by(cases ho)auto

fun insert :: "('a::linorder) \<Rightarrow> 'a heap \<Rightarrow> 'a heap" where
"insert x None = Some(Hp x [])" |
"insert x (Some h) = Some(link (Hp x []) h)"

fun pass\<^sub>1 :: "('a::linorder) hp list \<Rightarrow> 'a hp list" where
"pass\<^sub>1 (h1#h2#hs) = link h1 h2 # pass\<^sub>1 hs" |
"pass\<^sub>1 hs = hs"

fun pass\<^sub>2 :: "('a::linorder) hp list \<Rightarrow> 'a heap" where
"pass\<^sub>2 [] = None" |
"pass\<^sub>2 (h#hs) = Some(case pass\<^sub>2 hs of None \<Rightarrow> h | Some h' \<Rightarrow> link h h')"

fun merge_pairs :: "('a::linorder) hp list \<Rightarrow> 'a heap" where
  "merge_pairs [] = None"
| "merge_pairs [h] = Some h" 
| "merge_pairs (h1 # h2 # hs) =
  Some(let h12 = link h1 h2 in case merge_pairs hs of None \<Rightarrow> h12 | Some h \<Rightarrow> link h12 h)"

fun del_min :: "('a::linorder) heap \<Rightarrow> 'a heap" where
  "del_min None = None"
| "del_min (Some(Hp x hs)) = pass\<^sub>2 (pass\<^sub>1 hs)"


subsection \<open>Correctness Proofs\<close>

text \<open>An optimization:\<close>

lemma pass12_merge_pairs: "pass\<^sub>2 (pass\<^sub>1 hs) = merge_pairs hs"
by (induction hs rule: merge_pairs.induct) (auto split: option.split)

declare pass12_merge_pairs[code_unfold]

text \<open>Abstraction functions:\<close>

fun mset_hp :: "'a hp \<Rightarrow>'a multiset" where
"mset_hp (Hp x hs) = {#x#} + sum_list(map mset_hp hs)"

definition mset_heap :: "'a heap \<Rightarrow>'a multiset" where
"mset_heap ho = (case ho of None \<Rightarrow> {#} | Some h \<Rightarrow> mset_hp h)"


subsubsection \<open>Invariants\<close>

fun php :: "('a::linorder) hp \<Rightarrow> bool" where
"php (Hp x hs) = (\<forall>h \<in> set hs. (\<forall>y \<in># mset_hp h. x \<le> y) \<and> php h)"

definition invar :: "('a::linorder) heap \<Rightarrow> bool" where
"invar ho = (case ho of None \<Rightarrow> True | Some h \<Rightarrow> php h)"

lemma php_link: "php h1 \<Longrightarrow> php h2 \<Longrightarrow> php (link h1 h2)"
by (induction h1 h2 rule: link.induct) (fastforce simp flip: sum_mset_sum_list)+

lemma invar_merge:
  "\<lbrakk> invar ho1; invar ho2 \<rbrakk> \<Longrightarrow> invar (merge ho1 ho2)"
by (auto simp: php_link invar_def split: option.splits)

lemma invar_insert: "invar ho \<Longrightarrow> invar (insert x ho)"
by (auto simp: php_link invar_def split: option.splits)

lemma invar_pass1: "\<forall>h \<in> set hs. php h \<Longrightarrow> \<forall>h \<in> set (pass\<^sub>1 hs). php h"
by(induction hs rule: pass\<^sub>1.induct) (auto simp: php_link)

lemma invar_pass2: "\<forall>h \<in> set hs. php h \<Longrightarrow> invar (pass\<^sub>2 hs)"
by (induction hs)(auto simp: php_link invar_def split: option.splits)

lemma invar_Some: "invar(Some h) = php h"
by(simp add: invar_def)

lemma invar_del_min: "invar ho \<Longrightarrow> invar (del_min ho)"
by(induction ho rule: del_min.induct)
  (auto simp: invar_Some intro!: invar_pass1 invar_pass2)


subsubsection \<open>Functional Correctness\<close>

lemma mset_hp_empty[simp]: "mset_hp h \<noteq> {#}"
by (cases h) auto

lemma mset_heap_Some: "mset_heap(Some h) = mset_hp h"
by(simp add: mset_heap_def)

lemma mset_heap_empty: "mset_heap h = {#} \<longleftrightarrow> h = None"
by (cases h) (auto simp add: mset_heap_def)

lemma get_min_in:
  "ho \<noteq> None \<Longrightarrow> get_min ho \<in># mset_hp(the ho)"
by(induction rule: get_min.induct)(auto)

lemma get_min_min: "\<lbrakk> ho \<noteq> None; invar ho; x \<in># mset_hp(the ho) \<rbrakk> \<Longrightarrow> get_min ho \<le> x"
by(induction ho rule: get_min.induct)(auto simp: invar_def simp flip: sum_mset_sum_list)

lemma mset_link: "mset_hp (link h1 h2) = mset_hp h1 + mset_hp h2"
by(induction h1 h2 rule: link.induct)(auto simp: add_ac)

lemma mset_merge: "mset_heap (merge ho1 ho2) = mset_heap ho1 + mset_heap ho2"
by (induction ho1 ho2 rule: merge.induct)
   (auto simp add: mset_heap_def mset_link ac_simps)

lemma mset_insert: "mset_heap (insert a ho) = {#a#} + mset_heap ho"
by(cases ho) (auto simp add: mset_link mset_heap_def insert_def)

lemma mset_pass\<^sub>1: "sum_list(map mset_hp (pass\<^sub>1 hs)) = sum_list(map mset_hp hs)"
by(induction hs rule: pass\<^sub>1.induct)
  (auto simp: mset_link split: option.split)

lemma mset_pass\<^sub>2: "mset_heap (pass\<^sub>2 hs) = sum_list(map mset_hp hs)"
by(induction hs rule: merge_pairs.induct)
  (auto simp: mset_link mset_heap_def split: option.split)

lemma mset_del_min: "ho \<noteq> None \<Longrightarrow>
  mset_heap (del_min ho) = mset_heap ho - {#get_min ho#}"
by(induction ho rule: del_min.induct)
  (auto simp: mset_heap_Some mset_pass\<^sub>1 mset_pass\<^sub>2)


text \<open>Last step: prove all axioms of the priority queue specification:\<close>

interpretation pairing: Priority_Queue_Merge
where empty = None and is_empty = "\<lambda>h. h = None"
and merge = merge and insert = insert
and del_min = del_min and get_min = get_min
and invar = invar and mset = mset_heap
proof(standard, goal_cases)
  case 1 show ?case by(simp add: mset_heap_def)
next
  case (2 q) thus ?case by(auto simp add: mset_heap_def split: option.split)
next
  case 3 show ?case by(simp add: mset_insert mset_merge)
next
  case 4 thus ?case by(simp add: mset_del_min mset_heap_empty)
next
  case (5 q) thus ?case using get_min_in[of q]
    by(auto simp add: eq_Min_iff get_min_min mset_heap_empty mset_heap_Some)
next
  case 6 thus ?case by (simp add: invar_def)
next
  case 7 thus ?case by(rule invar_insert)
next
  case 8 thus ?case by (simp add: invar_del_min)
next
  case 9 thus ?case by (simp add: mset_merge)
next
  case 10 thus ?case by (simp add: invar_merge)
qed

end
