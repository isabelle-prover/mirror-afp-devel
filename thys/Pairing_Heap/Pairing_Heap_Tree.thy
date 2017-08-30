(* Author: Hauke Brinkop and Tobias Nipkow *)

section \<open>Pairing Heap in Binary Tree Representation\<close>

theory Pairing_Heap_Tree
imports  
  "HOL-Library.Tree_Multiset"
begin

subsection \<open>Definitions\<close>

text \<open>Pairing heaps \cite{FredmanSST86}
in their original representation as binary trees.\<close>

fun get_min  :: "'a :: linorder tree \<Rightarrow> 'a" where
"get_min (Node _ x _) = x"

context linorder
begin

fun link :: "'a tree \<Rightarrow> 'a tree" where
  "link Leaf = Leaf"
| "link (Node lx x Leaf) = Node lx x Leaf"
| "link (Node lx x (Node ly y ry)) = 
    (if x < y then Node (Node ly y lx) x ry else Node (Node lx x ly) y ry)"

fun pass\<^sub>1 :: "'a tree \<Rightarrow> 'a tree" where
  "pass\<^sub>1 Leaf = Leaf"
| "pass\<^sub>1 (Node lx x Leaf) = Node lx x Leaf" 
| "pass\<^sub>1 (Node lx x (Node ly y ry)) = link (Node lx x (Node ly y (pass\<^sub>1 ry)))"

fun pass\<^sub>2 :: "'a tree \<Rightarrow> 'a tree" where
  "pass\<^sub>2 Leaf = Leaf"
| "pass\<^sub>2 (Node l x r) = link(Node l x (pass\<^sub>2 r))"

fun merge_pairs :: "'a tree \<Rightarrow> 'a tree" where
  "merge_pairs Leaf = Leaf"
| "merge_pairs (Node lx x Leaf) = Node lx x Leaf" 
| "merge_pairs (Node lx x (Node ly y ry)) =
   link (link (Node lx x (Node ly y (merge_pairs ry))))"

fun del_min :: "'a tree \<Rightarrow> 'a tree" where
  "del_min Leaf = Leaf"
| "del_min (Node l _ Leaf) = pass\<^sub>2 (pass\<^sub>1 l)"

fun merge :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
  "merge Leaf h = h"
| "merge h Leaf = h"
| "merge (Node lx x Leaf) (Node ly y Leaf) = link (Node lx x (Node ly y Leaf))"

fun insert :: "'a \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
  "insert x h = merge (Node Leaf x Leaf) h"

end

text \<open>The invariant is the conjunction of \<open>is_root\<close> and \<open>pheap\<close>:\<close>

fun is_root :: "'a tree \<Rightarrow> bool" where
  "is_root h = (case h of Leaf \<Rightarrow> True | Node l x r \<Rightarrow> r = Leaf)"

fun pheap :: "('a :: linorder) tree \<Rightarrow> bool" where
"pheap Leaf = True" |
"pheap (Node l x r) = (pheap l \<and> pheap r \<and> (\<forall>y \<in> set_tree l. x \<le> y))"


subsection \<open>Correctness Proofs\<close>

text \<open>An optimization:\<close>

lemma pass12_merge_pairs: "pass\<^sub>2 (pass\<^sub>1 hs) = merge_pairs hs"
by (induction hs rule: merge_pairs.induct) auto

declare pass12_merge_pairs[code_unfold]


subsubsection \<open>Invariants\<close>

lemma link_struct: "\<exists>la a. link (Node lx x (Node ly y ry)) = Node la a ry" 
  by simp

lemma pass\<^sub>1_struct: "\<exists>la a ra. pass\<^sub>1 (Node lx x rx) = Node la a ra" 
  by (cases rx) simp_all

lemma pass\<^sub>2_struct: "\<exists>la a. pass\<^sub>2 (Node lx x rx) = Node la a Leaf" 
  by (induction rx arbitrary: x lx rule: pass\<^sub>2.induct) 
  (simp, metis pass\<^sub>2.simps(2) link_struct)

lemma is_root_merge:
  "is_root h1 \<Longrightarrow> is_root h2 \<Longrightarrow> is_root (merge h1 h2)"
by (simp split: tree.splits)

lemma is_root_insert: "is_root h \<Longrightarrow> is_root (insert x h)"
by (simp split: tree.splits)

lemma is_root_del_min:
  assumes "is_root h" shows "is_root (del_min h)"
proof (cases h)
  case [simp]: (Node lx x rx)
  have "rx = Leaf" using assms by simp
  thus ?thesis 
  proof (cases lx)
    case (Node ly y ry)
    then obtain la a ra where "pass\<^sub>1 lx = Node a la ra" 
      using pass\<^sub>1_struct by blast
    moreover obtain lb b where "pass\<^sub>2 \<dots> = Node b lb Leaf"
      using pass\<^sub>2_struct by blast
    ultimately show ?thesis using assms by simp
  qed simp
qed simp

lemma pheap_merge:
  "\<lbrakk> is_root h1; is_root h2; pheap h1; pheap h2 \<rbrakk> \<Longrightarrow> pheap (merge h1 h2)"
by (auto split: tree.splits)

lemma pheap_insert: "is_root h \<Longrightarrow> pheap h \<Longrightarrow> pheap (insert x h)"
by (auto split: tree.splits)

lemma pheap_link: "pheap t \<Longrightarrow> pheap (link t)"
by(induction t rule: link.induct)(auto)

lemma pheap_pass1: "pheap h \<Longrightarrow> pheap (pass\<^sub>1 h)"
by(induction h rule: pass\<^sub>1.induct) (auto)

lemma pheap_pass2: "pheap h \<Longrightarrow> pheap (pass\<^sub>2 h)"
by (induction h)(auto simp: pheap_link)

lemma pheap_del_min: "is_root h \<Longrightarrow> pheap h \<Longrightarrow> pheap (del_min h)"
by (auto simp: pheap_pass1 pheap_pass2 split: tree.splits)


subsubsection \<open>Functional Correctness\<close>

lemma get_min_in:
  "h \<noteq> Leaf \<Longrightarrow> get_min h \<in> set_tree h"
by(auto simp add: neq_Leaf_iff)

lemma get_min_min: "\<lbrakk> is_root h; pheap h; x \<in> set_tree h \<rbrakk> \<Longrightarrow> get_min h \<le> x"
by(auto split: tree.splits)


lemma mset_link: "mset_tree (link t) = mset_tree t"
by(induction t rule: link.induct)(auto simp: add_ac)

lemma mset_merge: "\<lbrakk> is_root h1; is_root h2 \<rbrakk>
 \<Longrightarrow>  mset_tree (merge h1 h2) = mset_tree h1 + mset_tree h2"
by (induction h1 h2 rule: merge.induct) (auto simp add: ac_simps)

lemma mset_insert:
  "is_root h \<Longrightarrow> mset_tree (insert a h) = {#a#} + mset_tree h"
by (simp add: mset_merge insert_def)

lemma mset_merge_pairs: "mset_tree (merge_pairs h) = mset_tree h"
by(induction h rule: merge_pairs.induct)(auto simp: mset_link add_ac)

lemma mset_del_min: "\<lbrakk> is_root h; t \<noteq> Leaf \<rbrakk> \<Longrightarrow>
  mset_tree (del_min h) = mset_tree h - {#get_min h#}"
by(induction h rule: del_min.induct)(auto simp: pass12_merge_pairs mset_merge_pairs)

end
