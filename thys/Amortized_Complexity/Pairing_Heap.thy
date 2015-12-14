(* Author: Hauke Brinkop *)

section {* Amortized Analysis of Pairing Heaps *}

subsection {* Binary Tree Representation *}

theory Pairing_Heap
imports  
  "~~/src/HOL/Library/Tree"
  Amor
  Priority_Queue_ops
  Lemmas_log
begin

text{* Pairing heaps were invented by Fredman, Sedgewick, Sleator and Tarjan
\cite{FredmanSST86}. In this theory we verify their logarithmic bound on the
amortized complexity of pairing heaps. *}

fun link :: "'a :: linorder tree \<Rightarrow> 'a tree" where
  "link Leaf = Leaf"
| "link (Node lx x Leaf) = Node lx x Leaf"
| "link (Node lx x (Node ly y ry)) = 
    (if x < y then Node (Node ly y lx) x else Node (Node lx x ly) y) ry"

fun pass\<^sub>1 :: "'a :: linorder tree \<Rightarrow> 'a tree" where
  "pass\<^sub>1 Leaf = Leaf"
| "pass\<^sub>1 (Node lx x Leaf) = Node lx x Leaf" 
| "pass\<^sub>1 (Node lx x (Node ly y ry)) = link (Node lx x (Node ly y (pass\<^sub>1 ry)))"

fun len :: "'a tree \<Rightarrow> nat" where 
  "len Leaf = 0"
| "len (Node _ _ r) = 1 + len r"

fun pass\<^sub>2 :: "'a :: linorder tree \<Rightarrow> 'a tree" where
  "pass\<^sub>2 Leaf = Leaf"
| "pass\<^sub>2 (Node l x r) = link(Node l x (pass\<^sub>2 r))"

fun del_min :: "'a :: linorder tree \<Rightarrow> 'a tree" where
  "del_min Leaf = Leaf"
| "del_min (Node l _ Leaf) = pass\<^sub>2 (pass\<^sub>1 l)"

fun merge :: "'a :: linorder tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
  "merge Leaf h = h"
| "merge h Leaf = h"
| "merge (Node lx x Leaf) (Node ly y Leaf) = link (Node lx x (Node ly y Leaf))"

fun insert :: "'a \<Rightarrow> 'a :: linorder tree \<Rightarrow> 'a tree" where
  "insert x = merge (Node Leaf x Leaf)"

fun isRoot :: "'a :: linorder tree \<Rightarrow> bool" where
  "isRoot h = (case h of Leaf \<Rightarrow> True | Node _ _ r \<Rightarrow> r = Leaf)"

fun ld\<^sub>0 :: "nat \<Rightarrow> real" where
  "ld\<^sub>0 x = (if x = 0 then 0 else log 2 x)"

fun \<Phi> :: "'a tree \<Rightarrow> real" where
  "\<Phi> Leaf = 0"
| "\<Phi> (Node l x r) = \<Phi> l + \<Phi> r + ld\<^sub>0 (1 + size l + size r)"

lemma link_size[simp]: "size (link h) = size h" 
  by (cases h rule: link.cases) simp_all

lemma size_pass\<^sub>1[simp]: "size (pass\<^sub>1 h) = size h" 
  by (induct h rule: pass\<^sub>1.induct) simp_all

lemma size_pass\<^sub>2: "size (pass\<^sub>2 h) = size h" 
  by (induct h rule: pass\<^sub>2.induct) simp_all

lemma size_merge[simp]: 
  "isRoot h1 \<Longrightarrow> isRoot h2 \<Longrightarrow> size (merge h1 h2) = size h1 + size h2"
  by (simp split: tree.splits)

lemma link_struct: "\<exists>la a. link(Node lx x (Node ly y ry)) = Node la a ry" 
  by simp

lemma pass\<^sub>1_struct: "\<exists>la a ra. pass\<^sub>1(Node lx x rx) = Node la a ra" 
  by (cases rx) simp_all

lemma pass\<^sub>2_struct: "\<exists>la a. pass\<^sub>2(Node lx x rx) = Node la a Leaf" 
  by (induction rx arbitrary: x lx rule: pass\<^sub>2.induct) 
  (simp, metis pass\<^sub>2.simps(2) link_struct)

lemma \<Delta>\<Phi>\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t: "isRoot h \<Longrightarrow> \<Phi> (insert x h) - \<Phi> h \<le> ld\<^sub>0 (size h + 1)"
  by (simp split: tree.splits)

lemma \<Delta>\<Phi>\<^sub>m\<^sub>e\<^sub>r\<^sub>g\<^sub>e: assumes "isRoot h1 \<and> isRoot h2" 
  shows "\<Phi> (merge h1 h2) - \<Phi> h1 - \<Phi> h2 \<le> 2*ld\<^sub>0 (size h1 + size h2)" 
proof (cases h1)
  case [simp]: (Node lx x rx)
  thus ?thesis
  proof (cases h2)
    case [simp]: (Node ly y ry)
    let ?h = "Node lx x (Node ly y Leaf)"
    have "\<Phi> (link ?h) - \<Phi> ?h \<le> ld\<^sub>0 (1 + size lx + size ly)" by (simp add: algebra_simps)
    also have "\<dots> \<le> ld\<^sub>0 (size h1 + size h2)" by simp
    moreover have "\<Phi> ?h - \<Phi> h1 - \<Phi> h2 \<le> \<dots>" using assms by simp
    ultimately have "\<Phi> (link ?h) - \<Phi> h1 - \<Phi> h2 \<le> 2*\<dots>" by linarith
    thus ?thesis using assms by simp
  qed simp
qed simp

fun upperbound :: "'a tree \<Rightarrow> real" where
  "upperbound Leaf = 0"
| "upperbound (Node _ _ Leaf) = 0"
| "upperbound (Node lx _ (Node ly _ Leaf)) = 2*ld\<^sub>0(2 + size lx + size ly)" 
| "upperbound (Node lx _ (Node ly _ ry)) = 2*ld\<^sub>0(2 + size lx + size ly + size ry) 
    - 2*ld\<^sub>0(size ry) - 2 + upperbound ry"

lemma \<Delta>\<Phi>_pass1_upperbound: "\<Phi> (pass\<^sub>1 h) - \<Phi> h  \<le> upperbound h"
proof (induction h rule: upperbound.induct)
  case (3 lx x ly y)
  have "ld\<^sub>0 (1 + size lx + size ly) - ld\<^sub>0 (1 + size ly) 
    \<le> ld\<^sub>0(1 + size lx + size ly)" by simp
  also have "\<dots> \<le> ld\<^sub>0(2 + size lx + size ly)" by simp
  also have "\<dots> \<le> 2*\<dots>" by simp
  finally show ?case by (simp add: algebra_simps)
next
  case (4 lx x ly y lz z rz)
  let ?ry = "Node lz z rz"
  let ?rx = "Node ly y ?ry"
  let ?h = "Node lx x ?rx"
  let ?t ="ld\<^sub>0(1 + size lx + size ly) - ld\<^sub>0(1 + size ly + size ?ry)"
  have "\<Phi> (pass\<^sub>1 ?h) - \<Phi> ?h \<le> ?t + upperbound ?ry" 
    using "4.IH" by (simp add: algebra_simps)
  also have "?t \<le> 2*ld\<^sub>0 (size ?h) - 2*ld\<^sub>0(size ?ry) - 2"
  proof -
    have "ld\<^sub>0 (1 + size lx + size ly) + ld\<^sub>0 (size ?ry) - 2*ld\<^sub>0 (size ?h) 
      = log 2 ((1 + size lx + size ly)/(size ?h) ) + log 2 (size ?ry / size ?h)"
      (is "_ = log 2 ?t1 + log 2 ?t2") by (simp add: log_divide)
    also have "\<dots> \<le> -2" 
    proof -
      have "2 + \<dots> \<le> 2*log 2 (?t1 + ?t2)"
        using ld_sum_inequality [of "?t1" "?t2"] by simp
      also have "\<dots> \<le> 0" by (simp add: field_simps del: of_nat_Suc)
      finally show ?thesis by linarith
    qed 
    finally have "log 2 (1 + size lx + size ly) + log 2 (size ?ry) + 2
      \<le>  2*log 2 (size ?h)" by simp
    moreover have "log 2 (size ?ry) \<le> log 2 (size ?rx)" by simp   
    ultimately have "log 2 (1 + size lx + size ly) - \<dots> 
      \<le>  2*log 2 (size ?h) - 2*log 2 (size ?ry) - 2" by linarith
    thus ?thesis by simp
  qed
  finally show ?case by (simp add: algebra_simps)
qed simp_all

lemma \<Delta>\<Phi>_pass1: "\<Phi> (pass\<^sub>1 h) - \<Phi> h \<le> 2*ld\<^sub>0(size h) - len h + 2"
proof -  
  have "upperbound h \<le> 2*ld\<^sub>0(size h) - len h + 2" 
    by (induct h rule: upperbound.induct) (simp_all add: algebra_simps)
  thus ?thesis using \<Delta>\<Phi>_pass1_upperbound [of "h"] by linarith
qed

lemma \<Delta>\<Phi>_pass2: "\<Phi> (pass\<^sub>2 h) - \<Phi> h \<le> ld\<^sub>0 (size h)"
proof (induction h rule: pass\<^sub>2.induct)
  case (2 lx x rx)
  thus ?case 
  proof (cases rx)
    case [simp]: (Node ly y ry)
    let ?h = "Node lx x rx"
    obtain la a where 1: "pass\<^sub>2 rx = Node la a Leaf" 
      using pass\<^sub>2_struct by force
    hence "size \<dots> = size rx" using size_pass\<^sub>2 by metis
    hence "\<Phi> (pass\<^sub>2 ?h) - \<Phi> ?h  
      \<le> ld\<^sub>0(size ?h) - ld\<^sub>0 \<dots> + \<Phi> (pass\<^sub>2 rx) - \<Phi> rx"
      using 1 by (simp add: algebra_simps) 
    thus ?thesis using "2.IH" 1 by simp
  qed simp
qed simp

lemma \<Delta>\<Phi>_del_min:  "\<Phi> (del_min (Node lx x Leaf)) - \<Phi> (Node lx x Leaf) 
  \<le> 3*ld\<^sub>0(size lx) - len lx + 2"
proof -
  let ?h = "Node lx x Leaf"
  let ?\<Delta>\<Phi>\<^sub>1 = "\<Phi> lx - \<Phi> ?h" 
  let ?\<Delta>\<Phi>\<^sub>2 = "\<Phi>(pass\<^sub>2(pass\<^sub>1 lx)) - \<Phi> lx"
  let ?\<Delta>\<Phi> = "\<Phi> (del_min ?h) - \<Phi> ?h"
  have "\<Phi>(pass\<^sub>2(pass\<^sub>1 lx)) - \<Phi> (pass\<^sub>1 lx) \<le> ld\<^sub>0 (size lx)" 
    using \<Delta>\<Phi>_pass2 [of "pass\<^sub>1 lx"] by simp
  moreover have "\<Phi> (pass\<^sub>1 lx) - \<Phi> lx \<le>  2*\<dots> - len lx + 2" 
    using \<Delta>\<Phi>_pass1 by metis
  moreover have "?\<Delta>\<Phi> \<le> ?\<Delta>\<Phi>\<^sub>2" by simp
  ultimately show ?thesis by linarith
qed

lemma merge_isRoot: "isRoot h1 \<Longrightarrow> isRoot h2 \<Longrightarrow> isRoot (merge h1 h2)"
  by (simp split: tree.splits)

lemma insert_isRoot: "isRoot h \<Longrightarrow> isRoot (insert x h)"
  by (simp split: tree.splits)

lemma del_min_isRoot: assumes "isRoot h" shows "isRoot (del_min h)"
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

lemma pass\<^sub>1_len: "len (pass\<^sub>1 h) \<le> len h"
  by (induct h rule: pass\<^sub>1.induct) simp_all

fun nxt :: "'a :: linorder op\<^sub>p\<^sub>q \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
  "nxt Del_min h = del_min h"
| "nxt (Insert x) h = insert x h"

fun t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 :: "'a tree \<Rightarrow> real" where
  "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 Leaf = 1"
| "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 (Node _ _ Leaf) = 1"
| "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 (Node _ _ (Node _ _ ry)) = 1 + t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 ry"

fun t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2 :: "'a tree \<Rightarrow> real" where
  "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2 Leaf = 1"
| "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2 (Node _ _ rx) = 1 + t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2 rx"

fun t :: "'a :: linorder op\<^sub>p\<^sub>q \<Rightarrow> 'a tree \<Rightarrow> real" where
  "t Del_min Leaf = 1"
| "t Del_min (Node lx _  _) = 1 + t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2 (pass\<^sub>1 lx) + t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 lx"
| "t (Insert a) _ = 1"

fun U :: "'a :: linorder op\<^sub>p\<^sub>q \<Rightarrow> 'a tree \<Rightarrow> real" where
  "U (Insert a) h = 1 + log 2 (size h + 1)"
| "U Del_min h = 3*log 2 (size h + 1) + 5"

interpretation pairing: amor
where init = "Leaf" 
and nxt = "nxt"
and t = "t" 
and inv = "isRoot" 
and \<Phi> = "\<Phi>"
and U = "U"
proof
  case goal2 thus ?case 
    using insert_isRoot del_min_isRoot by (cases f) simp_all  
  case goal3 show ?case by (induct s) simp_all 
  case goal5 show ?case 
  proof (cases f)
    case [simp]: (Insert x)
    have "\<Phi> (insert x s) - \<Phi> s \<le> ld\<^sub>0 (1 + size s)" using \<Delta>\<Phi>\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t goal5 by auto
    thus ?thesis by simp
  next
    case [simp]: (Del_min)
    thus ?thesis
    proof (cases s)
      case [simp]: (Node lx x rx)
      have "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2 (pass\<^sub>1 lx) + t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 lx \<le> 2 + len lx"
        by (induct lx rule: pass\<^sub>1.induct) simp_all
      hence  "t f s \<le> 1 + \<dots>" by simp
      moreover have  "\<Phi> (del_min s) - \<Phi> s \<le> 3*ld\<^sub>0(size lx) - len lx + 2"
        using  \<Delta>\<Phi>_del_min[of "lx" "x"] goal5 by simp
      moreover have "ld\<^sub>0(size lx) \<le> ld\<^sub>0 (size s + 1)" by simp
      ultimately show ?thesis by simp
    qed simp
  qed
qed simp_all

end
