(* Author: Hauke Brinkop *)
(* Last update 03/25/2015 (пять) *)

section {* Amortized Analysis of Pairing Heaps in Binary Tree Representation *}

theory Pairing_Heap
imports 
  Complex_Main 
  Amor
  "~~/src/HOL/Library/Tree"
begin

text{* Pairing heaps were invented by Fredman, Sedgewick, Sleator and Tarjan
\cite{FredmanSST86}. In this theory we verify their logarithmic bound on the
amortized complexity of pairing heaps. *}

fun link :: "'a :: linorder tree \<Rightarrow> 'a tree" where
  "link Leaf = Leaf"
| "link (Node lx x Leaf) = Node lx x Leaf"
| "link (Node lx x (Node ly y ry)) = 
    (if x < y then Node (Node ly y lx) x else Node (Node lx x ly) y) ry"

fun firstpass :: "'a :: linorder tree \<Rightarrow> 'a tree" where
  "firstpass Leaf = Leaf"
| "firstpass (Node lx x Leaf) = Node lx x Leaf" 
| "firstpass (Node lx x (Node ly y ry)) = link (Node lx x (Node ly y (firstpass ry)))"

fun countTrees :: "'a tree \<Rightarrow> nat" where 
  "countTrees Leaf = 0"
| "countTrees (Node _ _ r) = 1 + countTrees r"

fun secondpass :: "'a :: linorder tree \<Rightarrow> 'a tree" where
  "secondpass Leaf = Leaf"
| "secondpass (Node lx x rx) = link(Node lx x (secondpass rx))"

fun deleteMin :: "'a :: linorder tree \<Rightarrow> 'a tree" where
  "deleteMin Leaf = Leaf"
| "deleteMin (Node lx _ Leaf) = secondpass (firstpass lx)"
| "deleteMin (Node _ _ (Node _ _ _)) = Leaf"

fun findMin :: "'a :: linorder tree \<Rightarrow> 'a option" where
  "findMin Leaf = None"
| "findMin (Node _ x _) = Some x"

fun merge :: "'a :: linorder tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
  "merge Leaf h = h"
| "merge h Leaf = h"
| "merge (Node lx x Leaf) (Node ly y Leaf) = link (Node lx x (Node ly y Leaf))"
| "merge _ _ = undefined"

fun insert :: "'a \<Rightarrow> 'a :: linorder tree \<Rightarrow> 'a tree" where
  "insert x h = merge (Node Leaf x Leaf) h"

fun oneRoot :: "'a :: linorder tree \<Rightarrow> bool" where
"oneRoot h = (case h of Leaf \<Rightarrow> True | Node _ _ r \<Rightarrow> r = Leaf)"

fun ld :: "nat \<Rightarrow> real" where
  "ld x = (if x = 0 then 0 else log 2 x)"

fun \<Phi> :: "'a tree \<Rightarrow> real" where
  "\<Phi> Leaf = 0"
| "\<Phi> (Node lx _ rx) = \<Phi> lx + \<Phi> rx + ld (1 + size lx + size rx)"

declare algebra_simps[simp]

lemma add_log_log1: assumes "x > 0" "y > 0" shows "1 + log 2 x + log 2 y < 2 * log 2 (x+y)"
proof -
  have 1: "2*x*y < (x+y)^2" using assms by(simp add: numeral_eq_Suc add_pos_pos)
  show ?thesis apply(rule powr_less_cancel_iff[of 2, THEN iffD1])
    using assms 1 by (simp_all add: powr_add log_powr[symmetric] powr_numeral)
qed
lemma link_size[simp]: "size (link h) = size h" 
  by (cases h rule: link.cases) simp_all

lemma firstpass_size[simp]: "size (firstpass h) = size h" 
  by (induct h rule: firstpass.induct) simp_all

lemma secondpass_size: " size (secondpass h) = size h" 
  by (induct h rule: secondpass.induct) simp_all

lemma merge_size[simp]: "oneRoot h1 \<Longrightarrow> oneRoot h2 \<Longrightarrow> size (merge h1 h2) = size h1 + size h2"
  by(simp split: tree.splits)

lemma link_struct: "\<exists>la a. link(Node lx x (Node ly y ry)) = Node la a ry" 
  by simp

lemma firstpass_struct: "\<exists>la a ra. firstpass(Node lx x rx) = Node la a ra" 
  by (cases rx) simp_all

lemma secondpass_struct: "\<exists>la a. secondpass(Node lx x rx) = Node la a Leaf" 
  by (induction rx arbitrary: x lx rule: secondpass.induct) 
  (simp, metis secondpass.simps(2) link_struct)

lemma \<Delta>\<Phi>\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t: "oneRoot h \<Longrightarrow> \<Phi> (insert x h) - \<Phi> h \<le> ld (size h + 1)"
  by(simp split: tree.splits)

lemma \<Delta>\<Phi>\<^sub>m\<^sub>e\<^sub>r\<^sub>g\<^sub>e: assumes "oneRoot h1 \<and> oneRoot h2" 
  shows "\<Phi> (merge h1 h2) - \<Phi> h1 - \<Phi> h2 \<le> 2*ld (size h1 + size h2)" 
proof (cases h1)
  case [simp]: (Node lx x rx)
  thus ?thesis
  proof (cases h2)
    case [simp]: (Node ly y ry)
    let ?h = "Node lx x (Node ly y Leaf)"
    have "\<Phi> (link ?h) - \<Phi> ?h \<le> ld (1 + size lx + size ly)" by simp
    also have "\<dots> \<le> ld (size h1 + size h2)" by simp
    moreover have "\<Phi> ?h - \<Phi> h1 - \<Phi> h2 \<le> \<dots>" using assms by simp
    ultimately have "\<Phi> (link ?h) - \<Phi> h1 - \<Phi> h2 \<le> 2*\<dots>" by linarith
    thus ?thesis using assms by simp
  qed simp
qed simp

fun sum_ub :: "'a tree \<Rightarrow> real" where
  "sum_ub Leaf = 0"
| "sum_ub (Node _ _ Leaf) = 0"
| "sum_ub (Node lx _ (Node ly _ Leaf)) = 2*ld(2 + size lx + size ly)" 
| "sum_ub (Node lx _ (Node ly _ ry)) = 2*ld(2 + size lx + size ly + size ry) 
    - 2*ld(size ry) - 1 + sum_ub ry"

lemma \<Delta>\<Phi>\<^sub>f\<^sub>i\<^sub>r\<^sub>s\<^sub>t\<^sub>p\<^sub>a\<^sub>s\<^sub>s_sum_ub: "\<Phi> (firstpass h) - \<Phi> h  \<le> sum_ub h"
proof (induction h rule: sum_ub.induct)
  case (3 lx x ly y)
  have "ld (1 + size lx + size ly) - ld (1 + size ly) \<le> ld(1 + size lx + size ly)" by simp
  also have "\<dots> \<le> ld(2 + size lx + size ly)" by simp
  also have "\<dots> \<le> 2*\<dots>" by simp
  finally show ?case by simp
next
  case (4 lx x ly y lz z rz)
  let ?ry = "Node lz z rz"
  let ?rx = "Node ly y ?ry"
  let ?h = "Node lx x ?rx"
  have "\<Phi> (firstpass ?h) - \<Phi> ?h  
    \<le> ld(1 + size lx + size ly) - ld(1 + size ly + size ?ry) + sum_ub ?ry" using "4.IH" by simp
  also have "ld(1 + size lx + size ly) - ld(1 + size ly + size ?ry) 
    \<le> 2*ld (size ?h) - 2*ld(size ?ry) - 1"
  proof -
    have "ld (1 + size lx + size ly) + ld (size ?ry) - 2*ld (size ?h) 
      = log 2 ((1 + size lx + size ly)/(size ?h) ) + log 2 (size ?ry / size ?h)"
      by (simp add: log_divide)
    also have "\<dots> \<le> -1" 
    proof -
      have "1 + \<dots>
        \<le> 2*log 2 ((1 + size lx + size ly) / size ?h +  size ?ry / size ?h)"  
        using add_log_log1 [of "(1 + size lx + size ly) / size ?h" "(size ?ry / size ?h)"] by simp
      also have "\<dots> \<le> 0" by (simp del: algebra_simps add: field_simps)
      finally show ?thesis by linarith
    qed 
    finally have "log 2 (1 + size lx + size ly) + log 2 (size ?ry) + 1
      \<le>  2*log 2 (size ?h)" by simp
    moreover have "log 2 (size ?ry) \<le> log 2 (size ?rx)" by simp   
    ultimately have "log 2 (1 + size lx + size ly) - \<dots> 
      \<le>  2*log 2 (size ?h) - 2*log 2 (size ?ry) - 1" by linarith
    thus ?thesis by simp
  qed
  finally show ?case by simp
qed simp_all

lemma \<Delta>\<Phi>\<^sub>f\<^sub>i\<^sub>r\<^sub>s\<^sub>t\<^sub>p\<^sub>a\<^sub>s\<^sub>s: "\<Phi> (firstpass h) - \<Phi> h \<le> 2*ld(size h) - countTrees h/2 + 1"
proof - 
  have "\<Phi> (firstpass h) - \<Phi> h \<le> sum_ub h" using \<Delta>\<Phi>\<^sub>f\<^sub>i\<^sub>r\<^sub>s\<^sub>t\<^sub>p\<^sub>a\<^sub>s\<^sub>s_sum_ub .
  also have "2*sum_ub h \<le> 4*ld(size h) - countTrees h + 2" 
    by (induct h rule: sum_ub.induct) simp_all
  finally show ?thesis by fastforce
qed

lemma \<Delta>\<Phi>\<^sub>s\<^sub>e\<^sub>c\<^sub>o\<^sub>n\<^sub>d\<^sub>p\<^sub>a\<^sub>s\<^sub>s: "\<Phi> (secondpass h) - \<Phi> h \<le> ld (size h)"
proof (induction h rule: secondpass.induct)
  case (2 lx x rx)
  thus ?case 
  proof (cases rx)
    case [simp]: (Node ly y ry)
    let ?h = "Node lx x rx"
    obtain la a where 1: "secondpass rx = Node la a Leaf" using secondpass_struct by force
    hence "size \<dots> = size rx" using secondpass_size by metis
    hence "\<Phi> (secondpass ?h) - \<Phi> ?h  
      \<le> ld(size ?h) - ld \<dots> + \<Phi> (secondpass rx) - \<Phi> rx" using 1 by simp 
    thus ?thesis using "2.IH" by simp
  qed simp
qed simp

lemma \<Delta>\<Phi>\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e\<^sub>M\<^sub>i\<^sub>n:  "\<Phi> (deleteMin (Node lx x Leaf)) - \<Phi> (Node lx x Leaf) 
  \<le> 3*ld(size lx) - countTrees lx / 2 + 1"
proof -
  let ?h = "Node lx x Leaf"
  let ?\<Delta>\<Phi>\<^sub>1 = "\<Phi> lx - \<Phi> ?h" 
  let ?\<Delta>\<Phi>\<^sub>2 = "\<Phi>(secondpass(firstpass lx)) - \<Phi> lx"
  let ?\<Delta>\<Phi> = "\<Phi> (deleteMin ?h) - \<Phi> ?h"
  have "\<Phi>(secondpass(firstpass lx)) - \<Phi> (firstpass lx) \<le> ld (size lx)" 
    using \<Delta>\<Phi>\<^sub>s\<^sub>e\<^sub>c\<^sub>o\<^sub>n\<^sub>d\<^sub>p\<^sub>a\<^sub>s\<^sub>s[of "firstpass lx"] by (metis firstpass_size)
  moreover have "\<Phi> (firstpass lx) - \<Phi> lx \<le>  2*\<dots> - countTrees lx / 2 + 1"
    using \<Delta>\<Phi>\<^sub>f\<^sub>i\<^sub>r\<^sub>s\<^sub>t\<^sub>p\<^sub>a\<^sub>s\<^sub>s by blast
  moreover have "?\<Delta>\<Phi>\<^sub>1 \<le> 0" by simp
  moreover have "?\<Delta>\<Phi> = ?\<Delta>\<Phi>\<^sub>1 + ?\<Delta>\<Phi>\<^sub>2" by simp
  ultimately show ?thesis by linarith
qed

lemma merge_oneRoot: "oneRoot h1 \<Longrightarrow> oneRoot h2 \<Longrightarrow> oneRoot (merge h1 h2)"
  by(simp split: tree.splits)

lemma insert_oneRoot: "oneRoot h \<Longrightarrow> oneRoot (insert x h)"
  by(simp split: tree.splits)

lemma deleteMin_oneRoot: assumes "oneRoot h" shows "oneRoot (deleteMin h)"
proof (cases h)
  case [simp]: (Node lx x rx)
  have "rx = Leaf" using assms by simp
  thus ?thesis 
  proof (cases lx)
    case (Node ly y ry)
    then obtain la a ra where "firstpass lx = Node a la ra" using firstpass_struct by blast
    moreover obtain lb b where "secondpass \<dots> = Node b lb Leaf"
      using secondpass_struct by blast
    ultimately show ?thesis using assms by simp
  qed simp
qed simp

lemma firstpass_countTrees: "countTrees (firstpass h) \<le> countTrees h"
  by (induct h rule: firstpass.induct) simp_all

datatype 'a cmd = Insert 'a | Delmin | FindMin

fun nxt :: "'a :: linorder cmd \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
  "nxt FindMin h = h"
| "nxt Delmin h = deleteMin h"
| "nxt (Insert x) h = insert x h"

fun t\<^sub>f\<^sub>i\<^sub>r\<^sub>s\<^sub>t\<^sub>p\<^sub>a\<^sub>s\<^sub>s :: "'a tree \<Rightarrow> real" where
  "t\<^sub>f\<^sub>i\<^sub>r\<^sub>s\<^sub>t\<^sub>p\<^sub>a\<^sub>s\<^sub>s Leaf = 1"
| "t\<^sub>f\<^sub>i\<^sub>r\<^sub>s\<^sub>t\<^sub>p\<^sub>a\<^sub>s\<^sub>s (Node _ _ Leaf) = 1"
| "t\<^sub>f\<^sub>i\<^sub>r\<^sub>s\<^sub>t\<^sub>p\<^sub>a\<^sub>s\<^sub>s (Node _ _ (Node _ _ ry)) = 1 + t\<^sub>f\<^sub>i\<^sub>r\<^sub>s\<^sub>t\<^sub>p\<^sub>a\<^sub>s\<^sub>s ry"

fun t\<^sub>s\<^sub>e\<^sub>c\<^sub>o\<^sub>n\<^sub>d\<^sub>p\<^sub>a\<^sub>s\<^sub>s :: "'a tree \<Rightarrow> real" where
 "t\<^sub>s\<^sub>e\<^sub>c\<^sub>o\<^sub>n\<^sub>d\<^sub>p\<^sub>a\<^sub>s\<^sub>s Leaf = 1"
| "t\<^sub>s\<^sub>e\<^sub>c\<^sub>o\<^sub>n\<^sub>d\<^sub>p\<^sub>a\<^sub>s\<^sub>s (Node _ _ rx) = 1 + t\<^sub>s\<^sub>e\<^sub>c\<^sub>o\<^sub>n\<^sub>d\<^sub>p\<^sub>a\<^sub>s\<^sub>s rx"

fun t :: "'a :: linorder cmd \<Rightarrow> 'a tree \<Rightarrow> real" where
  "t FindMin _ = 1"
| "t Delmin Leaf = 1"
| "t Delmin (Node lx _  _) = 1 + t\<^sub>s\<^sub>e\<^sub>c\<^sub>o\<^sub>n\<^sub>d\<^sub>p\<^sub>a\<^sub>s\<^sub>s (firstpass lx) + t\<^sub>f\<^sub>i\<^sub>r\<^sub>s\<^sub>t\<^sub>p\<^sub>a\<^sub>s\<^sub>s lx"
| "t (Insert a) _ = 1"

fun U :: "'a :: linorder cmd \<Rightarrow> 'a tree \<Rightarrow> real" where
  "U FindMin _ = 1"
| "U (Insert a) h = 1 + 4*log 2 (size h + 1)"
| "U Delmin h = 4*3*log 2 (size h + 1) + 7"

interpretation pairing: amor where 
init = "Leaf" and nxt = "nxt" and t = "t" and inv = "oneRoot" and \<Phi> = "\<lambda> x. 4*\<Phi> x" and U = "U"
proof
  case goal2 thus ?case 
    using insert_oneRoot deleteMin_oneRoot by (cases f) simp_all  
  case goal3 show ?case by (induct s) simp_all 
  case goal5 show ?case 
  proof (cases f)
    case [simp]: (Insert x)
    have "\<Phi> (insert x s) - \<Phi> s \<le> ld (1 + size s)" using \<Delta>\<Phi>\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t goal5 by auto
    thus ?thesis by simp
  next
    case [simp]: Delmin
    thus ?thesis
    proof (cases s)
      case [simp]: (Node lx x rx)
      have "t\<^sub>s\<^sub>e\<^sub>c\<^sub>o\<^sub>n\<^sub>d\<^sub>p\<^sub>a\<^sub>s\<^sub>s (firstpass lx) + t\<^sub>f\<^sub>i\<^sub>r\<^sub>s\<^sub>t\<^sub>p\<^sub>a\<^sub>s\<^sub>s lx \<le> 2 + 2*countTrees lx"
        by (induct lx rule: firstpass.induct) simp_all
      hence  "t f s \<le> 1 + \<dots>" by simp
      moreover have  "\<Phi> (deleteMin s) - \<Phi> s \<le> 3*ld(size lx) - countTrees lx / 2 + 1"
        using  \<Delta>\<Phi>\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e\<^sub>M\<^sub>i\<^sub>n goal5 by fastforce
      moreover have "ld(size lx) \<le> ld (size s + 1)" by simp
      ultimately show ?thesis by simp 
    qed simp
  qed simp
qed simp_all

end
