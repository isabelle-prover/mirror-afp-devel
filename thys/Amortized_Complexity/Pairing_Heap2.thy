(* Author: Hauke Brinkop (w/ Tobias Nipkow) *)

section {* Amortized Analysis of Pairing Heaps *}

subsection {* Binary Tree Representation *}

theory Pairing_Heap2
imports  
  "~~/src/HOL/Library/Tree"
  Amortized_Framework
  Priority_Queue_ops_meld2
  Lemmas_log
begin

text{* Pairing heaps were invented by Fredman, Sedgewick, Sleator and Tarjan
\cite{FredmanSST86}. In this theory we verify their logarithmic bound on the
amortized complexity of pairing heaps. *}

fun link :: "'a :: linorder tree \<Rightarrow> 'a tree" where
  "link Leaf = Leaf"
| "link (Node lx x Leaf) = Node lx x Leaf"
| "link (Node lx x (Node ly y ry)) = 
    (if x < y then Node (Node ly y lx) x ry else Node (Node lx x ly) y ry)"

fun pass\<^sub>1 :: "'a :: linorder tree \<Rightarrow> 'a tree" where
  "pass\<^sub>1 Leaf = Leaf"
| "pass\<^sub>1 (Node lx x Leaf) = Node lx x Leaf" 
| "pass\<^sub>1 (Node lx x (Node ly y ry)) = link (Node lx x (Node ly y (pass\<^sub>1 ry)))"

fun len :: "'a tree \<Rightarrow> nat" where 
  "len Leaf = 0"
| "len (Node _ _ r) = len r + 1"

fun pass\<^sub>2 :: "'a :: linorder tree \<Rightarrow> 'a tree" where
  "pass\<^sub>2 Leaf = Leaf"
| "pass\<^sub>2 (Node l x r) = link(Node l x (pass\<^sub>2 r))"

fun mergepairs :: "'a :: linorder tree \<Rightarrow> 'a tree" where
  "mergepairs Leaf = Leaf"
| "mergepairs (Node lx x Leaf) = Node lx x Leaf" 
| "mergepairs (Node lx x (Node ly y ry)) =
   link (link (Node lx x (Node ly y (mergepairs ry))))"

fun del_min :: "'a :: linorder tree \<Rightarrow> 'a tree" where
  "del_min Leaf = Leaf"
| "del_min (Node l _ Leaf) = pass\<^sub>2 (pass\<^sub>1 l)"

fun meld :: "'a :: linorder tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
  "meld Leaf h = h"
| "meld h Leaf = h"
| "meld (Node lx x Leaf) (Node ly y Leaf) = link (Node lx x (Node ly y Leaf))"

fun insert :: "'a \<Rightarrow> 'a :: linorder tree \<Rightarrow> 'a tree" where
  "insert x h = meld (Node Leaf x Leaf) h"

fun is_root :: "'a :: linorder tree \<Rightarrow> bool" where
  "is_root h = (case h of Leaf \<Rightarrow> True | Node l x r \<Rightarrow> r = Leaf)"

fun \<Phi> :: "'a tree \<Rightarrow> real" where
  "\<Phi> Leaf = 0"
| "\<Phi> (Node l _ r) = \<Phi> l + \<Phi> r + log 2 (size l + size r + 1)"

lemma link_size[simp]: "size (link hs) = size hs" 
  by (cases hs rule: link.cases) simp_all

lemma size_pass\<^sub>1: "size (pass\<^sub>1 hs) = size hs" 
  by (induct hs rule: pass\<^sub>1.induct) simp_all

lemma size_pass\<^sub>2: "size (pass\<^sub>2 hs) = size hs" 
  by (induct hs rule: pass\<^sub>2.induct) simp_all

lemma size_meld[simp]: 
  "is_root h1 \<Longrightarrow> is_root h2 \<Longrightarrow> size (meld h1 h2) = size h1 + size h2"
  by (simp split: tree.splits)

lemma link_struct: "\<exists>la a. link (Node lx x (Node ly y ry)) = Node la a ry" 
  by simp

lemma pass\<^sub>1_struct: "\<exists>la a ra. pass\<^sub>1 (Node lx x rx) = Node la a ra" 
  by (cases rx) simp_all

lemma pass\<^sub>2_struct: "\<exists>la a. pass\<^sub>2 (Node lx x rx) = Node la a Leaf" 
  by (induction rx arbitrary: x lx rule: pass\<^sub>2.induct) 
  (simp, metis pass\<^sub>2.simps(2) link_struct)

lemma mergepairs_pass12: "mergepairs hs = pass\<^sub>2 (pass\<^sub>1 hs)"
by (induction hs rule: mergepairs.induct) auto

lemma \<Delta>\<Phi>_insert: "is_root h \<Longrightarrow> \<Phi> (insert x h) - \<Phi> h \<le> log 2  (size h + 1)"
  by (simp split: tree.splits)

lemma \<Delta>\<Phi>_meld:
  assumes "h1 = Node lx x Leaf" "h2 = Node ly y Leaf" 
  shows "\<Phi> (meld h1 h2) - \<Phi> h1 - \<Phi> h2 \<le> 2*log 2 (size h1 + size h2)" 
proof -
  let ?hs = "Node lx x (Node ly y Leaf)"
  have "\<Phi> (link ?hs) - \<Phi> ?hs \<le> log 2  (size lx + size ly + 1)" by (simp add: algebra_simps)
  also have "\<dots> \<le> log 2  (size h1 + size h2)" by (simp add: assms)
  moreover have "\<Phi> ?hs - \<Phi> h1 - \<Phi> h2 \<le> \<dots>" using assms by simp
  ultimately have "\<Phi> (link ?hs) - \<Phi> h1 - \<Phi> h2 \<le> 2*\<dots>" by linarith
  thus ?thesis using assms by simp
qed

fun upperbound :: "'a tree \<Rightarrow> real" where
  "upperbound Leaf = 0"
| "upperbound (Node _ _ Leaf) = 0"
| "upperbound (Node lx _ (Node ly _ Leaf)) = 2*log 2 (size lx + size ly + 2)" 
| "upperbound (Node lx _ (Node ly _ ry)) = 2*log 2 (size lx + size ly + size ry + 2) 
    - 2*log 2 (size ry) - 2 + upperbound ry"

lemma \<Delta>\<Phi>_pass1_upperbound: "\<Phi> (pass\<^sub>1 hs) - \<Phi> hs  \<le> upperbound hs"
proof (induction hs rule: upperbound.induct)
  case (3 lx x ly y)
  have "log 2  (size lx + size ly + 1) - log 2  (size ly + 1) 
    \<le> log 2 (size lx + size ly + 1)" by simp
  also have "\<dots> \<le> log 2 (size lx + size ly + 2)" by simp
  also have "\<dots> \<le> 2*\<dots>" by simp
  finally show ?case by (simp add: algebra_simps)
next
  case (4 lx x ly y lz z rz)
  let ?ry = "Node lz z rz"
  let ?rx = "Node ly y ?ry"
  let ?h = "Node lx x ?rx"
  let ?t ="log 2 (size lx + size ly + 1) - log 2 (size ly + size ?ry + 1)"
  have "\<Phi> (pass\<^sub>1 ?h) - \<Phi> ?h \<le> ?t + upperbound ?ry" 
    using "4.IH" by (simp add: size_pass\<^sub>1 algebra_simps)
  also have "?t \<le> 2*log 2  (size ?h) - 2*log 2 (size ?ry) - 2"
  proof -
    have "log 2 (size lx + size ly + 1) + log 2  (size ?ry) - 2*log 2 (size ?h) 
      = log 2 ((size lx + size ly + 1)/(size ?h) ) + log 2 (size ?ry / size ?h)"
      (is "_ = log 2 ?t1 + log 2 ?t2") by (simp add: log_divide)
    also have "\<dots> \<le> -2" 
    proof -
      have "2 + \<dots> \<le> 2*log 2 (?t1 + ?t2)"
        using ld_sum_inequality [of "?t1" "?t2"] by simp
      also have "\<dots> \<le> 0" by (simp add: field_simps del: of_nat_Suc)
      finally show ?thesis by linarith
    qed 
    finally have "log 2 (size lx + size ly + 1) + log 2 (size ?ry) + 2
      \<le>  2*log 2 (size ?h)" by simp
    moreover have "log 2 (size ?ry) \<le> log 2 (size ?rx)" by simp  
    ultimately have "log 2 (size lx + size ly + 1) - \<dots> 
      \<le>  2*log 2 (size ?h) - 2*log 2 (size ?ry) - 2" by linarith
    thus ?thesis by simp
  qed
  finally show ?case by (simp add: algebra_simps)
qed simp_all

lemma \<Delta>\<Phi>_pass1: assumes "hs \<noteq> Leaf"
  shows "\<Phi> (pass\<^sub>1 hs) - \<Phi> hs \<le> 2*log 2 (size hs) - len hs + 2"
proof -
  from assms have "upperbound hs \<le> 2*log 2 (size hs) - len hs + 2" 
    by (induct hs rule: upperbound.induct) (simp_all add: algebra_simps)
  thus ?thesis using \<Delta>\<Phi>_pass1_upperbound [of "hs"] order_trans by blast
qed

lemma \<Delta>\<Phi>_pass2: "hs \<noteq> Leaf \<Longrightarrow> \<Phi> (pass\<^sub>2 hs) - \<Phi> hs \<le> log 2 (size hs)"
proof (induction hs rule: pass\<^sub>2.induct)
  case (2 lx x rx)
  thus ?case 
  proof (cases rx)
    case *: (Node ly y ry)
    let ?h = "Node lx x rx"
    obtain la a where **: "pass\<^sub>2 rx = Node la a Leaf" 
      using pass\<^sub>2_struct * by force
    hence "size \<dots> = size rx" using size_pass\<^sub>2 by metis
    hence "\<Phi> (pass\<^sub>2 ?h) - \<Phi> ?h  
      \<le> log 2 (size ?h) - log 2  \<dots> + \<Phi> (pass\<^sub>2 rx) - \<Phi> rx"
      using * ** by (simp add: algebra_simps) 
    thus ?thesis using "2.IH" * by simp
  qed simp
qed simp

lemma \<Delta>\<Phi>_mergepairs: assumes "hs \<noteq> Leaf"
  shows "\<Phi> (mergepairs hs) - \<Phi> hs \<le> 3 * log 2 (size hs) - len hs + 2"
proof -
  have "pass\<^sub>1 hs \<noteq> Leaf" by (metis assms size_0_iff_Leaf size_pass\<^sub>1)
  with assms \<Delta>\<Phi>_pass1[of hs] \<Delta>\<Phi>_pass2[of "pass\<^sub>1 hs"]
  show ?thesis by (auto simp add: size_pass\<^sub>1 mergepairs_pass12)
qed

lemma \<Delta>\<Phi>_del_min: "lx \<noteq> Leaf \<Longrightarrow>
  \<Phi> (del_min (Node lx x Leaf)) - \<Phi> (Node lx x Leaf) 
  \<le> 3*log 2 (size lx) - len lx + 2"
proof -
  let ?h = "Node lx x Leaf"
  let ?\<Delta>\<Phi>\<^sub>1 = "\<Phi> lx - \<Phi> ?h" 
  let ?\<Delta>\<Phi>\<^sub>2 = "\<Phi>(pass\<^sub>2(pass\<^sub>1 lx)) - \<Phi> lx"
  let ?\<Delta>\<Phi> = "\<Phi> (del_min ?h) - \<Phi> ?h"
  have "lx \<noteq> Leaf \<Longrightarrow> \<Phi>(pass\<^sub>2(pass\<^sub>1 lx)) - \<Phi> (pass\<^sub>1 lx) \<le> log 2  (size lx)" 
    using \<Delta>\<Phi>_pass2 [of "pass\<^sub>1 lx"] 
    size_0_iff_Leaf size_pass\<^sub>1 by metis
  moreover have "lx \<noteq> Leaf \<Longrightarrow> \<Phi> (pass\<^sub>1 lx) - \<Phi> lx \<le>  2*\<dots> - len lx + 2" 
    using \<Delta>\<Phi>_pass1 by metis
  moreover have "?\<Delta>\<Phi> \<le> ?\<Delta>\<Phi>\<^sub>2" by simp
  moreover assume "lx \<noteq> Leaf"
  ultimately show ?thesis by linarith
qed

lemma is_root_meld:
  "is_root h1 \<Longrightarrow> is_root h2 \<Longrightarrow> is_root (meld h1 h2)"
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

lemma pass\<^sub>1_len: "len (pass\<^sub>1 h) \<le> len h"
by (induct h rule: pass\<^sub>1.induct) simp_all

fun exec :: "'a :: linorder op\<^sub>p\<^sub>q \<Rightarrow> 'a tree list \<Rightarrow> 'a tree" where
"exec Empty [] = Leaf" | 
"exec Del_min [h] = del_min h" |
"exec (Insert x) [h] = insert x h" |
"exec Meld [h1,h2] = meld h1 h2"

fun t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 :: "'a tree \<Rightarrow> nat" where
  "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 Leaf = 1"
| "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 (Node _ _ Leaf) = 1"
| "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 (Node _ _ (Node _ _ ry)) = t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 ry + 1"

fun t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2 :: "'a tree \<Rightarrow> nat" where
  "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2 Leaf = 1"
| "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2 (Node _ _ rx) = t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2 rx + 1"

fun cost :: "'a :: linorder op\<^sub>p\<^sub>q \<Rightarrow> 'a tree list \<Rightarrow> nat" where
  "cost Empty [] = 1"
| "cost Del_min [Leaf] = 1"
| "cost Del_min [Node lx _  _] = t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2 (pass\<^sub>1 lx) + t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 lx"
| "cost (Insert a) _ = 1"
| "cost Meld _ = 1"

fun U :: "'a :: linorder op\<^sub>p\<^sub>q \<Rightarrow> 'a tree list \<Rightarrow> real" where
  "U Empty [] = 1"
| "U (Insert a) [h] = log 2 (size h + 1) + 1"
| "U Del_min [h] = 3*log 2 (size h + 1) + 4"
| "U Meld [h1,h2] = 2*log 2 (size h1 + size h2 + 1) + 1"

interpretation Amortized
where arity = arity and exec = exec and cost = cost and inv = is_root 
and \<Phi> = \<Phi> and U = U
proof
  case goal1 thus ?case using is_root_insert is_root_del_min is_root_meld
    by (cases f) (auto simp: numeral_eq_Suc)
next
  case goal2 show ?case by (induct s) simp_all
next
  case goal3 thus ?case by(cases f) auto
next
  case goal4 show ?case 
  proof (cases f)
    case Empty with goal4 show ?thesis by(auto)
  next
    case (Insert x)
    then obtain h where "ss = [h]" "is_root h" using goal4 by auto
    thus ?thesis using Insert \<Delta>\<Phi>_insert goal4 by auto
  next
    case [simp]: (Del_min)
    then obtain h where [simp]: "ss = [h]" using goal4 by auto
    show ?thesis
    proof (cases h)
      case [simp]: (Node lx x rx)
      have "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2 (pass\<^sub>1 lx) + t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1 lx \<le> len lx + 2"
        by (induct lx rule: pass\<^sub>1.induct) simp_all
      hence "cost f ss \<le> \<dots>" by simp 
      moreover have "\<Phi> (del_min h) - \<Phi> h \<le> 3*log 2 (size h + 1) - len lx + 2"
      proof (cases lx)
        case [simp]: (Node ly y ry) 
        have "\<Phi> (del_min h) - \<Phi> h \<le> 3*log 2 (size lx) - len lx + 2"
          using  \<Delta>\<Phi>_del_min[of "lx" "x"] goal4 by simp
        also have "\<dots> \<le> 3*log 2 (size h + 1) - len lx + 2" by fastforce
        finally show ?thesis by blast
      qed (insert goal4, simp)
      ultimately show ?thesis by auto
    qed simp
  next
    case [simp]: Meld
    then obtain h1 h2 where [simp]: "ss = [h1,h2]" and 1: "is_root h1" "is_root h2"
      using goal4 by (auto simp: numeral_eq_Suc)
    show ?thesis
    proof (cases h1)
      case Leaf thus ?thesis by (cases h2) auto
    next
      case h1: Node
      show ?thesis
      proof (cases h2)
        case Leaf thus ?thesis using h1 by simp
      next
        case h2: Node
        have "\<Phi> (meld h1 h2) - \<Phi> h1 - \<Phi> h2 \<le> 2 * log 2 (real (size h1 + size h2))"
          apply(rule \<Delta>\<Phi>_meld) using h1 h2 1 by auto
        also have "\<dots> \<le> 2 * log 2 (size h1 + size h2 + 1)" by (simp add: h1)
        finally show ?thesis by(simp)
      qed
    qed
  qed
qed

end
