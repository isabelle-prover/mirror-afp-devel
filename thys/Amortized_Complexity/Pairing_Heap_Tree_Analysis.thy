(* Author: Hauke Brinkop and Tobias Nipkow *)

section \<open>Pairing Heaps\<close>

subsection \<open>Binary Tree Representation\<close>

theory Pairing_Heap_Tree_Analysis
imports  
  "HOL-Data_Structures.Define_Time_Function"
  Pairing_Heap.Pairing_Heap_Tree
  Amortized_Framework
  Priority_Queue_ops_merge
  Lemmas_log
begin

text
\<open>Verification of logarithmic bounds on the amortized complexity of
pairing heaps \<^cite>\<open>"FredmanSST86" and "Brinkop"\<close>.\<close>


subsubsection \<open>Analysis\<close>

fun len :: "'a tree \<Rightarrow> nat" where 
  "len Leaf = 0"
| "len (Node _ _ r) = 1 + len r"

fun \<Phi> :: "'a tree \<Rightarrow> real" where
  "\<Phi> Leaf = 0"
| "\<Phi> (Node l x r) = log 2 (size (Node l x r)) + \<Phi> l + \<Phi> r"

lemma link_size[simp]: "size (link hp) = size hp" 
  by (cases hp rule: link.cases) simp_all

lemma size_pass\<^sub>1: "size (pass\<^sub>1 hp) = size hp" 
  by (induct hp rule: pass\<^sub>1.induct) simp_all

lemma size_pass\<^sub>2: "size (pass\<^sub>2 hp) = size hp" 
  by (induct hp rule: pass\<^sub>2.induct) simp_all

lemma size_merge: 
  "is_root h1 \<Longrightarrow> is_root h2 \<Longrightarrow> size (merge h1 h2) = size h1 + size h2"
  by (simp split: tree.splits)

lemma \<Delta>\<Phi>_insert: "is_root hp \<Longrightarrow> \<Phi> (insert x hp) - \<Phi> hp \<le> log 2  (size hp + 1)"
  by (simp split: tree.splits)

lemma \<Delta>\<Phi>_merge:
  assumes "h1 = Node hs1 x1 Leaf" "h2 = Node hs2 x2 Leaf" 
  shows "\<Phi> (merge h1 h2) - \<Phi> h1 - \<Phi> h2 \<le> log 2 (size h1 + size h2) + 1" 
proof -
  let ?hs = "Node hs1 x1 (Node hs2 x2 Leaf)"
  have "\<Phi> (merge h1 h2) = \<Phi> (link ?hs)" using assms by simp
  also have "\<dots> = \<Phi> hs1 + \<Phi> hs2 + log 2 (size hs1 + size hs2 + 1) + log 2 (size hs1 + size hs2 + 2)"
    by (simp add: algebra_simps)
  also have "\<dots> = \<Phi> hs1 + \<Phi> hs2 + log 2 (size hs1 + size hs2 + 1) + log 2 (size h1 + size h2)"
     using assms by simp
  finally have "\<Phi> (merge h1 h2) = \<dots>" .
  have "\<Phi> (merge h1 h2) - \<Phi> h1 - \<Phi> h2 =
   log 2 (size hs1 + size hs2 + 1) + log 2 (size h1 + size h2)
   - log 2 (size hs1 + 1) - log 2 (size hs2 + 1)"
     using assms by (simp add: algebra_simps)
  also have "\<dots> \<le> log 2 (size h1 + size h2) + 1"
    using ld_le_2ld[of "size hs1" "size hs2"] assms by (simp add: algebra_simps)
  finally show ?thesis .
qed

fun ub_pass\<^sub>1 :: "'a tree \<Rightarrow> real" where
  "ub_pass\<^sub>1 (Node _ _ Leaf) = 0"
| "ub_pass\<^sub>1 (Node hs1 _ (Node hs2 _ Leaf)) = 2*log 2 (size hs1 + size hs2 + 2)" 
| "ub_pass\<^sub>1 (Node hs1 _ (Node hs2 _ hs)) = 2*log 2 (size hs1 + size hs2 + size hs + 2) 
    - 2*log 2 (size hs) - 2 + ub_pass\<^sub>1 hs"

lemma \<Delta>\<Phi>_pass1_ub_pass1: "hs \<noteq> Leaf \<Longrightarrow> \<Phi> (pass\<^sub>1 hs) - \<Phi> hs  \<le> ub_pass\<^sub>1 hs"
proof (induction hs rule: ub_pass\<^sub>1.induct)
  case (2 lx x ly y)
  have "log 2  (size lx + size ly + 1) - log 2  (size ly + 1) 
    \<le> log 2 (size lx + size ly + 1)" by simp
  also have "\<dots> \<le> log 2 (size lx + size ly + 2)" by simp
  also have "\<dots> \<le> 2*\<dots>" by simp
  finally show ?case by (simp add: algebra_simps)
next
  case (3 lx x ly y lz z rz)
  let ?ry = "Node lz z rz"
  let ?rx = "Node ly y ?ry"
  let ?h = "Node lx x ?rx"
  let ?t ="log 2 (size lx + size ly + 1) - log 2 (size ly + size ?ry + 1)"
  have "\<Phi> (pass\<^sub>1 ?h) - \<Phi> ?h \<le> ?t + ub_pass\<^sub>1 ?ry" 
    using "3.IH" by (simp add: size_pass\<^sub>1 algebra_simps)
  moreover have "log 2 (size lx + size ly + 1) + 2 * log 2 (size ?ry) + 2
    \<le> 2 * log 2 (size ?h) + log 2 (size ly + size ?ry + 1)" (is "?l \<le> ?r")
  proof -
    have "?l \<le> 2 * log 2 (size lx + size ly + size ?ry + 1) + log 2 (size ?ry)"
      using ld_sum_inequality [of "size lx + size ly + 1" "size ?ry"] by simp
    also have "\<dots> \<le> 2 * log 2 (size lx + size ly + size ?ry + 2) + log 2 (size ?ry)"
      by simp
    also have "\<dots> \<le> ?r" by simp
    finally show ?thesis .
  qed
  ultimately show ?case by simp
qed simp_all

lemma \<Delta>\<Phi>_pass1: assumes "hs \<noteq> Leaf"
  shows "\<Phi> (pass\<^sub>1 hs) - \<Phi> hs \<le> 2*log 2 (size hs) - len hs + 2"
proof -
  from assms have "ub_pass\<^sub>1 hs \<le> 2*log 2 (size hs) - len hs + 2" 
    by (induct hs rule: ub_pass\<^sub>1.induct) (simp_all add: algebra_simps)
  thus ?thesis using \<Delta>\<Phi>_pass1_ub_pass1 [OF assms] order_trans by blast
qed

lemma \<Delta>\<Phi>_pass2: "hs \<noteq> Leaf \<Longrightarrow> \<Phi> (pass\<^sub>2 hs) - \<Phi> hs \<le> log 2 (size hs)"
proof (induction hs)
  case (Node lx x rx)
  thus ?case 
  proof (cases rx)
    case 1: (Node ly y ry)
    let ?h = "Node lx x rx"
    obtain la a where 2: "pass\<^sub>2 rx = Node la a Leaf" 
      using pass\<^sub>2_struct 1 by force
    hence 3: "size rx = size \<dots>" using size_pass\<^sub>2 by metis
    have link: "\<Phi>(link(Node lx x (pass\<^sub>2 rx))) - \<Phi> lx - \<Phi> (pass\<^sub>2 rx) =
          log 2 (size lx + size rx + 1) + log 2 (size lx + size rx) - log 2 (size rx)"
      using 2 3 by (simp add: algebra_simps) 
    have "\<Phi> (pass\<^sub>2 ?h) - \<Phi> ?h =
        \<Phi> (link (Node lx x (pass\<^sub>2 rx))) - \<Phi> lx - \<Phi> rx - log 2 (size lx + size rx + 1)"
      by (simp)
    also have "\<dots> = \<Phi> (pass\<^sub>2 rx) - \<Phi> rx + log 2 (size lx + size rx) - log 2 (size rx)"
      using link by linarith
    also have "\<dots> \<le> log 2 (size lx + size rx)"
      using Node.IH 1 by simp
    also have "\<dots> \<le> log 2 (size ?h)" using 1 by simp
    finally show ?thesis .
  qed simp
qed simp

lemma \<Delta>\<Phi>_del_min: assumes "hs \<noteq> Leaf"
shows "\<Phi> (del_min (Node hs x Leaf)) - \<Phi> (Node hs x Leaf) 
  \<le> 3*log 2 (size hs) - len hs + 2"
proof -
  let ?h = "Node hs x Leaf"
  let ?\<Delta>\<Phi>\<^sub>1 = "\<Phi> hs - \<Phi> ?h" 
  let ?\<Delta>\<Phi>\<^sub>2 = "\<Phi>(pass\<^sub>2(pass\<^sub>1 hs)) - \<Phi> hs"
  let ?\<Delta>\<Phi> = "\<Phi> (del_min ?h) - \<Phi> ?h"
  have "\<Phi>(pass\<^sub>2(pass\<^sub>1 hs)) - \<Phi> (pass\<^sub>1 hs) \<le> log 2  (size hs)" 
    using \<Delta>\<Phi>_pass2 [of "pass\<^sub>1 hs"] assms by(metis eq_size_0 size_pass\<^sub>1)
  moreover have "\<Phi> (pass\<^sub>1 hs) - \<Phi> hs \<le>  2*\<dots> - len hs + 2" 
    by(rule \<Delta>\<Phi>_pass1[OF assms])
  moreover have "?\<Delta>\<Phi> \<le> ?\<Delta>\<Phi>\<^sub>2" by simp
  ultimately show ?thesis using assms by linarith
qed

lemma pass\<^sub>1_len: "len (pass\<^sub>1 h) \<le> len h"
by (induct h rule: pass\<^sub>1.induct) simp_all


subsubsection \<open>Putting it all together (boiler plate)\<close>

fun exec :: "'a :: linorder op \<Rightarrow> 'a tree list \<Rightarrow> 'a tree" where
"exec Empty [] = Leaf" | 
"exec Del_min [h] = del_min h" |
"exec (Insert x) [h] = insert x h" |
"exec Merge [h1,h2] = merge h1 h2"

time_fun link

lemma T_link_0[simp]: "T_link h = 0"
by (cases h rule: T_link.cases) auto

time_fun pass\<^sub>1

time_fun pass\<^sub>2

time_fun del_min

time_fun merge

lemma T_merge_0[simp]: "T_merge h1 h2 = 0"
by (cases "(h1,h2)" rule: T_merge.cases) auto

time_fun insert

fun cost :: "'a :: linorder op \<Rightarrow> 'a tree list \<Rightarrow> nat" where
  "cost Empty [] = 0"
| "cost Del_min [hp] = T_del_min hp"
| "cost (Insert a) [hp] = T_insert a hp"
| "cost Merge [h1,h2] = T_merge h1 h2"

fun U :: "'a :: linorder op \<Rightarrow> 'a tree list \<Rightarrow> real" where
  "U Empty [] = 0"
| "U (Insert a) [h] = log 2 (size h + 1)"
| "U Del_min [h] = 3*log 2 (size h + 1) + 4"
| "U Merge [h1,h2] = log 2 (size h1 + size h2 + 1) + 1"

interpretation Amortized
where arity = arity and exec = exec and cost = cost and inv = is_root 
and \<Phi> = \<Phi> and U = U
proof (standard, goal_cases)
  case (1 _ f) thus ?case using is_root_insert is_root_del_min is_root_merge
    by (cases f) (auto simp: numeral_eq_Suc)
next
  case (2 s) show ?case by (induct s) simp_all
next
  case (3 ss f) show ?case 
  proof (cases f)
    case Empty with 3 show ?thesis by(auto)
  next
    case (Insert x)
    then obtain h where "ss = [h]" "is_root h" using 3 by auto
    thus ?thesis using Insert \<Delta>\<Phi>_insert 3 by auto
  next
    case [simp]: (Del_min)
    then obtain h where [simp]: "ss = [h]" using 3 by auto
    show ?thesis
    proof (cases h)
      case [simp]: (Node lx x rx)
      have "T_pass\<^sub>2 (pass\<^sub>1 lx) + T_pass\<^sub>1 lx \<le> len lx + 2"
        by (induct lx rule: pass\<^sub>1.induct) simp_all
      hence "cost f ss \<le> \<dots>" by simp 
      moreover have "\<Phi> (del_min h) - \<Phi> h \<le> 3*log 2 (size h + 1) - len lx + 2"
      proof (cases lx)
        case [simp]: (Node ly y ry) 
        have "\<Phi> (del_min h) - \<Phi> h \<le> 3*log 2 (size lx) - len lx + 2"
          using  \<Delta>\<Phi>_del_min[of "lx" "x"] 3 by simp
        also have "\<dots> \<le> 3*log 2 (size h + 1) - len lx + 2" by fastforce
        finally show ?thesis by blast
      qed (insert 3, simp)
      ultimately show ?thesis by auto
    qed simp
  next
    case [simp]: Merge
    then obtain h1 h2 where [simp]: "ss = [h1,h2]" and 1: "is_root h1" "is_root h2"
      using 3 by (auto simp: numeral_eq_Suc)
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
        have "\<Phi> (merge h1 h2) - \<Phi> h1 - \<Phi> h2 \<le> log 2 (real (size h1 + size h2)) + 1"
          apply(rule \<Delta>\<Phi>_merge) using h1 h2 1 by auto
        also have "\<dots> \<le> log 2 (size h1 + size h2 + 1) + 1" by (simp add: h1)
        finally show ?thesis by(simp add: algebra_simps)
      qed
    qed
  qed
qed

end
