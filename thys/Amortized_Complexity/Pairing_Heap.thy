(* Author: Hauke Brinkop *)

header {* Amortized Analysis of Pairing Heaps in Binary Tree Representation *}

theory Pairing_Heap 
imports 
  Complex_Main 
  Amor
begin

text{* Pairing heaps were invented by Fredman, Sedgewick, Sleator and Tarjan
\cite{FredmanSST86}. In this theory we verify their logarithmic bound on the
amortized complexity of pairing heaps. *}

datatype 'a heap = Empty | Heap 'a "'a heap" "'a heap"

fun link :: "'a :: linorder heap \<Rightarrow> 'a heap" where
  "link Empty = Empty"
| "link (Heap x lx Empty) = Heap x lx Empty"
| "link (Heap x lx (Heap y ly ry)) = (if x < y then Heap x (Heap y ly lx) else Heap y (Heap x lx ly)) ry"

fun firstpass :: "'a :: linorder heap \<Rightarrow> 'a heap" where
  "firstpass Empty = Empty"
| "firstpass (Heap x lx Empty) = Heap x lx Empty" 
| "firstpass (Heap x lx (Heap y ly ry)) = link (Heap x lx (Heap y ly (firstpass ry)))"

(*Count the "trees" in a (sub)heap" *)
fun countTrees :: "'a heap \<Rightarrow> nat" where 
  "countTrees Empty = 0"
| "countTrees (Heap _ _ r) = 1 + countTrees r"
function (sequential)secondpass :: "'a :: linorder heap \<Rightarrow> 'a heap" where
  "secondpass Empty = Empty"
| "secondpass (Heap x lx rx) = link(Heap x lx (secondpass rx))"
by pat_completeness simp_all
termination by (relation "measure countTrees") simp_all

fun deleteMin :: "'a :: linorder heap \<Rightarrow> 'a heap" where
  "deleteMin Empty = Empty"
| "deleteMin (Heap _ lx Empty) = secondpass (firstpass lx)"
| "deleteMin (Heap _ _ (Heap _ _ _)) = Empty"

fun findMin :: "'a :: linorder heap \<Rightarrow> 'a option" where
  "findMin Empty = None"
| "findMin (Heap x _ _) = Some x"

fun merge :: "'a :: linorder heap \<Rightarrow> 'a heap \<Rightarrow> 'a heap" where
  "merge Empty h = h"
| "merge h Empty = h"
| "merge (Heap x lx Empty) (Heap y ly Empty) = link (Heap x lx (Heap y ly Empty))"
| "merge _ _ = Empty" (*the input is malformed, cannot work with that*)

fun insert :: "'a \<Rightarrow> 'a :: linorder heap \<Rightarrow> 'a heap" where
  "insert x h = merge (Heap x Empty Empty) h"

fun hasHeapProperty :: "'a :: linorder \<Rightarrow> 'a heap \<Rightarrow> bool" where
  "hasHeapProperty _ Empty = True"
| "hasHeapProperty m (Heap x lx rx) = (x \<le> m \<and> hasHeapProperty (min x m) lx \<and> hasHeapProperty m rx)"

fun oneRoot :: "'a :: linorder heap \<Rightarrow> bool" where
  "oneRoot Empty = True"
| "oneRoot (Heap _ _ r) = (r = Empty)"

fun isValid :: "'a :: linorder heap \<Rightarrow> bool" where
  "isValid (Heap x lx Empty) = hasHeapProperty x lx"
| "isValid Empty = True"
| "isValid (Heap _ _ (Heap _ _ _)) = False"

fun ld :: "nat \<Rightarrow> real" where
  "ld x = (if x = 0 then 0 else log 2 x)"

fun \<Phi> :: "'a heap \<Rightarrow> real" where
  "\<Phi> Empty = 0"
| "\<Phi> (Heap _ lx rx) = \<Phi> lx + \<Phi> rx + log 2 (1 + size lx + size rx)"

declare algebra_simps[simp]

lemma add_log_log1: assumes "x > 0" "y > 0" shows "1 + log 2 x + log 2 y < 2 * log 2 (x+y)"
proof -
  have 1: "2*x*y < (x+y)^2" using assms by(simp add: numeral_eq_Suc add_pos_pos)
  show ?thesis apply(rule powr_less_cancel_iff[of 2, THEN iffD1])
    using assms 1 by (simp_all add: powr_add log_powr[symmetric] powr_numeral)
qed

lemma isValid_oneRoot: assumes "oneRoot (Heap x lx rx)" shows "rx = Empty"
using assms by auto

lemma link_size[simp]: "size (link h) = size h" by (cases h rule: link.cases) simp_all

lemma firstpass_size[simp]: "size (firstpass h) = size h" by (induct h rule: firstpass.induct) simp_all

lemma secondpass_size[simp]: " size (secondpass h) = size h" by (induct h rule: secondpass.induct) simp_all

lemma merge_size[simp]: assumes "oneRoot h1" and "oneRoot h2" shows "size (merge h1 h2) = size h1 + size h2"
  apply (cases h1) 
  apply simp
  using isValid_oneRoot isValid_oneRoot assms
  by (cases h2) (simp_all)
(*
proof (cases h1)
  case (Heap x lx rx)[simp]
  have[simp]: "rx = Empty" using assms isValid_oneRoot by simp
  show ?thesis
  proof (cases h2)
    case (Heap y ly ry)[simp]
    have "ry = Empty" using assms isValid_oneRoot by simp
    thus ?thesis by simp
  qed simp
qed simp
*)


lemma link_cases_struct: "\<exists>a la. link(Heap x lx (Heap y ly ry)) = Heap a la ry" by simp

lemma firstpass_struct: "\<exists>a la ra. firstpass(Heap x lx rx) = Heap a la ra" by (cases rx) simp_all

lemma secondpass_struct: "\<exists>a la. secondpass(Heap x lx rx) = Heap a la Empty" 
proof (induct rx arbitrary: x lx rule: secondpass.induct)
  case 1 thus ?case by(metis link.simps(2) secondpass.simps(1) secondpass.simps(2))
next
  case 2 thus ?case by(metis secondpass.simps(2) link_cases_struct)
qed
(*
proof (induct rx arbitrary: x lx rule: secondpass.induct)
  case (2 y ly ry x lx) (* Heap x lx (Heap y ly ry) *)
    obtain a la where "secondpass (Heap y ly ry) = Heap a la Empty" using "2.hyps" by blast
    moreover obtain b lb where "link(Heap x lx (Heap a la Empty)) = Heap b lb Empty" using link_cases_struct by blast
    ultimately show ?case by simp
qed simp
*)

(*
proof (induct rx arbitrary: x lx rule: secondpass.induct)
  case (2 y ly ry x lx)
    let ?h = "Heap x lx (Heap y ly ry)"
    obtain a la where "secondpass (Heap y ly ry) = Heap a la Empty" using "2.hyps" by blast
    hence "secondpass ?h = link (Heap x lx (Heap a la Empty))" by simp
    moreover obtain b lb where "link(Heap x lx (Heap a la Empty)) = Heap b lb Empty" using link_cases_struct by blast
    ultimately show ?case by simp
qed simp
*)

lemma \<Delta>\<Phi>\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t: assumes "oneRoot h" shows "\<Phi> (insert x h) - \<Phi> h \<le> ld (size h + 1)"
  using assms isValid_oneRoot
  by (cases h) (simp,fastforce)

(*
proof (cases h) 
  case (Heap x lx rx)[simp]
    have "rx = Empty" using assms isValid_oneRoot by simp
    thus ?thesis by simp
qed simp
*)

lemma \<Delta>\<Phi>\<^sub>m\<^sub>e\<^sub>r\<^sub>g\<^sub>e: assumes "oneRoot h1 \<and> oneRoot h2" shows "\<Phi> (merge h1 h2) - \<Phi> h1 - \<Phi> h2 \<le> 2*ld (size h1 + size h2)" 
proof (cases h1)
  case (Heap x lx rx)[simp]
  have[simp]: "rx = Empty" using assms by auto
    thus ?thesis
    proof (cases h2)
      case (Heap y ly ry)[simp]
      have[simp]: "ry = Empty" using assms by auto
        let ?h = "Heap x lx (Heap y ly Empty)"
        have "\<Phi> (link ?h) - \<Phi> ?h \<le> ld (1 + size lx + size ly)" by simp
        also have "... \<le> ld (size h1 + size h2)" by simp
        moreover have "\<Phi> ?h - \<Phi> h1 - \<Phi> h2 \<le> ld (size h1 + size h2)" by simp
        ultimately have "\<Phi> (link ?h) - \<Phi> h1 - \<Phi> h2 \<le> 2*ld (size h1 + size h2)" by linarith
        thus ?thesis by simp
    qed simp
qed simp

fun sum_ub :: "'a heap \<Rightarrow> real" where
  "sum_ub Empty = 0"
| "sum_ub (Heap _ _ Empty) = 0"
| "sum_ub (Heap _ lx (Heap _ ly Empty)) = 2*ld(2 + size lx + size ly)" 
| "sum_ub (Heap _ lx (Heap _ ly ry)) = 2*ld(2 + size lx + size ly + size ry) - 2*ld(size ry) - 1 + sum_ub ry"

lemma \<Delta>\<Phi>\<^sub>f\<^sub>i\<^sub>r\<^sub>s\<^sub>t\<^sub>p\<^sub>a\<^sub>s\<^sub>s_sum_ub: "\<Phi> (firstpass h) - \<Phi> h  \<le> sum_ub h"
proof (induction h rule: sum_ub.induct)
  case (3 x lx y ly)
  let ?h = "(Heap x lx (Heap y ly Empty))"
  have "\<Phi> (firstpass ?h) - \<Phi> ?h = ld (1 + size lx + size ly) - ld (1 + size ly)" by simp
  also have "\<dots> \<le> ld(1 + size lx + size ly)" by simp
  also have "\<dots> \<le> ld(2 + size lx + size ly)" by simp
  also have "\<dots> \<le> 2*ld(2 + size lx + size ly)" by simp
  finally show ?case by simp
next
  case (4 x lx y ly z lz rz)
  let ?ry = "Heap z lz rz"
  let ?rx = "Heap y ly ?ry"
  let ?h = "Heap x lx ?rx"
  have "\<Phi> (firstpass ?h) - \<Phi> ?h = ld (1 + size lx + size ly) - ld (1 + size ly + size ?ry) + \<Phi> (firstpass ?ry) - \<Phi> ?ry" (is "?t = _") by simp
  also have "\<dots> \<le> ld(1 + size lx + size ly) - ld(1 + size ly + size ?ry) + sum_ub ?ry" using "4.IH" by linarith
  also have "ld(1 + size lx + size ly) - ld(1 + size ly + size ?ry) \<le> 2*ld (size ?h) - 2*ld(size ?ry) - 1"
  proof -
    have "ld (1 + size lx + size ly) + ld (size ?ry) - 2*ld (size ?h) = log 2 (1 + size lx + size ly) + log 2 (size ?ry) - 2*log 2 (size ?h)" (is "_ = ?t1") by simp 
    also have "?t1 = log 2 ( (1 + size lx + size ly)/(size ?h) ) + log 2 (size ?ry/size ?h)" (is "_ = ?t2")
    proof -
      have "log 2 (1 + size lx + size ly) - log 2 (size ?h) = log 2 ( (1 + size lx + size ly)/(size ?h) )" using log_divide  by simp
      moreover have "log 2 (size ?ry) - log 2 (size ?h) = log 2 (size ?ry/size ?h)" using log_divide by simp
      ultimately show ?thesis by simp
    qed 
    also have "?t2 \<le> -1"
    proof -
      have 1: "1 + log 2 ((1 + size lx + size ly) / size ?h) + log 2 (size ?ry / size ?h)
        \<le> 2*log 2 ((1 + size lx + size ly) / size ?h +  size ?ry / size ?h)"  
        using add_log_log1 [of "(1 + size lx + size ly) / size ?h" "(size ?ry / size ?h)"] by simp
      have 2: "(1 + size lx + size ly) / size ?h +  size ?ry / size ?h = (1 + size lx + size ly + size ?ry) / size ?h"
        by (simp del: algebra_simps add: field_simps)
      have "2*log 2 ( (1 + size lx + size ly) / size ?h + size ?ry / size ?h ) \<le> 0" using 1 2 by simp
      hence "1 + log 2 ((1 + size lx + size ly) / size ?h) + log 2 (size ?ry / size ?h) \<le> 0" using 1 by linarith
      thus ?thesis by simp
    qed 
    finally have "log 2 (1 + size lx + size ly) - log 2 (size ?ry) \<le>  2*log 2 (size ?h) - 2*log 2 (size ?ry) - 1" by simp
    moreover have "log 2 (size ?ry) \<le> log 2 (size ?rx)" by simp
    ultimately have "log 2 (1 + size lx + size ly) - log 2 (size ?rx) \<le>  2*log 2 (size ?h) - 2*log 2 (size ?ry) - 1" by linarith
    hence "log 2 (1 + size lx + size ly) - log 2 (1 + size ly + size ?ry) \<le>  2*log 2 (size ?h) - 2*log 2 (size ?ry) - 1" by simp
    thus ?thesis by simp
  qed
  finally have "?t \<le> 2*ld(2 + size lx + size ly + size ?ry) - 2*ld(size ?ry) - 1 + sum_ub ?ry" by simp
  thus ?case by simp
qed simp_all

lemma \<Delta>\<Phi>\<^sub>f\<^sub>i\<^sub>r\<^sub>s\<^sub>t\<^sub>p\<^sub>a\<^sub>s\<^sub>s: "\<Phi> (firstpass h) - \<Phi> h \<le> 2*ld(size h) - countTrees h/2 + 1"
proof - 
  let ?t = "\<Phi> (firstpass h) - \<Phi> h"
  have "?t \<le> sum_ub h" using \<Delta>\<Phi>\<^sub>f\<^sub>i\<^sub>r\<^sub>s\<^sub>t\<^sub>p\<^sub>a\<^sub>s\<^sub>s_sum_ub .
  also have "2*sum_ub h \<le> 4*ld(size h) - countTrees h + 2" by (induct h rule: sum_ub.induct) simp_all
  finally show ?thesis by fastforce
qed

lemma \<Delta>\<Phi>\<^sub>s\<^sub>e\<^sub>c\<^sub>o\<^sub>n\<^sub>d\<^sub>p\<^sub>a\<^sub>s\<^sub>s: "\<Phi> (secondpass h) - \<Phi> h \<le> ld (size h)"
proof (induction h rule: secondpass.induct)
  case (2 x lx rx)
    thus ?case 
    proof (cases rx)
      case (Heap y ly ry)[simp]
        let ?rx = "rx"
        let ?h = "Heap x lx ?rx"
        have "\<Phi> (secondpass ?h) - \<Phi> ?h = \<Phi> (link (Heap x lx (secondpass ?rx))) - \<Phi> ?h" (is "?d = _") by simp
        then obtain a la where 1: "secondpass rx = Heap a la Empty" using secondpass_struct by force
        hence "size (Heap a la Empty) = size ?rx" using secondpass_size by metis
        hence 2: "size la = size ?rx - 1" by simp
        hence "size la = size ly + size ry" by simp
        hence "?d = \<Phi> (link (Heap x lx (Heap a la Empty))) - \<Phi> (Heap x lx (Heap a la Empty)) + \<Phi> (secondpass ?rx) - \<Phi> ?rx" using 1 by simp
        hence "?d = ld (1 + size lx + size la) - ld (1 + size la) + \<Phi> (secondpass ?rx) - \<Phi> ?rx" using 1 by simp
        hence "?d = ld(size lx + size ?rx) - ld(1 + size la) + \<Phi> (secondpass ?rx) - \<Phi> ?rx"  using 2 by simp
        hence "?d \<le> ld(size ?h) - ld(size ?rx) + \<Phi> (secondpass ?rx) - \<Phi> ?rx"  using 2 by simp
        hence "?d \<le> ld(size ?h)" using "2.IH" by simp
        thus ?thesis .
    qed simp
qed simp

lemma \<Delta>\<Phi>\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e\<^sub>M\<^sub>i\<^sub>n:  "\<Phi> (deleteMin (Heap x lx Empty)) - \<Phi> (Heap x lx Empty) \<le> 3*ld(size lx) - countTrees lx / 2 + 1"
proof -
  let ?h = "Heap x lx Empty"
  let ?\<Delta>\<Phi>\<^sub>1 = "\<Phi> lx - \<Phi> ?h" 
  let ?\<Delta>\<Phi>\<^sub>2 = "\<Phi>(secondpass(firstpass lx)) - \<Phi> lx"
  let ?\<Delta>\<Phi> = "\<Phi> (deleteMin ?h) - \<Phi> ?h"
  have 1: "?\<Delta>\<Phi> = ?\<Delta>\<Phi>\<^sub>1 + ?\<Delta>\<Phi>\<^sub>2" by simp
  have 2: "?\<Delta>\<Phi>\<^sub>1 \<le> 0" by simp
  have "\<Phi>(secondpass(firstpass lx)) - \<Phi> (firstpass lx) \<le> ld (size lx)" using \<Delta>\<Phi>\<^sub>s\<^sub>e\<^sub>c\<^sub>o\<^sub>n\<^sub>d\<^sub>p\<^sub>a\<^sub>s\<^sub>s[of "firstpass lx"] by (metis firstpass_size)
  moreover have "\<Phi> (firstpass lx) - \<Phi> lx \<le>  2*ld(size lx) - countTrees lx / 2 + 1" using \<Delta>\<Phi>\<^sub>f\<^sub>i\<^sub>r\<^sub>s\<^sub>t\<^sub>p\<^sub>a\<^sub>s\<^sub>s by blast
  ultimately have "?\<Delta>\<Phi>\<^sub>2 \<le> 3*ld(size lx) - countTrees lx / 2 + 1" by linarith
  thus ?thesis using 1 2 by linarith
qed

lemma oneRoot_merge: assumes "oneRoot h1" and "oneRoot h2" shows "oneRoot (merge h1 h2)" 
proof (cases h1)
  case (Heap)
  thus ?thesis using link_cases_struct assms by(cases h2) (auto)
next 
  case Empty
  thus ?thesis using assms by(cases h2) (auto)
qed 

lemma oneRoot_insert: assumes "oneRoot h" shows "oneRoot (insert x h)"
  by (simp add: assms oneRoot_merge)
(*
proof -
  have "oneRoot (Heap x Empty Empty)" by simp
  thus ?thesis using assms oneRoot_merge by fastforce
qed
*)

lemma oneRoot_deleteMin: assumes "oneRoot h" shows "oneRoot (deleteMin h)"
proof (cases h)
  case (Heap x lx rx)[simp]
    have[simp]: "rx = Empty" using assms by simp
    thus ?thesis 
    proof (cases lx)
      case (Heap y ly ry)[simp]
        then obtain a la ra where "firstpass lx = Heap a la ra" using firstpass_struct by blast
        moreover obtain b lb where "secondpass (Heap a la ra) = Heap b lb Empty" using secondpass_struct by blast
        ultimately show ?thesis using secondpass_struct by simp
    qed simp
qed simp

lemma firstpass_countTrees: assumes "oneRoot h" shows "countTrees (firstpass h) \<le> countTrees h"
 by (induct h rule: firstpass.induct) simp_all
  (*by (metis (full_types) assms findMin.cases firstpass.simps(1) firstpass.simps(2) isValid_oneRoot order_refl) *)

(* Using Framework *)
datatype 'a cmd = Insert 'a | Delmin | FindMin
fun nxt :: "'a :: linorder cmd \<Rightarrow> 'a heap \<Rightarrow> 'a heap" where
  "nxt FindMin h = h"
| "nxt Delmin h = deleteMin h"
| "nxt (Insert x) h = insert x h"
fun t\<^sub>r\<^sub>e\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d :: "'a :: linorder heap \<Rightarrow> real" where
  "t\<^sub>r\<^sub>e\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d Empty = 1"
| "t\<^sub>r\<^sub>e\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d (Heap _ _ r) = 2 + t\<^sub>r\<^sub>e\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d r" 
fun t :: "'a :: linorder cmd \<Rightarrow> 'a heap \<Rightarrow> real" where
  "t FindMin _ = 1"
| "t Delmin Empty = 1"
| "t Delmin (Heap _ l _) = 1 + t\<^sub>r\<^sub>e\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d l"
| "t (Insert a) _ = 1"
fun U :: "'a :: linorder cmd \<Rightarrow> 'a heap \<Rightarrow> real" where
  "U FindMin _ = 1"
| "U (Insert a) h = 1 + 4*log 2 (size h + 1)"
| "U Delmin h = 4*3*log 2 (size h + 1) + 6"
interpretation pairing: amor
where init = "Empty"
and nxt = "nxt"
and t = "t"
and inv = "oneRoot"
and \<Phi> = "\<lambda> x. 4*\<Phi> x"
and U = "U"
proof
  case goal2 thus ?case proof (cases f)
    case (Insert x)[simp]
      have "oneRoot s" by (metis goal2)
      hence  "oneRoot (insert x s)" using oneRoot_insert by fast
      thus ?thesis by simp
    next
    case (Delmin)[simp]
      have "oneRoot s" by (metis goal2)
      thus ?thesis using oneRoot_deleteMin by auto
    next    
  qed simp_all
  case goal3 show ?case by (induct s) (simp, auto) next
  case goal5 show ?case proof (cases f)
    case (Insert x)[simp]
      have "oneRoot s" by (metis goal5)
      hence "\<Phi> (insert x s) - \<Phi> s \<le> ld (1 + size s)" using \<Delta>\<Phi>\<^sub>i\<^sub>n\<^sub>s\<^sub>e\<^sub>r\<^sub>t by auto
      thus ?thesis by simp
    next
    case (Delmin)[simp]
      thus ?thesis
      proof (cases s)
        case (Heap x lx rx)[simp]
          have "oneRoot s" by (metis goal5)
          hence "rx = Empty" by simp
          hence "\<Phi> (deleteMin s) - \<Phi> s \<le> 3*ld(size lx) - countTrees lx / 2 + 1" using  \<Delta>\<Phi>\<^sub>d\<^sub>e\<^sub>l\<^sub>e\<^sub>t\<^sub>e\<^sub>M\<^sub>i\<^sub>n by fastforce
          hence pot_diff:"4*(\<Phi> (deleteMin s) - \<Phi> s) \<le> 12*ld(size lx) - 2*countTrees lx  + 4" by simp

          have "nxt f s = deleteMin s" by simp
          hence "t f s = 1 + t\<^sub>r\<^sub>e\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d lx" by simp
          moreover have "t\<^sub>r\<^sub>e\<^sub>b\<^sub>u\<^sub>i\<^sub>l\<^sub>d lx = 1 + 2*countTrees lx" by (induct lx rule: countTrees.induct) auto
          ultimately have running_time: "t f s = 2 + 2*countTrees lx" by simp

          have "4*\<Phi> (deleteMin s) - 4* \<Phi> s + t f s \<le> 12*ld(size lx)  + 6" using pot_diff running_time by simp
          also have "... \<le> 12*log 2 (size s + 1) + 6" by simp
          moreover have "U f s = 12*log 2 (size s + 1) + 6" by simp
          moreover have "nxt f s = deleteMin s" by simp
          moreover have "\<Phi> (nxt f s) - \<Phi> (s) = \<Phi> (deleteMin s) - \<Phi> s" by simp
          ultimately show ?thesis by linarith
        next
      qed simp
    next
  qed simp
qed simp_all

end
