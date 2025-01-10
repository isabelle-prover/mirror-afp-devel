(*  Title:       Binary Search Trees, Isar-Style
    Author:      Viktor Kuncak, MIT CSAIL, November 2003
    Maintainer:  Larry Paulson <Larry.Paulson at cl.cam.ac.uk>
    License:     LGPL
*)

section \<open>Isar-style Reasoning for Binary Tree Operations\<close>
theory BinaryTree imports Main begin

text \<open>We prove correctness of operations on 
 binary search tree implementing a set.

 This document is LGPL.

 Author: Viktor Kuncak, MIT CSAIL, November 2003\<close>

(*============================================================*)
section \<open>Tree Definition\<close>
(*============================================================*)

datatype 'a Tree = Tip | T "'a Tree" 'a "'a Tree"

primrec
  setOf :: "'a Tree => 'a set" 
  \<comment> \<open>set abstraction of a tree\<close> 
where
  "setOf Tip = {}"
| "setOf (T t1 x t2) = (setOf t1) Un (setOf t2) Un {x}"

type_synonym
  \<comment> \<open>we require index to have an irreflexive total order <\<close>
  \<comment> \<open>apart from that, we do not rely on index being int\<close>
  index = int 

type_synonym \<comment> \<open>hash function type\<close>
  'a hash = "'a => index"

definition eqs :: "'a hash => 'a => 'a set" where
  \<comment> \<open>equivalence class of elements with the same hash code\<close>
  "eqs h x == {y. h y = h x}"

primrec
  sortedTree :: "'a hash => 'a Tree => bool"
  \<comment> \<open>check if a tree is sorted\<close>
where
  "sortedTree h Tip = True"
| "sortedTree h (T t1 x t2) = 
    (sortedTree h t1 \<and> 
     (\<forall>l \<in> setOf t1. h l < h x) \<and>
     (\<forall>r \<in> setOf t2. h x < h r) \<and>
     sortedTree h t2)"

lemma sortLemmaL: 
  "sortedTree h (T t1 x t2) ==> sortedTree h t1" by simp

lemma sortLemmaR: 
  "sortedTree h (T t1 x t2) ==> sortedTree h t2" by simp

(*============================================================*)
section \<open>Tree Lookup\<close>
(*============================================================*)

primrec
  tlookup :: "'a hash => index => 'a Tree => 'a option"
where
  "tlookup h k Tip = None"
| "tlookup h k (T t1 x t2) = 
   (if k < h x then tlookup h k t1
    else if h x < k then tlookup h k t2
    else Some x)"

lemma tlookup_none: 
  "sortedTree h t \<Longrightarrow> (tlookup h k t = None) \<Longrightarrow> x \<in> setOf t \<Longrightarrow> h x \<noteq> k"
  by (induction t, auto) 

lemma tlookup_some:
     "sortedTree h t \<Longrightarrow> (tlookup h k t = Some x) \<Longrightarrow> x \<in> setOf t \<and> h x = k"
proof (induction t)
  case Tip
  then show ?case by auto  
next
  case (T t1 x2 t2)
  then show ?case
    apply simp
    by (metis linorder_less_linear option.sel)
qed

definition sorted_distinct_pred :: "'a hash => 'a => 'a => 'a Tree => bool" where
  \<comment> \<open>No two elements have the same hash code\<close>
  "sorted_distinct_pred h a b t 
  \<equiv> sortedTree h t \<and> a \<in> setOf t \<and> b \<in> setOf t \<and> h a = h b \<longrightarrow>  a = b"

declare sorted_distinct_pred_def [simp]

text \<open>@{term sorted_distinct_pred} holds for out trees:\<close>

lemma sorted_distinct: "sorted_distinct_pred h a b t" (is "?P t")
  by (induct t) force+

lemma tlookup_finds: \<comment> \<open>if a node is in the tree, lookup finds it\<close>
  assumes "sortedTree h t" "y \<in> setOf t"
  shows "tlookup h (h y) t = Some y"
proof (cases "tlookup h (h y) t")
  case None 
  with assms show ?thesis
    by (meson tlookup_none)
next 
  case (Some z) 
  with assms show ?thesis
    by (metis sorted_distinct sorted_distinct_pred_def tlookup_some)
qed

subsection \<open>Tree membership as a special case of lookup\<close>

definition memb :: "'a hash => 'a => 'a Tree => bool" where
  "memb h x t == 
   (case (tlookup h (h x) t) of
      None => False
    | Some z => (x=z))"

lemma memb_spec: 
  assumes "sortedTree h t"  shows "memb h x t = (x \<in> setOf t)"
proof (cases "tlookup h (h x) t")
  case None
  then show ?thesis
    by (metis memb_def option.simps(4) assms tlookup_none)
next 
  case (Some z)
  with assms tlookup_some have "z \<in> setOf t" by fastforce
  then show ?thesis
    using memb_def assms Some tlookup_finds by force
qed

declare sorted_distinct_pred_def [simp del]

(*============================================================*)
section \<open>Insertion into a Tree\<close>
(*============================================================*)

primrec
  binsert :: "'a hash => 'a => 'a Tree => 'a Tree"
where
  "binsert h e Tip = (T Tip e Tip)"
| "binsert h e (T t1 x t2) = 
     (if h e < h x then (T (binsert h e t1) x t2)
                   else (if h x < h e then (T t1 x (binsert h e t2))
                         else (T t1 e t2)))"

text \<open>A technique for proving disjointness of sets.\<close>
lemma disjCond: "[| !! x. [| x:A; x:B |] ==> False |] ==> A Int B = {}"
  by fastforce

text \<open>The following is a proof that insertion correctly implements
        the set interface.
        Compared to \<open>BinaryTree_TacticStyle\<close>, the claim is more
        difficult, and this time we need to assume as a hypothesis
        that the tree is sorted.\<close>

lemma binsert_set: "sortedTree h t \<Longrightarrow>
                    setOf (binsert h e t) = (setOf t) - (eqs h e) Un {e}" 
  by (induction t) (auto simp: eqs_def)

text \<open>Using the correctness of set implementation,
        preserving sortedness is still simple.\<close>
lemma binsert_sorted: "sortedTree h t --> sortedTree h (binsert h x t)"
  by (induct t) (auto simp add: binsert_set)

text \<open>We summarize the specification of binsert as follows.\<close>
corollary binsert_spec: "sortedTree h t -->
                     sortedTree h (binsert h x t) \<and>
                     setOf (binsert h e t) = (setOf t) - (eqs h e) Un {e}"
  by (simp add: binsert_set binsert_sorted)

(*============================================================*)
section \<open>Removing an element from a tree\<close>
(*============================================================*)

text \<open>These proofs are influenced by those in \<open>BinaryTree_Tactic\<close>\<close>

primrec
  rm :: "'a hash => 'a Tree => 'a"
  \<comment> \<open>rightmost element of a tree\<close>
where
"rm h (T t1 x t2) =
  (if t2=Tip then x else rm h t2)"

primrec
  wrm :: "'a hash => 'a Tree => 'a Tree"
  \<comment> \<open>tree without the rightmost element\<close>
where
"wrm h (T t1 x t2) =
  (if t2=Tip then t1 else (T t1 x (wrm h t2)))"

primrec
  wrmrm :: "'a hash => 'a Tree => 'a Tree * 'a"
  \<comment> \<open>computing rightmost and removal in one pass\<close>
where
"wrmrm h (T t1 x t2) =
  (if t2=Tip then (t1,x)
   else (T t1 x (fst (wrmrm h t2)),
         snd (wrmrm h t2)))"

primrec
  remove :: "'a hash => 'a => 'a Tree => 'a Tree"
   \<comment> \<open>removal of an element from the tree\<close>
where
  "remove h e Tip = Tip"
| "remove h e (T t1 x t2) = 
    (if h e < h x then (T (remove h e t1) x t2)
     else if h x < h e then (T t1 x (remove h e t2))
     else (if t1=Tip then t2
           else let (t1p,r) = wrmrm h t1
                in (T t1p r t2)))"

theorem wrmrm_decomp: "t \<noteq> Tip \<Longrightarrow> wrmrm h t = (wrm h t, rm h t)"
  by (induct t) auto

lemma rm_set: "t \<noteq> Tip \<Longrightarrow> sortedTree h t \<Longrightarrow> rm h t \<in> setOf t"
  by (induct t) auto

lemma wrm_set: "t \<noteq> Tip \<Longrightarrow> sortedTree h t \<Longrightarrow>
                setOf (wrm h t) = setOf t - {rm h t}" 
proof (induction t)
  case Tip
  then show ?case
    by blast
next
  case (T t1 x t2)
  show ?case 
  proof (cases "t2 = Tip")
    case True
    with T show ?thesis
      by fastforce
  next
    case False
    with T rm_set show ?thesis
      by fastforce
  qed
qed

lemma wrm_set1: "t \<noteq> Tip \<Longrightarrow> sortedTree h t \<Longrightarrow> setOf (wrm h t) <= setOf t"
  by (auto simp add: wrm_set)

lemma wrm_sort: "t \<noteq> Tip \<Longrightarrow> sortedTree h t \<Longrightarrow> sortedTree h (wrm h t)"
  by (induction t) (auto simp: wrm_set)

lemma wrm_less_rm: 
  "t \<noteq> Tip \<Longrightarrow> sortedTree h t \<Longrightarrow> l \<in> setOf (wrm h t) \<Longrightarrow> 
   h l < h (rm h t)"
  by (induction t arbitrary: l) (use rm_set in fastforce)+

lemma remove_set: 
  "sortedTree h t \<Longrightarrow> setOf (remove h e t) = setOf t - eqs h e"
proof (induction t)
  case Tip
  then show ?case by auto
next
  case (T t1 x t2)
  show ?case
  proof (cases rule: linorder_cases [of "h e" "h x"])
    case less
    with T show ?thesis
      by (auto simp: eqs_def)
  next
    case equal
    then have *: "(setOf t2) \<inter> (eqs h e) = {}"
      using T.prems sup.strict_order_iff by (fastforce simp: eqs_def)
    show ?thesis 
    proof (cases "t1 = Tip")
      case True 
      with equal * show ?thesis
        by (fastforce simp: eqs_def)
    next 
      case False 
      with equal show ?thesis
        using T.prems rm_set wrm_set wrmrm_decomp by (fastforce simp: eqs_def)
    qed
  next
    case greater
    with T show ?thesis
      by (auto simp: eqs_def)
  qed
qed

lemma remove_sort: "sortedTree h t \<Longrightarrow> sortedTree h (remove h e t)"
proof (induction t)
  case Tip
  then show ?case
    by simp
next
  case (T t1 x t2)
  show ?case
  proof (cases "h e < h x")
    case True 
    then show ?thesis
      using T remove_set by force
  next 
    case False
    with T show ?thesis
      using DiffD1 remove_set rm_set wrm_less_rm wrm_sort wrmrm_decomp
      by fastforce
  qed
qed  

text \<open>We summarize the specification of remove as follows.\<close>
corollary remove_spec: 
  "sortedTree h t \<Longrightarrow>
    sortedTree h (remove h e t) \<and> setOf (remove h e t) = setOf t - eqs h e"
  by (simp add: remove_sort remove_set)

definition "test = tlookup id 4 (remove id 3 (binsert id 4 (binsert id 3 Tip)))"

export_code test
  in SML module_name BinaryTree_Code file \<open>BinaryTree_Code.ML\<close>

end
