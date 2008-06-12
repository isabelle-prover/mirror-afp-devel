(*  Title:      AVL Trees
    ID:         $Id: AVL.thy,v 1.13 2008-06-12 06:57:14 lsf37 Exp $
    Author:     Tobias Nipkow and Cornelia Pusch,
                converted to Isar by Gerwin Klein
                contributions by Achim Brucker, Burkhart Wolff and Jan Smaus
    Maintainer: Gerwin Klein <gerwin.klein at nicta.com.au>

    see the file Changelog for a list of changes
*)

header "AVL Trees"

theory AVL
imports Main
begin

text {* 
  This theory would be a nice candidate for structured Isar proof
  texts and for extensions (delete operation).
  At the moment only insertion is formalized.
*}

datatype 'a tree = ET |  MKT 'a "'a tree" "'a tree" nat

subsection"Invariants and auxiliary functions"

consts
  height :: "'a tree \<Rightarrow> nat"
  set_of :: "'a tree \<Rightarrow> 'a set" 
  avl :: "'a tree \<Rightarrow> bool" 
  is_ord :: "('a::order) tree \<Rightarrow> bool" 

primrec
"set_of ET = {}"
"set_of (MKT n l r h) = insert n (set_of l \<union> set_of r)"

primrec
"height ET = 0"
"height (MKT x l r h) = max (height l) (height r) + 1"

primrec
"avl ET = True"
"avl (MKT x l r h) =
 ((height l = height r \<or> height l = 1+height r \<or> height r = 1+height l) \<and> 
  h = max (height l) (height r) + 1 \<and> avl l \<and> avl r)"

primrec
"is_ord ET = True"
"is_ord (MKT n l r h) =
 ((\<forall>n' \<in> set_of l. n' < n) \<and> (\<forall>n' \<in> set_of r. n < n') \<and> is_ord l \<and> is_ord r)"


subsection "AVL interface and implementation"

consts
  is_in :: "('a::order) \<Rightarrow> 'a tree \<Rightarrow> bool"
  insrt :: "'a::order \<Rightarrow> 'a tree \<Rightarrow> 'a tree"


primrec
 "is_in k ET = False"
 "is_in k (MKT n l r h) = (if k = n then True else
                           if k < n then (is_in k l)
                           else (is_in k r))"


consts ht :: "'a tree \<Rightarrow> nat"
primrec
"ht ET = 0"
"ht (MKT x l r h) = h"

definition
 mkt :: "'a \<Rightarrow> 'a tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"mkt x l r = MKT x l r (max (ht l) (ht r) + 1)"

fun l_bal where
"l_bal(n, MKT ln ll lr h, r) =
 (if ht ll < ht lr
  then case lr of ET \<Rightarrow> ET (* impossible *)
                | MKT lrn lrl lrr lrh \<Rightarrow>
                  mkt lrn (mkt ln ll lrl) (mkt n lrr r)
  else mkt ln ll (mkt n lr r))"

fun r_bal where
"r_bal(n, l, MKT rn rl rr h) =
 (if ht rl > ht rr
  then case rl of ET \<Rightarrow> ET (* impossible *)
                | MKT rln rll rlr h \<Rightarrow> mkt rln (mkt n l rll) (mkt rn rlr rr)
  else mkt rn (mkt n l rl) rr)"

primrec
"insrt x ET = MKT x ET ET 1"
"insrt x (MKT n l r h) = 
   (if x=n
    then MKT n l r h
    else if x<n
         then let l' = insrt x l; hl' = ht l'; hr = ht r
              in if hl' = 2+hr then l_bal(n,l',r)
                 else MKT n l' r (1 + max hl' hr)
         else let r' = insrt x r; hl = ht l; hr' = ht r'
              in if hr' = 2+hl then r_bal(n,l,r')
                 else MKT n l r' (1 + max hl hr'))"

subsection"Correctness proof"

subsubsection {* Insertion maintains AVL balance *}

declare Let_def [simp]

lemma [simp]: "avl t \<Longrightarrow> ht t = height t"
by (induct t) simp_all

text {* Lemmas about height after rotation *}

lemma height_l_bal:
"\<lbrakk> height l = height r + 2; avl l; avl r \<rbrakk>
  \<Longrightarrow> height (l_bal(n,l,r)) = height r + 2 \<or>
      height (l_bal(n,l,r)) = height r + 3"
apply(cases l)
apply (auto simp add:max_def mkt_def split:tree.split split_if_asm)
done

lemma height_r_bal:
"\<lbrakk> height r = height l + 2; avl l; avl r \<rbrakk>
  \<Longrightarrow> height (r_bal(n,l,r)) = height l + 2 \<or>
      height (r_bal(n,l,r)) = height l + 3"
apply(cases r)
apply (auto simp add:max_def mkt_def split:tree.split split_if_asm)
done

lemma [simp]: "height(mkt x l r) = max (height l) (height r) + 1"
by (simp add: mkt_def)

lemma avl_mkt: "\<lbrakk> avl l; avl r;
 height l = height r \<or> height l = height r + 1 \<or> height r = height l + 1 \<rbrakk>
 \<Longrightarrow> avl(mkt x l r)"
by (auto simp add:max_def mkt_def)

lemma avl_l_bal:
"\<lbrakk> avl l; avl r; height l = height r + 2\<rbrakk>
 \<Longrightarrow> avl (l_bal(n, l, r))"
apply(cases l)
 (* separating the two auto's is just for speed *)
apply (auto simp:avl_mkt max_def)
apply (auto simp:avl_mkt max_def split:tree.split)
done

lemma avl_r_bal:
"\<lbrakk> avl l; avl r; height r = height l + 2\<rbrakk> \<Longrightarrow> avl (r_bal(n, l, r))"
apply(cases r)
 (* separating the two auto's is just for speed *)
apply (auto simp:avl_mkt max_def)
apply (auto simp:avl_mkt max_def split:tree.split)
done

(* It apppears that these two properties need to be proved simultaneously: *)

text{* Insertion maintains the AVL property: *}

theorem avl_insrt_aux:
"avl t \<Longrightarrow> avl(insrt x t) \<and>
 (height (insrt x t) = height t \<or> height (insrt x t) = height t + 1)"
apply (induct "t")
 apply simp
apply (rename_tac n t1 t2 h)
apply (case_tac "x=n")
 apply simp
apply (case_tac "x<n")
 apply (case_tac "height (insrt x t1) = height t2 + 2")
  apply(rule conjI)
   apply (simp add:avl_l_bal)
  apply (frule_tac n = n in height_l_bal) apply simp apply simp
  apply (simp add: max_def) apply arith
 apply(rule conjI)
  apply fastsimp
 apply (simp add: max_def) apply arith
apply (case_tac "height (insrt x t2) = height t1 + 2")
 apply(rule conjI)
  apply (simp add:avl_r_bal)
 apply (frule_tac n = n in height_r_bal) apply simp apply simp
 apply (simp add: max_def) apply arith
apply(rule conjI)
 apply fastsimp
apply (simp add: max_def) apply arith
done

lemmas avl_insrt = avl_insrt_aux[THEN conjunct1]


subsubsection "Correctness of insertion"

lemma set_of_l_bal: "height l = height r + 2 \<Longrightarrow>
 set_of (l_bal(x, l, r)) = insert x (set_of l \<union> set_of r)"
apply(cases l)
apply (auto simp:max_def mkt_def split:tree.splits)
done

lemma set_of_r_bal: "height r = height l + 2 \<Longrightarrow>
 set_of (r_bal(x, l, r)) = insert x (set_of l \<union> set_of r)"
apply(cases r)
apply (auto simp:max_def mkt_def split:tree.splits)
done

text{* Correctness of @{const insrt}: *}

theorem set_of_insrt: 
"avl t \<Longrightarrow> set_of(insrt x t) = insert x (set_of t)"
apply (induct t)
 apply simp
apply(force simp: avl_insrt set_of_l_bal set_of_r_bal)
done


subsubsection {*Correctness of lookup *}

theorem is_in_correct: "is_ord t \<Longrightarrow> is_in k t = (k : set_of t)"
by (induct "t") auto


subsubsection {* Insertion maintains order *}

lemma is_ord_l_bal:
 "\<lbrakk> is_ord(MKT x l r h); height l = height r + 2 \<rbrakk> \<Longrightarrow> is_ord(l_bal(x,l,r))"
apply (cases l)
apply (auto simp: mkt_def split:tree.splits intro: order_less_trans)
done

lemma is_ord_r_bal:
 "\<lbrakk> is_ord(MKT x l r h); height r = height l + 2 \<rbrakk> \<Longrightarrow> is_ord(r_bal(x,l,r))"
apply (cases r)
apply (auto simp: mkt_def split:tree.splits intro: order_less_trans)
done

text{* If the order is linear, @{const insrt} maintains the order: *}

theorem is_ord_insrt:
"\<lbrakk> avl t; is_ord t \<rbrakk> \<Longrightarrow> is_ord(insrt (x::'a::linorder) t)"
apply (induct t)
 apply simp
apply (simp add:is_ord_l_bal is_ord_r_bal avl_insrt set_of_insrt
                linorder_not_less order_neq_le_trans)
done


end
