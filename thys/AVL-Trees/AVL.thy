(*  Title:      AVL Trees
    ID:         $Id: AVL.thy,v 1.8 2006-05-25 21:14:43 nipkow Exp $
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

consts ht :: "'a tree \<Rightarrow> nat"
primrec
"ht ET = 0"
"ht (MKT x l r h) = h"

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

constdefs
 comb_ht :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> nat"
"comb_ht t1 t2 == max (ht t1) (ht t2) + 1"

datatype bal = Just | Left | Right

constdefs
 bal :: "'a tree \<Rightarrow> bal"
"bal t \<equiv> case t of ET \<Rightarrow> Just
                 | MKT n l r h \<Rightarrow> let hl = ht l; hr = ht r
                                  in if hl = hr then Just
                                     else if hl < hr then Right else Left"

consts
  r_rot  :: "'a * 'a tree * 'a tree \<Rightarrow> 'a tree"
  l_rot  :: "'a * 'a tree * 'a tree \<Rightarrow> 'a tree"
  lr_rot :: "'a * 'a tree * 'a tree \<Rightarrow> 'a tree"
  rl_rot :: "'a * 'a tree * 'a tree \<Rightarrow> 'a tree"

recdef r_rot "{}"
"r_rot(n, MKT ln ll lr h, r) =
  (let h = comb_ht lr r
   in MKT ln ll (MKT n lr r h) (1 + max (ht ll) h))"

recdef l_rot "{}"
"l_rot(n, l, MKT rn rl rr h) =
  (let h = comb_ht l rl
   in MKT rn (MKT n l rl h) rr (1 + max h (ht rr)))"

recdef lr_rot "{}"
"lr_rot(n, MKT ln ll (MKT lrn lrl lrr lrh) lh, r) =
   (let h1 = comb_ht ll lrl; h2 = comb_ht lrr r
    in MKT lrn (MKT ln ll lrl h1) (MKT n lrr r h2) (1 + max h1 h2))"

recdef rl_rot "{}"
"rl_rot(n, l, MKT rn (MKT rln rll rlr rlh) rr rh) =
  (let h1 = comb_ht l rll; h2 = comb_ht rlr rr
   in MKT rln (MKT n l rll h1) (MKT rn rlr rr h2) (1 + max h1 h2))"

constdefs
 l_bal :: "'a \<Rightarrow> 'a tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree"
"l_bal n l r \<equiv> if bal l = Right then lr_rot(n,l,r) else r_rot(n,l,r)"

 r_bal :: "'a \<Rightarrow> 'a tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree"
"r_bal n l r \<equiv> if bal r = Left then rl_rot (n, l, r) else l_rot (n, l, r)"

primrec
"insrt x ET = MKT x ET ET 1"
"insrt x (MKT n l r h) = 
   (if x=n
    then MKT n l r h
    else if x<n
         then let l' = insrt x l; hl' = ht l'; hr = height r
              in if hl' = 2+hr then l_bal n l' r
                 else MKT n l' r (1 + max hl' hr)
         else let r' = insrt x r; hl = ht l; hr' = ht r'
              in if hr' = 2+hl then r_bal n l r'
                 else MKT n l r' (1 + max hl hr'))"

subsection"Correctness proof"

subsubsection "@{const avl} properties"

declare Let_def [simp]

lemma [simp]: "avl t \<Longrightarrow> ht t = height t"
by (induct t) simp_all

lemma avl_lr_rot:
"\<lbrakk> height l = Suc(Suc(height r)); bal l = Right; avl l; avl r \<rbrakk>
  \<Longrightarrow> avl (lr_rot (n, l, r))"
apply (unfold bal_def)
apply (cases l)
 apply simp
apply (rename_tac t1 t2 h)
apply (case_tac t2)
 apply simp
apply (simp add: max_def comb_ht_def split: split_if_asm)
apply arith
done


lemma avl_r_rot: 
"\<lbrakk> height l = Suc(Suc(height r)); bal l \<noteq> Right; avl l; avl r \<rbrakk>
  \<Longrightarrow> avl (r_rot (n, l, r))"
apply (unfold bal_def)
apply (cases l)
 apply simp
apply (simp add: max_def comb_ht_def split: split_if_asm)
done


lemma avl_rl_rot: 
"\<lbrakk> height r = Suc(Suc(height l)); bal r = Left; avl l; avl r \<rbrakk>
  \<Longrightarrow> avl (rl_rot (n, l, r))"
apply (unfold bal_def)
apply (cases r)
 apply simp
apply (rename_tac t1 t2 h)
apply (case_tac t1)
 apply simp
apply (simp add: max_def comb_ht_def split: split_if_asm)
apply arith
done


lemma avl_l_rot: 
"\<lbrakk> height r = Suc(Suc(height l)); bal r \<noteq> Left; avl l; avl r \<rbrakk>
  \<Longrightarrow> avl (l_rot (n, l, r))"
apply (unfold bal_def)
apply (cases r)
 apply simp
apply (simp add: max_def comb_ht_def split: split_if_asm)
done


text {* Lemmas about height after rotation *}

lemma height_lr_rot:
"\<lbrakk> avl l; avl r; bal l = Right; height l = Suc(Suc(height r)) \<rbrakk>
 \<Longrightarrow> height (lr_rot (n, l, r)) = height r + 2"
apply (unfold bal_def)
apply (cases l)
 apply simp
apply (rename_tac t1 t2 u)
apply (case_tac t2)
 apply simp
apply (simp add: max_def split: split_if_asm)
done


lemma height_r_rot: 
"\<lbrakk> avl l; avl r; height l = Suc(Suc(height r)); bal l \<noteq> Right \<rbrakk>
  \<Longrightarrow> height (r_rot (n, l, r)) = height r + 2 \<or>
      height (r_rot (n, l, r)) = height r + 3"
apply (unfold bal_def)
apply (cases l)
 apply simp
apply (simp add: max_def split: split_if_asm)
done


lemma height_l_bal:
"\<lbrakk> height l = Suc(Suc(height r)); avl l; avl r \<rbrakk>
  \<Longrightarrow> height (l_bal n l r) = height r + 2 \<or>
      height (l_bal n l r) = height r + 3"
apply (unfold l_bal_def)
apply (cases "bal l = Right")
 apply (fastsimp simp: max_def dest: height_lr_rot)
apply (fastsimp simp: max_def dest: height_r_rot)
done


lemma height_rl_rot:
"\<lbrakk> avl l; avl r; height r = Suc(Suc(height l)); bal r = Left \<rbrakk> \<Longrightarrow>
 height (rl_rot (n, l, r)) = height l + 2"
apply (unfold bal_def)
apply (cases r)
 apply simp
apply (rename_tac t1 t2 u)
apply (case_tac t1)
 apply simp
apply (simp add: max_def split: split_if_asm)
done


lemma height_l_rot:
"\<lbrakk> avl l; avl r; height r = Suc(Suc(height l)) ; bal r \<noteq> Left \<rbrakk> \<Longrightarrow>
 height (l_rot (n, l, r)) = height l + 2 \<or>  
 height (l_rot (n, l, r)) = height l + 3"
apply (unfold bal_def)
apply (cases r)
 apply simp
apply (simp add: max_def split:split_if_asm)
done


lemma height_r_bal: 
"\<lbrakk> height r = Suc(Suc(height l)); avl l;  avl r \<rbrakk>
  \<Longrightarrow> height (r_bal n l r) = height l + 2 \<or>
      height (r_bal n l r) = height l + 3"
apply (unfold r_bal_def)
apply (cases "bal r = Left")
 apply (fastsimp simp: max_def dest: height_rl_rot)
apply (fastsimp simp: max_def dest: height_l_rot)
done

(* It apppears that these two properties need to be proved simultaneously: *)

text{* Insertion maintains the AVL property: *}

theorem avl_insrt_aux:
"avl t \<Longrightarrow> avl(insrt x t) \<and>
 (height (insrt x t) = height t \<or> height (insrt x t) = Suc(height t))"
apply (induct "t")
 apply simp
apply (rename_tac n t1 t2 h)
apply (case_tac "x=n")
 apply simp
apply (case_tac "x<n")
 apply (case_tac "height (insrt x t1) = Suc (Suc (height t2))")
  apply(rule conjI)
   apply (case_tac "bal (insrt x t1) = Right")
    apply (fastsimp intro: avl_lr_rot simp add: l_bal_def)
   apply (fastsimp intro: avl_r_rot simp add: l_bal_def)
  apply (frule_tac n = n in height_l_bal) apply simp apply simp
  apply (simp add: max_def) apply arith
 apply(rule conjI)
  apply fastsimp
 apply (simp add: max_def) apply arith
apply (case_tac "height (insrt x t2) = Suc (Suc (height t1))")
 apply(rule conjI)
  apply (case_tac "bal (insrt x t2) = Left")
   apply (fastsimp intro: avl_rl_rot simp add: r_bal_def)
  apply (fastsimp intro: avl_l_rot simp add: r_bal_def)
 apply (frule_tac n = n in height_r_bal) apply simp apply simp
 apply (simp add: max_def) apply arith
apply(rule conjI)
 apply fastsimp
apply (simp add: max_def) apply arith
done

lemmas avl_insrt = avl_insrt_aux[THEN conjunct1]

subsubsection "@{const set_of} properties"

lemma set_of_lr_rot: 
"\<lbrakk> avl l; height l = Suc(Suc(height r)); bal l = Right \<rbrakk>
  \<Longrightarrow> set_of (lr_rot(n,l,r)) = insert n (set_of l \<union> set_of r)"
apply (unfold bal_def)
apply (cases l)
 apply simp
apply (rename_tac t1 t2 u)
apply (case_tac t2)
 apply simp
apply fastsimp
done


lemma set_of_r_rot: 
"\<lbrakk> height l = Suc(Suc(height r)); bal l \<noteq> Right \<rbrakk>
  \<Longrightarrow> set_of(r_rot(n,l,r)) = insert n (set_of l  \<union> set_of r)"
apply (unfold bal_def)
apply (cases l)
 apply simp
apply fastsimp
done


lemma set_of_rl_rot:
"\<lbrakk> avl r; height r = Suc(Suc(height l)); bal r = Left \<rbrakk>
  \<Longrightarrow> set_of(rl_rot(n,l,r)) = insert n (set_of l  \<union> set_of r)"
apply (unfold bal_def)
apply (cases r)
 apply simp
apply (rename_tac t1 t2 u)
apply (case_tac t1)
 apply (simp add: max_def le_def)
apply fastsimp
done


lemma set_of_l_rot:
"\<lbrakk> height r = Suc(Suc(height l)); bal r \<noteq> Left \<rbrakk>
  \<Longrightarrow> set_of(l_rot(n,l,r)) = insert n (set_of l  \<union> set_of r)"
apply (unfold bal_def)
apply (cases r)
 apply simp
apply fastsimp
done

text{* Functional correctness of @{const insrt}: *}

theorem set_of_insrt: 
"avl t \<Longrightarrow> set_of(insrt x t) = insert x (set_of t)"
apply (induct t)
 apply simp
apply (force simp: l_bal_def r_bal_def avl_insrt
                   set_of_lr_rot set_of_r_rot set_of_rl_rot set_of_l_rot)
done


subsubsection "@{const is_in} properties"

text{* Correctness of @{text is_in}: *}

theorem is_in_correct: "is_ord t \<Longrightarrow> is_in k t = (k : set_of t)"
by (induct "t") auto


subsubsection "@{const is_ord} properties"

lemma is_ord_lr_rot: 
"\<lbrakk> avl l; height l = Suc(Suc(height r)); bal l = Right; is_ord (MKT n l r h) \<rbrakk>
  \<Longrightarrow> is_ord (lr_rot (n, l, r))"
apply (unfold bal_def)
apply (cases l)
 apply simp
apply (rename_tac t1 t2 u)
apply (case_tac t2)
 apply simp
apply simp
apply (blast intro: order_less_trans)
done


lemma is_ord_r_rot:
"\<lbrakk> avl l; height l = Suc(Suc(height r)); bal l \<noteq> Right; is_ord (MKT n l r h) \<rbrakk>
  \<Longrightarrow> is_ord (r_rot (n, l, r))"
apply (unfold bal_def)
apply (cases l)
apply (simp)
apply (auto intro: order_less_trans)
done


lemma is_ord_rl_rot: 
"\<lbrakk> avl r; height r = Suc(Suc(height l)); bal r = Left; is_ord (MKT n l r h) \<rbrakk>
  \<Longrightarrow> is_ord (rl_rot (n, l, r))"
apply (unfold bal_def)
apply (cases r)
 apply simp
apply (rename_tac t1 t2 u)
apply (case_tac t1)
 apply (simp add: le_def)
apply simp
apply (blast intro: order_less_trans)
done


lemma is_ord_l_rot: 
"\<lbrakk> avl r; height r = Suc(Suc(height l)); bal r \<noteq> Left; is_ord (MKT n l r h) \<rbrakk>
  \<Longrightarrow> is_ord (l_rot (n, l, r))"
apply (unfold bal_def)
apply (cases r)
 apply simp
apply simp
apply (blast intro: order_less_trans)
done

text{* If the order is linear, @{const insrt} maintains the order: *}

theorem is_ord_insrt:
"\<lbrakk> avl t; is_ord t \<rbrakk> \<Longrightarrow> is_ord(insrt (x::'a::linorder) t)"
apply (induct t)
 apply simp
apply (cut_tac x = "x" and y = "a" in linorder_less_linear)
apply (fastsimp simp: l_bal_def r_bal_def avl_insrt
           is_ord_lr_rot is_ord_r_rot is_ord_l_rot is_ord_rl_rot set_of_insrt)
done


end
