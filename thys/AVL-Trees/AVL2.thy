(*  Title:      AVL Trees
    ID:         $Id: AVL2.thy,v 1.1 2006-05-25 21:14:43 nipkow Exp $
    Author:     Tobias Nipkow and Cornelia Pusch,
                converted to Isar by Gerwin Klein
                contributions by Achim Brucker, Burkhart Wolff and Jan Smaus
    Maintainer: Gerwin Klein <gerwin.klein at nicta.com.au>

    see the file Changelog for a list of changes
*)

header "AVL Trees in 2 Stages"

theory AVL2
imports Main
begin

text {* This development of AVL trees leads to the same implementation
as the monolithic one (in theorey AVL) but via an intermediate
abstraction: AVL trees where the height is recomputed rather than
stored in the tree. This two-stage devlopment is longer than the
monolithic one but each individual step is simpler. It should really
be viewed as a blueprint for the development of data structures where
some of the fields contain redundant information (for efficiency
reasons). *}

subsection"Step 1: Pure binary and AVL trees"

text{* The basic formulation of AVL trees builds on pure binary trees
and recomputes all height information whenever it is required. This
simplifies the correctness proofs. *}

datatype 'a tree\<^isub>0 = ET\<^isub>0 |  MKT\<^isub>0 'a "'a tree\<^isub>0" "'a tree\<^isub>0"

subsubsection "Auxiliary functions"

consts
  height :: "'a tree\<^isub>0 \<Rightarrow> nat"
  set_of :: "'a tree\<^isub>0 \<Rightarrow> 'a set" 
  is_ord :: "('a::order) tree\<^isub>0 \<Rightarrow> bool" 
  is_bal :: "'a tree\<^isub>0 \<Rightarrow> bool"

primrec
"height ET\<^isub>0 = 0"
"height (MKT\<^isub>0 n l r) = 1 + max (height l) (height r)"

primrec
"set_of ET\<^isub>0 = {}"
"set_of (MKT\<^isub>0 n l r) = insert n (set_of l \<union> set_of r)"

primrec
"is_ord ET\<^isub>0 = True"
"is_ord (MKT\<^isub>0 n l r) =
   ((\<forall>n' \<in> set_of l. n' < n) \<and> (\<forall>n' \<in> set_of r. n < n') \<and> is_ord l \<and> is_ord r)"

primrec
"is_bal ET\<^isub>0 = True"
"is_bal (MKT\<^isub>0 n l r) =
 ((height l = height r \<or> height l = 1+height r \<or> height r = 1+height l) \<and>
  is_bal l \<and> is_bal r)"


subsubsection "AVL interface and simple implementation"

consts
  is_in\<^isub>0 :: "('a::order) \<Rightarrow> 'a tree\<^isub>0 \<Rightarrow> bool"
  insrt\<^isub>0 :: "'a::order \<Rightarrow> 'a tree\<^isub>0 \<Rightarrow> 'a tree\<^isub>0"


primrec
 "is_in\<^isub>0 k ET\<^isub>0 = False"
 "is_in\<^isub>0 k (MKT\<^isub>0 n l r) = (if k = n then True else
                         if k<n then (is_in\<^isub>0 k l)
                         else (is_in\<^isub>0 k r))"

datatype bal = Just | Left | Right

constdefs
 bal\<^isub>0 :: "'a tree\<^isub>0 \<Rightarrow> bal"
"bal\<^isub>0 t \<equiv> case t of ET\<^isub>0 \<Rightarrow> Just
                  | MKT\<^isub>0 n l r \<Rightarrow> if height l = height r then Just else
                                 if height l < height r then Right else Left"

consts
  r_rot\<^isub>0  :: "'a \<times> 'a tree\<^isub>0 \<times> 'a tree\<^isub>0 \<Rightarrow> 'a tree\<^isub>0"
  l_rot\<^isub>0  :: "'a \<times> 'a tree\<^isub>0 \<times> 'a tree\<^isub>0 \<Rightarrow> 'a tree\<^isub>0"
  lr_rot\<^isub>0 :: "'a \<times> 'a tree\<^isub>0 \<times> 'a tree\<^isub>0 \<Rightarrow> 'a tree\<^isub>0"
  rl_rot\<^isub>0 :: "'a \<times> 'a tree\<^isub>0 \<times> 'a tree\<^isub>0 \<Rightarrow> 'a tree\<^isub>0"

recdef r_rot\<^isub>0 "{}"
"r_rot\<^isub>0 (n, MKT\<^isub>0 ln ll lr, r) = MKT\<^isub>0 ln ll (MKT\<^isub>0 n lr r)"

recdef l_rot\<^isub>0 "{}"
"l_rot\<^isub>0(n, l, MKT\<^isub>0 rn rl rr) = MKT\<^isub>0 rn (MKT\<^isub>0 n l rl) rr"

recdef lr_rot\<^isub>0 "{}"
"lr_rot\<^isub>0(n, MKT\<^isub>0 ln ll (MKT\<^isub>0 lrn lrl lrr), r) =
 MKT\<^isub>0 lrn (MKT\<^isub>0 ln ll lrl) (MKT\<^isub>0 n lrr r)"

recdef rl_rot\<^isub>0 "{}"
"rl_rot\<^isub>0(n, l, MKT\<^isub>0 rn (MKT\<^isub>0 rln rll rlr) rr) =
 MKT\<^isub>0 rln (MKT\<^isub>0 n l rll) (MKT\<^isub>0 rn rlr rr)"


constdefs 
 l_bal\<^isub>0 :: "'a \<Rightarrow> 'a tree\<^isub>0 \<Rightarrow> 'a tree\<^isub>0 \<Rightarrow> 'a tree\<^isub>0"
"l_bal\<^isub>0 n l r \<equiv> if bal\<^isub>0 l = Right then lr_rot\<^isub>0 (n, l, r) else r_rot\<^isub>0 (n, l, r)"

 r_bal\<^isub>0 :: "'a \<Rightarrow> 'a tree\<^isub>0 \<Rightarrow> 'a tree\<^isub>0 \<Rightarrow> 'a tree\<^isub>0"
"r_bal\<^isub>0 n l r \<equiv> if bal\<^isub>0 r = Left then rl_rot\<^isub>0 (n, l, r) else l_rot\<^isub>0 (n, l, r)"

primrec
"insrt\<^isub>0 x ET\<^isub>0 = MKT\<^isub>0 x ET\<^isub>0 ET\<^isub>0"
"insrt\<^isub>0 x (MKT\<^isub>0 n l r) = 
   (if x=n
    then MKT\<^isub>0 n l r
    else if x<n
         then let l' = insrt\<^isub>0 x l
              in if height l' = 2+height r
                 then l_bal\<^isub>0 n l' r
                 else MKT\<^isub>0 n l' r
         else let r' = insrt\<^isub>0 x r
              in if height r' = 2+height l
                 then r_bal\<^isub>0 n l r'
                 else MKT\<^isub>0 n l r')"


subsubsection "@{const is_bal} properties"

declare Let_def [simp]

lemma is_bal_lr_rot:
"\<lbrakk> height l = Suc(Suc(height r)); bal\<^isub>0 l = Right; is_bal l; is_bal r \<rbrakk>
  \<Longrightarrow> is_bal (lr_rot\<^isub>0 (n, l, r))"
apply (unfold bal\<^isub>0_def)
apply (cases l)
 apply simp
apply (rename_tac t1 t2)
apply (case_tac t2)
 apply simp
apply (simp add: max_def split: split_if_asm)
apply arith
done


lemma is_bal_r_rot: 
"\<lbrakk> height l = Suc(Suc(height r)); bal\<^isub>0 l \<noteq> Right; is_bal l; is_bal r \<rbrakk>
  \<Longrightarrow> is_bal (r_rot\<^isub>0 (n, l, r))"
apply (unfold bal\<^isub>0_def)
apply (cases "l")
 apply simp
apply (simp add: max_def split: split_if_asm)
done


lemma is_bal_rl_rot: 
"\<lbrakk> height r = Suc(Suc(height l)); bal\<^isub>0 r = Left; is_bal l; is_bal r \<rbrakk>
  \<Longrightarrow> is_bal (rl_rot\<^isub>0 (n, l, r))"
apply (unfold bal\<^isub>0_def)
apply (cases r)
 apply simp
apply (rename_tac t1 t2)
apply (case_tac t1)
 apply (simp add: max_def split: split_if_asm)
apply (simp add: max_def split: split_if_asm)
apply arith
done


lemma is_bal_l_rot: 
"\<lbrakk> height r = Suc(Suc(height l)); bal\<^isub>0 r \<noteq> Left; is_bal l; is_bal r \<rbrakk>
  \<Longrightarrow> is_bal (l_rot\<^isub>0 (n, l, r))"
apply (unfold bal\<^isub>0_def)
apply (cases r)
 apply simp 
apply (simp add: max_def split: split_if_asm)
done


text {* Lemmas about height after rotation *}

lemma height_lr_rot:
"\<lbrakk> bal\<^isub>0 l = Right; height l = Suc(Suc(height r)) \<rbrakk>
 \<Longrightarrow> height (lr_rot\<^isub>0 (n, l, r)) = height r + 2"
apply (unfold bal\<^isub>0_def)
apply (cases l)
 apply simp
apply (rename_tac t1 t2)
apply (case_tac t2)
 apply simp
apply (simp add: max_def split: split_if_asm)
done


lemma height_r_rot: 
"\<lbrakk> height l = Suc(Suc(height r)); bal\<^isub>0 l \<noteq> Right \<rbrakk>
  \<Longrightarrow> height (r_rot\<^isub>0 (n, l, r)) = height r + 2 \<or>
      height (r_rot\<^isub>0 (n, l, r)) = height r + 3"
apply (unfold bal\<^isub>0_def)
apply (cases l)
 apply simp 
apply (simp add: max_def split: split_if_asm)
done


lemma height_l_bal:
"height l = Suc(Suc(height r))   
  \<Longrightarrow> height (l_bal\<^isub>0 n l r) = height r + 2 \<or>
      height (l_bal\<^isub>0 n l r)  = height r + 3"
apply (unfold l_bal\<^isub>0_def)
apply (cases "bal\<^isub>0 l = Right")
 apply (fastsimp dest: height_lr_rot)
apply (fastsimp dest: height_r_rot)
done


lemma height_rl_rot:
"\<lbrakk> height r = Suc(Suc(height l)); bal\<^isub>0 r = Left \<rbrakk> \<Longrightarrow>
 height (rl_rot\<^isub>0 (n, l, r))  = height l + 2"
apply (unfold bal\<^isub>0_def)
apply (cases r)
 apply simp
apply (rename_tac t1 t2)
apply (case_tac t1)
 apply simp
apply (simp add: max_def split: split_if_asm)
done


lemma height_l_rot:
"\<lbrakk> height r = Suc(Suc(height l)) ; bal\<^isub>0 r \<noteq> Left \<rbrakk> \<Longrightarrow>
 height (l_rot\<^isub>0 (n, l, r)) = height l + 2 \<or>
 height (l_rot\<^isub>0 (n, l, r)) = height l + 3"
apply (unfold bal\<^isub>0_def)
apply (cases r)
 apply simp
apply (simp add: max_def split:split_if_asm)
done


lemma height_r_bal: 
"height r = Suc(Suc(height l))   
  \<Longrightarrow> height (r_bal\<^isub>0 n l r) = height l + 2 \<or>
      height (r_bal\<^isub>0 n l r) = height l + 3"
apply (unfold r_bal\<^isub>0_def)
apply (cases "bal\<^isub>0 r = Left")
 apply (fastsimp dest: height_rl_rot)
apply (fastsimp dest: height_l_rot)
done

lemma height_insrt:
"is_bal t \<longrightarrow>
 height (insrt\<^isub>0 x t) = height t \<or> height (insrt\<^isub>0 x t) = Suc(height t)"
apply (induct "t")
 apply simp
apply (rename_tac n t1 t2)
apply (case_tac "x=n")
 apply simp
apply (case_tac "x<n")
 apply (case_tac "height (insrt\<^isub>0 x t1) = Suc (Suc (height t2))")
  apply (frule_tac n = n in height_l_bal)
  apply (simp add: max_def) apply arith
 apply (simp add: max_def) apply arith
apply (case_tac "height (insrt\<^isub>0 x t2) = Suc (Suc (height t1))")
 apply (frule_tac n = n in height_r_bal)
 apply (simp add: max_def) apply arith
apply (simp add: max_def) apply arith
done


text{* Insertion maintains the AVL property: *}

theorem is_bal_insrt: 
"is_bal t \<Longrightarrow> is_bal(insrt\<^isub>0 x t)"
apply (induct "t")
 apply simp
apply (rename_tac n t1 t2)
apply (case_tac "x=n")
 apply simp
apply (case_tac "x<n")
 apply (case_tac "height (insrt\<^isub>0 x t1) = Suc (Suc (height t2))")
  apply (case_tac "bal\<^isub>0 (insrt\<^isub>0 x t1) = Right")
   apply (fastsimp intro: is_bal_lr_rot simp add: l_bal\<^isub>0_def)
  apply (fastsimp intro: is_bal_r_rot simp add: l_bal\<^isub>0_def)
 apply (cut_tac x = "x" and t = "t1" in height_insrt)
 apply  fastsimp
apply (case_tac "height (insrt\<^isub>0 x t2) = Suc (Suc (height t1))")
 apply (case_tac "bal\<^isub>0 (insrt\<^isub>0 x t2) = Left")
  apply (fastsimp intro: is_bal_rl_rot simp add: r_bal\<^isub>0_def)
 apply (fastsimp intro: is_bal_l_rot simp add: r_bal\<^isub>0_def)
 apply (cut_tac x = "x" and t = "t2" in height_insrt)
 apply  fastsimp
done


subsubsection "@{const set_of} properties"

lemma set_of_lr_rot: 
"\<lbrakk> height l = Suc(Suc(height r)); bal\<^isub>0 l = Right \<rbrakk>
  \<Longrightarrow> set_of (lr_rot\<^isub>0(n,l,r)) = set_of (MKT\<^isub>0 n l r)"
apply (unfold bal\<^isub>0_def)
apply (cases l)
 apply simp
apply (rename_tac t1 t2)
apply (case_tac t2)
 apply simp
apply fastsimp
done


lemma set_of_r_rot: 
"\<lbrakk> height l = Suc(Suc(height r)); bal\<^isub>0 l \<noteq> Right \<rbrakk>
  \<Longrightarrow> set_of(r_rot\<^isub>0(n,l,r)) = set_of(MKT\<^isub>0 n l r)"
apply (unfold bal\<^isub>0_def)
apply (cases l)
 apply simp
apply fastsimp
done


lemma set_of_rl_rot:
"\<lbrakk> height r = Suc(Suc(height l)); bal\<^isub>0 r = Left \<rbrakk>
  \<Longrightarrow> set_of(rl_rot\<^isub>0(n,l,r)) = set_of(MKT\<^isub>0 n l r)"
apply (unfold bal\<^isub>0_def)
apply (cases r)
 apply simp
apply (rename_tac t1 t2)
apply (case_tac t1)
 apply (simp add: max_def le_def)
apply fastsimp
done


lemma set_of_l_rot:
"\<lbrakk> height r = Suc(Suc(height l)); bal\<^isub>0 r \<noteq> Left \<rbrakk>
  \<Longrightarrow> set_of(l_rot\<^isub>0(n,l,r)) = set_of(MKT\<^isub>0 n l r)"
apply (unfold bal\<^isub>0_def)
apply (cases r)
 apply simp
apply fastsimp
done

text{* Functional correctness of @{const insrt\<^isub>0}: *}

theorem set_of_insrt: 
"set_of(insrt\<^isub>0 x t) = insert x (set_of t)"
apply (induct t)
 apply simp
apply (simp add: l_bal\<^isub>0_def set_of_lr_rot set_of_r_rot r_bal\<^isub>0_def 
                 set_of_rl_rot set_of_l_rot)
apply blast
done


subsubsection {*@{text is_in} properties*}

text{* Correctness of @{text is_in\<^isub>0}: *}

theorem is_in_correct: "is_ord t \<Longrightarrow> is_in\<^isub>0 k t = (k : set_of t)"
by (induct "t") auto


subsubsection "@{const is_ord} properties"

lemma is_ord_lr_rot: 
"\<lbrakk> height l = Suc(Suc(height r)); bal\<^isub>0 l = Right; is_ord (MKT\<^isub>0 n l r) \<rbrakk>
  \<Longrightarrow> is_ord (lr_rot\<^isub>0 (n, l, r))"
apply (unfold bal\<^isub>0_def)
apply (cases l)
 apply simp
apply (rename_tac t1 t2)
apply (case_tac t2)
 apply simp
apply simp
apply (blast intro: order_less_trans)
done


lemma is_ord_r_rot:
"\<lbrakk> height l = Suc(Suc(height r)); bal\<^isub>0 l \<noteq> Right; is_ord (MKT\<^isub>0 n l r) \<rbrakk>
  \<Longrightarrow> is_ord (r_rot\<^isub>0 (n, l, r))"
apply (unfold bal\<^isub>0_def)
apply (cases l)
apply (simp (no_asm_simp))
apply (auto intro: order_less_trans)
done


lemma is_ord_rl_rot: 
"\<lbrakk> height r = Suc(Suc(height l)); bal\<^isub>0 r = Left; is_ord (MKT\<^isub>0 n l r) \<rbrakk>
  \<Longrightarrow> is_ord (rl_rot\<^isub>0 (n, l, r))"
apply (unfold bal\<^isub>0_def)
apply (cases r)
 apply simp
apply (rename_tac t1 t2)
apply (case_tac t1)
 apply (simp add: le_def)
apply simp
apply (blast intro: order_less_trans)
done


lemma is_ord_l_rot: 
"\<lbrakk> height r = Suc(Suc(height l)); bal\<^isub>0 r \<noteq> Left; is_ord (MKT\<^isub>0 n l r) \<rbrakk>
  \<Longrightarrow> is_ord (l_rot\<^isub>0 (n, l, r))"
apply (unfold bal\<^isub>0_def)
apply (cases r)
 apply simp
apply simp
apply (blast intro: order_less_trans)
done

text{* If the order is linear, @{const insrt\<^isub>0} maintains the order: *}

theorem is_ord_insrt:
"is_ord t \<Longrightarrow> is_ord(insrt\<^isub>0 (x::'a::linorder) t)"
apply (induct t)
 apply simp
apply (cut_tac x = "x" and y = "a" in linorder_less_linear)
apply (fastsimp simp add: l_bal\<^isub>0_def is_ord_lr_rot is_ord_r_rot r_bal\<^isub>0_def 
                           is_ord_l_rot is_ord_rl_rot set_of_insrt)
done


subsection "Step 2: Binary and AVL trees with height information"

datatype 'a tree = ET |  MKT 'a "'a tree" "'a tree" nat


subsubsection"Auxiliary functions"

consts erase :: "'a tree \<Rightarrow> 'a tree\<^isub>0"
primrec
"erase ET = ET\<^isub>0"
"erase (MKT x l r h) = MKT\<^isub>0 x (erase l) (erase r)"

consts ht :: "'a tree \<Rightarrow> nat"
primrec
"ht ET = 0"
"ht (MKT x l r h) = h"

constdefs comb_ht :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> nat"
"comb_ht t1 t2 == 1 + max (ht t1) (ht t2)"

consts hinv :: "'a tree \<Rightarrow> bool"
primrec
"hinv ET = True"
"hinv (MKT x l r h) = (h = 1 + max (height(erase l)) (height(erase r))
                        & hinv l & hinv r)"

constdefs
 avl :: "'a tree \<Rightarrow> bool"
"avl t \<equiv> is_bal(erase t) \<and> hinv t"

subsubsection "AVL interface and efficient implementation"

consts
  is_in :: "('a::order) \<Rightarrow> 'a tree \<Rightarrow> bool"
  insrt :: "'a::order \<Rightarrow> 'a tree \<Rightarrow> 'a tree"


primrec
"is_in k ET = False"
"is_in k (MKT n l r h) = (if k = n then True else
                          if k < n then (is_in k l)
                          else (is_in k r))"

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
         then let l' = insrt x l; hl' = ht l'; hr = ht r
              in if hl' = 2+hr then l_bal n l' r
                 else MKT n l' r (1 + max hl' hr)
         else let r' = insrt x r; hl = ht l; hr' = ht r'
              in if hr' = 2+hl then r_bal n l r'
                 else MKT n l r' (1 + max hl hr'))"


subsubsection "Correctness proof"

text{* The auxiliary functions @{const ht} and @{const bal}
correctly implement @{const height} and @{const bal\<^isub>0}: *}

lemma [simp]: "hinv t \<Longrightarrow> ht t = height(erase t)"
by (induct t) simp_all

lemma [simp]: "hinv t \<Longrightarrow> bal t = bal\<^isub>0(erase t)"
by (induct t) (simp_all add:bal\<^isub>0_def bal_def)

lemma hinv_lr_rot:
"\<lbrakk> hinv l; hinv r;
   height(erase l) = Suc(Suc(height(erase r))); bal\<^isub>0(erase l) = Right \<rbrakk>
  \<Longrightarrow> hinv(lr_rot(n,l,r))"
apply (unfold bal\<^isub>0_def)
apply (cases l)
 apply simp
apply (rename_tac t1 t2 h)
apply (case_tac t2)
 apply simp
apply (simp add: comb_ht_def)
done

lemma hinv_r_rot:
"\<lbrakk> hinv l;  hinv r;
   height(erase l) = Suc(Suc(height(erase r))); bal\<^isub>0(erase l) \<noteq> Right \<rbrakk>
  \<Longrightarrow> hinv(r_rot(n,l,r))"
by (cases l) (simp_all add:bal\<^isub>0_def comb_ht_def)

lemma hinv_rl_rot:
"\<lbrakk> hinv l; hinv r;
   height(erase r) = Suc(Suc(height(erase l))); bal\<^isub>0(erase r) = Left \<rbrakk>
  \<Longrightarrow> hinv(rl_rot(n,l,r))"
apply (unfold bal\<^isub>0_def)
apply (cases r)
 apply simp
apply (rename_tac t1 t2 h)
apply (case_tac t1)
 apply simp
apply (simp add: comb_ht_def)
done

lemma hinv_l_rot: 
"\<lbrakk> hinv l; hinv r;
   height(erase r) = Suc(Suc(height(erase l))); bal\<^isub>0(erase r) \<noteq> Left \<rbrakk>
  \<Longrightarrow> hinv(l_rot(n,l,r))"
by (cases r) (simp_all add:bal\<^isub>0_def comb_ht_def)


text{* Function @{const insrt} maintains the invariant: *}

theorem hinv_insrt[simp]: "hinv t \<Longrightarrow> hinv(insrt x t)"
apply(induct t)
 apply simp
apply(simp add:l_bal_def hinv_lr_rot hinv_r_rot
               r_bal_def hinv_rl_rot hinv_l_rot)
done

lemma erase_lr_rot:
"\<lbrakk> height(erase l) = Suc(Suc(height(erase r))); bal\<^isub>0(erase l) = Right \<rbrakk>
  \<Longrightarrow> erase(lr_rot(n,l,r)) = lr_rot\<^isub>0(n, erase l, erase r)"
apply (unfold bal\<^isub>0_def)
apply (cases l)
 apply simp
apply (rename_tac t1 t2 h)
apply (case_tac t2)
 apply simp
apply simp
done

lemma erase_r_rot:
"\<lbrakk> height(erase l) = Suc(Suc(height(erase r))); bal\<^isub>0(erase l) \<noteq> Right \<rbrakk>
  \<Longrightarrow> erase(r_rot(n,l,r)) = r_rot\<^isub>0(n, erase l, erase r)"
by (cases l) (simp_all add:bal\<^isub>0_def)

lemma erase_rl_rot:
"\<lbrakk> height(erase r) = Suc(Suc(height(erase l))); bal\<^isub>0(erase r) = Left \<rbrakk>
  \<Longrightarrow> erase(rl_rot(n,l,r)) = rl_rot\<^isub>0(n, erase l, erase r)"
apply (unfold bal\<^isub>0_def)
apply (cases r)
 apply simp
apply (rename_tac t1 t2 h)
apply (case_tac t1)
 apply simp
apply simp
done

lemma erase_l_rot:
"\<lbrakk> height(erase r) = Suc(Suc(height(erase l))); bal\<^isub>0(erase r) \<noteq> Left \<rbrakk>
  \<Longrightarrow> erase(l_rot(n,l,r)) = l_rot\<^isub>0(n, erase l, erase r)"
by (cases r) (simp_all add:bal\<^isub>0_def)


text{* Function @{const insrt} implements @{const insrt}: *}

lemma erase_insrt: "hinv t \<Longrightarrow> erase(insrt x t) = insrt\<^isub>0 x (erase t)"
apply(induct t)
 apply simp
apply (simp add:l_bal\<^isub>0_def l_bal_def erase_lr_rot erase_r_rot
                r_bal\<^isub>0_def r_bal_def erase_rl_rot erase_l_rot)
done

text{* Function @{const insrt} meets its spec: *}

corollary "avl t \<Longrightarrow> set_of(erase(insrt x t)) = insert x (set_of(erase t))"
by(simp add:avl_def erase_insrt set_of_insrt)

text{* Function @{const insrt} preserves the invariants: *}

corollary "avl t \<Longrightarrow> avl(insrt x t)"
by (simp add:avl_def erase_insrt is_bal_insrt)

corollary
 "avl t \<Longrightarrow> is_ord(erase t) \<Longrightarrow> is_ord(erase(insrt (x::'a::linorder) t))"
by(simp add: avl_def erase_insrt is_ord_insrt)

text{* Function @{const is_in} implements @{const is_in}: *}

theorem is_in: "is_in x t = is_in\<^isub>0 x (erase t)"
by (induct t) simp_all

text{* Function @{const is_in} meets its spec: *}

corollary "is_ord(erase t) \<Longrightarrow> is_in x t = (x : set_of(erase t))"
by(simp add:is_in is_in_correct)

end
