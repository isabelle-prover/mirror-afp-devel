(*  Title:      AVL Trees
    ID:         $Id: AVL.thy,v 1.4 2004-06-22 01:46:25 lsf37 Exp $
    Author:     Cornelia Pusch and Tobias Nipkow, converted to Isar by Gerwin Klein
    Author:     contributions by Achim Brucker, Burkhart Wolff and Jan Smaus
    Maintainer: Gerwin Klein <gerwin.klein@nicta.com.au>
    Copyright:  1998 TUM

    see the file Changelog for a list of changes
*)

header "Parameterized AVL Trees"

theory AVL = Main:

text {* 
  At the moment only insertion is formalized.

  This theory would be a nice candidate for structured Isar proof
  texts and for extensions (delete operation). 
*}

text {*
  This version works exclusively with nat. Balance check could be
  simplified by working with int: 
  @{text "is_bal (MKT n l r) = (abs(int(height l) - int(height r)) <= 1 & is_bal l & is_bal r)"}
*}

datatype 'a tree = ET |  MKT 'a "'a tree" "'a tree"

consts
  height :: "'a tree \<Rightarrow> nat"
  is_in  :: "'a \<Rightarrow> 'a tree \<Rightarrow> bool" 
  is_ord :: "('a::order) tree \<Rightarrow> bool" 
  is_bal :: "'a tree \<Rightarrow> bool" 

primrec
  "height ET = 0"
  "height (MKT n l r) = 1 + max (height l) (height r)"

primrec
  "is_in k ET = False"
  "is_in k (MKT n l r) = (k=n \<or> is_in k l \<or> is_in k r)"

primrec
  "is_ord ET = True"
  "is_ord (MKT n l r) = ((\<forall>n'. is_in n' l \<longrightarrow> n' < n) \<and>
                        (\<forall>n'. is_in n' r \<longrightarrow> n < n') \<and>
                        is_ord l \<and> is_ord r)"

primrec
  "is_bal ET = True"
  "is_bal (MKT n l r) = ((height l = height r \<or>
                         height l = 1+height r \<or>
                         height r = 1+height l) \<and> 
                         is_bal l \<and> is_bal r)"
text {* 
  We also provide a more efficient variant of @{text is_in}: 
*}

consts
  is_in_eff   :: "('a::order) \<Rightarrow> 'a tree \<Rightarrow> bool"
primrec
 "is_in_eff k ET = False"
 "is_in_eff k (MKT n l r) = (if k = n then True
                                      else (if k<n then (is_in_eff k l)
                                      else (is_in_eff k r)))"

datatype bal = Just | Left | Right

constdefs
  bal :: "'a tree \<Rightarrow> bal"
  "bal t \<equiv> case t of ET \<Rightarrow> Just
                   | (MKT n l r) \<Rightarrow> if height l = height r then Just
                                    else if height l < height r then Right else Left"

consts
  r_rot  :: "'a \<times> 'a tree \<times> 'a tree \<Rightarrow> 'a tree"
  l_rot  :: "'a \<times> 'a tree \<times> 'a tree \<Rightarrow> 'a tree"
  lr_rot :: "'a \<times> 'a tree \<times> 'a tree \<Rightarrow> 'a tree"
  rl_rot :: "'a \<times> 'a tree \<times> 'a tree \<Rightarrow> 'a tree"

recdef r_rot "{}"
  "r_rot (n, MKT ln ll lr, r) = MKT ln ll (MKT n lr r)"

recdef l_rot "{}"
  "l_rot(n, l, MKT rn rl rr) = MKT rn (MKT n l rl) rr"

recdef lr_rot "{}"
  "lr_rot(n, MKT ln ll (MKT lrn lrl lrr), r) = MKT lrn (MKT ln ll lrl) (MKT n lrr r)"

recdef rl_rot "{}"
  "rl_rot(n, l, MKT rn (MKT rln rll rlr) rr) = MKT rln (MKT n l rll) (MKT rn rlr rr)"


constdefs 
  l_bal :: "'a \<Rightarrow> 'a tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree"
  "l_bal n l r \<equiv> if bal l = Right 
                  then lr_rot (n, l, r)
                  else r_rot (n, l, r)"

  r_bal :: "'a \<Rightarrow> 'a tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree"
  "r_bal n l r \<equiv> if bal r = Left
                  then rl_rot (n, l, r)
                  else l_rot (n, l, r)"

consts
  insert :: "'a::order \<Rightarrow> 'a tree \<Rightarrow> 'a tree"
primrec
"insert x ET = MKT x ET ET"
"insert x (MKT n l r) = 
   (if x=n
    then MKT n l r
    else if x<n
         then let l' = insert x l
              in if height l' = 2+height r
                 then l_bal n l' r
                 else MKT n l' r
         else let r' = insert x r
              in if height r' = 2+height l
                 then r_bal n l r'
                 else MKT n l r')"

subsection "is-bal"

declare Let_def [simp]

lemma is_bal_lr_rot: 
"\<lbrakk> height l = Suc(Suc(height r)); bal l = Right; is_bal l; is_bal r \<rbrakk>
  \<Longrightarrow> is_bal (lr_rot (n, l, r))"
apply (unfold bal_def)
apply (cases l)
 apply simp
apply (rename_tac t1 t2)
apply (case_tac t2)
 apply simp
apply (simp add: max_def split: split_if_asm)
apply arith
done


lemma is_bal_r_rot: 
"\<lbrakk> height l = Suc(Suc(height r)); bal l \<noteq> Right; is_bal l; is_bal r \<rbrakk>
  \<Longrightarrow> is_bal (r_rot (n, l, r))"
apply (unfold bal_def)
apply (cases "l")
 apply simp
apply (simp add: max_def split: split_if_asm)
done


lemma is_bal_rl_rot: 
"\<lbrakk> height r = Suc(Suc(height l)); bal r = Left; is_bal l; is_bal r \<rbrakk>
  \<Longrightarrow> is_bal (rl_rot (n, l, r))"
apply (unfold bal_def)
apply (cases r)
 apply simp
apply (rename_tac t1 t2)
apply (case_tac t1)
 apply (simp add: max_def split: split_if_asm)
apply (simp add: max_def split: split_if_asm)
apply arith
done


lemma is_bal_l_rot: 
"\<lbrakk> height r = Suc(Suc(height l)); bal r \<noteq> Left; is_bal l; is_bal r \<rbrakk>
  \<Longrightarrow> is_bal (l_rot (n, l, r))"
apply (unfold bal_def)
apply (cases r)
 apply simp 
apply (simp add: max_def split: split_if_asm)
done


text {* Lemmas about height after rotation *}

lemma height_lr_rot:
"\<lbrakk> bal l = Right; height l = Suc(Suc(height r)) \<rbrakk>
 \<Longrightarrow> Suc(height (lr_rot (n, l, r))) = height (MKT n l r) "
apply (unfold bal_def)
apply (cases l)
 apply simp
apply (rename_tac t1 t2)
apply (case_tac t2)
 apply simp
apply (simp add: max_def split: split_if_asm)
done


lemma height_r_rot: 
"\<lbrakk> height l = Suc(Suc(height r)); bal l \<noteq> Right \<rbrakk>
  \<Longrightarrow> Suc(height (r_rot (n, l, r))) = height (MKT n l r) \<or>
          height (r_rot (n, l, r)) = height (MKT n l r)"
apply (unfold bal_def)
apply (cases l)
 apply simp 
apply (simp add: max_def split: split_if_asm)
done


lemma height_l_bal:
"height l = Suc(Suc(height r))   
  \<Longrightarrow> Suc(height (l_bal n l r)) = height (MKT n l r) |  
          height (l_bal n l r)  = height (MKT n l r)"
apply (unfold l_bal_def)
apply (cases "bal l = Right")
 apply (fastsimp dest: height_lr_rot)
apply (fastsimp dest: height_r_rot)
done


lemma height_rl_rot [rule_format (no_asm)]: 
"height r = Suc(Suc(height l)) \<longrightarrow> bal r = Left  
  \<longrightarrow> Suc(height (rl_rot (n, l, r)))  = height (MKT n l r)"
apply (unfold bal_def)
apply (cases r)
 apply simp
apply (rename_tac t1 t2)
apply (case_tac t1)
 apply simp
apply (simp add: max_def split: split_if_asm)
done


lemma height_l_rot [rule_format (no_asm)]: 
"height r = Suc(Suc(height l)) \<longrightarrow> bal r \<noteq> Left  
 \<longrightarrow> Suc(height (l_rot (n, l, r))) = height (MKT n l r) \<or>  
          height (l_rot (n, l, r)) = height (MKT n l r)"
apply (unfold bal_def)
apply (cases r)
 apply simp
apply (simp add: max_def)
done


lemma height_r_bal: 
"height r = Suc(Suc(height l))   
  \<Longrightarrow> Suc(height (r_bal n l r)) = height (MKT n l r) \<or>  
          height (r_bal n l r) = height (MKT n l r)"
apply (unfold r_bal_def)
apply (cases "bal r = Left")
 apply (fastsimp dest: height_rl_rot)
apply (fastsimp dest: height_l_rot)
done

lemma height_insert [rule_format (no_asm)]: 
"is_bal t
  \<longrightarrow> height (insert x t) = height t \<or> height (insert x t) = Suc(height t)"
apply (induct_tac "t")
 apply simp
apply (rename_tac n t1 t2)
apply (case_tac "x=n")
 apply simp
apply (case_tac "x<n")
 apply (case_tac "height (insert x t1) = Suc (Suc (height t2))")
  apply (frule_tac n = n in height_l_bal)
  apply (simp add: max_def)
  apply fastsimp
 apply (simp add: max_def)
 apply fastsimp
apply (case_tac "height (insert x t2) = Suc (Suc (height t1))")
 apply (frule_tac n = n in height_r_bal)
 apply (fastsimp simp add: max_def)
apply (simp add: max_def)
apply fastsimp
done


lemma is_bal_insert_left: 
"\<lbrakk>height (insert x l) \<noteq> Suc(Suc(height r)); is_bal (insert x l); is_bal (MKT n l r)\<rbrakk>  
  \<Longrightarrow> is_bal (MKT n (insert x l) r)"
apply (cut_tac x = "x" and t = "l" in height_insert)
 apply simp
apply fastsimp
done


lemma is_bal_insert_right: 
"\<lbrakk> height (insert x r) \<noteq> Suc(Suc(height l)); is_bal (insert x r); is_bal (MKT n l r) \<rbrakk>
  \<Longrightarrow> is_bal (MKT n l (insert x r))"
apply (cut_tac x = "x" and t = "r" in height_insert)
 apply simp
apply fastsimp
done


lemma is_bal_insert [rule_format (no_asm)]: 
"is_bal t \<longrightarrow> is_bal(insert x t)"
apply (induct_tac "t")
 apply simp
apply (rename_tac n t1 t2)
apply (case_tac "x=n")
 apply simp
apply (case_tac "x<n")
 apply (case_tac "height (insert x t1) = Suc (Suc (height t2))")
  apply (case_tac "bal (insert x t1) = Right")
   apply (fastsimp intro: is_bal_lr_rot simp add: l_bal_def)
  apply (fastsimp intro: is_bal_r_rot simp add: l_bal_def)
 apply clarify
 apply (frule is_bal_insert_left)
   apply simp
  apply assumption
 apply simp
apply (case_tac "height (insert x t2) = Suc (Suc (height t1))")
 apply (case_tac "bal (insert x t2) = Left")
  apply (fastsimp intro: is_bal_rl_rot simp add: r_bal_def)
 apply (fastsimp intro: is_bal_l_rot simp add: r_bal_def)
apply clarify
apply (frule is_bal_insert_right)
   apply simp
  apply assumption
 apply simp
done


subsection "is-in"

lemma is_in_lr_rot: 
"\<lbrakk> height l = Suc(Suc(height r)); bal l = Right \<rbrakk>
  \<Longrightarrow> is_in x (lr_rot (n, l, r)) = is_in x (MKT n l r)"
apply (unfold bal_def)
apply (cases l)
 apply simp
apply (rename_tac t1 t2)
apply (case_tac t2)
 apply simp 
apply fastsimp
done


lemma is_in_r_rot: 
"\<lbrakk> height l = Suc(Suc(height r)); bal l \<noteq> Right \<rbrakk>
  \<Longrightarrow> is_in x (r_rot (n, l, r)) = is_in x (MKT n l r)"
apply (unfold bal_def)
apply (cases l)
 apply simp
apply fastsimp
done


lemma is_in_rl_rot:
"\<lbrakk> height r = Suc(Suc(height l)); bal r = Left \<rbrakk>
  \<Longrightarrow> is_in x (rl_rot (n, l, r)) = is_in x (MKT n l r)"
apply (unfold bal_def)
apply (cases r)
 apply simp
apply (rename_tac t1 t2)
apply (case_tac t1)
 apply (simp add: max_def le_def)
apply fastsimp
done


lemma is_in_l_rot:
"\<lbrakk> height r = Suc(Suc(height l)); bal r \<noteq> Left \<rbrakk>
  \<Longrightarrow> is_in x (l_rot (n, l, r)) = is_in x (MKT n l r)"
apply (unfold bal_def)
apply (cases r)
 apply simp
apply fastsimp
done


lemma is_in_insert: 
"is_in y (insert x t) = (y=x \<or> is_in y t)"
apply (induct t)
 apply simp
apply (simp add: l_bal_def is_in_lr_rot is_in_r_rot r_bal_def 
                 is_in_rl_rot is_in_l_rot)
apply blast
done

lemma is_in_ord_l [rule_format (no_asm)]: 
"is_ord (MKT n l r) \<longrightarrow> x < n \<longrightarrow> is_in x (MKT n l r) \<longrightarrow> is_in x l"
apply(auto)
done

lemma is_in_ord_r [rule_format (no_asm)]: 
"is_ord (MKT n l r) \<longrightarrow> n < x \<longrightarrow> is_in x (MKT n l r) \<longrightarrow> is_in x r"
apply (auto)
done

subsection "is-in-eff"

lemma is_in_eff_correct [rule_format (no_asm)]: "is_ord t \<longrightarrow> (is_in k t = is_in_eff k t)"
apply (induct_tac "t")
apply (simp (no_asm))
apply (case_tac "k = a")
apply (auto);
done

subsection "is-ord"

lemma is_ord_lr_rot [rule_format (no_asm)]: 
"\<lbrakk> height l = Suc(Suc(height r)); bal l = Right; is_ord (MKT n l r) \<rbrakk>
  \<Longrightarrow> is_ord (lr_rot (n, l, r))"
apply (unfold bal_def)
apply (cases l)
 apply simp
apply (rename_tac t1 t2)
apply (case_tac t2)
 apply simp
apply simp
apply (blast intro: order_less_trans)
done


lemma is_ord_r_rot:
"\<lbrakk> height l = Suc(Suc(height r)); bal l \<noteq> Right; is_ord (MKT n l r) \<rbrakk>
  \<Longrightarrow> is_ord (r_rot (n, l, r))"
apply (unfold bal_def)
apply (cases l)
apply (simp (no_asm_simp))
apply (auto intro: order_less_trans)
done


lemma is_ord_rl_rot: 
"\<lbrakk> height r = Suc(Suc(height l)); bal r = Left; is_ord (MKT n l r) \<rbrakk>
  \<Longrightarrow> is_ord (rl_rot (n, l, r))"
apply (unfold bal_def)
apply (cases r)
 apply simp
apply (rename_tac t1 t2)
apply (case_tac t1)
 apply (simp add: le_def)
apply simp
apply (blast intro: order_less_trans)
done


lemma is_ord_l_rot: 
"\<lbrakk> height r = Suc(Suc(height l)); bal r \<noteq> Left; is_ord (MKT n l r) \<rbrakk>
  \<Longrightarrow> is_ord (l_rot (n, l, r))"
apply (unfold bal_def)
apply (cases r)
 apply simp
apply simp
apply (blast intro: order_less_trans)
done

(* insert operation presreves is_ord property *)

lemma is_ord_insert: 
"is_ord t \<Longrightarrow> is_ord(insert (x::'a::linorder) t)"
apply (induct t)
 apply simp
apply (cut_tac x = "x" and y = "a" in linorder_less_linear)
apply (fastsimp simp add: l_bal_def is_ord_lr_rot is_ord_r_rot r_bal_def 
                           is_ord_l_rot is_ord_rl_rot is_in_insert)
done


subsection "An extended tree datatype with labels for the balancing information"

datatype 'a etree = EET |  EMKT bal 'a "'a etree" "'a etree"


text {*
Pruning, i.e. throwing away the balancing labels:
*}
consts
  prune :: "'a etree \<Rightarrow> 'a tree"
primrec
  "prune EET = ET" 
  "prune (EMKT b n l r) =
		         MKT n (prune l) (prune r)"

text {*
Test if the balancing arguments are correct:
*}
consts
  correct :: "'a etree \<Rightarrow> bool"
primrec
  "correct EET = True"
  "correct (EMKT b n l r) =
	         (b = bal (MKT n (prune l) (prune r))\<and> correct l\<and> correct r)" 

text {*
  Add correct balancing labels:
*}
consts
 label :: "'a tree \<Rightarrow> 'a etree"
primrec
 "label ET = EET"
 "label (MKT n l r) =
	                 EMKT (bal (MKT n l r)) n (label l)
	                                              (label r)"

lemma correct_prune: "correct (EMKT b n l r) \<longrightarrow> (bal (prune (EMKT b n l r)) = b)"
apply (simp (no_asm_simp) add: bal_def)
done

subsection "Reversing of prune and label"

lemma prune_label: "prune (label t) = t"
apply (induct_tac "t")
apply (simp (no_asm))
apply (simp (no_asm))
apply (erule_tac conjI)
apply assumption 
done

lemma label_prune: "correct t \<Longrightarrow> label (prune t) = t"
apply (induct t)
apply auto
done

end
