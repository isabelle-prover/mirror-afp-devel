(*  Title:       Lazy_LList.thy
    Author:      Andreas Lochbihler
*)
header {* Explicit laziness in the code generator *}

theory Lazy_LList imports 
  Coinductive_List_Lib
begin

code_modulename SML
  Lazy_LList Coinductive_List

code_modulename OCaml
  Lazy_LList Coinductive_List

code_modulename Haskell
  Lazy_LList Coinductive_List

code_modulename Scala
  Lazy_LList Coinductive_List

definition Lazy_llist :: "(unit \<Rightarrow> ('a \<times> 'a llist) option) \<Rightarrow> 'a llist"
where [simp]:
  "Lazy_llist xs = (case xs () of None \<Rightarrow> LNil | Some (x, ys) \<Rightarrow> LCons x ys)"

definition force :: "'a llist \<Rightarrow> ('a \<times> 'a llist) option"
where [simp, code del]: "force xs = (case xs of LNil \<Rightarrow> None | LCons x ys \<Rightarrow> Some (x, ys))"

code_datatype Lazy_llist

declare option.splits [split] 

lemma Lazy_llist_inject [simp]:
  "Lazy_llist xs = Lazy_llist ys \<longleftrightarrow> xs = ys"
by(auto simp add: fun_eq_iff)

lemma Lazy_llist_inverse [code, simp]:
  "force (Lazy_llist xs) = xs ()"
by(auto)

lemma force_inverse [simp]:
  "Lazy_llist (\<lambda>_. force xs) = xs"
by(auto split: llist_split)

lemma LNil_Lazy_llist [code]: "LNil = Lazy_llist (\<lambda>_. None)"
by(simp)

lemma LCons_Lazy_llist [code]: "LCons x xs = Lazy_llist (\<lambda>_. Some (x, xs))"
by simp

lemma llist_corec_Lazy_llist [code]:
  "llist_corec a f = Lazy_llist (\<lambda>_. case f a of None \<Rightarrow> None | Some (x, a') \<Rightarrow> Some (x, llist_corec a' f))"
by(subst llist_corec) simp

declare llist_case_LNil [code del] llist_case_LCons [code del]

lemma llist_case_Lazy_llist [code]:
  "llist_case n c (Lazy_llist xs) = (case xs () of None \<Rightarrow> n | Some (x, ys) \<Rightarrow> c x ys)"
by simp

declare lappend_LNil1 [code del] lappend_LCons [code del]

lemma lappend_Lazy_llist [code]:
  "lappend (Lazy_llist xs) ys = 
  Lazy_llist (\<lambda>_. case xs () of None \<Rightarrow> force ys | Some (x, xs') \<Rightarrow> Some (x, lappend xs' ys))"
by(auto split: llist_splits)

declare lmap_LNil [code del] lmap_LCons [code del]

lemma lmap_Lazy_llist [code]:
  "lmap f (Lazy_llist xs) = Lazy_llist (\<lambda>_. Option.map (map_pair f (lmap f)) (xs ()))"
by simp

declare lfinite_code [code del]

lemma lfinite_Lazy_llist [code]:
  "lfinite (Lazy_llist xs) = (case xs () of None \<Rightarrow> True | Some (x, ys) \<Rightarrow> lfinite ys)"
by simp

declare llength_LNil [code del] llength_LCons [code del]

lemma llength_Lazy_llist [code]:
  "llength (Lazy_llist xs) = (case xs () of None \<Rightarrow> 0 | Some (_, ys) \<Rightarrow> eSuc (llength ys))"
by simp

declare ltake_LNil [code del] ltake_LCons [code del]

lemma ltake_Lazy_llist [code]:
  "ltake n (Lazy_llist xs) =
  Lazy_llist (\<lambda>_. if n = 0 then None else case xs () of None \<Rightarrow> None | Some (x, ys) \<Rightarrow> Some (x, ltake (n - 1) ys))"
by(cases n rule: enat_coexhaust) auto

declare ldropn.simps [code del]

lemma ldropn_Lazy_llist [code]:
  "ldropn n (Lazy_llist xs) = 
   Lazy_llist (\<lambda>_. if n = 0 then xs () else
                   case xs () of None \<Rightarrow> None | Some (x, ys) \<Rightarrow> force (ldropn (n - 1) ys))"
by(cases n)(auto split: llist_split)

declare ltakeWhile_simps [code del]

lemma ltakeWhile_Lazy_llist [code]:
  "ltakeWhile P (Lazy_llist xs) = 
  Lazy_llist (\<lambda>_. case xs () of None \<Rightarrow> None | Some (x, ys) \<Rightarrow> if P x then Some (x, ltakeWhile P ys) else None)"
by auto

declare ldropWhile_simps [code del]

lemma ldropWhile_Lazy_llist [code]:
  "ldropWhile P (Lazy_llist xs) = 
   Lazy_llist (\<lambda>_. case xs () of None \<Rightarrow> None | Some (x, ys) \<Rightarrow> if P x then force (ldropWhile P ys) else Some (x, ys))"
by(auto split: llist_split)

declare lzip_simps [code del]

lemma lzip_Lazy_llist [code]:
  "lzip (Lazy_llist xs) (Lazy_llist ys) =
  Lazy_llist (\<lambda>_. Option.bind (xs ()) (\<lambda>(x, xs'). Option.map (\<lambda>(y, ys'). ((x, y), lzip xs' ys')) (ys ())))"
by auto

declare lset_code [code del]

lemma lset_Lazy_llist [code]:
  "lset (Lazy_llist xs) x =
  (case xs () of None \<Rightarrow> False | Some (y, ys) \<Rightarrow> x = y \<or> lset ys x)"
by(auto simp add: insert_code)

declare llist_all2_code [code del]

lemma llist_all2_Lazy_llist [code]:
  "llist_all2 P (Lazy_llist xs) (Lazy_llist ys) =
  (case xs () of None \<Rightarrow> ys () = None 
      | Some (x, xs') \<Rightarrow> case ys () of None \<Rightarrow> False 
                           | Some (y, ys') \<Rightarrow> P x y \<and> llist_all2 P xs' ys')"
by auto

declare lhd_LCons [code del]

lemma lhd_Lazy_llist [code]:
  "lhd (Lazy_llist xs) = (case xs () of None \<Rightarrow> undefined | Some (x, xs') \<Rightarrow> x)"
by(simp add: lhd_def)

declare ltl_simps [code del]

lemma ltl_Lazy_llist [code]:
  "ltl (Lazy_llist xs) = Lazy_llist (\<lambda>_. case xs () of None \<Rightarrow> None | Some (x, ys) \<Rightarrow> force ys)"
by(auto split: llist_split)

declare llast_def [code del]

lemma llast_Lazy_llist [code]:
  "llast (Lazy_llist xs) =
  (case xs () of 
    None \<Rightarrow> undefined 
  | Some (x, xs') \<Rightarrow> 
    case force xs' of None \<Rightarrow> x | Some (x', xs'') \<Rightarrow> llast (LCons x' xs''))"
by(auto simp add: llast_def zero_enat_def eSuc_def split: enat.split llist_splits)

declare ldistinct_LNil_code [code del] ldistinct_LCons [code del]

lemma ldistinct_Lazy_llist [code]:
  "ldistinct (Lazy_llist xs) =
  (case xs () of None \<Rightarrow> True | Some (x, ys) \<Rightarrow> x \<notin> lset ys \<and> ldistinct ys)"
by(auto)

declare lprefix_code [code del]

lemma lprefix_Lazy_llist [code]:
  "lprefix (Lazy_llist xs) (Lazy_llist ys) =
  (case xs () of 
    None \<Rightarrow> True
  | Some (x, xs') \<Rightarrow> 
    case ys () of None \<Rightarrow> False | Some (y, ys') \<Rightarrow> x = y \<and> lprefix xs' ys')"
by auto

declare lstrict_prefix_code [code del]

lemma lstrict_prefix_Lazy_llist [code]:
  "lstrict_prefix (Lazy_llist xs) (Lazy_llist ys) \<longleftrightarrow>
  (case ys () of
    None \<Rightarrow> False 
  | Some (y, ys') \<Rightarrow> 
    case xs () of None \<Rightarrow> True | Some (x, xs') \<Rightarrow> x = y \<and> lstrict_prefix xs' ys')"
by auto

declare llexord_code [code del]

lemma llexord_Lazy_llist [code]:
  "llexord r (Lazy_llist xs) (Lazy_llist ys) \<longleftrightarrow>
  (case xs () of 
    None \<Rightarrow> True 
  | Some (x, xs') \<Rightarrow> 
    case ys () of None \<Rightarrow> False | Some (y, ys') \<Rightarrow> r x y \<or> x = y \<and> llexord r xs' ys')"
by auto
  
declare lfilter_code [code del]

lemma lfilter_Lazy_llist [code]:
  "lfilter P (Lazy_llist xs) =
  Lazy_llist (\<lambda>_. case xs () of None \<Rightarrow> None 
                  | Some (x, ys) \<Rightarrow> if P x then Some (x, lfilter P ys) else force (lfilter P ys))"
by(auto split: llist_split)

declare lconcat_LNil [code del] lconcat_LCons [code del]

lemma lconcat_Lazy_llist [code]:
  "lconcat (Lazy_llist xss) =
  Lazy_llist (\<lambda>_. case xss () of None \<Rightarrow> None | Some (xs, xss') \<Rightarrow> force (lappend xs (lconcat xss')))"
by(auto split: llist_split)

declare option.splits [split del]
declare Lazy_llist_def [simp del]

text {* Simple ML test for laziness *}

ML {*
  val zeros = @{code iterates} (fn x => x) 0;
  val lhd = @{code lhd} zeros;
  val ltl = @{code ltl} zeros;
  
  val ltake = @{code ltake} (@{code eSuc} @{code "0::enat"}) zeros;
  val ldrop = @{code ldrop} (@{code eSuc} @{code "0::enat"}) zeros;
  
  val ltakeWhile = @{code ltakeWhile} (fn _ => true) zeros;
  val ldropWhile = @{code ldropWhile} (fn _ => false) zeros;
  val hd = @{code lhd} ldropWhile;
  
  val lfilter = @{code lfilter} (fn _ => false) zeros;
  val ldropWhile = @{code force} ltl;
*}

hide_const (open) force

end