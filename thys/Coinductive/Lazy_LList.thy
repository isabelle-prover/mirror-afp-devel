(*  Title:       Lazy_LList.thy
    Author:      Andreas Lochbihler
*)
header {* Explicit laziness in the code generator *}

theory Lazy_LList imports 
  Coinductive_List
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
by(auto split: llist.split)

lemma LNil_Lazy_llist [code]: "LNil = Lazy_llist (\<lambda>_. None)"
by(simp)

lemma LCons_Lazy_llist [code, code_unfold]: "LCons x xs = Lazy_llist (\<lambda>_. Some (x, xs))"
by simp

lemma lnull_lazy [code]: "lnull = Option.is_none \<circ> force"
by(simp add: lnull_def Option.is_none_def fun_eq_iff split: llist.split)

lemma [code, code del]:
  "equal_class.equal = (equal_class.equal :: 'a :: equal llist \<Rightarrow> _)" ..

lemma equal_llist_Lazy_llist [code]:
  "equal_class.equal (Lazy_llist xs) (Lazy_llist ys) \<longleftrightarrow>
   (case xs () of None \<Rightarrow> (case ys () of None \<Rightarrow> True | _ \<Rightarrow> False)
    | Some (x, xs') \<Rightarrow> 
       (case ys () of None \<Rightarrow> False 
        | Some (y, ys') \<Rightarrow> if x = y then equal_class.equal xs' ys' else False))"
by(auto simp add: equal_llist_def)

lemma [code, code del]: "llist_corec = llist_corec" ..

lemma llist_corec_Lazy_llist [code]:
  "llist_corec IS_LNIL LHD endORmore LTL_end LTL_more b =
  Lazy_llist (\<lambda>_. if IS_LNIL b then None 
     else Some (LHD b,
       if endORmore b then LTL_end b
       else llist_corec IS_LNIL LHD endORmore LTL_end LTL_more (LTL_more b)))"
by(subst llist_corec_code) simp

lemma [code, code del]: "llist_unfold = llist_unfold" ..

lemma llist_unfold_Lazy_llist [code]:
  "llist_unfold IS_LNIL LHD LTL b =
  Lazy_llist (\<lambda>_. if IS_LNIL b then None else Some (LHD b, llist_unfold IS_LNIL LHD LTL (LTL b)))"
by(subst llist_unfold_code) simp

lemma [code, code del]: "llist_case = llist_case" ..

lemma llist_case_Lazy_llist [code]:
  "llist_case n c (Lazy_llist xs) = (case xs () of None \<Rightarrow> n | Some (x, ys) \<Rightarrow> c x ys)"
by simp

lemma [code, code del]: "lappend = lappend" ..

lemma lappend_Lazy_llist [code]:
  "lappend (Lazy_llist xs) ys = 
  Lazy_llist (\<lambda>_. case xs () of None \<Rightarrow> force ys | Some (x, xs') \<Rightarrow> Some (x, lappend xs' ys))"
by(auto split: llist.splits)

lemma [code, code del]: "lmap = lmap" ..

lemma lmap_Lazy_llist [code]:
  "lmap f (Lazy_llist xs) = Lazy_llist (\<lambda>_. Option.map (map_pair f (lmap f)) (xs ()))"
by simp

lemma [code, code del]: "lfinite = lfinite" ..

lemma lfinite_Lazy_llist [code]:
  "lfinite (Lazy_llist xs) = (case xs () of None \<Rightarrow> True | Some (x, ys) \<Rightarrow> lfinite ys)"
by simp

lemma [code, code del]: "list_of_aux = list_of_aux" ..

lemma list_of_aux_Lazy_llist [code]:
  "list_of_aux xs (Lazy_llist ys) = 
  (case ys () of None \<Rightarrow> rev xs | Some (y, ys) \<Rightarrow> list_of_aux (y # xs) ys)"
by(simp add: list_of_aux_code)

lemma [code, code del]: "gen_llength = gen_llength" ..

lemma gen_llength_Lazy_llist [code]:
  "gen_llength n (Lazy_llist xs) = (case xs () of None \<Rightarrow> enat n | Some (_, ys) \<Rightarrow> gen_llength (n + 1) ys)"
by(simp add: gen_llength_code)

lemma [code, code del]: "ltake = ltake" ..

lemma ltake_Lazy_llist [code]:
  "ltake n (Lazy_llist xs) =
  Lazy_llist (\<lambda>_. if n = 0 then None else case xs () of None \<Rightarrow> None | Some (x, ys) \<Rightarrow> Some (x, ltake (n - 1) ys))"
by(cases n rule: enat_coexhaust) auto

lemma [code, code del]: "ldropn = ldropn" ..

lemma ldropn_Lazy_llist [code]:
  "ldropn n (Lazy_llist xs) = 
   Lazy_llist (\<lambda>_. if n = 0 then xs () else
                   case xs () of None \<Rightarrow> None | Some (x, ys) \<Rightarrow> force (ldropn (n - 1) ys))"
by(cases n)(auto simp add: eSuc_enat[symmetric] split: llist.split)

lemma [code, code del]: "ltakeWhile = ltakeWhile" ..

lemma ltakeWhile_Lazy_llist [code]:
  "ltakeWhile P (Lazy_llist xs) = 
  Lazy_llist (\<lambda>_. case xs () of None \<Rightarrow> None | Some (x, ys) \<Rightarrow> if P x then Some (x, ltakeWhile P ys) else None)"
by auto

lemma [code, code del]: "ldropWhile = ldropWhile" ..

lemma ldropWhile_Lazy_llist [code]:
  "ldropWhile P (Lazy_llist xs) = 
   Lazy_llist (\<lambda>_. case xs () of None \<Rightarrow> None | Some (x, ys) \<Rightarrow> if P x then force (ldropWhile P ys) else Some (x, ys))"
by(auto split: llist.split)

lemma [code, code del]: "lzip = lzip" ..

lemma lzip_Lazy_llist [code]:
  "lzip (Lazy_llist xs) (Lazy_llist ys) =
  Lazy_llist (\<lambda>_. Option.bind (xs ()) (\<lambda>(x, xs'). Option.map (\<lambda>(y, ys'). ((x, y), lzip xs' ys')) (ys ())))"
by auto

lemma [code, code del]: "gen_lset = gen_lset" ..

lemma lset_Lazy_llist [code]:
  "gen_lset A (Lazy_llist xs) =
  (case xs () of None \<Rightarrow> A | Some (y, ys) \<Rightarrow> gen_lset (insert y A) ys)"
by(auto simp add: gen_lset_code)

lemma [code, code del]: "lmember = lmember" ..

lemma lmember_Lazy_llist [code]: 
  "lmember x (Lazy_llist xs) =
  (case xs () of None \<Rightarrow> False | Some (y, ys) \<Rightarrow> x = y \<or> lmember x ys)"
by(simp add: lmember_def)

lemma [code, code del]: "llist_all2 = llist_all2" ..

lemma llist_all2_Lazy_llist [code]:
  "llist_all2 P (Lazy_llist xs) (Lazy_llist ys) =
  (case xs () of None \<Rightarrow> ys () = None 
      | Some (x, xs') \<Rightarrow> case ys () of None \<Rightarrow> False 
                           | Some (y, ys') \<Rightarrow> P x y \<and> llist_all2 P xs' ys')"
by auto

lemma [code, code del]: "lhd = lhd" ..

lemma lhd_Lazy_llist [code]:
  "lhd (Lazy_llist xs) = (case xs () of None \<Rightarrow> undefined | Some (x, xs') \<Rightarrow> x)"
by(simp add: lhd_def)

lemma [code, code del]: "ltl = ltl" ..

lemma ltl_Lazy_llist [code]:
  "ltl (Lazy_llist xs) = Lazy_llist (\<lambda>_. case xs () of None \<Rightarrow> None | Some (x, ys) \<Rightarrow> force ys)"
by(auto split: llist.split)

lemma [code, code del]: "llast = llast" ..

lemma llast_Lazy_llist [code]:
  "llast (Lazy_llist xs) =
  (case xs () of 
    None \<Rightarrow> undefined 
  | Some (x, xs') \<Rightarrow> 
    case force xs' of None \<Rightarrow> x | Some (x', xs'') \<Rightarrow> llast (LCons x' xs''))"
by(auto simp add: llast_def zero_enat_def eSuc_def split: enat.split llist.splits)

lemma [code, code del]: "ldistinct = ldistinct" ..

lemma ldistinct_Lazy_llist [code]:
  "ldistinct (Lazy_llist xs) =
  (case xs () of None \<Rightarrow> True | Some (x, ys) \<Rightarrow> x \<notin> lset ys \<and> ldistinct ys)"
by(auto)

lemma [code, code del]: "lprefix = lprefix" ..

lemma lprefix_Lazy_llist [code]:
  "lprefix (Lazy_llist xs) (Lazy_llist ys) =
  (case xs () of 
    None \<Rightarrow> True
  | Some (x, xs') \<Rightarrow> 
    case ys () of None \<Rightarrow> False | Some (y, ys') \<Rightarrow> x = y \<and> lprefix xs' ys')"
by auto

lemma [code, code del]: "lstrict_prefix = lstrict_prefix" ..

lemma lstrict_prefix_Lazy_llist [code]:
  "lstrict_prefix (Lazy_llist xs) (Lazy_llist ys) \<longleftrightarrow>
  (case ys () of
    None \<Rightarrow> False 
  | Some (y, ys') \<Rightarrow> 
    case xs () of None \<Rightarrow> True | Some (x, xs') \<Rightarrow> x = y \<and> lstrict_prefix xs' ys')"
by auto

lemma [code, code del]: "llcp = llcp" ..

lemma llcp_Lazy_llist [code]:
  "llcp (Lazy_llist xs) (Lazy_llist ys) =
  (case xs () of None \<Rightarrow> 0 
   | Some (x, xs') \<Rightarrow> case ys () of None \<Rightarrow> 0
                     | Some (y, ys') \<Rightarrow> if x = y then eSuc (llcp xs' ys') else 0)"
by auto

lemma [code, code del]: "llexord = llexord" ..

lemma llexord_Lazy_llist [code]:
  "llexord r (Lazy_llist xs) (Lazy_llist ys) \<longleftrightarrow>
  (case xs () of 
    None \<Rightarrow> True 
  | Some (x, xs') \<Rightarrow> 
    case ys () of None \<Rightarrow> False | Some (y, ys') \<Rightarrow> r x y \<or> x = y \<and> llexord r xs' ys')"
by auto

lemma [code, code del]: "lfilter = lfilter" ..  

lemma lfilter_Lazy_llist [code]:
  "lfilter P (Lazy_llist xs) =
  Lazy_llist (\<lambda>_. case xs () of None \<Rightarrow> None 
                  | Some (x, ys) \<Rightarrow> if P x then Some (x, lfilter P ys) else force (lfilter P ys))"
by(auto split: llist.split)

lemma [code, code del]: "lconcat = lconcat" ..  

lemma lconcat_Lazy_llist [code]:
  "lconcat (Lazy_llist xss) =
  Lazy_llist (\<lambda>_. case xss () of None \<Rightarrow> None | Some (xs, xss') \<Rightarrow> force (lappend xs (lconcat xss')))"
by(auto split: llist.split)

declare option.splits [split del]
declare Lazy_llist_def [simp del]

text {* Simple ML test for laziness *}

ML_val {*
  val zeros = @{code iterates} (fn x => x + 1) 0;
  val lhd = @{code lhd} zeros;
  val ltl = @{code ltl} zeros;
  val ltl' = @{code force} ltl;
  
  val ltake = @{code ltake} (@{code eSuc} (@{code eSuc} @{code "0::enat"})) zeros;
  val ldrop = @{code ldrop} (@{code eSuc} @{code "0::enat"}) zeros;
  val list_of = @{code list_of} ltake;
  
  val ltakeWhile = @{code ltakeWhile} (fn _ => true) zeros;
  val ldropWhile = @{code ldropWhile} (fn _ => false) zeros;
  val hd = @{code lhd} ldropWhile;
  
  val lfilter = @{code lfilter} (fn _ => false) zeros;
*}

hide_const (open) force

end