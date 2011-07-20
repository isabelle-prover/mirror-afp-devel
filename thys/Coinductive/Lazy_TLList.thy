(*  Title:       Lazy_TLList.thy
    Author:      Andreas Lochbihler
*)

theory Lazy_TLList imports 
  TLList
  Lazy_LList
begin

code_modulename SML
  Lazy_TLList TLList

code_modulename OCaml
  Lazy_TLList TLList

code_modulename Haskell
  Lazy_TLList TLList

code_modulename Scala
  Lazy_TLList TLList

definition Lazy_tllist :: "(unit \<Rightarrow> 'a \<times> ('a, 'b) tllist + 'b) \<Rightarrow> ('a, 'b) tllist"
where [code del]:
  "Lazy_tllist xs = (case xs () of Inl (x, ys) \<Rightarrow> TCons x ys | Inr b \<Rightarrow> TNil b)"

definition force :: "('a, 'b) tllist \<Rightarrow> 'a \<times> ('a, 'b) tllist + 'b"
where [simp, code del]: "force xs = (case xs of TNil b \<Rightarrow> Inr b | TCons x ys \<Rightarrow> Inl (x, ys))"

code_datatype Lazy_tllist

declare Lazy_tllist_def [simp]
declare sum.splits [split]

lemma TNil_Lazy_tllist [code]: 
  "TNil b = Lazy_tllist (\<lambda>_. Inr b)"
by simp

lemma TCons_Lazy_tllist [code]:
  "TCons x xs = Lazy_tllist (\<lambda>_. Inl (x, xs))"
by simp

lemma Lazy_tllist_inverse [simp, code]:
  "force (Lazy_tllist xs) = xs ()"
by(simp)

declare tllist_corec [code del]

lemma tllist_corec_Lazy_tllist [code]:
  "tllist_corec a f = Lazy_tllist (\<lambda>_. case f a of Inl (x, a') \<Rightarrow> Inl (x, tllist_corec a' f) | Inr r \<Rightarrow> Inr r)"
by(subst tllist_corec)simp

declare tllist_case_simps [code del]

lemma tllist_case_Lazy_tllist [code]:
  "tllist_case n c (Lazy_tllist xs) = 
  (case xs () of Inl (x, ys) \<Rightarrow> c x ys | Inr b \<Rightarrow> n b)"
by simp

declare tllist_of_llist_simps[code del]

lemma tllist_of_llist_Lazy_llist [code]:
  "tllist_of_llist b (Lazy_llist xs) =
  Lazy_tllist (\<lambda>_. case xs () of None \<Rightarrow> Inr b | Some (x, ys) \<Rightarrow> Inl (x, tllist_of_llist b ys))"
by(simp add: Lazy_llist_def split: option.splits)

declare terminal_TNil [code del] terminal_TCons [code del]

lemma terminal_Lazy_tllist [code]:
  "terminal (Lazy_tllist xs) = 
  (case xs () of Inl (_, ys) \<Rightarrow> terminal ys | Inr b \<Rightarrow> b)"
by simp

declare tmap_TNil [code del] tmap_TCons [code del]

lemma tmap_Lazy_tllist [code]:
  "tmap f g (Lazy_tllist xs) =
  Lazy_tllist (\<lambda>_. case xs () of Inl (x, ys) \<Rightarrow> Inl (f x, tmap f g ys) | Inr b \<Rightarrow> Inr (g b))"
by simp

declare tappend_TNil [code del] tappend_TCons [code del]

lemma tappend_Lazy_tllist [code]:
  "tappend (Lazy_tllist xs) ys =
  Lazy_tllist (\<lambda>_. case xs () of Inl (x, xs') \<Rightarrow> Inl (x, tappend xs' ys) | Inr b \<Rightarrow> force (ys b))"
by(auto split: tllist_split)

declare lappendt_LNil [code del] lappendt_LCons [code del]

lemma lappendt_Lazy_llist [code]:
  "lappendt (Lazy_llist xs) ys =
  Lazy_tllist (\<lambda>_. case xs () of None \<Rightarrow> force ys | Some (x, xs') \<Rightarrow> Inl (x, lappendt xs' ys))"
by(auto simp add: Lazy_llist_def split: option.split tllist_split)

declare tfilter'_code [code del]

lemma tfilter'_Lazy_tllist [code]:
  "TLList.tfilter' b P (Lazy_tllist xs) =
   Lazy_tllist (\<lambda>_. case xs () of Inl (x, xs') \<Rightarrow> if P x then Inl (x, TLList.tfilter' b P xs') else force (TLList.tfilter' b P xs') | Inr b' \<Rightarrow> Inr b')"
by(simp split: tllist_split)

declare tconcat'_code [code del]

lemma tconcat_Lazy_tllist [code]:
  "TLList.tconcat' b (Lazy_tllist xss) =
  Lazy_tllist (\<lambda>_. case xss () of Inr b' \<Rightarrow> Inr b' | Inl (xs, xss') \<Rightarrow> force (lappendt xs (TLList.tconcat' b xss')))"
by(simp split: tllist_split)

declare tllist_all2_code [code del]

lemma tllist_all2_Lazy_tllist [code]:
  "tllist_all2 P Q (Lazy_tllist xs) (Lazy_tllist ys) \<longleftrightarrow>
  (case xs () of 
    Inr b \<Rightarrow> (case ys () of Inr b' \<Rightarrow> Q b b' | Inl _ \<Rightarrow> False)
  | Inl (x, xs') \<Rightarrow> (case ys () of Inr _ \<Rightarrow> False | Inl (y, ys') \<Rightarrow> P x y \<and> tllist_all2 P Q xs' ys'))"
by(simp add: tllist_all2_TNil1 tllist_all2_TNil2)

declare llist_of_tllist_TNil [code del] llist_of_tllist_TCons [code del]

lemma llist_of_tllist_Lazy_tllist [code]:
  "llist_of_tllist (Lazy_tllist xs) =
  Lazy_llist (\<lambda>_. case xs () of Inl (x, ys) \<Rightarrow> Some (x, llist_of_tllist ys) | Inr b \<Rightarrow> None)"
by(simp add: Lazy_llist_def)

declare tnth_code [code del]

lemma tnth_Lazy_tllist [code]:
  "tnth (Lazy_tllist xs) n =
  (case xs () of Inr b \<Rightarrow> undefined n | Inl (x, ys) \<Rightarrow> if n = 0 then x else tnth ys (n - 1))"
by(cases n)(auto simp add: tnth_TNil)

declare tlength_TNil [code del] tlength_TCons [code del]

lemma tlength_Lazy_tllist [code]:
  "tlength (Lazy_tllist xs) =
  (case xs () of Inr b \<Rightarrow> 0 | Inl (_, xs') \<Rightarrow> iSuc (tlength xs'))"
by simp

declare tdropn_0 [code del] tdropn_TNil [code del] tdropn_Suc_TCons [code del]

lemma tdropn_Lazy_tllist [code]:
  "tdropn n (Lazy_tllist xs) =
  Lazy_tllist (\<lambda>_. if n = 0 then xs () else case xs () of Inr b \<Rightarrow> Inr b | Inl (x, xs') \<Rightarrow> force (tdropn (n - 1) xs'))"
by(cases n)(auto split: tllist_split)

declare Lazy_tllist_def [simp del]
declare sum.splits [split del]

hide_const (open) force

end