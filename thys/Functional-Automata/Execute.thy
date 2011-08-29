(*
  Author:    Lukas Bulwahn, TUM 2011
*)

header {* Executing Automata and membership of Regular Expressions *}

theory Execute
imports AutoRegExp "~~/src/HOL/Library/List_Cset"
begin


subsection {* Executable types and homomorphisms *}

type_synonym ('a,'s) executable_na = "'s * ('a => 's => 's Cset.set) * ('s => bool)"
type_synonym 'a executable_bitsNA = "('a, bool list) executable_na"

definition NA_Rep
where
  "NA_Rep = (%(q, d, f). (q, %a s. Cset.member (d a s), f))" 

definition NA_Abs
where
  "NA_Abs = (%(q, d, f). (q, %a s. Cset.Set (d a s), f))"

lemma [simp]:
  "NA_Rep (NA_Abs x) = x"
unfolding NA_Rep_def NA_Abs_def
apply (auto simp add: fun_eq_iff split: prod.split)
apply (metis member_set_of set_of_Set)+
done

definition DA_Abs :: "('a, 's => bool) da => ('a, 's Cset.set) da"
where
  "DA_Abs = (%(q, d, f). (Set q, %a s. Set (d a (member s)), (%s. f (member s))))"


subsection {* Lifted operations on executable types *}

definition delta' :: "('a,'s) executable_na => 'a list => 's => 's Cset.set" where
  "delta' A w p = Set (delta (NA_Rep A) w p)" 

definition atom' :: "'a => 'a executable_bitsNA"
where
  "atom' = (%a. (%(q, d, f). (q, %a s. Cset.Set (d a s), f)) (RegExp2NA.atom a))"

definition or' :: "'a executable_bitsNA => 'a executable_bitsNA => 'a executable_bitsNA"
where
  "or' = (%na1 na2. NA_Abs (RegExp2NA.or (NA_Rep na1) (NA_Rep na2)))"

definition conc' :: "'a executable_bitsNA => 'a executable_bitsNA => 'a executable_bitsNA"
where
  "conc' = (%na1 na2. NA_Abs (RegExp2NA.conc (NA_Rep na1) (NA_Rep na2)))"

definition epsilon' :: "'a executable_bitsNA"
where
  "epsilon' = NA_Abs RegExp2NA.epsilon"

definition
  plus' :: "'a executable_bitsNA => 'a executable_bitsNA"
where
  "plus' = (%na. NA_Abs (RegExp2NA.plus (NA_Rep na)))"

definition star' :: "'a executable_bitsNA => 'a executable_bitsNA"
where
  "star' = (%na. NA_Abs (RegExp2NA.star (NA_Rep na)))"

definition rexp2na' :: "'a rexp => 'a executable_bitsNA"
where
  "rexp2na' = (%r. NA_Abs (rexp2na r))"

definition accepts' :: "('a,'s) executable_na => 'a list => bool"
where
  "accepts' A w = NA.accepts (NA_Rep A) w"

definition
  na2da' :: "('a, 's) executable_na => ('a, 's Cset.set) da"
where
  "na2da' A = DA_Abs (na2da (NA_Rep A))"

subsection {* Code equations for lifted operations *}

lemma next_NA_Rep[simp]:
  "next (NA_Rep A) a p = member (next A a p)"
unfolding next_def NA_Rep_def by (auto split: prod.split)

lemma [code]:
  "delta' A []    p = Cset.insert p bot"
  "delta' A (a#w) p = Cset.bind (next A a p) (delta' A w)"
unfolding delta.simps Cset.bind_def delta'_def
apply (metis Cset.empty_simp Cset.insert_def member_set_of)
unfolding delta'_def_raw delta.simps member_set_of
unfolding SUP_def Cset.Sup_set_def by simp

lemma [code]:
  "atom' a = ([True], %b s. if s = [True] & b = a then Cset.insert [False] bot else bot, %s. s = [False])"
unfolding atom'_def RegExp2NA.atom_def by (auto simp add: fun_eq_iff)

lemma [code]:
  "or' = (%(ql, dl, fl) (qr, dr, fr).
    ([], %a. list_case (sup (Cset.map (Cons True) (dl a ql)) (Cset.map (Cons False) (dr a qr)))
              (%left s. if left then Cset.map (Cons True) (dl a s) else Cset.map (Cons False) (dr a s)),
     list_case (fl ql | fr qr) (%left s. if left then fl s else fr s)))"
unfolding or'_def RegExp2NA.or_def
apply (auto simp add: fun_eq_iff NA_Abs_def NA_Rep_def split: list.split)
unfolding member_set_of by auto

lemma [code]:
  "conc' = (%(ql, dl, fl) (qr, dr, fr).
   (True # ql,
     %a. list_case bot
          (%left s.
              if left then sup (Cset.map (Cons True) (dl a s)) (if fl s then Cset.map (Cons False) (dr a qr) else bot) else Cset.map (Cons False) (dr a s)),
     list_case False (%left s. left & fl s & fr qr | ~ left & fr s)))"
unfolding conc'_def RegExp2NA.conc_def
apply (auto simp add: fun_eq_iff NA_Abs_def NA_Rep_def split: list.split)
unfolding member_set_of by auto

lemma [code]: "epsilon' = ([], %a s. bot, %s. s = [])"
unfolding epsilon'_def RegExp2NA.epsilon_def
by (auto simp add: NA_Abs_def NA_Rep_def)

lemma [code]:
  "plus' = (%(q, d, f). (q, %a s. sup (d a s) (if f s then d a q else bot), f))"
unfolding plus'_def RegExp2NA.plus_def
apply (auto simp add: fun_eq_iff NA_Abs_def NA_Rep_def)
unfolding member_set_of by auto
 
lemma [code]:
  "star' A = or' epsilon' (plus' A)"
unfolding star'_def or'_def epsilon'_def plus'_def RegExp2NA.star_def
by auto

lemma [code]:
  "rexp2na' (Star r) == star' (rexp2na' r)"
  "rexp2na' (Plus r s) = or' (rexp2na' r) (rexp2na' s)"
  "rexp2na' (rexp.Times r s) = conc' (rexp2na' r) (rexp2na' s)"
  "rexp2na' (Atom a) = atom' a"
  "rexp2na' Zero = ([], %a s. bot, %s. False)"
  "rexp2na' One = epsilon'"
unfolding rexp2na'_def rexp2na.simps or'_def star'_def conc'_def atom'_def epsilon'_def
apply (auto simp add: fun_eq_iff split: prod.split) 
apply (auto simp add: NA_Abs_def)
done

lemma [code]:
  "accepts' A w = (Cset.exists (fin A) (delta' A w (start A)))"
unfolding NA.accepts_def accepts'_def delta'_def NA_Rep_def
by (auto split: prod.split)

lemma [code]:
  "na2da' A = (Cset.insert (start A) bot, %a Q. Cset.bind Q (next A a), Cset.exists (fin A))"
unfolding na2da'_def DA_Abs_def NA_Rep_def na2da_def Cset.bind_def
apply (auto simp add: fun_eq_iff split: prod.split)
unfolding member_set_of SUPR_def Cset.Sup_set_def by auto

lemma [code_unfold]:
  "NA.accepts (rexp2na r) w = accepts' (rexp2na' r) w"
unfolding accepts'_def rexp2na'_def by simp

lemma next_Abs:
  "next (DA_Abs A) a (Set aa) = Set (next A a aa)"
unfolding next_def DA_Abs_def
apply (cases A)
apply simp
apply (rule fun_cong)
by (simp add: mem_def)

lemma start_Abs:
  "start (DA_Abs A) = Set (start A)"
unfolding DA_Abs_def by (cases A) simp

lemma fin_Abs:
  "fin (DA_Abs A) = (%s. (fin A) (member s))"
unfolding DA_Abs_def by (cases A) simp

lemma delta_Abs:
  "member (DA.delta (DA_Abs A) w (Set a)) = DA.delta A w a"
unfolding DA.delta_def
by (induct w arbitrary: a) (auto simp add: next_Abs mem_def)

lemma [simp]:
  "DA.accepts (DA_Abs A) w = DA.accepts A w"
unfolding DA.accepts_def
by (auto simp add: delta_Abs start_Abs fin_Abs)

lemma [code_unfold]:
  "DA.accepts (na2da (rexp2na r)) w = DA.accepts (na2da' (rexp2na' r)) w"
unfolding na2da'_def rexp2na'_def by simp


subsection {* Example *}

definition example_expression
where
  "example_expression = (let r0 = Atom (0::nat); r1 = Atom (1::nat)
     in Times (Star (Plus (Times r1 r1) r0)) (Star (Plus (Times r0 r0) r1)))"


value [code] "NA.accepts (rexp2na example_expression) [0,1,1,0,0,1]"
value [code] "DA.accepts (na2da (rexp2na example_expression)) [0,1,1,0,0,1]"


end
