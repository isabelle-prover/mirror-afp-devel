(*  Author:    Lukas Bulwahn, TUM 2011 *)

header {* Executing Automata and membership of Regular Expressions employing the Quotient package*}

theory Execute_Quotient
imports AutoRegExp "~~/src/HOL/Library/Quotient_Product" "~~/src/HOL/Quotient_Examples/List_Cset"
begin

subsection {* Preliminaries to be moved to Quotient_List (?) *}

lemma list_case_prs [quot_preserve]:
  assumes a: "Quotient R1 abs1 rep1"
  and     b: "Quotient R2 abs2 rep2"
  shows "(rep1 ---> (abs2 ---> (map abs2) ---> rep1) ---> (map rep2) ---> abs1) list_case = list_case"
  using assms
  apply (simp add: fun_eq_iff)
  apply auto
  apply (case_tac xb)
  apply auto
  apply (auto simp add: Quotient_abs_rep[OF a] Quotient_abs_rep[OF b] o_def)
   done

lemma list_case_prs' [quot_preserve]:
  assumes a: "Quotient R1 abs1 rep1"
  shows "(rep1 ---> (id ---> id ---> rep1) ---> id ---> abs1) list_case = list_case"
by (rule list_case_prs[OF a identity_quotient, unfolded List.map.id])

lemma list_case_rsp [quot_respect]:
  assumes q1: "Quotient R1 Abs1 Rep1"
  and     q2: "Quotient R2 Abs2 Rep2"
  shows "(R1 ===> (R2 ===> list_all2 R2 ===> R1) ===> list_all2 R2 ===> R1) list_case list_case"
  using assms
  apply(auto simp add: fun_rel_def)
  apply (case_tac xb)
  apply auto
  apply (case_tac yb)
  apply auto
  done


subsection {* Executable types *}

type_synonym ('a,'s) executable_na = "'s * ('a => 's => 's Cset.set) * ('s => bool)"
type_synonym 'a executable_bitsNA = "('a, bool list) executable_na"

subsection {* Lifted operations on executable types *}

lemma [quot_respect]:
  "(set_eq ===> (op = ===> op = ===> set_eq) ===> op = ===> set_eq) list_case list_case"
  "(prod_rel op = (prod_rel (op = ===> op = ===> set_eq) op =) ===> op = ===> op = ===> set_eq) NA.delta NA.delta"
  "(prod_rel op = (prod_rel (op = ===> op = ===> set_eq) op =) ===> op =) start start"
  "(prod_rel op = (prod_rel (op = ===> op = ===> set_eq) op =) ===> op = ===> op = ===> set_eq) next next"
  "(prod_rel op = (prod_rel (op = ===> op = ===> set_eq) op =) ===> op =) fin fin"
  "(op = ===> prod_rel op = (prod_rel (op = ===> op = ===> set_eq) op =)) RegExp2NA.atom RegExp2NA.atom"
  "prod_rel op = (prod_rel (op = ===> op = ===> set_eq) op =) RegExp2NA.epsilon RegExp2NA.epsilon"
  "(prod_rel op = (prod_rel (op = ===> op = ===> set_eq) op =) ===>
    prod_rel op = (prod_rel (op = ===> op = ===> set_eq) op =) ===>
    prod_rel op = (prod_rel (op = ===> op = ===> set_eq) op =)) RegExp2NA.conc RegExp2NA.conc"
  "(prod_rel op = (prod_rel (op = ===> op = ===> set_eq) op =) ===>
    prod_rel op = (prod_rel (op = ===> op = ===> set_eq) op =)) RegExp2NA.plus RegExp2NA.plus"
  "(prod_rel op = (prod_rel (op = ===> op = ===> set_eq) op =) ===>
    prod_rel op = (prod_rel (op = ===> op = ===> set_eq) op =)) RegExp2NA.star RegExp2NA.star"
    "(prod_rel op = (prod_rel (op = ===> op = ===> set_eq) op =) ===>
      prod_rel op = (prod_rel (op = ===> op = ===> set_eq) op =) ===>
      prod_rel op = (prod_rel (op = ===> op = ===> set_eq) op =)) RegExp2NA.or RegExp2NA.or"
  "(op = ===> prod_rel op = (prod_rel (op = ===> op = ===> set_eq) op =)) rexp2na rexp2na"
  "(prod_rel op = (prod_rel (op = ===> op = ===> set_eq) op =) ===>
    prod_rel set_eq (prod_rel (op = ===> set_eq ===> set_eq) (set_eq ===> op =))) na2da na2da"
  "(prod_rel op = (prod_rel (op = ===> op = ===> set_eq) op =) ===> op =) NA.accepts NA.accepts"
  "(prod_rel set_eq (prod_rel (op = ===> set_eq ===> set_eq) (set_eq ===> op =)) ===> op =) DA.accepts DA.accepts"
by (auto simp add: fun_rel_eq prod_rel_eq)

quotient_definition "delta' :: ('b, 'a) executable_na => 'b list => 'a => 'a Cset.set"
is delta

quotient_definition "atom' :: 'a => 'a executable_bitsNA"
is RegExp2NA.atom

quotient_definition "or' :: 'a executable_bitsNA => 'a executable_bitsNA => 'a executable_bitsNA"
is RegExp2NA.or

quotient_definition "conc' :: 'a executable_bitsNA => 'a executable_bitsNA => 'a executable_bitsNA"
is RegExp2NA.conc

quotient_definition "epsilon' :: 'a executable_bitsNA"
is RegExp2NA.epsilon

quotient_definition "plus' :: 'a executable_bitsNA => 'a executable_bitsNA"
is RegExp2NA.plus

quotient_definition "star' :: 'a executable_bitsNA => 'a executable_bitsNA"
is RegExp2NA.star

quotient_definition "rexp2na' :: 'a rexp => 'a executable_bitsNA"
is rexp2na

quotient_definition "accepts' :: ('b, 'a) executable_na => 'b list => bool"
is NA.accepts

quotient_definition "na2da' :: ('b, 'a) executable_na => ('b, 'a Cset.set) da"
is na2da

lemma [simp]: "abs_set (rep_set x) = x"
by (metis Quotient_def Quotient_set)

subsection {* Code equations for lifted operations *}

lemma [code]:
  "delta' A []    p = Cset.insert p Cset.empty"
  "delta' (A :: ('a, 's) executable_na) (a#(w :: 'a list)) p = Cset.UNION (next A a p) (delta' A w)"
apply (lifting delta.simps[unfolded Union_image_eq])
unfolding next_def_raw by simp

lemma [code]:
  "atom' a = ([True], %b s. if s = [True] & b = a then Cset.insert [False] Cset.empty else Cset.empty, %s. s = [False])"
apply (lifting RegExp2NA.atom_def)
apply (simp add: fun_rel_eq identity_equivp)
done

lemma [code]:
  "or' = (%(ql, dl, fl) (qr, dr, fr).
    ([], %a. list_case (Cset.union (Cset.map (Cons True) (dl a ql)) (Cset.map (Cons False) (dr a qr)))
              (%left s. if left then Cset.map (Cons True) (dl a s) else Cset.map (Cons False) (dr a s)),
     list_case (fl ql | fr qr) (%left s. if left then fl s else fr s)))"
apply (lifting RegExp2NA.or_def)
by (auto simp add: prod_rel_eq fun_rel_eq fun_eq_iff split: list.split)

lemma [code]:
  "conc' = (%(ql, dl, fl) (qr, dr, fr).
   (True # ql,
     %a. list_case Cset.empty
          (%left s.
              if left then Cset.union (Cset.map (Cons True) (dl a s)) (if fl s then Cset.map (Cons False) (dr a qr) else Cset.empty) else Cset.map (Cons False) (dr a s)),
     list_case False (%left s. left & fl s & fr qr | ~ left & fr s)))"
apply (lifting RegExp2NA.conc_def)
by (auto simp add: prod_rel_eq fun_rel_eq fun_eq_iff split: list.split)

lemma [code]: "epsilon' = ([], %a s. Cset.empty, %s. s = [])"
apply (lifting RegExp2NA.epsilon_def)
apply (simp add: fun_rel_eq identity_equivp)
done

lemma plus_def_equation:
  "plus (q, d, f) = (q, %a s. d a s Un (if f s then d a q else {}), f)"
unfolding RegExp2NA.plus_def by simp

lemma [code]:
  "plus' (q, d, f) = (q, %a s. Cset.union (d a s) (if f s then d a q else Cset.empty), f)"
apply (lifting plus_def_equation)
apply (simp add: fun_rel_eq identity_equivp)
done

lemma [code]:
  "star' A = or' epsilon' (plus' A)"
apply (lifting RegExp2NA.star_def)
apply (simp add: fun_rel_eq identity_equivp)
done

lemma [code]:
  "rexp2na' (Zero :: 'a rexp) = ([], %a s. Cset.empty, %s. False)"
  "rexp2na' (One :: 'a rexp) = epsilon'"
  "rexp2na' (Atom (a :: 'a)) = atom' a"
  "rexp2na' (Plus r s) = or' (rexp2na' r) (rexp2na' s)"
  "rexp2na' (rexp.Times r s) = conc' (rexp2na' r) (rexp2na' s)"
  "rexp2na' (Star (r :: 'a rexp)) == star' (rexp2na' r)"
apply (lifting rexp2na.simps)
apply (auto simp add: fun_rel_eq identity_equivp)
done

thm na2da_def[unfolded Union_image_eq]
lemma [code]:
  "na2da' A = (Cset.insert (start A) Cset.empty, %a Q. Cset.UNION Q (next A a), %Q. Cset.exists Q (fin A))"
apply (descending)
apply (fact na2da_def[unfolded Union_image_eq])
apply (simp add: fun_rel_eq identity_equivp)+
apply (simp add: Fun.map_fun_def o_def)
done

lemma [code]:
  "accepts' A w = (Cset.exists (delta' A w (start A)) (fin A))"
apply descending
apply (fact NA.accepts_def)
by auto

lemma [code_unfold]:
  "NA.accepts (rexp2na r) w = accepts' (rexp2na' r) w"
apply descending ..

lemma delta_prs [quot_preserve]:
  assumes a: "Quotient R1 abs1 rep1"
  and     b: "Quotient R2 abs2 rep2"
  shows "((map_pair rep1 (map_pair (abs2 ---> abs1 ---> rep1) (abs1 ---> id))) ---> (map rep2) ---> rep1 ---> abs1) DA.delta = DA.delta"
using assms
apply (simp only: fun_eq_iff)
apply (rule allI)
apply (rule allI)
apply (induct_tac xa)
apply simp
apply (metis Quotient_def id_apply)
apply simp
apply (rotate_tac 2, erule thin_rl)
apply (rule allI)
apply (frule_tac a="x" in Quotient_abs_rep)
apply (frule_tac a="ab" in Quotient_abs_rep)
apply simp
done

lemma [quot_preserve]:
   "(map_pair rep_set (map_pair (id ---> abs_set ---> rep_set) (abs_set ---> id)) ---> id) DA.accepts = DA.accepts"
unfolding DA.accepts_def_raw
apply (insert delta_prs[OF Quotient_set identity_quotient])
apply (simp only: fun_eq_iff)
apply simp
apply (rule allI)+
apply (erule_tac x="a" in allE)
apply (erule_tac x="aa" in allE)
apply (erule_tac x="b" in allE)
apply (erule_tac x="x" in allE)
apply (erule_tac x="a" in allE)
apply (fastforce simp only: map.id id_apply)
done

lemma [code_unfold]:
  "DA.accepts (na2da (rexp2na r)) w = DA.accepts (na2da' (rexp2na' r)) w"
by descending rule

subsection {* Example *}

definition example_expression
where
  "example_expression = (let r0 = Atom (0::nat); r1 = Atom (1::nat)
     in Times (Star (Plus (Times r1 r1) r0)) (Star (Plus (Times r0 r0) r1)))"


value [code] "NA.accepts (rexp2na example_expression) [0,1,1,0,0,1]"
value [code] "DA.accepts (na2da (rexp2na example_expression)) [0,1,1,0,0,1]"


end