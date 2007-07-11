(*  ID:         $Id: RegSet.thy,v 1.6 2007-07-11 10:13:01 stefanberghofer Exp $
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

header "Regular sets"

theory RegSet
imports Main
begin

constdefs
 conc :: "'a list set => 'a list set => 'a list set"
"conc A B == {xs@ys | xs ys. xs:A & ys:B}"

inductive_set
  star :: "'a list set => 'a list set"
  for A :: "'a list set"
where
  NilI[iff]:   "[] : star A"
| ConsI[intro,simp]:  "[| a:A; as : star A |] ==> a@as : star A"

lemma concat_in_star: "!xs: set xss. xs:S ==> concat xss : star S"
by (induct "xss") simp_all

lemma in_star:
 "w : star U = (? us. (!u : set(us). u : U) & (w = concat us))"
apply (rule iffI)
 apply (erule star.induct)
  apply (rule_tac x = "[]" in exI)
  apply simp
 apply clarify
 apply (rule_tac x = "a#us" in exI)
 apply simp
apply clarify
apply (simp add: concat_in_star)
done

end
