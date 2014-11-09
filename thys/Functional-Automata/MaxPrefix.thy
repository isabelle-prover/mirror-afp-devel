(*  Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

section "Maximal prefix"

theory MaxPrefix
imports "~~/src/HOL/Library/Sublist"
begin

definition
 is_maxpref :: "('a list => bool) => 'a list => 'a list => bool" where
"is_maxpref P xs ys =
 (prefixeq xs ys & (xs=[] | P xs) & (!zs. prefixeq zs ys & P zs --> prefixeq zs xs))"

type_synonym 'a splitter = "'a list => 'a list * 'a list"

definition
 is_maxsplitter :: "('a list => bool) => 'a splitter => bool" where
"is_maxsplitter P f =
 (!xs ps qs. f xs = (ps,qs) = (xs=ps@qs & is_maxpref P ps xs))"

primrec maxsplit :: "('a list => bool) => 'a list * 'a list => 'a list => 'a splitter" where
"maxsplit P res ps []     = (if P ps then (ps,[]) else res)" |
"maxsplit P res ps (q#qs) = maxsplit P (if P ps then (ps,q#qs) else res)
                                     (ps@[q]) qs"

declare split_if[split del]

lemma maxsplit_lemma: "!!(ps::'a list) res.
  (maxsplit P res ps qs = (xs,ys)) =
  (if EX us. prefixeq us qs & P(ps@us) then xs@ys=ps@qs & is_maxpref P xs (ps@qs)
   else (xs,ys)=res)"
apply(unfold is_maxpref_def)
apply (induct "qs")
 apply (simp split: split_if)
 apply blast
apply simp
apply (erule thin_rl)
apply clarify
apply (case_tac "EX us. prefixeq us qs & P (ps @ a # us)")
 apply (subgoal_tac "EX us. prefixeq us (a # qs) & P (ps @ us)")
  apply simp
 apply (blast intro: prefixeq_Cons[THEN iffD2])
apply (subgoal_tac "~P(ps@[a])")
 prefer 2 apply blast
apply (simp (no_asm_simp))
apply (case_tac "EX us. prefixeq us (a#qs) & P (ps @ us)")
 apply simp
 apply clarify
 apply (case_tac "us")
  apply (rule iffI)
   apply (simp add: prefixeq_Cons prefixeq_append)
   apply blast
  apply (simp add: prefixeq_Cons prefixeq_append)
  apply clarify
  apply (erule disjE)
   apply (fast dest: prefix_order.antisym)
  apply clarify
  apply (erule disjE)
   apply clarify
   apply simp
  apply (erule disjE)
   apply clarify
   apply simp
  apply blast
 apply simp
apply (subgoal_tac "~P(ps)")
apply (simp (no_asm_simp))
apply fastforce
done

declare split_if[split add]

lemma is_maxpref_Nil[simp]:
 "~(? us. prefixeq us xs & P us) ==> is_maxpref P ps xs = (ps = [])"
apply(unfold is_maxpref_def)
apply blast
done

lemma is_maxsplitter_maxsplit:
 "is_maxsplitter P (%xs. maxsplit P ([],xs) [] xs)"
apply(unfold is_maxsplitter_def)
apply (simp add: maxsplit_lemma)
apply (fastforce)
done

lemmas maxsplit_eq = is_maxsplitter_maxsplit[simplified is_maxsplitter_def]

end
