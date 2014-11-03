(*  Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

section "Deterministic automata"

theory DA
imports AutoProj
begin

type_synonym ('a,'s)da = "'s * ('a => 's => 's) * ('s => bool)"

definition
 foldl2 :: "('a => 'b => 'b) => 'a list => 'b => 'b" where
"foldl2 f xs a = foldl (%a b. f b a) a xs"

definition
 delta :: "('a,'s)da => 'a list => 's => 's" where
"delta A = foldl2 (next A)"

definition
 accepts :: "('a,'s)da => 'a list => bool" where
"accepts A = (%w. fin A (delta A w (start A)))"

lemma [simp]: "foldl2 f [] a = a & foldl2 f (x#xs) a = foldl2 f xs (f x a)"
by(simp add:foldl2_def)

lemma delta_Nil[simp]: "delta A [] s = s"
by(simp add:delta_def)

lemma delta_Cons[simp]: "delta A (a#w) s = delta A w (next A a s)"
by(simp add:delta_def)

lemma delta_append[simp]:
 "!!q ys. delta A (xs@ys) q = delta A ys (delta A xs q)"
by(induct xs) simp_all

end
