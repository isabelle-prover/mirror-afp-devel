theory Boolean_Expression_Example
imports Boolean_Expression_Checkers
begin

section{* Example *}

text {* Example usage of checkers. We have our own type of boolean expressions
with its own evaluation function: *}

datatype_new 'a bexp =
  Const bool |
  Atom 'a |
  Neg "'a bexp" |
  And "'a bexp" "'a bexp"

fun bval where
"bval (Const b) s = b" |
"bval (Atom a) s = s a" |
"bval (Neg b) s = (\<not> bval b s)" |
"bval (And b1 b2) s = (bval b1 s \<and> bval b2 s)"

text{* Now we translate into the datatype provided by the checkers interface
and show that the semantics remains the same: *}

fun bool_expr_of_bexp :: "'a bexp \<Rightarrow> 'a bool_expr" where
"bool_expr_of_bexp (Const b) = Const_bool_expr b" |
"bool_expr_of_bexp (Atom a) = Atom_bool_expr a" |
"bool_expr_of_bexp (Neg b) = Neg_bool_expr(bool_expr_of_bexp b)" |
"bool_expr_of_bexp (And b1 b2) = And_bool_expr (bool_expr_of_bexp b1) (bool_expr_of_bexp b2)"

lemma val_preservation: "val_bool_expr(bool_expr_of_bexp b) s = bval b s"
by(induction b) auto

text{* Trivial tautology checker and its correctness: *}

definition "my_taut_test = taut_test o bool_expr_of_bexp"

corollary my_taut_test: "my_taut_test b = (\<forall>s. bval b s)"
by(simp add: my_taut_test_def val_preservation taut_test)


text{* Test: pigeonhole formulas *}

definition "Or b1 b2 == Neg (And (Neg b1) (Neg b2))"
definition "ors = foldl Or (Const False)"
definition "ands = foldl And (Const True)"

definition "pc n = ands[ors[Atom(i,j). j <- [1..<n+1]]. i <- [1..<n+2]]"

definition "nc n = ands[Or (Neg(Atom(i,k))) (Neg(Atom(j,k))).
  k <- [1..<n+1], i <- [1..<n+1], j <- [i+1..<n+2]]"

definition "php n = Neg(And (pc n) (nc n))"

text{* Takes about 5 secs; with 7 instead of 6 it takes about 4 mins (2014). *}
lemma "my_taut_test (php 6)"
by eval

end
