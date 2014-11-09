(* Title:      Kleene algebra with tests
   Author:     Alasdair Armstrong, Victor B. F. Gomes, Georg Struth
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section {* Verification Tool Prototype  *}

theory Verification_Tool_Proto
  imports KAT_Models HoareLogic
begin

text {*
  We show how a simple verification tool prototype can be obtained from our formalisation of Kleene
  algebra with tests and its relational model. So far, only natural numbers are admitted as datatypes.
  A more versatile implementation is under construction.
  
  First, we implement states and stores of a program in the relational model.
*}

type_synonym state = "string \<Rightarrow> nat"
notation times (infixr ";" 64)

text {*
  Next, we define assignement.
*}

definition lift_fn :: "(state \<Rightarrow> state) \<Rightarrow> state relation" where
  "lift_fn f = Abs_relation {(x, f x) |x. True}"

definition assign_fn :: "string \<Rightarrow> (state \<Rightarrow> nat) \<Rightarrow> state \<Rightarrow> state" where
  "assign_fn x f \<sigma> = (\<lambda>y. if x = y then f \<sigma> else \<sigma> y)"

definition assign :: "string \<Rightarrow> (state \<Rightarrow> nat) \<Rightarrow> state relation" (infix ":=" 99) where
  "x := e = lift_fn (assign_fn x e)"

lemma lift_fn_compose [simp]: "lift_fn f \<cdot> lift_fn g = lift_fn (g \<circ> f)"
  apply (simp add: lift_fn_def)
  apply transfer
  by auto


text {*
  Then, we lift tests to the relational model.
*}

definition assert :: "'a set \<Rightarrow> 'a relation" where 
  "assert X \<equiv> Abs_relation (Id_on X)"

lemma test_assert [intro!, simp]: "test (assert X)"
  apply (simp add: assert_def test_def comp_op_relation_def)
  apply transfer
  by auto

lemma test_not_assert [intro!, simp]: "test (!(assert X))"
  apply (simp add: assert_def test_def comp_op_relation_def)
  apply transfer
  by auto

lemma [iff]: "assert X \<le> assert Y \<longleftrightarrow> X \<le> Y"
  apply (auto simp add: assert_def)
  apply transfer
  apply auto
  apply transfer
  by auto

lemma [simp]: "t (assert X) = assert X"
  by (metis test_assert test_double_comp_var)

lemma [simp]: "assert X ; assert Y = assert (X \<inter> Y)"
  apply (simp add: assert_def)
  apply transfer
  by auto

lemma [simp]: "assert X ; !assert Y = assert (X - Y)"
  apply (simp add: assert_def)
  apply transfer
  by auto

text {*
  Now, we implement Hoare's assignement axiom.
*}

abbreviation assigns_notation :: "state set \<Rightarrow> string \<Rightarrow> (state \<Rightarrow> nat) \<Rightarrow> state set"
  ("_[_|_]" [100,100,100] 101) where
  "P[x|m] \<equiv> (\<lambda>state. assign_fn x m state) ` P"

lemma hoare_assignment': "P[x|m] \<subseteq> Q \<Longrightarrow> assert P \<cdot> x := m \<le> x := m \<cdot> assert Q"
  apply (simp add: assert_def assign_def image_def lift_fn_def)
  apply transfer
  by auto

lemma hoare_assignment: "P[x|m] \<subseteq> Q \<Longrightarrow> \<lbrace>assert P\<rbrace> x := m \<lbrace>assert Q\<rbrace>"
  by (metis (full_types) hoare_assignment' hoare_triple_def_var test_assert)

text {*
  This a variant of the sequential rule where tests are assertions.
*}
  
lemma hoare_seq: "\<lbrace>assert p\<rbrace>x\<lbrace>assert q'\<rbrace> \<Longrightarrow> \<lbrace>assert q'\<rbrace>x'\<lbrace>assert q\<rbrace> \<Longrightarrow> \<lbrace>assert p\<rbrace>x\<cdot>x'\<lbrace>assert q\<rbrace>"
  by (metis sequence_rule)  
  
text {*
  We write a simple tactic for verification condition generation.
*}

named_theorems hoare_simp "simplification rules for the hoare tactic"
named_theorems hoare_rule "extra Hoare Rules"

ML {*
fun hoare_step_tac ctxt n =
  rtac @{thm hoare_assignment} n THEN TRY (rtac @{thm subset_refl} n)
  ORELSE (rtac @{thm hoare_while_inv} n THEN asm_full_simp_tac ( ctxt) 1)
  ORELSE (FIRST'
    (map (fn thm => rtac thm) (rev (Named_Theorems.get ctxt @{named_theorems hoare_rule}))) n)

val hoare_tac = Subgoal.FOCUS (fn {context = ctxt, ...} =>
  REPEAT (hoare_step_tac ctxt 1)
  THEN auto_tac ((fn ss => ss addsimps Named_Theorems.get ctxt @{named_theorems hoare_simp}) ctxt))
*}

declare hoare_seq [hoare_rule]

method_setup hoare_auto = {*
Scan.succeed (fn ctxt => SIMPLE_METHOD (REPEAT (CHANGED (hoare_tac ctxt 1))))
*}

declare assign_fn_def [hoare_simp]
declare image_def [hoare_simp]


text {*
  We add some syntactic sugar.
*}
abbreviation assign_sugar :: "string \<Rightarrow> string \<Rightarrow> state relation" (infix ":=" 99) where
  "x := y \<equiv> x := (\<lambda>\<sigma>. \<sigma> y)"

abbreviation hoare_sugar :: "'a set \<Rightarrow> 'a relation \<Rightarrow> 'a set \<Rightarrow> bool" ("\<lbrace>_\<rbrace>_\<lbrace>_\<rbrace>") where
  "\<lbrace>p\<rbrace> c \<lbrace>q\<rbrace> \<equiv> \<lbrace>assert p\<rbrace> c \<lbrace>assert q\<rbrace>"

abbreviation mod_sugar :: "string \<Rightarrow> string \<Rightarrow> state \<Rightarrow> nat" (infix "mod" 100) where
  "x mod y \<equiv> \<lambda>\<sigma>. (\<sigma> x) mod (\<sigma> y)"

abbreviation while_inv_sugar :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a relation \<Rightarrow> 'a relation" ("while _ inv _ do _" [64,64,64] 63) where
  "while b inv i do p \<equiv> while (assert b) inv (assert i) do p "


text {*
  As a complex example, we verify the partial correctness of Euclid's algorithm.
*}

lemma euclids_algorithm:
  "\<lbrace>{\<sigma>. \<sigma> ''x'' = x \<and> \<sigma> ''y'' = y}\<rbrace>
   while {\<sigma>. \<sigma> ''y'' \<noteq> 0}
   inv {\<sigma>. gcd (\<sigma> ''x'') (\<sigma> ''y'') = gcd x y}
   do (
     ''z'' := ''y'';
     ''y'' := ''x'' mod ''y'';
     ''x'' := ''z''
   )
   \<lbrace>{\<sigma>. \<sigma> ''x'' = gcd x y}\<rbrace>"
   apply hoare_auto
   by (metis gcd_red_nat)

end
