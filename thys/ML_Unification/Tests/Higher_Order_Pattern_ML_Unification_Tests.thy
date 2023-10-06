\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>contributor "Paul Bachmann"\<close>
subsection \<open>Higher-Order Pattern ML Unification Tests\<close>
theory Higher_Order_Pattern_ML_Unification_Tests
  imports
    ML_Unification_Tests_Base
begin

paragraph \<open>Summary\<close>
text \<open>Tests for @{ML_structure "Higher_Order_Pattern_Unification"}.\<close>

ML\<open>
  structure Prop = SpecCheck_Property
  structure UC = Unification_Combinator
  open Unification_Tests_Base
  structure Unif = Higher_Order_Pattern_Unification
  val match = Unif.match []
  val match_hints =
    let fun match binders =
      UC.add_fallback_matcher
      (fn match_theory => Unif.e_match Unification_Util.match_types match_theory match_theory)
      ((fn binders =>
        (Hints.map_retrieval (Hints.mk_retrieval Hints.TI.generalisations |> K)
        #> Hints.UH.map_concl_unifier (Unif.match |> K)
        #> Hints.UH.map_normalisers (Unif.norms_match |> K)
        #> Hints.UH.map_prems_unifier (match |> K))
        |> Context.proof_map
        #> Test_Unification_Hints.try_hints binders)
        |> UC.norm_matcher (#norm_term Unif.norms_match))
      binders
    in match [] end

  val unify = Unif.unify []
  val unify_hints =
    let fun unif binders =
      UC.add_fallback_unifier
      (fn unif_theory => Unif.e_unify Unification_Util.unify_types unif_theory unif_theory)
      ((fn binders =>
        (Hints.UH.map_concl_unifier (Unif.match |> K)
        #> Hints.UH.map_normalisers (Unif.norms_unify |> K)
        #> Hints.UH.map_prems_unifier (unif |> K))
        |> Context.proof_map
        #> Test_Unification_Hints.try_hints binders)
        |> UC.norm_unifier (#norm_term Unif.norms_unify))
      binders
    in unif [] end
\<close>

subsubsection \<open>Matching\<close>
paragraph \<open>Unit Tests\<close>

ML_command\<open>
  let
    val ctxt = Proof_Context.set_mode Proof_Context.mode_schematic @{context}
      |> Variable.declare_term @{term "f :: nat \<Rightarrow> bool \<Rightarrow> nat"}
    val tests = map (apply2 (Syntax.read_term ctxt))[
      ("?x :: nat", "(?x + 1 :: nat)"),
      ("(g :: nat \<Rightarrow> nat \<Rightarrow> nat) ?x ?x", "(g :: nat \<Rightarrow> nat \<Rightarrow> nat) (?x + 1) (?x + 1)"),
      ("\<lambda>y. (?x :: nat \<Rightarrow> ?'Z) y", "\<lambda>y. f y"),
      ("(g :: ?'X \<Rightarrow> ?'Y \<Rightarrow> ?'Z) (x :: ?'X) (y :: ?'Y)", "(g :: ?'Y \<Rightarrow> ?'Z \<Rightarrow> ?'Z) (x :: ?'Y) (y :: ?'Z)"),
      ("(g :: ?'Z \<Rightarrow> ?'X)", "\<lambda>(x :: ?'X). (g :: ?'X \<Rightarrow> ?'Y) x"),
      ("\<lambda> (x :: nat). (0 :: nat)", "\<lambda> (x :: nat). (0 :: nat)"),
      ("\<lambda> (x :: nat). x", "\<lambda> (x :: nat). x"),
      ("\<lambda> (x :: nat) (y :: bool). (x, y)", "\<lambda> (x :: nat) (y :: bool). (x, y)"),
      ("\<lambda> (x :: ?'A) (y :: bool). (?x :: ?'A \<Rightarrow> bool \<Rightarrow> ?'Z) x y", "\<lambda> (x :: nat) (y :: bool). f x y"),
      ("\<lambda>(x :: ?'X). (g :: ?'X \<Rightarrow> ?'X) x", "(g :: ?'X \<Rightarrow> ?'X)"),
      ("\<lambda>y. (?x :: nat \<Rightarrow> bool \<Rightarrow> nat) y", "\<lambda>y. f y"),
      ("\<lambda>y z. (?x :: nat \<Rightarrow> bool \<Rightarrow> nat) y z", "f")
    ]
    val check = check_unit_tests_hints_match tests true []
  in
    Lecker.test_group ctxt () [
      check "match" match,
      check "match_hints" match_hints
    ]
  end
\<close>

subparagraph \<open>Asymmetry\<close>

ML_command\<open>
  let
    val ctxt = Proof_Context.set_mode Proof_Context.mode_schematic @{context}
      |> Variable.declare_term @{term "f :: nat \<Rightarrow> bool \<Rightarrow> nat"}
    val tests = map (apply2 (Syntax.read_term ctxt))[
      ("\<lambda>y. f y", "\<lambda>y. (?x :: nat \<Rightarrow> bool \<Rightarrow> nat) y")
    ]
    val check = check_unit_tests_hints_match tests false []
  in
    Lecker.test_group ctxt () [
      check "match" match,
      check "match_hints" match_hints
    ]
  end
\<close>

subparagraph \<open>Ground Hints\<close>

ML_command\<open>
  let
    val ctxt = Proof_Context.set_mode Proof_Context.mode_schematic @{context}
    val hints = map (Skip_Proof.make_thm (Proof_Context.theory_of ctxt) o Syntax.read_term ctxt) [
      "?x \<equiv> 2 \<Longrightarrow> ?x + (-?x :: int) \<equiv> 0",
      "?x \<equiv> 0 \<Longrightarrow> ?y \<equiv> 0 \<Longrightarrow> (?x :: int) + ?y \<equiv> 0"
    ]
    val tests = map (apply2 (Syntax.read_term ctxt))[
      ("(2 + -2) + (0 + 0) :: int", "0 :: int")
    ]
    val check_hints = check_unit_tests_hints_match tests
  in
    Lecker.test_group ctxt () [
      check_hints false [] "match" match,
      check_hints false [] "match_hints without hints" match_hints,
      check_hints true hints "match_hints with hints" match_hints
    ]
  end
\<close>


subsubsection \<open>Unification\<close>

paragraph \<open>Generated Tests\<close>
subparagraph \<open>First-Order\<close>

ML_command\<open>
  structure Test_Params =
  struct
    val unify = unify
    val unify_hints = unify_hints
    val params = {
      nv = 10,
      ni = 10,
      max_h = 5,
      max_args = 4
    }
  end
  structure First_Order_Tests = First_Order_Unification_Tests(Test_Params)
  val _ = First_Order_Tests.tests @{context} (SpecCheck_Random.new ())
\<close>

subparagraph \<open>Higher-Order Pattern\<close>

ML_file\<open>higher_order_pattern_unification_tests.ML\<close>

ML_command\<open>
  val ctxt = @{context}
  val tests = Higher_Order_Pattern_Unification_Tests.unit_tests_unifiable ctxt
  val check_hints = check_unit_tests_hints_unif tests
  val _ = Lecker.test_group ctxt () [
      check_hints true [] "unify" unify,
      check_hints true [] "unify_hints" unify_hints
    ]
\<close>

paragraph \<open>Unit Tests\<close>
subparagraph \<open>With Unification Hints\<close>

ML_command\<open>
  let
    val ctxt = Proof_Context.set_mode Proof_Context.mode_schematic @{context}
      |> Variable.declare_term @{term "f :: (nat \<Rightarrow> nat) \<times> nat \<Rightarrow> nat"}
      |> Variable.declare_term @{term "g :: nat \<times> nat \<Rightarrow> nat"}
      |> Variable.declare_term @{term "h :: nat"}
    val hints = map (Skip_Proof.make_thm (Proof_Context.theory_of ctxt) o Syntax.read_term ctxt) [
      "?x \<equiv> (0 :: nat) \<Longrightarrow> ?y \<equiv> ?z \<Longrightarrow> ?x + ?y \<equiv> ?z",
      "(?x :: ?'X) \<equiv> (?y :: ?'X) \<Longrightarrow> id ?x \<equiv> ?y",
      "(?x1 :: nat) \<equiv> ?x2 \<Longrightarrow> (?y1 :: nat) \<equiv> ?y2 \<Longrightarrow> ?x1 + ?y1 \<equiv> ?y2 + ?x2"
    ]
    val tests = map (apply2 (Syntax.read_term ctxt)) [
      ("\<lambda> x y. 0 + 1 :: nat", "\<lambda> x y. 1 :: nat"),
      ("\<lambda> x. 0 + 0 + x :: nat", "\<lambda> x. x :: nat"),
      ("\<lambda> x y. 0 + Suc ?x", "\<lambda> x y. Suc 2"),
      ("\<lambda> (x :: nat) (y :: nat). y + (0 + x)", "\<lambda> (x :: nat) (y :: nat). x + (0 + y)"),
      ("f (\<lambda> u. g (?x, h), h)", "id (f (\<lambda> u. ?y, 0 + h))")
   ]
    val check_hints = check_unit_tests_hints_unif tests
  in
    Lecker.test_group ctxt () [
      check_hints false [] "unify" unify,
      check_hints false [] "unify_hints without hints" unify_hints,
      check_hints true hints "unify_hints with hints" unify_hints
    ]
  end
\<close>

end
