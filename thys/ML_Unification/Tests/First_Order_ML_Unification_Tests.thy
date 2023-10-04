\<^marker>\<open>creator "Kevin Kappelmann"\<close>
\<^marker>\<open>contributor "Paul Bachmann"\<close>
subsection \<open>First-Order ML Unification Tests\<close>
theory First_Order_ML_Unification_Tests
  imports
    ML_Unification_Tests_Base
begin

paragraph \<open>Summary\<close>
text \<open>Tests for @{ML_structure "First_Order_Unification"}.\<close>

ML\<open>
  structure Prop = SpecCheck_Property
  structure UC = Unification_Combinator
  open Unification_Tests_Base
  structure Unif = First_Order_Unification
  structure Norm = Envir_Normalisation
  val match = Unif.match []
  val match_hints =
    let fun match binders =
      UC.add_fallback_matcher
      (Unif.e_match Unification_Util.match_types)
      ((fn binders =>
        (Hints.map_retrieval (Hints.mk_retrieval Hints.TI.generalisations |> K)
        #> Hints.UH.map_concl_unifier (Higher_Order_Pattern_Unification.match |> K)
        #> Hints.UH.map_normalisers (Unification_Util.beta_eta_short_norms_match |> K)
        #> Hints.UH.map_prems_unifier (match |> UC.norm_matcher Norm.beta_norm_term_match |> K))
        |> Context.proof_map
        #> Test_Unification_Hints.try_hints binders)
        |> UC.norm_matcher (#norm_term Unif.norms_match))
      binders
    in match [] end

  val unify = Unif.unify []
  val unify_hints =
    let fun unif binders =
      UC.add_fallback_unifier
      (Unif.e_unify Unification_Util.unify_types)
      ((fn binders =>
        (Hints.UH.map_concl_unifier (Higher_Order_Pattern_Unification.match |> K)
        #> Hints.UH.map_normalisers (Unification_Util.beta_eta_short_norms_unif |> K)
        #> Hints.UH.map_prems_unifier (unif |> UC.norm_unifier Norm.beta_norm_term_unif |> K))
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
      ("(?x :: nat \<Rightarrow> ?'Z) 1", "f 1"),
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
      ("?g ?x ?y d", "g ?y ?x d"),
      ("f 0 True", "(\<lambda>x y. f y x) True 0"),
      ("\<lambda> (x :: ?'a) y. f y", "\<lambda>(x :: ?'b). f"),
      ("\<lambda>y z. (?x :: nat \<Rightarrow> bool \<Rightarrow> nat) y z", "f"),
      ("\<lambda>x. (?f :: nat \<Rightarrow> bool \<Rightarrow> nat) 0 x", "\<lambda>x. f 0 x")
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
      ("f 1", "(?x :: nat \<Rightarrow> ?'Z) 1")
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

ML_command\<open>
  structure Test_Params =
  struct
    val unify = unify
    val unify_hints = unify_hints
    val params = {
      nv = 4,
      ni = 2,
      max_h = 5,
      max_args = 4
    }
  end
  structure First_Order_Tests = First_Order_Unification_Tests(Test_Params)
  val _ = First_Order_Tests.tests @{context} (SpecCheck_Random.new ())
\<close>

paragraph \<open>Unit Tests\<close>
subparagraph \<open>Occurs-Check\<close>

ML_command\<open>
  let
    val unit_tests = [
      (
        Var (("x", 0), TVar (("X", 0), [])),
        Var (("y", 0), TVar (("X", 0), []) --> TFree ("'a", [])) $
          Var (("x", 0), TVar (("X", 0), []))
      ),
      (
        Var (("y", 0), TVar (("X", 0), []) --> TFree ("'a", [])) $
          Var (("x", 0), TVar (("X", 0), [])),
        Var (("x", 0), TVar (("X", 0), []))
      ),
      (
        Free (("f", [TVar (("X", 0), []), TVar (("X", 0), [])] ---> TFree ("'a", []))) $
          Var (("x", 0), TVar (("X", 0), [])) $
          Var (("y", 0), TVar (("X", 0), [])),
        Free (("f", [TVar (("X", 0), []), TVar (("X", 0), [])] ---> TFree ("'a", []))) $
          Var (("y", 0), TVar (("X", 0), [])) $ (
            Free (("g", TVar (("X", 0), []) --> TVar (("X", 0), []))) $
              Var (("x", 0), TVar (("X", 0), []))
          )
      ),
      (
        Free (("f", [TVar (("X", 0), []), TVar (("Y", 0), [])] ---> TFree ("'a", []))) $
          Var (("x", 0), TVar (("X", 0), [])) $
          Var (("y", 0), TVar (("Y", 0), [])),
        Free (("f", [TVar (("Y", 0), []), TVar (("X", 0), [])] ---> TFree ("'a", []))) $
          Var (("y", 0), TVar (("Y", 0), [])) $ (
            Free (("g", TVar (("X", 0), []) --> TVar (("X", 0), []))) $
              Var (("x", 0), TVar (("X", 0), []))
          )
      )
    ]
    fun check name unif ctxt _ =
      check_list unit_tests ("occurs-check for " ^ name)
        (Prop.prop (not o terms_unify_thms_correct_unif ctxt unif)) ctxt
      |> K ()
  in
    Lecker.test_group @{context} () [
      check "unify" unify,
      check "unify_hints" unify_hints
    ]
  end
\<close>

subparagraph \<open>Lambda-Abstractions\<close>

ML_command\<open>
  let
    val ctxt = Proof_Context.set_mode Proof_Context.mode_schematic @{context}
      |> Variable.declare_term @{term "f :: nat \<Rightarrow> bool \<Rightarrow> nat"}
    val tests = map (apply2 (Syntax.read_term ctxt))[
      ("\<lambda> (x :: nat). (0 :: nat)", "\<lambda> (x :: nat). (0 :: nat)"),
      ("\<lambda> (x :: nat). x", "\<lambda> (x :: nat). x"),
      ("\<lambda> (x :: nat) (y :: bool). (x, y)", "\<lambda> (x :: nat) (y :: bool). (x, y)"),
      ("\<lambda> (x :: ?'a) y. f y", "\<lambda>(x :: ?'b). f"),
      ("\<lambda> (x :: nat) (y :: bool). f x y", "\<lambda> (x :: nat) (y :: bool). (?x :: nat \<Rightarrow> bool \<Rightarrow> ?'Z) x y"),
      ("\<lambda>x. (?f :: nat \<Rightarrow> bool \<Rightarrow> nat) 0 x", "\<lambda>x. f ?g x"),
      ("(?f :: nat \<Rightarrow> bool \<Rightarrow> nat) (?n :: nat)", "?g :: bool \<Rightarrow> nat")
    ]
    val check = check_unit_tests_hints_unif tests true []
  in
    Lecker.test_group ctxt () [
      check "unify" unify,
      check "unify_hints" unify_hints
    ]
  end
\<close>

ML_command\<open>
  let
    val ctxt = Proof_Context.set_mode Proof_Context.mode_schematic @{context}
    val hints = map (Skip_Proof.make_thm (Proof_Context.theory_of ctxt) o Syntax.read_term ctxt) [
      "?x \<equiv> (0 :: nat) \<Longrightarrow> ?y \<equiv> ?z \<Longrightarrow> ?x + ?y \<equiv> ?z"
    ]
    val tests = map (apply2 (Syntax.read_term ctxt))[
      ("\<lambda> (x :: nat) (y :: bool). x", "\<lambda> (x :: nat) (y :: bool). 0 + x"),
      ("0 + (\<lambda> (x :: nat) (y :: bool). x) 0 ?y", "0 + (\<lambda> (x :: nat) (y :: bool). 0 + x) 0 ?z")
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
