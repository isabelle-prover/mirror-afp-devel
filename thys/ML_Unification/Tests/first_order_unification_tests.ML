(*  Title:      ML_Unification/first_order_unification_tests.ML
    Author:     Kevin Kappelmann

First-order unification tests.
*)
signature FIRST_ORDER_UNIFICATION_TESTS =
sig
  val tests_identical : Proof.context Lecker.test
  val tests_identical_env : Proof.context Lecker.test
  val tests_thm : Proof.context Lecker.test
  val tests_replaced : Proof.context Lecker.test
  val tests_symmetry : Proof.context Lecker.test
  val generated_tests : Proof.context Lecker.test

  val unit_tests_unifiable : Proof.context Lecker.test
  val unit_tests_non_unifiable : Proof.context Lecker.test

  val unit_tests_hints_non_recursive : Proof.context Lecker.test
  val unit_tests_multiple_matching_hints : Proof.context Lecker.test
  val unit_tests_hints_recursive : Proof.context Lecker.test
  val unit_tests_multiple_successful_hints : Proof.context Lecker.test
  val unit_tests_hints : Proof.context Lecker.test

  val unit_tests : Proof.context Lecker.test

  val tests : Proof.context Lecker.test
end

functor First_Order_Unification_Tests(P : sig
    val unify : Unification_Base.closed_unifier
    val unify_hints : Unification_Base.closed_unifier
    val params : {
      nv : int,
      ni : int,
      max_h : int,
      max_args : int
    }
  end) : FIRST_ORDER_UNIFICATION_TESTS =
struct

structure Prop = SpecCheck_Property
structure Gen = SpecCheck_Generator
structure UUtil = Unification_Util
open Unification_Tests_Base

val weights = (1, 1, 1, 0)

fun term_gen ctxt =
  let val {nv, ni, max_h, max_args} = P.params
  in term_gen' ctxt nv ni weights max_h max_args end

fun term_pair_gen ctxt =
  let val {nv, ni, max_h, max_args} = P.params
  in Unification_Tests_Base.term_pair_gen' ctxt nv ni weights max_h max_args end

(* standard unification *)
(** generated tests **)
(*** unification of identical terms ***)
fun tests_identical ctxt r =
  let fun check_identical name unif ctxt =
    let val term_gen' = term_gen ctxt
    in
      check_thm_unif (Gen.map (fn t => (t, t)) term_gen')
        ("Unifying identical terms with " ^ name) unif ctxt
    end
  in
    Lecker.test_group ctxt r [
      check_identical "unify" P.unify,
      check_identical "unify_hints" P.unify_hints
    ]
  end

fun tests_identical_env ctxt r =
  let
    fun check_identical_env name unif ctxt =
      let val term_gen' = term_gen ctxt
      in
        check (Gen.map (fn t => (t, t)) term_gen')
          ("Unifying identical terms does not change environment with " ^ name)
          (Prop.==> (terms_unify ctxt unif,
            (fn tp => unif ctxt tp (UUtil.empty_envir tp)
              |> Seq.list_of
              |> List.all (Envir.is_empty o fst))))
          ctxt
      end
  in
    Lecker.test_group ctxt r [
      check_identical_env "unify" P.unify,
      check_identical_env "unify_hints" P.unify_hints
    ]
  end

(*** unification of randomly generated terms ***)
fun tests_thm ctxt r =
  let
    fun check_thm' name unif ctxt =
      let val term_pair_gen' = term_pair_gen ctxt
      in check_thm_unif term_pair_gen' name unif ctxt end
    val ctxt' = Config.put SpecCheck_Configuration.max_discard_ratio 100 ctxt
  in
    Lecker.test_group ctxt' r [
      check_thm' "unify" P.unify,
      check_thm' "unify_hints" P.unify_hints
    ]
  end

fun tests_replaced ctxt r =
  let fun check_replaced name unif ctxt =
    let
      val term_gen' = term_gen ctxt
      val unvarify = map_aterms (fn (Var ((n, i), T)) => Free (n ^ Int.toString i, T) | T => T)
    in
      check_thm_unif (Gen.map (fn t => (t, unvarify t)) term_gen')
        ("Unifying terms with Var replaced by Free for " ^ name) unif ctxt
    end
  in
    Lecker.test_group ctxt r [
      check_replaced "unify" P.unify,
      check_replaced "unify_hints" P.unify_hints
    ]
  end

(**** symmetry of success ****)
fun tests_symmetry ctxt r =
  let fun check_thm_symmetry name unif ctxt =
    let
      val term_pair_gen' = term_pair_gen ctxt
      val terms_unify_thms_correct' = terms_unify_thms_correct_unif ctxt unif
    in
      check term_pair_gen' ("Symmetry of " ^ name)
        (Prop.prop (fn tp =>
          terms_unify_thms_correct' tp = terms_unify_thms_correct' (swap tp)))
        ctxt
    end
  in
    Lecker.test_group ctxt r [
      check_thm_symmetry "unify" P.unify,
      check_thm_symmetry "unify_hints" P.unify_hints
    ]
  end

fun generated_tests ctxt r =
  Lecker.test_group ctxt r [
    tests_identical,
    tests_identical_env,
    tests_thm,
    tests_replaced,
    tests_symmetry
  ]

(** Unit tests **)
(*** unifiable ***)
fun unit_tests_unifiable ctxt r =
  let
    val tests = [
      (Var (("x", 0), TVar (("X", 0), [])), Var (("x", 0), TVar (("Y", 0), []))),
      (Var (("x", 0), TVar (("X", 0), [])), Var (("x", 0), TFree ("'a", []))),
      (Var (("x", 0), TVar (("X", 0), [])), Var (("y", 0), TVar (("X", 0), []))),
      (Var (("x", 0), TVar (("X", 0), [])), Free ("c", TFree ("'a", []))),
      (Var (("x", 0), TFree ("'a", [])), Free ("f", TVar (("X", 0), []))),
      (Var (("x", 0), TVar (("X", 0), [])), Free ("f", TFree ("'a", []))),
      (Var (("x", 0), TFree ("'a", [])), Free ("f", TFree ("'a", []))),
      (
        Free ("x", TFree ("'a", []) --> TVar (("X", 0), [])) $
          Free ("x", TVar (("Y", 0), [])),
        Free ("x", TVar (("Y", 0), []) --> TFree ("'b", [])) $
          Free ("x", TFree ("'a", []))
      ),
      (
        Free ("f", TVar (("X", 0), []) --> TVar (("Y", 0), [])) $
          Free ("c", TVar (("X", 0), [])),
        Free ("f", TVar (("X", 0), []) --> TVar (("Y", 0), [])) $
          Var (("x", 0), TVar (("X", 1), []))
      ),
      (
        Free ("f", [TVar (("A", 0), []), TVar (("B", 0), [])] ---> TFree ("c", [])) $
          Free ("a", TVar (("A", 0), [])) $
          Free ("b", TVar (("B", 0), [])),
        Free ("f", [TVar (("B", 0), []), TVar (("A", 0), [])] ---> TFree ("c", [])) $
          Free ("a", TVar (("B", 0), [])) $
          Free ("b", TVar (("A", 0), []))
      )
    ]
    fun check name unif ctxt r =
      check_list tests ("unifiable unit tests for " ^ name)
        (Prop.prop (terms_unify_thms_correct_unif ctxt unif)) ctxt
      |> K r
  in
    Lecker.test_group ctxt r [
      check "unify" P.unify,
      check "unify_hints" P.unify_hints
    ]
  end

(*** non-unifiable ***)
fun unit_tests_non_unifiable ctxt r =
  let
    val unit_tests = [
      (Free("f", TFree("'a",[])), Free("f", TFree("'b",[]))),
      (Free("f", TFree("'a",[])), Free("g", TFree("'a",[])))
    ]
    fun check name unif ctxt r =
      check_list unit_tests ("non-unifiable unit tests for " ^ name)
        (Prop.prop (not o terms_unify ctxt unif)) ctxt
      |> K r
  in
    Lecker.test_group ctxt r [
      check "unify" P.unify,
      check "unify_hints" P.unify_hints
    ]
  end

(* hint tests *)
(** non-recursive tests **)
fun unit_tests_hints_non_recursive ctxt r =
  let
    val ctxt' = Proof_Context.set_mode Proof_Context.mode_schematic ctxt
    val hints = map (Skip_Proof.make_thm (Proof_Context.theory_of ctxt') o Syntax.read_term ctxt') [
      "?z \<equiv> ?x \<Longrightarrow> ?y \<equiv> (0 :: nat) \<Longrightarrow> ?z \<equiv> ?x + ?y",
      "?x \<equiv> 1 \<Longrightarrow> ?y \<equiv> 1 \<Longrightarrow> (1 :: nat) \<equiv> ?x * ?y"
    ]
    val tests = map (apply2 (Syntax.read_term ctxt')) [
      ("1 :: nat", "1 + 0 :: nat"),
      ("1 :: nat", "?x + 0 :: nat"),
      ("1 :: nat", "?a * ?b :: nat"),
      ("\<lambda>(x :: nat) y. x", "\<lambda>(x :: nat) y. x + 0")
    ]
    fun check_hints should_succeed hints name =
      check_unit_tests_hints_unif tests should_succeed hints ("non-recursive hint unit tests for " ^ name)
  in
    Lecker.test_group ctxt' r [
      check_hints false [] "unify" P.unify,
      check_hints false [] "unify_hints without hints" P.unify_hints,
      check_hints true hints "unify_hints with hints" P.unify_hints
    ]
  end

(** multiple matching hints **)
fun unit_tests_multiple_matching_hints ctxt r =
  let
    val ctxt' = Proof_Context.set_mode Proof_Context.mode_schematic ctxt
    val hints = map (Skip_Proof.make_thm (Proof_Context.theory_of ctxt') o Syntax.read_term ctxt') [
      "Suc ?x \<equiv> 1",
      "?x \<equiv> 0 \<Longrightarrow> Suc ?x \<equiv> 1"
    ]
    val tests = map (apply2 (Syntax.read_term ctxt')) [
      ("Suc x :: nat", "1 :: nat")
    ]
    fun check_hints should_succeed hints name =
      check_unit_tests_hints_unif tests should_succeed hints
        ("multiple matching hints unit tests for " ^ name)
  in
    Lecker.test_group ctxt' r [
      check_hints false [] "unify" P.unify,
      check_hints false [] "unify_hints without hints" P.unify_hints,
      check_hints false (tl hints) "unify_hints with wrong hints" P.unify_hints,
      check_hints true [hd hints] "unify_hints with correct hints" P.unify_hints,
      check_hints true hints "unify_hints with all hints" P.unify_hints,
      check_hints true (rev hints) "unify_hints with reversed hints order" P.unify_hints
    ]
  end

(** recursive hints **)
fun unit_tests_hints_recursive ctxt r =
  let
    val ctxt' =
      Proof_Context.set_mode Proof_Context.mode_schematic ctxt
      |> Variable.declare_term @{term "f :: nat => nat"}
      |> Variable.declare_term @{term "g :: nat => nat"}
    val hints = map (Skip_Proof.make_thm (Proof_Context.theory_of ctxt') o Syntax.read_term ctxt') [
        "?x \<equiv> ?z \<Longrightarrow> ?y \<equiv> (0 :: nat) \<Longrightarrow> ?x + ?y \<equiv> ?z",
        "?y \<equiv> ?x + ?z \<Longrightarrow> ?x + (Suc ?z) \<equiv> Suc ?y",
        "?x \<equiv> f (g 0) \<Longrightarrow> ?y \<equiv> g (f 0) \<Longrightarrow> f (g ?x) \<equiv> g (f ?y)",
        "?y \<equiv> f ?x \<Longrightarrow> ?x \<equiv> f (g 0) \<Longrightarrow> f (g ?x) \<equiv> g (f ?y)"
      ]
    val tests = map (apply2 (Syntax.read_term ctxt')) [
      ("1 :: nat", "(?x + 0) + 0 :: nat"),
      ("1 :: nat", "?x + (0 + 0) :: nat"),
      ("x + (Suc 0) :: nat", "Suc x :: nat"),
      ("f (g (f (g 0)))", "g (f (g (f 0)))"),
      ("f (g (f ((g 0) + 0)))", "g (f (f (f (g 0))))")
    ]
    fun check_hints should_succeed hints name =
      check_unit_tests_hints_unif tests should_succeed hints ("recursive hints unit tests for " ^ name)
  in
    Lecker.test_group ctxt' r [
      check_hints false [] "unify" P.unify,
      check_hints false [] "unify_hints without hints" P.unify_hints,
      check_hints true hints "unify_hints with hints" P.unify_hints
    ]
  end

(** disabling symmetric application of hints **)
fun unit_tests_hints_try_symmetric ctxt r =
  let
    open Unification_Tests_Base
    val ctxt' = Proof_Context.set_mode Proof_Context.mode_schematic ctxt
      |> Context.proof_map (Hints.map_retrieval
        (Hints.mk_retrieval Hints.TI.generalisations |> K))
    val hints = map (Skip_Proof.make_thm (Proof_Context.theory_of ctxt') o Syntax.read_term ctxt') [
        "?x \<equiv> ?z \<Longrightarrow> ?y \<equiv> (0 :: nat) \<Longrightarrow> ?x + ?y \<equiv> ?z"
      ]
    val (tests_correct, tests_incorrect) = map (apply2 (apply2 (Syntax.read_term ctxt'))) [
        (("?x + 0 :: nat", "1 :: nat"), ("1 :: nat", "?x + 0 :: nat"))
      ] |> split_list
    fun check_hints should_succeed tests name =
      check_unit_tests_hints_unif tests should_succeed hints ("no symmetric hints for " ^ name)
  in
    Lecker.test_group ctxt' r [
      check_hints true tests_correct "matching problem" P.unify_hints,
      check_hints false tests_incorrect "symmetric problem" P.unify_hints
    ]
  end

(** multiple successful hints **)
fun unit_tests_multiple_successful_hints ctxt r =
  let
    val ctxt' = Proof_Context.set_mode Proof_Context.mode_schematic ctxt
    val hints = map (Skip_Proof.make_thm (Proof_Context.theory_of ctxt') o Syntax.read_term ctxt') [
        "?x \<equiv> ?z \<Longrightarrow> ?y \<equiv> (0 :: nat) \<Longrightarrow> ?x + ?y \<equiv> ?z",
        "?x \<equiv> (?z + 0) \<Longrightarrow> ?y \<equiv> (0 :: nat) \<Longrightarrow> ?x + ?y \<equiv> ?z"
      ]
    val tests = map (apply2 (Syntax.read_term ctxt')) [
      ("(?x + 0) + 0 :: nat", "1 :: nat")
    ]
    fun check_num_success num_success hints name unif ctxt r =
      let val ctxt' = add_hints hints ctxt
      in
        check_list tests ("multiple successful hints unit tests for " ^ name)
          (SpecCheck_Property.prop (fn tp =>
            (UUtil.empty_envir tp
            |> unif ctxt' tp
            |> Seq.list_of
            |> length)
            = num_success))
          ctxt'
        |> K r
      end
  in
    Lecker.test_group ctxt' r [
      check_num_success 0 [] "unify" P.unify,
      check_num_success 0 [] "unify_hints without hints" P.unify_hints,
      check_num_success 3 hints "unify_hints with hints" P.unify_hints
    ]
  end

fun unit_tests_hints ctxt r =
  Lecker.test_group ctxt r [
    unit_tests_hints_non_recursive,
    unit_tests_multiple_matching_hints,
    unit_tests_hints_try_symmetric,
    unit_tests_hints_recursive,
    unit_tests_multiple_successful_hints
  ]

fun unit_tests ctxt r =
  Lecker.test_group ctxt r [
    unit_tests_unifiable,
    unit_tests_non_unifiable,
    unit_tests_hints
  ]

fun tests ctxt r =
  Lecker.test_group ctxt r [
    unit_tests,
    generated_tests
  ]

end
