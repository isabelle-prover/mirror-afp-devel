structure BexpParserTest : TESTSUITE = struct
structure C = Syntax.Constraint
open Syntax
open Difference
open BexpParser
open Either
open SMLUnit

fun create_testable (name, input, f, expected) =
    name >+ (assert_equal (f input |> mapL (K ())) expected)
(* XXX: Add tests for:  *)
(*    + failing updates *)
(*    + variable scan *)
local
  open Formula
in

val tests_input_bexp = [
    ("Bexp 1", "a < 3 && b >= 2 || c <= 4", bexp,
     Right ( Or (
               And (Pred (C.Lt(Single "a", 3)),
                    Pred(C.Ge(Single "b", 2))),
               Pred(C.Le(Single "c", 4))))),
    ("Bexp 2", "a < 3 && b >= 2 || ~ c <= 4", bexp,
     Right ( Or (
               And (Pred (C.Lt(Single "a", 3)),
                    Pred (C.Ge(Single "b", 2))),
               Not (Pred (C.Le (Single "c", 4)))))),
    ("Bexp 3", "a < 3 && b >= 2 || ~ (c <= 4)", bexp,
     Right ( Or (
               And (Pred (C.Lt(Single "a", 3)),
                    Pred (C.Ge(Single "b", 2))),
               Not (Pred (C.Le(Single "c", 4)))))),
    ("Bexp 4", "a < 3 -> (b >= 2 || ~ (c <= 4))", bexp,
     Right ( Impl
                 (Pred (C.Lt (Single "a", 3)),
                  Or (Pred (C.Ge(Single "b", 2)),
                      Not (Pred (C.Le(Single "c", 4))))))),
    ("Bexp 5", "a << 3", bexp, Left ()),
    ("Bexp 6", "a < 3", bexp,  Right ( Pred (C.Lt (Single "a", 3)))),
    ("Bexp 7", "a < 3 && b >= 2", bexp,
     Right ( And
                 (Pred (C.Lt(Single "a", 3)),
                  Pred (C.Ge(Single "b", 2))))),
    ("Bexp 81", "(_b = 123456789 && a12 > 0) && A_B3 <= 1", bexp,
     Right ( And
                 (And(Pred (C.Eq(Single "_b", 123456789)),
                      Pred (C.Gt(Single "a12", 0))),
                  Pred (C.Le(Single "A_B3", 1))))),
    ("Bexp 82", "_b = 123456789 && (A._a1 && A_B3 <= 1)", bexp,
     Right ( And (Pred (C.Eq(Single "_b", 123456789)),
                  And(Loc("A", "_a1"), Pred (C.Le(Single "A_B3", 1)))))),
    ("Bexp 8", "_b = 123456789 && a12 > 0 && A_B3 <= 1", bexp,
     Right ( And
                 (Pred (C.Eq (Single "_b", 123456789)),
                  And
                      (Pred (C.Gt(Single "a12", 0)),
                       Pred (C.Le(Single "A_B3", 1)))))),
    ("Bexp 9", "x - y < 7", bexp, Right ( Pred (C.Lt (Diff ("x", "y"), 7)))),
    ("Bexp 10", "a < 3 && a - b >= 2 || c <= 4", bexp,
     Right (
       Or
           (And (Pred (C.Lt (Single "a", 3)),
                 Pred (C.Ge (Diff ("a", "b"), 2))),
       Pred (C.Le(Single "c", 4))))),
    ("Bexp 11", "", bexp, Right (True))
]
end

val tests_input_upd = [
  ("upd empty", "", update, Left ()),
  ("update reset", "x := 2", update, Reset ("x", 2) |> succeed),
  ("update copy", "x := y", update, Copy ("x", "y") |> succeed),
  ("update shift", "x := x + 3", update, Shift ("x", 3) |> succeed)
  ]

val tests_input_actions = [
  ("Internal Empty", "", action, Internal "" |> succeed),
  ("Internal NonEmpty", "hi", action, Internal "hi" |> succeed),
  ("In", "hi?", action, In "hi" |> succeed),
  ("Out", "hi!", action, Out "hi" |> succeed),
  ("In and Out", "hi?!", action, Left ()),
  ("Out and In", "hi!?", action, Left ()),
  ("In and In", "hi??", action, Left ())
  ]

local
  open Formula
in
val tests_input_formula = [
  ("Formula1", "E<> TA1.C", formula, Right (Ex (Loc ("TA1", "C")))),
  ("Formula2", "E<> ((ST1.z_sync || ST1.z_async || ST1.y_sync || ST1.y_async)" ^
               "  && (ST2.z_sync || ST2.z_async || ST2.y_sync || ST2.y_async) )",
   formula, Right (Ex (And (Or(Loc ("ST1", "z_sync") ,
                               Or (Loc ("ST1", "z_async"),
                                   Or (Loc ("ST1", "y_sync"),
                                       Loc ("ST1", "y_async")))),
                            Or( Loc ("ST2", "z_sync") ,
                                Or (Loc ("ST2", "z_async"),
                                    Or(Loc ("ST2", "y_sync"),
                                       Loc ("ST2", "y_async")))))))),

  ("FormulaLeadsto1", "(ST1.z_sync || ST1.z_async) --> ST1.z_sync", formula,
   Right (Leadsto (Or (Loc ("ST1", "z_sync"), Loc ("ST1", "z_async")),
                   Loc ("ST1", "z_sync"))))
      (* XXX: More leads to tests *)
  ]
end

val tests_bexp =  "BEXPS" >++ List.map create_testable tests_input_bexp
val tests_upd = "Upd" >++ List.map create_testable tests_input_upd
val tests_action = "Actions" >++ List.map create_testable tests_input_actions

val tests_formula = "Formula" >++ List.map create_testable tests_input_formula

fun tests name = name >++ [tests_bexp, tests_upd, tests_formula, tests_action]
fun check name =
      run_test (tests name)

end
