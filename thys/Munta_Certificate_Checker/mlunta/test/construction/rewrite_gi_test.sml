(* XXX: Test check_dups *)
(* XXX: Tests for True *)
(* XXX: Test for whole edges, nodes, automata, network *)
structure RewriteGITest : TESTSUITE = struct

open Either

open NamingError
open LangError
open CompilationError

open Error
open RewriteBexps
open SMLUnit
open Syntax.Constraint
open Syntax.Difference
local
  open Syntax.Guard
in
(* Tests for compiling the guards *)
fun comp_g1 e = compile_guards ["x", "y"] ["a", "b"] e
fun guard_oracle ones diags vars = ((ones, diags), vars) |> succeed

fun lift_constr_err err = err |> constr_err |> lift_comp_err

fun test_g name t res = name >+ assert_equal (comp_g1 t) res
val test_g1 = test_g "Guard1"
                     (And (Constr (Lt (Diff ("x", "y"), 3)),
                           And (Constr (Gt (Single "a",4)),
                                Constr (Lt (Single "x", 5)))))
                     (guard_oracle [Lt (Single "x", 5)]
                                   [Lt (Diff ("x", "y"), 3)]
                                   [Constr (Gt (Single "a", 4))])

val test_g2 = test_g "GuardVCexp" (And (Constr (Lt (Diff ("a", "y"), 3)),
                                          Constr (Gt (Single "a",4))))
                   (clock_and_var "y" "a" |> lift_constr_err)

val test_g3 = test_g "GuardUnknownId" (Constr (Lt (Diff ("c", "c"), 4)))
                     (Syntax.Difference.to_string (Diff ("c", "c"))
                     |> unknown_var
                     |> lift_naming_err)

val test_g_disj = test_g "Guard Disj Right"
                             (And
                                 (Or (Constr (Lt (Single "a", 2)),
                                      Constr (Gt (Diff ("b", "a"), 4)))
                                 , Constr (Lt (Diff ("x", "y"), 7)))
                             )
                             (
                               guard_oracle
                                   []
                                   [Lt (Diff ("x", "y"), 7)]
                                   [Or (Constr (Lt (Single "a", 2)),
                                      Constr (Gt (Diff ("b", "a"), 4)))]
                             )

val wrong_disj = And
                     (Or (Constr (Lt (Single "x", 2)),
                          Constr (Gt (Diff ("x", "y"), 4)))
                     , Constr (Lt (Diff ("x", "y"), 7)))
local
  open Syntax
in
val guard_str = Guard.to_string wrong_disj
val single_str =  Constraint.to_string Difference.to_string (Lt (Single "x", 2))
val diff_str = Constraint.to_string Difference.to_string (Gt (Diff ("x", "y"), 4))
val error_f = (constr_err #> comp_err) oo disj
val errors = error_f guard_str single_str :: error_f guard_str diff_str :: []
end
val test_g_disj_fail = test_g "Guard Disj Wrong" wrong_disj
                              (Either.fail errors)
end
val test_guards = "Guards" >++ [
    test_g1, test_g2, test_g_disj, test_g_disj_fail
]


(* Testing compiling invars *)
fun comp_invar e = compile_invariant ["x", "y"] ["a", "b"] e
fun test_i name t res = name >+ assert_equal (comp_invar t) res
local
  open Syntax.Invariant
in
val test_i1 = test_i "Invar1" (And (Constr (Lt ("y", 3)), Constr (Lt ("x", 5))))
           (Right ([(Lt ("x", 5)), (Lt ("y", 3))]))
val invar_success = [test_i1]

val test_i_single_vexp = test_i "InvarSingleVexp"
                                                (And (Constr (Lt ("a", 1)),
                                      Constr (Le ("x", 5))))
                                 (("a" |> var_invar |> lift_constr_err))
end
val invar_fail =
    [test_i_single_vexp]

val test_invars = "Invariants" >++ (invar_success @ invar_fail)
open Syntax
(* Testing compile updates *)
fun comp_upd e = compile_updates ["x", "y"] ["a", "b"] e
fun test_upd name t res = name >+ assert_equal (comp_upd t) res

(* Success tests *)
val test_reset_clck = test_upd "ResetClock" [Reset ("x", 3)] (Right ([Reset ("x",3)], []))
val test_reset_var = test_upd "ResetVar" [Reset ("b", 3)] (Right ([], [Reset ("b",3)]))
val test_reset1 = test_upd "ResetBoth"
                         [Reset ("b", 3), Reset ("x",2), Reset ("a",1), Reset ("y", 3)]
                         (Right ([Reset ("x", 2), Reset ("y", 3)],
                                 [Reset ("b",3), Reset ("a",1)]))
val tests_reset_success = [test_reset_clck, test_reset_var, test_reset1]
val tests_reset_fail = []
val tests_reset = "Resets" >++ (tests_reset_success @ tests_reset_fail)

fun tests name = name >++ [test_guards, test_invars, tests_reset]
fun check name =
    run_test (tests name)
end
