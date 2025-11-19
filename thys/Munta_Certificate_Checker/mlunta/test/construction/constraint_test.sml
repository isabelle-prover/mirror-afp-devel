structure ConstraintTest : TESTSUITE = struct
open Either
open CompilationError
open Error
open SMLUnit
open Syntax
fun mk_test name input f expected = name >+ assert_equal (f input) expected

val test_lt_single =
    mk_test "LtSingle" [Constraint.Lt (Difference.Single 1, 3)]
            ClockConstraint.from_guard [ClockConstraint.Lt (1, 0, 3)]

val test_lt_diff =
    mk_test "LtDiff" [Constraint.Lt (Difference.Diff(2, 1), 3)]
            ClockConstraint.from_guard [ClockConstraint.Lt (2, 1, 3)]

fun tests name = name >++ [test_lt_single, test_lt_diff]

fun check name =
    run_test (tests name)
end
