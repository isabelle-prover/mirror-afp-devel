structure ReachabilityTest :> TESTSUITE = struct
open MLuntaTest
val root = "test/resources/"
val files = ["simple", "fddi"]
val expected = [assert_sat, assert_unsat]

fun check name = let
  val setup_tests = gen root files expected name
in
  SMLUnit.run_test setup_tests
end
end
