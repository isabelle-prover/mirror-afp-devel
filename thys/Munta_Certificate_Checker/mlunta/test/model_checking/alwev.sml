structure AlwaysEventuallyTest :> TESTSUITE = struct
open MLuntaTest
val root = "test/resources/"
val files = ["light_switch"]
val expected = [assert_sat]

fun check name = let
  val test_setup = gen root files expected name
in
  SMLUnit.run_test test_setup
end
end
