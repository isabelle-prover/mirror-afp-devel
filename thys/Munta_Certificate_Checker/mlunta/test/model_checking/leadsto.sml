structure LeadstoTest :> TESTSUITE = struct
open MLuntaTest
val root = "test/resources/"
val files = [(* "leadsto1", *) "leadsto2", "leadsto3", (* "leadsto4", *) "leadsto5",
             "leadsto6"]

val expected = [(* assert_unsat, *) assert_sat, assert_sat, (* assert_sat, *)
                assert_unsat, assert_sat]

fun check name = let
  val test_setup = gen root files expected name
in
  SMLUnit.run_test test_setup
end
end
