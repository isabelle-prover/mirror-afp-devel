signature MLUNTA_TEST = sig
  val assert_sat: 'a Property.result -> bool
  val assert_unsat: 'a Property.result -> bool
  val gen: string -> string list ->
           (unit Property.result -> bool) list ->
           (string -> SMLUnit.test)
end
structure MLuntaTest : MLUNTA_TEST = struct
open SMLUnit
fun assert_sat r =
    case r of
        Property.Satisfied _ => true
      | _ => false
fun assert_unsat r = (not o assert_sat) r
fun setup names expected results =
    if length names = length expected andalso
       length names = length results then
      map2 (curry (fn (f, r) => f r)) expected results
           |> (curry (op ~~)) names
           |> map (fn (name, r) => name >+ (assert_true r))
    else Exn.error
             ("The tests results names and expected results cannot be"
              ^ " zipped diff lengths")

fun tests results name = name >++ results

fun gen root files expected =
    let
      val test_paths = List.map (fn s => root ^ s ^ ".muntax") files
      val filehandles = List.map (fn path => TextIO.openIn path) test_paths
      val test_handles = List.map json_file_to_string test_paths
      val files_right = List.all (fn "" => false | _ => true) test_handles
      val traces = map Mlunta.just_check test_handles
      val res_list = map Either.the_right traces
      val test_res = setup files expected res_list
    in
      tests test_res
    end
end
(* XXX: Remove this downwards? *)
(* structure MluntaTest :> TESTSUITE = struct *)
(* open MLuntaTest_ *)
(* val root = "test/resources/" *)
(* val files = ["simple", "fddi", "light_switch", "leadsto1", *)
(*                   "leadsto2", "leadsto3", "leadsto4", "leadsto5", *)
(*                   "leadsto6"] *)

(* val expected = [assert_sat, assert_unsat, assert_sat, assert_unsat, *)
(*                 assert_sat, assert_sat, assert_sat, assert_unsat, assert_sat] *)

(* fun check name = *)
(*     SMLUnit.run_test ((gen root files expected) name) *)
(* end *)
