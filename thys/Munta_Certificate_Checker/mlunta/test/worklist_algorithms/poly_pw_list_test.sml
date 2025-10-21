structure PolyPWListTest :> TESTSUITE = struct
open SMLUnit
val ssetp_test = curry (op <=)
val insert' = PolyPWList.insert (fn (42, _) => true | _ => false) ssetp_test
val start_pw =
    PolyPWList.make (fn k => k mod 32) (op =) 32
    |> flip insert' (0, 3)
    |> fst;
val w_pair = apply2 Unsynchronized.!

val test_nitems_init = "No. items in union at beginning" >+
                        assert_equal (PolyPWList.n_buckets start_pw)
                        (PolyPWList.items_pw start_pw |> List.length)

val test_items_init = "items in union and waiting queue at beginning" >+
                            assert_equal
                            (PolyPWList.items_pw start_pw |> hd |> apsnd hd)
                            (PolyPWList.get start_pw |> the |> fst |> w_pair)

val same_bucket = "Insert into same bucket" >+
                          assert_equal
                          (insert' start_pw (32, 0)
                          |> fst
                          |> PolyPWList.items_pw)
                          ([(0, [3]), (32, [0])])

val two_inserts = "After 2 inserts size" >+
                   assert_equal
                   ((PolyPWList.n_buckets start_pw) + 2)
                   (
                     insert' start_pw (1, 3)
                     |> fst
                     |> flip insert' (30, 2)
                     |> fst
                     |> PolyPWList.n_buckets
                   )


val two_inserts_notf = "Check for not final stuff" >+
                              assert_equal
                              false
                              (
                                    insert' start_pw (1, 3)
                                    |> snd
                              )

(* XXX: More elaborate tests: *)
(* XXX: Tests for not ssetp: *)
(* XXX: Test for ssetp *)
(* XXX: Test for get *)
fun tests name =
    name >++
         [
           test_nitems_init, test_items_init, two_inserts,
           two_inserts_notf, same_bucket
         ]

fun check name =
    run_test (tests name)

end
