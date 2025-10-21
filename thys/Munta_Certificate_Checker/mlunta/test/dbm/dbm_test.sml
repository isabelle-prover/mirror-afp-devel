(* Tests for the DBMs here we have the LinearLayout right now *)
(* XXX: Test diff constraint normalization stuff , And, copy_dbm, satisfied, empty*)
functor LinDBMUintTester (D : DBM) :> TESTSUITE =
struct
open SMLUnit

val test_clocks = 2

fun from_int_list ls =
    ls
    |> List.map (fn l => List.map (fn x => IntRep.LT x) l)
    |> D.from_int_rep_list

fun test eq_f name f input expected =
    let
            val is = f input
    in
        name >+ assert_cmp_res
             eq_f is expected (D.to_string is) (D.to_string expected)
    end

val eqtest_dbm = test D.equal

val close_test =
    let
        val input = from_int_list
                        [
                          [3,2,1],
                          [3,20,~1],
                          [1,0,13]
                        ]
        val expected = from_int_list
                           [
                             [2,1,0],
                             [0, ~1,~2],
                             [0,~1,~2]
                           ]
    in
          eqtest_dbm "close" D.close input expected
    end

open IntRep

val up_test =
    let
        val input =  from_int_list
                         [
                           [3,2,1],
                           [3,20,~1],
                           [1,0,13]
                         ]
        val expected = D.from_int_rep_list
                         [
                           [ (LT 3),  (LT 2), (LT 1)],
                           [Inf,  (LT 20),  (LT (~1))],
                           [Inf,  (LT 0),  (LT 13)]
                         ]
    in eqtest_dbm "up" D.up input expected
    end

val free_test =
    let
        val input =  from_int_list
                     [
                       [3,2,1],
                       [3,20,~3],
                       [1, 0, ~2]
                     ]
        val expected = D.from_int_rep_list
                         [
                           [ (LT 3),  (LT 3),  (LT 1)],
                           [Inf,  (LT 20), Inf],
                           [ (LT 1),  (LT 1),  (LT (~ 2))]
                         ]
    in eqtest_dbm "free" (D.free 1) input expected
    end

val reset_test =
    let
        val input =  from_int_list
                     [
                       [3,2,1],
                       [3,20,~3],
                       [1, 0, ~2]
                     ]
        val expected = from_int_list
                     [
                       [3, ~7, 1],
                       [13, 3, 11],
                       [1, ~9, ~2]
                     ]
    in
        eqtest_dbm "reset"
                   (D.reset 1 10) input expected
    end

val copy_clock_test =
    let
        val input = from_int_list
                    [
                      [3,2,1],
                      [3,20,~3],
                      [1, 0, ~2]
                    ]
        open IntRep
        val expected = D.from_int_rep_list
                     [
                       map LT [3,1,1],
                       [LT 1, LT 20,LTE 0],
                       [LT 1,LTE 0,LT ~2]
                     ]
    in eqtest_dbm "copy_clock"
                  (D.copy_clock 1 2) input expected
    end

val shift_test =
    let
        val input = from_int_list
                    [
                      [3,2,1],
                      [3,20,~3],
                      [1, 0, ~2]
                    ]
        val expected = from_int_list
                     [
                       [3, ~8, 1],
                       [13, 20, 7],
                       [1, ~10, ~2]
                     ]
    in eqtest_dbm "shift"
                  (D.shift 1 10) input expected
    end

fun test_subsumption l r expected name =
    let
            fun bool_tup_str (x,y) =
            "(" ^ (Bool.toString x) ^ ", " ^ (Bool.toString y) ^ ")"
            val test_case = (D.subsumption l r, D.subsumption r l)
            val res = test_case = expected
            val is = bool_tup_str test_case
            val expected_str = bool_tup_str expected
    in
        name >+ assert_equal test_case expected
    end

val subsumption_test1 =
    let
            val input = from_int_list
                                [
                                  [3,2,1],
                                  [3,20,~3],
                                  [1, 0, ~2]
                                ]
            val expected_res = (true, true)
    in
        test_subsumption input input (true, true) "subsumption test l = r"
    end

fun tests name =
    name >++
    [
      close_test,up_test, free_test, reset_test, copy_clock_test,
      shift_test, subsumption_test1
    ]

fun check name =
    run_test (tests name)

end

structure TestLnDBM8 = LinDBMUintTester(LnDBM8Bit)
structure TestLnDBM32 = LinDBMUintTester(LnDBM32Bit)
structure TestLnDBM64 = LinDBMUintTester(LnDBM64Bit)
structure TestLnDBMIntRep = LinDBMUintTester(LnDBMInt)
