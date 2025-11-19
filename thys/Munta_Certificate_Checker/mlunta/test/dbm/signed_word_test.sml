functor TestWord(W : SIGNED_WORD) :> TESTSUITE =
struct
open SMLUnit
open W
fun test name is expected =
    let
      fun eq x y = x == y
    in name >+ assert_cmp eq is expected end

fun test_cmp name cmp input expected = name >+ assert_equal (cmp input) expected

val add_testex1 =
    test "add" ((W.from_int ~2) |+| (W.from_int 13)) (W.from_int 11)

val check_neg_test = test_cmp "check neg" W.check_neg (W.from_int (~2)) true

val small_test = test_cmp "smaller" W.|<| (W.from_int (~2), W.from_int 2) true

(* val great_test = test_cmp "greater" W.|>| (W.from_int (~2), W.from_int 2) false *)

val great_eq_test =
    test_cmp "greater_eq" W.|>=| (W.from_int (~1), W.from_int ~1) true

val small_eq_test =
    test_cmp "smaller_eq" W.|<=| (W.from_int (~1), W.from_int ~1) true

val max_test = test "max" (W.max (W.from_int ~2) (W.from_int 1))
                    (W.from_int 1)

val min_test = test "min" (W.min (W.from_int ~2) (W.from_int 1))
                    (W.from_int ~2)

val and_test = test "and" (W.from_int 5 |&| W.from_int 3) (W.from_int 1)

val or_test = test "or" (W.from_int 5 \/ W.from_int 3) (W.from_int 7)

val neg_test = test "neg" (W.|~| (W.from_int 3)) (W.from_int (~ 3))

val mod2_test = test "mod2" (W.mod2 (W.from_int 3)) (W.from_int 1)

val add_of_test =
    "Detecting Overflow" >+
                         assert_exception (W.maximum <\ W.|+|) W.Overflow W.one

val add_uf_test =
    "Detecting Underflow" >+
                          assert_exception
                          (W.minimum <\ W.|+|) W.Overflow (W.|~| W.one)

fun tests name =
    name >++
    [
      add_testex1, check_neg_test, small_test,
      great_eq_test, small_eq_test, max_test,
      min_test, and_test, or_test, mod2_test, add_of_test, add_uf_test
    ]

fun check name =
    run_test (tests name)

end

structure TestInt8 :> TESTSUITE =
struct
open SMLUnit

structure Test_funct = TestWord(Int8);

val from_int_test1 =
    "from_int pos Overflow" >+ assert_exception Int8.from_int Int8.Overflow 1000

val from_int_test2 =
    "from_int neg Overflow" >+ assert_exception Int8.from_int Int8.Overflow (~130)
      (* UnitTest.expect_exception Int8.from_int (~130) "from_int neg Overflow" *)



fun tests name = name >++ [from_int_test1, from_int_test2]


fun check name =
    (
      Test_funct.check name;
      run_test (tests "Int8 from_int")
    )
end

structure TestInt32 :>TESTSUITE =
struct
structure Test_funct = TestWord(Int32);
open SMLUnit

val from_int_test1 =
    "from_int pos Overflow" >+ assert_exception Int32.from_int
                           Int32.Overflow 100000000000

val from_int_test2 =
    "from_int neg Overflow" >+ assert_exception Int32.from_int
                           Int32.Overflow (~100000000000)

fun tests name = name >++ [from_int_test1, from_int_test2]

fun check name =
    (
      Test_funct.check name;
      run_test (tests "Int32 from_int")
    )

end

structure TestInt64 = TestWord(Int64);
