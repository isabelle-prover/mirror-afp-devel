(* Let there be TEsts for the DBM Entry module *)
functor TestDBMEntry(E : DBM_ENTRY) :> TESTSUITE =
struct
open SMLUnit

fun test name is expected =
    let
      fun eq x y = E.== (x, y)
    in name >+ assert_cmp eq is expected
    end

val add_test_inf = test "add_encoded inf" (E.add E.inf E.zero) E.inf

val add_1set_test = test "1 lsb set addition"
                                 (E.add (E.==< 3)
                                (E.=< 2))
                         (E.=< 5)

val add_noneset_test = test "No lsb set addition"
                            (E.add (E.=< 6) (E.=< 2))
                            (E.=< 8)

val add_bothset_test = test "both lsb set addition"
                            (E.add (E.==< 3) (E.==< 5))
                            (E.==< 8)
val add_zero_test = test "zero"
                             (E.add (E.=< ~7) (E.==< 7))
                             (E.=< 0)
val add_zero_test2 = test "zero2"
                             (E.add (E.==< ~7) (E.==< 7))
                             (E.zero)
val add_neg_test = test "neg1"
                             (E.add (E.=< ~8) (E.=< 4))
                             (E.=< ~4)
val add_neg_test2 = test "neg2"
                             (E.add (E.=< ~8) (E.==< 5))
                             (E.=< ~3)
val add_neg_test3 = test "neg3"
                             (E.add (E.==< ~8) (E.==< 1))
                             (E.==< ~7)

(* XXX: add tests for comparing*)

fun tests name = name >++
                      [
                        add_test_inf, add_1set_test, add_noneset_test,
                        add_bothset_test, add_zero_test, add_zero_test2, add_neg_test,
                        add_neg_test2, add_neg_test3
                      ](* ,  add_test_of, add_test_uf] *)

fun check name =
    run_test (tests name)

end

structure TestEntry64 = TestDBMEntry(Entry64Bit);
structure TestEntry32 = TestDBMEntry(Entry32Bit);
structure TestEntry8 = TestDBMEntry(Entry8Bit);
structure TestEntryInt = TestDBMEntry(Entry)
