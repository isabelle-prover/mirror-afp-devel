(* tests for creating the indexDicts and maps *)
(* XXX: Add test for loc_f location renaming and label_f renaming, formula renaming *)
(* XXX: Maybe also a small module test *)

structure RenamingTest : TESTSUITE = struct
open Renaming
open Either
open Error
open CompilationError
open NamingError
open SMLUnit


fun sset dest ix_dict tab =
    IndexDict.foldli (fn (ix,k,acc) => (k, ix) :: acc) [] ix_dict
    |> rev
    |> (fn ls => ls = dest tab)

fun strmap_cmp ix_dict tab = sset Symtab.dest ix_dict tab

fun intmap_cmp ix_dict tab = sset Inttab.dest ix_dict tab

(*
Corner cases for duplicates are not needed since they are checked in
check_dups in CompileBexp Module, Todo for Testing already exists
*)

(*
XXX: Test such that sizes and indices not neg
create s.t. all k in strmap 0 >= size arr
But actually this property should be covered by the fact that
Forall (k,v) : map. fin       d v dict = k
*)
fun mk_test name input f expected = name >+ assert_equal (f input) expected
(* Tests for strmap *)
val test_val1 = create_renaming_symtab ["x", "y"]
val test_empty_list = create_renaming_symtab []

val test_create_same =
    mk_test "eq create strmap"
                           test_val1
                           (fn (ix, map) => strmap_cmp ix map)
                           true
val test_create_empty =
        mk_test "empty create strmap"
                           test_empty_list
                           (fn (ix, map) => strmap_cmp ix map)
                           true

val tests_create_strmap = [test_create_empty, test_create_same]

(* Tests for intmap *)
val test_valint1 = create_renaming_inttab [4, 5, 6,7]
val test_empty_intlist = create_renaming_inttab []

val test_create_same_intmap =
    mk_test "eq create intmap"
                           test_valint1
                           (fn (ix, map) => intmap_cmp ix map)
                           true
val test_create_empty_intmap =
        mk_test "empty create strmap"
                           test_empty_intlist
                           (fn (ix, map) => intmap_cmp ix map)
                           true

val tests_create_intmap = [test_create_empty_intmap, test_create_same_intmap]

(* Test renaming updates *)
val upd_testf =
    Renaming.update
      (fn "a" => Either.succeed 1
      | "b" => Either.succeed 3
      | x => x |> unknown_var |> naming |> lift_comp_err)
val test_reset =
    mk_test "UpdatingRight" (Syntax.Reset ("b",1))
                           (the_right o upd_testf) (Syntax.Reset (3, 1))

val test_resetx =
    mk_test "UpdatingX" (Syntax.Reset ("x",1))
                           (the_left o upd_testf)
                           (unknown_var "x" |> naming |> comp_err |> single )

val tests_update = [test_reset, test_resetx]


fun tests name =
    name >++ (tests_create_intmap @ tests_create_strmap @ tests_update)
(* XXX: Check renaming constr and node?*)
fun check name =
    run_test (tests name)

end
