(* Title: CTR/Tests/CTR_TEST_PROCESS_CTR_RELATOR.ML
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins
*)

signature CTR_TEST_PROCESS_CTR_RELATOR =
sig
type process_ctr_relator_in_type
val test_suite : Proof.context -> unit -> unit
end;

structure ctr_test_process_ctr_relator : CTR_TEST_PROCESS_CTR_RELATOR =
struct




(**** Background ****)

open SpecCheck;
structure Prop = SpecCheck_Property;
structure Show = SpecCheck_Show;




(**** Auxiliary ****)

fun mk_msg_ctr_relator msg = "ctr_relator: " ^ msg;



(*** Data ***)

type process_ctr_relator_in_type = string * Proof.context;




(**** Visualization ****)

(*FIXME: complete the migration to SpecCheck.Show*)

fun show_ctr_relator_in (process_ctr_relator_in : process_ctr_relator_in_type) = 
  let
    val (c, _) = process_ctr_relator_in
    val name_c = "constant name: " ^ c
    val ctxt_c = "lthy: unknown context" 
    val out_c = [name_c, ctxt_c] |> String.concatWith "\n"
  in Pretty.str out_c end;




(**** Tests ****)



(*** Wrapper ***)

fun process_ctr_relator ((c, ctxt) : process_ctr_relator_in_type) = 
  CTR_Relators.process_ctr_relator c ctxt;



(*** Exceptions ***)

fun test_exc_template ctxt c err_msg_end_c test_name_c = 
  let
    val args = (c, ctxt)
    val err_msg = mk_msg_ctr_relator err_msg_end_c
    val exn_prop = Prop.expect_failure (ERROR err_msg) process_ctr_relator
  in 
    check_list_unit
      show_ctr_relator_in
      [args]
      test_name_c
      exn_prop
  end;

fun test_exc_not_const ctxt _ = test_exc_template 
  ctxt "a + b" "the input must be a constant term" "not a constant";

fun test_exc_not_body_bool ctxt _ = test_exc_template 
  ctxt 
  "Cons" 
  "the body of the type of the input must be bool" 
  "not bool body";

fun test_exc_not_binders_2 ctxt _ = test_exc_template 
  ctxt 
  "Ex" 
  "the type of the input must have more than two binders" 
  "not two binders";

fun test_exc_not_binders_binrelT ctxt _ = test_exc_template 
  ctxt 
  "not_binders_binrelT" 
  (
    "all of the binders associated with the type of the input" ^
    "except the last two must be the binary relation types"
  ) 
  "not binary relation types";

fun test_exc_no_dup_binrelT ctxt _ = test_exc_template 
  ctxt 
  "no_dup_binrelT"
  (
    "the types of the binders of the binary relations associated " ^
    "with the type of the input must have no duplicates"
  ) 
  "no duplicates in the binary relation types";

fun test_exc_not_binders_binrelT_ftv_stv ctxt _ = test_exc_template 
  ctxt 
  "not_binders_binrelT_ftv_stv"
  (
    "the types of the binders of the binary relation types associated " ^
    "with the input type must be either free type variables or " ^
    "schematic type variables"
  ) 
  "not binrel type ftv or stv";

fun test_exc_not_type_constructor_lhs ctxt _ = test_exc_template 
  ctxt 
  "not_type_constructor_lhs"
  (
    "the last two binders of the input type must be " ^
    "the results of an application of a type constructor"
  ) 
  "not type constructor lhs";

fun test_exc_not_type_constructor_rhs ctxt _ = test_exc_template 
  ctxt 
  "not_type_constructor_rhs"
  (
    "the last two binders of the input type must be " ^
    "the results of an application of a type constructor"
  ) 
  "not type constructor rhs";

fun test_exc_not_identical_type_constructors_lhs ctxt _ = test_exc_template 
  ctxt 
  "not_identical_type_constructors_lhs"
  (
    "the sequences of the input types to the type constructors that are " ^
    "associated with the last two binders of the input type must be " ^
    "identical to the sequences of the types formed by concatenating the " ^
    "type variables associated with the left hand side and the right " ^
    "hand side of the binary relation types, respectively"
  ) 
  "not identical type constructors lhs";

fun test_exc_not_identical_type_constructors_rhs ctxt _ = test_exc_template 
  ctxt 
  "not_identical_type_constructors_rhs"
  (
    "the sequences of the input types to the type constructors that are " ^
    "associated with the last two binders of the input type must be " ^
    "identical to the sequences of the types formed by concatenating the " ^
    "type variables associated with the left hand side and the right " ^
    "hand side of the binary relation types, respectively"
  ) 
  "not identical type constructors rhs";




(**** Test Suite ****)

fun test_suite ctxt s = 
  [
    test_exc_not_const,
    test_exc_not_body_bool,
    test_exc_not_binders_2,
    test_exc_not_binders_binrelT,
    test_exc_no_dup_binrelT,
    test_exc_not_binders_binrelT_ftv_stv,
    test_exc_not_type_constructor_lhs,
    test_exc_not_type_constructor_rhs,
    test_exc_not_identical_type_constructors_lhs,
    test_exc_not_identical_type_constructors_rhs
  ]
  |> map (fn f => f ctxt s) 
  |> Lecker.test_group ctxt s;

end;