(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver881

imports "AutoCorres2.CTranslation"

begin

install_C_file "jiraver881.c"

context jiraver881_simpl 
begin

(* note that x is assigned directly from f(),
   but that compound lvars and y (different notional type) are
   assigned via explicit statements. *)

thm baseline1_body_def
thm baseline2_body_def

thm test1_body_def
thm test2_body_def
thm test3_body_def
thm test4_body_def
thm test5_body_def

(* We expect the call to store the int retvals into ret__int and similar.
   To test this, we extract the update to the return variable and check. *)

ML \<open>

fun get_returns (t as (t1 $ t2)) = 
      (case strip_comb t of 
        (Const (c,_), [_,_,_,_,r]) => if c = @{const_name call_exn} then [r] else get_returns t1 @ get_returns t2
      | _ => get_returns t1 @ get_returns t2)
  | get_returns t = []

fun get_updates (t as (t1 $ t2)) = 
      (case strip_comb t of 
        (Const (c,_), (Const(n,_)::_)) => if c = @{const_name cupdate} then [Long_Name.base_name n] else get_updates t1 @ get_updates t2
      | _ => get_updates t1 @ get_updates t2)
  | get_updates (Abs (_, _ , t)) = get_updates t 
  | get_updates t = []

fun check_ret func var =
let 
  val fn_def = Proof_Context.get_thm @{context} (func ^ "_body_def")
  val upds = fn_def |> term_of_thm |> get_returns |> map get_updates |> flat
in
  assert
    (upds = [var])
    ("assert failed: jiraver881 test for " ^ func ^ " call" ^ ".\n " ^
      "upds: " ^ @{make_string} upds ^ " are not [" ^ var ^ "]")
end

\<close>
(* Should always work, since these are trivial assignments *)
ML \<open>
check_ret "baseline1" "x_'";
check_ret "baseline2" "ret'_'";
\<close>

(* Actual tests *)
ML \<open>
check_ret "test1" "ret'int'1_'";
check_ret "test2" "ret'int'1_'";
check_ret "test3" "ret'int'1_'";
check_ret "test4" "ret'int'1_'";
check_ret "test5" "ret'int'1_'";
\<close>

end

end
