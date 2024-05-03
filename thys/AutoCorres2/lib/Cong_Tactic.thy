(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *
 *)

theory Cong_Tactic
  imports
    "Main"
    "HOL-Eisbach.Eisbach_Tools"

begin

text \<open> Simple congruence prover

Replaces a goal of the shape:

  \<^term>\<open>f x (g y) (\<lambda>x. x + 1) = f x' (i y') (\<lambda>z. z + Suc 0)\<close>

by

  \<^term>\<open>x = x'\<close>
  \<^term>\<open>g y = i y'\<close>
  \<^term>\<open>1 = Suc 0\<close>

The tactic essentially applies @{thm cong}, but using first-order matching.

\<close>

ML \<open>

fun fo_cong_tac ctxt = CSUBGOAL (fn (cgoal, i) =>
  let
    val goal = Thm.term_of cgoal;
  in
    (case Logic.strip_assums_concl goal of
      _ $ (_ $ t $ s) =>
        let
          val (f, xs) = strip_comb t
          val (g, ys) = strip_comb s
        in
          if f aconv g andalso length xs = length ys
            then REPEAT_DETERM_N (length xs) (cong_tac ctxt i) 
                 THEN resolve_tac ctxt [@{thm refl}] i
            else no_tac
        end
    | _ => no_tac)
  end);


fun abs_cong_tac ctxt = CSUBGOAL (fn (cgoal, i) =>
  let
    val goal = Thm.term_of cgoal;
  in
    (case Logic.strip_assums_concl goal of
      _ $ (_ $ Abs _ $ Abs _) => resolve_tac ctxt [@{thm ext}] i
    | _ => no_tac)
  end);

\<close>

method_setup app_cong =
  \<open>Scan.succeed (fn ctxt => Method.SIMPLE_METHOD' (fo_cong_tac ctxt))\<close>
  "congruence method"

method_setup abs_cong =
  \<open>Scan.succeed (fn ctxt => Method.SIMPLE_METHOD' (abs_cong_tac ctxt))\<close>
  "congruence method"

method cong_step = (app_cong | abs_cong | rule refl | rule eq_reflection)
method cong = (cong_step ; cong?)

text \<open> Preserve context information from \<open>[cong]\<close> rules\<close>

ML \<open>
fun const_cong ctxt = CSUBGOAL (fn (cgoal, i) =>
  let
    val goal = Thm.term_of cgoal;
  in
    (case Logic.strip_assums_concl goal of
      _ $ (_ $ t $ s) => (case (head_of t, head_of s) of
          (Const (c, _), Const (c', _)) =>
            if c = c'
            then
              case AList.lookup (op =) (#congs (dest_ss (simpset_of ctxt))) (true, c) of
                SOME thm =>
                  resolve_tac ctxt [Thm.transfer' ctxt thm RS meta_eq_to_obj_eq] i
              | NONE => no_tac
          else no_tac
        | _ => no_tac
      )
    | _ => no_tac)
  end);
\<close>

method_setup const_cong =
  \<open>Scan.succeed (fn ctxt => Method.SIMPLE_METHOD' (const_cong ctxt))\<close>
  "congruence method (constant with [cong])"

method cong_context_step = (const_cong | cong_step | rule simp_impliesI)
method cong_context = (cong_context_step ; cong_context?)

end
