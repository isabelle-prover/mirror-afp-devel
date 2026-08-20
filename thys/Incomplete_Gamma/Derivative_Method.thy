(*
   File:    Derivative_Method.thy
   Author:  Manuel Eberl, University of Innsbruck
*)
section \<open>A proof method for computing derivatives\<close>
theory Derivative_Method
  imports Complex_Main
begin

(* TODO: Move to distribution *)

ML \<open>

signature DERIVATIVE_METHOD =
sig

val tac : bool -> Proof.context -> int -> tactic

end

structure Derivative_Method : DERIVATIVE_METHOD =
struct

fun is_deriv_prop prop = (
  case head_of (HOLogic.dest_Trueprop (Logic.strip_imp_concl prop)) of
    Const (\<^const_name>\<open>has_derivative\<close>, _) => true
  | Const (\<^const_name>\<open>has_field_derivative\<close>, _) => true
  | Const (\<^const_name>\<open>has_vector_derivative\<close>, _) => true
  | _ => false
  ) handle TERM _ => false  

fun tac nofail ctxt =
  let
    val eq_thms =
      @{thms has_derivative_eq_rhs[rotated]
             DERIV_cong[rotated]
             has_vector_derivative_eq_rhs[rotated]}
    val intros = Named_Theorems.get ctxt \<^named_theorems>\<open>derivative_intros\<close>
    val MYTRY = if nofail then TRY else I
    fun tac' (t, i) =
      if is_deriv_prop t then MYTRY (
        (resolve_tac ctxt intros
         THEN_ALL_NEW SUBGOAL tac') i)
      else all_tac
    fun tac i =
      resolve_tac ctxt eq_thms i
      THEN SUBGOAL tac' (i + 1)
  in
    tac
  end

val args_parser =
  Scan.lift (Scan.optional (Args.parens (Args.$$$ "nofail") >> K true) false) --|
  Method.sections [
    Args.add -- Args.colon >> 
      K (Method.modifier (Named_Theorems.add \<^named_theorems>\<open>derivative_intros\<close>) \<^here>),
    Args.del -- Args.colon >> 
      K (Method.modifier (Named_Theorems.del \<^named_theorems>\<open>derivative_intros\<close>) \<^here>)
  ]

val method = args_parser >> (SIMPLE_METHOD' oo tac)

val _ = 
  Theory.setup (Method.setup \<^binding>\<open>derivative\<close> method "automation for computing derivatives")

end

\<close>

end
