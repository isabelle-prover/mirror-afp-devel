(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Basic definitions for monad types.
 *
 * This file is loaded before type strengthening so that its
 * attributes can be used.
 *
 * The basic set of attributes is defined in TypeStrengthen.thy.
 *)

structure Monad_Types = struct


type refines_nondet_info = {rules_name : string, relator: term, relator_from_c_exntype: term option, lift: term, 
       dest_lift: term -> term option, lift_prev: thm list}

fun relator_from_c_exntype (info:refines_nondet_info) = the_default (#relator info) (#relator_from_c_exntype info)
(*
 * The monad_type and ts_rule attribute setup.
 *)
type monad_type = {

  (* A short name used to refer to this monad. *)
  name : string,

  (* A longer description. AutoCorres does not use this, so write whatever you want. *)
  description : string,

  ccpo_name : string,
  (*
   * Type conversion rules.
   * While we store full contexts, we are really only interested in their simpsets.
   * The rest of the context data is unused.
   *)

  (* Rules and simprocs for converting L2_monad to your monad. *)
  refines_nondet : refines_nondet_info,
  
  (*
   * TypeStrengthen internal usage
   *)

  (* Rule precedence; higher-numbered rules are tried first. *)
  precedence : int,

  (* Construct your monad type, given (state, result, exception). *)
  typ_from_L2 : {stateT:typ, resT:typ, exT: typ} -> typ,
  lift_from_previous_monad :  Proof.context -> typ (* state *) -> term -> term
}

fun update_mt_rules update_lifts update_unlifts update_polish (mt : monad_type) = {
  name = #name mt,
  description = #description mt,
  ccpo_name = #ccpo_name mt,
  refines_nondet = #refines_nondet mt,
  precedence = #precedence mt,
  lift_from_previous_monad = #lift_from_previous_monad mt,
  typ_from_L2 = #typ_from_L2 mt
}


(* TODO: figure out how to do this with Theory_Data *)
structure TSRules = Generic_Data
(
  type T = monad_type Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (K true)
)

fun error_no_such_mt name = error ("autocorres: no such monad type " ^ quote name)

fun update_the_mt (name : Symtab.key) (f : monad_type -> monad_type) (t : TSRules.T) =
  case Symtab.lookup t name of
      NONE => error_no_such_mt name
    | SOME mt => Symtab.update (name, f mt) t

fun change_TSRules update_rules update_simps name thms =
  TSRules.map (update_the_mt name (update_rules
    (fn thmset => update_simps thmset thms)))

fun thmset_adds set thms = fold (Thmset.insert o Thm.trim_context) thms set
fun thmset_dels set thms = fold Thmset.remove thms set


(*
 * Extra monad_type utilities.
 *)

(* Lazy check_lifting, which only checks the head term. *)
fun check_lifting_head (heads : term list) : (Proof.context -> term -> bool) =
  let val head_names = map (fn Const (name, _) => name | _ => raise Match) heads
      fun check _ t = case head_of t of
                          Const (name, _) => member (op =) head_names name
                        | _ => false
  in check end

fun new_monad_type
      (name : string)
      (description : string)
      (ccpo_name : string)
      (precedence : int)
      (typ_from_L2 : {stateT: typ, resT: typ, exT: typ} -> typ)
      (lift_from_previous_monad: Proof.context -> typ -> term -> term)
      (refines_nondet: refines_nondet_info)
      : Context.generic -> Context.generic =
  TSRules.map (fn t =>
    let
      val mt = {
        name = name,
        description = description,
        ccpo_name = ccpo_name,
        (* TODO: it seems that we could use empty_ss instead of HOL_basic_ss,
                 but then Isabelle throws all the rules away when we cross
                 theory boundaries or merge theories. Investigate. *)
        precedence = precedence,
        lift_from_previous_monad = lift_from_previous_monad,
        typ_from_L2 = typ_from_L2,
        refines_nondet = refines_nondet
      }
    in
      Symtab.update_new (name, mt) t
      handle Symtab.DUP _ =>
        error ("autocorres: cannot define the monad type " ^ quote name ^
               " because it has already been defined.")
    end)

fun get_monad_type (name : string) (ctxt : Context.generic) : monad_type option =
  Symtab.lookup (TSRules.get ctxt) name


(* Get rules ordered by precedence. If only_use is empty, return all rules. *)
fun get_ordered_rules (only_use : string list)
                      (ctxt : Context.generic) : monad_type list =
let
  val mts = TSRules.get ctxt
  val needed_mts =
      if null only_use then Symtab.dest mts |> map snd
      else only_use |> map (fn name => case Symtab.lookup mts name of
                                           SOME x => x
                                         | NONE => error_no_such_mt name)
in
  (* Order by highest precedence first. *)
  map (fn mt => (#precedence mt, mt)) needed_mts
  |> sort (rev_order o int_ord o apply2 fst)
  |> map snd
end

fun wrap_prems_with_DYN_CALL thm =
  let
     val n = Thm.nprems_of thm
  in
    if exists (exists_subterm (fn Const (c, _) => c = \<^const_name>\<open>DYN_CALL\<close> | _ => false)) (Thm.prems_of thm) then 
      thm
    else 
      thm OF replicate n @{thm DYN_CALL_D}
  end

fun add_call_rule_attrib (mt:monad_type) only_schematic_goal b priority  =
  Thm.declaration_attribute (fn thm => fn context => 
    let
      val thm = wrap_prems_with_DYN_CALL thm
      val lifted_thms = map_filter (fn rule => try (fn thm => rule OF [thm]) thm) (#lift_prev (#refines_nondet mt))
      
    in
      context 
      |> fold (Thm.attribute_declaration  
               (Synthesize_Rules.add_rule_most_generic_pattern_attrib (#rules_name (#refines_nondet mt)) only_schematic_goal b priority)) 
         (thm::lifted_thms)
    end)

fun add_call_rule_attribs ctxt (mt:monad_type) only_schematic_goal b priority =
  let
    val mts = get_ordered_rules [] ctxt |> filter_out (fn t => #precedence mt < #precedence t) 
  in
    map (fn mt => add_call_rule_attrib mt only_schematic_goal b priority) mts
  end

end
