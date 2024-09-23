(*
 * Copyright (c) 2024 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Subgoals
  imports Main
  keywords "prefers" :: prf_script % "proof" and "subgoals" :: prf_script_goal % "proof" 
begin

definition protected_conjunction :: "prop \<Rightarrow> prop \<Rightarrow> prop" (infixr \<open>&^&\<close> 2) where
  "protected_conjunction A B \<equiv> (PROP A &&& PROP B)"

definition
  "protected_prop A \<equiv> PROP A"

lemma protect_prop:
  "PROP A" if "PROP protected_prop A"
  using that unfolding protected_prop_def .

ML \<open>
fun filter_subgoals (test : cterm -> bool) thm =
  let                                      
    val indexed_subgoals = tag_list 0 (Thm.cprems_of thm);
  in
    map fst (Library.filter (fn (_, subgoal) => test subgoal) indexed_subgoals)
  end

fun match_cterm pattern cterm = 
  (Thm.match (pattern, cterm); true) handle Pattern.MATCH => false

datatype match_kind = Match_Concl | Match_Prems

fun match_cterm_rec pattern cterm = 
  if match_cterm pattern cterm then
    true
  else
    match_cterm_rec pattern (Thm.dest_fun cterm)
  handle
    Thm.CTERM _ => false

fun dest_all_cterm_all ctxt ct =
  let
    val ((_, ct), ctxt) = Variable.dest_all_cterm ct ctxt
  in
    dest_all_cterm_all ctxt ct
  end
  handle CTERM _ => ct

fun match_subgoal (kind : match_kind) (no_match : bool) ctxt (pattern : cterm) (subgoal : cterm) =
  let 
    val cterms = case kind of
      Match_Concl => [dest_all_cterm_all ctxt subgoal |> Drule.strip_imp_concl] |
      Match_Prems => (dest_all_cterm_all ctxt subgoal |> Drule.strip_imp_prems);
    val match = fold (fn cterm => fn b => b orelse match_cterm_rec pattern
      (Thm.dest_arg cterm)) cterms false
  in                                     
    if no_match then not match else match
  end

fun prefer_and_uncurry_subgoals_tac pred ctxt : tactic = fn thm =>
  let
    val indices = filter_subgoals pred thm
  in
    if indices = [] then
      Seq.empty
    else if length indices = 1 then
      CONVERSION (
        Conv.top_conv (K (Conv.rewr_conv @{thm protected_prop_def[symmetric]})) ctxt)
        1 (Drule.rearrange_prems indices thm)
    else
      Seq.single (Conjunction.uncurry_balanced
        (length indices)
        (Drule.rearrange_prems indices thm))
  end

fun prefer_and_protect_subgoals_tac pred ctxt =
  prefer_and_uncurry_subgoals_tac pred ctxt
    THEN (REPEAT_DETERM (CHANGED_PROP (CONVERSION ((Conv.top_sweep_conv (K (Conv.rewr_conv 
        @{thm protected_conjunction_def[symmetric]})) ctxt)) 1)))

fun prefer_and_protect_subgoals_tac_pat (kind : match_kind) (no_match : bool) (pattern : cterm) =
  fn ctxt => prefer_and_protect_subgoals_tac (match_subgoal kind no_match ctxt pattern) ctxt

fun unprotect_subgoals_tac thms ctxt : tactic =
  REPEAT_DETERM (CHANGED_PROP (CONVERSION
    (Conv.top_sweep_conv (K (Conv.rewrs_conv thms)) ctxt) 1))

fun construct_pattern ctxt pattern = 
  let
    val pattern = Proof_Context.read_term_pattern ctxt pattern;
    val pattern = 
      if Term.fastype_of pattern = @{typ prop} then
        HOLogic.dest_Trueprop pattern
      else
        pattern
  in 
    Thm.cterm_of ctxt pattern end

val parse_match_kind = Scan.optional (
  Args.parens (
    Args.$$$ "concl"     >> K (Match_Concl, false) ||
    Args.$$$ "not_concl" >> K (Match_Concl, true) ||
    Args.$$$ "prems"     >> K (Match_Prems, false) ||
    Args.$$$ "not_prems" >> K (Match_Prems, true))) (Match_Concl, false);

fun unprotect_and_finish thms =
  Seq.make_results o
  Seq.single o
  Proof.refine_singleton
    (Method.Basic (fn _ => Method.succeed)) o
  Proof.refine_singleton
    (Method.Basic (fn ctxt => SIMPLE_METHOD
      (unprotect_subgoals_tac thms ctxt))
    )

val _ = Outer_Syntax.command \<^command_keyword>\<open>prefers\<close> 
  "select subgoals that match a given pattern"
  (parse_match_kind -- Parse.embedded_inner_syntax >> (fn ((kind, invert), pattern) => 
      Toplevel.proofs (fn state => (
        let
          val ctxt = Proof.context_of state;
          val pattern = construct_pattern ctxt pattern
        in
          unprotect_and_finish @{thms protected_conjunction_def protected_prop_def} o
          Proof.refine_singleton 
            (Method.Basic (fn ctxt => SIMPLE_METHOD 
              (prefer_and_protect_subgoals_tac_pat kind invert pattern ctxt))) end) state)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>subgoals\<close>
    "focus on all subgoals that match a given pattern within backward refinement"
    (parse_match_kind -- Parse.embedded_inner_syntax >> (fn ((kind, invert), pattern) => 
      Toplevel.proofs (fn state => (
        let
          val ctxt = Proof.context_of state;
          val pattern = construct_pattern ctxt pattern
        in
          unprotect_and_finish @{thms protected_conjunction_def protected_prop_def} o
          #2 o
          Subgoal.subgoal Binding.empty_atts NONE (false, []) o
          Proof.refine_singleton
            (Method.Basic (fn ctxt => SIMPLE_METHOD 
              (prefer_and_protect_subgoals_tac_pat kind invert pattern ctxt))) end) state)))
\<close>

end