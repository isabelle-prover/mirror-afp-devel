(*
 * Copyright (c) 2024 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Sketch_Tags
  imports Tagging "HOL-ex.Sketch_and_Explore"
  keywords "sketch_subgoalsT" :: diag
begin

ML \<open>
fun print_subgoal apply_line_opt (is_prems, is_for, is_sh) ctxt indent stmt =
  let
    val ((fixes, _, _), ctxt') = eigen_context_for_statement stmt ctxt;
    val prefix = replicate_string indent " ";
    val (_, _, concl) = stmt;
    val tag_opt = tag_list_of concl;
    val kw_tag_spec_opt = (case tag_opt of
      [] => NONE
    | xs => SOME (map (ATP_Util.maybe_quote ctxt) xs |> separate " " |> String.concat))
    val fixes_s =
      if not is_for orelse null fixes then NONE
      else SOME ("for " ^ implode_space
        (map (fn (v, _) => Thy_Header.print_name' ctxt' v) fixes));
    val premises_s = if is_prems then SOME "premises prems" else NONE;
    val sh_s = if is_sh then SOME "sledgehammer" else NONE;
    val subgoal_s = map_filter I [SOME "subgoalT", kw_tag_spec_opt, premises_s, fixes_s]
      |> implode_space;
    val using_s = if is_prems then SOME "using prems" else NONE;
    val s = cat_lines (
      [subgoal_s]
      @ map_filter (Option.map (fn s => prefix ^ s)) [using_s, apply_line_opt, sh_s]
      @ [prefix ^ "sorry"]);
  in
    s
  end;

fun print_subgoals options apply_line_opt ctxt _ clauses =
  separate "" (map (print_subgoal apply_line_opt options ctxt 2) clauses) @ ["done"];

fun subgoals options method_ref =
  let
    val apply_line_opt = case method_ref of
        NONE => NONE
      | SOME (_, toks) => SOME ("apply " ^ coalesce_method_txt (map Token.unparse toks))
    val succeed_method_ref = SOME ((Method.succeed_text, Position.no_range), [])
  in
    print_proof_text_from_state (print_subgoals options apply_line_opt) succeed_method_ref
  end;

fun subgoals_cmd (modes, method_ref) =
  let
    val is_prems = not (member (op =) modes "noprems")
    val is_for = not (member (op =) modes "nofor")
    val is_sh = member (op =) modes "sh"
    fun tidy_all ctxt = SIMPLE_METHOD (TRYALL (tidy_tags_tac false ctxt))
  in
    Toplevel.keep_proof (fn state =>
      subgoals (is_prems, is_for, is_sh) method_ref
        (Proof.refine_singleton (Method.Basic tidy_all) (Toplevel.proof_of state)))
  end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>sketch_subgoalsT\<close>
    "sketch proof obligations as subgoals, applying a method and/or sledgehammer to each"
    (opt_modes -- Scan.option (Scan.trace Method.parse) >> subgoals_cmd);
\<close>

end