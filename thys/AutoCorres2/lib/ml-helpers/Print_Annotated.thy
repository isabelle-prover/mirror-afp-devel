(*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
print term with (minimal) complete type annotations
  (based on sledgehammer utility functions)
*)

theory Print_Annotated
  imports Main
  keywords "print_annotated_thm" :: diag
begin

ML \<open>
signature ANNOTATE_TERM =
sig
  val string_of_term: Proof.context -> int option -> term -> string
  val string_of_thm: Proof.context -> int option -> thm -> string
  val print_thm: Proof.context -> int option -> thm -> unit
end

structure Annotate_Term: ANNOTATE_TERM =
struct

fun string_of_term ctxt margin t =
  let
    val ctxt' = ctxt
      |> Config.put show_markup false
      |> Config.put Printer.show_type_emphasis false
      |> Config.put show_types false
      |> Config.put show_sorts false
      |> Config.put show_consts false
    fun print_term t' =
      Syntax.unparse_term ctxt' t'
      |> Pretty.string_of_ops (Pretty.output_ops margin)
  in
    t
    |> singleton (Syntax.uncheck_terms ctxt')
    |> Sledgehammer_Isar_Annotate.annotate_types_in_term ctxt'
    |> Print_Mode.setmp [] print_term
  end

fun string_of_thm ctxt margin thm =
  string_of_term ctxt margin (Thm.concl_of thm)

fun print_thm ctxt margin thm =
  writeln (Active.sendback_markup_command ("lemma \"" ^
    string_of_thm ctxt margin (Variable.import_vars ctxt thm) ^ "\""))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_annotated_thm\<close>
    "print theorems with (minimal) complete type annotations"
    (Scan.option (Args.parens Parse.nat) -- Parse.thm
      >> (fn (margin, thm_src) => Toplevel.keep (fn state =>
        let
          val ctxt = Toplevel.context_of state
          val [thm] = Attrib.eval_thms ctxt [thm_src]
        in print_thm ctxt margin thm end)));

end
\<close>

end
