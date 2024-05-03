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
  imports
    Main
  keywords
    "print_annotated_thm" :: diag
begin

ML \<open>
signature ANNOTATE_TERM =
sig
  val string_of_term:
     Proof.context -> int option -> term -> string
  val string_of_thm:
     Proof.context -> int option -> thm -> string
  val print_thm: Proof.context -> int option -> thm -> unit
  val print_thm_cmd:
     int option ->
     Facts.ref * Token.src list ->
       Toplevel.transition -> Toplevel.transition
end
structure Annotate_Term : ANNOTATE_TERM =
struct

local
open Sledgehammer_Util
in
fun string_of_term ctxt margin term =
  let
    val keywords = Thy_Header.get_keywords' ctxt
    val ctxt' = ctxt
      |> Config.put show_markup false
      |> Config.put Printer.show_type_emphasis false
      |> Config.put show_types false
      |> Config.put show_sorts false
      |> Config.put show_consts false
  in
    term
      |> singleton (Syntax.uncheck_terms ctxt')
      |> Sledgehammer_Isar_Annotate.annotate_types_in_term ctxt'
      |> Print_Mode.setmp []
          (Syntax.unparse_term ctxt'
            #> the_default Pretty.string_of (Option.map Pretty.string_of_margin margin))
  end
end

fun string_of_thm ctxt margin thm = string_of_term ctxt margin (thm |> Thm.concl_of)

fun print_thm ctxt margin thm =
  writeln (Active.sendback_markup_command ("lemma \"" ^
    string_of_thm ctxt margin (Variable.import_vars ctxt thm) ^ "\""))

fun print_thm_cmd margin arg = Toplevel.keep (fn state =>
  let
    val ctxt = Toplevel.context_of state
    val [thm] = Attrib.eval_thms ctxt [arg]
  in print_thm ctxt margin thm end
)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_annotated_thm\<close>
    "print theorems with (minimal) complete type annotations"
    ((Scan.option (Args.parens Parse.nat) -- Parse.thm) >> (fn (margin, facts) =>
      print_thm_cmd margin facts));

end
\<close>

end
