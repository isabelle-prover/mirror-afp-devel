(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Misc_Antiquotation
  imports Main
begin

section \<open>Various Antiquotations\<close>

subsection \<open>Antiquotations for terms with schematic variables\<close>

setup \<open>
let
  val parser = Args.context -- Scan.lift Parse.embedded_inner_syntax
  fun pattern (ctxt, str) =
     str |> Proof_Context.read_term_pattern ctxt
         |> ML_Syntax.print_term
         |> ML_Syntax.atomic
in
 ML_Antiquotation.inline @{binding "pattern"} (parser >> pattern)
end
\<close>

ML \<open>@{pattern "\<lambda>(a,b,c). ?g a b c"}\<close>

setup \<open>
let
type style = term -> term;

fun pretty_term_style ctxt (style: style, t) =
  Document_Output.pretty_term ctxt (style t);

val basic_entity = Document_Output.antiquotation_pretty_source;

in
(* Document antiquotation that allows schematic variables *)
(basic_entity \<^binding>\<open>pattern\<close> (Term_Style.parse -- Args.term_pattern) pretty_term_style)
end
\<close>

subsection \<open>Antiquotation for types with schematic variables\<close>

setup \<open>
let
  val parser = Args.context -- Scan.lift Parse.embedded_inner_syntax
  fun typ_pattern (ctxt, str) =
    let
      val ctxt' = Proof_Context.set_mode Proof_Context.mode_schematic ctxt
    in
      str |> Proof_Context.read_typ ctxt'
          |> ML_Syntax.print_typ
          |> ML_Syntax.atomic
    end
in
 ML_Antiquotation.inline @{binding "typ_pattern"} (parser >> typ_pattern)
end
\<close>

ML \<open>@{typ_pattern "?'a list"}\<close>
ML \<open>Sign.typ_instance @{theory} (@{typ "'a list"}, @{typ_pattern "?'a list"})\<close>


end