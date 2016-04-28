chapter{* Part ... *}

theory Isabelle_function_common
imports "../../../Pure/Isar/Isabelle_parse_spec"
begin

section{* ... *}

ML{*
structure Isabelle_Function_Common =
struct
(*  Title:      HOL/Tools/Function/function_common.ML
    Author:     Alexander Krauss, TU Muenchen

Common definitions and other infrastructure for the function package.
*)
  val function_parser =
      (* config_parser default_cfg -- *) Parse.fixes -- Isabelle_Parse_Spec.where_multi_specs
end
*}

end
