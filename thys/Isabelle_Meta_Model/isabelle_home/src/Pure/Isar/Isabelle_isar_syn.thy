chapter{* Part ... *}

theory Isabelle_isar_syn
  imports Isabelle_parse_spec
  keywords "definition'" :: thy_decl
begin

ML{* 
structure Isabelle_Isar_Syn =
struct
(*  Title:      Pure/Isar/isar_syn.ML
    Author:     Makarius

Outer syntax for Isabelle/Pure.
*)
  val _ =
    Outer_Syntax.local_theory' @{command_keyword definition'} "constant definition"
      (Scan.option Parse_Spec.constdecl -- Isabelle_Parse_Spec.spec
        >> (fn (a, (b, c)) => #2 oo Specification.definition_cmd a b c));
end
*}

end
