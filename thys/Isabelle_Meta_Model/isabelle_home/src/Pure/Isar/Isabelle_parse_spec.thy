chapter{* Part ... *}

theory Isabelle_parse_spec
  imports Main
begin

ML{* 
structure Isabelle_Parse_Spec =
struct
(*  Title:      Pure/Isar/parse_spec.ML
    Author:     Makarius

Parsers for complex specifications.
*)
  val simple_spec = Parse_Spec.opt_thm_name ":" -- Parse.inner_syntax Parse.cartouche;

  val if_assumes =
    Scan.optional (Parse.$$$ "if" |-- Parse.!!! (Parse.and_list1 (Scan.repeat1 Parse.prop) >> flat))
      [];

  val spec = (Parse_Spec.opt_thm_name ":" -- Parse.inner_syntax Parse.cartouche) -- if_assumes >> swap;

  val multi_specs =
    Parse.enum1 "|"
      (Parse_Spec.opt_thm_name ":" -- Parse.inner_syntax Parse.cartouche -- if_assumes --|
        Scan.option (Scan.ahead (Parse.name || Parse.$$$ "[") -- Parse.!!! (Parse.$$$ "|")));

  val where_multi_specs = Parse.where_ |-- Parse.!!! multi_specs;
end
*}

end
