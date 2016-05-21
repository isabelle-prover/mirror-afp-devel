chapter{* Part ... *}

theory Isabelle_fun
imports Isabelle_function_common
  keywords "fun'" :: thy_decl
begin

section{* ... *}

ML{*
structure Isabelle_Function_Fun =
struct
(*  Title:      HOL/Tools/Function/fun.ML
    Author:     Alexander Krauss, TU Muenchen

Command "fun": Function definitions with pattern splitting/completion
and automated termination proofs.
*)
  val _ =
    Outer_Syntax.local_theory' @{command_keyword fun'}
      "define general recursive functions (short version)"
      (Isabelle_Function_Common.function_parser 
        >> (fn (fixes, statements) => Function_Fun.add_fun_cmd fixes statements Function_Fun.fun_config))
end
*}

end
