(* Author: Tobias Nipkow *)

header {* Archive *}

theory Arch
imports Main Efficient_Nat
begin

(*
setup {*
let val T = @{typ "nat list list list"}
in
  Code_Runtime.polyml_as_definition
    [(@{binding Tri},T), (@{binding Quad},T), (@{binding Pent},T),
     (@{binding Hex},T)]
    (map Path.explode ["Archives/Tri.ML", "Archives/Quad.ML",
                       "Archives/Pent.ML", "Archives/Hex.ML"])
end
*}
*)

ML {* Secure.use_file ML_Env.local_context false "Archives/Tri.ML" *}
ML {* Secure.use_file ML_Env.local_context false "Archives/Quad.ML" *}
ML {* Secure.use_file ML_Env.local_context false "Archives/Pent.ML" *}
ML {* Secure.use_file ML_Env.local_context false "Archives/Hex.ML" *}

consts
Tri :: "nat list list list"
Quad :: "nat list list list"
Pent :: "nat list list list"
Hex :: "nat list list list"

code_const Tri and Quad and Pent and Hex
  (SML "Tri" and "Quad" and "Pent" and "Hex")

text {* The definition of these constants is only ever needed at the ML level
when running the eval proof method. *}

end
