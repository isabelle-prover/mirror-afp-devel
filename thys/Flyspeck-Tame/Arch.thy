(* Author: Tobias Nipkow *)

header {* Archive *}

theory Arch
imports Main "~~/src/HOL/Library/Efficient_Nat"
begin

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

text {* The definition of these constants is only ever needed at the ML level
when running the eval proof method. *}

end
