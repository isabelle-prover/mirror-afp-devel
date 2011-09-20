(* Author: Tobias Nipkow *)

header {* Archive *}

theory Arch
imports Main "~~/src/HOL/Library/Efficient_Nat"
begin

setup {* fn thy =>
  let
    val T = @{typ "nat list list list"}
    val dir = Thy_Load.master_directory thy
  in
    thy |>
    Code_Runtime.polyml_as_definition
      [(@{binding Tri}, T), (@{binding Quad}, T), (@{binding Pent}, T),
       (@{binding Hex}, T)]
      (map (Path.append dir o Path.explode)
        ["Archives/Tri.ML", "Archives/Quad.ML",
          "Archives/Pent.ML", "Archives/Hex.ML"])
  end
*}

text {* The definition of these constants is only ever needed at the ML level
when running the eval proof method. *}

end
