(* Author: Tobias Nipkow *)

header {* Archive *}

theory Arch
imports Main Efficient_Nat
(*uses
  ("Archives/Tri.ML")
  ("Archives/Quad.ML")
  ("Archives/Pent.ML")
  ("Archives/Hex.ML")
  ("Archives/Hept.ML")
  ("Archives/Oct.ML")*)
begin

setup {*
  Code_Runtime.polyml_as_definition
    (map (rpair @{typ "nat list list list"})
      [@{binding Tri}, @{binding Quad}, @{binding Pent}, @{binding Hex}, @{binding Hept}, @{binding Oct}])
    (map (Path.append (Path.explode "Archives") o Path.ext "ML" o Path.explode)
      ["Tri", "Quad", "Pent", "Hex", "Hept", "Oct"])
*}

end
