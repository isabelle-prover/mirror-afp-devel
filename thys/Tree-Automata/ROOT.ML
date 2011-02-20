no_document use_thys [
  "../Collections/common/Misc",
  "~~/src/HOL/Library/Efficient_Nat",
  "~~/src/HOL/Library/While_Combinator",
  "../Collections/Collections",
  "../Collections/DatRef",
  "../Collections/examples/Exploration"];

(* Tree Automata *)
use_thys ["Tree", "Ta", "AbsAlgo", "Ta_impl"];

(* Code Generation *)
no_document use_thy "Ta_impl_codegen";
