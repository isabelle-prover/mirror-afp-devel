no_document use_thys
  ["../Collections/common/Misc",
   "../Collections/common/bugfixes/Efficient_Nat",
   "While_Combinator", "../Collections/Collections",
   "../Collections/DatRef",
   "../Collections/Exploration"];

(* Tree Automata *)
use_thys ["Tree", "Ta", "AbsAlgo", "Ta_impl"];

(* Code Generation *)
no_document use_thy "Ta_impl_codegen";
