no_document use_thys 
  ["common/Misc",
   "common/Assoc_List",
   "common/RBT_add",
   "common/Dlist_add",
   "common/Array",
   "Efficient_Nat",
   "While_Combinator"];

use_thys 
   [ (* Specifications *)
    "MapSpec", "OrderedMap", "SetSpec", "OrderedSet", "ListSpec",
     (* Generic Algorithms *)
    "MapGA", "SetGA", "SetByMap", "ListGA", "SetIndex", "Algos",
     (* Implementations *)
    "MapStdImpl", "SetStdImpl",
    "Fifo"];

no_document use_thys ["StdInst"];

use_thys
   ["Collections",
    "Userguide",
    (* Examples *)
    "examples/itp_2010", "examples/Exploration", "examples/Exploration_DFS", "All"];
