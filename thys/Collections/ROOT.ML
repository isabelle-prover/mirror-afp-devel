no_document use_thy "common/Misc";

(* Specifications *)
use_thys ["MapSpec", "SetSpec", "Fifo"];

(* Generic algorithms *)
use_thys ["MapGA", "SetGA", "SetByMap", "Algos", "SetIndex"];

(* Implementations *)
no_document use_thys
 ["While_Combinator", "AssocList", "RBT_add", "Efficient_Nat"];

use_thys
  ["ListMapImpl", "ListSetImpl", "RBTMapImpl", "RBTSetImpl",
   "HashCode", "HashMap", "HashSet"];

no_document use_thy "StdInst";

use_thy "Collections";

(* Userguide *)
use_thy "Userguide";

(* Example *)
no_document use_thy "While_Combinator";
use_thys ["DatRef", "Exploration", "Exploration_Example"];

(* Test *)
(* no_document use _ thy "Test"; *)
