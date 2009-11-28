no_document use_thy "common/Misc";

(* Specifications *)
use_thy "MapSpec";
use_thy "SetSpec";
use_thy "Fifo";

(* Generic algorithms *)
use_thy "MapGA";
use_thy "SetGA";
use_thy "SetByMap";
use_thy "Algos";
use_thy "Index";

(* Implementations *)
no_document use_thy "AssocList";
no_document use_thy "RBT";
no_document use_thy "RBT_add";
no_document use_thy "common/bugfixes/Efficient_Nat";

use_thy "ListMapImpl";
use_thy "ListSetImpl";
use_thy "RBTMapImpl";
use_thy "RBTSetImpl";

use_thy "HashCode";
use_thy "HashMap";
use_thy "HashSet";

no_document use_thy "StdInst";

use_thy "Collections";

(* Userguide *)
use_thy "Userguide";

(* Example *)
no_document use_thy "While_Combinator";
use_thy "DatRef";
use_thy "Exploration";
use_thy "Exploration_Example";

(* Test *)
(* no_document use _ thy "Test"; *)
