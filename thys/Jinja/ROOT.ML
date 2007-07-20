goals_limit := 1;

add_path "BV";
add_path "Common";
add_path "Compiler";
add_path "DFA";
add_path "J";
add_path "JVM";

no_document use_thy "List_Prefix";
no_document use_thy "While_Combinator";

use_thy "J/TypeSafe";
use_thy "J/Annotate";

(*
use_thy "Example";
*)

no_document use_thy "Efficient_Nat";
use_thy "J/execute_Bigstep";
use_thy "J/execute_WellType";

use_thy "JVM/JVMDefensive";

use_thy "JVM/JVMListExample";

use_thy "BV/BVExec";
use_thy "BV/LBVJVM";
use_thy "BV/BVNoTypeError";

no_document use_thy "Executable_Set";
use_thy "BV/BVExample";

use_thy "Compiler/TypeComp";
