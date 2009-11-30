use "generated/Ta.ML";

open Ta;
open List; (* Get back some standard defs that have been overwritten in Ta *)

(* Build tree automaton *)
fun createFta (initial, rules) =
  let val f1 = foldl (fn (q,a) => htai_add_qi q a) (htai_empty) initial in
    foldl (fn (r,a) => htai_add_rule r a) f1 rules
  end;

(* Return info about tree automaton *)
fun info H =
  Int.toString( ls_size (hta_delta H) ) ^ " Rules";

(* Tree pretty printer *)

fun concpad (pad, []) = "" |
    concpad (pad, [s]) = s |
    concpad (pad, (s::ss)) = s ^ pad ^ concpad(pad,ss);

fun pretty_tree (Node(f, [])) = Int.toString f |
    pretty_tree (Node(f,ts)) = Int.toString f ^ "(" ^ concpad(", ", map pretty_tree ts) ^ ")";

fun pretty_witness (NONE) = "none" |
    pretty_witness (SOME t) = pretty_tree t;
