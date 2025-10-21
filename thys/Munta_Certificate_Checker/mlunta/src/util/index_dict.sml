(* XXX: Add sig *)
structure IndexDict =
struct
type key = int

type 'a t = 'a vector
val fromList = Vector.fromList
val fromVector = I

fun find k dict = Vector.sub (dict, k)
fun app f dict = Vector.app f dict
fun update i v vec = Vector.update (vec, i, v)
val map = Vector.map
fun tabulate n = (curry Vector.tabulate) n
val mapi = Vector.mapi
val foldli = Vector.foldli
val foldl = Vector.foldl
val size = Vector.length
fun to_list dict = List.tabulate (size dict, flip find dict)
val collate = Vector.collate
fun show f dict =
    "["
    ^ (map f dict |> to_list |> String.concatWith ",")
    ^ "]"
end
