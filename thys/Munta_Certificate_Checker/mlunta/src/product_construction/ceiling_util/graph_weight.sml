signature GRAPH_WEIGHT = sig
  structure W : WEIGHT
  type t
  val unbound: t
  val is_unbound: t -> bool
  val max: t -> t -> t
  val update: W.t -> t -> t
  val add: t -> t -> t
  val back: t -> W.t
  val show: t -> string
end

functor GraphWeightFn(W : WEIGHT): GRAPH_WEIGHT = struct
structure W = W
type t = W.t option
val unbound = NONE
fun is_unbound x =
    case x of
        NONE => true |
        _ => false

fun max x y =
    case (x, y) of
        (NONE, _) => y |
        (_, NONE) => x |
        (SOME x, SOME y) => W.max x y |> SOME

fun update x =
    max (SOME x)

fun add x y =
    case (x, y) of
        (NONE, _) => NONE |
        (_, NONE) => NONE |
        (SOME x, SOME y) => W.add x y |> SOME

fun back x =
    case x of
        NONE => W.zero |
        SOME x => x

fun show x =
    case x of
        NONE => "inf" |
        SOME x => W.show x
end
