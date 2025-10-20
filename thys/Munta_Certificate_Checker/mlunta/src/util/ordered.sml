datatype order = Lt | Gt | Eq
fun order_to_ordered LESS = Lt
  | order_to_ordered GREATER = Gt
  | order_to_ordered EQUAL = Eq
signature ORDERED = sig
    type t
    val cmp: t -> t -> order
end

structure IntCmp : ORDERED = struct
type t = int
fun cmp x y = if x < y then Lt else if x > y then Gt else Eq
end

structure StrCmp : ORDERED = struct
type t = string
fun cmp x y = String.compare (x, y) |> order_to_ordered
end
