(*  Title:      Logger/Data_Structures/map.ML
    Author:     Kevin Kappelmann

Key-Value Maps
*)
signature MAP =
sig
  type key
  type 'a map

  val empty : 'a map
  val is_empty : 'a map -> bool

  val lookup: 'a map -> key -> 'a option

  val map : (key -> 'a -> 'b) -> 'a map -> 'b map

  exception SAME
  (*raises SAME if entry is not found*)
  val map_entry : key -> ('a -> 'a) -> 'a map -> 'a map
  val map_default : key * 'a -> ('a -> 'a) -> 'a map -> 'a map

  val delete : key -> 'a map -> 'a map
  val join : (key -> 'a * 'a -> 'a) -> ('a map * 'a map) -> 'a map
end

functor TableMap(T : TABLE) : MAP =
struct

type key = T.key
type 'a map = 'a T.table

val empty = T.empty
val is_empty = T.is_empty

val lookup = T.lookup

val map = T.map

exception SAME = T.SAME
val map_entry = T.map_entry
val map_default = T.map_default

val delete = T.delete
val join = T.join

end