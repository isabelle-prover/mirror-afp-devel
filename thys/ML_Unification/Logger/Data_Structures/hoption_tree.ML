(*  Title:      Logger/Data_Structures/hoption_tree.ML
    Author:     Kevin Kappelmann

Hierarchical trees with optional values.
*)
signature HOPTION_TREE =
sig
  type letter
  type word = letter list
  type 'a hoption_tree

  val empty : 'a hoption_tree
  val is_empty : 'a hoption_tree -> bool

  val lookup: 'a hoption_tree -> word -> 'a option

  exception INSERT
  (*raises INSERT if the entry is already set*)
  val insert : (word * 'a) -> 'a hoption_tree -> 'a hoption_tree
  val insert_safe : (word * 'a) -> 'a hoption_tree -> 'a hoption_tree

  exception DELETE
  (*deletes entry; raises DELETE if the corresponding entry is not set*)
  val delete : word -> 'a hoption_tree -> 'a hoption_tree
  val delete_safe : word -> 'a hoption_tree -> 'a hoption_tree
  (*like delete but also cuts off all subtrees*)
  val cut : word -> 'a hoption_tree -> 'a hoption_tree
  (*does not cut subtrees if entry is not set*)
  val cut_safe : word -> 'a hoption_tree -> 'a hoption_tree

  (*maps entry*)
  val map : word -> ('a option -> 'a option) -> 'a hoption_tree -> 'a hoption_tree
  (*maps entry and all entries in subtrees*)
  val map_below : word -> ('a option -> 'a option) -> 'a hoption_tree -> 'a hoption_tree

  val join : ('a option * 'a option -> 'a option) -> 'a hoption_tree * 'a hoption_tree ->
    'a hoption_tree
end

functor HOption_Tree(M : MAP) : HOPTION_TREE =
struct

type letter = M.key
type word = letter list

datatype 'a hoption_tree = HOption_Tree of 'a option * ('a hoption_tree M.map)

fun get_data (HOption_Tree (data, _)) = data
fun get_map (HOption_Tree (_, m)) = m

val empty = HOption_Tree (NONE, M.empty)
fun has_empty_data hoptt = is_none (get_data hoptt)
fun has_empty_map hoptt = M.is_empty (get_map hoptt)
fun is_empty hoptt = has_empty_data hoptt andalso has_empty_map hoptt

fun hoptt_map f (HOption_Tree p) = HOption_Tree (f p)
fun map_data f = hoptt_map (apfst f)
fun map_map f = hoptt_map (apsnd f)


exception INSERT
fun insert_data data =
  map_data (fn old_data => if is_some old_data then raise INSERT else SOME data)

exception DELETE
fun delete_data hoptt =
  map_data (fn old_data => if is_none old_data then raise DELETE else NONE) hoptt

fun lookup hoptt [] = get_data hoptt
  | lookup hoptt (l :: ls) =
      M.lookup (get_map hoptt) l
      |> Option.mapPartial (fn hoptt => lookup hoptt ls)

fun insert ([], data) = insert_data data
  | insert (l :: ls, data) =
      map_map (M.map_default (l, empty) (insert (ls, data)))

fun insert_safe args hoptt = insert args hoptt handle INSERT => hoptt

local
exception EMPTY
fun check_empty hoptt = if is_empty hoptt then raise EMPTY else hoptt
fun del [] cut hoptt =
      delete_data hoptt |> cut ? (map_map (K M.empty)) |> check_empty
  | del (l :: ls) cut hoptt =
      let val hoptt = map_map (M.map_entry l (del ls cut)) hoptt
        handle M.SAME => raise DELETE
          | EMPTY => map_map (M.delete l) hoptt
      in check_empty hoptt end
in

fun delete word hoptt = del word false hoptt handle EMPTY => empty
fun cut word hoptt = del word true hoptt handle EMPTY => empty

end

fun delete_safe p hoptt = delete p hoptt handle DELETE => hoptt
fun cut_safe p hoptt = cut p hoptt handle DELETE => hoptt

local
fun map_aux [] map_below f hoptt =
      map_data f hoptt |> map_below ? (map_map (M.map (map_aux [] true f |> K)))
  | map_aux (l :: ls) map_below f hoptt =
      map_map (M.map_entry l (map_aux ls map_below f)) hoptt
      handle M.SAME => hoptt
in

fun map word = map_aux word false
fun map_below word = map_aux word true

end

fun join f (HOption_Tree (data1, m1), HOption_Tree (data2, m2)) =
  HOption_Tree (f (data1, data2), M.join (join f |> K) (m1, m2))

end