(*  Title:      Logger/Data_Structures/binding_tree.ML
    Author:     Kevin Kappelmann

A hierarchical tree indexed on bindings.
*)
signature BINDING_TREE =
sig
  type 'a binding_tree
  val empty : 'a binding_tree
  val is_empty : 'a binding_tree -> bool

  val lookup: 'a binding_tree -> binding -> 'a option

  exception INSERT
  (*raises INSERT if the entry is already set*)
  val insert : (binding * 'a) -> 'a binding_tree -> 'a binding_tree
  val insert_safe : (binding * 'a) -> 'a binding_tree -> 'a binding_tree

  exception DELETE
  (*deletes entry; raises DELETE if the corresponding entry is not set*)
  val delete : binding -> 'a binding_tree -> 'a binding_tree
  val delete_safe : binding -> 'a binding_tree -> 'a binding_tree
  (*like delete but also cuts off all subtrees*)
  val cut : binding -> 'a binding_tree -> 'a binding_tree
  (*does not cut subtrees if entry is not set*)
  val cut_safe : binding -> 'a binding_tree -> 'a binding_tree

  (*maps entry*)
  val map : binding -> ('a option -> 'a option) -> 'a binding_tree -> 'a binding_tree
  (*maps entry and all entries in subtrees*)
  val map_below : binding -> ('a option -> 'a option) -> 'a binding_tree -> 'a binding_tree

  val join : ('a option * 'a option -> 'a option) -> 'a binding_tree * 'a binding_tree ->
    'a binding_tree
  val merge : 'a binding_tree * 'a binding_tree -> 'a binding_tree
end

structure Binding_Tree : BINDING_TREE =
struct

structure HOT = HOption_Tree(TableMap(Symtab))

fun full_path_of binding = (Binding.path_of binding |> map fst) @ [Binding.name_of binding]

type 'a binding_tree = 'a HOT.hoption_tree
val empty = HOT.empty
val is_empty = HOT.is_empty
fun lookup bt = HOT.lookup bt o full_path_of
exception INSERT = HOT.INSERT
fun insert p = HOT.insert (apfst full_path_of p)
fun insert_safe p = HOT.insert_safe (apfst full_path_of p)
exception DELETE = HOT.DELETE
fun delete binding = HOT.delete (full_path_of binding)
fun delete_safe  binding = HOT.delete_safe (full_path_of binding)
fun cut binding = HOT.cut (full_path_of binding)
fun cut_safe  binding = HOT.cut_safe (full_path_of binding)
fun map binding = HOT.map (full_path_of binding)
fun map_below binding = HOT.map_below (full_path_of binding)
val join = HOT.join

fun merge opttp = join (fn (data1, data2) => if is_none data1 then data2 else data1) opttp

end
