(*  Title:      Zippy/imperative_union_find.ML
    Author:     Kevin Kappelmann

Adapted from https://github.com/standardml/cmlib, MIT license.
*)
signature IMPERATIVE_UNION_FIND =
sig
  type 'a set
  val new : 'a -> 'a set
  val union : ('a * 'a -> 'a) -> 'a set -> 'a set -> unit
  val eq : 'a set * 'a set -> bool
  val representative : 'a set -> 'a
end

structure Imperative_Union_Find : IMPERATIVE_UNION_FIND =
struct

datatype 'a state = Root of 'a * int | Child of 'a set
withtype 'a set = 'a state Unsynchronized.ref

fun new label = Unsynchronized.ref (Root (label, 0))

fun root set = case !set of
    Root _ => set
  | Child parent =>
      let val ancestor = root parent
      in set := Child ancestor; ancestor end

fun union merge_label set1 set2 = case (root set1, root set2) of
  (ancestor1 as Unsynchronized.ref (Root (label1, rank1)),
  ancestor2 as Unsynchronized.ref (Root (label2, rank2))) =>
    if ancestor1 = ancestor2 then ()
    else if rank1 < rank2 then
      (ancestor1 := Child ancestor2; ancestor2 := Root (merge_label (label2, label1), rank2))
    else if rank1 > rank2 then
      (ancestor2 := Child ancestor1; ancestor1 := Root (merge_label (label1, label2), rank1))
    else (* rank1 = rank2 *)
      (ancestor2 := Child ancestor1; ancestor1 := Root (merge_label (label1, label2), rank1+1))
  | _ => (* root always returns a Root state *) error "impossible"

fun eq (set1, set2) = root set1 = root set2

fun representative set = case !(root set) of
    Root (label, _) => label
  | _ => error "invariant"

end
