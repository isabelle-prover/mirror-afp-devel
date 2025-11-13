(*  Title:      leftist_heap.ML
    Author:     Lawrence C Paulson and Markus Wenzel and Kevin Kappelmann

Note: This is a modified version of heap.ML from Pure supporting polymorphic
elements.

Heaps over linearly ordered types.  See also Chris Okasaki: "Purely
Functional Data Structures" (Chapter 3), Cambridge University Press,
1998.
*)
functor Leftist_Heap(type prio; val ord: prio ord): PRIORITY_QUEUE =
struct

(* datatype heap *)

type prio = prio
datatype 'a t = Empty | Heap of int * (prio * 'a) * 'a t * 'a t

(* empty heaps *)

val empty = Empty

fun is_empty Empty = true
  | is_empty (Heap _) = false

(* build heaps *)

local

fun rank Empty = 0
  | rank (Heap (r, _, _, _)) = r;

fun heap x a b =
  if rank a >= rank b then Heap (rank b + 1, x, a, b)
  else Heap (rank a + 1, x, b, a);

in

fun merge (h, Empty) = h
  | merge (Empty, h) = h
  | merge (h1 as Heap (_, px1 as (p1, _), a1, b1),
      h2 as Heap (_, px2 as (p2, _), a2, b2)) =
      (case ord (p1, p2) of
        GREATER => heap px2 a2 (merge (h1, b2))
      | _ => heap px1 a1 (merge (b1, h2)))

fun insert x h = merge (Heap (1, x, Empty, Empty), h);

end;


(* minimum element *)

fun min Empty = NONE
  | min (Heap (_, x, _, _)) = SOME x

fun delete_min Empty = NONE
  | delete_min (Heap (_, _, a, b)) = SOME (merge (a, b))

fun min_elem h = min h |> Option.map (fn m => (m, the (delete_min h)))

end