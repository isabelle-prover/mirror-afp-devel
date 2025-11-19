(*  Title:      priority_queue.ML
    Author:     Lawrence C Paulson and Markus Wenzel and Kevin Kappelmann

Note: This is a modified version of heap.ML from Pure supporting polymorphic
content.
*)
signature PRIORITY_QUEUE =
sig
  type prio
  type 'a t
  val empty: 'a t
  val is_empty: 'a t -> bool
  val insert: prio * 'a -> 'a t -> 'a t
  val min: 'a t -> (prio * 'a) option
  val delete_min: 'a t -> 'a t option
  val min_elem: 'a t -> ((prio * 'a) * 'a t) option
  val merge: 'a t * 'a t -> 'a t
end
