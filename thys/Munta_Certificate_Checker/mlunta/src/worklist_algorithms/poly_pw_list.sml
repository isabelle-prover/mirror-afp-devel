(* XXX: Do we really need thos references ? or shouldn't it be enough to just have refs in waiting *)
signature POLY_PW_LIST = sig
  type hash = int
  type ('key, 'zone) t
  type ('key, 'zone) waiting
  val make: ('key -> hash) -> ('key * 'key -> bool) -> int -> ('key, 'zone) t
  val insert:
      ('key * 'zone -> bool) ->
      ('zone -> 'zone -> bool) ->
      ('key, 'zone) t -> 'key * 'zone ->
      ('key, 'zone) t * bool
  val get: ('key, 'zone) t -> (('key, 'zone) waiting * ('key, 'zone) t) option
  val n_buckets: ('key, 'zone) t -> int
  val items_pw: ('key, 'zone) t -> ('key * 'zone list) list
  val fold_until: ('b -> bool) -> ('key * 'zone * 'b -> 'b) ->
                  ('key, 'zone) t -> 'b -> 'b
end


structure PolyPWList : POLY_PW_LIST = struct
type hash = int

type ('key, 'zone) waiting = ('key, 'zone) PolyPassedSet.waiting
type ('key, 'zone) t = ('key, 'zone) PolyPassedSet.hash_table *
                       ('key, 'zone) waiting list
open PolyPassedSet

(* Creates a new PWList *)
fun make hashf keyeq sz = (mkTable hashf keyeq sz, [])

(* Get number of items in passed *)
fun n_buckets (p, _) = PolyPassedSet.n_buckets p


(* Inserts a new symbolic state into the PWList *)
fun insert pred ssetp (pw as (p, w)) (l, D) =
    case insert_p ssetp p (l, D) of
            NONE => (pw, false) |
            SOME r => ((p, r::w), pred (l, D))

(* Pops of a state from the waiting list *)
fun get (p, w) =
    case w of
            [] => NONE |
            (w::ws) => SOME (w, (p, ws))

(* Returns the items in the PWList Hashtable *)
fun items_pw (p, _) = kv_list p

(* Folds over passed until the accumulator satisfies pred *)
fun fold_until pred f (p, _) =
    PolyPassedSet.fold_until pred f p
end
