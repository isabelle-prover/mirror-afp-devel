signature MONO_PW_LIST = sig
  structure Key : HASHABLE
  structure Zone : UNIONABLE

  type waiting = Key.key Unsynchronized.ref *
                 Zone.zone Unsynchronized.ref
  type pwlist
  val make: int -> pwlist
  val insert: (Key.key * Zone.zone -> bool)
              -> pwlist -> Key.key * Zone.zone
              -> pwlist * bool
  val get: pwlist -> (waiting * pwlist) option
  val n_buckets: pwlist -> int
  val kv_list: pwlist -> (Key.key * Zone.zone list) list
  val fold_until: ('b -> bool) -> (Key.key * Zone.zone * 'b -> 'b) ->
                  pwlist -> 'b -> 'b
end

functor PassedToPWList(structure P : MONO_PASSED_SET)
        : MONO_PW_LIST where type Key.key = P.Key.key
                       where type Zone.zone = P.Zone.zone

= struct
structure Key = P.Key
structure Zone = P.Zone
structure PassedSet = P

type waiting = Key.key Unsynchronized.ref *
               Zone.zone Unsynchronized.ref

type pwlist = PassedSet.passed_set * waiting list

fun make n = (PassedSet.mkTable n, [])

fun insert pred (pw as (p, w)) state =
    case PassedSet.insert_p p state of
        NONE => (pw, false) |
        SOME r => ((p, r::w), pred state)

fun get (p, w) =
    case w of
        [] => NONE |
        (w::ws) => SOME (w, (p, ws))

fun kv_list (p, _) = PassedSet.kv_list p

fun fold_until p f (passed, _) =
    PassedSet.fold_until p f passed

fun n_buckets (p, _) = PassedSet.n_buckets p
end

functor MonoPWList(structure Key : HASHABLE
                   structure Zone : UNIONABLE)
        : MONO_PW_LIST = PassedToPWList(
  structure P = MonoPassedSet(structure Key = Key
                              structure Zone = Zone)
)
