signature HASHABLE = sig
  type key
  type hash
  include BINARY where type from = key
  val eq: key * key -> bool
  val hash: key -> int
end

signature UNIONABLE = sig
  type zone
  include BINARY where type from = zone
  val subsumption: zone -> zone -> bool
end

signature MONO_PASSED_SET = sig
  structure Key : HASHABLE
  structure Zone : UNIONABLE
  type passed_set
  include BINARY where type from = passed_set

  type waiting = Key.key Unsynchronized.ref *
                 Zone.zone Unsynchronized.ref

  val mkTable: int -> passed_set
  val insert_p: passed_set -> (Key.key * Zone.zone) ->
                waiting option

  val insert_p': passed_set -> (Key.key * Zone.zone) ->
                 passed_set

  val push: passed_set -> (Key.key * Zone.zone) ->
            passed_set
  val pop: passed_set -> Key.key -> unit

  val exists: (Zone.zone -> Zone.zone -> bool) -> passed_set ->
              Key.key * Zone.zone -> bool

  val kv_list: passed_set -> (Key.key * Zone.zone list) list
  val size_tbl: passed_set -> int
  val n_buckets: passed_set -> int
  val fold_until: ('b -> bool) -> (Key.key * Zone.zone * 'b -> 'b) ->
                  passed_set -> 'b -> 'b

  val fold: (Key.key * Zone.zone list * 'b -> 'b) ->
            'b -> passed_set -> 'b
  val n_states: passed_set -> int
end

functor MonoPassedSet(structure Key : HASHABLE
                      structure Zone : UNIONABLE) : MONO_PASSED_SET = struct
structure Key = Key
structure Zone = Zone

type table = (Key.key Unsynchronized.ref,
              Zone.zone Unsynchronized.ref list) HashTableRep.table

type waiting = Key.key Unsynchronized.ref *
               Zone.zone Unsynchronized.ref

datatype passed_set = Passed of
                  {
                    table: table Unsynchronized.ref,
                    n_buckets: int Unsynchronized.ref,
                    n_states: int Unsynchronized.ref
                  }
type from = passed_set
type to = Word8Vector.vector

fun mkTable n = Passed
                    {
                      table = Unsynchronized.ref (HashTableRep.init n),
                      n_buckets = Unsynchronized.ref 0,
                      n_states = Unsynchronized.ref 0
                    }

local
  open Unsynchronized
  open HashTableRep
in


(* Grows a table if needed *)
fun grow_cond (Passed{table, n_buckets, ...}) =
    let
      val arr = ! table
      val sz = Array.length arr
    in
      if ! n_buckets >= sz then table := HashTableRep.grow_tbl (arr, sz)
      else ()
    end


fun subsume' p zone =
    List.exists (! #> p zone)

fun subsume zone =
    subsume' Zone.subsumption zone

(* Inserts a key and zone into a passed waiting list if it is discarded it
   returns NONE Other wise it adds the zone to the passed Htbl and returns the
   reference for the waiting queue *)
fun insert p (tbl as Passed{table, n_buckets, n_states}) (key, zone) =
    let
      val arr = ! table
      val sz = Array.length arr
      val hash = Key.hash key
      val indx = index (hash, sz)
      fun empty k v =
          let val r as (k, zone) = (ref k, ref v) in
            (
              Array.update
                  (
                    arr,
                    indx,
                    B (hash, (k, [zone]), Array.sub(arr, indx))
                  );
              inc n_buckets;
              inc n_states;
              grow_cond tbl;
              SOME (r, NONE)
            )
          end

      fun non_empty (B (h, (k, union), rs)) key zone =
          if subsume' p zone union then NONE
          else
            (let
              val w_ref as (_, zone) = (k, ref zone)
              val new_bucket = B (h, (k, zone :: union), rs) |> SOME
            in
               SOME (w_ref, new_bucket)
            end)

      (* Why check for same hash ? we check for an equal key anyway *)
      fun lookahead bucket =
          case bucket of
              Empty => empty key zone |
              (b as B (h, (k, union), rs)) => (
                if hash = h andalso Key.eq (key, ! k) then non_empty b key zone
                else
                  case lookahead rs of
                      NONE => NONE |
                      SOME (r, NONE) => SOME (r, NONE) |
                      SOME (r, SOME rest) => (let
                                               val b' = B (h, (k, union), rest)
                                             in
                                               SOME (r, SOME b')
                                             end)
              )
    in
      case lookahead (Array.sub (arr, indx)) of
          NONE => NONE |
          SOME (r, NONE) => SOME r |
          SOME (r, SOME b) => (inc n_states; Array.update (arr, indx, b); SOME r)
    end
end

fun insert_p' p (tbl as Passed{table, n_buckets, n_states}) kv =
    insert p tbl kv |> (K tbl)


val just_insert = insert_p' (K (K true))
val push = just_insert

val insert_p' = insert_p' Zone.subsumption
val insert_p = insert Zone.subsumption

local
  open HashTableRep
  open Unsynchronized
in

fun pop (Passed{table, n_buckets, n_states}) k = let
        val arr = !table
        val sz = Array.length arr
        val hash = Key.hash k
        val indx = index (hash, sz)
        fun look bucket =
            case bucket of
                Empty => Empty |
                B (h, (k', union), rs) =>
                if hash = h andalso Key.eq (k, ! k') then
                  (case union of
                       [] => Exn.impossible () |
                       [ref D] => (dec n_buckets; rs) |
                      (_::DS) => B (h, (k', DS), rs))
                else let val r' = look rs in B (h, (k', union), r') end
        val bucket = look (Array.sub (arr, indx))
    in
      (dec n_states; Array.update (arr, indx, bucket))
    end

fun exists p (Passed{table, ...}) (k, zone) =
    let
      val arr = ! table
      val sz = Array.length arr
      val hash = Key.hash k
      val indx = index (hash, sz)
      fun lookup' bucket =
          case bucket of
              Empty => false |
              (b as B (h, (k', union), rs)) =>
              if hash = h andalso Key.eq (k, ! k')
              then subsume' p zone union
              else lookup' rs
    in
      lookup' (Array.sub (arr, indx))
    end

end

local open Unsynchronized in

fun fold_until p f (Passed{table, ...}) =
    let
      fun inner (ref l) (ref dbm, acc) = f (l, dbm, acc)
    in
      flip
          (HashTableRep.fold_until p
                               (fn ((l, dbms), acc') =>
                                   foldl_until p (inner l) acc' dbms))
          (!table)
    end

fun fold_ref_list f =
    List.foldl (fn (ref x, acc) => f (x, acc))

fun fold f acc (Passed{table, ...}) =
    HashTableRep.fold_until
        (K false)
        (fn ((ref l, dbms), acc') => f (l, fold_ref_list (op ::) [] dbms, acc'))
        acc
        (! table)

fun kv_list passed =
    fold (fn (l, dbms, acc) => (l, dbms) :: acc)
         []
         passed

fun n_states (Passed{n_states, ...}) = ! n_states

fun n_buckets (Passed{n_buckets, ...}) = ! n_buckets

fun size_tbl (Passed{table, ...}) = Array.length (! table)

fun serialize_union dbms =
    map Zone.serialize dbms

fun one_union (l, dbms, acc) =
    let
      val length = dbms |> length |> SerInt.serialize
      val loc = Key.serialize l
    in
      dbms
      |> serialize_union
      |> cons length
      |> cons loc
      |> Word8Vector.concat
      |> flip cons acc
    end

fun serialize passed =
    let
      val n_buckets = passed  |> n_buckets |> SerInt.serialize
      val states = fold one_union [] passed
    in
      states |> cons n_buckets |> Word8Vector.concat
    end
end
end

functor PolyToMonoPassed(structure Key : HASHABLE
                         structure Zone : UNIONABLE)
        : MONO_PASSED_SET
= struct
structure Key = Key
structure Zone = Zone
open PolyPassedSet
type passed_set = (Key.key, Zone.zone) PolyPassedSet.hash_table
type from = passed_set
type to = Word8Vector.vector
type waiting = (Key.key, Zone.zone) PolyPassedSet.waiting


fun mkTable n = PolyPassedSet.mkTable Key.hash Key.eq n

fun insert_p tbl = PolyPassedSet.insert_p Zone.subsumption tbl
fun insert_p' tbl = PolyPassedSet.insert_p' Zone.subsumption tbl
fun push tbl = PolyPassedSet.push tbl
fun pop tbl = PolyPassedSet.pop tbl
fun exists p = PolyPassedSet.exists p

fun serialize_union dbms =
    map Zone.serialize dbms

fun one_union (l, dbms, acc) =
    let
      val length = dbms |> length |> SerInt.serialize
      val loc = Key.serialize l
    in
      dbms
      |> serialize_union
      |> cons length
      |> cons loc
      |> Word8Vector.concat
      |> flip cons acc
    end

fun serialize passed =
    let
      val n_buckets = passed  |> n_buckets
      (* val _ = print ("len of state space: " ^ (Int.toString n_buckets) ^ "\n") *)
      val n_buckets_ser = n_buckets |> SerInt.serialize
      val states = fold one_union [] passed
    in
      states |> cons n_buckets_ser |> Word8Vector.concat
    end

end
