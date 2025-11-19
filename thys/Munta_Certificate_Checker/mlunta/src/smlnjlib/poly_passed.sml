(*
--------------------------------------------------------------------------------

This file incorporates work covered by the following copyright and permission notice:

STANDARD ML OF NEW JERSEY COPYRIGHT NOTICE, LICENSE AND DISCLAIMER.

Copyright (c) 1989-2002 by Lucent Technologies

Permission to use, copy, modify, and distribute this software and its
documentation for any purpose and without fee is hereby granted,
provided that the above copyright notice appear in all copies and that
both the copyright notice and this permission notice and warranty
disclaimer appear in supporting documentation, and that the name of
Lucent Technologies, Bell Labs or any Lucent entity not be used in
advertising or publicity pertaining to distribution of the software
without specific, written prior permission.

Lucent disclaims all warranties with regard to this software,
including all implied warranties of merchantability and fitness. In no
event shall Lucent be liable for any special, indirect or
consequential damages or any damages whatsoever resulting from loss of
use, data or profits, whether in an action of contract, negligence or
other tortious action, arising out of or in connection with the use
or performance of this software.

--------------------------------------------------------------------------------

Copyright notice of the original file:

COPYRIGHT (c) 1993 by AT&T Bell Laboratories.

ORIGINAL AUTHOR:  John Reppy
                  AT&T Bell Laboratories
                  Murray Hill, NJ 07974
                  jhr@research.att.com
*)

structure PolyPassedSet : POLY_PASSED_SET =
struct
structure HTRep = HashTableRep

type hash = int

type ('key, 'zone) waiting = 'key Unsynchronized.ref *
                           'zone Unsynchronized.ref

datatype ('key, 'zone) hash_table = Htbl of {
           hash : 'key -> int,
           key_eq : ('key * 'key) -> bool,
           table : ('key Unsynchronized.ref,
                    'zone Unsynchronized.ref list)
                       HTRep.table Unsynchronized.ref,
           n_buckets : int ref,
           n_states: int ref
         }

(* Create a new table; the int is a size hint and the exception
 * is to be raised by find.
 *)
open Unsynchronized

fun mkTable hash eq sizeHint = Htbl{
      hash = hash,
      key_eq = eq,
      table = ref (HTRep.init sizeHint),
      n_buckets = ref 0,
      n_states = ref 0
    }

(* Grows a table if needed *)
fun grow_cond (Htbl{table, n_buckets, ...}) =
    let
      val arr = ! table
      val sz = Array.length arr
    in
      if ! n_buckets >= sz then table := HTRep.grow_tbl (arr, sz)
      else ()
    end

(* Creates a waiting list reference *)
fun mk_waiting k v = (ref k, ref v)


(* Inserts a key and zone into a passed waiting list if it is discarded it
       returns NONE Other wise it adds the zone to the passed Htbl and returns the
       reference for the waiting queue *)
fun insert_p p (tbl as Htbl{hash, key_eq, table, n_buckets, n_states})
             (key, zone) =
    let
      val arr = ! table
      val sz = Array.length arr
      val hash = hash key
      val indx = HTRep.index (hash, sz)
      open HTRep
      fun ins_new k v =
          let
            val r as (k, zone) = mk_waiting k v
          in
            (
              Array.update(arr, indx, B (hash, (k, [zone]),
                                         Array.sub(arr, indx)));
              inc n_states;
              inc n_buckets;
              grow_cond tbl;
              SOME (r, NONE)
            )
          end

      fun ins_non_empty (B (h, (k, union), rs)) key zone =
          if List.exists
                 (fn ref zone' => p zone zone') union then NONE
          else
            (let
              val zone_ref = ref zone
              val b' = B (h, (k, zone_ref :: union), rs)
            in
              SOME ((k, zone_ref), SOME b')
            end)

      (* Why check for same hash ? we check for an equal key anyway *)
      fun lookahead bucket =
          case bucket of
              Empty => ins_new key zone |
              (b as B (h, (k, union),rs)) => (
                if hash = h andalso key_eq (key, ! k)
                then ins_non_empty b key zone
                else
                  case lookahead rs of
                      NONE => NONE |
                      SOME (r, NONE) => SOME (r, NONE) |
                      SOME (r, SOME rest) =>
                      SOME (r, SOME (B (h, (k, union), rest)))
              )
    in
      case lookahead (Array.sub (arr, indx)) of
          NONE => NONE |
          SOME (r, NONE) => SOME r |
          SOME (r, SOME b) => (inc n_states; Array.update (arr, indx, b); SOME r)
    end

fun insert_p' p (tbl as Htbl{hash, key_eq, table, n_buckets, n_states})
              (key, zone) =
    let
      val arr = ! table
      val sz = Array.length arr
      val hash = hash key
      val indx = HTRep.index (hash, sz)
      open HTRep
      fun ins_new k v =
          let
            val r as (k, zone) = mk_waiting k v
            val bucket = B (hash, (k, [zone]),
                            Array.sub(arr, indx))
          in
            (
              Array.update (arr, indx, bucket);
              inc n_states;
              inc n_buckets;
              grow_cond tbl;
              NONE
            )
          end

      fun ins_non_empty (B (h, (k, union), rs)) key zone =
          if List.exists (fn ref zone' => p zone zone') union
          then NONE
          else
            let
              val zone_ref = ref zone
              val b' = B (h, (k, zone_ref :: union), rs)
            in
              SOME b'
            end
      (* Why check for same hash ? we check for an equal key anyway this
                 would assume the compiler knows that it would be faster *)
      fun lookahead bucket =
          case bucket of
              Empty => ins_new key zone |
              (b as B (h, (k, union),rs)) => (
                if hash = h andalso key_eq (key, ! k)
                then ins_non_empty b key zone
                else case lookahead rs of
                         NONE => NONE |
                         SOME rs => SOME (B (h, (k, union), rs))
              )
    in
      case lookahead (Array.sub (arr, indx)) of
          NONE => tbl |
          SOME b => (inc n_states; Array.update (arr, indx, b); tbl)
    end

(* XXX: Could be a bottle neck but for now leave it *)
fun push tbl entry = (insert_p (true |> K |> K) tbl entry; tbl)

fun pop (Htbl{hash, key_eq, table, n_buckets, n_states}) k = let
  val arr = !table
  val sz = Array.length arr
  val hash = hash k
  open HTRep
  val indx = index (hash, sz)
  fun look bucket =
      case bucket of
          Empty => Empty |
          B (h, (k', union), rs) =>
          if hash = h andalso key_eq (k, ! k') then
            (case union of
                 [] => Exn.impossible () |
                 [ref D] => (dec n_buckets; rs) |
                 ((ref D)::DS) => B (h, (k', DS), rs))
          else let val r' = look rs in B (h, (k', union), r') end
  val bucket = look (Array.sub (arr, indx))
in
  (
    dec n_states;
    Array.update (arr, indx, bucket)
  )
end

fun exists p (Htbl{hash, key_eq, table, n_buckets, ...}) (k, zone) =
    let
      open HTRep
      val arr = ! table
      val sz = Array.length arr
      val hash = hash k
      val indx = HTRep.index (hash, sz)
      fun lookup' bucket =
          case bucket of
              Empty => false |
              (b as B (h, (k', union), rs)) =>
              if hash = h andalso key_eq (k, ! k') then
                (List.exists (fn ref zone' => p zone zone') union)
              else lookup' rs
    in
      lookup' (Array.sub (arr, indx))
    end

fun fold_until p f (Htbl{table, ...}) =
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

fun fold f acc (Htbl{table, ...}) =
    HashTableRep.fold_until
        (K false)
        (fn ((ref l, dbms), acc') => f (l, fold_ref_list (op ::) [] dbms, acc'))
        acc
        (! table)

(* Creates a key value list of the table *)
local open Unsynchronized in
fun kv_list (Htbl{table, ...}) =
    HTRep.fold_until (K false)
                     (fn ((ref l, dbms), kvs) => (l, map ! dbms) :: kvs)
                     []
                     (! table)
end
(* Returns size of the table *)
fun size_tbl (Htbl{table, ...}) = Array.length (! table)

(* Returns n_buckets of the Htbl *)
fun n_buckets (Htbl{n_buckets, ...}) = ! n_buckets
fun n_states tbl = flip (fold_until (K false) (fn (_, _, i) => i + 1)) 0 tbl
end (* PolyPassedSet *)
