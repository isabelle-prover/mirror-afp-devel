(*
--------------------------------------------------------------------------------

This file incorporates work covered by the following copyright and permission notice:

STANDARD ML OF NEW JERSEY COPYRIGHT NOTICE, LICENSE AND DISCLAIMER.

Copyright (c) 1989-2002 by Lucent Technologies

Permission to use, copy, modify, and distribute this software and its
documentation for any purpose and without fee is hereby granted,
provided that the above copyright notice appear in all copies and that
both the copyright notice and this permission nkeyotice and warranty
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
COPYRIGHT (c) 1996 AT&T Research.

ORIGINAL AUTHOR:  John Reppy
                  AT&T Bell Laboratories
                  Murray Hill, NJ 07974
                  jhr@research.att.com
*)

(* Signature of the Hashtable Representation *)
signature HASH_TABLE_REP = sig
  type hash
  datatype ('key, 'zone) bucket =
           Empty |
           B of hash * ('key * 'zone) * ('key, 'zone) bucket

  type ('key, 'zone) table
  (* Initialize array of Table of size n *)
  val init : int -> ('key, 'zone) table

  val index: (int * int) -> int

  (* Copy one table with hashes into another *)
  val copy : ('a, 'zone) table * int -> ('a, 'zone) table * int -> unit

  val fold_until : ('b -> bool) ->
                   (('key * 'zone) * 'b -> 'b) ->
                   'b -> ('key, 'zone) table -> 'b

  (* grow table of size n to size n*2 *)
  val grow_tbl : (('key, 'zone) table * int) -> ('key, 'zone) table

  (* returns key value list *)
  val kv_list: ('key, 'zone) table -> ('key * 'zone) list
end

structure HashTableRep : HASH_TABLE_REP = struct
type hash = int
datatype ('key, 'zone) bucket =
         Empty |
         B of hash * ('key * 'zone) * ('key, 'zone) bucket

type ('key, 'zone) table = ('key, 'zone) bucket array


local
    fun andb_ x y = Word.toInt (Word.andb (Word.fromInt x, Word.fromInt y));
    fun lshift_ x y = Word.toInt (Word.<< (Word.fromInt x, Word.fromInt y));
in
    fun index (i, sz) = andb_ i (sz-1)

    (* find smallest power of 2 (>= 32) that is >= n *)
    fun roundUp n =
        let fun f i = if (i >= n) then i else f (lshift_ i 1)
        in f 32 end
end;


fun init' n = Array.array (n, Empty)
fun init n = Array.array(roundUp n, Empty)

(* Copy arr h, k into arr' h, k *)
fun copy (arr, sz) (arr', sz') =
    let
      fun index' h = index (h, sz')
      fun copy' new_sz new_arr bs =
                case bs of
                    Empty => () |
                    (B (h,kv,rest)) => (
                      let val ix = index' h in
                        (
                          Array.update (new_arr, ix,
                                        B (h, kv, Array.sub(new_arr, ix)));
                          copy' new_sz new_arr rest
                        )
                      end
                    )
      fun bucket n =
          if n >= sz then ()
          else (copy' sz' arr' (Array.sub(arr, n)); bucket (n+1))
    in
      bucket 0
    end

(* conditionally grow a table *)
fun grow_tbl (arr, sz) = let
  val new_sz = sz+sz
  val new_arr = init new_sz
in
  (
    copy (arr, sz) (new_arr, new_sz);
    new_arr
  )
end

(* folds over the items in a bucket*)
fun fold_bucket f acc bucket =
    case bucket of
            Empty => acc |
            B (h, (k, v), rs) => fold_bucket f (f ((h, (k, v)), acc)) rs

(* Fold over a table *)
fun fold_tbl f acc tbl =
  Array.foldl
    (fn (b, acc') => (fold_bucket f acc' b)) acc tbl

fun fold_until_bucket p f (bucket, acc) =
    case bucket of
        Empty => acc |
        B (_, k_union, rs) => let val acc' = f (k_union, acc) in
                               if p acc' then acc'
                               else fold_until_bucket p f (rs, acc') end

fun fold_until_arr p f init tbl =
    let
      val len = Array.length tbl
      fun inner i acc =
          if i >= len then acc
          else let val acc' = f (Array.sub (tbl, i), acc) in
                 if p acc' then acc'
                 else inner (i + 1) acc'
               end
    in
      inner 0 init
    end

fun fold_until p f =
    fold_until_arr p (fold_until_bucket p f)

(* Returns a list of all kv_pairs *)
fun kv_list arr =
    Array.foldl
        (fn (b, acc) =>
            (fold_bucket (fn ((_, kv), acc') => kv :: acc') [] b) @ acc)
        [] arr

end (* HashTableRep *)
