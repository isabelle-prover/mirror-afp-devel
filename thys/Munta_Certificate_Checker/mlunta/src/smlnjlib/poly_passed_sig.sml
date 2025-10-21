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

signature POLY_PASSED_SET = sig
  type hash = int
  type ('key, 'zone) waiting
  (* type of hash table mapping 'key to 'zone *)
  type ('key, 'zone) hash_table


  val mkTable: ('key -> hash) -> (('key * 'key) -> bool) -> int
               -> ('key, 'zone) hash_table

  val insert_p: ('zone -> 'zone -> bool) -> ('key, 'zone) hash_table
                -> ('key * 'zone) -> ('key, 'zone) waiting option

  val insert_p': ('zone -> 'zone -> bool) -> ('key, 'zone) hash_table ->
                 ('key * 'zone) -> ('key, 'zone) hash_table

  val push: ('key, 'zone) hash_table -> ('key * 'zone) ->
                    ('key, 'zone) hash_table
  val pop: ('key, 'zone) hash_table -> 'key -> unit

  val exists: ('zone -> 'zone -> bool)
                     -> ('key, 'zone) hash_table
                     -> ('key * 'zone) -> bool

  val kv_list: ('key, 'zone) hash_table ->
                ('key * 'zone list) list
  val size_tbl: ('key, 'zone) hash_table -> int
  val n_buckets:  ('key, 'zone) hash_table -> int
  val n_states: ('key, 'zone) hash_table -> int

  val fold_until: ('b -> bool) ->
                  ('key * 'zone * 'b -> 'b) ->
                  ('key, 'zone) hash_table -> 'b -> 'b
  val fold: ('key * 'zone list * 'b -> 'b) -> 'b ->
            ('key, 'zone) hash_table -> 'b
end (* HASH_TABLE *)
