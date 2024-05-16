(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* provide an inputLine function à la old version of the Basis Library *)
structure StrictCBasics =
struct
  fun inputLine istr = case TextIO.inputLine istr of
                         NONE => ""
                       | SOME s => s

  (*
  val inputLine = TextIO.inputLine
  *)

fun measure_ord f (x,y) = int_ord (f x, f y)
fun inv_img_ord f c (x,y) = c (f x, f y)

end;

open StrictCBasics

signature FLIP_TABLE =
sig
  type key
  type 'a table
  val flip : key list table -> key list table
end
functor FlipTable(structure Table : TABLE) : FLIP_TABLE =
struct
  type key = Table.key
  type 'a table = 'a Table.table
  fun flip table = let
    fun foldthis (k:key,elems:key list) acc = acc |>
        fold (fn e => fn acc => Table.cons_list (e,k) acc) elems
  in
    Table.fold foldthis table Table.empty
  end
end
local
  structure FlipSymTab = FlipTable(structure Table = Symtab)
in
  val flip_symtab = FlipSymTab.flip
end
