(* SPDX-License-Identifier: HPND *)

(* Copyright (C) 1999-2002 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-1999 NEC Research Institute.
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * Please see the file MLton-LICENSE for license information.
 *)
signature REGION =
   sig

      type t

      val <= : t * t -> bool
      val append: t * t -> t
      val bogus: t
      val compare: t * t -> order
      val equals: t * t -> bool
      val extendRight: t * SourcePos.t -> t
      val left: t -> SourcePos.t option
      val list: 'a list * ('a -> t) -> t
      val make: {left: SourcePos.t, right: SourcePos.t} -> t
      val right: t -> SourcePos.t option
      val toString: t -> string

      structure Wrap:
         sig
            type region
            type 'a t
            val region: 'a t -> region
            val node: 'a t -> 'a
            val makeRegion: 'a * region -> 'a t
            val makeRegion':  'a * SourcePos.t * SourcePos.t -> 'a t
            val dest: 'a t -> 'a * region
            val map_node: ('a -> 'a) -> ('a t -> 'a t)
         end
      sharing type Wrap.region = t
   end


structure Region: REGION =
struct

datatype t =
   Bogus
 | T of {left: SourcePos.t,
         right: SourcePos.t}

val bogus = Bogus

local
   fun make f r =
      case r of
         Bogus => NONE
       | T r => SOME (f r)
in
   val left = make #left
   val right = make #right
end

val extendRight =
   fn (Bogus, _) => Bogus
    | (T {left, ...}, right) => T {left = left, right = right}


val prettyRegion =
   fn Bogus => Pretty.str "Bogus"
    | T {left, right} =>
         Pretty.strs [SourcePos.posToString left, "-", 
            SourcePos.posToString right, "in " ^ quote (SourcePos.file left)]

val toString = Pretty.string_of o prettyRegion

val make = T

val append =
   fn (Bogus, r) => r
    | (r, Bogus) => r
    | (T {left, ...}, T {right, ...}) => T {left = left, right = right}

fun list (xs, reg) = List.foldl (fn (x, r) => append (reg x, r)) Bogus xs

fun compare (r, r') =
   case (left r, left r') of
      (NONE, NONE) => EQUAL
    | (NONE, _) => LESS
    | (_, NONE) => GREATER
    | (SOME p, SOME p') => SourcePos.compare (p, p')

fun equals (r, r') = compare (r, r') = EQUAL

fun r <= r' =
   case compare (r, r') of
      EQUAL => true
    | GREATER => false
    | LESS => true

structure Wrap =
   struct
      type region = t
      datatype 'a t = T of {node: 'a,
                            region: region}

      fun node (T {node, ...}) = node
      fun region (T {region, ...}) = region
      fun makeRegion (node, region) = T {node = node, region = region}
      fun makeRegion' (node, left, right) = T {node = node,
                                               region = make {left = left,
                                                              right = right}}

      fun dest (T {node, region}) = (node, region)
      fun map_node f (T {node, region}) = T {node=f node, region=region}
   end

val _ =
  ML_system_pp (fn depth => fn pretty => fn (region:t) =>
    if print_mode_active SourcePos.show_c_parser_positions 
    then Pretty.to_polyml (prettyRegion region)
    else Pretty.to_polyml (Pretty.str "<region>"));
end

local

val reg = Region.make {left=SourcePos.bogus, right=SourcePos.bogus}
val wrap = Region.Wrap.makeRegion ("some node data", reg)
in
val _ = tracing ("region hidden: " ^ @{make_string} reg)
val _ = Print_Mode.with_modes [SourcePos.show_c_parser_positions] 
          (fn _ => tracing ("region pretty: " ^ @{make_string} reg)) ()

val _ = tracing ("wrap hidden: " ^ @{make_string} wrap)
val _ = Print_Mode.with_modes [SourcePos.show_c_parser_positions] 
          (fn _ => tracing ("wrap pretty: " ^ @{make_string} wrap)) ()
end