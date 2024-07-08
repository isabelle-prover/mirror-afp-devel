(* SPDX-License-Identifier: HPND *)

(* Copyright (C) 1999-2002 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-1999 NEC Research Institute.
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * Please see the file MLton-LICENSE for license information.

 * Slightly adjusted by Michael Norrish (2006)

 *)

(*

(line, column) based source position instead of 'offset' based Position.T.

Note that we work on preprocessed (cpp) files, but want to have positions that are valid in the
original .c / .h files.

As cpp keeps track of lines and with option -CC it also keeps comments, but it will remove lines
like #include foo.h and replace it by an empty line followd by a line-directive. 
From the line-directive alone it is not possible to infer how much contribution to the "offset" the 
original line had.

Taking line-directives into account, for all other lines (column,line) positions from the
cpp-ed version of the file match to (column, line) in the original file.
With the original file ht hand we can calculate the offset from (column, line). 

See also: Feedback.ML SourceFile.ML
*)
signature SOURCE_POS =
sig

  type t

  val bogus: t
  val column: t -> int
  val compare: t * t -> order
  val equals: t * t -> bool
  val is_bogus: t -> bool
  val file: t -> string
  val line: t -> int
  val make: {column: int, file: string, line: int} -> t
  val toString: t -> string
  val posToString : t -> string
  val show_c_parser_positions : string
end

structure SourcePos : SOURCE_POS =
struct

datatype t = T of {column: int, file: string, line: int}

local
   fun f g (T r) = g r
in
   val column = f #column
   val line = f #line
end

fun compare (T {column = c, file = f, line = l},
             T {column = c', file = f', line = l'}) =
   case string_ord (f, f') of
      EQUAL =>
         (case int_ord (l, l') of
             EQUAL => int_ord (c, c')
           | r => r)
    | r => r

fun equals (T r, T r') = r = r'

fun make {column, file, line} =
   T {column = column,
      file = file,
      line = line}

fun file (T {file, ...}) = file

val bogus = T {column = ~1,
               file = "<bogus>",
               line = ~1}

fun is_bogus t = equals (t, bogus)


fun prettyPos (T {column, line, file}) = 
  Pretty.strs [Int.toString line ^ "." ^ Int.toString column, "in " ^  quote (file) ]

fun toString (p as T {column, line, file}) =
   String.concat [file, " ", Int.toString line, ".", Int.toString column]

fun posToString (T {column,line,...}) =
   String.concat [Int.toString line, ".", Int.toString column]

val show_c_parser_positions = "show_c_parser_positions"

val _ =
  ML_system_pp (fn depth => fn pretty => fn (pos:t) =>
    if print_mode_active show_c_parser_positions 
    then Pretty.to_polyml (prettyPos pos)
    else Pretty.to_polyml (Pretty.str "<pos>"));

end



val _ = tracing ("position hidden: " ^ @{make_string} SourcePos.bogus)
val _ = Print_Mode.with_modes [SourcePos.show_c_parser_positions] 
          (fn _ => tracing ("position pretty: " ^ @{make_string} SourcePos.bogus)) ()


