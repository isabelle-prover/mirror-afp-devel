(* SPDX-License-Identifier: HPND *)

(* Copyright (C) 1999-2002 Henry Cejtin, Matthew Fluet, Suresh
 *    Jagannathan, and Stephen Weeks.
 * Copyright (C) 1997-1999 NEC Research Institute.
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * Please see the file MLton-LICENSE for license information.
 *)
signature SOURCE_FILE =
   sig
      type t

      (* The pos in the following specs is a file position (e.g. yypos of mllex).
       *)
      val getPos: t * int -> SourcePos.t
      val observe_line_directives : bool Unsynchronized.ref
      val lineDirective:
           t * string option * {lineNum: int, lineStart: int} -> unit
      val lineStart: t -> SourcePos.t

      val get_included: t -> string list
      val new: string -> t
      val newline: t * int -> unit
   end;



structure SourceFile: SOURCE_FILE =
struct

datatype t = T of {file: string Unsynchronized.ref,
                   lineNum: int Unsynchronized.ref,
                   lineStart: int Unsynchronized.ref,
                   main_file: string,
                   included: string list Unsynchronized.ref}

fun getPos (T {file, lineNum, lineStart, ...}, n) =
   SourcePos.make {column = n - !lineStart,
                   file = !file,
                   line = !lineNum}

fun lineStart (s as T {lineStart, ...}) = getPos (s, !lineStart)

val observe_line_directives = Unsynchronized.ref true

fun new file = T {file = Unsynchronized.ref file,
                  lineNum = Unsynchronized.ref 1,
                  lineStart = Unsynchronized.ref 0,
                  main_file = file,
                  included = Unsynchronized.ref []}

fun newline (T {lineStart, lineNum, ...}, n) =
   (lineNum := !lineNum + 1
    ; lineStart := n)

fun get_included (T {included,...}) = !included

val base_file_name = try (Path.file_name o Path.base o Path.explode) 
                       
fun lineDirective (src as T {file, lineNum, lineStart, main_file, included},
                   f,
                   {lineNum = n, lineStart = s}) =
  let
    val included' = 
      case (base_file_name (the_default "" f)) of
        SOME bf => if bf <> main_file andalso bf <> "" andalso not (member (op =) (!included) bf)
                   then bf :: !included
                   else !included
       | _ => !included
  in
    if !observe_line_directives then
      (Option.app (fn f => file := f) f
       ; lineNum := n
       ; lineStart := s
       ; included := included')
    else newline(src,s)
  end


end;

