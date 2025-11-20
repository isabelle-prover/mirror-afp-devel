(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)


structure C_Files = Theory_Data
(struct
   type T = {main: string, 
     files: ({sources: (Token.file * Position.T (* command thread position *)) Symtab.table, cpp_output:string list} Symtab.table)}
   val empty = {main = "", files = Symtab.empty}
   val merge = Utils.fast_merge (fn ({files=files1,...}, {files=files2,...}) =>
     {main = "", files = Symtab.join (fn _ => fn (
         {sources = sources1, cpp_output = cpp_output1}, {sources = sources2, cpp_output = cpp_output2})=> 
         {sources = Symtab.merge (K false) (sources1, sources2), 
           cpp_output =  if pointer_eq (cpp_output1, cpp_output2) then cpp_output1 else error "cpp_output should be identical"}) 
     (files1, files2)})
end);

structure C_Files =
struct
   open C_Files

   val get_main = #main o get
   val get_files = #files o get

   fun map_main' f {main, files} = {main = f main, files = files}
   fun map_files' f {main, files} = {main = main, files = f files}
   fun map_sources' f {sources, cpp_output} = {sources = f sources, cpp_output = cpp_output}
   fun map_cpp_output' f {sources, cpp_output} = {sources = sources, cpp_output = f cpp_output}

   val map_main = map o map_main'
   val map_files = map o map_files'

   fun get_current_files thy = 
     let  
       val {main, files} = get thy 
     in the_default Symtab.empty (Option.map #sources (Symtab.lookup files main)) end

   val default_file = ({src_path = Path.root, lines = [], digest=SHA1.fake "", pos = Position.none}, Position.none)

   fun get_file thy main name = Symtab.lookup (#files (get thy)) main 
     |> Option.mapPartial (fn {sources, ...} => Symtab.lookup sources name)

   fun get_cpp_output thy main = Symtab.lookup (#files (get thy)) main 
     |> Option.map (#cpp_output)

   fun map_file main name f = 
     map (map_files' 
      (Symtab.map_default (main, {sources = Symtab.empty, cpp_output = []}) 
        (map_sources' (Symtab.map_default (name, default_file) f))))

   fun map_cpp_output main f = 
     map (map_files' 
      (Symtab.map_default (main, {sources = Symtab.empty, cpp_output = []}) 
        (map_cpp_output' f)))

   fun get_current_file thy = get_file thy (get_main thy)
   fun map_current_file name f thy = map_file (get_main thy) name f thy

   fun get_current_cpp_output thy = get_cpp_output thy (get_main thy)
   fun map_current_cpp_output f thy = map_cpp_output (get_main thy) f thy
end

signature FEEDBACK =
sig

  exception WantToExit of string

  val level : int Config.T
  val verbose : bool Config.T
  val feedback_as_error: bool Config.T
  val expect_reject : bool Config.T

  val get_num_errors_val : Proof.context -> int
  val reset_num_errors : Proof.context -> Proof.context
  val get_threshold : Proof.context -> int option
  val map_threshold : (int option -> int option) -> Proof.context -> Proof.context  
  val transfer_error_state : Proof.context -> Proof.context -> Proof.context

  val errorStr : Proof.context -> Region.t * string -> unit
  val errorStr' : Proof.context -> SourcePos.t * SourcePos.t * string -> unit
  val warnStr' : Proof.context -> SourcePos.t * SourcePos.t * string -> unit
  val informStr : Proof.context -> int * string -> unit
  val informStr' : Proof.context -> int * SourcePos.t * SourcePos.t * string -> unit
  val writelns: Proof.context -> int * (string list) -> unit
  val error_region : Proof.context -> Region.t -> string -> 'a
  val error_range : Proof.context -> SourcePos.t -> SourcePos.t -> string -> 'a 
  val error_pos : Proof.context -> SourcePos.t -> string -> 'a

  val report_error : (string * Position.T option) -> unit
  val report_warning : (string * Position.T option) -> unit
  val report_inform : (string * Position.T option) -> unit

  val errorf : ((string * Position.T option) -> unit) Unsynchronized.ref
  val warnf : ((string * Position.T option) -> unit) Unsynchronized.ref
  val informf : ((string * Position.T option) -> unit) Unsynchronized.ref

  val timestamp : string -> string

  val in_target : xstring -> (local_theory -> local_theory) -> local_theory -> local_theory
end

structure Feedback :> FEEDBACK =
struct

val expect_reject  = Attrib.setup_config_bool @{binding "c_parser_expect_reject"} (K false)
val level   = Attrib.setup_config_int @{binding "c_parser_feedback_level"} (K 0)
val verbose = Attrib.setup_config_bool @{binding "c_parser_verbose"} (K false)
val feedback_as_error   = Attrib.setup_config_bool @{binding "c_parser_feedback_as_error"} (K false)

datatype truncate = truncate_at_line_begin | truncate_at_line_end | no_truncate

fun pos_of_cpos trunc (file:Token.file) cpos = if SourcePos.is_bogus cpos then Position.none else
  let
     val c = SourcePos.column cpos
     val l = SourcePos.line cpos
     val {lines, pos,...} = file
     val (lines_before, lines_end)  = chop (l - 1) lines
     val offset_lines = fold (fn l => fn off => off + (length (Symbol.explode l)) + 1)  lines_before 1
     val line = hd lines_end
     val max_column = length (Symbol.explode line)
     val c' = if c <= max_column then c else (* cpp macros may blow up columns *)
       case trunc of 
               truncate_at_line_begin => 0 
             | truncate_at_line_end   => max_column
             | no_truncate => c
     val offset = offset_lines + c'
     val end_offset = 0
  in 
    Position.make {line = l, offset = offset, end_offset= end_offset, props = #props (Position.dest pos)}
  end


fun map_column f p = SourcePos.make {column = f (SourcePos.column p), file = SourcePos.file p, line = SourcePos.line p, yypos = SourcePos.yypos p}

fun pos_of_crange file cpos1 cpos2 =
  let
    
    val pos1 = pos_of_cpos truncate_at_line_begin file cpos1
    val pos2 = pos_of_cpos truncate_at_line_end file (map_column (fn n => n + 1) cpos2) (* end_offsets are exclusive in Position.T *)
  in 
    Position.range_position (pos1, pos2)
  end

fun pos_of_cregion (file: Token.file) region =
  let
    val fpos = #pos file
  in 
    case Region.left region of 
      NONE => fpos
    | SOME l => (case Region.right region of
         NONE => pos_of_cpos truncate_at_line_end file l
       | SOME r => pos_of_crange file l r)
  end

val empty_pos = {line = ~1, col = ~1}
fun is_empty_pos pos = (pos = empty_pos)

fun inter_region (begin1, end1) (begin2, end2) = (Int.max (begin1, begin2), Int.min (end1, end2))
fun is_empty_region (begin, the_end) = (the_end <= begin) 

fun get_cpp_output_span ctxt region =
  Region.left region |> Option.mapPartial (fn l => 
  Region.right region |> Option.mapPartial (fn r => 
  C_Files.get_current_cpp_output (Proof_Context.theory_of ctxt) |> Option.map (fn cpp_output =>
    let
      val left = SourcePos.yypos l - 1 (* yypos counts from 1 *)
      val right = SourcePos.yypos r - 1
      fun has_overlap p = not (is_empty_region (inter_region (left, right) p))
      fun chop_lines (offset, current_line, begin_pos, end_pos) result_lines input_lines =
        if offset >= right then (result_lines, begin_pos, end_pos)
        else
          (case input_lines of [] => (result_lines, begin_pos, end_pos)
           | (l::ls) => 
              let
                val l' = Symbol.explode l
                val len = length l'
                val line_end_offset = offset + len + 1
                val line_overlap = has_overlap (offset, line_end_offset)
                val left' = left - offset
                val begin_line_match = 
                  if line_overlap then 
                    if left' >= 0 then (drop left' l') else l' 
                  else []
                val (begin_pos', col) = 
                  if is_empty_pos begin_pos andalso line_overlap then ({line = current_line, col = left'}, left') 
                  else (begin_pos, 0)
                val remaining_span = right + 1 - (offset + col)
                val inside_region = take remaining_span (begin_line_match)
                val end_pos' = if not (null inside_region) andalso line_end_offset >= right then {line = current_line, col = right - offset} else end_pos
                val result_lines' = if null inside_region then result_lines else result_lines @ [implode inside_region]
              in chop_lines (line_end_offset, current_line + 1, begin_pos', end_pos') result_lines' ls end)
    in
      chop_lines (0, 0, empty_pos, empty_pos ) [] cpp_output
    end ))) |> the_default ([], empty_pos, empty_pos)
  
exception WantToExit of string


structure Data = Proof_Data(
struct
  type T = int Synchronized.var * (int option)
  val init = (fn _ => (Synchronized.var "num_errors" 0, NONE))
end
);

val get_num_errors = fst o Data.get
fun map_num_errors f = Data.map (apfst f)

fun transfer_error_state ctxt1 ctxt2 = Data.map (K (Data.get ctxt1)) ctxt2


val get_num_errors_val = Synchronized.value o get_num_errors
fun reset_num_errors ctxt = map_num_errors (K (Synchronized.var "num_errors" 0)) ctxt

fun incr_num_errors ctxt = 
  let
    val v = get_num_errors ctxt
  in Synchronized.guarded_access v (fn n => SOME (n, n + 1)) end

val get_threshold = snd o Data.get
fun map_threshold f = Data.map (apsnd f)

fun command_output output (s, NONE) = output s
  | command_output output (s, SOME command_thread_pos) = 
      let 
        val current_thread_pos = Position.thread_data ()
        val _ = 
          if command_thread_pos <> current_thread_pos then
            (* Also put message and markup to other command, e.g. include_C_file *)
            Position.setmp_thread_data command_thread_pos output s 
          else ()
      in
        output s
      end

val report_error = command_output Output.error_message
val report_warning = command_output warning
val report_inform = command_output tracing

val errorf = Unsynchronized.ref report_error
val warnf = Unsynchronized.ref report_warning
val informf = Unsynchronized.ref report_inform

val _ = Option.map


fun message ctxt r s = 
  let
    val thy = Proof_Context.theory_of ctxt
    val file = \<^try>\<open>Region.left r 
      |> Option.map (SourcePos.file #> Path.explode #> Path.base #> Path.file_name) 
      |> Option.mapPartial (C_Files.get_current_file thy)
      catch _ => NONE\<close>
  in
    case file of
      NONE => (Region.toString r ^ ": " ^ s, NONE)
    | SOME (f, command_thread_pos) => 
        let
          val pos = pos_of_cregion f r
          (* We add the relevant portion of the cpp-output as macro-expansion is not visible in the source files *)
          val (relevant_cpp_source, {line=begin_cpp_line, col=begin_cpp_col}, {line=end_cpp_line, col=end_cpp_col}) = get_cpp_output_span ctxt r
          val src = if null relevant_cpp_source then "" else 
            ":\n cpp output in error region (" ^ 
                string_of_int (begin_cpp_line + 1) ^ ":" ^ string_of_int (begin_cpp_col + 1) ^ " - " ^ 
                string_of_int (end_cpp_line + 1) ^ ":" ^ string_of_int (end_cpp_col + 1)  ^ "):\n " ^ cat_lines relevant_cpp_source 
          val str = s ^ ": " ^ Position.here pos ^ src
        in
          (str, SOME command_thread_pos)
        end
  end

fun message' ctxt l r = message ctxt (Region.make {left = l, right = r})
fun message_pos ctxt p = message ctxt (Region.make {left = p, right = SourcePos.bogus})

fun writelns ctxt (v, s) = if v <= Config.get ctxt level then Output.writelns s else ()
fun informStr0 ctxt (v,s) = if v <= Config.get ctxt level then !informf s else ()

fun informStr' ctxt (v,l,r,s) =
    informStr0 ctxt (v, message' ctxt l r s)

fun informStr ctxt (v, s) = informStr0 ctxt (v, (s, NONE))

fun errf ctxt = if Config.get ctxt expect_reject then !warnf else !errorf

fun errorStr ctxt (r, s) = 
  let
    val msg = message ctxt r s
  in
    if Config.get ctxt feedback_as_error then
        error (fst msg)
    else
      let
        val _ = errf ctxt msg
        val n = incr_num_errors ctxt
        val threshold = get_threshold ctxt
      in
        if is_some threshold andalso n > the threshold then
          raise WantToExit "Too many errors - aborted."
        else ()
      end
  end

fun errorStr' ctxt (l,r,s) = errorStr ctxt (Region.make {left = l, right = r}, s)

fun warnStr' ctxt (l,r,s) =
    !warnf ( message' ctxt l r s |> apfst (prefix "Warning "))

fun timestamp s = Time.fmt 0 (Time.now()) ^ ": " ^ s

fun raise_error ctxt (msg as (s, _)) = 
  (errf ctxt msg; error s)

fun error_region ctxt r s = raise_error ctxt (message ctxt r s)
fun error_range ctxt l r s = raise_error ctxt (message' ctxt l r s)
fun error_pos ctxt p s = raise_error ctxt (message_pos ctxt p s)

fun in_target name f lthy =
  let
    val (reenter, target_lthy) = Target_Context.switch_named_cmd (SOME (name, Position.none)) (Context.Proof lthy) 
  in
    target_lthy
    |> transfer_error_state lthy
    |> f
    |> (fn lthy' => 
         lthy' 
         |> reenter
         |> Context.the_proof
         |> transfer_error_state lthy') 
  end

end; (* struct *)

structure More_Local_Theory =
struct
  open More_Local_Theory
  
fun in_theory f = gen_in_theory Feedback.transfer_error_state f
fun in_theory_result f = gen_in_theory_result Feedback.transfer_error_state f

end

