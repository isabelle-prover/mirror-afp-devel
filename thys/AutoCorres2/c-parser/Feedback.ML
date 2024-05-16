(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)


structure C_Files = Theory_Data
(struct
   type T = {main: string, 
     files: (Token.file * Position.T (* command thread position *)) Symtab.table Symtab.table}
   val empty = {main = "", files = Symtab.empty}
   val merge = Utils.fast_merge (fn ({files=files1,...}, {files=files2,...}) =>
     {main = "", files = Symtab.join (fn _ => Symtab.merge (K false)) (files1, files2)})
end);

structure C_Files =
struct
   open C_Files

   val get_main = #main o get
   val get_files = #files o get

   fun map_main' f {main, files} = {main = f main, files = files}
   fun map_files' f {main, files} = {main = main, files = f files}

   val map_main = map o map_main'
   val map_files = map o map_files'

   fun get_current_files thy = 
     let  
       val {main, files} = get thy 
     in the_default Symtab.empty (Symtab.lookup files main) end

   val default_file = ({src_path = Path.root, lines = [], digest=SHA1.fake "", pos = Position.none}, Position.none)

   fun get_file thy main name = Symtab.lookup (#files (get thy)) main 
     |> Option.mapPartial (fn tab => Symtab.lookup tab name)

   fun map_file main name f = 
     map (map_files' 
      (Symtab.map_default (main, Symtab.empty) (Symtab.map_default (name, default_file) f)))

   fun get_current_file thy = get_file thy (get_main thy)
   fun map_current_file name f thy = map_file (get_main thy) name f thy
end

signature FEEDBACK =
sig

  exception WantToExit of string

  val level : int Config.T
  val verbose : bool Config.T

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

val level   = Attrib.setup_config_int @{binding "c_parser_feedback_level"} (K 0)
val verbose = Attrib.setup_config_bool @{binding "c_parser_verbose"} (K false)

fun pos_of_cpos (file:Token.file) cpos = if SourcePos.is_bogus cpos then Position.none else
  let
     val c = SourcePos.column cpos
     val l = SourcePos.line cpos
     val {lines, pos,...} = file
     val lines = take (l - 1) lines
     val offset_lines = fold (fn l => fn off => off + (length (Symbol.explode l)) + 1)  lines 1
     val offset = offset_lines + c
     val end_offset = 0
  in 
    Position.make {line = l, offset = offset, end_offset= end_offset, props = #props (Position.dest pos)}
  end


fun map_column f p = SourcePos.make {column = f (SourcePos.column p), file = SourcePos.file p, line = SourcePos.line p}

fun pos_of_crange file cpos1 cpos2 =
  let
    
    val pos1 = pos_of_cpos file cpos1
    val pos2 = pos_of_cpos file (map_column (fn n => n + 1) cpos2) (* end_offsets are exclusive in Position.T *)
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
         NONE => pos_of_cpos file l
       | SOME r => pos_of_crange file l r)
  end

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


fun message ctxt markup r s = 
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
          val str = s ^ ": " ^ Position.here pos
        in
          (str, SOME command_thread_pos)
        end
  end

fun message' ctxt markup l r = message ctxt markup (Region.make {left = l, right = r})
fun message_pos ctxt markup p = message ctxt markup (Region.make {left = p, right = SourcePos.bogus})

fun informStr0 ctxt (v,s) = if v <= Config.get ctxt level then !informf s else ()

fun informStr' ctxt (v,l,r,s) =
    informStr0 ctxt (v, message' ctxt Markup.tracing l r s)

fun informStr ctxt (v, s) = informStr0 ctxt (v, (s, NONE))

fun errorStr ctxt (r, s) = 
  let
    val msg = message ctxt Markup.error r s
    val _ = !errorf msg
    val n = incr_num_errors ctxt
    val threshold = get_threshold ctxt
  in
    if is_some threshold andalso n > the threshold then
      raise WantToExit "Too many errors - aborted."
    else ()
  end

fun errorStr' ctxt (l,r,s) = errorStr ctxt (Region.make {left = l, right = r}, s)


fun warnStr' ctxt (l,r,s) =
    !warnf ( message' ctxt Markup.warning l r s |> apfst (prefix "Warning "))

fun timestamp s = Time.fmt 0 (Time.now()) ^ ": " ^ s

fun raise_error (msg as (s, _)) = 
  (!errorf msg; error s)

fun error_region ctxt r s = raise_error (message ctxt Markup.error r s)
fun error_range ctxt l r s = raise_error (message' ctxt Markup.error l r s)
fun error_pos ctxt p s = raise_error (message_pos ctxt Markup.error p s)

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

