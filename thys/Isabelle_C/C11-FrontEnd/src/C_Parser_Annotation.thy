(******************************************************************************
 * Isabelle/C
 *
 * Copyright (c) 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************)

section \<open>Annotation Language: Command Parser Registration\<close>

theory C_Parser_Annotation
  imports C_Lexer_Annotation C_Environment
begin

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/Isar/outer_syntax.ML\<close>\<close>
(*  Author:     Frédéric Tuong, Université Paris-Saclay
    Analogous to:
(*  Title:      Pure/Isar/outer_syntax.ML
    Author:     Markus Wenzel, TU Muenchen

Isabelle/Isar outer syntax.
*)*)
\<open>
structure C_Annotation =
struct

(** outer syntax **)

(* errors *)

fun err_command msg name ps =
  error (msg ^ quote (Markup.markup Markup.keyword1 name) ^ Position.here_list ps);

fun err_dup_command name ps =
  err_command "Duplicate annotation syntax command " name ps;


(* command parsers *)

datatype command_parser =
  Parser of (Symbol_Pos.T list * (bool * Symbol_Pos.T list)) * Position.range ->
            C_Env.eval_time c_parser;

datatype command = Command of
 {comment: string,
  command_parser: command_parser,
  pos: Position.T,
  id: serial};

fun eq_command (Command {id = id1, ...}, Command {id = id2, ...}) = id1 = id2;

fun new_command comment command_parser pos =
  Command {comment = comment, command_parser = command_parser, pos = pos, id = serial ()};

fun command_pos (Command {pos, ...}) = pos;

fun command_markup def (name, Command {pos, id, ...}) =
  Position.make_entity_markup def id Markup.commandN (name, pos);



(* theory data *)

structure Data = Theory_Data
(
  type T = command Symtab.table;
  val empty = Symtab.empty;
  fun merge data : T =
    data |> Symtab.join (fn name => fn (cmd1, cmd2) =>
      if eq_command (cmd1, cmd2) then raise Symtab.SAME
      else err_dup_command name [command_pos cmd1, command_pos cmd2]);
);

val get_commands = Data.get;
val dest_commands = get_commands #> Symtab.dest #> sort_by #1;
val lookup_commands = Symtab.lookup o get_commands;


(* maintain commands *)

fun add_command name cmd thy =
    let
      val _ =
        C_Keyword.is_command (C_Thy_Header.get_keywords thy) name orelse
          err_command "Undeclared outer syntax command " name [command_pos cmd];
      val _ =
        (case lookup_commands thy name of
          NONE => ()
        | SOME cmd' => err_dup_command name [command_pos cmd, command_pos cmd']);
      val _ =
        Context_Position.report_generic (Context.the_generic_context ())
          (command_pos cmd) (command_markup {def = true} (name, cmd));
    in Data.map (Symtab.update (name, cmd)) thy end;

fun delete_command (name, pos) thy =
    let
      val _ =
        C_Keyword.is_command (C_Thy_Header.get_keywords thy) name orelse
          err_command "Undeclared outer syntax command " name [pos];
    in Data.map (Symtab.delete name) thy end;


(* implicit theory setup *)

type command_keyword = string * Position.T;

fun raw_command0 kind (name, pos) comment command_parser =
  C_Thy_Header.add_keywords [((name, pos), Keyword.command_spec (kind, [name]))]
  #> add_command name (new_command comment command_parser pos);

fun raw_command (name, pos) comment command_parser =
  let val setup = add_command name (new_command comment command_parser pos)
  in Context.>> (Context.mapping setup (Local_Theory.background_theory setup)) end;

fun command (name, pos) comment parse =
  raw_command (name, pos) comment (Parser parse);

fun command'' kind (name, pos) comment parse =
  raw_command0 kind (name, pos) comment (Parser parse);

val command' = command'' Keyword.thy_decl;



(** toplevel parsing **)

(* parse spans *)


(* parse commands *)

local
fun scan_stack' f b = Scan.one f >> (pair b o C_Token.content_of')
in
val before_command =
  C_Token.scan_stack C_Token.is_stack1
  -- Scan.optional (   scan_stack' C_Token.is_stack2 false
                    || scan_stack' C_Token.is_stack3 true)
                   (pair false [])
end

fun parse_command thy =
  Scan.ahead (before_command |-- C_Parse.position C_Parse.command) :|-- (fn (name, pos) =>
    let val command_tags = before_command -- C_Parse.range C_Parse.command
                           >> (fn (cmd, (_, range)) => (cmd, range));
    in
      case lookup_commands thy name of
        SOME (cmd as Command {command_parser = Parser parse, ...}) =>
          C_Parse.!!! (command_tags :|-- parse)
          >> pair [((pos, command_markup {def = false} (name, cmd)), "")]
      | NONE =>
          Scan.fail_with (fn _ => fn _ =>
            let
              val msg = "undefined command ";
            in msg ^ quote (Markup.markup Markup.keyword1 name) end)
    end)


(* check commands *)

fun command_reports thy tok =
  if C_Token.is_command tok then
    let val name = C_Token.content_of tok in
      (case lookup_commands thy name of
        NONE => []
      | SOME cmd => [((C_Token.pos_of tok, command_markup {def = false} (name, cmd)), "")])
    end
  else [];

fun check_command ctxt (name, pos) =
  let
    val thy = Proof_Context.theory_of ctxt;
    val keywords = C_Thy_Header.get_keywords thy;
  in
    if C_Keyword.is_command keywords name then
      let
        val markup =
          C_Token.explode0 keywords name
          |> maps (command_reports thy)
          |> map (#2 o #1);
        val _ = Context_Position.reports ctxt (map (pair pos) markup);
      in name end
    else
      let
        val completion_report =
          Completion.make_report (name, pos)
            (fn completed =>
              C_Keyword.dest_commands keywords
              |> filter completed
              |> sort_strings
              |> map (fn a => (a, (Markup.commandN, a))));
      in error ("Bad command " ^ quote name ^ Position.here pos ^ completion_report) end
  end;
end
\<close>

ML \<comment> \<open>\<^file>\<open>~~/src/Pure/PIDE/resources.ML\<close>\<close>
(*  Author:     Frédéric Tuong, Université Paris-Saclay
    Analogous to:
(*  Title:      Pure/PIDE/resources.ML
    Author:     Makarius

Resources for theories and auxiliary files.
*)*)
\<open>
structure C_Resources:
sig
  val parse_file: C_Parse.T list -> (theory -> Token.file) * C_Parse.T list
end =
struct

val parse_file =
  (Scan.ahead C_Parse.not_eof >> C_Token.get_files) -- C_Parse.path_input
    >> (the_single oo Resources.parsed_files single)

end;
\<close>

end
