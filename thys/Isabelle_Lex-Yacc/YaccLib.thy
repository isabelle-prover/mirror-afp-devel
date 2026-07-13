(***********************************************************************************
 * Copyright (c) University of Exeter, UK
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 ***********************************************************************************)

theory
  YaccLib
imports
  Main
begin 
SML_file\<open>mlyacc-polyml/mlyacc-lib/base.sig\<close> 
SML_file\<open>mlyacc-polyml/mlyacc-lib/join.sml\<close>
SML_file\<open>mlyacc-polyml/mlyacc-lib/lrtable.sml\<close>
SML_file\<open>mlyacc-polyml/mlyacc-lib/stream.sml\<close>   
SML_file\<open>mlyacc-polyml/mlyacc-lib/parser2.sml\<close>

ML\<open>

signature ISABELLE_LEX_YACC = 
  sig
    eqtype pos
    val get_pos: int -> Position.T
    val header: unit -> string
    val linker: string -> string
    val parse_source:
       (int * 'a * (string * Position.T * Position.T -> 'b) * unit -> 'c * 'd) ->
         (('e -> string) -> 'a) -> ('d -> 'f * 'a) -> ('f * 'g -> bool) -> (Position.T * Position.T -> 'g) -> Input.source -> 'c
    val print_error: string * Position.T * Position.T -> 'a
    val report_token: int * int * Markup.T * string * string -> unit
    val reset: unit -> unit
    val set: Input.source -> Proof.context -> unit
    val tok: int * string * Markup.T * string * string * (Position.T * Position.T -> 'a) -> 'a
    val tok_val: int * string * Markup.T * string * string * ('a * Position.T * Position.T -> 'b) * 'a -> 'b
  end

structure Isabelle_lex_yacc:ISABELLE_LEX_YACC = struct
  type pos = Position.T
  val src = Unsynchronized.ref (Input.string "")
  val ctxt = Unsynchronized.ref (Context.the_local_context ())

  fun set source ctx =
    let
      val _ = src := source
      val _ = ctxt := ctx
    in () end

  fun reset () =
    let
      val _ = src := Input.string ""
      val _ = ctxt := Context.the_local_context ()
    in () end

  (* Helper: Explodes the source but strips the \<open> and \<close> markers so positions align with source_content *)
  fun get_inner_syms source =
    let
      val syms = Input.source_explode source
    in
      if length syms >= 2 then List.take (tl syms, length syms - 2) else syms
    end

  fun get_pos yypos  =
    let
      val inner_syms = get_inner_syms (!src)
      val pos_vec = Vector.fromList inner_syms
      val idx = yypos - 1
    in
      if Vector.length pos_vec = 0 then Input.pos_of (!src)
      else if idx < 0 then #2 (Vector.sub (pos_vec, 0))
      else if idx >= Vector.length pos_vec then
        #2 (Vector.sub (pos_vec, Vector.length pos_vec - 1))
      else #2 (Vector.sub (pos_vec, idx))
    end

  fun report_token (start_idx, len, markup, token_type, token_sort) =
        if 0 < len then
          let val p_start = get_pos start_idx 
              val p_end = get_pos (start_idx + len) 
              val p = Position.range_position (Position.range(p_start, p_end))
          in
            Context_Position.report (!ctxt) p markup;
            Context_Position.report_text (!ctxt) p Markup.typing (token_type);
            Context_Position.report_text (!ctxt) p Markup.sorting(token_sort)
          end
        else ()




  fun get_line_col p =
    let
      val inner_syms = get_inner_syms (!src)
      val pos_vec = Vector.fromList inner_syms
      val (input_text, _) = Input.source_content (!src)
      val target_offset = Position.offset_of p

      fun is_target pos =
        case (Position.offset_of pos, target_offset) of
          (SOME o1, SOME o2) => o1 = o2
        | _ => false

      fun find_idx i =
        if i >= Vector.length pos_vec then Vector.length pos_vec
        else if is_target (#2 (Vector.sub (pos_vec, i))) then i
        else find_idx (i + 1)

      val limit = find_idx 0

      fun scan 0 _ line col = (line, col)
        | scan n i line col =
            if i = limit then (line, col)
            else if String.sub (input_text, i) = #"\n" then scan (n - 1) (i + 1) (line + 1) 1
            else scan (n - 1) (i + 1) line (col + 1)
    in scan limit 0 1 1 end

  fun print_error (s, p: Position.T, p') =
    let
      val start_line = the_default 1 (Position.line_of (Input.pos_of (!src)))
      val _ = Position.report (Position.range_position (Position.range(p,p')))  Markup.error 
      val (local_line, col) = get_line_col p
      val abs_line = start_line + local_line - 1
    in
      error ("Parse Error at line " ^ Int.toString abs_line ^
             ", column " ^ Int.toString (col + 1) ^ ": " ^ s ^Position.here p)
    end

  fun tok (yypos, yytext, markup, typ, sort, cons) =
    let
      val p = get_pos yypos
      val p' = get_pos (yypos+(String.size yytext))
      val _ = report_token (yypos, String.size yytext, markup, typ, sort)
    in cons (p, p') end

  fun tok_val (yypos, yytext, markup, typ, sort, cons, value) =
    let
      val p = get_pos yypos
      val _ = report_token (yypos, String.size yytext, markup, typ, sort)
    in cons (value, p, p) end

  fun parse_source parse makeLexer get sameToken EOF source =
    let
      val (input_text, _) = Input.source_content source
      
      fun invoke lexstream =
        parse (0, lexstream, print_error, ())
      
      val parsed = Unsynchronized.ref false
      fun input_string _ = if !parsed then "" else (parsed := true; input_text)
      
      val lexer = makeLexer input_string
      
      val eof_pos = get_pos (String.size input_text + 1)
      val dummyEOF = EOF (eof_pos, eof_pos)
      
      fun loop lexer =
        let
          val (res, lexer) = invoke lexer
          val (nextToken, lexer) = get lexer
        in 
          if sameToken (nextToken, dummyEOF) then ((), res) 
          else loop lexer 
        end
    in
      (#2 (loop lexer))
    end

  fun header () =
    "open Isabelle_lex_yacc\n" ^
    "structure Tokens = Tokens\n" ^
    "type svalue = Tokens.svalue\n" ^
    "type ('a,'b) token = ('a,'b) Tokens.token\n" ^
    "type lexresult= (svalue,pos) token\n" ^
    "fun eof () = Tokens.EOF(Position.none, Position.none)\n"

  fun linker name = 
    "structure "^name^" =\n"^
    "struct\n"^
    "  structure "^name^"LrVals =\n"^
    "    "^name^"LrValsFun(structure Token = LrParser.Token)\n"^
    "  structure "^name^"Lex =\n"^
    "    "^name^"LexFun(structure Tokens = "^name^"LrVals.Tokens)\n"^
    "  structure "^name^"Parser =\n"^
    "    Join(\n"^
    "      structure LrParser = LrParser\n"^
    "      structure ParserData = "^name^"LrVals.ParserData\n"^
    "      structure Lex = "^name^"Lex\n"^
    "    )\n"^
    "  fun parse_source ctxt source =\n"^
    "    let\n"^
    "      val _ = "^name^"Lex.UserDeclarations.set source ctxt\n"^
    "    in\n"^
    "      Isabelle_lex_yacc.parse_source\n"^
    "        "^name^"Parser.parse\n"^
    "        "^name^"Parser.makeLexer\n"^
    "        "^name^"Parser.Stream.get\n"^
    "        "^name^"Parser.sameToken\n"^
    "        "^name^"LrVals.Tokens.EOF\n"^
    "        source\n"^
    "    end\n"^
    "end\n"

end
\<close>

SML_import \<open>structure Position = struct open Position end\<close>
SML_import \<open>structure Markup = struct open Markup end\<close>
SML_import \<open>structure Isabelle_lex_yacc = struct open Isabelle_lex_yacc end\<close> 
SML_export \<open>structure LrParser = struct open LrParser end\<close>

end
