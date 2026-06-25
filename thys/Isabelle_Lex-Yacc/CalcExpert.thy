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
  CalcExpert
imports
  LexYacc
keywords
  "calc2" :: diag
begin


ml_lex_yacc [verbose, expert] "Calc" where
lex_user_declarations\<open>
structure Tokens = Tokens
type pos = Position.T
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult= (svalue,pos) token

val pos_lookup = ref (fn (yypos: int) => Position.none)

val report_token = ref (fn (idx: int, len: int, m: Markup.T, typ: string, sort: string) => ())

fun get_pos yypos = (!pos_lookup) yypos

fun tok (yypos, yytext, markup, typ, sort, cons) =
  let
    val p = get_pos yypos
    val p' = get_pos (yypos+(String.size yytext))
    val _ = !report_token (yypos, String.size yytext, markup, typ, sort)
  in cons (p, p') end

fun tok_val (yypos, yytext, markup, typ, sort, cons, value) =
  let
    val p = get_pos yypos
    val _ = !report_token (yypos, String.size yytext, markup, typ, sort)
  in cons (value, p, p) end



fun eof () = Tokens.EOF(Position.none, Position.none)
fun error' (e, p: Position.T, _) = () 
\<close>
lex_definitions\<open>
%header (functor CalcLexFun(structure Tokens: Calc_TOKENS));
alpha=[A-Za-z];
digit=[0-9];
ws = [\ \t\r];
\<close>
lex_rules\<open>
\n       => (lex());
{ws}+    => (lex());

{digit}+ => (tok_val (yypos, yytext, Markup.numeral, "NUM", "", Tokens.NUM, valOf (Int.fromString yytext)));

"+"      => (tok (yypos, yytext, Markup.keyword2, "PLUS", "", Tokens.PLUS));
"*"      => (tok (yypos, yytext, Markup.keyword2, "TIMES", "", Tokens.TIMES));
";"      => (tok (yypos, yytext, Markup.delimiter, "SEMI", "", Tokens.SEMI));

{alpha}+ => (if yytext="print"
                 then tok (yypos, yytext, Markup.keyword1, "PRINT", "", Tokens.PRINT)
                 else tok_val (yypos, yytext, Markup.free, "ID", "", Tokens.ID, yytext)
            );

"-"      => (tok (yypos, yytext, Markup.keyword2, "SUB", "", Tokens.SUB));
"^"      => (tok (yypos, yytext, Markup.keyword2, "CARAT", "", Tokens.CARAT));
"/"      => (tok (yypos, yytext, Markup.keyword2, "DIV", "", Tokens.DIV));
.        => (lex());
\<close>
and yacc_user_declarations\<open>
fun lookup "bogus" = 10000
  | lookup s = 0
\<close>
yacc_definitions\<open>
%eop EOF SEMI
%pos Position.T

%left SUB PLUS
%left TIMES DIV
%right CARAT

%term ID of string | NUM of int | PLUS | TIMES | PRINT |
      SEMI | EOF | CARAT | DIV | SUB
%nonterm EXP of int | START of int option

%name Calc

%subst PRINT for ID
%prefer PLUS TIMES DIV SUB
%keyword PRINT SEMI

%noshift EOF
%value ID ("bogus")
%verbose
\<close>
yacc_rules\<open>
  START : PRINT EXP (print (Int.toString EXP);
                     print "\n";
                     SOME EXP)
        | EXP (SOME EXP)
        | (NONE)
  EXP : NUM             (NUM)
      | ID              (lookup ID)
      | EXP PLUS EXP    (EXP1+EXP2)
      | EXP TIMES EXP   (EXP1*EXP2)
      | EXP DIV EXP     (EXP1 div EXP2)
      | EXP SUB EXP     (EXP1-EXP2)
      | EXP CARAT EXP   (let fun e (m,0) = 1
                                | e (m,l) = m*e(m,l-1)
                         in e (EXP1,EXP2)
                         end)
\<close>

 

text\<open>Linking lexer and parser and establishing PIDE position lookups\<close>
ML\<open>
structure Calc : sig
           val parse_source : Proof.context -> Input.source -> int
                 end   = 
struct
  structure CalcLrVals =
    CalcLrValsFun(structure Token = LrParser.Token)

  structure CalcLex =
    CalcLexFun(structure Tokens = CalcLrVals.Tokens)

  structure CalcParser =
    Join(structure LrParser = LrParser
         structure ParserData = CalcLrVals.ParserData
         structure Lex = CalcLex)

  fun parse_source ctxt source = let
        val input_text = Input.text_of source
        val syms = Input.source_explode source
        val pos_vec = Vector.fromList syms
        
        fun to_index yypos = yypos - 1

        fun lookup_fn yypos = 
            let val idx = to_index yypos in
              if Vector.length pos_vec = 0 then Input.pos_of source
              else if idx < 0 then #2 (Vector.sub (pos_vec, 0))
              else if idx >= Vector.length pos_vec 
              then #2 (Vector.sub (pos_vec, Vector.length pos_vec - 1))
              else #2 (Vector.sub (pos_vec, idx))
            end

        fun report_fn (start_idx, len, markup, token_type, token_sort) =
            let
              fun report_char i =
                  if i < len then
                    let val p = lookup_fn (start_idx + i) in
                      (* apply the syntax highlighting color *)
                      Context_Position.report ctxt p markup;
                      (* apply the hover tooltip *)
                      Context_Position.report_text ctxt p Markup.typing ("Token Type: " ^ token_type);
                      Context_Position.report_text ctxt p Markup.typing ("Token Sort: " ^ token_sort);
                      report_char (i + 1)
                    end
                  else ()
            in report_char 0 end

        val _ = CalcLex.UserDeclarations.pos_lookup := lookup_fn
        val _ = CalcLex.UserDeclarations.report_token := report_fn

        fun get_line_col p =
            let
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
                    else if String.sub (input_text, i) = #"\n" then scan (n-1) (i+1) (line+1) 1
                    else scan (n-1) (i+1) line (col+1)
            in scan limit 0 1 1 end

        fun invoke lexstream =
          let 
            val start_line = the_default 1 (Position.line_of (Input.pos_of source))

            fun print_error (s, p: Position.T, _) =
                 let 
                   val _ = Position.report p Markup.error
                   val (local_line, col) = get_line_col p
                   val abs_line = start_line + local_line - 1
                 in
                    error ("Parse Error at line " ^ Int.toString abs_line ^ 
                           ", column " ^ Int.toString (col + 1) ^ ": " ^ s ^ 
                           Position.here p)
                 end
          in 
            CalcParser.parse(0,lexstream,print_error,())
          end

        val parsed = Unsynchronized.ref false
        fun input_string _  = if !parsed then "" else (parsed := true; input_text)
        val lexer = CalcParser.makeLexer input_string
        
        val eof_pos = lookup_fn (String.size input_text + 1)
        val dummyEOF = CalcLrVals.Tokens.EOF(eof_pos, eof_pos)
        
        fun loop lexer =
          let
            val (res,lexer) = invoke lexer
            val (nextToken,lexer) = CalcParser.Stream.get lexer
          in 
            if CalcParser.sameToken(nextToken,dummyEOF) 
            then ((),res) 
            else loop lexer 
          end
      in
        the (#2 (loop lexer))
      end
end
\<close>

text\<open>Defining a simple Isar-toplevel command\<close>
ML\<open>
fun calc source thy = 
    let 
      val ctxt = Proof_Context.init_global thy
      val _ = writeln(Int.toString (Calc.parse_source ctxt source)) 
    in thy end

val _ = Outer_Syntax.command @{command_keyword "calc2"}
        "A simple inline calculator" 
        (Parse.input Parse.cartouche >> (fn source => Toplevel.theory (calc source)))
\<close>

calc2\<open>
1
  +
    3
   * (201 - 7)
\<close>


end
