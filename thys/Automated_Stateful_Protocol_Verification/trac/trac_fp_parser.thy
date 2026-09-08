(*  Title:      trac_fp_parser.thy
    Author:     Andreas Viktor Hess, DTU
    Author:     Sebastian A. Mödersheim, DTU
    Author:     Achim D. Brucker, University of Exeter
    Author:     Anders Schlichtkrull, DTU
    SPDX-License-Identifier: BSD-3-Clause
*)

section\<open>Parser for Trac FP definitions\<close>
theory
  trac_fp_parser
  imports
    "trac_term"
    "Isabelle_Lex-Yacc.LexYacc"
begin

SML_import \<open>val error = error\<close>
SML_import \<open>structure Trac_Term  = Trac_Term\<close>
SML_import \<open>structure Position = struct open Position end\<close>

ml_lex_yacc[expert] Trac where 
lex_user_declarations\<open>
structure Tokens = Tokens
open Trac_Term
  
type pos = Position.T
type svalue = Tokens.svalue

type ('a,'b) token = ('a,'b) Tokens.token
type lexresult= (svalue,pos) token

val source_pos_array = ref (Array.array (0, Position.none))

fun get_pos yypos =
  let val arr = !source_pos_array
      val len = Array.length arr
  in 
    if yypos < 0 then Position.none
    else if yypos >= len then 
      if len > 0 then Array.sub (arr, len - 1) else Position.none
    else Array.sub (arr, yypos)
  end

fun get_range yypos yylen =
  if yylen <= 0 then get_pos yypos
  else 
    (Position.range_position (get_pos yypos, get_pos (yypos + yylen)))
    handle _ => get_pos yypos | Fail _ => get_pos yypos

fun report_kw yypos yylen mk = 
  let val pos = get_range yypos yylen in
    if pos = Position.none then () else Position.report pos mk
  end

fun report_comment yypos yylen = 
  let val pos = get_range yypos yylen in
    if pos = Position.none then () else Position.report pos Markup.comment
  end

fun report_var yypos yylen name =
  let val pos = get_range yypos yylen in
    if pos = Position.none then () else (
      Position.report pos Markup.free;
      Position.report pos (Markup.entity "Trac Variable" name)
    )
  end

fun report_fun yypos yylen name =
  let val pos = get_range yypos yylen in
    if pos = Position.none then () else (
      Position.report pos (Markup.entity "constant" name);
      Position.report pos (Markup.entity "Trac Function" name)
    )
  end

fun report_str yypos yylen =
  let val pos = get_range yypos yylen in
    if pos = Position.none then () else Position.report pos Markup.inner_string
  end

fun eof () = Tokens.EOF(Position.none, Position.none)
fun error' (e, p: Position.T, _) = error (e ^ Position.here p)
\<close>
lex_definitions\<open>
%header (functor TracLexFun(structure Tokens: Trac_TOKENS));
alpha=[A-Za-z_];
upper=[A-Z];
lower=[a-z];
digit=[0-9];
ws = [\ \t\r\127];
\<close>
lex_rules\<open>
\n       => (lex());
{ws}+    => (lex()); 

(#)[^\n]*\n                    => (report_comment yypos (size yytext); lex());
"/*""/"*([^*/]|[^*]"/"|"*"[^/])*"*"*"*/" => (report_comment yypos (size yytext); lex());

","          => (report_kw yypos (size yytext) Markup.keyword3; Tokens.COMMA(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"Fixedpoint" => (report_kw yypos (size yytext) Markup.keyword1; Tokens.FIXEDPOINT(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"where"      => (report_kw yypos (size yytext) Markup.keyword2; Tokens.WHERE(yytext, get_pos yypos, get_pos (yypos + size yytext)));
":"          => (report_kw yypos (size yytext) Markup.keyword3; Tokens.COLON(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"("          => (report_kw yypos (size yytext) Markup.keyword3; Tokens.PAREN_OPEN(yytext, get_pos yypos, get_pos (yypos + size yytext)));
")"          => (report_kw yypos (size yytext) Markup.keyword3; Tokens.PAREN_CLOSE(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"**"         => (report_kw yypos (size yytext) Markup.keyword3; Tokens.DOUBLE_ASTERISK(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"*"          => (report_kw yypos (size yytext) Markup.keyword3; Tokens.ASTERISK(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"=>"         => (report_kw yypos (size yytext) Markup.keyword3; Tokens.DOUBLE_RARROW(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"one"        => (report_kw yypos (size yytext) Markup.keyword2; Tokens.ONE(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"zero"       => (report_kw yypos (size yytext) Markup.keyword2; Tokens.ZERO(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"attack"     => (report_kw yypos (size yytext) Markup.keyword1; Tokens.ATTACK(yytext, get_pos yypos, get_pos (yypos + size yytext)));

{digit}+                                                                  => (Tokens.INTEGER_LITERAL(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"'"({alpha}|{ws}|{digit})*(("."|"_"|"/"|"-")*({alpha}|{ws}|{digit})*)*"'" => (report_str yypos (size yytext); Tokens.STRING_LITERAL(yytext, get_pos yypos, get_pos (yypos + size yytext)));
{upper}({alpha}|{digit})*("'")*   => (report_var yypos (size yytext) yytext; Tokens.UPPER_STRING_LITERAL(yytext, get_pos yypos, get_pos (yypos + size yytext)));
{lower}({alpha}|{digit})*("'")*   => (report_fun yypos (size yytext) yytext; Tokens.LOWER_STRING_LITERAL(yytext, get_pos yypos, get_pos (yypos + size yytext)));

.      => (error' ("Bad character: "^yytext, get_pos yypos, get_pos yypos));
\<close>
 and 
yacc_user_declarations\<open>
open Trac_Term
exception NotYetSupported of string 
\<close>
yacc_definitions\<open>
%verbose

%eop EOF 

%left 

%name Trac

%term EOF
    | COMMA of string
    | FIXEDPOINT of string
    | WHERE of string
    | COLON of string
    | PAREN_OPEN of string
    | PAREN_CLOSE of string
    | ASTERISK of string
    | DOUBLE_ASTERISK of string
    | DOUBLE_RARROW of string
    | STRING_LITERAL of string
    | UPPER_STRING_LITERAL of string
    | LOWER_STRING_LITERAL of string
    | INTEGER_LITERAL of string
    | ONE of string
    | ZERO of string
    | ATTACK of string              
         
%nonterm START of (Msg * TypeDecl list) list
       | trac_file of (Msg * TypeDecl list) list   
       | symfact_list_exp of (Msg * TypeDecl list) list    
       | symfact_exp of Msg * TypeDecl list  
       | rule_exp of Msg   
       | arg_list_exp of Msg list
       | arg_exp  of Msg 
       | type_list_exp of TypeDecl list
       | type_exp of TypeDecl
       | string_literal of string
       | upper_literal of string
       | lower_literal of string
       | int_literal of string

%pos Position.T

%noshift EOF
\<close>
yacc_rules\<open>
START:               trac_file                                                  (trac_file)
trac_file:           FIXEDPOINT symfact_list_exp                                (symfact_list_exp)
                   | symfact_list_exp                                           (symfact_list_exp)
symfact_list_exp:    symfact_exp                                                ([symfact_exp])                 
                   | symfact_exp symfact_list_exp                               ([symfact_exp]@symfact_list_exp)

symfact_exp:         DOUBLE_RARROW ATTACK                                       ((Attack,[])) 
                   | rule_exp WHERE type_list_exp                               ((rule_exp,type_list_exp))
                   | DOUBLE_RARROW rule_exp WHERE type_list_exp                 ((rule_exp,type_list_exp))
                   | DOUBLE_ASTERISK DOUBLE_RARROW rule_exp WHERE type_list_exp ((rule_exp,type_list_exp))
                   | rule_exp                                                   ((rule_exp,[]))
                   | DOUBLE_RARROW rule_exp                                     ((rule_exp,[]))
                   | DOUBLE_ASTERISK DOUBLE_RARROW rule_exp                     ((rule_exp,[]))

rule_exp:            upper_literal                                              (Var (upper_literal))
                   | lower_literal                                              (Fun (lower_literal,[]))
                   | lower_literal PAREN_OPEN arg_list_exp PAREN_CLOSE          (Fun (lower_literal,arg_list_exp)) 
arg_list_exp:        arg_exp                                                    ([arg_exp])
                   | arg_exp COMMA arg_list_exp                                 ([arg_exp]@arg_list_exp)
arg_exp:             rule_exp                                                   (rule_exp)
                   | ASTERISK int_literal                                       (Var (int_literal))
                   | int_literal                                                (Const (int_literal))

type_list_exp:       type_exp                                                   ([type_exp])
                   | type_exp type_list_exp                                     ([type_exp]@type_list_exp)
type_exp:            ASTERISK int_literal COLON string_literal                  ((int_literal,string_literal))
                   | upper_literal COLON string_literal                         ((upper_literal,string_literal))

upper_literal:       UPPER_STRING_LITERAL                                       (UPPER_STRING_LITERAL)
lower_literal:       LOWER_STRING_LITERAL                                       (LOWER_STRING_LITERAL)
string_literal:      upper_literal                                              (upper_literal)
                   | lower_literal                                              (lower_literal)
int_literal:         INTEGER_LITERAL                                            (INTEGER_LITERAL)
                   | ZERO                                                       ("0")
                   | ONE                                                        ("1")
\<close>


ML\<open>
structure TracFpParser : sig  
       val parse_source: Input.source -> (Trac_Term.Msg * (string * string) list) list
       val parse_file: string -> (Trac_Term.Msg * (string * string) list) list
       val parse_str: string -> (Trac_Term.Msg * (string * string) list) list
end = 
struct

  open Trac_Term

  structure TracLrVals =
    TracLrValsFun(structure Token = LrParser.Token)

  structure TracLex =
    TracLexFun(structure Tokens = TracLrVals.Tokens)

  structure TracParser =
    Join(structure LrParser = LrParser
     structure ParserData = TracLrVals.ParserData
     structure Lex = TracLex)
  
  fun invoke lexstream =
      let fun print_error (s, p: Position.T, _) =
          TextIO.output(TextIO.stdOut,
                "Error at " ^ Position.here p ^ ", " ^ s ^ "\n")
       in TracParser.parse(0, lexstream, print_error, ())
      end

 fun parse_fp lexer =  
   let
    val dummyEOF = TracLrVals.Tokens.EOF(Position.none, Position.none)
    fun loop lexer =
      let 
        val (res, lexer) = invoke lexer
        val (nextToken, lexer) = TracParser.Stream.get lexer
      in if TracParser.sameToken(nextToken, dummyEOF) then ((), res) else loop lexer end
   in #2(loop lexer) end

 fun init_pos_array syms =
   let
     val total_bytes = fold (fn (s, _) => fn acc => acc + size s) syms 0
     val arr = Array.array (total_bytes + 1, Position.none)
     fun fill [] _ = ()
       | fill ((s, p) :: rest) idx =
           let
             val n = size s
             fun loop i = if i < n then (Array.update (arr, idx + i, p); loop (i + 1)) else ()
             val _ = loop 0
           in fill rest (idx + n) end
     val _ = fill syms 0
     val last_pos = if null syms then Position.none else #2 (List.last syms)
     val _ = Array.update (arr, total_bytes, last_pos)
   in arr end

 fun parse_syms (content, syms) =
   let
     val _ = TracLex.UserDeclarations.source_pos_array := init_pos_array syms
     val parsed = Unsynchronized.ref false 
     fun input_string _ = if !parsed then "" else (parsed := true; content)
     val lexer = TracParser.makeLexer input_string
   in parse_fp lexer end

 fun parse_source source =
   let
     val syms = Input.source_explode source
     val content = Symbol_Pos.content syms
   in parse_syms (content, syms) end

 fun parse_file tracFile = 
   let
     val content_raw = File.read (Path.explode tracFile)
     val syms = Symbol_Pos.explode (content_raw, Position.file tracFile)
     val content = Symbol_Pos.content syms
   in parse_syms (content, syms) end

 fun parse_str trac_fp_str = 
   let  
     val syms = Symbol_Pos.explode (trac_fp_str, Position.none)
     val content = Symbol_Pos.content syms
   in parse_syms (content, syms) end
end
\<close>

end