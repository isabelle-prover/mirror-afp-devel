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

ml_lex_yacc[expert] Trac where 
lex_user_declarations\<open>
structure Tokens = Tokens
open Trac_Term
  
type pos = int * int * int
type svalue = Tokens.svalue

type ('a,'b) token = ('a,'b) Tokens.token
type lexresult= (svalue,pos) token

val pos = ref (0,0,0)

fun eof () = Tokens.EOF((!pos,!pos))
fun error' (e,p : (int * int * int),_) = error (
							 String.concat[
								       "Line ", (Int.toString (#1 p)), "/",
								       (Int.toString (#2 p - #3 p)),": ", e, "\n"
								       ])
  
fun inputPos yypos = ((#1 (!pos), yypos - (#3(!pos)), (#3 (!pos))),
                      (#1 (!pos), yypos - (#3(!pos)), (#3 (!pos))))
fun inputPos_half yypos = (#1 (!pos), yypos - (#3(!pos)), (#3 (!pos)))
\<close>
lex_definitions\<open>
%header (functor TracLexFun(structure Tokens: Trac_TOKENS));
alpha=[A-Za-z_];
upper=[A-Z];
lower=[a-z];
digit=[0-9];
ws = [\ \t];
\<close>
lex_rules\<open>
\n       => (pos := ((#1 (!pos)) + 1, yypos - (#3(!pos)),yypos  ); lex());
{ws}+    => (pos := (#1 (!pos), yypos - (#3(!pos)), (#3 (!pos))); lex()); 

(#)[^\n]*\n                    => (pos := ((#1 (!pos)) + 1, yypos - (#3(!pos)),yypos  ); lex());

"/*""/"*([^*/]|[^*]"/"|"*"[^/])*"*"*"*/" => (lex());


","          => (Tokens.COMMA(yytext,inputPos_half yypos,inputPos_half yypos));
"Fixedpoint" => (Tokens.FIXEDPOINT(yytext,inputPos_half yypos,inputPos_half yypos));
"where"      => (Tokens.WHERE(yytext,inputPos_half yypos,inputPos_half yypos));
":"          => (Tokens.COLON(yytext,inputPos_half yypos,inputPos_half yypos));
"("          => (Tokens.PAREN_OPEN(yytext,inputPos_half yypos,inputPos_half yypos));
")"          => (Tokens.PAREN_CLOSE(yytext,inputPos_half yypos,inputPos_half yypos));
"**"         => (Tokens.DOUBLE_ASTERISK(yytext,inputPos_half yypos,inputPos_half yypos));
"*"          => (Tokens.ASTERISK(yytext,inputPos_half yypos,inputPos_half yypos));
"=>"         => (Tokens.DOUBLE_RARROW(yytext,inputPos_half yypos,inputPos_half yypos));
"one"        => (Tokens.ONE(yytext,inputPos_half yypos,inputPos_half yypos));
"zero"       => (Tokens.ZERO(yytext,inputPos_half yypos,inputPos_half yypos));
"attack"       => (Tokens.ATTACK(yytext,inputPos_half yypos,inputPos_half yypos));


{digit}+                          => (Tokens.INTEGER_LITERAL(yytext,inputPos_half yypos,inputPos_half yypos));
"'"({alpha}|{ws}|{digit})*(("."|"_"|"/"|"-")*({alpha}|{ws}|{digit})*)*"'"  => (Tokens.STRING_LITERAL(yytext,inputPos_half yypos,inputPos_half yypos));
{upper}({alpha}|{digit})*("'")*   => (Tokens.UPPER_STRING_LITERAL(yytext,inputPos_half yypos,inputPos_half yypos));
{lower}({alpha}|{digit})*("'")*   => (Tokens.LOWER_STRING_LITERAL(yytext,inputPos_half yypos,inputPos_half yypos));


.      => (error' ("Bad character: "^yytext,
		    ((#1 (!pos), yypos - (#3(!pos)), (#3 (!pos)))),
		    ((#1 (!pos), yypos - (#3(!pos)), (#3 (!pos))))));
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

%pos (int * int * int)

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
      let fun print_error (s,i:(int * int * int),_) =
	      TextIO.output(TextIO.stdOut,
			    "Error, line .... " ^ (Int.toString (#1 i)) ^"."^(Int.toString (#2 i ))^ ", " ^ s ^ "\n")
       in TracParser.parse(0,lexstream,print_error,())
      end

 fun parse_fp lexer =  let
    val dummyEOF = TracLrVals.Tokens.EOF((0,0,0),(0,0,0))
    fun loop lexer =
      let 
        val _ = (TracLex.UserDeclarations.pos := (0,0,0);())
        val (res,lexer) = invoke lexer
        val (nextToken,lexer) = TracParser.Stream.get lexer
      in if TracParser.sameToken(nextToken,dummyEOF) then ((),res) else loop lexer end
  in #2(loop lexer)
  end

 fun parse_file tracFile = let
	     val infile = TextIO.openIn tracFile
	     val lexer = TracParser.makeLexer  (fn _ => case ((TextIO.inputLine) infile) of
                                                   SOME s => s
                                                 | NONE   => "")
     in
       parse_fp lexer
     end

 fun parse_str trac_fp_str = let  
       val parsed = Unsynchronized.ref false 
       fun input_string _  = if !parsed then "" else (parsed := true ;trac_fp_str)
	     val lexer = TracParser.makeLexer input_string
     in
       parse_fp lexer
     end
end
\<close>


end
