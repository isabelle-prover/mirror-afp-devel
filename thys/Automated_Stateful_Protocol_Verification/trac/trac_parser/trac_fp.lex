(* SPDX-License-Identifier: BSD-3-Clause *)
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



%%
%header (functor TracLexFun(structure Tokens: Trac_TOKENS));
alpha=[A-Za-z_];
upper=[A-Z];
lower=[a-z];
digit=[0-9];
ws = [\ \t];
%%

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
