(* SPDX-License-Identifier: BSD-3-Clause *)
structure Tokens = Tokens
open TracProtocol
  
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
%header (functor TracTransactionLexFun(structure Tokens: TracTransaction_TOKENS));
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

"("             => (Tokens.OPENP(yytext,inputPos_half yypos,inputPos_half yypos));
")"             => (Tokens.CLOSEP(yytext,inputPos_half yypos,inputPos_half yypos));
"{"             => (Tokens.OPENB(yytext,inputPos_half yypos,inputPos_half yypos));
"}"             => (Tokens.CLOSEB(yytext,inputPos_half yypos,inputPos_half yypos));
"{|"            => (Tokens.OPENSCRYPT(yytext,inputPos_half yypos,inputPos_half yypos));
"|}"            => (Tokens.CLOSESCRYPT(yytext,inputPos_half yypos,inputPos_half yypos));
":"             => (Tokens.COLON(yytext,inputPos_half yypos,inputPos_half yypos));
";"             => (Tokens.SEMICOLON(yytext,inputPos_half yypos,inputPos_half yypos));
"->"            => (Tokens.ARROW(yytext,inputPos_half yypos,inputPos_half yypos));
"%"             => (Tokens.PERCENT(yytext,inputPos_half yypos,inputPos_half yypos));
"!="            => (Tokens.UNEQUAL(yytext,inputPos_half yypos,inputPos_half yypos));
"!"             => (Tokens.EXCLAM (yytext,inputPos_half yypos,inputPos_half yypos));
"."             => (Tokens.DOT(yytext,inputPos_half yypos,inputPos_half yypos));
","             => (Tokens.COMMA(yytext,inputPos_half yypos,inputPos_half yypos));
"["             => (Tokens.OPENSQB(yytext,inputPos_half yypos,inputPos_half yypos));
"]"             => (Tokens.CLOSESQB(yytext,inputPos_half yypos,inputPos_half yypos));
"++"            => (Tokens.UNION(yytext,inputPos_half yypos,inputPos_half yypos));
"{..}"          => (Tokens.INFINITESET(yytext,inputPos_half yypos,inputPos_half yypos));
"Protocol"      => (Tokens.PROTOCOL(yytext,inputPos_half yypos,inputPos_half yypos));
"Knowledge"     => (Tokens.KNOWLEDGE(yytext,inputPos_half yypos,inputPos_half yypos));
"where"         => (Tokens.WHERE(yytext,inputPos_half yypos,inputPos_half yypos));
"Types"         => (Tokens.TYPES(yytext,inputPos_half yypos,inputPos_half yypos));
"Enumerations"  => (Tokens.ENUMERATIONS(yytext,inputPos_half yypos,inputPos_half yypos));
"Actions"       => (Tokens.ACTIONS(yytext,inputPos_half yypos,inputPos_half yypos));
"Abstraction"   => (Tokens.ABSTRACTION(yytext,inputPos_half yypos,inputPos_half yypos));
"Goals"         => (Tokens.GOALS(yytext,inputPos_half yypos,inputPos_half yypos));
"authenticates" => (Tokens.AUTHENTICATES(yytext,inputPos_half yypos,inputPos_half yypos));
"weakly"        => (Tokens.WEAKLY(yytext,inputPos_half yypos,inputPos_half yypos));
"on"            => (Tokens.ON(yytext,inputPos_half yypos,inputPos_half yypos));
"secret"        => (Tokens.TSECRET(yytext,inputPos_half yypos,inputPos_half yypos));
"between"       => (Tokens.TBETWEEN(yytext,inputPos_half yypos,inputPos_half yypos));
"Sets"          => (Tokens.SETS(yytext,inputPos_half yypos,inputPos_half yypos));
"Functions"     => (Tokens.FUNCTIONS(yytext,inputPos_half yypos,inputPos_half yypos));
"Public"        => (Tokens.PUBLIC(yytext,inputPos_half yypos,inputPos_half yypos));
"Private"       => (Tokens.PRIVATE(yytext,inputPos_half yypos,inputPos_half yypos));
"Analysis"      => (Tokens.ANALYSIS(yytext,inputPos_half yypos,inputPos_half yypos));
"Transactions"  => (Tokens.TRANSACTIONS(yytext,inputPos_half yypos,inputPos_half yypos));
"Abbreviations" => (Tokens.ABBREVIATIONS(yytext,inputPos_half yypos,inputPos_half yypos));
"receive"       => (Tokens.RECEIVE(yytext,inputPos_half yypos,inputPos_half yypos));
"send"          => (Tokens.SEND(yytext,inputPos_half yypos,inputPos_half yypos));
"let"           => (Tokens.LET(yytext,inputPos_half yypos,inputPos_half yypos));
"in"            => (Tokens.IN(yytext,inputPos_half yypos,inputPos_half yypos));
"notin"         => (Tokens.NOTIN(yytext,inputPos_half yypos,inputPos_half yypos));
"insert"        => (Tokens.INSERT(yytext,inputPos_half yypos,inputPos_half yypos));
"delete"        => (Tokens.DELETE(yytext,inputPos_half yypos,inputPos_half yypos));
"new"           => (Tokens.NEW(yytext,inputPos_half yypos,inputPos_half yypos));
"attack"        => (Tokens.ATTACK(yytext,inputPos_half yypos,inputPos_half yypos));
"/"             => (Tokens.SLASH(yytext,inputPos_half yypos,inputPos_half yypos));
"//"            => (Tokens.DOUBLESLASH(yytext,inputPos_half yypos,inputPos_half yypos));
"?"             => (Tokens.QUESTION(yytext,inputPos_half yypos,inputPos_half yypos));
"="             => (Tokens.EQUAL(yytext,inputPos_half yypos,inputPos_half yypos));
"=="            => (Tokens.DOUBLEEQUAL(yytext,inputPos_half yypos,inputPos_half yypos));
"_"             => (Tokens.UNDERSCORE(yytext,inputPos_half yypos,inputPos_half yypos));
"*"             => (Tokens.STAR(yytext,inputPos_half yypos,inputPos_half yypos));
"of"            => (Tokens.OF(yytext,inputPos_half yypos,inputPos_half yypos));
"or"            => (Tokens.OR(yytext,inputPos_half yypos,inputPos_half yypos));
"forall"        => (Tokens.FORALL(yytext,inputPos_half yypos,inputPos_half yypos));


{digit}+                          => (Tokens.INTEGER_LITERAL(yytext,inputPos_half yypos,inputPos_half yypos));
"'"({alpha}|{ws}|{digit})*(("."|"_"|"/"|"-")*({alpha}|{ws}|{digit})*)*"'"  => (Tokens.STRING_LITERAL(yytext,inputPos_half yypos,inputPos_half yypos));
{lower}({alpha}|{digit})*("'")*   => (Tokens.LOWER_STRING_LITERAL(yytext,inputPos_half yypos,inputPos_half yypos));
{upper}({alpha}|{digit})*("'")*   => (Tokens.UPPER_STRING_LITERAL(yytext,inputPos_half yypos,inputPos_half yypos));


.      => (error' ("Bad character: "^yytext,
		    ((#1 (!pos), yypos - (#3(!pos)), (#3 (!pos)))),
		    ((#1 (!pos), yypos - (#3(!pos)), (#3 (!pos))))));
