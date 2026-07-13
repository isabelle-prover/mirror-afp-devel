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
  Calc 
imports
  LexYacc
keywords
  "calc" :: diag
begin

ml_lex_yacc [verbose] "Calc" where
lex_definitions\<open>
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

%left SUB PLUS
%left TIMES DIV
%right CARAT

%term ID of string | NUM of int | PLUS | TIMES | PRINT |
      SEMI | EOF | CARAT | DIV | SUB
%nonterm EXP of int | START of int option


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

text\<open>Defining a simple Isar-toplevel command\<close>
ML\<open>
fun calc source thy = 
    let 
      val ctxt = Proof_Context.init_global thy
      val _ = writeln((Int.toString (the (Calc.parse_source ctxt source))))
    in thy end

val _ = Outer_Syntax.command @{command_keyword "calc"}
        "A simple inline calculator" 
        (Parse.input Parse.cartouche >> (fn source => Toplevel.theory (calc source)))
\<close>

calc\<open>
1
  /
    3
   * (201 - 7)
\<close>

end
