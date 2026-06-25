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

theory Datalog
  imports Main LexYacc
  keywords "datalog" :: thy_decl
begin

section \<open>Isabelle/HOL Deep Embedding of Datalog (Syntax/AST)\<close>

type_synonym vname = string
type_synonym pname = string

datatype dl_literal =
    LInt int
(*  | LFloat real *)
  | LBool bool
  | LChar char
  | LString string

datatype dl_agg_op = Count | Avg | Sum | Min | Max

datatype dl_term =
    Var vname
  | Lit dl_literal
  | Agg dl_agg_op vname

datatype dl_atom =
    Pred pname "dl_term list"
  | Neg dl_atom

datatype dl_fact = Fact pname "dl_literal list"
datatype dl_rule = Rule dl_atom "dl_atom list"
datatype dl_query = Query dl_atom

datatype dl_program = Program "dl_fact list" "dl_rule list" "dl_query option"


section \<open>SML AST Definition\<close>

ML \<open>
structure Datalog_AST = 
struct
  type vname = string
  type pname = string

  datatype dl_literal =
      LInt of int
    | LReal of real
    | LBool of bool
    | LChar of char
    | LString of string

  datatype dl_agg_op = Count | Avg | Sum | Min | Max

  datatype dl_term =
      Var of vname
    | Lit of dl_literal
    | Agg of dl_agg_op * vname

  datatype dl_atom =
      Pred of pname * dl_term list
    | Neg of dl_atom

  datatype dl_fact = Fact of pname * dl_literal list
  datatype dl_rule = Rule of dl_atom * dl_atom list
  datatype dl_query = Query of dl_atom

  datatype dl_program = Program of dl_fact list * dl_rule list * dl_query option

  (* AST building helpers to resolve LALR(1) conflicts *)
  datatype dl_clause = CFact of dl_fact | CRule of dl_rule

  fun atom_to_fact (Pred (p, terms)) =
      let
          fun term_to_lit (Lit l) = l
            | term_to_lit _ = raise Fail "Fact contains variable or aggregation"
      in
          Fact (p, map term_to_lit terms)
      end
    | atom_to_fact (Neg _) = raise Fail "Fact cannot be negated"

  fun split_clauses [] = ([], [])
    | split_clauses (CFact f :: cs) =
        let val (fs, rs) = split_clauses cs in (f :: fs, rs) end
    | split_clauses (CRule r :: cs) =
        let val (fs, rs) = split_clauses cs in (fs, r :: rs) end

  fun parse_int s = 
      let val s' = String.map (fn #"-" => #"~" | c => c) s
      in Option.valOf (Int.fromString s') end handle Option => 0

  fun parse_real s = 
      let val s' = String.map (fn #"-" => #"~" | c => c) s
      in Option.valOf (Real.fromString s') end handle Option => 0.0

  fun parse_string s =
      if size s >= 2 then String.substring (s, 1, size s - 2) else s

  fun parse_char s =
      if size s >= 3 then String.sub (s, 1) else #" "
end
\<close>

SML_import \<open>structure Datalog_AST = Datalog_AST\<close>

section \<open>Lexer and Parser Definition\<close>

ml_lex_yacc [verbose] "Datalog" where
lex_user_declarations\<open>
structure KeyWord : sig
    val find : string -> (Position.T * Position.T -> (svalue, Position.T) token) option
end = struct
    val TableSize = 211
    val HashFactor = 5
    fun hash s = foldl (fn (c,v) => (v * HashFactor + (ord c)) mod TableSize) 0 (explode s)
    val HashTable = Array.array(TableSize, nil) : (string * (Position.T * Position.T -> (svalue, Position.T) token)) list Array.array
    fun add (s, v) =
        let val i = hash s
        in Array.update(HashTable, i, (s, v) :: (Array.sub(HashTable, i))) end
    fun find s =
        let val i = hash s
            fun f ((key, v)::r) = if s = key then SOME v else f r
              | f nil = NONE
        in f (Array.sub(HashTable, i)) end

    val _ = List.app add [
         ("not",Tokens.YNOT), ("count",Tokens.YCOUNT), ("avg",Tokens.YAVG),
         ("sum",Tokens.YSUM), ("min",Tokens.YMIN), ("max",Tokens.YMAX),
         ("true",Tokens.YTRUE), ("false",Tokens.YFALSE)
    ]
end
open KeyWord
\<close>
lex_definitions\<open>
%s C L;
alpha=[A-Za-z];
digit=[0-9];
hexdigit=[0-9a-fA-F];
octdigit=[0-7];
bindigit=[01];
idletterordigit=[a-zA-Z0-9_];

optsign=("+"|"-")?;
integer={digit}+;
frac="."{digit}+;
exp=(e|E){optsign}{digit}+;
ws = [\ \t\r\n\f];
\<close>
lex_rules\<open>
<INITIAL>{ws}+  => (lex());
<INITIAL>{alpha}{idletterordigit}* => (
    case find (String.map Char.toLower yytext) of 
        SOME v => 
            let val p = get_pos yypos
                val _ = report_token (yypos, String.size yytext, Markup.keyword1, yytext, "")
            in v(p, p) end
      | _ => tok_val (yypos, yytext, Markup.free, "YPREDICATE", "", Tokens.YPREDICATE, yytext));

<INITIAL>"?"{alpha}{idletterordigit}* => (tok_val (yypos, yytext, Markup.free, "YVARIABLE", "", Tokens.YVARIABLE, yytext));

<INITIAL>{optsign}{integer}({frac}{exp}?|{frac}?{exp}) => (tok_val (yypos, yytext, Markup.numeral, "YFLOAT", "", Tokens.YFLOAT, yytext));
<INITIAL>{optsign}{integer} => (tok_val (yypos, yytext, Markup.numeral, "YINT", "", Tokens.YINT, yytext));
<INITIAL>0[xX]{hexdigit}+   => (tok_val (yypos, yytext, Markup.numeral, "YINT", "", Tokens.YINT, yytext));
<INITIAL>0[bB]{bindigit}+   => (tok_val (yypos, yytext, Markup.numeral, "YINT", "", Tokens.YINT, yytext));
<INITIAL>0{octdigit}+       => (tok_val (yypos, yytext, Markup.numeral, "YINT", "", Tokens.YINT, yytext));

<INITIAL>"'"([^'\\]|\\.)"'" => (tok_val (yypos, yytext, Markup.string, "YCHAR", "", Tokens.YCHAR, yytext));
<INITIAL>"\""([^\"\\]|\\.)*"\"" => (tok_val (yypos, yytext, Markup.string, "YSTRING", "", Tokens.YSTRING, yytext));

<INITIAL>"/*"   => (YYBEGIN C; lex());
<INITIAL>"%"    => (YYBEGIN L; lex());

<INITIAL>":-"   => (tok (yypos, yytext, Markup.operator, "YCOLONDASH", "", Tokens.YCOLONDASH));
<INITIAL>"?-"   => (tok (yypos, yytext, Markup.operator, "YQUESTIONDASH", "", Tokens.YQUESTIONDASH));
<INITIAL>"."    => (tok (yypos, yytext, Markup.delimiter, "YDOT", "", Tokens.YDOT));
<INITIAL>","    => (tok (yypos, yytext, Markup.delimiter, "YCOMMA", "", Tokens.YCOMMA));
<INITIAL>"("    => (tok (yypos, yytext, Markup.delimiter, "YLPAR", "", Tokens.YLPAR));
<INITIAL>")"    => (tok (yypos, yytext, Markup.delimiter, "YRPAR", "", Tokens.YRPAR));
<INITIAL>"<"    => (tok (yypos, yytext, Markup.operator, "YLT", "", Tokens.YLT));
<INITIAL>">"    => (tok (yypos, yytext, Markup.operator, "YGT", "", Tokens.YGT));
<INITIAL>.      => (tok (yypos, yytext, Markup.error, "YILLCH", "", Tokens.YILLCH));

<C>"*/"         => (YYBEGIN INITIAL; lex());
<C>[^*]+        => (lex());
<C>"*"          => (lex());

<L>\n           => (YYBEGIN INITIAL; lex());
<L>[^\n]+       => (lex());
\<close>
and yacc_user_declarations\<open>
open Datalog_AST
\<close>
yacc_definitions\<open>
%eop EOF
%pure
%noshift EOF

%term
        YNOT    |   YCOUNT  |   YAVG    |   YSUM    |   YMIN |
        YMAX    |   YTRUE   |   YFALSE  |   YILLCH  |
        YVARIABLE of string | YPREDICATE of string | YINT of string | YFLOAT of string | YCHAR of string | YSTRING of string |
        YDOT    |   YLPAR   |   YRPAR   |   YCOMMA  |
        YCOLONDASH | YQUESTIONDASH | YLT |  YGT     |
        EOF

%nonterm start_rule of Datalog_AST.dl_program option | program of Datalog_AST.dl_program | clauses of Datalog_AST.dl_clause list | clause of Datalog_AST.dl_clause |
         query of Datalog_AST.dl_query | atom of Datalog_AST.dl_atom | atoms of Datalog_AST.dl_atom list | 
         variableOrLiteral of Datalog_AST.dl_term | variableOrLiterals of Datalog_AST.dl_term list | aggregateVariable of Datalog_AST.dl_term | 
         aggregateOp of Datalog_AST.dl_agg_op | variable of Datalog_AST.dl_term | predicate of Datalog_AST.pname | literal of Datalog_AST.dl_literal

%keyword
        YNOT        YCOUNT      YAVG        YSUM        YMIN
        YMAX        YTRUE       YFALSE

%prefer YPREDICATE YDOT YCOMMA YLPAR
\<close>
yacc_rules\<open>
start_rule: program (SOME program)

program: clauses query                     (let val (fs, rs) = split_clauses clauses in Program (fs, rs, SOME query) end)
       | clauses                           (let val (fs, rs) = split_clauses clauses in Program (fs, rs, NONE) end)
       | query                             (Program ([], [], SOME query))

clauses: clause                            ([clause])
       | clauses clause                    (clauses @ [clause])

clause: atom YDOT                          (CFact (atom_to_fact atom))
      | atom YCOLONDASH atoms YDOT         (CRule (Rule (atom, atoms)))

query: YQUESTIONDASH atom                  (Query atom)

atom: predicate YLPAR variableOrLiterals YRPAR (Pred (predicate, variableOrLiterals))
    | YNOT atom                            (Neg atom)

atoms: atom                                ([atom])
     | atoms YCOMMA atom                   (atoms @ [atom])

variableOrLiteral: variable                (variable)
                 | literal                 (Lit literal)
                 | aggregateVariable       (aggregateVariable)

variableOrLiterals: variableOrLiteral                           ([variableOrLiteral])
                  | variableOrLiterals YCOMMA variableOrLiteral (variableOrLiterals @ [variableOrLiteral])

aggregateVariable: aggregateOp YLT variable YGT (
                     case variable of
                         Var v => Agg (aggregateOp, v)
                       | _ => raise Fail "Expected variable in aggregation"
                   )

aggregateOp: YCOUNT                        (Count)
           | YAVG                          (Avg)
           | YSUM                          (Sum)
           | YMIN                          (Min)
           | YMAX                          (Max)

variable: YVARIABLE                        (Var YVARIABLE)
predicate: YPREDICATE                      (YPREDICATE)

literal: YINT                              (LInt (parse_int YINT))
       | YFLOAT                            (LReal (parse_real YFLOAT))
       | YTRUE                             (LBool true)
       | YFALSE                            (LBool false)
       | YCHAR                             (LChar (parse_char YCHAR))
       | YSTRING                           (LString (parse_string YSTRING))
\<close>


section \<open>Translation and Isar Top-Level Command\<close>

ML \<open>
structure Datalog_AST_Translator =
struct
  open Datalog_AST

  fun mk_option T NONE = Const (\<^const_name>\<open>None\<close>, Type (\<^type_name>\<open>option\<close>, [T]))
    | mk_option T (SOME t) = Const (\<^const_name>\<open>Some\<close>, T --> Type (\<^type_name>\<open>option\<close>, [T])) $ t

  fun mk_literal ctxt l = 
    case l of
      LInt i => \<^const>\<open>LInt\<close> $ HOLogic.mk_number \<^typ>\<open>int\<close> i
(*    | LReal r => let val r_term = Syntax.read_term ctxt (Real.toString r ^ " :: real") in \<^const>\<open>LFloat\<close> $ r_term end *)
    | LBool b => \<^const>\<open>LBool\<close> $ (if b then \<^term>\<open>True\<close> else \<^term>\<open>False\<close>)
    | LChar c => let val c_term = Syntax.read_term ctxt ("CHR ''" ^ String.str c ^ "''") in \<^const>\<open>LChar\<close> $ c_term end
    | LString s => \<^const>\<open>LString\<close> $ HOLogic.mk_string s

  fun mk_agg_op op_val =
    case op_val of Count => \<^const>\<open>Count\<close> | Avg => \<^const>\<open>Avg\<close> | Sum => \<^const>\<open>Sum\<close> | Min => \<^const>\<open>Min\<close> | Max => \<^const>\<open>Max\<close>

  fun mk_term ctxt t =
    case t of
      Var v => \<^const>\<open>Var\<close> $ HOLogic.mk_string v
    | Lit l => \<^const>\<open>Lit\<close> $ mk_literal ctxt l
    | Agg (op_val, v) => \<^const>\<open>Agg\<close> $ mk_agg_op op_val $ HOLogic.mk_string v

  fun mk_atom ctxt a =
    case a of
      Pred (p, ts) => \<^const>\<open>Pred\<close> $ HOLogic.mk_string p $ HOLogic.mk_list \<^typ>\<open>dl_term\<close> (map (mk_term ctxt) ts)
    | Neg a_in => \<^const>\<open>Neg\<close> $ mk_atom ctxt a_in

  fun mk_fact ctxt f =
    case f of Fact (p, ls) => \<^const>\<open>Fact\<close> $ HOLogic.mk_string p $ HOLogic.mk_list \<^typ>\<open>dl_literal\<close> (map (mk_literal ctxt) ls)

  fun mk_rule ctxt r =
    case r of Rule (h, bs) => \<^const>\<open>Rule\<close> $ mk_atom ctxt h $ HOLogic.mk_list \<^typ>\<open>dl_atom\<close> (map (mk_atom ctxt) bs)

  fun mk_query ctxt q =
    case q of Query a => \<^const>\<open>Query\<close> $ mk_atom ctxt a

  fun mk_program ctxt p =
    case p of
      Program (fs, rs, q_opt) =>
        \<^const>\<open>Program\<close> 
        $ HOLogic.mk_list \<^typ>\<open>dl_fact\<close> (map (mk_fact ctxt) fs)
        $ HOLogic.mk_list \<^typ>\<open>dl_rule\<close> (map (mk_rule ctxt) rs)
        $ mk_option \<^typ>\<open>dl_query\<close> (Option.map (mk_query ctxt) q_opt)
end

fun define_datalog (binding, source) lthy = 
    let 
      val ast_opt = Datalog.parse_source lthy source
    in  
      case ast_opt of
        SOME ast => 
          let
            val raw_term = Datalog_AST_Translator.mk_program lthy ast
            val hol_term = Syntax.check_term lthy raw_term
            
            val ((_, _), lthy') = 
                Local_Theory.define ((binding, NoSyn), ((Thm.def_binding binding, []), hol_term)) lthy
            
            val _ = writeln ("Successfully defined Datalog program: " ^ Binding.name_of binding)
          in
            lthy'
          end
      | NONE => error "Failed to parse Datalog."
    end

val _ = Outer_Syntax.local_theory @{command_keyword "datalog"}
        "Parse a Datalog block and define it as a HOL constant" 
        (Parse.binding -- Parse.input Parse.cartouche >> define_datalog)
\<close>


section \<open>Example\<close>

datalog datalog_example \<open>
  /* A comment */
  parent("john", "mary").
  ancestor(?x, ?y) :- parent(?x, ?y).
\<close>

thm "datalog_example_def"

datalog datalog_example2 \<open>parent("john", "mary"). ancestor(?x, ?y) :- parent(?x, ?y).\<close>

lemma \<open>datalog_example = datalog_example2\<close>
  by(metis datalog_example_def datalog_example2_def)

end
