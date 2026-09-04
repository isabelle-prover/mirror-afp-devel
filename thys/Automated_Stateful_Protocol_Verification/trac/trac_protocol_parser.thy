(*  Title:      trac_protocol_parser.thy
    Author:     Andreas Viktor Hess, DTU
    Author:     Sebastian A. Mödersheim, DTU
    Author:     Achim D. Brucker, University of Exeter
    Author:     Anders Schlichtkrull, DTU
    SPDX-License-Identifier: BSD-3-Clause
*)

section \<open>Parser for the Trac Format\<close>
theory
  trac_protocol_parser
  imports
    "trac_term"
    "Isabelle_Lex-Yacc.LexYacc"
begin

SML_import \<open>val error = error\<close>
SML_import \<open>structure Symbol_Pos = Symbol_Pos\<close>
SML_import \<open>structure Position = struct open Position end\<close>
SML_import \<open>structure TracProtocol=TracProtocol\<close>
SML_import \<open>structure Trac_Term=Trac_Term\<close>
SML_import \<open>structure Trac_Utils=Trac_Utils\<close>

ml_lex_yacc[expert] TracTransaction where 
lex_user_declarations \<open>
structure Tokens = Tokens

open TracProtocol
  
type pos = Position.T
type svalue = Tokens.svalue

type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue, pos) token

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
      Position.report pos (Markup.entity "free" name)
    )
  end

fun report_fun yypos yylen name =
  let val pos = get_range yypos yylen in
    if pos = Position.none then () else (
      Position.report pos (Markup.entity "constant" name)
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
%header (functor TracTransactionLexFun(structure Tokens: TracTransaction_TOKENS));
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

"("             => (report_kw yypos (size yytext) Markup.keyword3; Tokens.OPENP(yytext, get_pos yypos, get_pos (yypos + size yytext)));
")"             => (report_kw yypos (size yytext) Markup.keyword3; Tokens.CLOSEP(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"{"             => (report_kw yypos (size yytext) Markup.keyword3; Tokens.OPENB(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"}"             => (report_kw yypos (size yytext) Markup.keyword3; Tokens.CLOSEB(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"{|"            => (report_kw yypos (size yytext) Markup.keyword3; Tokens.OPENSCRYPT(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"|}"            => (report_kw yypos (size yytext) Markup.keyword3; Tokens.CLOSESCRYPT(yytext, get_pos yypos, get_pos (yypos + size yytext)));
":"             => (report_kw yypos (size yytext) Markup.keyword3; Tokens.COLON(yytext, get_pos yypos, get_pos (yypos + size yytext)));
";"             => (report_kw yypos (size yytext) Markup.keyword3; Tokens.SEMICOLON(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"->"            => (report_kw yypos (size yytext) Markup.keyword3; Tokens.ARROW(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"%"             => (report_kw yypos (size yytext) Markup.keyword3; Tokens.PERCENT(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"!="            => (report_kw yypos (size yytext) Markup.keyword3; Tokens.UNEQUAL(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"!"             => (report_kw yypos (size yytext) Markup.keyword3; Tokens.EXCLAM (yytext, get_pos yypos, get_pos (yypos + size yytext)));
"."             => (report_kw yypos (size yytext) Markup.keyword3; Tokens.DOT(yytext, get_pos yypos, get_pos (yypos + size yytext)));
","             => (report_kw yypos (size yytext) Markup.keyword3; Tokens.COMMA(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"["             => (report_kw yypos (size yytext) Markup.keyword3; Tokens.OPENSQB(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"]"             => (report_kw yypos (size yytext) Markup.keyword3; Tokens.CLOSESQB(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"++"            => (report_kw yypos (size yytext) Markup.keyword3; Tokens.UNION(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"{..}"          => (report_kw yypos (size yytext) Markup.keyword3; Tokens.INFINITESET(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"Protocol"      => (report_kw yypos (size yytext) Markup.keyword1; Tokens.PROTOCOL(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"Knowledge"     => (report_kw yypos (size yytext) Markup.keyword1; Tokens.KNOWLEDGE(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"where"         => (report_kw yypos (size yytext) Markup.keyword2; Tokens.WHERE(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"Types"         => (report_kw yypos (size yytext) Markup.keyword1; Tokens.TYPES(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"Enumerations"  => (report_kw yypos (size yytext) Markup.keyword1; Tokens.ENUMERATIONS(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"Actions"       => (report_kw yypos (size yytext) Markup.keyword1; Tokens.ACTIONS(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"Abstraction"   => (report_kw yypos (size yytext) Markup.keyword1; Tokens.ABSTRACTION(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"Goals"         => (report_kw yypos (size yytext) Markup.keyword1; Tokens.GOALS(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"authenticates" => (report_kw yypos (size yytext) Markup.keyword2; Tokens.AUTHENTICATES(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"weakly"        => (report_kw yypos (size yytext) Markup.keyword2; Tokens.WEAKLY(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"on"            => (report_kw yypos (size yytext) Markup.keyword2; Tokens.ON(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"secret"        => (report_kw yypos (size yytext) Markup.keyword2; Tokens.TSECRET(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"between"       => (report_kw yypos (size yytext) Markup.keyword2; Tokens.TBETWEEN(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"Sets"          => (report_kw yypos (size yytext) Markup.keyword1; Tokens.SETS(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"Functions"     => (report_kw yypos (size yytext) Markup.keyword1; Tokens.FUNCTIONS(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"Public"        => (report_kw yypos (size yytext) Markup.keyword2; Tokens.PUBLIC(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"Private"       => (report_kw yypos (size yytext) Markup.keyword2; Tokens.PRIVATE(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"Analysis"      => (report_kw yypos (size yytext) Markup.keyword1; Tokens.ANALYSIS(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"Transactions"  => (report_kw yypos (size yytext) Markup.keyword1; Tokens.TRANSACTIONS(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"Abbreviations" => (report_kw yypos (size yytext) Markup.keyword1; Tokens.ABBREVIATIONS(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"receive"       => (report_kw yypos (size yytext) Markup.keyword2; Tokens.RECEIVE(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"send"          => (report_kw yypos (size yytext) Markup.keyword2; Tokens.SEND(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"let"           => (report_kw yypos (size yytext) Markup.keyword2; Tokens.LET(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"in"            => (report_kw yypos (size yytext) Markup.keyword2; Tokens.IN(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"notin"         => (report_kw yypos (size yytext) Markup.keyword2; Tokens.NOTIN(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"insert"        => (report_kw yypos (size yytext) Markup.keyword2; Tokens.INSERT(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"delete"        => (report_kw yypos (size yytext) Markup.keyword2; Tokens.DELETE(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"new"           => (report_kw yypos (size yytext) Markup.keyword2; Tokens.NEW(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"attack"        => (report_kw yypos (size yytext) Markup.keyword2; Tokens.ATTACK(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"/"             => (report_kw yypos (size yytext) Markup.keyword3; Tokens.SLASH(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"//"            => (report_kw yypos (size yytext) Markup.keyword3; Tokens.DOUBLESLASH(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"?"             => (report_kw yypos (size yytext) Markup.keyword3; Tokens.QUESTION(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"="             => (report_kw yypos (size yytext) Markup.keyword3; Tokens.EQUAL(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"=="            => (report_kw yypos (size yytext) Markup.keyword3; Tokens.DOUBLEEQUAL(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"_"             => (report_kw yypos (size yytext) Markup.keyword3; Tokens.UNDERSCORE(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"*"             => (report_kw yypos (size yytext) Markup.keyword3; Tokens.STAR(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"of"            => (report_kw yypos (size yytext) Markup.keyword2; Tokens.OF(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"or"            => (report_kw yypos (size yytext) Markup.keyword2; Tokens.OR(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"forall"        => (report_kw yypos (size yytext) Markup.keyword2; Tokens.FORALL(yytext, get_pos yypos, get_pos (yypos + size yytext)));


{digit}+                                                                  => (Tokens.INTEGER_LITERAL(yytext, get_pos yypos, get_pos (yypos + size yytext)));
"'"({alpha}|{ws}|{digit})*(("."|"_"|"/"|"-")*({alpha}|{ws}|{digit})*)*"'" => (report_str yypos (size yytext); Tokens.STRING_LITERAL(yytext, get_pos yypos, get_pos (yypos + size yytext)));
{lower}({alpha}|{digit})*("'")*   => (report_fun yypos (size yytext) yytext; Tokens.LOWER_STRING_LITERAL(yytext, get_pos yypos, get_pos (yypos + size yytext)));
{upper}({alpha}|{digit})*("'")*   => (report_var yypos (size yytext) yytext; Tokens.UPPER_STRING_LITERAL(yytext, get_pos yypos, get_pos (yypos + size yytext)));


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

%name TracTransaction

%term EOF
    | OPENP of string
    | CLOSEP of string
    | OPENB of string
    | CLOSEB of string
    | OPENSCRYPT of string
    | CLOSESCRYPT of string
    | COLON of string
    | SEMICOLON of string
    | SECCH of string
    | AUTHCH of string
    | CONFCH of string
    | INSECCH of string
    | FAUTHCH of string
    | FSECCH of string
    | PERCENT of string
    | UNEQUAL of string
    | EXCLAM  of string
    | DOT of string
    | COMMA of string
    | OPENSQB of string
    | CLOSESQB of string
    | UNION of string
    | INFINITESET of string
    | PROTOCOL of string
    | KNOWLEDGE of string
    | WHERE of string
    | ACTIONS of string
    | ABSTRACTION of string
    | GOALS of string
    | AUTHENTICATES of string
    | WEAKLY of string
    | ON of string
    | TSECRET of string
    | TBETWEEN of string
    | Sets of string
    | FUNCTIONS of string
    | PUBLIC of string
    | PRIVATE of string
    | RECEIVE of string
    | SEND of string
    | LET of string
    | IN of string
    | NOTIN of string
    | INSERT of string
    | DELETE of string
    | NEW of string
    | ATTACK of string
    | SLASH of string
    | DOUBLESLASH of string
    | QUESTION of string
    | EQUAL of string
    | DOUBLEEQUAL of string
    | TYPES of string
    | ENUMERATIONS of string
    | SETS of string
    | ARROW of string
    | ANALYSIS of string
    | TRANSACTIONS of string
    | ABBREVIATIONS of string
    | STRING_LITERAL of string
    | UPPER_STRING_LITERAL of string
    | LOWER_STRING_LITERAL of string
    | UNDERSCORE of string
    | INTEGER_LITERAL of string
    | STAR of string
    | OF of string
    | OR of string
    | FORALL of string
                    
%nonterm START of TracProtocol.protocol
       | name of string 
       | arity of int 
       | uident of string
       | lident of string
       | ident of string
       | trac_protocol of TracProtocol.protocol
       | protocol_spec of TracProtocol.protocol
       | type_union of (string list)
       | enum_spec of (string * TracProtocol.enum_spec_elem) 
       | enum_specs of (string * TracProtocol.enum_spec_elem) list
       | type_specs of string list
       | lidents of string list
       | uidents of string list
       | set_specs of TracProtocol.set_spec     
       | set_spec of TracProtocol.set_spec_elem    
       | priv_or_pub_fun_spec of TracProtocol.fun_spec      
       | fun_specs of TracProtocol.funT list 
       | fun_spec of TracProtocol.funT     
       | priv_fun_spec of TracProtocol.funT list 
       | pub_fun_spec of TracProtocol.funT list     
       | analysis_spec of TracProtocol.anaT
       | transaction_spec_head of string option
       | transaction_spec of TracProtocol.transaction list
       | rule of TracProtocol.ruleT
       | head of string * string list
       | head_params of string list 
       | keys of Trac_Term.Msg list
       | result of string list
       | msg_atom of Trac_Term.Msg
       | msg of Trac_Term.Msg
       | msgs of Trac_Term.Msg list
       | setexp of string * Trac_Term.Msg list
       | action of TracProtocol.prot_label * TracProtocol.action  
       | actions of (TracProtocol.prot_label * TracProtocol.action) list
       | action_ext of TracProtocol.labeled_action 
       | actions_ext of TracProtocol.labeled_action list
       | ineq_aux of string
       | ineq of string * string
       | ineqs of (string * string) list
       | transaction_name of TracProtocol.transaction_name
       | typ of Trac_Term.MsgType 
       | typs of Trac_Term.MsgType list 
       | vars of string list
       | vars_typ of string list * Trac_Term.MsgType
       | vars_typs of (string list * Trac_Term.MsgType) list
       | vars_opts of (string list * Trac_Term.MsgType) list
       | negcheck_disj of TracProtocol.Negcheck list
       | negcheck of TracProtocol.Negcheck
       | abbrev of string * Trac_Term.Msg list
       | abbrev_head of string * string list
       | abbrev_decl of TracProtocol.abbreviation
       | abbrev_spec of TracProtocol.abbreviation list
                     
%pos Position.T

%noshift EOF
\<close>
yacc_rules\<open>
START:         trac_protocol                                      (trac_protocol)
trac_protocol: PROTOCOL COLON name protocol_spec                  (TracProtocol.update_name protocol_spec name)

protocol_spec: TYPES COLON enum_specs protocol_spec                       (error "Using the name \"Types\" for the section containing the enumeration declarations is deprecated - use \"Enumerations\" instead.")
             | ENUMERATIONS COLON enum_specs protocol_spec                (TracProtocol.update_enum_spec protocol_spec enum_specs)
             | TYPES COLON type_specs protocol_spec                       (TracProtocol.update_type_spec protocol_spec type_specs)
             | SETS COLON  set_specs protocol_spec                        (TracProtocol.update_sets protocol_spec set_specs)
             | FUNCTIONS COLON priv_or_pub_fun_spec protocol_spec         (TracProtocol.update_functions protocol_spec priv_or_pub_fun_spec)
             | ANALYSIS COLON analysis_spec protocol_spec                 (TracProtocol.update_analysis protocol_spec analysis_spec)
             | transaction_spec_head COLON transaction_spec protocol_spec (TracProtocol.update_transactions transaction_spec_head protocol_spec transaction_spec)
             | ABBREVIATIONS COLON abbrev_spec protocol_spec              (TracProtocol.update_abbreviations protocol_spec abbrev_spec)
             |                                                            (TracProtocol.empty)

type_union:    ident                                             ([ident])
             | ident UNION type_union                            (ident::type_union)


type_specs:    ident                                             ([ident])
             | ident type_specs                                  (ident::type_specs)
 
enum_specs:    enum_spec                                         ([enum_spec])
             | enum_spec enum_specs                              (enum_spec::enum_specs)
enum_spec:     ident EQUAL OPENB lidents CLOSEB                  ((ident, TracProtocol.Consts lidents))
             | ident EQUAL type_union                            ((ident, TracProtocol.Union type_union))
             | ident EQUAL INFINITESET                           ((ident, TracProtocol.InfiniteSet))

set_specs:     set_spec                                          ([set_spec])
             | set_spec set_specs                                (set_spec::set_specs)
set_spec:      ident SLASH arity                                 ((ident, arity, false))
             | ident DOUBLESLASH arity                           ((ident, arity, true))
                            
priv_or_pub_fun_spec: pub_fun_spec priv_or_pub_fun_spec       (TracProtocol.update_fun_public priv_or_pub_fun_spec pub_fun_spec)
                    | priv_fun_spec priv_or_pub_fun_spec      (TracProtocol.update_fun_private priv_or_pub_fun_spec priv_fun_spec)   
                    |                                         (TracProtocol.fun_empty)
pub_fun_spec: PUBLIC fun_specs                                (fun_specs)
priv_fun_spec: PRIVATE fun_specs                              (fun_specs)
fun_specs: fun_spec                                           ([fun_spec])
         | fun_spec fun_specs                                 (fun_spec::fun_specs)
fun_spec:      lident SLASH arity                             ((lident, arity, NONE))
        |      lident SLASH arity COLON typ                   ((lident, arity, SOME(typ)))

analysis_spec: rule                                           ([rule])
             | rule analysis_spec                             (rule::analysis_spec)
             
rule: head ARROW result                                       ((head,[],result)) 
    | head QUESTION keys ARROW result                         ((head,keys,result)) 

head: LOWER_STRING_LITERAL OPENP head_params CLOSEP       ((LOWER_STRING_LITERAL,head_params))

head_params: UPPER_STRING_LITERAL                         ([UPPER_STRING_LITERAL])
           | UPPER_STRING_LITERAL COMMA head_params       ([UPPER_STRING_LITERAL]@head_params)

keys: msgs                                                (msgs)

result: UPPER_STRING_LITERAL                              ([UPPER_STRING_LITERAL])
      | UPPER_STRING_LITERAL COMMA result                 ([UPPER_STRING_LITERAL]@result)


transaction_spec_head: TRANSACTIONS                       (NONE)
                     | TRANSACTIONS OF LOWER_STRING_LITERAL (SOME LOWER_STRING_LITERAL)

transaction_spec: transaction_name actions_ext DOT                  ([TracProtocol.mkTransaction transaction_name actions_ext])
                | transaction_name actions_ext DOT transaction_spec ((TracProtocol.mkTransaction transaction_name actions_ext)::transaction_spec)

ineq_aux: UNEQUAL UPPER_STRING_LITERAL                    (UPPER_STRING_LITERAL)

ineq: UPPER_STRING_LITERAL ineq_aux                       ((UPPER_STRING_LITERAL,ineq_aux))

ineqs: ineq                                               ([ineq])
     | ineq COMMA ineqs                                   ([ineq]@ineqs)
                       
transaction_name: ident OPENP vars_typs CLOSEP WHERE ineqs    ((ident,vars_typs,ineqs))
                | ident OPENP vars_typs CLOSEP                ((ident,vars_typs,[]))
                | ident OPENP CLOSEP                          ((ident,[],[]))
   


abbrev: ident EXCLAM OPENSQB CLOSESQB                   ((ident,[]))
      | ident EXCLAM OPENSQB msgs CLOSESQB              ((ident,msgs))

actions: action                                         ([action])
       | action actions                                 (action::actions)

action: RECEIVE msgs                                  ((TracProtocol.LabelN,TracProtocol.RECEIVE(msgs)))
      | SEND msgs                                     ((TracProtocol.LabelN,TracProtocol.SEND(msgs)))
      | msg DOUBLEEQUAL msg                           ((TracProtocol.LabelN,TracProtocol.EQUATION(msg1,msg2)))
      | LET msg EQUAL msg                             ((TracProtocol.LabelN,TracProtocol.LETBINDING(msg1,msg2)))
      | msg IN setexp                                 ((TracProtocol.LabelN,TracProtocol.IN(msg,setexp)))
      | msg NOTIN lident OPENP UNDERSCORE CLOSEP      ((TracProtocol.LabelN,TracProtocol.NOTINANY(msg,lident)))
      | negcheck_disj                                 ((TracProtocol.LabelN,TracProtocol.NEGCHECKS([],negcheck_disj)))
      | negcheck_disj FORALL vars_typs                ((TracProtocol.LabelN,TracProtocol.NEGCHECKS(vars_typs,negcheck_disj)))
      | INSERT msg setexp                             ((TracProtocol.LabelN,TracProtocol.INSERT(msg,setexp)))
      | DELETE msg setexp                             ((TracProtocol.LabelN,TracProtocol.DELETE(msg,setexp)))
      | NEW vars_opts                                 ((TracProtocol.LabelS,TracProtocol.NEW(vars_opts)))
      | ATTACK                                        ((TracProtocol.LabelN,TracProtocol.ATTACK))
      | STAR RECEIVE msgs                             ((TracProtocol.LabelS,TracProtocol.RECEIVE(msgs)))
      | STAR SEND msgs                                ((TracProtocol.LabelS,TracProtocol.SEND(msgs)))
      | STAR msg DOUBLEEQUAL msg                      ((TracProtocol.LabelS,TracProtocol.EQUATION(msg1,msg2)))
      | STAR LET msg EQUAL msg                        ((TracProtocol.LabelS,TracProtocol.LETBINDING(msg1,msg2)))
      | STAR msg IN setexp                            ((TracProtocol.LabelS,TracProtocol.IN(msg,setexp)))
      | STAR msg NOTIN lident OPENP UNDERSCORE CLOSEP ((TracProtocol.LabelS,TracProtocol.NOTINANY(msg,lident)))
      | STAR negcheck_disj                            ((TracProtocol.LabelS,TracProtocol.NEGCHECKS([],negcheck_disj)))
      | STAR negcheck_disj FORALL vars_typs           ((TracProtocol.LabelS,TracProtocol.NEGCHECKS(vars_typs,negcheck_disj)))
      | STAR INSERT msg setexp                        ((TracProtocol.LabelS,TracProtocol.INSERT(msg,setexp)))
      | STAR DELETE msg setexp                        ((TracProtocol.LabelS,TracProtocol.DELETE(msg,setexp)))

action_ext: abbrev                                    (TracProtocol.ABBREVIATION(abbrev))
          | action                                    (TracProtocol.LABELED_ACTION(action))

actions_ext: action_ext                               ([action_ext])
           | action_ext actions_ext                   (action_ext::actions_ext)
          
typ: UPPER_STRING_LITERAL                             (Trac_Term.TAtom(UPPER_STRING_LITERAL))
   | LOWER_STRING_LITERAL                             (Trac_Term.TAtom(LOWER_STRING_LITERAL))
   | LOWER_STRING_LITERAL OPENP typs CLOSEP           (Trac_Term.TComp(LOWER_STRING_LITERAL,typs))

typs: typ                                             ([typ])
    | typ COMMA typs                                  (typ::typs)

vars: uident                                          ([uident])
    | uident COMMA vars                               (uident::vars)

vars_typ: vars COLON typ                              ((vars,typ))

vars_typs: vars_typ                                   ([vars_typ])
         | vars_typ COMMA vars_typs                   (vars_typ::vars_typs)

vars_opts: vars                                       ([(vars,Trac_Term.TAtom(Trac_Utils.value_trac_typeN))])
         | vars_typs                                  (vars_typs)

setexp: lident                                        ((lident,[]))
      | lident OPENP msgs CLOSEP                      ((lident,msgs))

negcheck_disj: negcheck                               ([negcheck])
             | negcheck OR negcheck_disj              (negcheck::negcheck_disj)

negcheck: msg UNEQUAL msg                             (TracProtocol.INEQ(msg1,msg2))
        | msg NOTIN setexp                            (TracProtocol.NOTIN(msg,setexp))

msg_atom: uident                                      (Var(uident))
        | lident                                      (Const(lident))

msg: msg_atom                                         (msg_atom) 
   | lident OPENP msgs CLOSEP                         (Fun(lident,msgs))
   | abbrev                                           (Abbrev(abbrev))

msgs: msg                                             ([msg])
    | msg COMMA msgs                                  (msg::msgs)

name: UPPER_STRING_LITERAL                            (UPPER_STRING_LITERAL)                         
    | LOWER_STRING_LITERAL                            (LOWER_STRING_LITERAL) 

uident: UPPER_STRING_LITERAL                          (UPPER_STRING_LITERAL)

lident: LOWER_STRING_LITERAL                          (LOWER_STRING_LITERAL)

lidents: lident                                       ([lident])
       | lident COMMA lidents                         (lident::lidents)

uidents: uident                                       ([uident])
       | uident COMMA uidents                         (uident::uidents)

ident: uident                                         (uident)
     | lident                                         (lident)

arity: INTEGER_LITERAL                                (Option.valOf(Int.fromString(INTEGER_LITERAL)))

abbrev_head: ident EXCLAM OPENSQB CLOSESQB            ((ident,[]))
           | ident EXCLAM OPENSQB uidents CLOSESQB    ((ident,uidents))

abbrev_decl: abbrev_head EQUAL msg                    (TracProtocol.TermAbbreviation(abbrev_head,msg))
           | abbrev_head actions_ext DOT              (TracProtocol.ActionsAbbreviation(abbrev_head,actions_ext))

abbrev_spec: abbrev_decl                              ([abbrev_decl])
           | abbrev_decl abbrev_spec                  (abbrev_decl::abbrev_spec)
\<close>



ML\<open>
structure TracProtocolParser : sig  
       val parse_source: Input.source -> TracProtocol.protocol
       val parse_file: string -> TracProtocol.protocol
       val parse_str:  string -> TracProtocol.protocol
end = 
struct

  structure TracLrVals =
    TracTransactionLrValsFun(structure Token = LrParser.Token)

  structure TracLex =
    TracTransactionLexFun(structure Tokens = TracLrVals.Tokens)

  structure TracParser =
    Join(structure LrParser = LrParser
     structure ParserData = TracLrVals.ParserData
     structure Lex = TracLex)
  
  fun invoke lexstream =
      let fun print_error (s, p: Position.T, _) =
          error("Error at " ^ Position.here p ^ ", " ^ s)
       in TracParser.parse(0, lexstream, print_error, ())
      end

 fun parse_fp lexer =  
   let
      val dummyEOF = TracLrVals.Tokens.EOF(Position.none, Position.none)
      fun loop lexer =
          let 
          val (res, lexer) = invoke lexer
          val (nextToken, lexer) = TracParser.Stream.get lexer
         in if TracParser.sameToken(nextToken, dummyEOF) then ((), res)
          else loop lexer
          end
       in  (#2(loop lexer))
      end

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
   handle LrParser.ParseError => TracProtocol.empty 

 fun parse_file tracFile = 
   let
     val content_raw = File.read (Path.explode tracFile)
     val syms = Symbol_Pos.explode (content_raw, Position.file tracFile)
     val content = Symbol_Pos.content syms
   in parse_syms (content, syms) end
   handle LrParser.ParseError => TracProtocol.empty 

 fun parse_str str = 
   let
     val syms = Symbol_Pos.explode (str, Position.none)
     val content = Symbol_Pos.content syms
   in parse_syms (content, syms) end
   handle LrParser.ParseError => TracProtocol.empty 

end
\<close>

end