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

SML_import \<open>structure TracProtocol=TracProtocol\<close>
SML_import \<open>structure Trac_Term=Trac_Term\<close>
SML_import \<open>structure Trac_Utils=Trac_Utils\<close>
SML_import \<open>val error = error\<close>

ml_lex_yacc[expert] TracTransaction where 
lex_user_declarations \<open>
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
\<close>
lex_definitions\<open>
%header (functor TracTransactionLexFun(structure Tokens: TracTransaction_TOKENS));
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
                     
%pos (int * int * int)

%noshift EOF
\<close>
yacc_rules\<open>
START:         trac_protocol                                    (trac_protocol)
trac_protocol: PROTOCOL COLON name protocol_spec                (TracProtocol.update_name protocol_spec name)

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

analysis_spec: rule                        	              ([rule])
             | rule analysis_spec                         (rule::analysis_spec)
             
rule: head ARROW result                                   ((head,[],result)) 
    | head QUESTION keys ARROW result                     ((head,keys,result)) 

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
      let fun print_error (s,i:(int * int * int),_) =
	      error("Error, line .... " ^ (Int.toString (#1 i)) ^"."^(Int.toString (#2 i ))^ ", " ^ s ^ "\n")
       in TracParser.parse(0,lexstream,print_error,())
      end

 fun parse_fp lexer =  let
	  val dummyEOF = TracLrVals.Tokens.EOF((0,0,0),(0,0,0))
	  fun loop lexer =
	      let 
		  val _ = (TracLex.UserDeclarations.pos := (0,0,0);())
		  val (res,lexer) = invoke lexer
		  val (nextToken,lexer) = TracParser.Stream.get lexer
	       in if TracParser.sameToken(nextToken,dummyEOF) then ((),res)
		  else loop lexer
	      end
       in  (#2(loop lexer))
      end

 fun parse_file tracFile = 
     let
	        val infile = TextIO.openIn tracFile
	        val lexer = TracParser.makeLexer  (fn _ => case ((TextIO.inputLine) infile) of
                                                           SOME s => s
                                                          | NONE   => "")
     in
       parse_fp lexer
      handle LrParser.ParseError => TracProtocol.empty 
     end

 fun parse_str str = 
     let
          val parsed = Unsynchronized.ref false 
          fun input_string _  = if !parsed then "" else (parsed := true ;str)
	        val lexer = TracParser.makeLexer input_string
     in
       parse_fp lexer
      handle LrParser.ParseError => TracProtocol.empty 
     end

end
\<close>


end
