(* User declarations.  This is a -*- sml -*- file. *)

type lexresult = int

val eof = fn x => 0

val count_body = ref 0
val count_braces = ref 0

val funs =
  ["tInit", "tFirst", "tLast", "tLength", "tMap",
   "finite", "linorder",
   "guard", "action",
   "jAction", "subjective",
   "spr{\\isaliteral{5F}{\\isacharunderscore}}jview",
   "spr{\\isaliteral{5F}{\\isacharunderscore}}jview{\\isaliteral{5F}{\\isacharunderscore}}abs",
   "spr{\\isaliteral{5F}{\\isacharunderscore}}sim",
   "jkbpTn", "jkbpT",
   "jkbpCn", "jkbpC", "jkbpSEC",
   "mkM", "mkMC", "mkMCS", "mkKripke",
   "worlds",
   "Suc",
   "pInit", "pTrans", "pAct", "runJP", "actJP",
   "mkAuto", "mkAutoSim", "mkAutoAlg",
   "gen{\\isaliteral{5F}{\\isacharunderscore}}dfs",
   "alg{\\isaliteral{5F}{\\isacharunderscore}}dfs",
   "equiv{\\isaliteral{5F}{\\isacharunderscore}}class",
   "tObsC", "tObsC{\\isaliteral{5F}{\\isacharunderscore}}abs",
   "sprFst", "sprLst", "sprCRel",
   "SOME",
   "bool", "list", "option", "nat",
   "KBP", "Trace", "BEState", "SPRstate", "KripkeStructure", "Protocol", "odlist",
   "if", "then", "else", "case", "of", "let", "in",
   "UNIV",
   "fst", "snd", "set", "length",
   "Environment", "SimEnvironment", "DFS", "Algorithm", "AlgorithmForAgent", "DetBroadcastEnvironment", "SingleAgentEnvironment",
   "MapOps",
   "KBPAlg",
   "ODList{\\isaliteral{2E}{\\isachardot}}lookup",
   "ODList{\\isaliteral{2E}{\\isachardot}}toSet",
   "eval",
   "es", "ps"
  ]

fun mem x [] = false
  | mem x (y::ys) = if x=y then true else mem x ys

fun subst s = if mem s funs then "\\isafun{" ^ s ^ "}" else s

%%

%s B C D E;

ws = [\ \t];

name=[A-Za-z0-9]+;
sym="{\\isaliteral{5F}{\\isacharunderscore}}" | "{\\isaliteral{2E}{\\isachardot}}";
tick="{\\isaliteral{27}{\\isacharprime}}";
label=:{name};
typvar={tick}{name};
id=({sym}|{name})+;

%%

<INITIAL,B,C,D,E>\n       => (print (yymktext()); continue());
<INITIAL,B,C,D,E>{ws}+    => (print (yymktext()); continue());

<INITIAL>"\\begin{isabellebody}"   => (YYBEGIN C; print (yymktext()); continue());

<C>"\\begin{isabellebody}"   => (count_body := (!count_body+1); print (yymktext()); continue());
<C>"\\end{isabellebody}"     => (if !count_body=0 then YYBEGIN INITIAL else count_body := (!count_body-1); print (yymktext()); continue());
<C>"\\begin{isamarkuptext}"  => (YYBEGIN D; print (yymktext()); continue());
<C>"\\isamarkupsection{"     => (YYBEGIN E; print (yymktext()); continue());
<C>"\\isamarkupsubsection{"  => (YYBEGIN E; print (yymktext()); continue());
<C>{label}                   => (print (yymktext()); continue());
<C>{typvar}                  => (print (yymktext()); continue());
<C>{id}                      => (print (subst (yymktext())); continue());

<E>"{"                       => (count_braces := (!count_braces+1); print (yymktext()); continue());
<E>"}"                       => (if !count_braces=0 then YYBEGIN C else count_braces := (!count_braces-1); print (yymktext()); continue());

<D>"\\end{isamarkuptext}"    => (YYBEGIN C; print (yymktext()); continue());
<D>"\\isa{"                  => (YYBEGIN B; print (yymktext()); continue());

<B>"{"                       => (count_braces := (!count_braces+1); print (yymktext()); continue());
<B>"}"                       => (if !count_braces=0 then YYBEGIN D else count_braces := (!count_braces-1); print (yymktext()); continue());
<B>{typvar}                  => (print (yymktext()); continue());
<B>{id}                      => (print (subst (yymktext())); continue());

<INITIAL,B,C,D,E>.    => (print (yymktext()); continue());
