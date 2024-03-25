theory Examples
  imports
    Earley_Parser
    "HOL-Library.Code_Target_Nat"
begin

section \<open>Examples\<close>

subsection \<open>Common symbols\<close>

datatype symbol = a | S | X | Y | Z


subsection \<open>$O(n^3)$ ambiguous grammars\<close>

subsubsection \<open>S -> SS | a\<close>

definition rules1 :: "symbol rule list" where
  "rules1 = [
    (S, [S, S]),
    (S, [a])
  ]"

definition cfg1 :: "symbol cfg" where
  "cfg1 = CFG rules1 S"

lemma \<epsilon>_free1:
  "\<epsilon>_free cfg1"
  by (auto simp: \<epsilon>_free_def cfg1_def rules1_def rhs_rule_def)


subsection \<open>$O(n^2)$ unambiguous or bounded ambiguity\<close>

subsubsection \<open>S -> aS | a\<close>

definition rules2 :: "symbol rule list" where
  "rules2 = [
    (S, [a, S]),
    (S, [a])
  ]"

definition cfg2 :: "symbol cfg" where
  "cfg2 = CFG rules2 S"

lemma \<epsilon>_free2:
  "\<epsilon>_free cfg2"
  by (auto simp: \<epsilon>_free_def cfg2_def rules2_def rhs_rule_def)


subsubsection \<open>S -> aSa | a\<close>

definition rules3 :: "symbol rule list" where
  "rules3 = [
    (S, [a, S, a]),
    (S, [a])
  ]"

definition cfg3 :: "symbol cfg" where
  "cfg3 = CFG rules3 S"

lemma \<epsilon>_free3:
  "\<epsilon>_free cfg3"
  by (auto simp: \<epsilon>_free_def cfg3_def rules3_def rhs_rule_def)


subsection \<open>O(n) bounded state, non-right recursive LR(k) grammars\<close>

subsubsection \<open>S -> Sa | a\<close>

definition rules4 :: "symbol rule list" where
  "rules4 = [
    (S, [S, a]),
    (S, [a])
  ]"

definition cfg4 :: "symbol cfg" where
  "cfg4 = CFG rules4 S"

lemma \<epsilon>_free4:
  "\<epsilon>_free cfg4"
  by (auto simp: \<epsilon>_free_def cfg4_def rules4_def rhs_rule_def)


subsection \<open>S -> SX, X -> Y | Z, Y -> a, Z -> a\<close>

definition rules5 :: "symbol rule list" where
  "rules5 = [
    (S, [S, X]),
    (S, [a]),
    (X, [Y]),
    (X, [Z]),
    (Y, [a]),
    (Z, [a])
  ]"

definition cfg5 :: "symbol cfg" where
  "cfg5 = CFG rules5 S"

lemma \<epsilon>_free5:
  "\<epsilon>_free cfg5"
  by (auto simp: \<epsilon>_free_def cfg5_def rules5_def rhs_rule_def)


section \<open>Input and Evaluation\<close>

definition inp :: "symbol list" where
  "inp = [a,
    a, a, a, a, a, a, a, a, a, a, a, a, a, a, a, a,
    a, a, a, a, a, a, a, a, a, a, a, a, a, a, a, a,
    a, a, a, a, a, a, a, a, a, a, a, a, a, a, a, a,
    a, a, a, a, a, a, a, a, a, a, a, a, a, a, a, a
  ]"

lemma is_word_inp1:
  "is_word cfg1 inp"
  by (auto simp: is_word_def cfg1_def rules1_def nonterminals_def inp_def)

lemma is_word_inp2:
  "is_word cfg2 inp"
  by (auto simp: is_word_def cfg2_def rules2_def nonterminals_def inp_def)

lemma is_word_inp3:
  "is_word cfg3 inp"
  by (auto simp: is_word_def cfg3_def rules3_def nonterminals_def inp_def)

lemma is_word_inp4:
  "is_word cfg4 inp"
  by (auto simp: is_word_def cfg4_def rules4_def nonterminals_def inp_def)

lemma is_word_inp5:
  "is_word cfg5 inp"
  by (auto simp: is_word_def cfg5_def rules5_def nonterminals_def inp_def)

definition size_bins :: "'a bins \<Rightarrow> nat" where
  "size_bins bs = fold (+) (map length bs) 0"

fun size_pointer :: "'a item \<times> pointer \<Rightarrow> nat" where
  "size_pointer (_, (PreRed _ ps)) = 1 + length ps"
| "size_pointer _ = 1"

definition size_pointers :: "'a bins \<Rightarrow> nat" where
  "size_pointers bs = fold (+) (map (\<lambda>b. fold (+) (map (\<lambda>e. size_pointer e) b) 0) bs) 0" 

export_code Earley\<^sub>L build_tree rules1 cfg1 rules2 cfg2 rules3 cfg3 rules4 cfg4 rules5 cfg5 inp size_bins size_pointers in Scala

value "size_bins (Earley\<^sub>L cfg1 inp)"
value "size_pointers (Earley\<^sub>L cfg1 inp)"

value "size_bins (Earley\<^sub>L cfg2 inp)"
value "size_pointers (Earley\<^sub>L cfg2 inp)"

value "size_bins (Earley\<^sub>L cfg3 inp)"
value "size_pointers (Earley\<^sub>L cfg3 inp)"

value "size_bins (Earley\<^sub>L cfg4 inp)"
value "size_pointers (Earley\<^sub>L cfg4 inp)"

value "size_bins (Earley\<^sub>L cfg5 inp)"
value "size_pointers (Earley\<^sub>L cfg5 inp)"


(*
subsection \<open>JSON\<close>

text\<open>

json ::= element

value ::= object | array | string | number | "true" | "false" | "null"

object     ::= '{' '}' | '{' ws '}' | '{' members '}'
members    ::= member | member ',' members
member     ::= identifier ':' element
identifier ::= string | ws string | string ws | ws string ws

array    ::= '[' ']' | '[' ws ']' | '[' elements ']'
elements ::= element | element ',' elements
element  ::= value | ws value | value ws | ws value ws

ws       ::= wssymbol | wssymbol ws
wssymbol ::= '0x20' | '0x0A' | '0x0D' | '0x09'

string     ::= '"' '"' | '"' characters '"'
characters ::= character | character characters
character  ::= 0x20 | .. | 0xFF (- '"') (- '\') | '\' escape
escape     ::= '"' | '\' | '/' | 'b' | 'f' | 'n' | 'r' | 't' | 'u' hex hex hex hex
hex        ::= digit | 'A' . 'F' | 'a' . 'f'

number    ::= integer | integer exponent | integer fraction | integer fraction exponent
fraction  ::= '.' digits
exponent  ::= expsymbol digits | expsymbol sign digits
expsymbol ::= 'E' | 'e'
sign      ::= '+' | '-'
integer   ::= digit | onenine digits | '-' digit | '-' onenine digits
digits    ::= digit | digit digits
digit     ::= '0' | onenine
onenine   ::= '1' | .. | '9'

OMITTED:

character ::= '00FF' . '10FFFF'
\<close>

datatype JSON =
  json
  | val
  | object
  | members
  | member
  | identifier
  | array
  | elements
  | element
  | ws
  | wssymbol
  | string
  | characters
  | character
  | escape
  | hex
  | number
  | fraction
  | exponent
  | expsymbol
  | sign
  | integer
  | digits
  | digit
  | onenine
  | c char

value "''t''"

definition JSON_rules :: "JSON rule list" where
  "JSON_rules = [
    (json, [element]),
  
    (val, [object]),
    (val, [array]),
    (val, [string]),
    (val, [number]),
    (val, [c (CHR ''t''), c (CHR ''r''), c (CHR ''u''), c (CHR ''e'')]),
    (val, [c (CHR ''f''), c (CHR ''a''), c (CHR ''l''), c (CHR ''s''), c (CHR ''e'')]),
    (val, [c (CHR ''n''), c (CHR ''u''), c (CHR ''l''), c (CHR ''l'')]),

    (object, [c (CHR ''{''), c (CHR ''}'')]),
    (object, [c (CHR ''{''), ws, c (CHR ''}'')]),
    (object, [c (CHR ''{''), members, c (CHR ''}'')]),

    (members, [member]),
    (members, [member, c (CHR '',''), members]),

    (member, [identifier, c (CHR '':''), element]),

    (identifier, [string]),
    (identifier, [ws, string]),
    (identifier, [string, ws]),
    (identifier, [ws, string, ws]),

    (array, [c (CHR ''[''), c (CHR '']'')]),
    (array, [c (CHR ''[''), ws, c (CHR '']'')]),
    (array, [c (CHR ''[''), elements, c (CHR '']'')]),

    (elements, [element]),
    (elements, [element, c (CHR '',''), elements]),

    (element, [val]),
    (element, [ws, val]),
    (element, [val, ws]),
    (element, [ws, val, ws]),

    (ws, [wssymbol]),
    (ws, [wssymbol, ws]),

    (wssymbol, [c (CHR '' '')]),
    (wssymbol, [c (CHR 0x0A)]),
    (wssymbol, [c (CHR 0x0D)]),
    (wssymbol, [c (CHR 0x09)]),

    (string, [c (CHR 0x22), c (CHR 0x22)]),
    (string, [c (CHR 0x22), characters, c (CHR 0x22)]),

    (characters, [character]),
    (characters, [character, characters]),

    (character, [c (CHR '' '')]),
    (character, [c (CHR ''!'')]),
    (character, [c (CHR ''#'')]),
    (character, [c (CHR ''$'')]),
    (character, [c (CHR ''%'')]),
    (character, [c (CHR ''&'')]),
    (character, [c (CHR 0x27)]),
    (character, [c (CHR ''('')]),
    (character, [c (CHR '')'')]),
    (character, [c (CHR ''*'')]),
    (character, [c (CHR ''+'')]),
    (character, [c (CHR '','')]),
    (character, [c (CHR ''-'')]),
    (character, [c (CHR ''.'')]),
    (character, [c (CHR ''/'')]),
    (character, [c (CHR ''0'')]),
    (character, [c (CHR ''1'')]),
    (character, [c (CHR ''2'')]),
    (character, [c (CHR ''3'')]),
    (character, [c (CHR ''4'')]),
    (character, [c (CHR ''5'')]),
    (character, [c (CHR ''6'')]),
    (character, [c (CHR ''7'')]),
    (character, [c (CHR ''8'')]),
    (character, [c (CHR ''9'')]),
    (character, [c (CHR '':'')]),
    (character, [c (CHR '';'')]),
    (character, [c (CHR ''<'')]),
    (character, [c (CHR ''='')]),
    (character, [c (CHR ''>'')]),
    (character, [c (CHR ''?'')]),
    (character, [c (CHR ''@'')]),
    (character, [c (CHR ''A'')]),
    (character, [c (CHR ''B'')]),
    (character, [c (CHR ''C'')]),
    (character, [c (CHR ''D'')]),
    (character, [c (CHR ''E'')]),
    (character, [c (CHR ''F'')]),
    (character, [c (CHR ''G'')]),
    (character, [c (CHR ''H'')]),
    (character, [c (CHR ''I'')]),
    (character, [c (CHR ''J'')]),
    (character, [c (CHR ''K'')]),
    (character, [c (CHR ''L'')]),
    (character, [c (CHR ''M'')]),
    (character, [c (CHR ''N'')]),
    (character, [c (CHR ''O'')]),
    (character, [c (CHR ''P'')]),
    (character, [c (CHR ''Q'')]),
    (character, [c (CHR ''R'')]),
    (character, [c (CHR ''S'')]),
    (character, [c (CHR ''T'')]),
    (character, [c (CHR ''U'')]),
    (character, [c (CHR ''V'')]),
    (character, [c (CHR ''W'')]),
    (character, [c (CHR ''X'')]),
    (character, [c (CHR ''Y'')]),
    (character, [c (CHR ''Z'')]),
    (character, [c (CHR ''['')]),
    (character, [c (CHR '']'')]),
    (character, [c (CHR ''^'')]),
    (character, [c (CHR ''_'')]),
    (character, [c (CHR 0x60)]),
    (character, [c (CHR ''a'')]),
    (character, [c (CHR ''b'')]),
    (character, [c (CHR ''c'')]),
    (character, [c (CHR ''d'')]),
    (character, [c (CHR ''e'')]),
    (character, [c (CHR ''f'')]),
    (character, [c (CHR ''g'')]),
    (character, [c (CHR ''h'')]),
    (character, [c (CHR ''i'')]),
    (character, [c (CHR ''j'')]),
    (character, [c (CHR ''k'')]),
    (character, [c (CHR ''l'')]),
    (character, [c (CHR ''m'')]),
    (character, [c (CHR ''n'')]),
    (character, [c (CHR ''o'')]),
    (character, [c (CHR ''p'')]),
    (character, [c (CHR ''q'')]),
    (character, [c (CHR ''r'')]),
    (character, [c (CHR ''s'')]),
    (character, [c (CHR ''t'')]),
    (character, [c (CHR ''u'')]),
    (character, [c (CHR ''v'')]),
    (character, [c (CHR ''w'')]),
    (character, [c (CHR ''x'')]),
    (character, [c (CHR ''y'')]),
    (character, [c (CHR ''z'')]),
    (character, [c (CHR ''{'')]),
    (character, [c (CHR ''|'')]),
    (character, [c (CHR ''}'')]),
    (character, [c (CHR ''~'')]),
    (character, [c (CHR 0x7F)]),
    (character, [c (CHR 0x80)]),
    (character, [c (CHR 0x81)]),
    (character, [c (CHR 0x82)]),
    (character, [c (CHR 0x83)]),
    (character, [c (CHR 0x84)]),
    (character, [c (CHR 0x85)]),
    (character, [c (CHR 0x86)]),
    (character, [c (CHR 0x87)]),
    (character, [c (CHR 0x88)]),
    (character, [c (CHR 0x89)]),
    (character, [c (CHR 0x8A)]),
    (character, [c (CHR 0x8B)]),
    (character, [c (CHR 0x8C)]),
    (character, [c (CHR 0x8D)]),
    (character, [c (CHR 0x8E)]),
    (character, [c (CHR 0x8F)]),
    (character, [c (CHR 0x90)]),
    (character, [c (CHR 0x91)]),
    (character, [c (CHR 0x92)]),
    (character, [c (CHR 0x93)]),
    (character, [c (CHR 0x94)]),
    (character, [c (CHR 0x95)]),
    (character, [c (CHR 0x96)]),
    (character, [c (CHR 0x97)]),
    (character, [c (CHR 0x98)]),
    (character, [c (CHR 0x99)]),
    (character, [c (CHR 0x9A)]),
    (character, [c (CHR 0x9B)]),
    (character, [c (CHR 0x9C)]),
    (character, [c (CHR 0x9D)]),
    (character, [c (CHR 0x9E)]),
    (character, [c (CHR 0x9F)]),
    (character, [c (CHR 0xA0)]),
    (character, [c (CHR 0xA1)]),
    (character, [c (CHR 0xA2)]),
    (character, [c (CHR 0xA3)]),
    (character, [c (CHR 0xA4)]),
    (character, [c (CHR 0xA5)]),
    (character, [c (CHR 0xA6)]),
    (character, [c (CHR 0xA7)]),
    (character, [c (CHR 0xA8)]),
    (character, [c (CHR 0xA9)]),
    (character, [c (CHR 0xAA)]),
    (character, [c (CHR 0xAB)]),
    (character, [c (CHR 0xAC)]),
    (character, [c (CHR 0xAD)]),
    (character, [c (CHR 0xAE)]),
    (character, [c (CHR 0xAF)]),
    (character, [c (CHR 0xB0)]),
    (character, [c (CHR 0xB1)]),
    (character, [c (CHR 0xB2)]),
    (character, [c (CHR 0xB3)]),
    (character, [c (CHR 0xB4)]),
    (character, [c (CHR 0xB5)]),
    (character, [c (CHR 0xB6)]),
    (character, [c (CHR 0xB7)]),
    (character, [c (CHR 0xB8)]),
    (character, [c (CHR 0xB9)]),
    (character, [c (CHR 0xBA)]),
    (character, [c (CHR 0xBB)]),
    (character, [c (CHR 0xBC)]),
    (character, [c (CHR 0xBD)]),
    (character, [c (CHR 0xBE)]),
    (character, [c (CHR 0xBF)]),
    (character, [c (CHR 0xC0)]),
    (character, [c (CHR 0xC1)]),
    (character, [c (CHR 0xC2)]),
    (character, [c (CHR 0xC3)]),
    (character, [c (CHR 0xC4)]),
    (character, [c (CHR 0xC5)]),
    (character, [c (CHR 0xC6)]),
    (character, [c (CHR 0xC7)]),
    (character, [c (CHR 0xC8)]),
    (character, [c (CHR 0xC9)]),
    (character, [c (CHR 0xCA)]),
    (character, [c (CHR 0xCB)]),
    (character, [c (CHR 0xCC)]),
    (character, [c (CHR 0xCD)]),
    (character, [c (CHR 0xCE)]),
    (character, [c (CHR 0xCF)]),
    (character, [c (CHR 0xD0)]),
    (character, [c (CHR 0xD1)]),
    (character, [c (CHR 0xD2)]),
    (character, [c (CHR 0xD3)]),
    (character, [c (CHR 0xD4)]),
    (character, [c (CHR 0xD5)]),
    (character, [c (CHR 0xD6)]),
    (character, [c (CHR 0xD7)]),
    (character, [c (CHR 0xD8)]),
    (character, [c (CHR 0xD9)]),
    (character, [c (CHR 0xDA)]),
    (character, [c (CHR 0xDB)]),
    (character, [c (CHR 0xDC)]),
    (character, [c (CHR 0xDD)]),
    (character, [c (CHR 0xDE)]),
    (character, [c (CHR 0xDF)]),
    (character, [c (CHR 0xE0)]),
    (character, [c (CHR 0xE1)]),
    (character, [c (CHR 0xE2)]),
    (character, [c (CHR 0xE3)]),
    (character, [c (CHR 0xE4)]),
    (character, [c (CHR 0xE5)]),
    (character, [c (CHR 0xE6)]),
    (character, [c (CHR 0xE7)]),
    (character, [c (CHR 0xE8)]),
    (character, [c (CHR 0xE9)]),
    (character, [c (CHR 0xEA)]),
    (character, [c (CHR 0xEB)]),
    (character, [c (CHR 0xEC)]),
    (character, [c (CHR 0xED)]),
    (character, [c (CHR 0xEE)]),
    (character, [c (CHR 0xEF)]),
    (character, [c (CHR 0xF0)]),
    (character, [c (CHR 0xF1)]),
    (character, [c (CHR 0xF2)]),
    (character, [c (CHR 0xF3)]),
    (character, [c (CHR 0xF4)]),
    (character, [c (CHR 0xF5)]),
    (character, [c (CHR 0xF6)]),
    (character, [c (CHR 0xF7)]),
    (character, [c (CHR 0xF8)]),
    (character, [c (CHR 0xF9)]),
    (character, [c (CHR 0xFA)]),
    (character, [c (CHR 0xFB)]),
    (character, [c (CHR 0xFC)]),
    (character, [c (CHR 0xFD)]),
    (character, [c (CHR 0xFE)]),
    (character, [c (CHR 0xFF)]),
    (character, [c (CHR 0x5C), escape]),

    (escape, [c (CHR 0x22)]),
    (escape, [c (CHR 0x5C)]),
    (escape, [c (CHR ''/'')]),
    (escape, [c (CHR ''b'')]),
    (escape, [c (CHR ''f'')]),
    (escape, [c (CHR ''n'')]),
    (escape, [c (CHR ''r'')]),
    (escape, [c (CHR ''t'')]),
    (escape, [c (CHR ''u''), hex, hex, hex, hex]),

    (hex, [digit]),
    (hex, [c (CHR ''A'')]),
    (hex, [c (CHR ''B'')]),
    (hex, [c (CHR ''C'')]),
    (hex, [c (CHR ''D'')]),
    (hex, [c (CHR ''E'')]),
    (hex, [c (CHR ''F'')]),
    (hex, [c (CHR ''a'')]),
    (hex, [c (CHR ''b'')]),
    (hex, [c (CHR ''c'')]),
    (hex, [c (CHR ''d'')]),
    (hex, [c (CHR ''e'')]),
    (hex, [c (CHR ''f'')]),

    (number, [integer]),
    (number, [integer, exponent]),
    (number, [integer, fraction]),
    (number, [integer, fraction, exponent]),

    (fraction, [c (CHR ''.''), digits]),

    (exponent, [expsymbol, digits]),
    (exponent, [expsymbol, sign, digits]),
  
    (expsymbol, [c (CHR ''E'')]),
    (expsymbol, [c (CHR ''e'')]),

    (sign, [c (CHR ''+'')]),
    (sign, [c (CHR ''-'')]),

    (integer, [digit]),
    (integer, [onenine, digits]),
    (integer, [c (CHR ''-''), digit]),
    (integer, [c (CHR ''-''), onenine, digits]),

    (digits, [digit]),
    (digits, [digit, digits]),

    (digit, [c (CHR ''0'')]),
    (digit, [onenine]),

    (onenine, [c (CHR ''1'')]),
    (onenine, [c (CHR ''2'')]),
    (onenine, [c (CHR ''3'')]),
    (onenine, [c (CHR ''4'')]),
    (onenine, [c (CHR ''5'')]),
    (onenine, [c (CHR ''6'')]),
    (onenine, [c (CHR ''7'')]),
    (onenine, [c (CHR ''8'')]),
    (onenine, [c (CHR ''9'')])
  ]"

definition JSON_cfg :: "JSON cfg" where
  "JSON_cfg = CFG JSON_rules json"


lemma \<epsilon>_free_JSON:
  "\<epsilon>_free JSON_cfg"
  by (auto simp: \<epsilon>_free_def JSON_cfg_def JSON_rules_def rhs_rule_def)

definition JSON_inp1 :: "JSON list" where
  \<open>JSON_inp1 = map c ''
{
    "glossary": {
        "title": "example glossary",
		"GlossDiv": {
            "title": "S",
			"GlossList": {
                "GlossEntry": {
                    "ID": "SGML",
					"SortAs": "SGML",
					"GlossTerm": "Standard Generalized Markup Language",
					"Acronym": "SGML",
					"Abbrev": "ISO 8879:1986",
					"GlossDef": {
                        "para": "A meta-markup language, used to create markup languages such as DocBook.",
						"GlossSeeAlso": ["GML", "XML"]
                    },
					"GlossSee": "markup"
                }
            }
        }
    }
}
  ''\<close>

value "size_bins (Earley\<^sub>L JSON_cfg JSON_inp1)" \<comment>\<open>77921\<close>
value "size_pointers (Earley\<^sub>L JSON_cfg JSON_inp1)" \<comment>\<open>77921\<close>
value "recognizer JSON_cfg JSON_inp1"
value "build_tree JSON_cfg JSON_inp1 (Earley\<^sub>L JSON_cfg JSON_inp1)"

definition JSON_inp2 :: "JSON list" where
  \<open>JSON_inp2 = map c ''
{"menu": {
  "id": "file",
  "value": "File",
  "popup": {
    "menuitem": [
      {"value": "New", "onclick": "CreateNewDoc()"},
      {"value": "Open", "onclick": "OpenDoc()"},
      {"value": "Close", "onclick": "CloseDoc()"}
    ]
  }
}}
  ''\<close>

value "size_bins (Earley\<^sub>L JSON_cfg JSON_inp2)" \<comment>\<open>33720\<close>
value "size_pointers (Earley\<^sub>L JSON_cfg JSON_inp2)" \<comment>\<open>33720\<close>
value "recognizer JSON_cfg JSON_inp2"
value "build_tree JSON_cfg JSON_inp2 (Earley\<^sub>L JSON_cfg JSON_inp2)"

definition JSON_inp3 :: "JSON list" where
  \<open>JSON_inp3 = map c ''
{"widget": {
    "debug": "on",
    "window": {
        "title": "Sample Konfabulator Widget",
        "name": "main_window",
        "width": 500,
        "height": 500
    },
    "image": { 
        "src": "Images/Sun.png",
        "name": "sun1",
        "hOffset": 250,
        "vOffset": 250,
        "alignment": "center"
    },
    "text": {
        "data": "Click Here",
        "size": 36,
        "style": "bold",
        "name": "text1",
        "hOffset": 250,
        "vOffset": 100,
        "alignment": "center",
        "onMouseUp": "sun1.opacity = (sun1.opacity / 100) * 90;"
    }
}}  
  ''\<close>

value "size_bins (Earley\<^sub>L JSON_cfg JSON_inp3)" \<comment>\<open>74472\<close>
value "size_pointers (Earley\<^sub>L JSON_cfg JSON_inp3)" \<comment>\<open>74472\<close>
value "recognizer JSON_cfg JSON_inp3"
value "build_tree JSON_cfg JSON_inp3 (Earley\<^sub>L JSON_cfg JSON_inp3)"

definition JSON_inp4 :: "JSON list" where
  \<open>JSON_inp4 = map c ''
{"web-app": {
  "servlet": [   
    {
      "servlet-name": "cofaxCDS",
      "servlet-class": "org.cofax.cds.CDSServlet",
      "init-param": {
        "configGlossary:installationAt": "Philadelphia, PA",
        "configGlossary:adminEmail": "ksm@pobox.com",
        "configGlossary:poweredBy": "Cofax",
        "configGlossary:poweredByIcon": "/images/cofax.gif",
        "configGlossary:staticPath": "/content/static",
        "templateProcessorClass": "org.cofax.WysiwygTemplate",
        "templateLoaderClass": "org.cofax.FilesTemplateLoader",
        "templatePath": "templates",
        "templateOverridePath": "",
        "defaultListTemplate": "listTemplate.htm",
        "defaultFileTemplate": "articleTemplate.htm",
        "useJSP": false,
        "jspListTemplate": "listTemplate.jsp",
        "jspFileTemplate": "articleTemplate.jsp",
        "cachePackageTagsTrack": 200,
        "cachePackageTagsStore": 200,
        "cachePackageTagsRefresh": 60,
        "cacheTemplatesTrack": 100,
        "cacheTemplatesStore": 50,
        "cacheTemplatesRefresh": 15,
        "cachePagesTrack": 200,
        "cachePagesStore": 100,
        "cachePagesRefresh": 10,
        "cachePagesDirtyRead": 10,
        "searchEngineListTemplate": "forSearchEnginesList.htm",
        "searchEngineFileTemplate": "forSearchEngines.htm",
        "searchEngineRobotsDb": "WEB-INF/robots.db",
        "useDataStore": true,
        "dataStoreClass": "org.cofax.SqlDataStore",
        "redirectionClass": "org.cofax.SqlRedirection",
        "dataStoreName": "cofax",
        "dataStoreDriver": "com.microsoft.jdbc.sqlserver.SQLServerDriver",
        "dataStoreUrl": "jdbc:microsoft:sqlserver://LOCALHOST:1433;DatabaseName=goon",
        "dataStoreUser": "sa",
        "dataStorePassword": "dataStoreTestQuery",
        "dataStoreTestQuery": "SET NOCOUON;select test='test';",
        "dataStoreLogFile": "/usr/local/tomcat/logs/datastore.log",
        "dataStoreInitConns": 10,
        "dataStoreMaxConns": 100,
        "dataStoreConnUsageLimit": 100,
        "dataStoreLogLevel": "debug",
        "maxUrlLength": 500}},
    {
      "servlet-name": "cofaxEmail",
      "servlet-class": "org.cofax.cds.EmailServlet",
      "init-param": {
      "mailHost": "mail1",
      "mailHostOverride": "mail2"}},
    {
      "servlet-name": "cofaxAdmin",
      "servlet-class": "org.cofax.cds.AdminServlet"},
 
    {
      "servlet-name": "fileServlet",
      "servlet-class": "org.cofax.cds.FileServlet"},
    {
      "servlet-name": "cofaxTools",
      "servlet-class": "org.cofax.cms.CofaxToolsServlet",
      "init-param": {
        "templatePath": "toolstemplates/",
        "log": 1,
        "logLocation": "/usr/local/tomcat/logs/CofaxTools.log",
        "logMaxSize": "",
        "dataLog": 1,
        "dataLogLocation": "/usr/local/tomcat/logs/dataLog.log",
        "dataLogMaxSize": "",
        "removePageCache": "/content/admin/remove?cache=pages&id=",
        "removeTemplateCache": "/content/admin/remove?cache=templates&id=",
        "fileTransferFolder": "/usr/local/tomcat/webapps/content/fileTransferFolder",
        "lookInContext": 1,
        "adminGroupID": 4,
        "betaServer": true}}],
  "servlet-mapping": {
    "cofaxCDS": "/",
    "cofaxEmail": "/cofaxutil/aemail/*",
    "cofaxAdmin": "/admin/*",
    "fileServlet": "/static/*",
    "cofaxTools": "/tools/*"},
 
  "taglib": {
    "taglib-uri": "cofax.tld",
    "taglib-location": "/WEB-INF/tlds/cofax.tld"}}}
  ''\<close>

value "size_bins (Earley\<^sub>L JSON_cfg JSON_inp4)" \<comment>\<open>584814\<close>
value "size_pointers (Earley\<^sub>L JSON_cfg JSON_inp4)" \<comment>\<open>584814\<close>
value "recognizer JSON_cfg JSON_inp4"
value "build_tree JSON_cfg JSON_inp4 (Earley\<^sub>L JSON_cfg JSON_inp4)"


definition JSON_inp5 :: "JSON list" where
  \<open>JSON_inp5 = map c ''
{"menu": {
    "header": "SVG Viewer",
    "items": [
        {"id": "Open"},
        {"id": "OpenNew", "label": "Open New"},
        null,
        {"id": "ZoomIn", "label": "Zoom In"},
        {"id": "ZoomOut", "label": "Zoom Out"},
        {"id": "OriginalView", "label": "Original View"},
        null,
        {"id": "Quality"},
        {"id": "Pause"},
        {"id": "Mute"},
        null,
        {"id": "Find", "label": "Find..."},
        {"id": "FindAgain", "label": "Find Again"},
        {"id": "Copy"},
        {"id": "CopyAgain", "label": "Copy Again"},
        {"id": "CopySVG", "label": "Copy SVG"},
        {"id": "ViewSVG", "label": "View SVG"},
        {"id": "ViewSource", "label": "View Source"},
        {"id": "SaveAs", "label": "Save As"},
        null,
        {"id": "Help"},
        {"id": "About", "label": "About Adobe CVG Viewer..."}
    ]
}}
  ''\<close>

value "size_bins (Earley\<^sub>L JSON_cfg JSON_inp5)" \<comment>\<open>114506\<close>
value "size_pointers (Earley\<^sub>L JSON_cfg JSON_inp5)" \<comment>\<open>114506\<close>
value "recognizer JSON_cfg JSON_inp5"
value "build_tree JSON_cfg JSON_inp5 (Earley\<^sub>L JSON_cfg JSON_inp5)"
*)

end