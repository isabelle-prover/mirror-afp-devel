section \<open>Examples\<close>

theory Parser_Example
  imports LL1_Parser_show "Show.Show_Instances"
begin

text\<open>In this section we present two examples for LL1-grammars to show how the
parser generator can be used to create a parse tree from a sequence of symbols.\<close>

subsection \<open>Mini-language\<close>

text\<open>The first example is based on Grammar 3.11 from Appel's ``Modern Compiler
Implementation in ML''~\cite{DBLP:books/cu/Appel1998ml}:

   S @{text \<rightarrow>} if E then S else S | begin S L | print E

   L @{text \<rightarrow>} end | ; S L

   E @{text \<rightarrow>} num = num
\<close>

datatype terminal = If | Then | Else | Begin | Print | End | Semi | Num | Eq

datatype nterminal = S | L | E

derive "show" "terminal"
derive "show" "nterminal"
derive "show" "(terminal, nterminal) symbol"

definition gr :: "(nterminal, terminal) grammar" where
  "gr = G S [
    (S, [T If, NT E, T Then, NT S, T Else, NT S]),
    (S, [T Begin, NT S, NT L]),
    (S, [T Print, NT E]),

    (L, [T End]),
    (L, [T Semi, NT S, NT L]),

    (E, [T Num, T Eq, T Num])
  ]"

definition pt :: "(nterminal, terminal) ll1_parse_table" where
  "pt = mkParseTable gr"

\<comment> \<open>We parse lists of pairs of terminal symbols and lexemes. We ignore the latter here.\<close>
definition L where
  "L x = (x, ())"

lemma "parse pt (NT (start gr))
  (map L [If, Num, Eq, Num, Then, Print, Num, Eq, Num, Else, Print, Num, Eq, Num]) =
  RESULT (map_parse_tree id L
     (Node S
       [Leaf If, Node E [Leaf Num, Leaf Eq, Leaf Num], Leaf Then,
        Node S [Leaf Print, Node E [Leaf Num, Leaf Eq, Leaf Num]], Leaf Else,
        Node S [Leaf Print, Node E [Leaf Num, Leaf Eq, Leaf Num]]]))
     []"
  by eval

text\<open>Example input:
\begin{verbatim}
if 2 = 5 then
  print 2 = 5
else
  print 42 = 42
\end{verbatim}
\<close>

lemma "parseToString pt (NT (start gr))
  (map L [If, Num, Eq, Num, Then, Print, Num, Eq, Num, Else, Print, Num, Eq, Num]) =
  ''(If, ()) (Num, ()) (Eq, ()) (Num, ()) (Then, ()) (Print, ()) (Num, ()) (Eq, ()) (Num, ()) ''
  @ ''(Else, ()) (Print, ()) (Num, ()) (Eq, ()) (Num, ())''"
  by eval

text\<open>Example input:
\begin{verbatim}
if 2 5 then
  print 2 = 5
else
  print 42 = 42
\end{verbatim}
\<close>

lemma "parse pt (NT (start gr))
  (map L [If, Num, Num, Then, Print, Num, Eq, Num, Else, Print, Num, Eq, Num]) =
  REJECT ''Token mismatch. Expected Eq, saw Num (())''
   (map L [Num, Then, Print, Num, Eq, Num, Else, Print, Num, Eq, Num])"
  by eval

end