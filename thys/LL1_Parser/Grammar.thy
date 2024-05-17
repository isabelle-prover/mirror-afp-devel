section \<open>Types and Definitions\<close>

theory Grammar
imports Main
begin

subsection \<open>Grammar\<close>

text\<open>We first define the datatypes for a grammar. A symbol is either a non-terminal of type
@{typ 'n} or a terminal of type @{typ 't}. A production is then a tuple of a non-terminal, and a
list of symbols. An empty list of symbols corresponds to the empty word. A grammar is defined
through a non-terminal as start symbol and a list of productions. Note that there may be more than
one production for some non-terminal.\<close>

datatype ('n, 't) symbol = NT 'n | T 't

type_synonym ('n, 't) rhs = "(('n, 't) symbol) list"

type_synonym ('n, 't) prod = "'n \<times> ('n, 't) rhs"
type_synonym ('n, 't) prods = "('n, 't) prod list"

datatype ('n, 't) grammar = G (start: "'n") (prods: "('n, 't) prods")

text\<open>An LL($1$) parser considers a lookahead of size one to determine the appropriate rule for the next
expansion. A lookahead may either be a terminal symbol or @{text EOF}, the special lookahead to mark
the end of input.\<close>

datatype 't lookahead = LA 't | EOF


subsection \<open>Definition of Nullable, First, Follow and Lookahead\<close>

text\<open>The set of nullable symbols contains all nonterminals from which the empty word can be derived.
This is the case, either when there is a production for the non-terminal with an empty right-hand
side or when the right-hand side consists only of nullable symbols.\<close>

inductive nullable_sym :: "('n, 't) grammar \<Rightarrow> ('n, 't) symbol \<Rightarrow> bool"
    and nullable_gamma :: "('n, 't) grammar \<Rightarrow> ('n, 't) rhs \<Rightarrow> bool"
for g where
  NullableSym:
  "(x, gamma) \<in> set (prods g) \<Longrightarrow> nullable_gamma g gamma
  \<Longrightarrow> nullable_sym g (NT x)"
| NullableNil:
  "nullable_gamma g []"
| NullableCons:
  "nullable_sym g s \<Longrightarrow> nullable_gamma g ss
  \<Longrightarrow> nullable_gamma g (s # ss)"

text\<open>First symbols are all symbols that are prefixes of possible derivations. For some lookahead,
this is the terminal corresponding to the lookahead, and all non-terminals for which there exists a
production where a first symbol occurs after a nullable prefix.\<close>

inductive first_sym
  :: "('n, 't) grammar \<Rightarrow> 't lookahead \<Rightarrow> ('n, 't) symbol \<Rightarrow> bool"
for g where
  FirstT: "first_sym g (LA y) (T y)"
| FirstNT:
  "(x, gpre @ s # gsuf) \<in> set (prods g) \<Longrightarrow> nullable_gamma g gpre
  \<Longrightarrow> first_sym g la s
  \<Longrightarrow> first_sym g la (NT x)"

inductive first_gamma
  :: "('n, 't) grammar \<Rightarrow> 't lookahead \<Rightarrow> ('n, 't) symbol list \<Rightarrow> bool"
for g where
  FirstGamma:
  "nullable_gamma g gpre \<Longrightarrow> first_sym g la s
  \<Longrightarrow> first_gamma g la (gpre @ s # gsuf)"

text\<open>The set of follow symbols contains for some non-terminal all symbols that may directly follow
after a derivation for it. For the start symbol a follow symbol is EOF. In general, follow symbols
of some non-terminal are all first symbols of the list of symbols following after an occurrence of
this non-terminal in the productions right-hand sides. In case the list of symbols following a
non-terminal in a production's right-hand side is nullable, the non-terminal on the left-hand side
of the production is a follow symbol of it as well.\<close>

inductive follow_sym :: "('n, 't) grammar \<Rightarrow> 't lookahead \<Rightarrow> ('n, 't) symbol \<Rightarrow> bool"
for g where
  FollowStart: "follow_sym g EOF (NT (start g))"
| FollowRight:
  "(x1, gpre @ (NT x2) # gsuf) \<in> set (prods g)
  \<Longrightarrow> first_gamma g la gsuf
  \<Longrightarrow> follow_sym g la (NT x2)"
| FollowLeft : "(x1, gpre @ (NT x2) # gsuf) \<in> set (prods g)
  \<Longrightarrow> nullable_gamma g gsuf
  \<Longrightarrow> follow_sym g la (NT x1)
  \<Longrightarrow> follow_sym g la (NT x2)"

text\<open>A symbol is a lookahead for some production if it is either a first symbol of the production's
right-hand side or, when the right-hand side is nullable, a follow symbol of the non-terminal on the
production's left-hand side.\<close>

definition lookahead_for
  :: "'t lookahead \<Rightarrow> 'n \<Rightarrow> ('n, 't) rhs \<Rightarrow> ('n, 't) grammar \<Rightarrow> bool"
where
  "lookahead_for la x gamma g = (
    first_gamma g la gamma
    \<or> (nullable_gamma g gamma \<and> follow_sym g la (NT x)))"


subsection \<open>Left-Recursive Grammars\<close>

text\<open>A left-recursive grammar is a grammar where some non-terminal symbol can be reached from the
same non-terminal symbol via some nullable path. LL(1) grammars may not be left-recursive.
We give a definition for left-recursive grammars to later use it as an error condition for parsing.\<close>

inductive nullable_path ::
  "('n, 't) grammar \<Rightarrow> 't lookahead \<Rightarrow> ('n, 't) symbol \<Rightarrow> ('n, 't) symbol
  \<Rightarrow> bool"
where
  DirectPath: "(x, gamma) \<in> set (prods g) \<Longrightarrow> gamma = gpre @ NT z # gsuf
  \<Longrightarrow> nullable_gamma g gpre \<Longrightarrow> lookahead_for la x gamma g
  \<Longrightarrow> nullable_path g la (NT x) (NT z)"
| IndirectPath: "(x, gamma) \<in> set (prods g)
  \<Longrightarrow> gamma = gpre @ NT y # gsuf
  \<Longrightarrow> nullable_gamma g gpre \<Longrightarrow> lookahead_for la x gamma g
  \<Longrightarrow> nullable_path g la (NT y) (NT z)
  \<Longrightarrow> nullable_path g la (NT x) (NT z)"

abbreviation left_recursive ::
  "('n, 't) grammar \<Rightarrow> ('n, 't) symbol \<Rightarrow> 't lookahead \<Rightarrow> bool"
where
  "left_recursive g s la \<equiv> nullable_path g la s s"

end