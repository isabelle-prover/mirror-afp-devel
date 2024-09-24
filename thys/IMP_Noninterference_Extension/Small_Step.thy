(*  Title:       Extension of Stateful Intransitive Noninterference with Inputs, Outputs, and Nondeterminism in Language IMP
    Author:      Pasquale Noce
                 Senior Staff Firmware Engineer at HID Global, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at hidglobal dot com
*)

section "Extension of language IMP with inputs, outputs, and nondeterminism"

theory Small_Step
  imports
    "HOL-IMP.BExp"
    "HOL-IMP.Star"
begin

text \<open>
\null

In a previous paper of mine \<^cite>\<open>"Noce24"\<close>, the notion of termination-sensitive information flow
security with respect to a level-based interference relation, as studied in \<^cite>\<open>"Volpano96"\<close>,
\<^cite>\<open>"Volpano97"\<close> and formalized in \<^cite>\<open>"Nipkow23"\<close>, is generalized to the notion of
termination-sensitive information flow correctness with respect to an interference function mapping
program states to (generally) intransitive interference relations. Moreover, a static type system is
specified and is proven to be capable of enforcing such information flow correctness policies.

The present paper extends both the aforesaid information flow correctness criterion and the related
static type system to the case of an imperative programming language supporting inputs, outputs, and
nondeterminism. Regarding inputs and nondeterminism, \<^cite>\<open>"Volpano96"\<close>, section 7.1, observes that
``if we try to extend the core language with a primitive random number generator \emph{rand( )} and
allow an assignment such as \emph{z := rand( )} to be well typed when \emph{z} is low, then the
soundness theorem no longer holds'', and from this infers that ``new security models [...] should be
explored as potential notions of type soundness for new type systems that deal with nondeterministic
programs''. The present paper shows that this difficulty can be solved by extending the inductive
definition of the programming language's operational semantics so as to reflect the fact that, even
though the input instruction \emph{z := rand( )} may set \emph{z} to an arbitrary input value, the
same program state is produced whenever the input value is the same. As shown in this paper, this
enables to apply a suitably extended information flow correctness criterion based on stateful
intransitive noninterference, as well as an extended static type system enforcing this criterion, to
such an extended programming language.

The didactic imperative programming language IMP employed in \<^cite>\<open>"Nipkow23"\<close>, extended with an
input instruction, an output instruction, and a control structure allowing for nondeterministic
choice, will be used for this purpose. Yet, in the same way as in my previous paper \<^cite>\<open>"Noce24"\<close>,
the introduced concepts are applicable to larger, real-world imperative programming languages, too,
by just affording the additional type system complexity arising from richer language constructs.

For further information about the formal definitions and proofs contained in this paper, refer to
Isabelle documentation, particularly \<^cite>\<open>"Paulson24"\<close>, \<^cite>\<open>"Nipkow24-4"\<close>, \<^cite>\<open>"Krauss24"\<close>,
\<^cite>\<open>"Nipkow11"\<close>, and \<^cite>\<open>"Ballarin24"\<close>.

As mentioned above, the first task to be tackled, which is the subject of this section, consists of
extending the original syntax, big-step operational semantics, and small-step operational semantics
of language IMP, as formalized in \<^cite>\<open>"Nipkow24-1"\<close>, \<^cite>\<open>"Nipkow24-2"\<close>, and \<^cite>\<open>"Nipkow24-3"\<close>,
respectively.
\<close>


subsection "Extended syntax"

text \<open>
The starting point is extending the original syntax of language IMP with the following additional
constructs.

  \<^item> An input instruction @{text "IN x"}, which sets variable \emph{x} to an input value.

  \<^item> An output instruction @{text "OUT x"}, which outputs the current value of variable \emph{x}.

  \<^item> A control structure @{text "c\<^sub>1 OR c\<^sub>2"}, which allows for a nondeterministic choice between
commands @{text "c\<^sub>1"} and @{text "c\<^sub>2"}.

\null
\<close>

declare [[syntax_ambiguity_warning = false]]

datatype com =
  SKIP |
  Assign vname aexp  (\<open>_ ::= _\<close> [1000, 61] 70) |
  Input vname  (\<open>(IN _)\<close> [61] 70) |
  Output vname  (\<open>(OUT _)\<close> [61] 70) |
  Seq com com  (\<open>_;;/ _\<close> [61, 61] 70) |
  Or com com  (\<open>(_ OR _)\<close> [61, 61] 70) |
  If bexp com com  (\<open>(IF _/ THEN _/ ELSE _)\<close> [0, 0, 61] 70) |
  While bexp com  (\<open>(WHILE _/ DO _)\<close> [0, 61] 70)


subsection "Extended big-step semantics"

text \<open>
The original big-step semantics of language IMP associates a pair formed by a command and an initial
\emph{program execution stage}, consisting of a program state, with a corresponding final program
execution stage, consisting of a program state as well. The extended big-step semantics defined here
below extends such program execution stage notion by considering, in addition to a program state,
the following additional parameters.

  \<^item> A \emph{stream of input values}, consisting of a function @{text f} mapping each pair formed by
a variable and a natural number with an integer value, where @{text "f x n"} is the input value
assigned to variable @{text x} by an input instruction @{term "IN x"} after @{text n} previous such
assignments to @{text x}.

  \<^item> A \emph{trace of inputs}, consisting of a list @{text vs} of pairs formed by a variable and an
integer value, to which a further element @{text "(x, i)"} is appended as a result of the execution
of an input instruction @{term "IN x"}, where @{text i} is the input value assigned to variable
@{text x}.

  \<^item> A \emph{trace of outputs}, consisting of a list @{text ws} of pairs formed by a variable and an
integer value, to which a further element @{text "(x, i)"} is appended as a result of the execution
of an output instruction @{term "OUT x"}, where @{text i} is the current value of variable @{text x}
being output.

Unlike the other components of a program execution stage, the stream of input values is an
\emph{invariant} of the big-step semantics, and then also of the small-step semantics defined
subsequently, in that any two program execution stages associated with each other by either
semantics share the same stream of input values.

\null
\<close>

type_synonym stream = "vname \<Rightarrow> nat \<Rightarrow> val"
type_synonym inputs = "(vname \<times> val) list"
type_synonym outputs = "(vname \<times> val) list"
type_synonym stage = "state \<times> stream \<times> inputs \<times> outputs"


inductive big_step :: "com \<times> stage \<Rightarrow> stage \<Rightarrow> bool"
  (infix \<open>\<Rightarrow>\<close> 55) where
Skip:
 "(SKIP, p) \<Rightarrow> p" |
Assign:
 "(x ::= a, s, p) \<Rightarrow> (s(x := aval a s), p)" |
Input:
 "n = length [p\<leftarrow>vs. fst p = x] \<Longrightarrow> (IN x, s, f, vs, ws) \<Rightarrow>
    (s(x := f x n), f, vs @ [(x, f x n)], ws)" |
Output:
 "(OUT x, s, f, vs, ws) \<Rightarrow> (s, f, vs, ws @ [(x, s x)])" |
Seq:
 "\<lbrakk>(c\<^sub>1, p\<^sub>1) \<Rightarrow> p\<^sub>2; (c\<^sub>2, p\<^sub>2) \<Rightarrow> p\<^sub>3\<rbrakk> \<Longrightarrow> (c\<^sub>1;; c\<^sub>2, p\<^sub>1) \<Rightarrow> p\<^sub>3" |
Or1:
 "(c\<^sub>1, p) \<Rightarrow> p' \<Longrightarrow> (c\<^sub>1 OR c\<^sub>2, p) \<Rightarrow> p'" |
Or2:
 "(c\<^sub>2, p) \<Rightarrow> p' \<Longrightarrow> (c\<^sub>1 OR c\<^sub>2, p) \<Rightarrow> p'" |
IfTrue:
 "\<lbrakk>bval b s; (c\<^sub>1, s, p) \<Rightarrow> p'\<rbrakk> \<Longrightarrow>
    (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s, p) \<Rightarrow> p'" |
IfFalse:
 "\<lbrakk>\<not> bval b s; (c\<^sub>2, s, p) \<Rightarrow> p'\<rbrakk> \<Longrightarrow>
    (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s, p) \<Rightarrow> p'" |
WhileFalse:
 "\<not> bval b s \<Longrightarrow> (WHILE b DO c, s, p) \<Rightarrow> (s, p)" |
WhileTrue:
 "\<lbrakk>bval b s\<^sub>1; (c, s\<^sub>1, p\<^sub>1) \<Rightarrow> (s\<^sub>2, p\<^sub>2);
    (WHILE b DO c, s\<^sub>2, p\<^sub>2) \<Rightarrow> (s\<^sub>3, p\<^sub>3)\<rbrakk> \<Longrightarrow>
  (WHILE b DO c, s\<^sub>1, p\<^sub>1) \<Rightarrow> (s\<^sub>3, p\<^sub>3)"


declare big_step.intros [intro]

inductive_cases SkipE [elim!]: "(SKIP, p) \<Rightarrow> p'"

inductive_cases AssignE [elim!]: "(x ::= a, p) \<Rightarrow> p'"

inductive_cases InputE [elim!]: "(IN x, p) \<Rightarrow> p'"

inductive_cases OutputE [elim!]: "(OUT x, p) \<Rightarrow> p'"

inductive_cases SeqE [elim!]: "(c\<^sub>1;; c\<^sub>2, p) \<Rightarrow> p'"

inductive_cases OrE [elim!]: "(c\<^sub>1 OR c\<^sub>2, p) \<Rightarrow> p'"

inductive_cases IfE [elim!]: "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, p) \<Rightarrow> p'"

inductive_cases WhileE [elim]: "(WHILE b DO c, p) \<Rightarrow> p'"


subsection "Extended small-step semantics"

text \<open>
The original small-step semantics of language IMP associates a pair formed by a command and a
program execution stage, which consists of a program state, with another such pair, formed by a
command to be executed next and a resulting program execution stage, which consists of a program
state as well. The extended small-step semantics defined here below rather uses the same extended
program execution stage notion as the extended big-step semantics specified above, and is defined
accordingly.

\null
\<close>

inductive small_step :: "com \<times> stage \<Rightarrow> com \<times> stage \<Rightarrow> bool"
  (infix \<open>\<rightarrow>\<close> 55) where
Assign:
 "(x ::= a, s, p) \<rightarrow> (SKIP, s(x := aval a s), p)" |
Input:
 "n = length [p\<leftarrow>vs. fst p = x] \<Longrightarrow> (IN x, s, f, vs, ws) \<rightarrow>
    (SKIP, s(x := f x n), f, vs @ [(x, f x n)], ws)" |
Output:
 "(OUT x, s, f, vs, ws) \<rightarrow> (SKIP, s, f, vs, ws @ [(x, s x)])" |
Seq1:
 "(SKIP;; c\<^sub>2, p) \<rightarrow> (c\<^sub>2, p)" |
Seq2:
 "(c\<^sub>1, p) \<rightarrow> (c\<^sub>1', p') \<Longrightarrow> (c\<^sub>1;; c\<^sub>2, p) \<rightarrow> (c\<^sub>1';; c\<^sub>2, p')" |
Or1:
 "(c\<^sub>1 OR c\<^sub>2, p) \<rightarrow> (c\<^sub>1, p)" |
Or2:
 "(c\<^sub>1 OR c\<^sub>2, p) \<rightarrow> (c\<^sub>2, p)" |
IfTrue:
 "bval b s \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s, p) \<rightarrow> (c\<^sub>1, s, p)" |
IfFalse:
 "\<not> bval b s \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s, p) \<rightarrow> (c\<^sub>2, s, p)" |
WhileFalse:
 "\<not> bval b s \<Longrightarrow> (WHILE b DO c, s, p) \<rightarrow> (SKIP, s, p)" |
WhileTrue:
 "bval b s \<Longrightarrow> (WHILE b DO c, s, p) \<rightarrow> (c;; WHILE b DO c, s, p)"


declare small_step.intros [simp, intro]

inductive_cases skipE [elim!]: "(SKIP, p) \<rightarrow> cf"

inductive_cases assignE [elim!]: "(x ::= a, p) \<rightarrow> cf"

inductive_cases inputE [elim!]: "(IN x, p) \<rightarrow> cf"

inductive_cases outputE [elim!]: "(OUT x, p) \<rightarrow> cf"

inductive_cases seqE [elim!]: "(c\<^sub>1;; c\<^sub>2, p) \<rightarrow> cf"

inductive_cases orE [elim!]: "(c\<^sub>1 OR c\<^sub>2, p) \<rightarrow> cf"

inductive_cases ifE [elim!]: "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, p) \<rightarrow> cf"

inductive_cases whileE [elim]: "(WHILE b DO c, p) \<rightarrow> cf"


abbreviation small_steps :: "com \<times> stage \<Rightarrow> com \<times> stage \<Rightarrow> bool"
  (infix \<open>\<rightarrow>*\<close> 55) where
"cf \<rightarrow>* cf' \<equiv> star small_step cf cf'"

function small_stepsl ::
 "com \<times> stage \<Rightarrow> (com \<times> stage) list \<Rightarrow> com \<times> stage \<Rightarrow> bool"
  (\<open>(_ \<rightarrow>*'{_'} _)\<close> [51, 51] 55)
where
"cf \<rightarrow>*{[]} cf' = (cf = cf')" |
"cf \<rightarrow>*{cfs @ [cf']} cf'' = (cf \<rightarrow>*{cfs} cf' \<and> cf' \<rightarrow> cf'')"

by (atomize_elim, auto intro: rev_cases)
termination by lexicographic_order


subsection "Equivalence of big-step and small-step semantics"

lemma star_seq2:
 "(c\<^sub>1, p) \<rightarrow>* (c\<^sub>1', p') \<Longrightarrow> (c\<^sub>1;; c\<^sub>2, p) \<rightarrow>* (c\<^sub>1';; c\<^sub>2, p')"
proof (induction rule: star_induct)
  case refl
  thus ?case
    by simp
next
  case step
  thus ?case
    by (blast intro: star.step)
qed

lemma seq_comp:
 "\<lbrakk>(c\<^sub>1, p\<^sub>1) \<rightarrow>* (SKIP, p\<^sub>2); (c\<^sub>2, p\<^sub>2) \<rightarrow>* (SKIP, p\<^sub>3)\<rbrakk> \<Longrightarrow>
    (c\<^sub>1;; c\<^sub>2, p\<^sub>1) \<rightarrow>* (SKIP, p\<^sub>3)"
by (blast intro: star.step star_seq2 star_trans)

lemma big_to_small:
 "cf \<Rightarrow> p \<Longrightarrow> cf \<rightarrow>* (SKIP, p)"
proof (induction rule: big_step.induct)
  fix c\<^sub>1 c\<^sub>2 p\<^sub>1 p\<^sub>2 p\<^sub>3
  assume "(c\<^sub>1, p\<^sub>1) \<rightarrow>* (SKIP, p\<^sub>2)" and "(c\<^sub>2, p\<^sub>2) \<rightarrow>* (SKIP, p\<^sub>3)"
  thus "(c\<^sub>1;; c\<^sub>2, p\<^sub>1) \<rightarrow>* (SKIP, p\<^sub>3)"
    by (rule seq_comp)
next
  fix c\<^sub>1 c\<^sub>2 p p'
  assume "(c\<^sub>1, p) \<rightarrow>* (SKIP, p')"
  thus "(c\<^sub>1 OR c\<^sub>2, p) \<rightarrow>* (SKIP, p')"
    by (blast intro: star.step)
next
  fix c\<^sub>1 c\<^sub>2 p p'
  assume "(c\<^sub>2, p) \<rightarrow>* (SKIP, p')"
  thus "(c\<^sub>1 OR c\<^sub>2, p) \<rightarrow>* (SKIP, p')"
    by (blast intro: star.step)
next
  fix b c\<^sub>1 c\<^sub>2 s p p'
  assume "bval b s"
  hence "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s, p) \<rightarrow> (c\<^sub>1, s, p)"
    by simp
  moreover assume "(c\<^sub>1, s, p) \<rightarrow>* (SKIP, p')"
  ultimately show
   "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s, p) \<rightarrow>* (SKIP, p')"
    by (simp add: star.step)
next
  fix b c\<^sub>1 c\<^sub>2 s p p'
  assume "\<not> bval b s"
  hence "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s, p) \<rightarrow> (c\<^sub>2, s, p)"
    by simp
  moreover assume "(c\<^sub>2, s, p) \<rightarrow>* (SKIP, p')"
  ultimately show
   "(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s, p) \<rightarrow>* (SKIP, p')"
    by (simp add: star.step)
next
  fix b c s\<^sub>1 s\<^sub>2 s\<^sub>3 p\<^sub>1 p\<^sub>2 p\<^sub>3
  assume "bval b s\<^sub>1"
  hence "(WHILE b DO c, s\<^sub>1, p\<^sub>1) \<rightarrow>* (c;; WHILE b DO c, s\<^sub>1, p\<^sub>1)"
    by simp
  moreover assume
   "(c, s\<^sub>1, p\<^sub>1) \<rightarrow>* (SKIP, s\<^sub>2, p\<^sub>2)" and
   "(WHILE b DO c, s\<^sub>2, p\<^sub>2) \<rightarrow>* (SKIP, s\<^sub>3, p\<^sub>3)"
  hence "(c;; WHILE b DO c, s\<^sub>1, p\<^sub>1) \<rightarrow>* (SKIP, s\<^sub>3, p\<^sub>3)"
    by (rule seq_comp)
  ultimately show "(WHILE b DO c, s\<^sub>1, p\<^sub>1) \<rightarrow>* (SKIP, s\<^sub>3, p\<^sub>3)"
    by (blast intro: star_trans)
qed fastforce+

lemma small1_big_continue:
 "\<lbrakk>cf \<rightarrow> cf'; cf' \<Rightarrow> p\<rbrakk> \<Longrightarrow> cf \<Rightarrow> p"
by (induction arbitrary: p rule: small_step.induct, force+)

lemma small_to_big:
 "cf \<rightarrow>* (SKIP, p) \<Longrightarrow> cf \<Rightarrow> p"
by (induction cf "(SKIP, p)" rule: star.induct,
 auto intro: small1_big_continue)

lemma big_iff_small:
 "cf \<Rightarrow> p = cf \<rightarrow>* (SKIP, p)"
by (blast intro: big_to_small small_to_big)

end
