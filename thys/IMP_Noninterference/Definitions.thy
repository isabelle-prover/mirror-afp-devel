(*  Title:       Information Flow Control via Stateful Intransitive Noninterference in Language IMP
    Author:      Pasquale Noce
                 Senior Staff Firmware Engineer at HID Global, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at hidglobal dot com
*)

section "Underlying concepts and formal definitions"

theory Definitions
  imports "HOL-IMP.Small_Step"
begin

(*<*)
setup \<open>
  Document_Output.antiquotation_raw_embedded \<^binding>\<open>lstlisting\<close>
    (Scan.lift Parse.embedded)
    (fn _ => fn s =>
      Latex.string "\\begin{lstlisting}\n" @
      Latex.string (cat_lines (trim (forall_string Symbol.is_space) (trim_split_lines s))) @
      Latex.string "\n\\end{lstlisting}")
\<close>
(*>*)

text \<open>
\null

In a passage of his book \emph{Clean Architecture: A Craftsman's Guide to Software Structure and
Design} (Prentice Hall, 2017), Robert C. Martin defines a computer program as ``a detailed
description of the policy by which inputs are transformed into outputs'', remarking that ``indeed,
at its core, that's all a computer program actually is''. Accordingly, the scope of information flow
control via static type systems is in principle much broader than language-based information flow
security, since this concept promises to cope with information flow correctness in full generality.

This is already shown by a basic program implementing the Euclidean algorithm, in Donald Knuth's
words ``the granddaddy of all algorithms, because it is the oldest nontrivial algorithm that has
survived to the present day'' (from \emph{The Art of Computer Programming, Volume 2: Seminumerical
Algorithms}, third edition, Addison-Wesley, 1997). Here below is a sample such C program, where
variables \lstinline{a} and \lstinline{b} initially contain two positive integers and \lstinline{a}
will finally contain the output, namely the greatest common divisor of those integers.

\null

\<^lstlisting>\<open>
do
{
    r = a % b;
    a = b;
    b = r;
} while (b);
\<close>

\null

Even in a so basic program, information is not allowed to indistinctly flow from any variable to any
other one, on pain of the program being incorrect. If an incautious programmer swapped \lstinline{a}
for \lstinline{b} in the assignment at line 4, the greatest common divisor output for any two inputs
\lstinline{a} and \lstinline{b} would invariably match \lstinline{a}, whereas swapping the sides of
the assignment at line 5 would give rise to an endless loop. Indeed, despite the marked differences
in the resulting program behavior, both of these potential errors originate in information flowing
between variables along paths other than the demanded ones. A sound implementation of the Euclidean
algorithm does not provide for any information flow from \lstinline{a} to \lstinline{b}, or from
\lstinline{b} to \lstinline{r}.

The static security type systems addressed in \<^cite>\<open>"Volpano96"\<close>, \<^cite>\<open>"Volpano97"\<close>, and
\<^cite>\<open>"Nipkow23-1"\<close> restrict the information flows occurring in a program based on a mapping of each
of its variables to a \emph{domain} along with an \emph{interference relation} between such domains,
including any pair of domains such that the former may interfere with the latter. Accordingly, if
function @{text dom} stands for such a mapping, and infix notation @{text "u \<leadsto> v"} denotes the
inclusion of any pair of domains @{text "(u, v)"} in such a relation (both notations are borrowed
from \<^cite>\<open>"Rushby92"\<close>), the above errors would be detected at compile time by a static type system
enforcing an interference relation such that:

  \<^item> @{text "dom a \<leadsto> dom r"}, @{text "dom b \<leadsto> dom r"} (line 3),

  \<^item> @{text "dom b \<leadsto> dom a"} (line 4),

  \<^item> @{text "dom r \<leadsto> dom b"} (line 5),

and ruling out any other pair of distinct domains. Such an interference relation would also embrace
the implicit information flow from \lstinline{b} to the other two variables arising from the loop's
termination condition (line 6).

Remarkably, as @{text "dom a \<leadsto> dom r"} and @{text "dom r \<leadsto> dom b"} but @{text "\<not> dom a \<leadsto> dom b"},
this interference relation turns out to be intransitive. Therefore, unlike the security static type
systems studied in \<^cite>\<open>"Volpano96"\<close> and \<^cite>\<open>"Volpano97"\<close>, which deal with \emph{level-based}, and
then \emph{transitive}, interference relations, a static type system aimed at enforcing information
flow correctness in full generality must be capable of dealing with \emph{intransitive} interference
relations as well. This should come as no surprise, since \<^cite>\<open>"Rushby92"\<close> shows that this is the
general case already for interference relations expressing information flow security policies.

But the bar can be raised further. Considering the above program again, the information flows needed
for its operation, as listed above, need not be allowed throughout the program. Indeed, information
needs to flow from \lstinline{a} and \lstinline{b} to \lstinline{r} at line 3, from \lstinline{b} to
\lstinline{a} at line 4, from \lstinline{r} to \lstinline{b} at line 5, and then (implicitly) from
\lstinline{b} to the other two variables at line 6. Based on this observation, error detection at
compile time can be made finer-grained by rewriting the program as follows, where \lstinline{i} is a
further integer variable introduced for this purpose.

\null

\<^lstlisting>\<open>
do
{
    i = 0;
    r = a % b;
    i = 1;
    a = b;
    i = 2;
    b = r;
    i = 3;
} while (b);
\<close>

\null

In this program, \lstinline{i} serves as a state variable whose value in every execution step can be
determined already at compile time. Since a distinct set of information flows is allowed for each of
its values, a finer-grained information flow correctness policy for this program can be expressed by
extending the concept of a single, \emph{stateless} interference relation applying throughout the
program to that of a \emph{stateful interference function} mapping program states to interference
relations (in this case, according to the value of \lstinline{i}). As a result of this extension,
for each program state, a distinct interference relation -- that is, the one to which the applied
interference function maps that state -- can be enforced at compile time by a suitable static type
system.

If mixfix notation @{text "s: u \<leadsto> v"} denotes the inclusion of any pair of domains @{text "(u, v)"}
in the interference relation associated with any state @{text s}, a finer-grained information flow
correctness policy for this program can then be expressed as an interference function such that:

  \<^item> @{text "s: dom a \<leadsto> dom r"}, @{text "s: dom b \<leadsto> dom r"} for any @{text s} where \lstinline{i}
$=0$ (line 4),

  \<^item> @{text "s: dom b \<leadsto> dom a"} for any @{text s} where \lstinline{i} $=1$ (line 6),

  \<^item> @{text "s: dom r \<leadsto> dom b"} for any @{text s} where \lstinline{i} $=2$ (line 8),

  \<^item> @{text "s: dom b \<leadsto> dom a"}, @{text "s: dom b \<leadsto> dom r"}, @{text "s: dom b \<leadsto> dom i"} for any
@{text s} where \lstinline{i} $=3$ (line 10),

and ruling out any other pair of distinct domains in any state.

Notably, to enforce such an interference function, a static type system would not need to keep track
of the full program state in every program execution step (which would be unfeasible, as the values
of \lstinline{a}, \lstinline{b}, and \lstinline{r} cannot be determined at compile time), but only
of the values of some specified state variables (in this case, of \lstinline{i} alone). Accordingly,
term \emph{state variable} will henceforth refer to any program variable whose value may affect that
of the interference function expressing the information flow correctness policy in force, namely the
interference relation to be applied.

Needless to say, there would be something artificial about the introduction of such a state variable
into the above sample program, since it is indeed so basic as not to provide for a state machine on
its own, so that \lstinline{i} would be aimed exclusively at enabling the enforcement of such an
information flow correctness policy. Yet, real-world imperative programs, for which error detection
at compile time is truly meaningful, \emph{do} typically provide for state machines such that only a
subset of all the potential information flows is allowed in each state; and even for those which do
not, the addition of some \emph{ad hoc} state variable to enforce such a policy could likely be an
acceptable trade-off.

Accordingly, the goal of this paper is to study information flow control via stateful intransitive
noninterference. First, the notion of termination-sensitive information flow security with respect
to a level-based interference relation, as defined in \<^cite>\<open>"Nipkow23-1"\<close>, section 9.2.6, is
generalized to that of termination-sensitive information flow correctness with respect to a stateful
interference function having (generally) intransitive interference relations as values. Then, a
static type system is specified and is proven to be capable of enforcing such information flow
correctness policies. Finally, the information flow correctness notion and the static type system
introduced here are proven to degenerate to the counterparts addressed in \<^cite>\<open>"Nipkow23-1"\<close>,
section 9.2.6, in case of a stateless level-based information flow correctness policy.

Although the operational semantics of the didactic imperative programming language IMP employed in
\<^cite>\<open>"Nipkow23-1"\<close> is used for this purpose, the introduced concepts are applicable to larger,
real-world imperative programming languages as well, by just affording the additional type system
complexity arising from richer language constructs. Accordingly, the informal explanations
accompanying formal content in what follows will keep making use of sample C code snippets.

For further information about the formal definitions and proofs contained in this paper, see
Isabelle documentation, particularly \<^cite>\<open>"Paulson23"\<close>, \<^cite>\<open>"Nipkow23-4"\<close>, \<^cite>\<open>"Krauss23"\<close>,
\<^cite>\<open>"Nipkow11"\<close>, and \<^cite>\<open>"Ballarin23"\<close>.
\<close>


subsection "Global context definitions"

declare [[syntax_ambiguity_warning = false]]


datatype com_flow =
  Assign vname aexp  ("_ ::= _" [1000, 61] 70) |
  Observe "vname set"  ("\<langle>_\<rangle>" [61] 70)

type_synonym flow = "com_flow list"
type_synonym config = "state set \<times> vname set"
type_synonym scope = "config set \<times> bool"


abbreviation eq_states :: "state \<Rightarrow> state \<Rightarrow> vname set \<Rightarrow> bool"
  ("(_ = _ '(\<subseteq> _'))" [51, 51] 50) where
"s = t (\<subseteq> X) \<equiv> \<forall>x \<in> X. s x = t x"

abbreviation univ_states :: "state set \<Rightarrow> vname set \<Rightarrow> state set"
  ("(Univ _ '(\<subseteq> _'))" [51] 75) where
"Univ A (\<subseteq> X) \<equiv> {s. \<exists>t \<in> A. s = t (\<subseteq> X)}"

abbreviation univ_vars_if :: "state set \<Rightarrow> vname set \<Rightarrow> vname set"
  ("(Univ?? _ _)" [51, 75] 75) where
"Univ?? A X \<equiv> if A = {} then UNIV else X"

abbreviation "tl2 xs \<equiv> tl (tl xs)"


fun run_flow :: "flow \<Rightarrow> state \<Rightarrow> state" where
"run_flow (x ::= a # cs) s = run_flow cs (s(x := aval a s))" |
"run_flow (_ # cs) s = run_flow cs s" |
"run_flow _ s = s"

primrec no_upd :: "flow \<Rightarrow> vname \<Rightarrow> bool" where
"no_upd (c # cs) x =
  ((case c of y ::= _ \<Rightarrow> y \<noteq> x | _ \<Rightarrow> True) \<and> no_upd cs x)" |
"no_upd [] _ = True"

primrec avars :: "aexp \<Rightarrow> vname set" where
"avars (N i) = {}" |
"avars (V x) = {x}" |
"avars (Plus a\<^sub>1 a\<^sub>2) = avars a\<^sub>1 \<union> avars a\<^sub>2"

primrec bvars :: "bexp \<Rightarrow> vname set" where
"bvars (Bc v) = {}" |
"bvars (Not b) = bvars b" |
"bvars (And b\<^sub>1 b\<^sub>2) = bvars b\<^sub>1 \<union> bvars b\<^sub>2" |
"bvars (Less a\<^sub>1 a\<^sub>2) = avars a\<^sub>1 \<union> avars a\<^sub>2"


fun flow_aux :: "com list \<Rightarrow> flow" where
"flow_aux ((x ::= a) # cs) = (x ::= a) # flow_aux cs" |
"flow_aux ((IF b THEN _ ELSE _) # cs) = \<langle>bvars b\<rangle> # flow_aux cs" |
"flow_aux ((c;; _) # cs) = flow_aux (c # cs)" |
"flow_aux (_ # cs) = flow_aux cs" |
"flow_aux [] = []"

definition flow :: "(com \<times> state) list \<Rightarrow> flow" where
"flow cfs = flow_aux (map fst cfs)"


function small_stepsl ::
 "com \<times> state \<Rightarrow> (com \<times> state) list \<Rightarrow> com \<times> state \<Rightarrow> bool"
  ("(_ \<rightarrow>*'{_'} _)" [51, 51] 55)
where
"cf \<rightarrow>*{[]} cf' = (cf = cf')" |
"cf \<rightarrow>*{cfs @ [cf']} cf'' = (cf \<rightarrow>*{cfs} cf' \<and> cf' \<rightarrow> cf'')"

by (atomize_elim, auto intro: rev_cases)
termination by lexicographic_order

lemmas small_stepsl_induct = small_stepsl.induct [split_format(complete)]


subsection "Local context definitions"

text \<open>
In what follows, stateful intransitive noninterference will be formalized within the local context
defined by means of a \emph{locale} \<^cite>\<open>"Ballarin23"\<close>, named @{text noninterf}. Later on, this
will enable to prove the degeneracy of the following definitions to the stateless level-based
counterparts addressed in \<^cite>\<open>"Volpano96"\<close>, \<^cite>\<open>"Volpano97"\<close>, and \<^cite>\<open>"Nipkow23-1"\<close>, and
formalized in \<^cite>\<open>"Nipkow23-2"\<close> and \<^cite>\<open>"Nipkow23-3"\<close>, via a suitable locale interpretation.

Locale @{text noninterf} contains three parameters, as follows.

  \<^item> A stateful interference function @{text interf} mapping program states to \emph{interference
    predicates} of two domains, intended to be true just in case the former domain is allowed to
    interfere with the latter.

  \<^item> A function @{text dom} mapping program variables to their respective domains.

  \<^item> A set @{text state} collecting all state variables.

As the type of the domains is modeled using a type variable, it may be assigned arbitrarily by any
locale interpretation, which will enable to set it to @{typ nat} upon proving degeneracy. Moreover,
the above mixfix notation @{text "s: u \<leadsto> v"} is adopted to express the fact that any two domains
@{text u}, @{text v} satisfy the interference predicate @{text "interf s"} associated with any state
@{text s}, namely the fact that @{text u} is allowed to interfere with @{text v} in state @{text s}.

Locale @{text noninterf} also contains an assumption, named @{text interf_state}, which serves the
purpose of supplying parameter @{text state} with its intended semantics, namely standing for the
set of all state variables. The assumption is that function @{text interf} maps any two program
states agreeing on the values of all the variables in set @{text state} to the same interference
predicate. Correspondingly, any locale interpretation instantiating parameter @{text state} as the
empty set must instantiate parameter @{text interf} as a function mapping any two program states,
even if differing in the values of all variables, to the same interference predicate -- namely, as a
constant function. Hence, any such locale interpretation refers to a single, stateless interference
predicate applying throughout the program. Unsurprisingly, this is the way how those parameters will
be instantiated upon proving degeneracy.

The one just mentioned is the only locale assumption. Particularly, the following formalization does
not rely upon the assumption that the interference predicates returned by function @{text interf} be
\emph{reflexive}, although this will be the case for any meaningful real-world information flow
correctness policy.

\null
\<close>

locale noninterf =
  fixes
    interf :: "state \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> bool"
      ("(_: _ \<leadsto> _)" [51, 51, 51] 50) and
    dom :: "vname \<Rightarrow> 'd" and
    state :: "vname set"
  assumes
    interf_state: "s = t (\<subseteq> state) \<Longrightarrow> interf s = interf t"


context noninterf
begin

text \<open>
\null

Locale parameters @{term interf} and @{term dom} are provided with their intended semantics by the
definitions of functions @{text sources} and @{text correct}, which are formalized here below based
on the following underlying ideas.

As long as a stateless transitive interference relation between domains is considered, the condition
for the correctness of the value of a variable resulting from a full or partial program execution
need not take into account the execution flow producing it, but rather the initial program state
only. In fact, this is what happens with the stateless level-based correctness condition addressed
in \<^cite>\<open>"Volpano96"\<close>, \<^cite>\<open>"Volpano97"\<close>, and \<^cite>\<open>"Nipkow23-1"\<close>: the resulting value of a variable
of level \emph{l} is correct if the same value is produced for any initial state agreeing with the
given one on the value of every variable of level not higher than \emph{l}.

Things are so simple because, for any variables \lstinline{x}, \lstinline{y}, and \lstinline{z}, if
@{text "dom z \<leadsto> dom y"} and @{text "dom y \<leadsto> dom x"}, transitivity entails @{text "dom z \<leadsto> dom x"},
and these interference relationships hold statelessly. Therefore, \lstinline{z} may be counted among
the variables whose initial values are allowed to affect \lstinline{x} independently of whether some
intermediate value of \lstinline{y} may affect \lstinline{x} within the actual execution flow.

Unfortunately, switching to stateful intransitive interference relations puts an end to that happy
circumstance -- indeed, even statefulness or intransitivity alone would suffice for this sad ending.
In this context, deciding about the correctness of the resulting value of a variable \lstinline{x}
still demands the detection of the variables whose initial values are allowed to interfere with
\lstinline{x}, but the execution flow leading from the initial program state to the resulting one
needs to be considered to perform such detection.

This is precisely the task of function @{text sources}, so named after its finite state machine
counterpart defined in \<^cite>\<open>Rushby92\<close>. It takes as inputs an execution flow @{term cs}, an initial
program state @{term s}, and a variable \lstinline{x}, and outputs the set of the variables whose
values in @{term s} are allowed to affect the value of \lstinline{x} in the state @{term s'} into
which @{term cs} turns @{term s}, according to @{term cs} as well as to the information flow
correctness policy expressed by parameters @{term interf} and @{term dom}.

In more detail, execution flows are modeled as lists comprising items of two possible kinds, namely
an assignment of the value of an arithmetic expression @{term a} to a variable \lstinline{z} or else
an \emph{observation} of the values of the variables in a set @{term X}, denoted through notations
@{term "z ::= a :: com_flow"} (same as with assignment commands) and @{term "\<langle>X\<rangle>"} and keeping track
of explicit and implicit information flows, respectively. Particularly, item @{term "\<langle>X\<rangle>"} refers to
the act of observing the values of the variables in @{term X} leaving the program state unaltered.
During the execution of an IMP program, this happens upon any evaluation of a boolean expression
containing all and only the variables in @{term X}.

Function @{text sources} is defined along with an auxiliary function @{text sources_aux} by means of
mutual recursion. Based on this definition, @{term "sources cs s x"} contains a variable @{term y}
if there exist a descending sequence of left sublists @{text "cs\<^sub>n\<^sub>+\<^sub>1"}, @{term "cs\<^sub>n @ [c\<^sub>n]"}, ...,
@{term "cs\<^sub>1 @ [c\<^sub>1]"} of @{term cs} and a sequence of variables @{text "y\<^sub>n\<^sub>+\<^sub>1"}, ..., @{term y\<^sub>1}, where
$n \ge 1$, @{text "cs\<^sub>n\<^sub>+\<^sub>1 = cs"}, @{text "y\<^sub>n\<^sub>+\<^sub>1 = x"}, and @{prop "y\<^sub>1 = y"}, satisfying the following
conditions.

  \<^item> For each positive integer $i \le n$, @{term c\<^sub>i} is an assignment @{text "y\<^sub>i\<^sub>+\<^sub>1 ::= a\<^sub>i"} where:

    \<^item> @{prop "y\<^sub>i \<in> avars a\<^sub>i"},

    \<^item> @{text "run_flow cs\<^sub>i s: dom y\<^sub>i \<leadsto> dom y\<^sub>i\<^sub>+\<^sub>1"}, and

    \<^item> the right sublist of @{text "cs\<^sub>i\<^sub>+\<^sub>1"} complementary to @{term "cs\<^sub>i @ [c\<^sub>i]"} does not comprise
any assignment to variable @{text "y\<^sub>i\<^sub>+\<^sub>1"} (as assignment @{term c\<^sub>i} would otherwise be irrelevant),

  or else an observation @{term "\<langle>X\<^sub>i\<rangle>"} where:

    \<^item> @{prop "y\<^sub>i \<in> X\<^sub>i"} and

    \<^item> @{text "run_flow cs\<^sub>i s: dom y\<^sub>i \<leadsto> dom y\<^sub>i\<^sub>+\<^sub>1"}.

  \<^item> @{term cs\<^sub>1} does not comprise any assignment to variable @{term y}.

In addition, @{term "sources cs s x"} contains variable @{term x} also if @{term cs} does not
comprise any assignment to variable @{term x}.

\null
\<close>

function
  sources :: "flow \<Rightarrow> state \<Rightarrow> vname \<Rightarrow> vname set" and
  sources_aux :: "flow \<Rightarrow> state \<Rightarrow> vname \<Rightarrow> vname set" where

"sources (cs @ [c]) s x = (case c of
  z ::= a \<Rightarrow> if z = x
    then sources_aux cs s x \<union> \<Union> {sources cs s y | y.
      run_flow cs s: dom y \<leadsto> dom x \<and> y \<in> avars a}
    else sources cs s x |
  \<langle>X\<rangle> \<Rightarrow>
    sources cs s x \<union> \<Union> {sources cs s y | y.
      run_flow cs s: dom y \<leadsto> dom x \<and> y \<in> X})" |

"sources [] _ x = {x}" |

"sources_aux (cs @ [c]) s x = (case c of
  _ ::= _ \<Rightarrow>
    sources_aux cs s x |
  \<langle>X\<rangle> \<Rightarrow>
    sources_aux cs s x \<union> \<Union> {sources cs s y | y.
      run_flow cs s: dom y \<leadsto> dom x \<and> y \<in> X})" |

"sources_aux [] _ _ = {}"

proof (atomize_elim)
  fix a :: "flow \<times> state \<times> vname + flow \<times> state \<times> vname"
  {
    assume
     "\<forall>cs c s x. a \<noteq> Inl (cs @ [c], s, x)" and
     "\<forall>s x. a \<noteq> Inl ([], s, x)" and
     "\<forall>s x. a \<noteq> Inr ([], s, x)"
    hence "\<exists>cs c s x. a = Inr (cs @ [c], s, x)"
      by (metis obj_sumE prod_cases3 rev_exhaust)
  }
  thus
   "(\<exists>cs c s x. a = Inl (cs @ [c], s, x)) \<or>
    (\<exists>s x. a = Inl ([], s, x)) \<or>
    (\<exists>cs c s x. a = Inr (cs @ [c], s, x)) \<or>
    (\<exists>s x. a = Inr ([], s, x))"
    by blast
qed auto

termination by lexicographic_order

lemmas sources_induct = sources_sources_aux.induct

text \<open>
\null

Predicate @{text correct} takes as inputs a program @{term c}, a set of program states @{term A},
and a set of variables @{term X}. Its truth value equals that of the following termination-sensitive
information flow correctness condition: for any state @{term s} agreeing with a state in @{term A}
on the values of the state variables in @{term X}, if the \emph{small-step} program semantics turns
configuration @{term "(c, s)"} into configuration @{term "(c\<^sub>1, s\<^sub>1)"}, and @{term "(c\<^sub>1, s\<^sub>1)"} into
configuration @{term "(c\<^sub>2, s\<^sub>2)"}, then for any state @{term t\<^sub>1} agreeing with @{term s\<^sub>1} on the
values of the variables in @{term "sources cs s\<^sub>1 x"}, where @{term cs} is the execution flow leading
from @{term "(c\<^sub>1, s\<^sub>1)"} to @{term "(c\<^sub>2, s\<^sub>2)"}, the small-step semantics turns @{term "(c\<^sub>1, t\<^sub>1)"} into
some configuration @{term "(c\<^sub>2', t\<^sub>2)"} such that:

  \<^item> @{prop "c\<^sub>2' = SKIP"} (namely, @{term "(c\<^sub>2', t\<^sub>2)"} is a \emph{final} configuration) just in case
@{prop "c\<^sub>2 = SKIP"}, and

  \<^item> the value of variable \lstinline{x} in state @{term t\<^sub>2} is the same as in state @{term s\<^sub>2}.

Here below are some comments about this definition.

  \<^item> As @{term "sources cs s\<^sub>1 x"} is the set of the variables whose values in @{term s\<^sub>1} are allowed
to affect the value of \lstinline{x} in @{term s\<^sub>2}, this definition requires any state @{term t\<^sub>1}
indistinguishable from @{term s\<^sub>1} in the values of those variables to produce a state where variable
\lstinline{x} has the same value as in @{term s\<^sub>2} in the continuation of program execution.

  \<^item> Configuration @{term "(c\<^sub>2', t\<^sub>2)"} must be the same one for \emph{any} variable \lstinline{x}
such that @{term s\<^sub>1} and @{term t\<^sub>1} agree on the values of any variable in @{term "sources cs s\<^sub>1 x"}.
Otherwise, even if states @{term s\<^sub>2} and @{term t\<^sub>2} agreed on the value of \lstinline{x}, they could
be distinguished all the same based on a discrepancy between the respective values of some other
variable. Likewise, if state @{term t\<^sub>2} alone had to be the same for any such \lstinline{x}, while
command @{term c\<^sub>2'} were allowed to vary, state @{term t\<^sub>1} could be distinguished from @{term s\<^sub>1}
based on the continuation of program execution. This is the reason why the universal quantification
over @{term x} is nested within the existential quantification over both @{term c\<^sub>2'} and @{term t\<^sub>2}.

  \<^item> The state machine for a program typically provides for a set of initial states from which its
execution is intended to start. In any such case, information flow correctness need not be assessed
for arbitrary initial states, but just for those complying with the settled tuples of initial values
for state variables. The values of any other variables do not matter, as they do not affect function
@{term interf}'s ones. This is the motivation for parameter @{term A}, which then needs to contain
just one state for each of such tuples, while parameter @{term X} enables to exclude the state
variables, if any, whose initial values are not settled.

  \<^item> If locale parameter @{term state} matches the empty set, @{term s} will be any state agreeing
with some state in @{term A} on the value of possibly even no variable at all, that is, a fully
arbitrary state provided that @{term A} is nonempty. This makes @{term s} range over all possible
states, as required for establishing the degeneracy of the present definition to the stateless
level-based counterpart addressed in \<^cite>\<open>"Nipkow23-1"\<close>, section 9.2.6.

Why express information flow correctness in terms of the small-step program semantics, instead of
resorting to the big-step one as happens with the stateless level-based correctness condition in
\<^cite>\<open>"Nipkow23-1"\<close>, section 9.2.6? The answer is provided by the following sample C programs, where
\lstinline{i} is a state variable.

\null

\<^lstlisting>\<open>
y = i;
i = (i) ? 1 : 0;
x = i + y;
\<close>

\null

\<^lstlisting>\<open>
x = 0;
if (i == 10)
{
  x = 10;
}
i = (i) ? 1 : 0;
x += i;
\<close>

\null

Let \lstinline{i} be allowed to interfere with \lstinline{x} just in case \lstinline{i} matches 0 or
1, and \lstinline{y} be never allowed to do so. If @{term s\<^sub>1} were constrained to be the initial
state, for both programs \lstinline{i} would be included among the variables on which @{term t\<^sub>1}
needs to agree with @{term s\<^sub>1} in order to be indistinguishable from @{term s\<^sub>1} in the value of
\lstinline{x} resulting from the final assignment. Thus, both programs would fail to be labeled as
wrong ones, although in both of them the information flow blatantly bypasses the sanitization of the
initial value of \lstinline{i}, respectively due to an illegal explicit flow and an illegal implicit
flow. On the contrary, the present information flow correctness definition detects any such illegal
information flow by checking every partial program execution on its own.

\null
\<close>

abbreviation ok_flow :: "com \<Rightarrow> com \<Rightarrow> state \<Rightarrow> state \<Rightarrow> flow \<Rightarrow> bool" where
"ok_flow c\<^sub>1 c\<^sub>2 s\<^sub>1 s\<^sub>2 cs \<equiv>
  \<forall>t\<^sub>1. \<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
    s\<^sub>1 = t\<^sub>1 (\<subseteq> sources cs s\<^sub>1 x) \<longrightarrow>
      (c\<^sub>1, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c\<^sub>2 = SKIP) = (c\<^sub>2' = SKIP) \<and> s\<^sub>2 x = t\<^sub>2 x"

definition correct :: "com \<Rightarrow> state set \<Rightarrow> vname set \<Rightarrow> bool" where
"correct c A X \<equiv>
  \<forall>s \<in> Univ A (\<subseteq> state \<inter> X). \<forall>c\<^sub>1 c\<^sub>2 s\<^sub>1 s\<^sub>2 cfs.
    (c, s) \<rightarrow>* (c\<^sub>1, s\<^sub>1) \<and> (c\<^sub>1, s\<^sub>1) \<rightarrow>*{cfs} (c\<^sub>2, s\<^sub>2) \<longrightarrow>
      ok_flow c\<^sub>1 c\<^sub>2 s\<^sub>1 s\<^sub>2 (flow cfs)"


abbreviation interf_set :: "state set \<Rightarrow> 'd set \<Rightarrow> 'd set \<Rightarrow> bool"
  ("(_: _ \<leadsto> _)" [51, 51, 51] 50) where
"A: U \<leadsto> W \<equiv> \<forall>s \<in> A. \<forall>u \<in> U. \<forall>w \<in> W. s: u \<leadsto> w"

abbreviation ok_flow_aux ::
 "config set \<Rightarrow> com \<Rightarrow> com \<Rightarrow> state \<Rightarrow> state \<Rightarrow> flow \<Rightarrow> bool" where
"ok_flow_aux U c\<^sub>1 c\<^sub>2 s\<^sub>1 s\<^sub>2 cs \<equiv>
  (\<forall>t\<^sub>1. \<exists>c\<^sub>2' t\<^sub>2. \<forall>x.
    (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux cs s\<^sub>1 x) \<longrightarrow>
      (c\<^sub>1, t\<^sub>1) \<rightarrow>* (c\<^sub>2', t\<^sub>2) \<and> (c\<^sub>2 = SKIP) = (c\<^sub>2' = SKIP)) \<and>
    (s\<^sub>1 = t\<^sub>1 (\<subseteq> sources cs s\<^sub>1 x) \<longrightarrow> s\<^sub>2 x = t\<^sub>2 x)) \<and>
  (\<forall>x. (\<exists>p \<in> U. case p of (B, Y) \<Rightarrow>
    \<exists>s \<in> B. \<exists>y \<in> Y. \<not> s: dom y \<leadsto> dom x) \<longrightarrow> no_upd cs x)"

text \<open>
\null

The next step is defining a static type system guaranteeing that well-typed programs satisfy this
information flow correctness criterion. Whenever defining a function, and the pursued type system is
obviously no exception, the primary question that one has to answer is: which inputs and outputs
should it provide for? The type system formalized in \<^cite>\<open>"Nipkow23-3"\<close> simply makes a pass/fail
decision on an input program, based on an input security level, and outputs the verdict as a boolean
value. Is this still enough in the present case? The answer can be found by considering again the
above C program that computes the greatest common divisor of two positive integers \lstinline{a},
\lstinline{b} using a state variable \lstinline{i}, along with its associated stateful interference
function. For the reader's convenience, the program is reported here below.

\null

\<^lstlisting>\<open>
do
{
    i = 0;
    r = a % b;
    i = 1;
    a = b;
    i = 2;
    b = r;
    i = 3;
} while (b);
\<close>

\null

As @{prop "s: dom a \<leadsto> dom r"} only for a state @{term s} where \lstinline{i} $=0$, the type system
cannot determine that the assignment \lstinline{r = a % b} at line 4 is well-typed without knowing
that \lstinline{i} $=0$ whenever that step is executed. Consequently, upon checking the assignment
\lstinline{i = 0} at line 3, the type system must output information indicating that \lstinline{i}
$=0$ as a result of its execution. This information will then be input to the type system when it is
recursively invoked to check line 4, so as to enable the well-typedness of the next assignment to be
ascertained.

Therefore, in addition to the program under scrutiny, the type system needs to take a set of program
states as input, and as long as the program is well-typed, the output must include a set of states
covering any change to the values of the state variables possibly triggered by the input program. In
other words, the type system has to \emph{simulate} the execution of the input program at compile
time as regards the values of its state variables. In the following formalization, this results in
making the type system take an input of type @{typ "state set"} and output a value of the same type.
Yet, since state variables alone are relevant, a real-world implementation of the type system would
not need to work with full @{typ state} values, but just with tuples of state variables' values.

Is the input/output of a set of program states sufficient to keep track of the possible values of
the state variables at each execution step? Here below is a sample C program helping find an answer,
which determines the minimum of two integers \lstinline{a}, \lstinline{b} and assigns it to variable
\lstinline{a} using a state variable \lstinline{i}.

\null

\<^lstlisting>\<open>
i = (a > b) ? 1 : 0;
if (i > 0)
{
  a = b;
}
\<close>

\null

Assuming that the initial value of \lstinline{i} is 0, the information flow correctness policy for
this program will be such that:

  \<^item> @{prop "s: dom a \<leadsto> dom i"}, @{prop "s: dom b \<leadsto> dom i"} for any program state @{text s} where
\lstinline{i} $=0$ (line 1),

  \<^item> @{prop "s: dom i \<leadsto> dom a"} for any @{text s} where \lstinline{i} $=0$ or \lstinline{i} $=1$
(line 2, more on this later),

  \<^item> @{prop "s: dom b \<leadsto> dom a"} for any @{text s} where \lstinline{i} $=1$ (line 4),

ruling out any other pair of distinct domains in any state.

So far, everything has gone smoothly. However, what happens if the program is changed as follows?

\null

\<^lstlisting>\<open>
i = a - b;
if (i > 0)
{
  a = b;
}
\<close>

\null

Upon simulating the execution of the former program, the type system can determine the set
$\{0, 1\}$ of the possible values of variable \lstinline{i} arising from the conditional assignment
\lstinline{i = (a > b) ? 1 : 0} at line 1. On the contrary, in the case of the latter program, the
possible values of \lstinline{i} after the assignment \lstinline{i = a - b} at line 1 must be marked
as being \emph{indeterminate}, since they depend on the initial values of variables \lstinline{a}
and \lstinline{b}, which are unknown at compile time. Hence, the type system needs to provide for an
additional input/output parameter of type @{typ "vname set"}, whose input and output values shall
collect the variables whose possible values before and after the execution of the input program are
\emph{determinate}.

The correctness of the simulation of program execution by the type system can be expressed as the
following condition. Suppose that the type system outputs a @{typ "state set"} @{term A'} and a
@{typ "vname set"} @{term X'} when it is input a program @{term c}, a @{typ "state set"} @{term A},
and a @{typ "vname set"} @{term X}. Then, for any state @{term s} agreeing with some state in
@{term A} on the value of every state variable in @{term X}, if @{prop "(c, s) \<Rightarrow> s'"}, @{term s'}
must agree with some state in @{term A'} on the value of every state variable in @{term X'}. This
can be summarized by saying that the type system must \emph{overapproximate} program semantics,
since any algorithm simulating program execution cannot but be imprecise (see \<^cite>\<open>"Nipkow23-1"\<close>,
\emph{incipit} of chapter 13).

In turn, if the outputs for @{term c}, @{term A'}, @{term X'} are @{term A''}, @{term X''} and
@{prop "(c, s') \<Rightarrow> s''"}, @{term s''} must agree with some state in @{term A''} on the value of
every state variable in @{term X''}. But if @{term c} is a loop and @{prop "(c, s) \<Rightarrow> s'"}, then
@{prop "(c, s') \<Rightarrow> s''"} just in case @{prop "s' = s''"}, so that the type system is guaranteed to
overapproximate the semantics of @{term c} only if states consistent with @{term A'}, @{term X'} are
also consistent with @{term "A''"}, @{term X''} and vice versa. Thus, the type system needs to be
\emph{idempotent} if @{term c} is a loop, that is, it must be such that @{prop "A' = A''"} and
@{prop "X' = X''"} in this case. Since idempotence is not required for control structures other than
loops, the main type system @{text ctyping2} formalized in what follows will delegate the simulation
of the execution of loop bodies to an auxiliary, idempotent type system @{text ctyping1}.

This type system keeps track of the program state updates possibly occurring in its input program
using sets of lists of functions of type @{typ "vname \<Rightarrow> val option option"}. Command @{const SKIP}
is mapped to a singleton made of the empty list, as no state update takes place. An assignment to a
variable \lstinline{x} is mapped to a singleton made of a list comprising a single function, whose
value is @{term "Some (Some i)"} or @{term "Some None"} for \lstinline{x} if it is a state variable
and the right-hand side is a constant @{term "N i"} or a non-constant expression, respectively, and
@{const None} otherwise. That is, @{const None} stands for \emph{unchanged/non-state variable}
(remember, only state variable updates need to be tracked), whereas @{term "Some None"} stands for
\emph{indeterminate variable}, since the value of a non-constant expression in a loop iteration
(remember, @{text ctyping1} is meant for simulating the execution of loop bodies) is in general
unknown at compile time.

At first glance, a conditional statement could simply be mapped to the union of the sets tracking
the program state updates possibly occurring in its branches. However, things are not so simple, as
shown by the sample C loop here below, which has a conditional statement as its body.

\null

\<^lstlisting>\<open>
for (i = 0; i < 2; i++)
{
  if (n % 2)
  {
    a = 1;
    b = 1;
    n++;
  }
  else
  {
    a = 2;
    c = 2;
    n++;
  }
}
\<close>

\null

If the initial value of the integer variable \lstinline{n} is even, the final values of variables
\lstinline{a}, \lstinline{b}, and \lstinline{c} will be 1, 1, 2, whereas if the initial value of
\lstinline{n} is odd, the final values of the aforesaid variables will be 2, 1, 2. Assuming that
their initial value is 0, the potential final values tracked by considering each branch individually
are 1, 1, 0 and 2, 0, 2 instead. These are exactly the values generated by a single loop iteration;
if they are fed back into the loop body along with the increased value of \lstinline{n}, the actual
final values listed above are produced.

As a result, a mere union of the sets tracking the program state updates possibly occurring in each
branch would not be enough for the type system to be idempotent. The solution is to rather construct
every possible alternate concatenation without repetitions of the lists contained in each set, which
is referred to as \emph{merging} those sets in the following formalization. In fact, alternating the
state updates performed by each branch in the previous example produces the actual final values
listed above. Since the latest occurrence of a state update makes any previous occurrence irrelevant
for the final state, repetitions need not be taken into account, which ensures the finiteness of the
construction provided that the sets being merged are finite. In the special case where the boolean
condition can be evaluated at compile time, considering the picked branch alone is of course enough.

Another case trickier than what one could expect at first glance is that of sequential composition.
This is shown by the sample C loop here below, whose body consists of the sequential composition of
some assignments with a conditional statement.

\null

\<^lstlisting>\<open>
for (i = 0; i < 2; i++)
{
  a = 1;
  b = 1;
  if (n % 2)
  {
    a = 2;
    c = 2;
    n++;
  }
  else
  {
    b = 3;
    d = 3;
    n++;
  }
}
\<close>

\null

If the initial value of the integer variable \lstinline{n} is even, the final values of variables
\lstinline{a}, \lstinline{b}, \lstinline{c}, and \lstinline{d} will be 2, 1, 2, 3, whereas if the
initial value of \lstinline{n} is odd, the final values of the aforesaid variables will be 1, 3, 2,
3. Assuming that their initial value is 0, the potential final values tracked by considering the
sequences of the state updates triggered by the starting assignments with the updates, simulated as
described above, possibly triggered by the conditional statement rather are:

  \<^item> 2, 1, 2, 0,

  \<^item> 1, 3, 0, 3,

  \<^item> 2, 3, 2, 3.

The first two tuples of values match the ones generated by a single loop iteration, and produce the
actual final values listed above if they are fed back into the loop body along with the increased
value of \lstinline{n}.

Hence, concatenating the lists tracking the state updates possibly triggered by the first command in
the sequence (the starting assignment sequence in the previous example) with the lists tracking the
updates possibly triggered by the second command in the sequence (the conditional statement in the
previous example) would not suffice for the type system to be idempotent. The solution is to rather
append the latter lists to those constructed by \emph{merging} the sets tracking the state updates
possibly performed by each command in the sequence. Again, provided that such sets are finite, this
construction is finite, too. In the special case where the latter set is a singleton, the aforesaid
merging is unnecessary, as it would merely insert a preceding occurrence of the single appended list
into the resulting concatenated lists, and such repetitions are irrelevant as observed above.

Surprisingly enough, the case of loops is actually simpler than possible first-glance expectations.
A loop defines two branches, namely its body and an implicit alternative branch doing nothing. Thus,
it can simply be mapped to the union of the set tracking the state updates possibly occurring in its
body with a singleton made of the empty list. As happens with conditional statements, in the special
case where the boolean condition can be evaluated at compile time, considering the selected branch
alone is obviously enough.

Type system @{text ctyping1} uses the set of lists resulting from this recursion over the input
command to construct a set @{text F} of functions of type @{typ "vname \<Rightarrow> val option option"}, as
follows: for each list @{text ys} in the former set, @{text F} contains the function mapping any
variable \lstinline{x} to the rightmost occurrence, if any, of pattern @{term "Some v"} to which
\lstinline{x} is mapped by any function in @{text ys} (that is, to the latest update, if any, of
\lstinline{x} tracked in @{text ys}), or else to @{const None}. Then, if @{text A}, @{text X} are
the input @{typ "state set"} and @{typ "vname set"}, and @{text B}, @{text Y} the output ones:

  \<^item> @{text B} is the set of the program states constructed by picking a function @{text f} and a
state @{text s} from @{text F} and @{text A}, respectively, and mapping any variable \lstinline{x}
to @{text i} if @{prop "f x = Some (Some i)"}, or else to @{term "s x"} if @{prop "f x = None"}
(namely, to its value in the initial state @{text s} if @{text f} marks it as being unchanged).

  \<^item> @{text Y} is @{const UNIV} if @{prop "A = {}"} (more on this later), or else the set of the
variables not mapped to @{term "Some None"} (that is, not marked as being indeterminate) by any
function in @{text F}, and contained in @{text X} (namely, being initially determinate) if mapped to
@{const None} (that is, if marked as being unchanged) by some function in @{text F}.

When can @{text ctyping1} evaluate the boolean condition of a conditional statement or a loop, so as
to possibly detect and discard some ``dead'' branch? This question can be answered by examining the
following sample C loop, where \lstinline{n} is a state variable, while integer \lstinline{j} is
unknown at compile time.

\null

\<^lstlisting>\<open>
for (i = 0; i != j; i++)
{
  if (n == 1)
  {
    n = 2;
  }
  else if (n == 0)
  {
    n = 1;
  }
}
\<close>

\null

Assuming that the initial value of \lstinline{n} is 0, its final value will be 0, 1, or 2 according
to whether \lstinline{j} matches 0, 1, or any other positive integer, respectively, whereas the loop
will not even terminate if \lstinline{j} is negative. Consequently, the type system cannot avoid
tracking the state updates possibly triggered in every branch, on pain of failing to be idempotent.
As a result, evaluating the boolean conditions in the conditional statement at compile time so as to
discard some branch is not possible, even though they only depend on an initially determinate state
variable. The conclusion is that @{text ctyping1} may generally evaluate boolean conditions just in
case they contain constants alone, namely only if they are trivial enough to be possibly eliminated
by program optimization. This is exactly what @{text ctyping1} does by passing any boolean condition
found in the input program to the type system @{text btyping1} for boolean expressions, defined here
below as well.

\null
\<close>

primrec btyping1 :: "bexp \<Rightarrow> bool option" ("(\<turnstile> _)" [51] 55) where

"\<turnstile> Bc v = Some v" |

"\<turnstile> Not b = (case \<turnstile> b of
  Some v \<Rightarrow> Some (\<not> v) | _ \<Rightarrow> None)" |

"\<turnstile> And b\<^sub>1 b\<^sub>2 = (case (\<turnstile> b\<^sub>1, \<turnstile> b\<^sub>2) of
  (Some v\<^sub>1, Some v\<^sub>2) \<Rightarrow> Some (v\<^sub>1 \<and> v\<^sub>2) | _ \<Rightarrow> None)" |

"\<turnstile> Less a\<^sub>1 a\<^sub>2 = (if avars a\<^sub>1 \<union> avars a\<^sub>2 = {}
  then Some (aval a\<^sub>1 (\<lambda>x. 0) < aval a\<^sub>2 (\<lambda>x. 0)) else None)"


type_synonym state_upd = "vname \<Rightarrow> val option option"

inductive_set ctyping1_merge_aux :: "state_upd list set \<Rightarrow>
  state_upd list set \<Rightarrow> (state_upd list \<times> bool) list set"
  (infix "\<Squnion>" 55) for A and B where

"xs \<in> A \<Longrightarrow> [(xs, True)] \<in> A \<Squnion> B" |

"ys \<in> B \<Longrightarrow> [(ys, False)] \<in> A \<Squnion> B" |

"\<lbrakk>ws \<in> A \<Squnion> B; \<not> snd (last ws); xs \<in> A; (xs, True) \<notin> set ws\<rbrakk> \<Longrightarrow>
   ws @ [(xs, True)] \<in> A \<Squnion> B" |

"\<lbrakk>ws \<in> A \<Squnion> B; snd (last ws); ys \<in> B; (ys, False) \<notin> set ws\<rbrakk> \<Longrightarrow>
   ws @ [(ys, False)] \<in> A \<Squnion> B"

declare ctyping1_merge_aux.intros [intro]

definition ctyping1_append ::
 "state_upd list set \<Rightarrow> state_upd list set \<Rightarrow> state_upd list set"
  (infixl "@" 55) where
"A @ B \<equiv> {xs @ ys | xs ys. xs \<in> A \<and> ys \<in> B}"

definition ctyping1_merge ::
 "state_upd list set \<Rightarrow> state_upd list set \<Rightarrow> state_upd list set"
  (infixl "\<squnion>" 55) where
"A \<squnion> B \<equiv> {concat (map fst ws) | ws. ws \<in> A \<Squnion> B}"

definition ctyping1_merge_append ::
 "state_upd list set \<Rightarrow> state_upd list set \<Rightarrow> state_upd list set"
  (infixl "\<squnion>\<^sub>@" 55) where
"A \<squnion>\<^sub>@ B \<equiv> (if card B = Suc 0 then A else A \<squnion> B) @ B"


primrec ctyping1_aux :: "com \<Rightarrow> state_upd list set"
  ("(\<turnstile> _)" [51] 60) where

"\<turnstile> SKIP = {[]}" |

"\<turnstile> y ::= a = {[\<lambda>x. if x = y \<and> y \<in> state
  then if avars a = {} then Some (Some (aval a (\<lambda>x. 0))) else Some None
  else None]}" |

"\<turnstile> c\<^sub>1;; c\<^sub>2 = \<turnstile> c\<^sub>1 \<squnion>\<^sub>@ \<turnstile> c\<^sub>2" |

"\<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 = (let f = \<turnstile> b in
  (if f \<in> {Some True, None} then \<turnstile> c\<^sub>1 else {}) \<squnion>
  (if f \<in> {Some False, None} then \<turnstile> c\<^sub>2 else {}))" |

"\<turnstile> WHILE b DO c = (let f = \<turnstile> b in
  (if f \<in> {Some False, None} then {[]} else {}) \<union>
  (if f \<in> {Some True, None} then \<turnstile> c else {}))"

definition ctyping1_seq :: "state_upd \<Rightarrow> state_upd \<Rightarrow> state_upd"
  (infixl ";;" 55) where
"S;; T \<equiv> \<lambda>x. case T x of None \<Rightarrow> S x | Some v \<Rightarrow> Some v"

definition ctyping1 :: "com \<Rightarrow> state set \<Rightarrow> vname set \<Rightarrow> config"
  ("(\<turnstile> _ '(\<subseteq> _, _'))" [51] 55) where
"\<turnstile> c (\<subseteq> A, X) \<equiv> let F = {\<lambda>x. foldl (;;) (\<lambda>x. None) ys x | ys. ys \<in> \<turnstile> c} in
  ({\<lambda>x. case f x of None \<Rightarrow> s x | Some None \<Rightarrow> t x | Some (Some i) \<Rightarrow> i |
     f s t. f \<in> F \<and> s \<in> A},
   Univ?? A {x. \<forall>f \<in> F. f x \<noteq> Some None \<and> (f x = None \<longrightarrow> x \<in> X)})"

text \<open>
\null

A further building block propaedeutic to the definition of the main type system @{text ctyping2} is
the definition of its own companion type system @{text btyping2} for boolean expressions. The goal
of @{text btyping2} is splitting, whenever feasible at compile time, an input @{typ "state set"}
into two complementary subsets, respectively comprising the program states making the input boolean
expression true or false. This enables @{text ctyping2} to apply its information flow correctness
checks to conditional branches by considering only the program states in which those branches are
executed.

As opposed to @{const btyping1}, @{text btyping2} may evaluate its input boolean expression even if
it contains variables, provided that all of their values are known at compile time, namely that all
of them are determinate state variables -- hence @{text btyping2}, like @{text ctyping2}, needs to
take a @{typ "vname set"} collecting determinate variables as an additional input. In fact, in the
case of a loop body, the dirty work of covering any nested branch by skipping the evaluation of
non-constant boolean conditions is already done by @{const ctyping1}, so that any @{typ "state set"}
and @{typ "vname set"} input to @{text btyping2} already encompass every possible execution flow.

\null
\<close>

primrec btyping2_aux :: "bexp \<Rightarrow> state set \<Rightarrow> vname set \<Rightarrow> state set option"
  ("(\<TTurnstile> _ '(\<subseteq> _, _'))" [51] 55) where

"\<TTurnstile> Bc v (\<subseteq> A, _) = Some (if v then A else {})" |

"\<TTurnstile> Not b (\<subseteq> A, X) = (case \<TTurnstile> b (\<subseteq> A, X) of
  Some B \<Rightarrow> Some (A - B) | _ \<Rightarrow> None)" |

"\<TTurnstile> And b\<^sub>1 b\<^sub>2 (\<subseteq> A, X) = (case (\<TTurnstile> b\<^sub>1 (\<subseteq> A, X), \<TTurnstile> b\<^sub>2 (\<subseteq> A, X)) of
  (Some B\<^sub>1, Some B\<^sub>2) \<Rightarrow> Some (B\<^sub>1 \<inter> B\<^sub>2) | _ \<Rightarrow> None)" |

"\<TTurnstile> Less a\<^sub>1 a\<^sub>2 (\<subseteq> A, X) = (if avars a\<^sub>1 \<union> avars a\<^sub>2 \<subseteq> state \<inter> X
  then Some {s. s \<in> A \<and> aval a\<^sub>1 s < aval a\<^sub>2 s} else None)"

definition btyping2 :: "bexp \<Rightarrow> state set \<Rightarrow> vname set \<Rightarrow>
  state set \<times> state set"
  ("(\<Turnstile> _ '(\<subseteq> _, _'))" [51] 55) where
"\<Turnstile> b (\<subseteq> A, X) \<equiv> case \<TTurnstile> b (\<subseteq> A, X) of
  Some A' \<Rightarrow> (A', A - A') | _ \<Rightarrow> (A, A)"

text \<open>
\null

It is eventually time to define the main type system @{text ctyping2}. Its output consists of the
@{typ "state set"} of the final program states and the @{typ "vname set"} of the finally determinate
variables produced by simulating the execution of the input program, based on the @{typ "state set"}
of initial program states and the @{typ "vname set"} of initially determinate variables taken as
inputs, if information flow correctness checks are passed; otherwise, the output is @{const None}.

An additional input is the counterpart of the level input to the security type systems formalized in
\<^cite>\<open>"Nipkow23-3"\<close>, in that it specifies the \emph{scope} in which information flow correctness is
validated. It consists of a set of @{typ "state set \<times> vname set"} pairs and a boolean flag. The set
keeps track of the variables contained in the boolean conditions, if any, nesting the input program,
in association with the program states in which they are evaluated. The flag is @{const False} if
the input program is nested in a loop, in which case state variables set to non-constant expressions
are marked as being indeterminate (as observed previously, the value of a non-constant expression in
a loop iteration is in general unknown at compile time).

In the recursive definition of @{text ctyping2}, the equations dealing with conditional branches,
namely those applying to conditional statements and loops, construct the output @{typ "state set"}
and @{typ "vname set"} respectively as the \emph{union} and the \emph{intersection} of the sets
computed for each branch. In fact, a possible final state is any one resulting from either branch,
and a variable is finally determinate just in case it is such regardless of the branch being picked.
Yet, a ``dead'' branch should have no impact on the determinateness of variables, as it only depends
on the other branch. Accordingly, provided that information flow correctness checks are passed, the
cases where the output is constructed non-recursively, namely those of @{const SKIP}, assignments,
and loops, return @{const UNIV} as @{typ "vname set"} if the input @{typ "state set"} is empty. In
the case of a loop, the @{typ "state set"} and the @{typ "vname set"} resulting from one or more
iterations of its body are computed using the auxiliary type system @{const ctyping1}. This explains
why @{const ctyping1} returns @{const UNIV} as @{typ "vname set"} if the input @{typ "state set"} is
empty, as mentioned previously.

As happens with the syntax-directed security type system formalized in \<^cite>\<open>"Nipkow23-3"\<close>, the
cases performing non-recursive information flow correctness checks are those of assignments and
loops. In the former case, @{text ctyping2} verifies that the sets of variables contained in the
scope, as well as any variable occurring in the expression on the right-hand side of the assignment,
are allowed to interfere with the variable on the left-hand side, respectively in their associated
sets of states and in the input @{typ "state set"}. In the latter case, @{text ctyping2} verifies
that the sets of variables contained in the scope, as well as any variable occurring in the boolean
condition of the loop, are allowed to interfere with \emph{every} variable, respectively in their
associated sets of states and in the states in which the boolean condition is evaluated. In both
cases, if the applying interference relation is unknown as some state variable is indeterminate,
each of those checks must be passed for \emph{any} possible state (unless the respective set of
states is empty).

Why do the checks performed for loops test interference with \emph{every} variable? The answer is
provided by the following sample C program, which sets variables \lstinline{a} and \lstinline{b} to
the terms in the zero-based positions \lstinline{j} and \lstinline{j} + 1 of the Fibonacci sequence.

\null

\<^lstlisting>\<open>
a = 0;
b = 1;
for (i = 0; i != j; i++)
{
  c = b;
  b += a;
  a = c;
}
\<close>

\null

The loop in this program terminates for any nonnegative value of \lstinline{j}. For any variable
\lstinline{x}, suppose that \lstinline{j} is not allowed to interfere with \lstinline{x} in such an
initial state, say @{text s}. According to the above information flow correctness definition, any
initial state @{text t} differing from @{text s} in the value of \lstinline{j} must make execution
terminate all the same in order for the program to be correct. However, this is not the case, since
execution does not terminate for any negative value of \lstinline{j}. Thus, the type system needs to
verify that \lstinline{j} may interfere with \lstinline{x}, on pain of returning a wrong \emph{pass}
verdict.

The cases that change the scope upon recursively calling the type system are those of conditional
statements and loops. In the latter case, the boolean flag is set to @{const False}, and the set of
@{typ "state set \<times> vname set"} pairs is empty as the whole scope nesting the loop body, including
any variable occurring in the boolean condition of the loop, must be allowed to interfere with every
variable. In the former case, for both branches, the boolean flag is left unchanged, whereas the set
of pairs is extended with the pair composed of the input @{typ "state set"} (or of @{const UNIV} if
some state variable is indeterminate, unless the input @{typ "state set"} is empty) and of the set
of the variables, if any, occurring in the boolean condition of the statement.

Why is the scope extended with the whole input @{typ "state set"} for both branches, rather than
just with the set of states in which each single branch is selected? Once more, the question can be
answered by considering a sample C program, namely a previous one determining the minimum of two
integers \lstinline{a} and \lstinline{b} using a state variable \lstinline{i}. For the reader's
convenience, the program is reported here below.

\null

\<^lstlisting>\<open>
i = (a > b) ? 1 : 0;
if (i > 0)
{
  a = b;
}
\<close>

\null

Since the branch changing the value of variable \lstinline{a} is executed just in case \lstinline{i}
$=1$, suppose that in addition to \lstinline{b}, \lstinline{i} also is not allowed to interfere with
\lstinline{a} for \lstinline{i} $=0$, and let @{text s} be any initial state where \lstinline{a}
$\le$ \lstinline{b}. Based on the above information flow correctness definition, any initial state
@{text t} differing from @{text s} in the value of \lstinline{b} (not bound by the interference of
\lstinline{i} with \lstinline{a}) must produce the same final value of \lstinline{a} in order for
the program to be correct. However, this is not the case, as the final value of \lstinline{a} will
change for any state @{text t} where \lstinline{a} $>$ \lstinline{b}. Therefore, the type system
needs to verify that \lstinline{i} may interfere with \lstinline{a} for \lstinline{i} $=0$, too, on
pain of returning a wrong \emph{pass} verdict. This is the reason why, as mentioned previously, an
information flow correctness policy for this program should be such that @{prop "s: dom i \<leadsto> dom a"}
even for any state @{text s} where \lstinline{i} $=0$.

An even simpler example explains why, in the case of an assignment or a loop, the information flow
correctness checks described above need to be applied to the set of @{typ "state set \<times> vname set"}
pairs in the scope even if the input @{typ "state set"} is empty, namely even if the assignment or
the loop are nested in a ``dead'' branch. Here below is a sample C program showing this.

\null

\<^lstlisting>\<open>
if (i)
{
  a = 1;
}
\<close>

\null

Assuming that the initial value of \lstinline{i} is 0, the assignment nested within the conditional
statement is not executed, so that the final value of \lstinline{a} matches the initial one, say 0.
Suppose that \lstinline{i} is not allowed to interfere with \lstinline{a} in such an initial state,
say @{text s}. According to the above information flow correctness definition, any initial state
@{text t} differing from @{text s} in the value of \lstinline{i} must produce the same final value
of \lstinline{a} in order for the program to be correct. However, this is not the case, as the final
value of \lstinline{a} is 1 for any nonzero value of \lstinline{i}. Therefore, the type system needs
to verify that \lstinline{i} may interfere with \lstinline{a} in state @{text s} even though the
conditional branch is not executed in that state, on pain of returning a wrong \emph{pass} verdict.

\null
\<close>

abbreviation atyping :: "bool \<Rightarrow> aexp \<Rightarrow> vname set \<Rightarrow> bool"
  ("(_ \<Turnstile> _ '(\<subseteq> _'))" [51, 51] 50) where
"v \<Turnstile> a (\<subseteq> X) \<equiv> avars a = {} \<or> avars a \<subseteq> state \<inter> X \<and> v"

definition univ_states_if :: "state set \<Rightarrow> vname set \<Rightarrow> state set"
  ("(Univ? _ _)" [51, 75] 75) where
"Univ? A X \<equiv> if state \<subseteq> X then A else Univ A (\<subseteq> {})"


fun ctyping2 :: "scope \<Rightarrow> com \<Rightarrow> state set \<Rightarrow> vname set \<Rightarrow> config option"
  ("(_ \<Turnstile> _ '(\<subseteq> _, _'))" [51, 51] 55) where

"_ \<Turnstile> SKIP (\<subseteq> A, X) = Some (A, Univ?? A X)" |

"(U, v) \<Turnstile> x ::= a (\<subseteq> A, X) =
 (if (\<forall>(B, Y) \<in> insert (Univ? A X, avars a) U. B: dom ` Y \<leadsto> {dom x})
  then Some (if x \<in> state \<and> A \<noteq> {}
    then if v \<Turnstile> a (\<subseteq> X)
      then ({s(x := aval a s) | s. s \<in> A}, insert x X) else (A, X - {x})
    else (A, Univ?? A X))
  else None)" |

"(U, v) \<Turnstile> c\<^sub>1;; c\<^sub>2 (\<subseteq> A, X) =
 (case (U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) of
    Some (B, Y) \<Rightarrow> (U, v) \<Turnstile> c\<^sub>2 (\<subseteq> B, Y) | _ \<Rightarrow> None)" |

"(U, v) \<Turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X) =
 (case (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) of (U', B\<^sub>1, B\<^sub>2) \<Rightarrow>
    case ((U', v) \<Turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X), (U', v) \<Turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X)) of
      (Some (C\<^sub>1, Y\<^sub>1), Some (C\<^sub>2, Y\<^sub>2)) \<Rightarrow> Some (C\<^sub>1 \<union> C\<^sub>2, Y\<^sub>1 \<inter> Y\<^sub>2) |
      _ \<Rightarrow> None)" |

"(U, v) \<Turnstile> WHILE b DO c (\<subseteq> A, X) = (case \<Turnstile> b (\<subseteq> A, X) of (B\<^sub>1, B\<^sub>2) \<Rightarrow>
  case \<turnstile> c (\<subseteq> B\<^sub>1, X) of (C, Y) \<Rightarrow> case \<Turnstile> b (\<subseteq> C, Y) of (B\<^sub>1', B\<^sub>2') \<Rightarrow>
    if \<forall>(B, W) \<in> insert (Univ? A X \<union> Univ? C Y, bvars b) U.
      B: dom ` W \<leadsto> UNIV
    then case (({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1, X), ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1', Y)) of
      (Some _, Some _) \<Rightarrow> Some (B\<^sub>2 \<union> B\<^sub>2', Univ?? B\<^sub>2 X \<inter> Y) |
      _ \<Rightarrow> None
    else None)"

end

end
