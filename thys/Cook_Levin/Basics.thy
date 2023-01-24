chapter \<open>Introduction\<close>

text \<open>
The Cook-Levin theorem states that the problem \SAT{} of deciding the
satisfiability of Boolean formulas in conjunctive normal form is
$\NP$-complete~\cite{Cook,Levin}. This article formalizes a proof of this
theorem based on the textbook \emph{Computational Complexity:\ A Modern
Approach} by Arora and Barak~\cite{ccama}.
\<close>

section \<open>Outline\<close>

text \<open>
We start out in Chapter~\ref{s:TM} with a definition of multi-tape Turing
machines (TMs) slightly modified from Arora and Barak's definition. The
remainder of the chapter is devoted to constructing ever more complex machines
for arithmetic on binary numbers, evaluating polynomials, and performing basic
operations on lists of numbers and even lists of lists of numbers.

Specifying Turing machines and proving their correctness and running time is
laborious at the best of times. We slightly alleviate the seemingly inevitable
tedium of this by defining elementary reusable Turing machines and introducing
ways of composing them sequentially as well as in if-then-else branches and
while loops. Together with the representation of natural numbers and lists, we
thus get something faintly resembling a structured programming language of
sorts.

In Chapter~\ref{s:TC} we introduce some basic concepts of complexity theory,
such as $\mathcal{P}$, $\NP$, and polynomial-time many-one reduction.  Following
Arora and Barak the complexity class $\NP$ is defined via verifier Turing
machines rather than nondeterministic machines, and so the deterministic TMs
introduced in the previous chapter suffice for all definitions. To flesh out the
chapter a little we formalize obvious proofs of $\mathcal{P} \subseteq \NP$ and
the transitivity of the reducibility relation, although neither result is needed
for proving the Cook-Levin theorem.

Chapter~\ref{s:Sat} introduces the problem \SAT{} as a language over bit
strings. Boolean formulas in conjunctive normal form (CNF) are represented as
lists of clauses, each consisting of a list of literals encoded in binary numbers.
The list of lists of numbers ``data type'' defined in Chapter~\ref{s:TM} will
come in handy at this point.

The proof of the Cook-Levin theorem has two parts: Showing that \SAT{} is in
$\NP$ and showing that \SAT{} is $\NP$-hard, that is, that every language in
$\NP$ can be reduced to \SAT{} in polynomial time. The first part, also proved
in Chapter~\ref{s:Sat}, is fairly easy: For a satisfiable CNF formula, a
satisfying assignment can be given in roughly the size of the formula, because
only the variables in the formula need be assigned a truth value.  Moreover
whether an assignment satisfies a CNF formula can be verified easily.

The hard part is showing the $\NP$-hardness of \SAT{}. The first step
(Chapter~\ref{s:oblivious}) is to show that every polynomial-time computation on
a multi-tape TM can be performed in polynomial time on a two-tape
\emph{oblivious} TM.  Oblivious means that the sequence of positions of the
Turing machine's tape heads depends only on the \emph{length} of the input.
Thus any language in $\NP$ has a polynomial-time two-tape oblivious verifier TM.
In Chapter~\ref{s:Reducing} the proof goes on to show how the computations of
such a machine can be mapped to CNF formulas such that a CNF formula is
satisfiable if and only if the underlying computation was for a string in the
language \SAT{} paired with a certificate. Finally in Chapter~\ref{s:Aux_TM} and
Chapter~\ref{s:Red_TM} we construct a Turing machine that carries out the
reduction in polynomial time.
\<close>


section \<open>Related work\<close>

text \<open>
The Cook-Levin theorem has been formalized before. Gamboa and
Cowles~\cite{Gamboa2004AMP} present a formalization in ACL2~\cite{acl2}.  They
formalize $\NP$ and reducibility in terms of Turing machines, but analyze the
running time of the reduction from $\NP$-languages to \SAT{} in a
different, somewhat ad-hoc, model of computation that they call ``the major
weakness'' of their formalization.

Employing Coq~\cite{coq}, Gäher and Kunze~\cite{Gher2021MechanisingCT} define
$\NP$ and reducibility in the computational model ``call-by-value
$\lambda$-calculus L'' introduced by Forster and
Smolka~\cite{Forster2017WeakCL}. They show the $\NP$-completeness of \SAT{} in
this framework. Turing machines appear in an intermediate problem in the chain
of reductions from $\NP$ languages to \SAT{}, but are not used to show the
polynomiality of the reduction. Nevertheless, this is likely the first
formalization of the Cook-Levin theorem where both the complexity theoretic
concepts and the proof of the polynomiality of the reduction use the same model
of computation.

With regards to Isabelle, Xu~et al.~\cite{Universal_Turing_Machine-AFP} provide
a formalization of single-tape Turing machines with a fixed binary alphabet in
the computability theory setting and construct a universal TM.  While I was
putting the finishing touches on this article, Dalvit and
Thiemann~\cite{Multitape_To_Singletape_TM-AFP} published a formalization of
(deterministic and nondeterministic) multi-tape and single-tape Turing machines
and showed how to simulate the former on the latter with quadratic slowdown.
Moreover, Thiemann and Schmidinger~\cite{Multiset_Ordering_NPC-AFP} prove the
$\NP$-completeness of the Multiset Ordering problem, without, however, proving
the polynomial-time computability of the reduction.

This article uses Turing machines as model of computation for both the
complexity theoretic concepts and the running time analysis of the reduction. It
is thus most similar to Gäher and Kunze's work, but has a more elementary, if
not brute-force, flavor to it.
\<close>


section \<open>The core concepts\<close>

text \<open>
The proof of the Cook-Levin theorem awaits us in Section~\ref{s:complete} on the
very last page of this article. The way there is filled with definitions of
Turing machines, correctness proofs for Turing machines, and running time-bound
proofs for Turing machines, all of which can easily drown out the more relevant
concepts. For instance, for verifying that the theorem on the last page really
is the Cook-Levin theorem, only a small fraction of this article is relevant,
namely the definitions of $\NP$-completeness and of \SAT{}. Recursively breaking
down these definitions yields:

\begin{itemize}
  \item $\NP$-completeness: Section~\ref{s:TC-NP}
  \begin{itemize}
    \item languages: Section~\ref{s:TC-NP}
    \item $\NP$-hard: Section~\ref{s:TC-NP}
    \begin{itemize}
      \item $\NP$: Section~\ref{s:TC-NP}
      \begin{itemize}
        \item Turing machines: Section~\ref{s:tm-basic-tm}
        \item computing a function: Section~\ref{s:tm-basic-comp}
        \item pairing strings: Section~\ref{s:tm-basic-pair}
        \item Big-Oh, polynomial: Section~\ref{s:tm-basic-bigoh}
      \end{itemize}
      \item polynomial-time many-one reduction: Section~\ref{s:TC-NP}
    \end{itemize}
  \end{itemize}

  \item \SAT{}: Section~\ref{s:sat-sat-repr}
  \begin{itemize}
    \item literal, clause, CNF formula, assignment, satisfiability: Section~\ref{s:CNF}
    \item representing CNF formulas as strings: Section~\ref{s:sat-sat-repr}
    \begin{itemize}
      \item string: Section~\ref{s:tm-basic-tm}
      \item CNF formula: Section~\ref{s:CNF}
      \item mapping between symbols and strings: Section~\ref{s:tm-basic-comp}
      \item mapping between binary and quaternary alphabets: Section~\ref{s:tm-quaternary-encoding}
      \item lists of lists of natural numbers: Section~\ref{s:tm-numlistlist-repr}
      \begin{itemize}
        \item binary representation of natural numbers: Section~\ref{s:tm-arithmetic-binary}
        \item lists of natural numbers: Section~\ref{s:tm-numlist-repr}
      \end{itemize}
    \end{itemize}
  \end{itemize}
\end{itemize}

In other words the Sections~\ref{s:tm-basic}, \ref{s:tm-arithmetic-binary},
\ref{s:tm-numlist-repr}, \ref{s:tm-numlistlist-repr}, \ref{s:tm-quaternary-encoding},
\ref{s:TC-NP}, \ref{s:CNF}, and \ref{s:sat-sat-repr} cover all definitions for
formalizing the statement ``\SAT{} is $\NP$-complete''.
\<close>


chapter \<open>Turing machines\label{s:TM}\<close>

text \<open>
This chapter introduces Turing machines as a model of computing functions within
a running-time bound. Despite being quite intuitive, Turing machines are
notoriously tedious to work with. And so most of the rest of the chapter is
devoted to making this a little easier by providing means of combining TMs and a
library of reusable TMs for common tasks.

The basic idea (Sections~\ref{s:tm-basic} and~\ref{s:tm-trans}) is to treat
Turing machines as a kind of GOTO programming language. A state of a TM
corresponds to a line of code executing a rather complex command that, depending
on the symbols read, can write symbols, move tape heads, and jump to another
state (that is, line of code). States are identified by line numbers. This makes
it easy to execute TMs in sequence by concatenating two TM ``programs''. On top
of the GOTO implicit in all commands, we then define IF and WHILE in the
traditional way (Section~\ref{s:tm-combining}). This makes TMs more composable.

The interpretation of states as line numbers deprives TMs of the ability to
memorize values ``in states'', for example, the carry bit during a binary
addition. In Section~\ref{s:tm-memorizing} we recover some of this flexibility.

Being able to combine TMs is helpful, but we also need TMs to combine. This
takes up most of the remainder of the chapter. We start with simple operations,
such as moving a tape head to the next blank symbol or copying symbols between
tapes (Section~\ref{s:tm-elementary}). Extending our programming language
analogy for more complex TMs, we identify tapes with variables, so that a tape
contains a value of a specific type, such as a number or a list of numbers. In
the remaining Sections~\ref{s:tm-arithmetic} to~\ref{s:tm-wellformed} we define
these ``data types'' and devise TMs for operations over them.

It would be an exaggeration to say all this makes working with Turing machines
easy or fun. But at least it makes TMs somewhat more feasible to use for
complexity theory, as witnessed by the subsequent chapters.
\<close>


section \<open>Basic definitions\label{s:tm-basic}\<close>

theory Basics
  imports Main
begin

text \<open>
While Turing machines are fairly simple, there are still a few parts to define,
especially if one allows multiple tapes and an arbitrary alphabet: states, tapes
(read-only or read-write), cells, tape heads, head movements, symbols, and
configurations. Beyond these are more semantic aspects like executing one or
many steps of a Turing machine, its running time, and what it means for a TM to
``compute a function''. Our approach at formalizing all this must look rather
crude compared to Dalvit and Thiemann's~\cite{Multitape_To_Singletape_TM-AFP},
but still it does get the job done.

For lack of a better place, this section also introduces a minimal version of
Big-Oh, polynomials, and a pairing function for strings.
\<close>


subsection \<open>Multi-tape Turing machines\label{s:tm-basic-tm}\<close>

text \<open>
Arora and Barak~\cite[p.~11]{ccama} define multi-tape Turing machines with these
features:

\begin{itemize}
\item There are $k \geq 2$ infinite one-directional tapes, and each has one head.
\item The first tape is the input tape and read-only; the other $k - 1$ tapes
  can be written to.
\item The tape alphabet is a finite set $\Gamma$ containing at least the blank
  symbol $\Box$, the start symbol $\triangleright$, and the symbols \textbf{0}
  and \textbf{1}.
\item There is a finite set $Q$ of states with start state and halting state
  $q_\mathit{start}, q_\mathit{halt} \in Q$.
\item The behavior is described by a transition function $\delta\colon\ Q
  \times \Gamma^k \to Q \times \Gamma^{k-1} \times \{L, S, R\}^k$.  If the TM is
  in a state $q$ and the symbols $g_1,\dots,g_k$ are under the $k$ tape heads
  and $\delta(q, (g_1, \dots, g_k)) = (q', (g'_2, \dots, g'_k), (d_1, \dots,
  d_k))$, then the TM writes $g'_2, \dots, g'_k$ to the writable tapes, moves
  the tape heads in the direction (Left, Stay, or Right) indicated by the $d_1,
  \dots, d_k$ and switches to state $q'$.
\end{itemize}
\<close>


subsubsection \<open>Syntax\<close>

text \<open>
An obvious data type for the direction a tape head can move:
\<close>

datatype direction = Left | Stay | Right

text \<open>
We simplify the definition a bit in that we identify both symbols and states
with natural numbers:
\begin{itemize}
\item We set $\Gamma = \{0, 1, \dots, G - 1\}$ for some $G \geq 4$ and represent
  the symbols $\Box$, $\triangleright$, \textbf{0}, and \textbf{1} by the
  numbers 0, 1, 2, and~3, respectively. We represent an alphabet $\Gamma$ by its
  size $G$.
\item We let the set of states be of the form $\{0, 1, \dots, Q\}$ for some
  $Q\in\nat$ and set the start state $q_\mathit{start} = 0$ and halting state
  $q_\mathit{halt} = Q$.
\end{itemize}

The last item presents a fundamental difference to the textbook definition,
because it requires that Turing machines with $q_\mathit{start} =
q_\mathit{halt}$ have exactly one state, whereas the textbook definition allows
them arbitrarily many states.  However, if $q_\mathit{start} = q_\mathit{halt}$
then the TM starts in the halting state and thus does not actually do anything.
But then it does not matter if there are other states besides that one
start/halting state.  Our simplified definition therefore does not restrict the
expressive power of TMs. It does, however, simplify composing them.
\<close>

text \<open>
The type @{type nat} is used for symbols and for states.
\<close>

type_synonym state = nat

type_synonym symbol = nat

text \<open>
It is confusing to have the numbers 2 and 3 represent the symbols \textbf{0} and
\textbf{1}. The next abbreviations try to hide this somewhat. The glyphs for
symbols number~4 and~5 are chosen arbitrarily. While we will encounter Turing
machines with huge alphabets, only the following symbols will be used literally:
\<close>

abbreviation (input) blank_symbol :: nat ("\<box>") where "\<box> \<equiv> 0"
abbreviation (input) start_symbol :: nat ("\<triangleright>")   where "\<triangleright> \<equiv> 1"
abbreviation (input) zero_symbol :: nat ("\<zero>")   where "\<zero> \<equiv> 2"
abbreviation (input) one_symbol :: nat ("\<one>")    where "\<one> \<equiv> 3"
abbreviation (input) bar_symbol :: nat ("\<bar>")      where "\<bar> \<equiv> 4"
abbreviation (input) sharp_symbol :: nat ("\<sharp>")  where "\<sharp> \<equiv> 5"

no_notation abs ("\<bar>_\<bar>")

text \<open>
Tapes are infinite in one direction, so each cell can be addressed by a natural
number. Likewise the position of a tape head is a natural number. The contents
of a tape are represented by a mapping from cell numbers to symbols. A
\emph{tape} is a pair of tape contents and head position:
\<close>

type_synonym tape = "(nat \<Rightarrow> symbol) \<times> nat"

text \<open>
Our formalization of Turing machines begins with a data type representing a more
general concept, which we call \emph{machine}, and later adds a predicate to
define which machines are \emph{Turing} machines. In this generalization the
number $k$ of tapes is arbitrary, although machines with zero tapes are of
little interest. Also, all tapes are writable and the alphabet is not limited,
that is, $\Gamma = \nat$. The transition function becomes
$
  \delta\colon\ \{0, \dots, Q\} \times \nat^k \to \{0, \dots, Q\} \times \nat^k \times \{L,S,R\}^k
$
or, saving us one occurrence of~$k$,
$
  \delta\colon\ \{0, \dots, Q\} \times \nat^k \to \{0, \dots, Q\} \times (\nat \times \{L,S,R\})^k\;.
$

The transition function $\delta$ has a fixed behavior in the state $q_{halt} =
Q$ (namely making the machine do nothing). Hence $\delta$ needs to be specified
only for the $Q$ states $0, \dots, Q - 1$ and thus can be given as a sequence
$\delta_0, \dots, \delta_{Q-1}$ where each $\delta_q$ is a function
\begin{equation} \label{eq:wf}
  \delta_q\colon \nat^k \to \{0, \dots, Q\} \times (\nat \times \{L,S,R\})^k.
\end{equation}
Going one step further we allow the machine to jump to any state in $\nat$, and
we will treat any state $q \geq Q$ as a halting state. The $\delta_q$ are then
\begin{equation} \label{eq:proper}
  \delta_q\colon \nat^k \to \nat \times (\nat \times \{L,S,R\})^k.
\end{equation}
Finally we allow inputs and outputs of arbitrary length, turning the $\delta_q$
into
\[
  \delta_q\colon \nat^* \to \nat \times (\nat \times \{L,S,R\})^*.
\]
Such a $\delta_q$ will be called a \emph{command}, and the elements of $\nat
\times \{L,S,R\}$ will be called \emph{actions}. An action consists of writing a
symbol to a tape at the current tape head position and then moving the tape
head.
\<close>

type_synonym action = "symbol \<times> direction"

text \<open>
A command maps the list of symbols read from the tapes to a follow-up state and
a list of actions. It represents the machine's behavior in one state.
\<close>

type_synonym command = "symbol list \<Rightarrow> state \<times> action list"

text \<open>
Machines are then simply lists of commands. The $q$-th element of the list
represents the machine's behavior in state $q$. The halting state of a machine
$M$ is @{term "length M"}, but there is obviously no such element in the list.
\<close>

type_synonym machine = "command list"

text \<open>
Commands in this general form are too amorphous. We call a command
\emph{well-formed} for $k$ tapes and the state space $Q$ if on reading $k$
symbols it performs $k$ actions and jumps to a state in $\{0, \dots, Q\}$. A
well-formed command corresponds to (\ref{eq:wf}).
\<close>

definition wf_command :: "nat \<Rightarrow> nat \<Rightarrow> command \<Rightarrow> bool" where
  "wf_command k Q cmd \<equiv> \<forall>gs. length gs = k \<longrightarrow> length (snd (cmd gs)) = k \<and> fst (cmd gs) \<le> Q"

text \<open>
A well-formed command is a \emph{Turing command} for $k$ tapes and alphabet $G$
if it writes only symbols from $G$ when reading symbols from $G$ and does not
write to tape $0$; that is, it writes to tape $0$ the symbol it read from
tape~$0$.
\<close>

definition turing_command :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> command \<Rightarrow> bool" where
  "turing_command k Q G cmd \<equiv>
    wf_command k Q cmd \<and>
    (\<forall>gs. length gs = k \<longrightarrow>
      ((\<forall>i<k. gs ! i < G) \<longrightarrow> (\<forall>i<k. fst (snd (cmd gs) ! i) < G)) \<and>
       (k > 0 \<longrightarrow> fst (snd (cmd gs) ! 0) = gs ! 0))"

text \<open>
A \emph{Turing machine} is a machine with at least two tapes and four symbols
and only Turing commands.
\<close>

definition turing_machine :: "nat \<Rightarrow> nat \<Rightarrow> machine \<Rightarrow> bool" where
  "turing_machine k G M \<equiv> k \<ge> 2 \<and> G \<ge> 4 \<and> (\<forall>cmd\<in>set M. turing_command k (length M) G cmd)"


subsubsection \<open>Semantics\<close>

text \<open>
Next we define the semantics of machines. The state and the list of tapes make
up the \emph{configuration} of a machine. The semantics are given as functions
mapping configurations to follow-up configurations.
\<close>

type_synonym config = "state \<times> tape list"

text \<open>
We start with the semantics of a single command. An action affects a tape in the
following way. For the head movements we imagine the tapes having cell~0 at the
left and the cell indices growing rightward.
\<close>

fun act :: "action \<Rightarrow> tape \<Rightarrow> tape" where
  "act (w, m) tp =
    ((fst tp)(snd tp:=w),
     case m of Left \<Rightarrow> snd tp - 1 | Stay \<Rightarrow> snd tp | Right \<Rightarrow> snd tp + 1)"

text \<open>
Reading symbols from one tape, from all tapes, and from configurations:
\<close>

abbreviation tape_read :: "tape \<Rightarrow> symbol" ("|.|") where
  "|.| tp \<equiv> fst tp (snd tp)"

definition read :: "tape list \<Rightarrow> symbol list" where
  "read tps \<equiv> map tape_read tps"

abbreviation config_read :: "config \<Rightarrow> symbol list" where
  "config_read cfg \<equiv> read (snd cfg)"

text \<open>
The semantics of a command:
\<close>

definition sem :: "command \<Rightarrow> config \<Rightarrow> config" where
  "sem cmd cfg \<equiv>
    let (newstate, actions) = cmd (config_read cfg)
    in (newstate, map (\<lambda>(a, tp). act a tp) (zip actions (snd cfg)))"

text \<open>
The semantics of one step of a machine consist in the semantics of the command
corresponding to the state the machine is in. The following definition ensures
that the configuration does not change when it is in a halting state.
\<close>

definition exe :: "machine \<Rightarrow> config \<Rightarrow> config" where
  "exe M cfg \<equiv> if fst cfg < length M then sem (M ! (fst cfg)) cfg else cfg"

text \<open>
Executing a machine $M$ for multiple steps:
\<close>

fun execute :: "machine \<Rightarrow> config \<Rightarrow> nat \<Rightarrow> config" where
  "execute M cfg 0 = cfg" |
  "execute M cfg (Suc t) = exe M (execute M cfg t)"

text \<open>
We have defined the semantics for arbitrary machines, but most lemmas we are
going to prove about @{const exe}, @{const execute}, etc.\ will require the
commands to be somewhat well-behaved, more precisely to map lists of $k$ symbols
to lists of $k$ actions, as shown in (\ref{eq:proper}). We will call such
commands \emph{proper}.  \<close>

abbreviation proper_command :: "nat \<Rightarrow> command \<Rightarrow> bool" where
  "proper_command k cmd \<equiv> \<forall>gs. length gs = k \<longrightarrow> length (snd (cmd gs)) = length gs"

text \<open>
Being proper is a weaker condition than being well-formed. Since @{const exe}
treats the state $Q$ and the states $q > Q$ the same, we do not need the
$Q$-closure property of well-formedness for most lemmas about semantics.
\<close>

text \<open>
Next we introduce a number of abbreviations for components of a machine and
aspects of its behavior. In general, symbols between bars $|\cdot|$ represent
operations on tapes, inside angle brackets $<\cdot>$ operations on
configurations, between colons $:\!\cdot\!:$ operations on lists of tapes, and
inside brackets $[\cdot]$ operations on state/action-list pairs. As for the
symbol inside the delimiters, a dot ($.$) refers to a tape symbol, a colon ($:$)
to the entire tape contents, and a hash ($\#$) to a head position; an equals
sign ($=$) means some component of the left-hand side is changed. An exclamation
mark ($!$) accesses an element in a list on the left-hand side term.

\null
\<close>

abbreviation config_length :: "config \<Rightarrow> nat"  ("||_||") where
  "config_length cfg \<equiv> length (snd cfg)"

abbreviation tape_move_right :: "tape \<Rightarrow> nat \<Rightarrow> tape" (infixl "|+|" 60) where
  "tp |+| n \<equiv> (fst tp, snd tp + n)"

abbreviation tape_move_left :: "tape \<Rightarrow> nat \<Rightarrow> tape" (infixl "|-|" 60) where
  "tp |-| n \<equiv> (fst tp, snd tp - n)"

abbreviation tape_move_to :: "tape \<Rightarrow> nat \<Rightarrow> tape" (infixl "|#=|" 60) where
  "tp |#=| n \<equiv> (fst tp, n)"

abbreviation tape_write :: "tape \<Rightarrow> symbol \<Rightarrow> tape" (infixl "|:=|" 60) where
  "tp |:=| h \<equiv> ((fst tp) (snd tp := h), snd tp)"

abbreviation config_tape_by_no :: "config \<Rightarrow> nat \<Rightarrow> tape" (infix "<!>" 90) where
  "cfg <!> j \<equiv> snd cfg ! j"

abbreviation config_contents_by_no :: "config \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> symbol)" (infix "<:>" 100) where
  "cfg <:> j \<equiv> fst (cfg <!> j)"

abbreviation config_pos_by_no :: "config \<Rightarrow> nat \<Rightarrow> nat" (infix "<#>" 100) where
  "cfg <#> j \<equiv> snd (cfg <!> j)"

abbreviation config_symbol_read :: "config \<Rightarrow> nat \<Rightarrow> symbol" (infix "<.>" 100) where
  "cfg <.> j \<equiv> (cfg <:> j) (cfg <#> j)"

abbreviation config_update_state :: "config \<Rightarrow> nat \<Rightarrow> config" (infix "<+=>" 90) where
  "cfg <+=> q \<equiv> (fst cfg + q, snd cfg)"

abbreviation tapes_contents_by_no :: "tape list \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> symbol)" (infix ":::" 100) where
  "tps ::: j \<equiv> fst (tps ! j)"

abbreviation tapes_pos_by_no :: "tape list \<Rightarrow> nat \<Rightarrow> nat" (infix ":#:" 100) where
  "tps :#: j \<equiv> snd (tps ! j)"

abbreviation tapes_symbol_read :: "tape list \<Rightarrow> nat \<Rightarrow> symbol" (infix ":.:" 100) where
  "tps :.: j \<equiv> (tps ::: j) (tps :#: j)"

abbreviation jump_by_no :: "state \<times> action list \<Rightarrow> state" ("[*] _" [90]) where
  "[*] sas \<equiv> fst sas"

abbreviation actions_of_cmd :: "state \<times> action list \<Rightarrow> action list" ("[!!] _" [100] 100) where
  "[!!] sas \<equiv> snd sas"

abbreviation action_by_no :: "state \<times> action list \<Rightarrow> nat \<Rightarrow> action" (infix "[!]" 90) where
  "sas [!] j \<equiv> snd sas ! j"

abbreviation write_by_no :: "state \<times> action list \<Rightarrow> nat \<Rightarrow> symbol" (infix "[.]" 90) where
  "sas [.] j \<equiv> fst (sas [!] j)"

abbreviation direction_by_no :: "state \<times> action list \<Rightarrow> nat \<Rightarrow> direction" (infix "[~]" 100) where
  "sas [~] j \<equiv> snd (sas [!] j)"

text \<open>
Symbol sequences consisting of symbols from an alphabet $G$:
\<close>

abbreviation symbols_lt :: "nat \<Rightarrow> symbol list \<Rightarrow> bool" where
  "symbols_lt G rs \<equiv> \<forall>i<length rs. rs ! i < G"

text \<open>
We will frequently have to show that commands are proper or Turing commands.
\<close>

lemma turing_commandI [intro]:
  assumes "\<And>gs. length gs = k \<Longrightarrow> length ([!!] cmd gs) = length gs"
    and "\<And>gs. length gs = k \<Longrightarrow>  (\<And>i. i < length gs \<Longrightarrow> gs ! i < G) \<Longrightarrow> (\<And>j. j < length gs \<Longrightarrow> cmd gs [.] j < G)"
    and "\<And>gs. length gs = k \<Longrightarrow> k > 0 \<Longrightarrow> cmd gs [.] 0 = gs ! 0"
    and "\<And>gs. length gs = k \<Longrightarrow> [*] (cmd gs) \<le> Q"
  shows "turing_command k Q G cmd"
  using assms turing_command_def wf_command_def by simp

lemma turing_commandD:
  assumes "turing_command k Q G cmd" and "length gs = k"
  shows "length ([!!] cmd gs) = length gs"
    and "(\<And>i. i < length gs \<Longrightarrow> gs ! i < G) \<Longrightarrow> (\<And>j. j < length gs \<Longrightarrow> cmd gs [.] j < G)"
    and "k > 0 \<Longrightarrow> cmd gs [.] 0 = gs ! 0"
    and "\<And>gs. length gs = k \<Longrightarrow> [*] (cmd gs) \<le> Q"
  using assms turing_command_def wf_command_def by simp_all

lemma turing_command_mono:
  assumes "turing_command k Q G cmd" and "Q \<le> Q'"
  shows "turing_command k Q' G cmd"
  using turing_command_def wf_command_def assms by auto

lemma proper_command_length:
  assumes "proper_command k cmd" and "length gs = k"
  shows "length ([!!] cmd gs) = length gs"
  using assms by simp

abbreviation proper_machine :: "nat \<Rightarrow> machine \<Rightarrow> bool" where
  "proper_machine k M \<equiv> \<forall>i<length M. proper_command k (M ! i)"

lemma prop_list_append:
  assumes "\<forall>i<length M1. P (M1 ! i)"
    and "\<forall>i<length M2. P (M2 ! i)"
  shows "\<forall>i<length (M1 @ M2). P ((M1 @ M2) ! i)"
  using assms by (simp add: nth_append)

text \<open>
The empty Turing machine $[]$ is the one Turing machine where the start state is
the halting state, that is, $q_\mathit{start} = q_\mathit{halt} = Q = 0$. It is
a Turing machine for every $k \geq 2$ and $G \geq 4$:
\<close>

lemma Nil_tm: "G \<ge> 4 \<Longrightarrow> k \<ge> 2 \<Longrightarrow> turing_machine k G []"
  using turing_machine_def by simp

lemma turing_machineI [intro]:
  assumes "k \<ge> 2"
    and "G \<ge> 4"
    and "\<And>i. i < length M \<Longrightarrow> turing_command k (length M) G (M ! i)"
  shows "turing_machine k G M"
  unfolding turing_machine_def using assms by (metis in_set_conv_nth)

lemma turing_machineD:
  assumes "turing_machine k G M"
  shows "k \<ge> 2"
    and "G \<ge> 4"
    and "\<And>i. i < length M \<Longrightarrow> turing_command k (length M) G (M ! i)"
  using turing_machine_def assms by simp_all

text \<open>
A few lemmas about @{const act}, @{const read}, and @{const sem}:

\null
\<close>

lemma act: "act a tp =
  ((fst tp)(snd tp := fst a),
   case snd a of Left \<Rightarrow> snd tp - 1 | Stay \<Rightarrow> snd tp | Right \<Rightarrow> snd tp + 1)"
  by (metis act.simps prod.collapse)

lemma act_Stay: "j < length tps \<Longrightarrow> act (read tps ! j, Stay) (tps ! j) = tps ! j"
  by (simp add: read_def)

lemma act_Right: "j < length tps \<Longrightarrow> act (read tps ! j, Right) (tps ! j) = tps ! j |+| 1"
  by (simp add: read_def)

lemma act_Left: "j < length tps \<Longrightarrow> act (read tps ! j, Left) (tps ! j) = tps ! j |-| 1"
  by (simp add: read_def)

lemma act_Stay': "act (h, Stay) (tps ! j) = tps ! j |:=| h"
  by simp

lemma act_Right': "act (h, Right) (tps ! j) = tps ! j |:=| h |+| 1"
  by simp

lemma act_Left': "act (h, Left) (tps ! j) = tps ! j |:=| h |-| 1"
  by simp

lemma act_pos_le_Suc: "snd (act a (tps ! j)) \<le> Suc (snd (tps ! j))"
proof -
  obtain w m where "a = (w, m)"
    by fastforce
  then show "snd (act a (tps ! j)) \<le> Suc (snd (tps ! j))"
    using act_Left' act_Stay' act_Right' by (cases m) simp_all
qed

lemma act_changes_at_most_pos:
  assumes "i \<noteq> snd tp"
  shows "fst (act (h, mv) tp) i = fst tp i"
  by (simp add: assms)

lemma act_changes_at_most_pos':
  assumes "i \<noteq> snd tp"
  shows "fst (act a tp) i = fst tp i"
  by (simp add: assms act)

lemma read_length: "length (read tps) = length tps"
  using read_def by simp

lemma tapes_at_read: "j < length tps \<Longrightarrow> (q, tps) <.> j = read tps ! j"
  unfolding read_def by simp

lemma tapes_at_read': "j < length tps \<Longrightarrow> tps :.: j = read tps ! j"
  unfolding read_def by simp

lemma read_abbrev: "j < ||cfg|| \<Longrightarrow> read (snd cfg) ! j = cfg <.> j"
  unfolding read_def by simp

lemma sem:
  "sem cmd cfg =
    (let rs = read (snd cfg)
     in (fst (cmd rs), map (\<lambda>(a, tp). act a tp) (zip (snd (cmd rs)) (snd cfg))))"
  using sem_def read_def by (metis (no_types, lifting) case_prod_beta)

lemma sem':
  "sem cmd cfg =
    (fst (cmd (read (snd cfg))), map (\<lambda>(a, tp). act a tp) (zip (snd (cmd (read (snd cfg)))) (snd cfg)))"
  using sem_def read_def by (metis (no_types, lifting) case_prod_beta)

lemma sem'':
  "sem cmd (q, tps) =
    (fst (cmd (read tps)), map (\<lambda>(a, tp). act a tp) (zip (snd (cmd (read tps))) tps))"
  using sem' by simp

lemma sem_num_tapes_raw: "proper_command k cmd \<Longrightarrow> k = ||cfg|| \<Longrightarrow> k = ||sem cmd cfg||"
  using sem_def read_length by (simp add: case_prod_beta)

lemma sem_num_tapes2: "turing_command k Q G cmd \<Longrightarrow> k = ||cfg|| \<Longrightarrow> k = ||sem cmd cfg||"
  using sem_num_tapes_raw turing_commandD(1) by simp

corollary sem_num_tapes2': "turing_command ||cfg|| Q G cmd \<Longrightarrow> ||cfg|| = ||sem cmd cfg||"
  using sem_num_tapes2 by simp

corollary sem_num_tapes3: "turing_command ||cfg|| Q G cmd \<Longrightarrow> ||cfg|| = ||sem cmd cfg||"
  by (simp add: turing_commandD(1) sem_num_tapes_raw)

lemma sem_fst:
  assumes "cfg' = sem cmd cfg" and "rs = read (snd cfg)"
  shows "fst cfg' = fst (cmd rs)"
  using sem by (metis (no_types, lifting) assms(1) assms(2) fstI)

lemma sem_snd:
  assumes "proper_command k cmd"
    and "||cfg|| = k"
    and "rs = read (snd cfg)"
    and "j < k"
  shows "sem cmd cfg <!> j = act (snd (cmd rs) ! j) (snd cfg ! j)"
  using assms sem' read_length by simp

lemma snd_semI:
  assumes "proper_command k cmd"
    and "length tps = k"
    and "length tps' = k"
    and "\<And>j. j < k \<Longrightarrow> act (cmd (read tps) [!] j) (tps ! j) = tps' ! j"
  shows "snd (sem cmd (q, tps)) = snd (q', tps')"
  using assms sem_snd[OF assms(1)] sem_num_tapes_raw by (metis nth_equalityI snd_conv)

lemma sem_snd_tm:
  assumes "turing_machine k G M"
    and "length tps = k"
    and "rs = read tps"
    and "j < k"
    and "q < length M"
  shows "sem (M ! q) (q, tps) <!> j = act (snd ((M ! q) rs) ! j) (tps ! j)"
  using assms sem_snd turing_machine_def turing_commandD(1) by (metis nth_mem snd_conv)

lemma semI:
  assumes "proper_command k cmd"
    and "length tps = k"
    and "length tps' = k"
    and "fst (cmd (read tps)) = q'"
    and "\<And>j. j < k \<Longrightarrow> act (cmd (read tps) [!] j) (tps ! j) = tps' ! j"
  shows "sem cmd (q, tps) = (q', tps')"
  using snd_semI[OF assms(1,2,3)] assms(4,5) sem_fst by (metis prod.exhaust_sel snd_conv)

text \<open>
Commands ignore the state element of the configuration they are applied to.
\<close>

lemma sem_state_indep:
  assumes "snd cfg1 = snd cfg2"
  shows "sem cmd cfg1 = sem cmd cfg2"
  using sem_def assms by simp

text \<open>
A few lemmas about @{const exe} and @{const execute}:
\<close>

lemma exe_lt_length: "fst cfg < length M \<Longrightarrow> exe M cfg = sem (M ! (fst cfg)) cfg"
  using exe_def by simp

lemma exe_ge_length: "fst cfg \<ge> length M \<Longrightarrow> exe M cfg = cfg"
  using exe_def by simp

lemma exe_num_tapes:
  assumes "turing_machine k G M" and "k = ||cfg||"
  shows "k = ||exe M cfg||"
  using assms sem_num_tapes2 turing_machine_def exe_def by (metis nth_mem)

lemma exe_num_tapes_proper:
  assumes "proper_machine k M" and "k = ||cfg||"
  shows "k = ||exe M cfg||"
  using assms sem_num_tapes_raw turing_machine_def exe_def by metis

lemma execute_num_tapes_proper:
  assumes "proper_machine k M" and "k = ||cfg||"
  shows "k = ||execute M cfg t||"
  using exe_num_tapes_proper assms by (induction t) simp_all

lemma execute_num_tapes:
  assumes "turing_machine k G M" and "k = ||cfg||"
  shows "k = ||execute M cfg t||"
  using exe_num_tapes assms by (induction t) simp_all

lemma execute_after_halting:
  assumes "fst (execute M cfg0 t) = length M"
  shows "execute M cfg0 (t + n) = execute M cfg0 t"
  by (induction n) (simp_all add: assms exe_def)

lemma execute_after_halting':
  assumes "fst (execute M cfg0 t) \<ge> length M"
  shows "execute M cfg0 (t + n) = execute M cfg0 t"
  by (induction n) (simp_all add: assms exe_ge_length)

corollary execute_after_halting_ge:
  assumes "fst (execute M cfg0 t) = length M" and "t \<le> t'"
  shows "execute M cfg0 t' = execute M cfg0 t"
  using execute_after_halting assms le_Suc_ex by blast

corollary execute_after_halting_ge':
  assumes "fst (execute M cfg0 t) \<ge> length M" and "t \<le> t'"
  shows "execute M cfg0 t' = execute M cfg0 t"
  using execute_after_halting' assms le_Suc_ex by blast

lemma execute_additive:
  assumes "execute M cfg1 t1 = cfg2" and "execute M cfg2 t2 = cfg3"
  shows "execute M cfg1 (t1 + t2) = cfg3"
  using assms by (induction t2 arbitrary: cfg3) simp_all

lemma turing_machine_execute_states:
  assumes "turing_machine k G M" and "fst cfg \<le> length M" and "||cfg|| = k"
  shows "fst (execute M cfg t) \<le> length M"
proof (induction t)
  case 0
  then show ?case
    by (simp add: assms(2))
next
  case (Suc t)
  then show ?case
    using turing_command_def assms(1,3) exe_def execute.simps(2) execute_num_tapes sem_fst
      turing_machine_def wf_command_def read_length
    by (smt (verit, best) nth_mem)
qed

text \<open>
While running times are important, usually upper bounds for them suffice. The
next predicate expresses that a machine \emph{transits} from one configuration
to another one in at most a certain number of steps.
\<close>

definition transits :: "machine \<Rightarrow> config \<Rightarrow> nat \<Rightarrow> config \<Rightarrow> bool" where
  "transits M cfg1 t cfg2 \<equiv> \<exists>t'\<le>t. execute M cfg1 t' = cfg2"

lemma transits_monotone:
  assumes "t \<le> t'" and "transits M cfg1 t cfg2"
  shows "transits M cfg1 t' cfg2"
  using assms dual_order.trans transits_def by auto

lemma transits_additive:
  assumes "transits M cfg1 t1 cfg2" and "transits M cfg2 t2 cfg3"
  shows "transits M cfg1 (t1 + t2) cfg3"
proof-
  from assms(1) obtain t1' where 1: "t1' \<le> t1" "execute M cfg1 t1' = cfg2"
    using transits_def by auto
  from assms(2) obtain t2' where 2: "t2' \<le> t2" "execute M cfg2 t2' = cfg3"
    using transits_def by auto
  then have "execute M cfg1 (t1' + t2') = cfg3"
    using execute_additive 1 by simp
  moreover have "t1' + t2' \<le> t1 + t2"
    using "1"(1) "2"(1) by simp
  ultimately show ?thesis
    using transits_def "1"(2) "2"(2) by auto
qed

lemma transitsI:
  assumes "execute M cfg1 t' = cfg2" and "t' \<le> t"
  shows "transits M cfg1 t cfg2"
  unfolding transits_def using assms by auto

lemma execute_imp_transits:
  assumes "execute M cfg1 t = cfg2"
  shows "transits M cfg1 t cfg2"
  unfolding transits_def using assms by auto

text \<open>
In the vast majority of cases we are only interested in transitions from the
start state to the halting state. One way to look at it is the machine
\emph{transforms} a list of tapes to another list of tapes within a certain
number of steps.
\<close>

definition transforms :: "machine \<Rightarrow> tape list \<Rightarrow> nat \<Rightarrow> tape list \<Rightarrow> bool" where
  "transforms M tps t tps' \<equiv> transits M (0, tps) t (length M, tps')"

text \<open>
The previous predicate will be the standard way in which we express the
behavior of a (Turing) machine. Consider, for example, the empty machine:
\<close>

lemma transforms_Nil: "transforms [] tps 0 tps"
  using transforms_def transits_def by simp

lemma transforms_monotone:
  assumes "transforms M tps t tps'" and "t \<le> t'"
  shows "transforms M tps t' tps'"
  using assms transforms_def transits_monotone by simp

text \<open>
Most often the tapes will have a start symbol in the first cell followed by
a finite sequence of symbols.
\<close>

definition contents :: "symbol list \<Rightarrow> (nat \<Rightarrow> symbol)" ("\<lfloor>_\<rfloor>") where
  "\<lfloor>xs\<rfloor> i \<equiv> if i = 0 then \<triangleright> else if i \<le> length xs then xs ! (i - 1) else \<box>"

lemma contents_at_0 [simp]: "\<lfloor>zs\<rfloor> 0 = \<triangleright>"
  using contents_def by simp

lemma contents_inbounds [simp]: "i > 0 \<Longrightarrow> i \<le> length zs \<Longrightarrow> \<lfloor>zs\<rfloor> i = zs ! (i - 1)"
  using contents_def by simp

lemma contents_outofbounds [simp]: "i > length zs \<Longrightarrow> \<lfloor>zs\<rfloor> i = \<box>"
  using contents_def by simp

text \<open>
When Turing machines are used to compute functions, they are started in a
specific configuration where all tapes have the format just defined and the
first tape contains the input. This is called the \emph{start
configuration}~\cite[p.~13]{ccama}.
\<close>

definition start_config :: "nat \<Rightarrow> symbol list \<Rightarrow> config" where
  "start_config k xs \<equiv> (0, (\<lfloor>xs\<rfloor>, 0) # replicate (k - 1) (\<lfloor>[]\<rfloor>, 0))"

lemma start_config_length: "k > 0 \<Longrightarrow> ||start_config k xs|| = k"
  using start_config_def contents_def by simp

lemma start_config1:
  assumes "cfg = start_config k xs" and "0 < j" and "j < k" and "i > 0"
  shows "(cfg <:> j) i = \<box>"
  using start_config_def contents_def assms by simp

lemma start_config2:
  assumes "cfg = start_config k xs" and "j < k"
  shows "(cfg <:> j) 0  = \<triangleright>"
  using start_config_def contents_def assms by (cases "0 = j") simp_all

lemma start_config3:
  assumes "cfg = start_config k xs" and "i > 0" and "i \<le> length xs"
  shows "(cfg <:> 0) i = xs ! (i - 1)"
  using start_config_def contents_def assms by simp

lemma start_config4:
  assumes "0 < j" and "j < k"
  shows "snd (start_config k xs) ! j = (\<lambda>i. if i = 0 then \<triangleright> else \<box>, 0)"
  using start_config_def contents_def assms by auto

lemma start_config_pos: "j < k \<Longrightarrow> start_config k zs <#> j = 0"
  using start_config_def by (simp add: nth_Cons')

text \<open>
We call a symbol \emph{proper} if it is neither the blank symbol nor the
start symbol.
\<close>

abbreviation proper_symbols :: "symbol list \<Rightarrow> bool" where
  "proper_symbols xs \<equiv> \<forall>i<length xs. xs ! i > Suc 0"

lemma proper_symbols_append:
  assumes "proper_symbols xs" and "proper_symbols ys"
  shows "proper_symbols (xs @ ys)"
  using assms prop_list_append by (simp add: nth_append)

lemma proper_symbols_ne0: "proper_symbols xs \<Longrightarrow> \<forall>i<length xs. xs ! i \<noteq> \<box>"
  by auto

lemma proper_symbols_ne1: "proper_symbols xs \<Longrightarrow> \<forall>i<length xs. xs ! i \<noteq> \<triangleright>"
  by auto

text \<open>
We call the symbols \textbf{0} and \textbf{1} \emph{bit symbols}.
\<close>

abbreviation bit_symbols :: "nat list \<Rightarrow> bool" where
  "bit_symbols xs \<equiv> \<forall>i<length xs. xs ! i = \<zero> \<or> xs ! i = \<one>"

lemma bit_symbols_append:
  assumes "bit_symbols xs" and "bit_symbols ys"
  shows "bit_symbols (xs @ ys)"
  using assms prop_list_append by (simp add: nth_append)


subsubsection \<open>Basic facts about Turing machines\<close>

text \<open>
A Turing machine with alphabet $G$ started on a symbol sequence over $G$ will
only ever have symbols from $G$ on any of its tapes.
\<close>

lemma tape_alphabet:
  assumes "turing_machine k G M" and "symbols_lt G zs" and "j < k"
  shows "((execute M (start_config k zs) t) <:> j) i < G"
  using assms(3)
proof (induction t arbitrary: i j)
  case 0
  have "G \<ge> 2"
    using turing_machine_def assms(1) by simp
  then show ?case
    using start_config_def contents_def 0 assms(2) start_config1 start_config2
    by (smt One_nat_def Suc_1 Suc_lessD Suc_pred execute.simps(1)
      fst_conv lessI nat_less_le neq0_conv nth_Cons_0 snd_conv)
next
  case (Suc t)
  let ?cfg = "execute M (start_config k zs) t"
  have *: "execute M (start_config k zs) (Suc t) = exe M ?cfg"
    by simp
  show ?case
  proof (cases "fst ?cfg \<ge> length M")
    case True
    then have "execute M (start_config k zs) (Suc t) = ?cfg"
      using * exe_def by simp
    then show ?thesis
      using Suc by simp
  next
    case False
    then have **: "execute M (start_config k zs) (Suc t) = sem (M ! (fst ?cfg)) ?cfg"
      using * exe_def by simp
    let ?rs = "config_read ?cfg"
    let ?cmd = "M ! (fst ?cfg)"
    let ?sas = "?cmd ?rs"
    let ?cfg' = "sem ?cmd ?cfg"
    have "\<forall>j<length ?rs. ?rs ! j < G"
      using Suc assms(1) execute_num_tapes start_config_length read_abbrev read_length by auto
    moreover have len: "length ?rs = k"
      using assms(1) assms(3) execute_num_tapes start_config_def read_length by auto
    moreover have 2: "turing_command k (length M) G ?cmd"
      using assms(1) turing_machine_def False leI by simp
    ultimately have sas: "\<forall>j<length ?rs. ?sas [.] j < G"
      using turing_command_def by simp
    have "?cfg' <!> j = act (?sas [!] j) (?cfg <!> j)"
      using Suc.prems 2 len read_length sem_snd turing_commandD(1) by metis
    then have "?cfg' <:> j = (?cfg <:> j)(?cfg <#> j := ?sas [.] j)"
      using act by simp
    then have "(?cfg' <:> j) i < G"
      by (simp add: len Suc sas)
    then show ?thesis
      using ** by simp
  qed
qed

corollary read_alphabet:
  assumes "turing_machine k G M" and "symbols_lt G zs"
  shows "\<forall>i<k. config_read (execute M (start_config k zs) t) ! i < G"
  using assms tape_alphabet execute_num_tapes start_config_length read_abbrev
  by simp

corollary read_alphabet':
  assumes "turing_machine k G M" and "symbols_lt G zs"
  shows "symbols_lt G (config_read (execute M (start_config k zs) t))"
  using read_alphabet assms execute_num_tapes start_config_length read_length turing_machine_def
  by (metis neq0_conv not_numeral_le_zero)

corollary read_alphabet_set:
  assumes "turing_machine k G M" and "symbols_lt G zs"
  shows "\<forall>h\<in>set (config_read (execute M (start_config k zs) t)). h < G"
  using read_alphabet'[OF assms] by (metis in_set_conv_nth)

text \<open>
The contents of the input tape never change.
\<close>

lemma input_tape_constant:
  assumes "turing_machine k G M" and "k = ||cfg||"
  shows "execute M cfg t <:> 0 = execute M cfg 0 <:> 0"
proof (induction t)
  case 0
  then show ?case
    by simp
next
  case (Suc t)
  let ?cfg = "execute M cfg t"
  have 1: "execute M cfg (Suc t) = exe M ?cfg"
    by simp
  have 2: "length (read (snd ?cfg)) = k"
    using execute_num_tapes assms read_length by simp
  have k: "k > 0"
    using assms(1) turing_machine_def by simp
  show ?case
  proof (cases "fst ?cfg < length M")
    case True
    then have 3: "turing_command k (length M) G (M ! fst ?cfg)"
      using turing_machine_def assms(1) by simp
    then have "(M ! fst ?cfg) (read (snd ?cfg)) [.] 0 = read (snd ?cfg) ! 0"
      using turing_command_def 2 k by auto
    then have 4: "(M ! fst ?cfg) (read (snd ?cfg)) [.] 0 = ?cfg <.> 0"
      using 2 k read_abbrev read_length by auto
    have "execute M cfg (Suc t) <:> 0 = sem (M ! fst ?cfg) ?cfg <:> 0"
      using True exe_def by simp
    also have "... = fst (act (((M ! fst ?cfg) (read (snd ?cfg))) [!] 0) (?cfg <!> 0))"
      using sem_snd 2 3 k read_length turing_commandD(1) by metis
    also have "... = (?cfg <:> 0) ((?cfg <#> 0):=(((M ! fst ?cfg) (read (snd ?cfg))) [.] 0))"
      using act by simp
    also have "... = (?cfg <:> 0) ((?cfg <#> 0):=?cfg <.> 0)"
      using 4 by simp
    also have "... = ?cfg <:> 0"
      by simp
    finally have "execute M cfg (Suc t) <:> 0 = ?cfg <:> 0" .
    then show ?thesis
      using Suc by simp
  next
    case False
    then have "execute M cfg (Suc t) = ?cfg"
      using exe_def by simp
    then show ?thesis
      using Suc by simp
  qed
qed

text \<open>
A head position cannot be greater than the number of steps the machine has been
running.
\<close>

lemma head_pos_le_time:
  assumes "turing_machine k G M" and "j < k"
  shows "execute M (start_config k zs) t <#> j \<le> t"
proof (induction t)
  case 0
  have "0 < k"
    using assms(1) turing_machine_def by simp
  then have "execute M (start_config k zs) 0 <#> j = 0"
    using start_config_def assms(2) start_config_pos by simp
  then show ?case
    by simp
next
  case (Suc t)
  have *: "execute M (start_config k zs) (Suc t) = exe M (execute M (start_config k zs) t)"
      (is "_ = exe M ?cfg")
    by simp
  show ?case
  proof (cases "fst ?cfg = length M")
    case True
    then have "execute M (start_config k zs) (Suc t) = ?cfg"
      using * exe_def by simp
    then show ?thesis
      using Suc by simp
  next
    case False
    then have less: "fst ?cfg < length M"
      using assms(1) turing_machine_def
      by (simp add: start_config_def le_neq_implies_less turing_machine_execute_states)
    then have "exe M ?cfg = sem (M ! (fst ?cfg)) ?cfg"
      using exe_def by simp
    moreover have "proper_command k (M ! (fst ?cfg))"
      using assms(1) turing_commandD(1) less turing_machine_def nth_mem by blast
    ultimately have "exe M ?cfg <!> j = act (snd ((M ! (fst ?cfg)) (config_read ?cfg)) ! j) (?cfg <!> j)"
      using assms(1,2) execute_num_tapes start_config_length sem_snd by auto
    then have "exe M ?cfg <#> j \<le> Suc (?cfg <#> j)"
      using act_pos_le_Suc assms(1,2) execute_num_tapes start_config_length by auto
    then show ?thesis
      using * Suc.IH by simp
  qed
qed

lemma head_pos_le_halting_time:
  assumes "turing_machine k G M"
    and "fst (execute M (start_config k zs) T) = length M"
    and "j < k"
  shows "execute M (start_config k zs) t <#> j \<le> T"
  using assms execute_after_halting_ge[OF assms(2)] head_pos_le_time[OF assms(1,3)]
  by (metis nat_le_linear order_trans)

text \<open>
A tape cannot contain non-blank symbols at a position larger than the number of
steps the Turing machine has been running, except on the input tape.
\<close>

lemma blank_after_time:
  assumes "i > t" and "j < k" and "0 < j" and "turing_machine k G M"
  shows "(execute M (start_config k zs) t <:> j) i = \<box>"
  using assms(1)
proof (induction t)
  case 0
  have "execute M (start_config k zs) 0 = start_config k zs"
    by simp
  then show ?case
    using start_config1 assms turing_machine_def by simp
next
  case (Suc t)
  have "k \<ge> 2"
    using assms(2,3) by simp
  let ?icfg = "start_config k zs"
  have *: "execute M ?icfg (Suc t) = exe M (execute M ?icfg t)"
    by simp
  show ?case
  proof (cases "fst (execute M ?icfg t) \<ge> length M")
    case True
    then have "execute M ?icfg (Suc t) = execute M ?icfg t"
      using * exe_def by simp
    then show ?thesis
      using Suc by simp
  next
    case False
    then have "execute M ?icfg (Suc t) <:> j = sem (M ! (fst (execute M ?icfg t))) (execute M ?icfg t) <:> j"
        (is "_ = sem ?cmd ?cfg <:> j")
      using exe_lt_length * by simp
    also have "... = fst (map (\<lambda>(a, tp). act a tp) (zip (snd (?cmd (read (snd ?cfg)))) (snd ?cfg)) ! j)"
      using sem' by simp
    also have "... = fst (act (snd (?cmd (read (snd ?cfg))) ! j) (snd ?cfg ! j))"
      (is "_ = fst (act ?h (snd ?cfg ! j))")
    proof -
      have "||?cfg|| = k"
        using assms(2) execute_num_tapes[OF assms(4)] start_config_length turing_machine_def
        by simp
      moreover have "length (snd (?cmd (read (snd ?cfg)))) = k"
        using assms(4) execute_num_tapes[OF assms(4)] start_config_length turing_machine_def
          read_length False turing_command_def wf_command_def
        by simp
      ultimately show ?thesis
        using assms by simp
    qed
    finally have "execute M ?icfg (Suc t) <:> j = fst (act ?h (snd ?cfg ! j))" .
    moreover have "i \<noteq> ?cfg <#> j"
      using head_pos_le_time[OF assms(4,2)] Suc Suc_lessD leD by blast
    ultimately have "(execute M ?icfg (Suc t) <:> j) i = fst (?cfg <!> j) i"
      using act_changes_at_most_pos by (metis prod.collapse)
    then show ?thesis
      using Suc Suc_lessD by presburger
  qed
qed


subsection \<open>Computing a function\label{s:tm-basic-comp}\<close>

text \<open>
Turing machines are supposed to compute functions. The functions in question map
bit strings to bit strings. We model such strings as lists of Booleans and
denote the bits by @{text \<bbbO>} and @{text \<bbbI>}.
\<close>

type_synonym string = "bool list"

notation False ("\<bbbO>") and True ("\<bbbI>")

text \<open>
This keeps the more abstract level of computable functions separate from the
level of concrete implementations as Turing machines, which can use an arbitrary
alphabet. We use the term ``string'' only for bit strings, on which functions
operate, and the terms ``symbol sequence'' or ``symbols'' for the things written
on the tapes of Turing machines. We translate between the two levels in a
straightforward way:
\<close>

abbreviation string_to_symbols :: "string \<Rightarrow> symbol list" where
  "string_to_symbols x \<equiv> map (\<lambda>b. if b then \<one> else \<zero>) x"

abbreviation symbols_to_string :: "symbol list \<Rightarrow> string" where
  "symbols_to_string zs \<equiv> map (\<lambda>z. z = \<one>) zs"

proposition
  "string_to_symbols [\<bbbO>, \<bbbI>] = [\<zero>, \<one>]"
  "symbols_to_string [\<zero>, \<one>] = [\<bbbO>, \<bbbI>]"
  by simp_all

lemma bit_symbols_to_symbols:
  assumes "bit_symbols zs"
  shows "string_to_symbols (symbols_to_string zs) = zs"
  using assms by (intro nth_equalityI) auto

lemma symbols_to_string_to_symbols: "symbols_to_string (string_to_symbols x) = x"
  by (intro nth_equalityI) simp_all

lemma proper_symbols_to_symbols: "proper_symbols (string_to_symbols zs)"
  by simp

abbreviation string_to_contents :: "string \<Rightarrow> (nat \<Rightarrow> symbol)" where
  "string_to_contents x \<equiv>
    \<lambda>i. if i = 0 then \<triangleright> else if i \<le> length x then (if x ! (i - 1) then \<one> else \<zero>) else \<box>"

lemma contents_string_to_contents: "string_to_contents xs = \<lfloor>string_to_symbols xs\<rfloor>"
  using contents_def by auto

lemma bit_symbols_to_contents:
  assumes "bit_symbols ns"
  shows "\<lfloor>ns\<rfloor> = string_to_contents (symbols_to_string ns)"
  using assms bit_symbols_to_symbols contents_string_to_contents by simp

text \<open>
Definition~1.3 in the textbook~\cite{ccama} says that for a Turing machine $M$
to compute a function $f\colon\bbOI^*\to\bbOI^*$ on input $x$, ``it halts with
$f(x)$ written on its output tape.'' My initial interpretation of this phrase,
and the one formalized below, was that the output is written \emph{after} the
start symbol $\triangleright$ in the same fashion as the input is given on the
input tape. However after inspecting the Turing machine in Example~1.1, I now
believe the more likely meaning is that the output \emph{overwrites} the start
symbol, although Example~1.1 precedes Definition~1.3 and might not be subject to
it.

One advantage of the interpretation with start symbol intact is that the output
tape can then be used unchanged as the input of another Turing machine, a
property we exploit in Section~\ref{s:tm-composing}. Otherwise one would have to
find the start cell of the output tape and either copy the contents to another
tape with start symbol or shift the string to the right and restore the start
symbol.  One way to find the start cell is to move the tape head left while
``marking'' the cells until one reaches an already marked cell, which can only
happen when the head is in the start cell, where ``moving left'' does not
actually move the head. This process will take time linear in the length of the
output and thus will not change the asymptotic running time of the machine.
Therefore the choice of interpretation is purely one of convenience.

\null
\<close>

definition halts :: "machine \<Rightarrow> config \<Rightarrow> bool" where
  "halts M cfg \<equiv> \<exists>t. fst (execute M cfg t) = length M"

lemma halts_impl_le_length:
  assumes "halts M cfg"
  shows "fst (execute M cfg t) \<le> length M"
  using assms execute_after_halting_ge' halts_def by (metis linear)

definition running_time :: "machine \<Rightarrow> config \<Rightarrow> nat" where
  "running_time M cfg \<equiv> LEAST t. fst (execute M cfg t) = length M"

lemma running_timeD:
  assumes "running_time M cfg = t" and "halts M cfg"
  shows "fst (execute M cfg t) = length M"
    and "\<And>t'. t' < t \<Longrightarrow> fst (execute M cfg t') \<noteq> length M"
  using assms running_time_def halts_def
    not_less_Least[of _ "\<lambda>t. fst (execute M cfg t) = length M"]
    LeastI[of "\<lambda>t. fst (execute M cfg t) = length M"]
  by auto

definition halting_config :: "machine \<Rightarrow> config \<Rightarrow> config" where
  "halting_config M cfg \<equiv> execute M cfg (running_time M cfg)"

abbreviation start_config_string :: "nat \<Rightarrow> string \<Rightarrow> config" where
  "start_config_string k x \<equiv> start_config k (string_to_symbols x)"

text \<open>
Another, inconsequential, difference to the textbook definition is that we
designate the second tape, rather than the last tape, as the output tape. This
means that the indices for the input and output tape are fixed at~0 and~1,
respectively, regardless of the total number of tapes. Next is our definition of
a $k$-tape Turing machine $M$ computing a function $f$ in $T$-time:
\<close>

definition computes_in_time :: "nat \<Rightarrow> machine \<Rightarrow> (string \<Rightarrow> string) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "computes_in_time k M f T \<equiv> \<forall>x.
    halts M (start_config_string k x) \<and>
    running_time M (start_config_string k x) \<le> T (length x) \<and>
    halting_config M (start_config_string k x) <:> 1 = string_to_contents (f x)"

lemma computes_in_time_mono:
  assumes "computes_in_time k M f T" and "\<And>n. T n \<le> T' n"
  shows "computes_in_time k M f T'"
  using assms computes_in_time_def halts_def running_time_def halting_config_def execute_after_halting_ge
  by (meson dual_order.trans)

text \<open>
The definition of @{const computes_in_time} can be expressed with @{const
transforms} as well, which will be more convenient for us.
\<close>

lemma halting_config_execute:
  assumes "fst (execute M cfg t) = length M"
  shows "halting_config M cfg = execute M cfg t"
proof-
  have 1: "t \<ge> running_time M cfg"
    using assms running_time_def by (simp add: Least_le)
  then have "fst (halting_config M cfg) = length M"
    using assms LeastI[of "\<lambda>t. fst (execute M cfg t) = length M" t]
    by (simp add: halting_config_def running_time_def)
  then show ?thesis
    using execute_after_halting_ge 1 halting_config_def by metis
qed

lemma transforms_halting_config:
  assumes "transforms M tps t tps'"
  shows "halting_config M (0, tps) = (length M, tps')"
  using assms transforms_def halting_config_def halting_config_execute transits_def
  by (metis fst_eqD)

lemma computes_in_time_execute:
  assumes "computes_in_time k M f T"
  shows "execute M (start_config_string k x) (T (length x)) <:> 1 = string_to_contents (f x)"
proof -
  let ?t = "running_time M (start_config_string k x)"
  let ?cfg = "start_config_string k x"
  have "execute M ?cfg ?t = halting_config M ?cfg"
    using halting_config_def by simp
  then have "fst (execute M ?cfg ?t) = length M"
    using assms computes_in_time_def running_timeD(1) by blast
  moreover have "?t \<le> T (length x)"
    using computes_in_time_def assms by simp
  ultimately have "execute M ?cfg ?t = execute M ?cfg (T (length x)) "
    using execute_after_halting_ge by presburger
  moreover have "execute M ?cfg ?t <:> 1 = string_to_contents (f x)"
    using computes_in_time_def halting_config_execute assms halting_config_def by simp
  ultimately show ?thesis
    by simp
qed

lemma transforms_running_time:
  assumes "transforms M tps t tps'"
  shows "running_time M (0, tps) \<le> t"
  using running_time_def transforms_def transits_def
  by (smt Least_le[of _ t] assms execute_after_halting_ge fst_conv)

text \<open>
This is the alternative characterization of @{const computes_in_time}:
\<close>

lemma computes_in_time_alt:
  "computes_in_time k M f T =
    (\<forall>x. \<exists>tps.
      tps ::: 1 = string_to_contents (f x) \<and>
      transforms M (snd (start_config_string k x)) (T (length x)) tps)"
  (is "?lhs = ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
  proof
    fix x :: string
    let ?cfg = "start_config_string k x"
    assume "computes_in_time k M f T"
    then have
      1: "halts M ?cfg" and
      2: "running_time M ?cfg \<le> T (length x)" and
      3: "halting_config M ?cfg <:> 1 = string_to_contents (f x)"
      using computes_in_time_def by simp_all
    define cfg where "cfg = halting_config M ?cfg"
    then have "transits M ?cfg (T (length x)) cfg"
      using 2 halting_config_def transits_def by auto
    then have "transforms M (snd ?cfg) (T (length x)) (snd cfg)"
      using transits_def transforms_def start_config_def
      by (metis (no_types, lifting) "1" cfg_def halting_config_def prod.collapse running_timeD(1) snd_conv)
    moreover have "snd cfg ::: 1 = string_to_contents (f x)"
      using cfg_def 3 by simp
    ultimately show "\<exists>tps. tps ::: 1 = string_to_contents (f x) \<and>
        transforms M (snd (start_config_string k x)) (T (length x)) tps"
      by auto
  qed
  show "?rhs \<Longrightarrow> ?lhs"
    unfolding computes_in_time_def
  proof
    assume rhs: ?rhs
    fix x :: string
    let ?cfg = "start_config_string k x"
    obtain tps where tps:
      "tps ::: 1 = string_to_contents (f x)"
      "transforms M (snd ?cfg) (T (length x)) tps"
      using rhs by auto
    then have "transits M ?cfg (T (length x)) (length M, tps)"
      using transforms_def start_config_def by simp
    then have 1: "halts M ?cfg"
      using halts_def transits_def by (metis fst_eqD)
    moreover have 2: "running_time M ?cfg \<le> T (length x)"
      using tps(2) transforms_running_time start_config_def by simp
    moreover have 3: "halting_config M ?cfg <:> 1 = string_to_contents (f x)"
    proof -
      have "halting_config M ?cfg = (length M, tps)"
        using transforms_halting_config[OF tps(2)] start_config_def by simp
      then show ?thesis
        using tps(1) by simp
    qed
    ultimately show "halts M ?cfg \<and> running_time M ?cfg \<le> T (length x) \<and> halting_config M ?cfg <:> 1 = string_to_contents (f x)"
      by simp
  qed
qed

lemma computes_in_timeD:
  fixes x
  assumes "computes_in_time k M f T"
  shows "\<exists>tps. tps ::: 1 = string_to_contents (f x) \<and>
       transforms M (snd (start_config k (string_to_symbols x))) (T (length x)) tps"
  using assms computes_in_time_alt by simp

lemma computes_in_timeI [intro]:
  assumes "\<And>x. \<exists>tps. tps ::: 1 = string_to_contents (f x) \<and>
      transforms M (snd (start_config k (string_to_symbols x))) (T (length x)) tps"
  shows "computes_in_time k M f T"
  using assms computes_in_time_alt by simp

text \<open>
As an example, the function mapping every string to the empty string is
computable within any time bound by the empty Turing machine.
\<close>

lemma computes_Nil_empty:
  assumes "k \<ge> 2"
  shows "computes_in_time k [] (\<lambda>x. []) T"
proof
  fix x :: string
  let ?tps = "snd (start_config_string k x)"
  let ?f = "\<lambda>x. []"
  have "?tps ::: 1 = string_to_contents (?f x)"
    using start_config4 assms by auto
  moreover have "transforms [] ?tps (T (length x)) ?tps"
    using transforms_Nil transforms_monotone by blast
  ultimately show "\<exists>tps. tps ::: 1 = string_to_contents (?f x) \<and> transforms [] ?tps (T (length x)) tps"
    by auto
qed


subsection \<open>Pairing strings\label{s:tm-basic-pair}\<close>

text \<open>
In order to define the computability of functions with two arguments, we need a
way to encode a pair of strings as one string. The idea is to write the two
strings with a separator, for example,
$\bbbO\bbbI\bbbO\bbbO\#\bbbI\bbbI\bbbI\bbbO$ and then encode every symbol
$\bbbO, \bbbI, \#$ by two bits from $\bbOI$. We slightly deviate from Arora and
Barak's encoding~\cite[p.~2]{ccama} and map $\bbbO$ to $\bbbO\bbbO$, $\bbbI$ to
$\bbbO\bbbI$, and \# to $\bbbI\bbbI$, the idea being that the first bit
signals whether the second bit is to be taken literally or as a special
character. Our example turns into
$\bbbO\bbbO\bbbO\bbbI\bbbO\bbbO\bbbO\bbbO\bbbI\bbbI\bbbO\bbbI\bbbO\bbbI\bbbO\bbbI\bbbO\bbbO$.

\null
\<close>

abbreviation bitenc :: "string \<Rightarrow> string" where
  "bitenc x \<equiv> concat (map (\<lambda>h. [\<bbbO>, h]) x)"

definition string_pair :: "string \<Rightarrow> string \<Rightarrow> string" ("\<langle>_, _\<rangle>") where
  "\<langle>x, y\<rangle> \<equiv> bitenc x @ [\<bbbI>, \<bbbI>] @ bitenc y"

text \<open>
Our example:
\<close>

proposition "\<langle>[\<bbbO>, \<bbbI>, \<bbbO>, \<bbbO>], [\<bbbI>, \<bbbI>, \<bbbI>, \<bbbO>]\<rangle> = [\<bbbO>, \<bbbO>, \<bbbO>, \<bbbI>, \<bbbO>, \<bbbO>, \<bbbO>, \<bbbO>, \<bbbI>, \<bbbI>, \<bbbO>, \<bbbI>, \<bbbO>, \<bbbI>, \<bbbO>, \<bbbI>, \<bbbO>, \<bbbO>]"
  using string_pair_def by simp

lemma length_string_pair: "length \<langle>x, y\<rangle> = 2 * length x + 2 * length y + 2"
proof -
  have "length (concat (map (\<lambda>h. [\<bbbO>, h]) z)) = 2 * length z" for z
    by (induction z) simp_all
  then show ?thesis
    using string_pair_def by simp
qed

lemma length_bitenc: "length (bitenc z) = 2 * length z"
  by (induction z) simp_all

lemma bitenc_nth:
  assumes "i < length zs"
  shows "bitenc zs ! (2 * i) = \<bbbO>"
    and "bitenc zs ! (2 * i + 1) = zs ! i"
proof -
  let ?f = "\<lambda>h. [\<bbbO>, h]"
  let ?xs = "concat (map ?f zs)"

  have eqtake: "bitenc (take i zs) = take (2 * i) (bitenc zs)"
      if "i \<le> length zs" for i zs
  proof -
    have "take (2 * i) (bitenc zs) = take (2 * i) (bitenc (take i zs @ drop i zs))"
      by simp
    then have "take (2 * i) (bitenc zs) = take (2 * i) (bitenc (take i zs) @ (bitenc (drop i zs)))"
      by (metis concat_append map_append)
    then show ?thesis
      using length_bitenc that by simp
  qed

  have eqdrop: "bitenc (drop i zs) = drop (2 * i) (bitenc zs)"
      if "i < length zs" for i
  proof -
    have "drop (2 * i) (bitenc zs) = drop (2 * i) (bitenc (take i zs @ drop i zs))"
      by simp
    then have "drop (2 * i) (bitenc zs) = drop (2 * i) (bitenc (take i zs) @ bitenc (drop i zs))"
      by (metis concat_append map_append)
    then show ?thesis
      using length_bitenc that by simp
  qed

  have take2: "take 2 (drop (2 * i) (bitenc zs)) = ?f (zs ! i)" if "i < length zs" for i
  proof -
    have 1: "1 \<le> length (drop i zs)"
      using that by simp
    have "take 2 (drop (2*i) (bitenc zs)) = take 2 (bitenc (drop i zs))"
      using that eqdrop by simp
    also have "... = bitenc (take 1 (drop i zs))"
      using 1 eqtake by simp
    also have "... = bitenc [zs ! i]"
      using that by (metis Cons_nth_drop_Suc One_nat_def take0 take_Suc_Cons)
    also have "... = ?f (zs ! i)"
      by simp
    finally show ?thesis .
  qed

  show "bitenc zs ! (2 * i) = \<bbbO>"
  proof -
    have "bitenc zs ! (2 * i) = drop (2 * i) (bitenc zs) ! 0"
      using assms drop0 length_bitenc by simp
    also have "... = take 2 (drop (2 * i) (bitenc zs)) ! 0"
      using eqdrop by simp
    also have "... = ?f (zs ! i) ! 0"
      using assms take2 by simp
    also have "... = \<bbbO>"
      by simp
    finally show ?thesis .
  qed

  show "bitenc zs ! (2*i + 1) = zs ! i"
  proof -
    have "bitenc zs ! (2*i+1) = drop (2 * i) (bitenc zs) ! 1"
      using assms length_bitenc by simp
    also have "... = take 2 (drop (2*i) (bitenc zs)) ! 1"
      using eqdrop by simp
    also have "... = ?f (zs ! i) ! 1"
      using assms(1) take2 by simp
    also have "... = zs ! i"
      by simp
    finally show ?thesis .
  qed
qed

lemma string_pair_first_nth:
  assumes "i < length x"
  shows "\<langle>x, y\<rangle> ! (2 * i) = \<bbbO>"
    and "\<langle>x, y\<rangle> ! (2 * i + 1) = x ! i"
proof -
  have "\<langle>x, y\<rangle> ! (2*i) = concat (map (\<lambda>h. [\<bbbO>, h]) x) ! (2*i)"
    using string_pair_def length_bitenc by (simp add: assms nth_append)
  then show "\<langle>x, y\<rangle> ! (2 * i) = \<bbbO>"
    using bitenc_nth(1) assms by simp
  have "2 * i + 1 < 2 * length x"
    using assms by simp
  then have "\<langle>x, y\<rangle> ! (2*i+1) = concat (map (\<lambda>h. [\<bbbO>, h]) x) ! (2*i+1)"
    using string_pair_def length_bitenc[of x] assms nth_append
    by force
  then show "\<langle>x, y\<rangle> ! (2 * i + 1) = x ! i"
    using bitenc_nth(2) assms by simp
qed

lemma string_pair_sep_nth:
  shows "\<langle>x, y\<rangle> ! (2 * length x) = \<bbbI>"
    and "\<langle>x, y\<rangle> ! (2 * length x + 1) = \<bbbI>"
  using string_pair_def length_bitenc
  by (metis append_Cons nth_append_length) (simp add: length_bitenc nth_append string_pair_def)

lemma string_pair_second_nth:
  assumes "i < length y"
  shows "\<langle>x, y\<rangle> ! (2 * length x + 2 + 2 * i) = \<bbbO>"
    and "\<langle>x, y\<rangle> ! (2 * length x + 2 + 2 * i + 1) = y ! i"
proof -
  have "\<langle>x, y\<rangle> ! (2 * length x + 2 + 2*i) = concat (map (\<lambda>h. [\<bbbO>, h]) y) ! (2*i)"
    using string_pair_def length_bitenc by (simp add: assms nth_append)
  then show "\<langle>x, y\<rangle> ! (2 * length x + 2 + 2 * i) = \<bbbO>"
    using bitenc_nth(1) assms by simp
  have "2 * i + 1 < 2 * length y"
    using assms by simp
  then have "\<langle>x, y\<rangle> ! (2 * length x + 2 + 2*i+1) = concat (map (\<lambda>h. [\<bbbO>, h]) y) ! (2*i+1)"
    using string_pair_def length_bitenc[of x] assms nth_append
    by force
  then show "\<langle>x, y\<rangle> ! (2 * length x + 2 + 2 * i + 1) = y ! i"
    using bitenc_nth(2) assms by simp
qed

lemma string_pair_inj:
  assumes "\<langle>x1, y1\<rangle> = \<langle>x2, y2\<rangle>"
  shows "x1 = x2 \<and> y1 = y2"
proof
  show "x1 = x2"
  proof (rule ccontr)
    assume neq: "x1 \<noteq> x2"
    consider "length x1 = length x2" | "length x1 < length x2" | "length x1 > length x2"
      by linarith
    then show False
    proof (cases)
      case 1
      then obtain i where i: "i < length x1" "x1 ! i \<noteq> x2 ! i"
        using neq list_eq_iff_nth_eq by blast
      then have "\<langle>x1, y1\<rangle> ! (2 * i + 1) = x1 ! i" and "\<langle>x2, y2\<rangle> ! (2 * i + 1) = x2 ! i"
        using 1 string_pair_first_nth by simp_all
      then show False
        using assms i(2) by simp
    next
      case 2
      let ?i = "length x1"
      have "\<langle>x1, y1\<rangle> ! (2 * ?i) = \<bbbI>"
        using string_pair_sep_nth by simp
      moreover have "\<langle>x2, y2\<rangle> ! (2 * ?i) = \<bbbO>"
        using string_pair_first_nth 2 by simp
      ultimately show False
        using assms by simp
    next
      case 3
      let ?i = "length x2"
      have "\<langle>x2, y2\<rangle> ! (2 * ?i) = \<bbbI>"
        using string_pair_sep_nth by simp
      moreover have "\<langle>x1, y1\<rangle> ! (2 * ?i) = \<bbbO>"
        using string_pair_first_nth 3 by simp
      ultimately show False
        using assms by simp
    qed
  qed
  then have len_x_eq: "length x1 = length x2"
    by simp
  then have len_y_eq: "length y1 = length y2"
    using assms length_string_pair
    by (smt (verit) Suc_1 Suc_mult_cancel1 add_left_imp_eq add_right_cancel)
  show "y1 = y2"
  proof (rule ccontr)
    assume neq: "y1 \<noteq> y2"
    then obtain i where i: "i < length y1" "y1 ! i \<noteq> y2 ! i"
      using list_eq_iff_nth_eq len_y_eq by blast
    then have "\<langle>x1, y1\<rangle> ! (2 * length x1 + 2 + 2 * i + 1) = y1 ! i" and
        "\<langle>x2, y2\<rangle> ! (2 * length x2 + 2 + 2 * i + 1) = y2 ! i"
      using string_pair_second_nth len_y_eq by simp_all
    then show False
      using assms i(2) len_x_eq by simp
  qed
qed

text \<open>
Turing machines have to deal with pairs of symbol sequences rather than strings.
\<close>

abbreviation pair :: "string \<Rightarrow> string \<Rightarrow> symbol list" ("\<langle>_; _\<rangle>") where
  "\<langle>x; y\<rangle> \<equiv> string_to_symbols \<langle>x, y\<rangle>"

lemma symbols_lt_pair: "symbols_lt 4 \<langle>x; y\<rangle>"
  by simp

lemma length_pair: "length \<langle>x; y\<rangle> = 2 * length x + 2 * length y + 2"
  by (simp add: length_string_pair)

lemma pair_inj:
  assumes "\<langle>x1; y1\<rangle> = \<langle>x2; y2\<rangle>"
  shows "x1 = x2 \<and> y1 = y2"
  using string_pair_inj assms symbols_to_string_to_symbols by metis


subsection \<open>Big-Oh and polynomials\label{s:tm-basic-bigoh}\<close>

text \<open>
The Big-Oh notation is standard~\cite[Definition~0.2]{ccama}. It can be defined
with $c$ ranging over real or natural numbers. We choose natural numbers for
simplicity.
\<close>

definition big_oh :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "big_oh g f \<equiv> \<exists>c m. \<forall>n>m. g n \<le> c * f n"

text \<open>
Some examples:
\<close>

proposition "big_oh (\<lambda>n. n) (\<lambda>n. n)"
  using big_oh_def by auto

proposition "big_oh (\<lambda>n. n) (\<lambda>n. n * n)"
  using big_oh_def by auto

proposition "big_oh (\<lambda>n. 42 * n) (\<lambda>n. n * n)"
proof-
  have "\<forall>n>0::nat. 42 * n \<le> 42 * n * n"
    by simp
  then have "\<exists>(c::nat)>0. \<forall>n>0. 42 * n \<le> c * n * n"
    using zero_less_numeral by blast
  then show ?thesis
    using big_oh_def by auto
qed

proposition "\<not> big_oh (\<lambda>n. n * n) (\<lambda>n. n)" (is "\<not> big_oh ?g ?f")
proof
  assume "big_oh (\<lambda>n. n * n) (\<lambda>n. n)"
  then obtain c m where "\<forall>n>m. ?g n \<le> c * ?f n"
    using big_oh_def by auto
  then have 1: "\<forall>n>m. n * n \<le> c * n"
    by auto
  define nn where "nn = max (m + 1) (c + 1)"
  then have 2: "nn > m"
    by simp
  then have "nn * nn > c * nn"
    by (simp add: nn_def max_def)
  with 1 2 show False
    using not_le by blast
qed

text \<open>
Some lemmas helping with polynomial upper bounds.
\<close>

lemma pow_mono:
  fixes n d1 d2 :: nat
  assumes "d1 \<le> d2" and "n > 0"
  shows "n ^ d1 \<le> n ^ d2"
  using assms by (simp add: Suc_leI power_increasing)

lemma pow_mono':
  fixes n d1 d2 :: nat
  assumes "d1 \<le> d2" and "0 < d1"
  shows "n ^ d1 \<le> n ^ d2"
  using assms by (metis dual_order.eq_iff less_le_trans neq0_conv pow_mono power_eq_0_iff)

lemma linear_le_pow:
  fixes n d1 :: nat
  assumes "0 < d1"
  shows "n \<le> n ^ d1"
  using assms by (metis One_nat_def gr_implies_not0 le_less_linear less_Suc0 self_le_power)

text \<open>
The next definition formalizes the phrase ``polynomially bounded'' and the term
``polynomial'' in ``polynomial running-time''. This is often written ``$f(n) =
n^{O(1)}$'' (for example, Arora and Barak~\cite[Example 0.3]{ccama}).
\<close>

definition big_oh_poly :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "big_oh_poly f \<equiv> \<exists>d. big_oh f (\<lambda>n. n ^ d)"

lemma big_oh_poly: "big_oh_poly f \<longleftrightarrow> (\<exists>d c n\<^sub>0. \<forall>n>n\<^sub>0. f n \<le> c * n ^ d)"
  using big_oh_def big_oh_poly_def by auto

lemma big_oh_polyI:
  assumes "\<And>n. n > n\<^sub>0 \<Longrightarrow> f n \<le> c * n ^ d"
  shows "big_oh_poly f"
  using assms big_oh_poly by auto

lemma big_oh_poly_const: "big_oh_poly (\<lambda>n. c)"
proof -
  let ?c = "max 1 c"
  have "(\<lambda>n. c) n \<le> ?c * n ^ 1" if "n > 0" for n
  proof -
    have "c \<le> n * ?c"
      by (metis (no_types) le_square max.cobounded2 mult.assoc mult_le_mono nat_mult_le_cancel_disj that)
    then show ?thesis
      by (simp add: mult.commute)
  qed
  then show ?thesis
    using big_oh_polyI[of 0 _ ?c] by simp
qed

lemma big_oh_poly_poly: "big_oh_poly (\<lambda>n. n ^ d)"
  using big_oh_polyI[of 0 _ 1 d] by simp

lemma big_oh_poly_id: "big_oh_poly (\<lambda>n. n)"
  using big_oh_poly_poly[of 1] by simp

lemma big_oh_poly_le:
  assumes "big_oh_poly f" and "\<And>n. g n \<le> f n"
  shows "big_oh_poly g"
  using assms big_oh_polyI by (metis big_oh_poly le_trans)

lemma big_oh_poly_sum:
  assumes "big_oh_poly f1" and "big_oh_poly f2"
  shows "big_oh_poly (\<lambda>n. f1 n + f2 n)"
proof-
  obtain d1 c1 m1 where 1: "\<forall>n>m1. f1 n \<le> c1 * n ^ d1"
    using big_oh_poly assms(1) by blast
  obtain d2 c2 m2 where 2: "\<forall>n>m2. f2 n \<le> c2 * n ^ d2"
    using big_oh_poly assms(2) by blast
  let ?f3 = "\<lambda>n. f1 n + f2 n"
  let ?c3 = "max c1 c2"
  let ?m3 = "max m1 m2"
  let ?d3 = "max d1 d2"
  have "\<forall>n>?m3. f1 n \<le> ?c3 * n ^ d1"
    using 1 by (simp add: max.coboundedI1 nat_mult_max_left)
  moreover have "\<forall>n>?m3. n ^ d1 \<le> n^?d3"
    using pow_mono by simp
  ultimately have *: "\<forall>n>?m3. f1 n \<le> ?c3 * n^?d3"
    using order_subst1 by fastforce
  have "\<forall>n>?m3. f2 n \<le> ?c3 * n ^ d2"
    using 2 by (simp add: max.coboundedI2 nat_mult_max_left)
  moreover have "\<forall>n>?m3. n ^ d2 \<le> n ^ ?d3"
    using pow_mono by simp
  ultimately have "\<forall>n>?m3. f2 n \<le> ?c3 * n ^ ?d3"
    using order_subst1 by fastforce
  then have "\<forall>n>?m3. f1 n + f2 n \<le> ?c3 * n ^ ?d3 + ?c3 * n ^ ?d3"
    using * by fastforce
  then have "\<forall>n>?m3. f1 n + f2 n \<le> 2 * ?c3 * n ^ ?d3"
    by auto
  then have "\<exists>d c m. \<forall>n>m. ?f3 n \<le> c * n ^ d"
    by blast
  then show ?thesis
    using big_oh_poly by simp
qed

lemma big_oh_poly_prod:
  assumes "big_oh_poly f1" and "big_oh_poly f2"
  shows "big_oh_poly (\<lambda>n. f1 n * f2 n)"
proof-
  obtain d1 c1 m1 where 1: "\<forall>n>m1. f1 n \<le> c1 * n ^ d1"
    using big_oh_poly assms(1) by blast
  obtain d2 c2 m2 where 2: "\<forall>n>m2. f2 n \<le> c2 * n ^ d2"
    using big_oh_poly assms(2) by blast
  let ?f3 = "\<lambda>n. f1 n * f2 n"
  let ?c3 = "max c1 c2"
  let ?m3 = "max m1 m2"
  have "\<forall>n>?m3. f1 n \<le> ?c3 * n ^ d1"
    using 1 by (simp add: max.coboundedI1 nat_mult_max_left)
  moreover have "\<forall>n>?m3. n ^ d1 \<le> n ^ d1"
    using pow_mono by simp
  ultimately have *: "\<forall>n>?m3. f1 n \<le> ?c3 * n ^ d1"
    using order_subst1 by fastforce
  have "\<forall>n>?m3. f2 n \<le> ?c3 * n ^ d2"
    using 2 by (simp add: max.coboundedI2 nat_mult_max_left)
  moreover have "\<forall>n>?m3. n ^ d2 \<le> n ^ d2"
    using pow_mono by simp
  ultimately have "\<forall>n>?m3. f2 n \<le> ?c3 * n ^ d2"
    using order_subst1 by fastforce
  then have "\<forall>n>?m3. f1 n * f2 n \<le> ?c3 * n ^ d1 * ?c3 * n ^ d2"
    using * mult_le_mono by (metis mult.assoc)
  then have "\<forall>n>?m3. f1 n * f2 n \<le> ?c3 * ?c3 * n ^ d1 * n ^ d2"
    by (simp add: semiring_normalization_rules(16))
  then have "\<forall>n>?m3. f1 n * f2 n \<le> ?c3 * ?c3 * n ^ (d1 + d2)"
    by (simp add: mult.assoc power_add)
  then have "\<exists>d c m. \<forall>n>m. ?f3 n \<le> c * n ^ d"
    by blast
  then show ?thesis
    using big_oh_poly by simp
qed

lemma big_oh_poly_offset:
  assumes "big_oh_poly f"
  shows "\<exists>b c d. d > 0 \<and> (\<forall>n. f n \<le> b + c * n ^ d)"
proof -
  obtain d c m where dcm: "\<forall>n>m. f n \<le> c * n ^ d"
    using assms big_oh_poly by auto
  have *: "f n \<le> c * n ^ Suc d" if "n > m" for n
  proof -
    have "n > 0"
      using that by simp
    then have "n ^ d \<le> n ^ Suc d"
      by simp
    then have "c * n ^ d \<le> c * n ^ Suc d"
      by simp
    then show "f n \<le> c * n ^ Suc d"
      using dcm order_trans that by blast
  qed
  define b :: nat where "b = Max {f n | n. n \<le> m}"
  then have "y \<le> b" if "y \<in> {f n | n. n \<le> m}" for y
    using that by simp
  then have "f n \<le> b" if "n \<le> m" for n
    using that by auto
  then have "f n \<le> b + c * n ^ Suc d" for n
    using * by (meson trans_le_add1 trans_le_add2 verit_comp_simplify1(3))
  then show ?thesis
    using * dcm(1) by blast
qed

lemma big_oh_poly_composition:
  assumes "big_oh_poly f1" and "big_oh_poly f2"
  shows "big_oh_poly (f2 \<circ> f1)"
proof-
  obtain d1 c1 m1 where 1: "\<forall>n>m1. f1 n \<le> c1 * n ^ d1"
    using big_oh_poly assms(1) by blast
  obtain d2 c2 b where 2: "\<forall>n. f2 n \<le> b + c2 * n ^ d2"
    using big_oh_poly_offset assms(2) by blast
  define c where "c = c2 * c1 ^ d2"
  have 3: "\<forall>n>m1. f1 n \<le> c1 * n ^ d1"
    using 1 by simp
  have "\<forall>n>m1. f2 n \<le> b + c2 * n ^ d2"
    using 2 by simp
  { fix n
    assume "n > m1"
    then have 4: "(f1 n) ^ d2 \<le> (c1 * n ^ d1) ^ d2"
      using 3 by (simp add: power_mono)
    have "f2 (f1 n) \<le> b + c2 * (f1 n) ^ d2"
      using 2 by simp
    also have "... \<le> b + c2 * (c1 * n ^ d1) ^ d2"
      using 4 by simp
    also have "... = b + c2 * c1 ^ d2 * n ^ (d1 * d2)"
      by (simp add: power_mult power_mult_distrib)
    also have "... = b + c * n ^ (d1 * d2)"
      using c_def by simp
    also have "... \<le> b * n ^ (d1 * d2) + c * n ^ (d1 * d2)"
      using `n > m1` by simp
    also have "... \<le> (b + c) * n ^ (d1 * d2)"
      by (simp add: comm_semiring_class.distrib)
    finally have "f2 (f1 n) \<le> (b + c) * n ^ (d1 * d2)" .
  }
  then show ?thesis
    using big_oh_polyI[of m1 _ "b + c" "d1 * d2"] by simp
qed

lemma big_oh_poly_pow:
  fixes f :: "nat \<Rightarrow> nat" and d :: nat
  assumes "big_oh_poly f"
  shows "big_oh_poly (\<lambda>n. f n ^ d)"
proof -
  let ?g = "\<lambda>n. n ^ d"
  have "big_oh_poly ?g"
    using big_oh_poly_poly by simp
  moreover have "(\<lambda>n. f n ^ d) = ?g \<circ> f"
    by auto
  ultimately show ?thesis
    using assms big_oh_poly_composition by simp
qed

text \<open>
The textbook does not give an explicit definition of polynomials. It treats them
as functions between natural numbers. So assuming the coefficients are natural
numbers too, seems natural. We justify this choice when defining $\NP$ in
Section~\ref{s:TC-NP}.

\null
\<close>

definition polynomial :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "polynomial f \<equiv> \<exists>cs. \<forall>n. f n = (\<Sum>i\<leftarrow>[0..<length cs]. cs ! i * n ^ i)"

lemma const_polynomial: "polynomial (\<lambda>_. c)"
proof -
  let ?cs = "[c]"
  have "\<forall>n. (\<lambda>_. c) n = (\<Sum>i\<leftarrow>[0..<length ?cs]. ?cs ! i * n ^ i)"
    by simp
  then show ?thesis
    using polynomial_def by blast
qed

lemma polynomial_id: "polynomial id"
proof -
  let ?cs = "[0, 1::nat]"
  have "\<forall>n::nat. id n = (\<Sum>i\<leftarrow>[0..<length ?cs]. ?cs ! i * n ^ i)"
    by simp
  then show ?thesis
    using polynomial_def by blast
qed

lemma big_oh_poly_polynomial:
  fixes f :: "nat \<Rightarrow> nat"
  assumes "polynomial f"
  shows "big_oh_poly f"
proof -
  have "big_oh_poly (\<lambda>n. (\<Sum>i\<leftarrow>[0..<length cs]. cs ! i * n ^ i))" for cs
  proof (induction "length cs" arbitrary: cs)
    case 0
    then show ?case
      using big_oh_poly_const by simp
  next
    case (Suc len)
    let ?cs = "butlast cs"
    have len: "length ?cs = len"
      using Suc by simp
    {
      fix n :: nat
      have "(\<Sum>i\<leftarrow>[0..<length cs]. cs ! i * n ^ i) = (\<Sum>i\<leftarrow>[0..<Suc len]. cs ! i * n ^ i)"
        using Suc by simp
      also have "... = (\<Sum>i\<leftarrow>[0..<len]. cs ! i * n ^ i) + cs ! len * n ^ len"
        using Suc(2)
        by (metis (mono_tags, lifting) Nat.add_0_right list.simps(8) list.simps(9) map_append
          sum_list.Cons sum_list.Nil sum_list_append upt_Suc zero_le)
      also have "... = (\<Sum>i\<leftarrow>[0..<len]. ?cs ! i * n ^ i) + cs ! len * n ^ len"
        using Suc(2) len by (metis (no_types, lifting) atLeastLessThan_iff map_eq_conv nth_butlast set_upt)
      finally have "(\<Sum>i\<leftarrow>[0..<length cs]. cs ! i * n ^ i) = (\<Sum>i\<leftarrow>[0..<len]. ?cs ! i * n ^ i) + cs ! len * n ^ len" .
    }
    then have "(\<lambda>n. \<Sum>i\<leftarrow>[0..<length cs]. cs ! i * n ^ i) = (\<lambda>n. (\<Sum>i\<leftarrow>[0..<len]. ?cs ! i * n ^ i) + cs ! len * n ^ len)"
      by simp
    moreover have "big_oh_poly (\<lambda>n. cs ! len * n ^ len)"
      using big_oh_poly_poly big_oh_poly_prod big_oh_poly_const by simp
    moreover have "big_oh_poly (\<lambda>n. (\<Sum>i\<leftarrow>[0..<len]. ?cs ! i * n ^ i))"
      using Suc len by blast
    ultimately show "big_oh_poly (\<lambda>n. \<Sum>i\<leftarrow>[0..<length cs]. cs ! i * n ^ i)"
      using big_oh_poly_sum by simp
  qed
  moreover obtain cs where "f = (\<lambda>n. (\<Sum>i\<leftarrow>[0..<length cs]. cs ! i * n ^ i))"
    using assms polynomial_def by blast
  ultimately show ?thesis
    by simp
qed


section \<open>Increasing the alphabet or the number of tapes\label{s:tm-trans}\<close>

text \<open>
For technical reasons it is sometimes necessary to add tapes to a machine or to
formally enlarge its alphabet such that it matches another machine's tape number
or alphabet size without changing the behavior of the machine. The primary use
of this is when composing machines with unequal alphabets or tape numbers (see
Section~\ref{s:tm-composing}).
\<close>

subsection \<open>Enlarging the alphabet\<close>

text \<open>
A Turing machine over alphabet $G$ is not necessarily a Turing machine over a
larger alphabet $G' > G$ because reading a symbol in $\{G, \dots, G'-1\}$ the TM
may write a symbol $\geq G'$. This is easy to remedy by modifying the TM to do
nothing when it reads a symbol $\geq G$. It then formally satisfies the alphabet
restriction property of Turing commands. This is rather crude, because the new
TM loops infinitely on encountering a ``forbidden'' symbol, but it is good
enough for our purposes.

The next function performs this transformation on a TM $M$ over alphabet $G$.
The resulting machine is a Turing machine for every alphabet size $G' \ge G$.
\<close>

definition enlarged :: "nat \<Rightarrow> machine \<Rightarrow> machine" where
  "enlarged G M \<equiv> map (\<lambda>cmd rs. if symbols_lt G rs then cmd rs else (0, map (\<lambda>r. (r, Stay)) rs)) M"

lemma length_enlarged: "length (enlarged G M) = length M"
  using enlarged_def by simp

lemma enlarged_nth:
  assumes "symbols_lt G gs" and "i < length M"
  shows "(M ! i) gs = (enlarged G M ! i) gs"
  using assms enlarged_def by simp

lemma enlarged_write:
  assumes "length gs = k" and "i < length M" and "turing_machine k G M"
  shows "length (snd ((M ! i) gs)) = length (snd ((enlarged G M ! i) gs))"
proof (cases "symbols_lt G gs")
  case True
  then show ?thesis
    using assms enlarged_def by simp
next
  case False
  then have "(enlarged G M ! i) gs = (0, map (\<lambda>r. (r, Stay)) gs)"
    using assms enlarged_def by auto
  then show ?thesis
    using assms turing_commandD(1) turing_machine_def by (metis length_map nth_mem snd_conv)
qed

lemma turing_machine_enlarged:
  assumes "turing_machine k G M" and "G' \<ge> G"
  shows "turing_machine k G' (enlarged G M)"
proof
  let ?M = "enlarged G M"
  show "2 \<le> k" and "4 \<le> G'"
    using assms turing_machine_def by simp_all
  show "turing_command k (length ?M) G' (?M ! i)"
      if i: "i < length ?M" for i
  proof
    have len: "length ?M = length M"
      using enlarged_def by simp
    then have 1: "turing_command k (length M) G (M ! i)"
      using assms(1) that turing_machine_def by simp
    show "\<And>gs. length gs = k \<Longrightarrow> length ([!!] (?M ! i) gs) = length gs"
      using enlarged_write that 1 len assms(1) by (metis turing_commandD(1))
    show "(?M ! i) gs [.] j < G'"
        if "length gs = k" "(\<And>i. i < length gs \<Longrightarrow> gs ! i < G')" "j < length gs"
        for gs j
    proof (cases "symbols_lt G gs")
      case True
      then have "(?M ! i) gs = (M ! i) gs"
        using enlarged_def i by simp
      moreover have "(M ! i) gs [.] j < G"
        using "1" turing_commandD(2) that(1,3) True by simp
      ultimately show ?thesis
        using assms(2) by simp
    next
      case False
      then have "(?M ! i) gs = (0, map (\<lambda>r. (r, Stay)) gs)"
        using enlarged_def i by auto
      then show ?thesis
        using that by simp
    qed
    show "(?M ! i) gs [.] 0 = gs ! 0" if "length gs = k" and "k > 0" for gs
    proof (cases "symbols_lt G gs")
      case True
      then show ?thesis
        using enlarged_def i "1" turing_command_def that by simp
    next
      case False
      then have "(?M ! i) gs = (0, map (\<lambda>r. (r, Stay)) gs)"
        using that enlarged_def i by auto
      then show ?thesis
        using assms(1) turing_machine_def that by simp
    qed
    show "[*] ((?M ! i) gs) \<le> length ?M" if "length gs = k" for gs
    proof (cases "symbols_lt G gs")
      case True
      then show ?thesis
        using enlarged_def i that assms(1) turing_machine_def "1" turing_commandD(4) enlarged_nth len
        by (metis (no_types, lifting))
    next
      case False
      then show ?thesis
        using that enlarged_def i by auto
    qed
  qed
qed

text \<open>
The enlarged machine has the same behavior as the original machine when started
on symbols over the original alphabet $G$.
\<close>

lemma execute_enlarged:
  assumes "turing_machine k G M" and "symbols_lt G zs"
  shows "execute (enlarged G M) (start_config k zs) t = execute M (start_config k zs) t"
proof (induction t)
  case 0
  then show ?case
    by simp
next
  case (Suc t)
  let ?M = "enlarged G M"
  have "execute ?M (start_config k zs) (Suc t) = exe ?M (execute ?M (start_config k zs) t)"
    by simp
  also have "... = exe ?M (execute M (start_config k zs) t)"
      (is "_ = exe ?M ?cfg")
    using Suc by simp
  also have "... = execute M (start_config k zs) (Suc t)"
  proof (cases "fst ?cfg < length M")
    case True
    then have "exe ?M ?cfg = sem (?M ! (fst ?cfg)) ?cfg"
        (is "_ = sem ?cmd ?cfg")
      using exe_lt_length length_enlarged by simp
    then have "exe ?M ?cfg =
        (fst (?cmd (config_read ?cfg)),
         map (\<lambda>(a, tp). act a tp) (zip (snd (?cmd (config_read ?cfg))) (snd ?cfg)))"
      using sem' by simp
    moreover have "symbols_lt G (config_read ?cfg)"
      using read_alphabet' assms by auto
    ultimately have "exe ?M ?cfg =
        (fst ((M ! (fst ?cfg)) (config_read ?cfg)),
         map (\<lambda>(a, tp). act a tp) (zip (snd ((M ! (fst ?cfg)) (config_read ?cfg))) (snd ?cfg)))"
      using True enlarged_nth by auto
    then have "exe ?M ?cfg = exe M ?cfg"
      using sem' by (simp add: True exe_lt_length)
    then show ?thesis
      using Suc by simp
  next
    case False
    then show ?thesis
      using Suc enlarged_def exe_def by auto
  qed
  finally show ?case .
qed

lemma transforms_enlarged:
  assumes "turing_machine k G M"
    and "symbols_lt G zs"
    and "transforms M (snd (start_config k zs)) t tps1"
  shows "transforms (enlarged G M) (snd (start_config k zs)) t tps1"
proof -
  let ?tps = "snd (start_config k zs)"
  have "\<exists>t'\<le>t. execute M (start_config k zs) t' = (length M, tps1)"
    using assms(3) transforms_def transits_def start_config_def by simp
  then have "\<exists>t'\<le>t. execute (enlarged G M) (start_config k zs) t' = (length M, tps1)"
    using assms(1,2) transforms_def transits_def execute_enlarged by auto
  moreover have "length M = length (enlarged G M)"
    using enlarged_def by simp
  ultimately show ?thesis
    using start_config_def transforms_def transitsI by auto
qed


subsection \<open>Increasing the number of tapes\<close>

text \<open>
We can add tapes to a Turing machine in such a way that on the additional tapes
the machine does nothing. While the new tapes could go anywhere, we only
consider appending them at the end or inserting them at the beginning.
\<close>


subsubsection \<open>Appending tapes at the end\<close>

text \<open>
The next function turns a $k$-tape Turing machine into a $k'$-tape Turing
machine (for $k' \geq k$) by appending $k' - k$ tapes at the end.
\<close>

definition append_tapes :: "nat \<Rightarrow> nat \<Rightarrow> machine \<Rightarrow> machine" where
  "append_tapes k k' M \<equiv>
    map (\<lambda>cmd rs. (fst (cmd (take k rs)), snd (cmd (take k rs)) @ (map (\<lambda>i. (rs ! i, Stay)) [k..<k']))) M"

lemma length_append_tapes: "length (append_tapes k k' M) = length M"
  unfolding append_tapes_def by simp

lemma append_tapes_nth:
  assumes "i < length M" and "length gs = k'"
  shows "(append_tapes k k' M ! i) gs =
         (fst ((M ! i) (take k gs)), snd ((M ! i) (take k gs)) @ (map (\<lambda>j. (gs ! j, Stay)) [k..<k']))"
  unfolding append_tapes_def using assms(1) by simp

lemma append_tapes_tm:
  assumes "turing_machine k G M" and "k' \<ge> k"
  shows "turing_machine k' G (append_tapes k k' M)"
proof
  let ?M = "append_tapes k k' M"
  show "2 \<le> k'"
    using assms turing_machine_def by simp
  show "4 \<le> G"
    using assms(1) turing_machine_def by simp
  show "turing_command k' (length ?M) G (?M ! i)" if "i < length ?M" for i
  proof
    have "i < length M"
      using that by (simp add: append_tapes_def)
    then have turing_command: "turing_command k (length M) G (M ! i)"
      using assms(1) that turing_machine_def by simp
    have ith: "append_tapes k k' M ! i =
        (\<lambda>rs. (fst ((M ! i) (take k rs)), snd ((M ! i) (take k rs)) @ (map (\<lambda>j. (rs ! j, Stay)) [k..<k'])))"
      unfolding append_tapes_def using `i < length M` by simp
    show "\<And>gs. length gs = k' \<Longrightarrow> length ([!!] (append_tapes k k' M ! i) gs) = length gs"
      using assms(2) ith turing_command turing_commandD by simp
    show "(append_tapes k k' M ! i) gs [.] j < G"
      if "length gs = k'" "\<And>i. i < length gs \<Longrightarrow> gs ! i < G" "j < length gs"
      for j gs
    proof (cases "j < k")
      case True
      let ?gs = "take k gs"
      have len: "length ?gs = k"
        using that(1) assms(2) by simp
      have "\<And>i. i < length ?gs \<Longrightarrow> ?gs ! i < G"
        using that(2) by simp
      then have "\<forall>i'<length ?gs. (M ! i) ?gs [.] i' < G"
        using turing_commandD(2)[OF turing_command len] by simp
      then show ?thesis
        using ith that turing_commandD(1)[OF turing_command len] by (simp add: nth_append)
    next
      case False
      then have "j \<ge> k"
        by simp
      have *: "length (snd ((M ! i) (take k gs))) = k"
        using turing_commandD(1)[OF turing_command] assms(2) that(1) by auto
      have "(append_tapes k k' M ! i) gs [.] j =
          fst ((snd ((M ! i) (take k gs)) @ (map (\<lambda>j. (gs ! j, Stay)) [k..<k'])) ! j)"
        using ith by simp
      also have "... = fst ((map (\<lambda>j. (gs ! j, Stay)) [k..<k']) ! (j - k))"
        using * that `j \<ge> k` by (simp add: False nth_append)
      also have "... = fst (gs ! j, Stay)"
        by (metis False \<open>k \<le> j\<close> add_diff_inverse_nat diff_less_mono length_upt nth_map nth_upt that(1,3))
      also have "... = gs ! j"
        by simp
      also have "... < G"
        using that(2,3) by simp
      finally show ?thesis
        by simp
    qed
    show "(append_tapes k k' M ! i) gs [.] 0 = gs ! 0" if "length gs = k'" for gs
    proof -
      have "k > 0"
        using assms(1) turing_machine_def by simp
      then have 1: "(M ! i) rs [.] 0 = rs ! 0" if "length rs = k" for rs
        using turing_commandD(3)[OF turing_command that] that by simp
      have len: "length (take k gs) = k"
        by (simp add: assms(2) min_absorb2 that(1))
      then have *: "length (snd ((M ! i) (take k gs))) = k"
        using turing_commandD(1)[OF turing_command] by auto
      have "(append_tapes k k' M ! i) gs [.] 0 =
          fst ((snd ((M ! i) (take k gs)) @ (map (\<lambda>j. (gs ! j, Stay)) [k..<k'])) ! 0)"
        using ith by simp
      also have "... = fst (snd ((M ! i) (take k gs)) ! 0)"
        using * by (simp add: nth_append `0 < k`)
      finally show ?thesis
        using 1 len \<open>0 < k\<close> by simp
    qed
    show "[*] ((append_tapes k k' M ! i) gs) \<le> length (append_tapes k k' M)" if "length gs = k'" for gs
    proof -
      have "length (take k gs) = k"
        using assms(2) that by simp
      then have 1: "fst ((M ! i) (take k gs)) \<le> length M"
        using turing_commandD[OF turing_command] \<open>i < length M\<close> assms(1) turing_machine_def by blast
      moreover have "fst ((append_tapes k k' M ! i) gs) = fst ((M ! i) (take k gs))"
        using ith by simp
      ultimately show "fst ((append_tapes k k' M ! i) gs) \<le> length (append_tapes k k' M)"
        using length_append_tapes by metis
    qed
  qed
qed

lemma execute_append_tapes:
  assumes "turing_machine k G M" and "k' \<ge> k" and "length tps = k'"
  shows "execute (append_tapes k k' M) (q, tps) t =
     (fst (execute M (q, take k tps) t), snd (execute M (q, take k tps) t) @ drop k tps)"
proof (induction t)
  case 0
  then show ?case
    by simp
next
  case (Suc t)
  let ?M = "append_tapes k k' M"
  let ?cfg = "execute M (q, take k tps) t"
  let ?cfg' = "execute M (q, take k tps) (Suc t)"
  have "execute ?M (q, tps) (Suc t) = exe ?M (execute ?M (q, tps) t)"
    by simp
  also have "... = exe ?M (fst ?cfg, snd ?cfg @ drop k tps)"
    using Suc by simp
  also have "... = (fst ?cfg', snd ?cfg' @ drop k tps)"
  proof (cases "fst ?cfg < length ?M")
    case True
    have "sem (?M ! (fst ?cfg)) (fst ?cfg, snd ?cfg @ drop k tps) = (fst ?cfg', snd ?cfg' @ drop k tps)"
    proof (rule semI)
      have "turing_machine k' G (append_tapes k k' M)"
        using append_tapes_tm[OF assms(1,2)] by simp
      then show 1: "proper_command k' (append_tapes k k' M ! fst (execute M (q, take k tps) t))"
        using True turing_machine_def turing_commandD by (metis nth_mem)
      show 2: "length (snd ?cfg @ drop k tps) = k'"
        using assms execute_num_tapes by fastforce
      show "length (snd ?cfg' @ drop k tps) = k'"
        by (metis (no_types, lifting) append_take_drop_id assms execute_num_tapes
          length_append length_take min_absorb2 snd_conv)
      show "fst ((?M ! fst ?cfg) (read (snd ?cfg @ drop k tps))) = fst ?cfg'"
      proof -
        have less': "fst ?cfg < length M"
          using True by (simp add: length_append_tapes)
        let ?tps = "snd ?cfg @ drop k tps"
        have "length (snd ?cfg) = k"
          using assms execute_num_tapes by fastforce
        then have take2: "take k ?tps = snd ?cfg"
          by simp
        let ?rs = "read ?tps"
        have len: "length ?rs = k'"
          using 2 read_length by simp
        have take2': "take k ?rs = read (snd ?cfg)"
          using read_def take2 by (metis (mono_tags, lifting) take_map)
        have "fst ((?M ! fst ?cfg) ?rs) =
            fst (fst ((M ! fst ?cfg) (take k ?rs)), snd ((M ! fst ?cfg) (take k ?rs)) @ (map (\<lambda>j. (?rs ! j, Stay)) [k..<k']))"
          using append_tapes_nth[OF less' len] by simp
        also have "... = fst ((M ! fst ?cfg) (read (snd ?cfg)))"
          using take2' by simp
        also have "... = fst (exe M ?cfg)"
          by (simp add: exe_def less' sem_fst)
        finally show ?thesis
          by simp
      qed
      show "(act ((?M ! fst ?cfg) (read (snd ?cfg @ drop k tps)) [!] j) ((snd ?cfg @ drop k tps) ! j) =
            (snd ?cfg' @ drop k tps) ! j)"
          if "j < k'" for j
      proof -
        have less': "fst ?cfg < length M"
          using True by (simp add: length_append_tapes)
        let ?tps = "snd ?cfg @ drop k tps"
        have len2: "length (snd ?cfg) = k"
          using assms execute_num_tapes by fastforce
        then have take2: "take k ?tps = snd ?cfg"
          by simp
        from len2 have len2': "length (snd ((M ! fst ?cfg) (read (snd ?cfg)))) = k"
          using assms(1) turing_commandD(1) less' read_length turing_machine_def by (metis nth_mem)
        let ?rs = "read ?tps"
        have len: "length ?rs = k'"
          using 2 read_length by simp
        have take2': "take k ?rs = read (snd ?cfg)"
          using read_def take2 by (metis (mono_tags, lifting) take_map)
        have "act ((?M ! fst ?cfg) ?rs [!] j) (?tps ! j) =
            act ((fst ((M ! fst ?cfg) (take k ?rs)), snd ((M ! fst ?cfg) (take k ?rs)) @ (map (\<lambda>j. (?rs ! j, Stay)) [k..<k'])) [!] j) (?tps ! j)"
          using append_tapes_nth[OF less' len] by simp
        also have "... = act
             ((fst ((M ! fst ?cfg) (read (snd ?cfg))), snd ((M ! fst ?cfg) (read (snd ?cfg))) @ (map (\<lambda>j. (?rs ! j, Stay)) [k..<k'])) [!] j)
             (?tps ! j)"
          using take2' by simp
        also have "... = act
             ((snd ((M ! fst ?cfg) (read (snd ?cfg))) @ (map (\<lambda>j. (?rs ! j, Stay)) [k..<k'])) ! j)
             (?tps ! j)"
          by simp
        also have "... = (snd ?cfg' @ drop k tps) ! j"
        proof (cases "j < k")
          case True
          then have tps: "?tps ! j = snd ?cfg ! j"
            by (simp add: len2 nth_append)
          have "(snd ?cfg' @ drop k tps) ! j = (snd (exe M ?cfg) @ drop k tps) ! j"
            by simp
          also have "... = snd (exe M ?cfg) ! j"
            using assms(1) True by (metis exe_num_tapes len2 nth_append)
          also have "... = snd (sem (M ! fst ?cfg) ?cfg) ! j"
            by (simp add: exe_lt_length less')
          also have "... = act (snd ((M ! fst ?cfg) (read (snd ?cfg))) ! j) (?tps ! j)"
          proof -
            have "proper_command k (M ! (fst ?cfg))"
              using turing_commandD(1) turing_machine_def assms(1) less' nth_mem by blast
            then show ?thesis
              using sem_snd True tps len2 by simp
          qed
          finally show ?thesis
              using len2' True by (simp add: nth_append)
        next
          case False
          then have tps: "?tps ! j = tps ! j"
            using len2 by (metis (no_types, lifting) "2" append_take_drop_id assms(3) length_take nth_append take2)
          from False have gt2: "j \<ge> k"
            by simp
          have len': "length (snd ?cfg') = k"
            using assms(1) exe_num_tapes len2 by auto
          have rs: "?rs ! j = read tps ! j"
            using tps by (metis (no_types, lifting) "2" assms(3) that nth_map read_def)
          have "act ((snd ((M ! fst ?cfg) (read (snd ?cfg))) @ (map (\<lambda>j. (?rs ! j, Stay)) [k..<k'])) ! j) (?tps ! j) =
               act ((map (\<lambda>j. (?rs ! j, Stay)) [k..<k']) ! (j - k)) (?tps ! j)"
            using False len2 len2' by (simp add: nth_append)
          also have "... = act (?rs ! j, Stay) (?tps ! j)"
            by (metis (no_types, lifting) False add_diff_inverse_nat diff_less_mono gt2 that length_upt nth_map nth_upt)
          also have "... = act (?rs ! j, Stay) (tps ! j)"
            using tps by simp
          also have "... = act (read tps ! j, Stay) (tps ! j)"
            using rs by simp
          also have "... = tps ! j"
            using act_Stay assms(3) that by simp
          also have "... = (snd (exe M ?cfg) @ drop k tps) ! j"
            using len'
            by (metis (no_types, lifting) "2" False append_take_drop_id assms(3) execute.simps(2) len2 length_take nth_append take2)
          also have "... = (snd ?cfg' @ drop k tps) ! j"
            by simp
          finally show ?thesis
            by simp
        qed
        finally show "act ((?M ! fst ?cfg) ?rs [!] j) (?tps ! j) = (snd ?cfg' @ drop k tps) ! j" .
      qed
    qed
    then show ?thesis
      using exe_def True by simp
  next
    case False
    then show ?thesis
      using assms by (simp add: exe_ge_length length_append_tapes)
  qed
  finally show "execute ?M (q, tps) (Suc t) = (fst ?cfg', snd ?cfg' @ drop k tps)" .
qed

lemma execute_append_tapes':
  assumes "turing_machine k G M" and "length tps = k"
  shows "execute (append_tapes k (k + length tps') M) (q, tps @ tps') t =
     (fst (execute M (q, tps) t), snd (execute M (q, tps) t) @ tps')"
  using assms execute_append_tapes by simp

lemma transforms_append_tapes:
  assumes "turing_machine k G M"
    and "length tps0 = k"
    and "transforms M tps0 t tps1"
  shows "transforms (append_tapes k (k + length tps') M) (tps0 @ tps') t (tps1 @ tps')"
    (is "transforms ?M _ _ _")
proof -
  have "execute M (0, tps0) t = (length M, tps1)"
    using assms(3) transforms_def transits_def by (metis (no_types, opaque_lifting) execute_after_halting_ge fst_conv)
  then have "execute ?M (0, tps0 @ tps') t = (length M, tps1 @ tps')"
    using assms(1,2) execute_append_tapes' by simp
  moreover have "length M = length ?M"
    by (simp add: length_append_tapes)
  ultimately show ?thesis
    by (simp add: execute_imp_transits transforms_def)
qed


subsubsection \<open>Inserting tapes at the beginning\<close>

text \<open>
The next function turns a $k$-tape Turing machine into a $(k + d)$-tape Turing
machine by inserting $d$ tapes at the beginning.
\<close>

definition prepend_tapes :: "nat \<Rightarrow> machine \<Rightarrow> machine" where
  "prepend_tapes d M \<equiv>
    map (\<lambda>cmd rs. (fst (cmd (drop d rs)), map (\<lambda>h. (h, Stay)) (take d rs) @ snd (cmd (drop d rs)))) M"

lemma prepend_tapes_at:
  assumes "i < length M"
  shows "(prepend_tapes d M ! i) gs =
    (fst ((M ! i) (drop d gs)), map (\<lambda>h. (h, Stay)) (take d gs) @ snd ((M ! i) (drop d gs)))"
  using assms prepend_tapes_def by simp

lemma prepend_tapes_tm:
  assumes "turing_machine k G M"
  shows "turing_machine (d + k) G (prepend_tapes d M)"
proof
  show "2 \<le> d + k"
    using assms turing_machine_def by simp
  show "4 \<le> G"
    using assms turing_machine_def by simp
  let ?M = "prepend_tapes d M"
  show "turing_command (d + k) (length ?M) G (?M ! i)" if "i < length ?M" for i
  proof
    have len: "i < length M"
      using that prepend_tapes_def by simp
    then have *: "(?M ! i) gs = (fst ((M ! i) (drop d gs)), map (\<lambda>h. (h, Stay)) (take d gs) @ snd ((M ! i) (drop d gs)))"
        if "length gs = d + k" for gs
      using prepend_tapes_def that by simp
    have tc: "turing_command k (length M) G (M ! i)"
      using that turing_machine_def len assms by simp
    show "length (snd ((?M ! i) gs)) = length gs" if "length gs = d + k" for gs
      using * that turing_commandD[OF tc] by simp
    show "(?M ! i) gs [.] j < G"
        if "length gs = d + k" "(\<And>i. i < length gs \<Longrightarrow> gs ! i < G)" "j < length gs"
        for gs j
    proof (cases "j < d")
      case True
      have "(?M ! i) gs [.] j = fst ((map (\<lambda>h. (h, Stay)) (take d gs) @ snd ((M ! i) (drop d gs))) ! j)"
        using * that(1) by simp
      also have "... = fst (map (\<lambda>h. (h, Stay)) (take d gs) ! j)"
        using True that(1) by (simp add: nth_append)
      also have "... = gs ! j"
        by (simp add: True that(3))
      finally have "(?M ! i) gs [.] j = gs ! j" .
      then show ?thesis
        using that(2,3) by simp
    next
      case False
      have "(?M ! i) gs [.] j = fst ((map (\<lambda>h. (h, Stay)) (take d gs) @ snd ((M ! i) (drop d gs))) ! j)"
        using * that(1) by simp
      also have "... = fst (snd ((M ! i) (drop d gs)) ! (j - d))"
        using False that(1)
        by (metis (no_types, lifting) add_diff_cancel_left' append_take_drop_id
          diff_add_inverse2 length_append length_drop length_map nth_append)
      also have "... < G"
        using False that turing_commandD[OF tc] by simp
      finally show ?thesis
        by simp
    qed
    show "(?M ! i) gs [.] 0 = gs ! 0" if "length gs = d + k" and "d + k > 0" for gs
    proof (cases "d = 0")
      case True
      then have "(?M ! i) gs [.] 0 = fst (snd ((M ! i) gs) ! 0)"
        using * that(1) by simp
      then show ?thesis
        using True that turing_commandD[OF tc] by simp
    next
      case False
      then have "(?M ! i) gs [.] 0 = fst ((map (\<lambda>h. (h, Stay)) (take d gs)) ! 0)"
        using * that(1) by (simp add: nth_append)
      also have "... = fst ((map (\<lambda>h. (h, Stay)) gs) ! 0)"
        using False by (metis gr_zeroI nth_take take_map)
      also have "... = gs ! 0"
        using False that by simp
      finally show ?thesis
        by simp
    qed
    show "[*] ((?M ! i) gs) \<le> length ?M" if "length gs = d + k" for gs
    proof -
      have "fst ((?M ! i) gs) = fst ((M ! i) (drop d gs))"
        using that * by simp
      moreover have "length (drop d gs) = k"
        using that by simp
      ultimately have "fst ((?M ! i) gs) \<le> length M"
        using turing_commandD(4)[OF tc] by fastforce
      then show "fst ((?M ! i) gs) \<le> length ?M"
        using prepend_tapes_def by simp
    qed
  qed
qed

definition shift_cfg :: "tape list \<Rightarrow> config \<Rightarrow> config" where
  "shift_cfg tps cfg \<equiv> (fst cfg, tps @ snd cfg)"

lemma execute_prepend_tapes:
  assumes "turing_machine k G M" and "length tps = d" and "||cfg0|| = k"
  shows "execute (prepend_tapes d M) (shift_cfg tps cfg0) t = shift_cfg tps (execute M cfg0 t)"
proof (induction t)
  case 0
  show ?case
    by simp
next
  case (Suc t)
  let ?M = "prepend_tapes d M"
  let ?scfg = "shift_cfg tps cfg0"
  let ?scfg' = "execute ?M ?scfg t"
  let ?cfg' = "execute M cfg0 t"
  have fst: "fst ?cfg' = fst ?scfg'"
    using shift_cfg_def Suc.IH by simp
  have len: "||?cfg'|| = k"
    using assms(1,3) execute_num_tapes read_length by auto
  have len_s: "||?scfg'|| = d + k"
    using prepend_tapes_tm[OF assms(1)] shift_cfg_def assms(2,3) execute_num_tapes read_length
    by (metis length_append snd_conv)
  let ?srs = "read (snd ?scfg')"
  let ?rs = "read (snd ?cfg')"
  have len_rs: "length ?rs = k"
    using assms(1,3) execute_num_tapes read_length by auto
  moreover have len_srs: "length ?srs = k + d"
    using prepend_tapes_tm[OF assms(1)] shift_cfg_def assms(2,3)
    by (metis add.commute execute_num_tapes length_append read_length snd_conv)
  ultimately have srs_rs: "drop d ?srs = ?rs"
    using Suc shift_cfg_def read_def by simp
  have *: "execute ?M ?scfg (Suc t) = exe ?M ?scfg'"
    by simp
  show ?case
  proof (cases "fst ?scfg' \<ge> length ?M")
    case True
    then show ?thesis
      using * Suc exe_ge_length shift_cfg_def prepend_tapes_def by auto
  next
    case running: False
    then have scmd: "?M ! (fst ?scfg') =
      (\<lambda>gs. (fst ((M ! (fst ?scfg')) (drop d gs)), map (\<lambda>h. (h, Stay)) (take d gs) @ snd ((M ! (fst ?scfg')) (drop d gs))))"
      (is "?scmd = _")
      using prepend_tapes_at prepend_tapes_def by auto
    then have cmd: "?M ! (fst ?scfg') =
      (\<lambda>gs. (fst ((M ! (fst ?cfg')) (drop d gs)), map (\<lambda>h. (h, Stay)) (take d gs) @ snd ((M ! (fst ?cfg')) (drop d gs))))"
      using fst by simp
    let ?cmd = "M ! (fst ?cfg')"

    have "execute ?M ?scfg (Suc t) = sem (?M ! (fst ?scfg')) ?scfg'"
      using running * exe_lt_length by simp
    then have lhs: "execute ?M ?scfg (Suc t) =
        (fst (?scmd ?srs), map (\<lambda>(a, tp). act a tp) (zip (snd (?scmd ?srs)) (snd ?scfg')))"
        (is "_ = ?lhs")
      using sem' by simp

    have "shift_cfg tps (execute M cfg0 (Suc t)) = shift_cfg tps (exe M ?cfg')"
      by simp
    also have "... = shift_cfg tps (sem (M ! (fst ?cfg')) ?cfg')"
      using exe_lt_length running fst prepend_tapes_def by auto
    also have "... = shift_cfg tps
        (fst (?cmd ?rs), map (\<lambda>(a, tp). act a tp) (zip (snd (?cmd ?rs)) (snd ?cfg')))"
      using sem' by simp
    also have "... = (fst (?cmd ?rs), tps @ map (\<lambda>(a, tp). act a tp) (zip (snd (?cmd ?rs)) (snd ?cfg')))"
      using shift_cfg_def by simp
    finally have rhs: "shift_cfg tps (execute M cfg0 (Suc t)) =
       (fst (?cmd ?rs), tps @ map (\<lambda>(a, tp). act a tp) (zip (snd (?cmd ?rs)) (snd ?cfg')))"
      (is "_ = ?rhs") .

    have "?lhs = ?rhs"
    proof standard+
      show "fst (?scmd ?srs) = fst (?cmd ?rs)"
        using srs_rs cmd by simp
      show "map (\<lambda>(a, tp). act a tp) (zip (snd (?scmd ?srs)) (snd ?scfg')) =
          tps @ map (\<lambda>(a, tp). act a tp) (zip (snd (?cmd ?rs)) (snd ?cfg'))"
          (is "?l = ?r")
      proof (rule nth_equalityI)
        have lenl: "length ?l = d + k"
          using lhs execute_num_tapes assms prepend_tapes_tm len_s
          by (smt (z3) length_append shift_cfg_def snd_conv)
        moreover have "length ?r = d + k"
          using rhs execute_num_tapes assms shift_cfg_def
          by (metis (mono_tags, lifting) length_append snd_conv)
        ultimately show "length ?l = length ?r"
          by simp
        show "?l ! j = ?r ! j" if "j < length ?l" for j
        proof (cases "j < d")
          case True
          let ?at = "zip (snd (?scmd ?srs)) (snd ?scfg') ! j"
          have "?l ! j = act (fst ?at) (snd ?at)"
            using that by simp
          moreover have "fst ?at = snd (?scmd ?srs) ! j"
            using that by simp
          moreover have "snd ?at = snd ?scfg' ! j"
            using that by simp
          ultimately have "?l ! j = act (snd (?scmd ?srs) ! j) (snd ?scfg' ! j)"
            by simp
          moreover have "snd ?scfg' ! j = tps ! j"
            using shift_cfg_def assms(2) by (metis (no_types, lifting) Suc.IH True nth_append snd_conv)
          moreover have "snd (?scmd ?srs) ! j = (?srs ! j, Stay)"
          proof -
            have "snd (?scmd ?srs) = map (\<lambda>h. (h, Stay)) (take d ?srs) @ snd ((M ! (fst ?scfg')) (drop d ?srs))"
              using scmd by simp
            then have "snd (?scmd ?srs) ! j = map (\<lambda>h. (h, Stay)) (take d ?srs) ! j"
              using len_srs lenl True that
              by (smt (z3) add.commute length_map length_take min_less_iff_conj nth_append)
            then show ?thesis
              using len_srs True by simp
          qed
          moreover have "?r ! j = tps ! j"
            using True assms(2) by (simp add: nth_append)
          ultimately show ?thesis
            using len_s that lenl by (metis act_Stay)
        next
          case False
          have jle: "j < d + k"
            using lenl that by simp
          have jle': "j - d < k"
            using lenl that False by simp

          let ?at = "zip (snd (?scmd ?srs)) (snd ?scfg') ! j"
          have "?l ! j = act (fst ?at) (snd ?at)"
            using that by simp
          moreover have "fst ?at = snd (?scmd ?srs) ! j"
            using that by simp
          moreover have "snd ?at = snd ?scfg' ! j"
            using that by simp
          ultimately have "?l ! j = act (snd (?scmd ?srs) ! j) (snd ?scfg' ! j)"
            by simp
          moreover have "snd ?scfg' ! j = snd ?cfg' ! (j - d)"
            using shift_cfg_def assms(2) Suc False jle by (metis nth_append snd_conv)
          moreover have "snd (?scmd ?srs) ! j = snd (?cmd ?rs) ! (j - d)"
          proof -
            have "snd (?scmd ?srs) = map (\<lambda>h. (h, Stay)) (take d ?srs) @ snd ((M ! (fst ?cfg')) (drop d ?srs))"
              using cmd by simp
            then have "snd (?scmd ?srs) ! j = snd ((M ! (fst ?cfg')) (drop d ?srs)) ! (j - d)"
              using len_srs lenl False that len_rs
              by (smt (z3) Nat.add_diff_assoc add.right_neutral add_diff_cancel_left' append_take_drop_id
                le_add1 length_append length_map nth_append srs_rs)
            then have "snd (?scmd ?srs) ! j = snd (?cmd ?rs) ! (j - d)"
              using srs_rs by simp
            then show ?thesis
              by simp
          qed
          moreover have "?r ! j = act (snd (?cmd ?rs) ! (j - d)) (snd ?cfg' ! (j - d))"
          proof -
            have "fst (execute M cfg0 t) < length M"
              using running fst prepend_tapes_def by simp
            then have len1: "length (snd (?cmd ?rs)) = k"
              using assms(1) len_rs turing_machine_def[of k G M] turing_commandD(1) by fastforce
            have "?r ! j = map (\<lambda>(a, tp). act a tp) (zip (snd (?cmd ?rs)) (snd ?cfg')) ! (j - d)"
              using assms(2) False by (simp add: nth_append)
            also have "... = act (snd (?cmd ?rs) ! (j - d)) (snd ?cfg' ! (j - d))"
              using len1 len jle' by simp
            finally show ?thesis
              by simp
          qed
          ultimately show ?thesis
            by simp
        qed
      qed
    qed
    then show ?thesis
      using lhs rhs by simp
  qed
qed

lemma transforms_prepend_tapes:
  assumes "turing_machine k G M"
    and "length tps = d"
    and "length tps0 = k"
    and "transforms M tps0 t tps1"
  shows "transforms (prepend_tapes d M) (tps @ tps0) t (tps @ tps1)"
proof -
  have "\<exists>t'\<le>t. execute M (0, tps0) t' = (length M, tps1)"
    using assms(4) transforms_def transits_def by simp
  then have "\<exists>t'\<le>t. execute (prepend_tapes d M) (shift_cfg tps (0, tps0)) t' = shift_cfg tps (length M, tps1)"
    using assms transforms_def transits_def execute_prepend_tapes shift_cfg_def by auto
  moreover have "length M = length (prepend_tapes d M)"
    using prepend_tapes_def by simp
  ultimately show ?thesis
    using shift_cfg_def transforms_def transitsI by auto
qed

end