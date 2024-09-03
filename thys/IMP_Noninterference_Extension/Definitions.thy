(*  Title:       Extension of Stateful Intransitive Noninterference with Inputs, Outputs, and Nondeterminism in Language IMP
    Author:      Pasquale Noce
                 Senior Staff Firmware Engineer at HID Global, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at hidglobal dot com
*)

section "Underlying concepts and formal definitions"

theory Definitions
  imports Small_Step
begin


subsection "Global context definitions"

text \<open>
As compared with my previous paper \<^cite>\<open>"Noce24"\<close>:

  \<^item> Type @{text flow}, which models any potential program execution flow as a list of instructions,
occurring in their order of execution, is extended with two additional instructions, namely an input
instruction @{text "IN x"} and an output instruction @{text "OUT x"} standing for the respective
additional commands of the considered extension of language IMP.

  \<^item> Function @{text run_flow}, which used to map a pair formed by such a program execution flow
@{text cs} and a starting program state @{text s} to the resulting program state, here takes two
additional parameters, namely a starting trace of inputs @{text vs} and a stream of input values
@{text f}, since they are required as well for computing the resulting program state according to
the semantics of the considered extension of language IMP.

\null
\<close>

declare [[syntax_ambiguity_warning = false]]


datatype com_flow =
  Assign vname aexp  ("_ ::= _" [1000, 61] 70) |
  Input vname  ("(IN _)" [61] 70) |
  Output vname  ("(OUT _)" [61] 70) |
  Observe "vname set"  ("\<langle>_\<rangle>" [61] 70)

type_synonym flow = "com_flow list"
type_synonym tag = "vname \<times> nat"
type_synonym config = "state set \<times> vname set"
type_synonym scope = "config set \<times> bool"
type_synonym state_upd = "vname \<times> val option"


definition eq_streams ::
 "stream \<Rightarrow> stream \<Rightarrow> inputs \<Rightarrow> inputs \<Rightarrow> tag set \<Rightarrow> bool"
  ("(_ = _ '(\<subseteq> _, _, _'))" [51, 51] 50) where
"f = f' (\<subseteq> vs, vs', T) \<equiv> \<forall>(x, n) \<in> T.
  f x (length [p\<leftarrow>vs. fst p = x] + n) =
  f' x (length [p\<leftarrow>vs'. fst p = x] + n)"

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


primrec avars :: "aexp \<Rightarrow> vname set" where
"avars (N i) = {}" |
"avars (V x) = {x}" |
"avars (Plus a\<^sub>1 a\<^sub>2) = avars a\<^sub>1 \<union> avars a\<^sub>2"

primrec bvars :: "bexp \<Rightarrow> vname set" where
"bvars (Bc v) = {}" |
"bvars (Not b) = bvars b" |
"bvars (And b\<^sub>1 b\<^sub>2) = bvars b\<^sub>1 \<union> bvars b\<^sub>2" |
"bvars (Less a\<^sub>1 a\<^sub>2) = avars a\<^sub>1 \<union> avars a\<^sub>2"

fun no_upd :: "flow \<Rightarrow> vname set \<Rightarrow> bool" where
"no_upd (x ::= _ # cs) X = (x \<notin> X \<and> no_upd cs X)" |
"no_upd (IN x # cs) X = (x \<notin> X \<and> no_upd cs X)" |
"no_upd (OUT x # cs) X = (x \<notin> X \<and> no_upd cs X)" |
"no_upd (_ # cs) X = no_upd cs X" |
"no_upd _ _ = True"


fun flow_aux :: "com list \<Rightarrow> flow" where
"flow_aux (x ::= a # cs) = (x ::= a) # flow_aux cs" |
"flow_aux (IN x # cs) = IN x # flow_aux cs" |
"flow_aux (OUT x # cs) = OUT x # flow_aux cs" |
"flow_aux (IF b THEN _ ELSE _ # cs) = \<langle>bvars b\<rangle> # flow_aux cs" |
"flow_aux (WHILE b DO _ # cs) = \<langle>bvars b\<rangle> # flow_aux cs" |
"flow_aux (c;; _ # cs) = flow_aux (c # cs)" |
"flow_aux (_ # cs) = flow_aux cs" |
"flow_aux [] = []"

definition flow :: "(com \<times> stage) list \<Rightarrow> flow" where
"flow cfs = flow_aux (map fst cfs)"


function in_flow :: "flow \<Rightarrow> inputs \<Rightarrow> stream \<Rightarrow> inputs" where
"in_flow (cs @ [_ ::= _]) vs f = in_flow cs vs f" |
"in_flow (cs @ [IN x]) vs f = in_flow cs vs f @ (let
  n = length [p\<leftarrow>vs. fst p = x] + length [c\<leftarrow>cs. c = IN x]
  in [(x, f x n)])" |
"in_flow (cs @ [OUT _]) vs f = in_flow cs vs f" |
"in_flow (cs @ [\<langle>_\<rangle>]) vs f = in_flow cs vs f" |
"in_flow [] _ _ = []"

proof atomize_elim
  fix p :: "flow \<times> inputs \<times> stream"
  show
   "(\<exists>cs x a vs f. p = (cs @ [x ::= a], vs, f)) \<or>
    (\<exists>cs x vs f. p = (cs @ [IN x], vs, f)) \<or>
    (\<exists>cs x vs f. p = (cs @ [OUT x], vs, f)) \<or>
    (\<exists>cs X vs f. p = (cs @ [\<langle>X\<rangle>], vs, f)) \<or>
    (\<exists>vs f. p = ([], vs, f))"
    by (cases p, metis com_flow.exhaust rev_exhaust)
qed auto

termination by lexicographic_order


function run_flow :: "flow \<Rightarrow> inputs \<Rightarrow> state \<Rightarrow> stream \<Rightarrow> state" where
"run_flow (cs @ [x ::= a]) vs s f = (let t = run_flow cs vs s f
  in t(x := aval a t))" |
"run_flow (cs @ [IN x]) vs s f = (let t = run_flow cs vs s f;
  n = length [p\<leftarrow>vs. fst p = x] + length [c\<leftarrow>cs. c = IN x]
  in t(x := f x n))" |
"run_flow (cs @ [OUT _]) vs s f = run_flow cs vs s f" |
"run_flow (cs @ [\<langle>_\<rangle>]) vs s f = run_flow cs vs s f" |
"run_flow [] vs s _ = s"

proof atomize_elim
  fix p :: "flow \<times> inputs \<times> state \<times> stream"
  show
   "(\<exists>cs x a vs s f. p = (cs @ [x ::= a], vs, s, f)) \<or>
    (\<exists>cs x vs s f. p = (cs @ [IN x], vs, s, f)) \<or>
    (\<exists>cs x vs s f. p = (cs @ [OUT x], vs, s, f)) \<or>
    (\<exists>cs X vs s f. p = (cs @ [\<langle>X\<rangle>], vs, s, f)) \<or>
    (\<exists>vs s f. p = ([], vs, s, f))"
    by (cases p, metis com_flow.exhaust rev_exhaust)
qed auto

termination by lexicographic_order


function out_flow :: "flow \<Rightarrow> inputs \<Rightarrow> state \<Rightarrow> stream \<Rightarrow> outputs" where
"out_flow (cs @ [_ ::= _]) vs s f = out_flow cs vs s f" |
"out_flow (cs @ [IN _]) vs s f = out_flow cs vs s f" |
"out_flow (cs @ [OUT x]) vs s f = (let t = run_flow cs vs s f
  in out_flow cs vs s f @ [(x, t x)])" |
"out_flow (cs @ [\<langle>_\<rangle>]) vs s f = out_flow cs vs s f" |
"out_flow [] _ _ _ = []"

proof atomize_elim
  fix p :: "flow \<times> inputs \<times> state \<times> stream"
  show
   "(\<exists>cs x a vs s f. p = (cs @ [x ::= a], vs, s, f)) \<or>
    (\<exists>cs x vs s f. p = (cs @ [IN x], vs, s, f)) \<or>
    (\<exists>cs x vs s f. p = (cs @ [OUT x], vs, s, f)) \<or>
    (\<exists>cs X vs s f. p = (cs @ [\<langle>X\<rangle>], vs, s, f)) \<or>
    (\<exists>vs s f. p = ([], vs, s, f))"
    by (cases p, metis com_flow.exhaust rev_exhaust)
qed auto

termination by lexicographic_order


subsection "Local context definitions"

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

As in my previous paper \<^cite>\<open>"Noce24"\<close>, function @{text sources} is defined along with an auxiliary
function @{text sources_aux} by means of mutual recursion. According to this definition, the set of
variables @{text "sources cs vs s f x"}, where:

  \<^item> @{text cs} is a program execution flow,

  \<^item> @{text vs} is a trace of inputs,

  \<^item> @{text s} is a program state,

  \<^item> @{text f} is a stream of input values, and

  \<^item> @{text x} is a variable,

contains a variable @{text y} if there exist a descending sequence of left sublists @{text "cs\<^sub>n\<^sub>+\<^sub>1"},
@{term "cs\<^sub>n @ [c\<^sub>n]"}, ..., @{term "cs\<^sub>1 @ [c\<^sub>1]"} of @{text cs} and a sequence of variables
@{text "y\<^sub>n\<^sub>+\<^sub>1"}, ..., @{text y\<^sub>1}, where $n \ge 1$, @{text "cs\<^sub>n\<^sub>+\<^sub>1 = cs"}, @{text "y\<^sub>n\<^sub>+\<^sub>1 = x"}, and
@{text "y\<^sub>1 = y"}, satisfying the following conditions.

  \<^item> For each positive integer $i \le n$, the instruction @{text "c\<^sub>i"} is an assignment
@{text "y\<^sub>i\<^sub>+\<^sub>1 ::= a\<^sub>i"} such that:

    \<^item> @{prop "y\<^sub>i \<in> avars a\<^sub>i"},

    \<^item> @{text "run_flow cs\<^sub>i vs s f: dom y\<^sub>i \<leadsto> dom y\<^sub>i\<^sub>+\<^sub>1"}, and

    \<^item> the right sublist of @{text "cs\<^sub>i\<^sub>+\<^sub>1"} complementary to @{term "cs\<^sub>i @ [c\<^sub>i]"} does not comprise
any assignment or input instruction setting variable @{text "y\<^sub>i\<^sub>+\<^sub>1"} (as the assignment @{text "c\<^sub>i"}
would otherwise be irrelevant),

  or else an observation @{term "\<langle>X\<^sub>i\<rangle>"} such that:

    \<^item> @{prop "y\<^sub>i \<in> X\<^sub>i"} and

    \<^item> @{text "run_flow cs\<^sub>i vs s f: dom y\<^sub>i \<leadsto> dom y\<^sub>i\<^sub>+\<^sub>1"}.

  \<^item> The program execution flow @{text "cs\<^sub>1"} does not comprise any assignment or input instruction
setting variable @{text y}.

In addition, @{text "sources cs vs s f x"} contains variable @{text x} also if the program execution
flow @{text cs} does not comprise any assignment or input instruction setting variable @{text x}.

\null
\<close>

function
  sources :: "flow \<Rightarrow> inputs \<Rightarrow> state \<Rightarrow> stream \<Rightarrow> vname \<Rightarrow> vname set" and
  sources_aux :: "flow \<Rightarrow> inputs \<Rightarrow> state \<Rightarrow> stream \<Rightarrow> vname \<Rightarrow> vname set"
where

"sources (cs @ [c]) vs s f x = (case c of
  z ::= a \<Rightarrow> if z = x
    then sources_aux cs vs s f x \<union> \<Union> {sources cs vs s f y | y.
      run_flow cs vs s f: dom y \<leadsto> dom x \<and> y \<in> avars a}
    else sources cs vs s f x |
  IN z \<Rightarrow> if z = x
    then sources_aux cs vs s f x
    else sources cs vs s f x |
  \<langle>X\<rangle> \<Rightarrow>
    sources cs vs s f x \<union> \<Union> {sources cs vs s f y | y.
      run_flow cs vs s f: dom y \<leadsto> dom x \<and> y \<in> X} |
  _ \<Rightarrow>
    sources cs vs s f x)" |

"sources [] _ _ _ x = {x}" |

"sources_aux (cs @ [c]) vs s f x = (case c of
  \<langle>X\<rangle> \<Rightarrow>
    sources_aux cs vs s f x \<union> \<Union> {sources cs vs s f y | y.
      run_flow cs vs s f: dom y \<leadsto> dom x \<and> y \<in> X} |
  _ \<Rightarrow>
    sources_aux cs vs s f x)" |

"sources_aux [] _ _ _ _ = {}"

proof atomize_elim
  fix a :: "flow \<times> inputs \<times> state \<times> stream \<times> vname +
    flow \<times> inputs \<times> state \<times> stream \<times> vname"
  show
   "(\<exists>cs c vs s f x. a = Inl (cs @ [c], vs, s, f, x)) \<or>
    (\<exists>vs s f x. a = Inl ([], vs, s, f, x)) \<or>
    (\<exists>cs c vs s f x. a = Inr (cs @ [c], vs, s, f, x)) \<or>
    (\<exists>vs s f x. a = Inr ([], vs, s, f, x))"
    by (metis obj_sumE prod_cases3 rev_exhaust)
qed auto

termination by lexicographic_order

lemmas sources_induct = sources_sources_aux.induct

text \<open>
\null

Function @{text sources_out}, defined here below, takes the same parameters @{text cs}, @{text vs},
@{text s}, @{text f}, and @{text x} as function @{const sources}, and returns the set of the
variables whose values in the program state @{text s} are allowed to affect the outputs of variable
@{text x} possibly occurring as a result of the execution of flow @{text cs} if it starts from the
initial state @{text s} and the initial trace of inputs @{text vs}, and takes place according to the
stream of input values @{text f}.

In more detail, the set of variables @{text "sources_out cs vs s f x"} is defined as the union of
any set of variables @{text "sources cs\<^sub>i vs s f x\<^sub>i"}, where @{term "cs\<^sub>i @ [c\<^sub>i]"} is any left sublist
of @{text cs} such that the instruction @{text "c\<^sub>i"} is an output instruction @{text "OUT x"}, in
which case @{text "x\<^sub>i = x"}, or else an observation @{term "\<langle>X\<^sub>i\<rangle>"} such that:

  \<^item> @{prop "x\<^sub>i \<in> X\<^sub>i"} and

  \<^item> @{text "run_flow cs\<^sub>i vs s f: dom x\<^sub>i \<leadsto> dom x"}.

\null
\<close>

function
  sources_out :: "flow \<Rightarrow> inputs \<Rightarrow> state \<Rightarrow> stream \<Rightarrow> vname \<Rightarrow> vname set"
where

"sources_out (cs @ [c]) vs s f x = (case c of
  OUT z \<Rightarrow>
    sources_out cs vs s f x \<union> (if z = x then sources cs vs s f x else {}) |
  \<langle>X\<rangle> \<Rightarrow>
    sources_out cs vs s f x \<union> \<Union> {sources cs vs s f y | y.
      run_flow cs vs s f: dom y \<leadsto> dom x \<and> y \<in> X} |
  _ \<Rightarrow>
    sources_out cs vs s f x)" |

"sources_out [] _ _ _ _ = {}"

by (atomize_elim, auto intro: rev_cases)
termination by lexicographic_order

text \<open>
\null

Function @{text tags}, defined here below, takes the same parameters @{text cs}, @{text vs},
@{text s}, @{text f}, and @{text x} as the previous functions, and returns the set of the
\emph{tags}, namely of the pairs @{text "(y, m)"} where @{text y} is a variable and @{text m} is a
natural number, such that the @{text m}-th input instruction @{text "IN y"} within flow @{text cs}
is allowed to affect the value of variable @{text x} resulting from the execution of @{text cs} if
it starts from the initial state @{text s} and the initial trace of inputs @{text vs}, and takes
place according to the stream of input values @{text f}.

In more detail, the set of tags @{text "tags cs vs s f x"} contains a tag @{text "(y, m)"} just in
case there exist a descending sequence of left sublists @{text "cs\<^sub>n\<^sub>+\<^sub>1"}, @{term "cs\<^sub>n @ [c\<^sub>n]"}, ...,
@{term "cs\<^sub>1 @ [c\<^sub>1]"} of @{text cs} and a sequence of variables @{text "y\<^sub>n\<^sub>+\<^sub>1"}, ..., @{text y\<^sub>1}, where
$n \ge 1$, @{text "cs\<^sub>n\<^sub>+\<^sub>1 = cs"}, @{text "y\<^sub>n\<^sub>+\<^sub>1 = x"}, @{text "y\<^sub>1 = y"}, and @{text "y = x"} if $n = 1$,
satisfying the following conditions.

  \<^item> For each integer $i$, if any, such that $1 < i \le n$, the instruction @{text "c\<^sub>i"} is an
assignment @{text "y\<^sub>i\<^sub>+\<^sub>1 ::= a\<^sub>i"} such that:

    \<^item> @{prop "y\<^sub>i \<in> avars a\<^sub>i"},

    \<^item> @{text "run_flow cs\<^sub>i vs s f: dom y\<^sub>i \<leadsto> dom y\<^sub>i\<^sub>+\<^sub>1"}, and

    \<^item> the right sublist of @{text "cs\<^sub>i\<^sub>+\<^sub>1"} complementary to @{term "cs\<^sub>i @ [c\<^sub>i]"} does not comprise
any assignment or input instruction setting variable @{text "y\<^sub>i\<^sub>+\<^sub>1"} (as the assignment @{text "c\<^sub>i"}
would otherwise be irrelevant),

  or else an observation @{term "\<langle>X\<^sub>i\<rangle>"} such that:

    \<^item> @{prop "y\<^sub>i \<in> X\<^sub>i"} and

    \<^item> @{text "run_flow cs\<^sub>i vs s f: dom y\<^sub>i \<leadsto> dom y\<^sub>i\<^sub>+\<^sub>1"}.

  \<^item> The instruction @{text "c\<^sub>1"} is the @{text m}-th input instruction @{text "IN y"} within flow
@{text cs}.

  \<^item> The right sublist of @{text "cs\<^sub>2"} complementary to @{term "cs\<^sub>1 @ [c\<^sub>1]"} does not comprise any
assignment or input instruction setting variable @{text y} (as the input instruction @{text "c\<^sub>1"}
would otherwise be irrelevant).

\null
\<close>

function
  tags :: "flow \<Rightarrow> inputs \<Rightarrow> state \<Rightarrow> stream \<Rightarrow> vname \<Rightarrow> tag set" and
  tags_aux :: "flow \<Rightarrow> inputs \<Rightarrow> state \<Rightarrow> stream \<Rightarrow> vname \<Rightarrow> tag set"
where

"tags (cs @ [c]) vs s f x = (case c of
  z ::= a \<Rightarrow> if z = x
    then tags_aux cs vs s f x \<union> \<Union> {tags cs vs s f y | y.
      run_flow cs vs s f: dom y \<leadsto> dom x \<and> y \<in> avars a}
    else tags cs vs s f x |
  IN z \<Rightarrow> if z = x
    then insert (x, length [c\<leftarrow>cs. c = IN x]) (tags_aux cs vs s f x)
    else tags cs vs s f x |
  \<langle>X\<rangle> \<Rightarrow>
    tags cs vs s f x \<union> \<Union> {tags cs vs s f y | y.
      run_flow cs vs s f: dom y \<leadsto> dom x \<and> y \<in> X} |
  _ \<Rightarrow>
    tags cs vs s f x)" |

"tags [] _ _ _ _ = {}" |

"tags_aux (cs @ [c]) vs s f x = (case c of
  \<langle>X\<rangle> \<Rightarrow>
    tags_aux cs vs s f x \<union> \<Union> {tags cs vs s f y | y.
      run_flow cs vs s f: dom y \<leadsto> dom x \<and> y \<in> X} |
  _ \<Rightarrow>
    tags_aux cs vs s f x)" |

"tags_aux [] _ _ _ _ = {}"

proof atomize_elim
  fix a :: "flow \<times> inputs \<times> state \<times> stream \<times> vname +
    flow \<times> inputs \<times> state \<times> stream \<times> vname"
  show
   "(\<exists>cs c vs s f x. a = Inl (cs @ [c], vs, s, f, x)) \<or>
    (\<exists>vs s f x. a = Inl ([], vs, s, f, x)) \<or>
    (\<exists>cs c vs s f x. a = Inr (cs @ [c], vs, s, f, x)) \<or>
    (\<exists>vs s f x. a = Inr ([], vs, s, f, x))"
    by (metis obj_sumE prod_cases3 rev_exhaust)
qed auto

termination by lexicographic_order

lemmas tags_induct = tags_tags_aux.induct

text \<open>
\null

Finally, function @{text tags_out}, defined here below, takes the same parameters @{text cs},
@{text vs}, @{text s}, @{text f}, and @{text x} as the previous functions, and returns the set of
the tags @{text "(y, m)"} such that the @{text m}-th input instruction @{text "IN y"} within flow
@{text cs} is allowed to affect the outputs of variable @{text x} possibly occurring as a result of
the execution of flow @{text cs} if it starts from the initial state @{text s} and the initial trace
of inputs @{text vs}, and takes place according to the stream of input values @{text f}.

In more detail, the set of tags @{text "tags_out cs vs s f x"} is defined as the union of any set of
tags @{text "tags cs\<^sub>i vs s f x\<^sub>i"}, where @{term "cs\<^sub>i @ [c\<^sub>i]"} is any left sublist of @{text cs} such
that the instruction @{text "c\<^sub>i"} is an output instruction @{text "OUT x"}, in which case
@{text "x\<^sub>i = x"}, or else an observation @{term "\<langle>X\<^sub>i\<rangle>"} such that:

  \<^item> @{prop "x\<^sub>i \<in> X\<^sub>i"} and

  \<^item> @{text "run_flow cs\<^sub>i vs s f: dom x\<^sub>i \<leadsto> dom x"}.

\null
\<close>

function
  tags_out :: "flow \<Rightarrow> inputs \<Rightarrow> state \<Rightarrow> stream \<Rightarrow> vname \<Rightarrow> tag set"
where

"tags_out (cs @ [c]) vs s f x = (case c of
  OUT z \<Rightarrow>
    tags_out cs vs s f x \<union> (if z = x then tags cs vs s f x else {}) |
  \<langle>X\<rangle> \<Rightarrow>
    tags_out cs vs s f x \<union> \<Union> {tags cs vs s f y | y.
      run_flow cs vs s f: dom y \<leadsto> dom x \<and> y \<in> X} |
  _ \<Rightarrow>
    tags_out cs vs s f x)" |

"tags_out [] _ _ _ _ = {}"

by (atomize_elim, auto intro: rev_cases)
termination by lexicographic_order

text \<open>
\null

Predicate @{text correct}, defined here below, formalizes the extended termination-sensitive
information flow correctness criterion. As in my previous paper \<^cite>\<open>"Noce24"\<close>, its parameters
consist of a program @{text c}, a set of program states @{text A}, and a set of variables @{text X}.

In more detail, for any state @{text s} agreeing with a state in @{text A} on the value of each
state variable contained in @{text X}, let the small-step semantics turn:

  \<^item> the command @{text c} and the program execution stage @{text "(s, f, vs, ws)"} into a command
@{text "c\<^sub>1"} and a program execution stage @{text "(s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1)"}, and

  \<^item> the command @{text c\<^sub>1} and the program execution stage @{text "(s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1)"} into a command
@{text "c\<^sub>2"} and a program execution stage @{text "(s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)"}.

Furthermore, let:

  \<^item> @{text cs} be the program execution flow leading from @{text "(c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1)"} to
@{text "(c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2)"}, and

  \<^item> @{text "(t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1')"} be any program execution stage,

and assume that the following conditions hold.

  \<^item> @{text S} is a nonempty subset of the set of the variables @{text x} such that state
@{text "t\<^sub>1"} agrees with @{text "s\<^sub>1"} on the value of each variable contained in
@{term "sources cs vs\<^sub>1 s\<^sub>1 f x"}.

  \<^item> For each variable @{text x} contained in @{text S}, and each tag @{text "(y, n)"} contained in
@{term "tags cs vs\<^sub>1 s\<^sub>1 f x"}, the stream of input values @{text f'} agrees with @{text f} on the
input value assigned to variable @{text y} by an input instruction @{text "IN y"} after @{text n}
previous such assignments to @{text y} following any one tracked by the starting trace of inputs
@{text vs\<^sub>1'} and @{text "vs\<^sub>1"}, respectively.

Then, the information flow is correct only if the small-step semantics turns the command
@{text "c\<^sub>1"} and the program execution stage @{text "(t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1')"} into a command
@{text "c\<^sub>2'"} and a program execution stage @{text "(t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2')"} satisfying the following
correctness conditions.

  \<^item> @{prop "c\<^sub>2' = SKIP"} just in case @{prop "c\<^sub>2 = SKIP"}; namely, program execution terminates just
in case it terminates as a result of the execution of flow @{text cs}, so that the two program
executions cannot be distinguished based on program termination.

  \<^item> The resulting sequence of input requests @{text "IN x"} being prompted, where @{text x} is any
variable contained in @{text S}, matches the one triggered by the execution of flow @{text cs}, so
that the two program executions cannot be distinguished based on those sequences.

  \<^item> States @{text "t\<^sub>2"} and @{text "s\<^sub>2"} agree on the value of each variable contained in @{text S},
so that the two program executions cannot be distinguished based on the resulting program states.

Likewise, if the above assumptions hold for functions @{const sources_out} and @{const tags_out}
in place of functions @{const sources} and @{const tags}, respectively, then the information flow
correctness requires the first two correctness conditions listed above to hold as well, plus the
following one.

  \<^item> The resulting sequence of outputs of any variable contained in @{text S} matches the one
produced by the execution of flow @{text cs}, so that the two program executions cannot be
distinguished based on those sequences.

\null
\<close>

abbreviation ok_flow_1 where
"ok_flow_1 c\<^sub>1 c\<^sub>2 c\<^sub>2' s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' cs \<equiv>
  \<forall>S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources cs vs\<^sub>1 s\<^sub>1 f x)}.
    S \<noteq> {} \<longrightarrow>
    f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', \<Union> {tags cs vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S}) \<longrightarrow>
      (c\<^sub>1, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (c\<^sub>2', t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2') \<and>
      (c\<^sub>2 = SKIP) = (c\<^sub>2' = SKIP) \<and>
      map fst [p\<leftarrow>drop (length vs\<^sub>1) vs\<^sub>2. fst p \<in> S] =
        map fst [p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>2'. fst p \<in> S] \<and>
      s\<^sub>2 = t\<^sub>2 (\<subseteq> S)"

abbreviation ok_flow_2 where
"ok_flow_2 c\<^sub>1 c\<^sub>2 c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' cs \<equiv>
  \<forall>S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_out cs vs\<^sub>1 s\<^sub>1 f x)}.
    S \<noteq> {} \<longrightarrow>
    f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', \<Union> {tags_out cs vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S}) \<longrightarrow>
      (c\<^sub>1, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (c\<^sub>2', t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2') \<and>
      (c\<^sub>2 = SKIP) = (c\<^sub>2' = SKIP) \<and>
      map fst [p\<leftarrow>drop (length vs\<^sub>1) vs\<^sub>2. fst p \<in> S] =
        map fst [p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>2'. fst p \<in> S] \<and>
      [p\<leftarrow>drop (length ws\<^sub>1) ws\<^sub>2. fst p \<in> S] =
        [p\<leftarrow>drop (length ws\<^sub>1') ws\<^sub>2'. fst p \<in> S]"

abbreviation ok_flow where
"ok_flow c\<^sub>1 c\<^sub>2 s\<^sub>1 s\<^sub>2 f vs\<^sub>1 vs\<^sub>2 ws\<^sub>1 ws\<^sub>2 cs \<equiv>
  \<forall>t\<^sub>1 f' vs\<^sub>1' ws\<^sub>1'. \<exists>c\<^sub>2' t\<^sub>2 vs\<^sub>2' ws\<^sub>2'.
    ok_flow_1 c\<^sub>1 c\<^sub>2 c\<^sub>2' s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' cs \<and>
    ok_flow_2 c\<^sub>1 c\<^sub>2 c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' cs"

definition correct :: "com \<Rightarrow> state set \<Rightarrow> vname set \<Rightarrow> bool" where
"correct c A X \<equiv>
  \<forall>s \<in> Univ A (\<subseteq> state \<inter> X). \<forall>c\<^sub>1 c\<^sub>2 s\<^sub>1 s\<^sub>2 f vs vs\<^sub>1 vs\<^sub>2 ws ws\<^sub>1 ws\<^sub>2 cfs.
    (c, s, f, vs, ws) \<rightarrow>* (c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<and>
    (c\<^sub>1, s\<^sub>1, f, vs\<^sub>1, ws\<^sub>1) \<rightarrow>*{cfs} (c\<^sub>2, s\<^sub>2, f, vs\<^sub>2, ws\<^sub>2) \<longrightarrow>
      ok_flow c\<^sub>1 c\<^sub>2 s\<^sub>1 s\<^sub>2 f vs\<^sub>1 vs\<^sub>2 ws\<^sub>1 ws\<^sub>2 (flow cfs)"


abbreviation noninterf_set :: "state set \<Rightarrow> vname set \<Rightarrow> vname set \<Rightarrow> bool"
  ("(_: _ \<leadsto>| _)" [51, 51, 51] 50) where
"A: X \<leadsto>| Y \<equiv> \<forall>y \<in> Y. \<exists>s \<in> A. \<exists>x \<in> X. \<not> s: dom x \<leadsto> dom y"

abbreviation ok_flow_aux_1 where
"ok_flow_aux_1 c\<^sub>1 c\<^sub>2 c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' cs \<equiv>
  \<forall>S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_aux cs vs\<^sub>1 s\<^sub>1 f x)}.
    S \<noteq> {} \<longrightarrow>
    f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', \<Union> {tags_aux cs vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S}) \<longrightarrow>
      (c\<^sub>1, t\<^sub>1, f', vs\<^sub>1', ws\<^sub>1') \<rightarrow>* (c\<^sub>2', t\<^sub>2, f', vs\<^sub>2', ws\<^sub>2') \<and>
      (c\<^sub>2 = SKIP) = (c\<^sub>2' = SKIP) \<and>
      map fst [p\<leftarrow>drop (length vs\<^sub>1) vs\<^sub>2. fst p \<in> S] =
        map fst [p\<leftarrow>drop (length vs\<^sub>1') vs\<^sub>2'. fst p \<in> S]"

abbreviation ok_flow_aux_2 where
"ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' cs \<equiv>
  \<forall>S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources cs vs\<^sub>1 s\<^sub>1 f x)}.
    S \<noteq> {} \<longrightarrow>
    f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', \<Union> {tags cs vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S}) \<longrightarrow>
      s\<^sub>2 = t\<^sub>2 (\<subseteq> S)"

abbreviation ok_flow_aux_3 where
"ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' cs \<equiv>
  \<forall>S \<subseteq> {x. s\<^sub>1 = t\<^sub>1 (\<subseteq> sources_out cs vs\<^sub>1 s\<^sub>1 f x)}.
    S \<noteq> {} \<longrightarrow>
    f = f' (\<subseteq> vs\<^sub>1, vs\<^sub>1', \<Union> {tags_out cs vs\<^sub>1 s\<^sub>1 f x | x. x \<in> S}) \<longrightarrow>
      [p\<leftarrow>drop (length ws\<^sub>1) ws\<^sub>2. fst p \<in> S] =
        [p\<leftarrow>drop (length ws\<^sub>1') ws\<^sub>2'. fst p \<in> S]"

abbreviation ok_flow_aux :: "config set \<Rightarrow> com \<Rightarrow> com \<Rightarrow> state \<Rightarrow> state \<Rightarrow>
  stream \<Rightarrow> inputs \<Rightarrow> inputs \<Rightarrow> outputs \<Rightarrow> outputs \<Rightarrow> flow \<Rightarrow> bool"
where
"ok_flow_aux U c\<^sub>1 c\<^sub>2 s\<^sub>1 s\<^sub>2 f vs\<^sub>1 vs\<^sub>2 ws\<^sub>1 ws\<^sub>2 cs \<equiv>
  (\<forall>t\<^sub>1 f' vs\<^sub>1' ws\<^sub>1'. \<exists>c\<^sub>2' t\<^sub>2 vs\<^sub>2' ws\<^sub>2'.
    ok_flow_aux_1 c\<^sub>1 c\<^sub>2 c\<^sub>2' s\<^sub>1 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' vs\<^sub>2 vs\<^sub>2' ws\<^sub>1' ws\<^sub>2' cs \<and>
    ok_flow_aux_2 s\<^sub>1 s\<^sub>2 t\<^sub>1 t\<^sub>2 f f' vs\<^sub>1 vs\<^sub>1' cs \<and>
    ok_flow_aux_3 s\<^sub>1 t\<^sub>1 f f' vs\<^sub>1 vs\<^sub>1' ws\<^sub>1 ws\<^sub>1' ws\<^sub>2 ws\<^sub>2' cs) \<and>
  (\<forall>Y. (\<exists>(A, X) \<in> U. A: X \<leadsto>| Y) \<longrightarrow> no_upd cs Y)"

text \<open>
\null

In addition to the equations handling the further constructs of the considered extension of language
IMP, the auxiliary recursive function @{text ctyping1_aux} used to define the idempotent type system
@{text ctyping1} differs from its counterpart used in my previous paper \<^cite>\<open>"Noce24"\<close> also in that
it records any update of a state variable using a pair of type @{typ "vname \<times> val option"}, where
the first component is the state variable being updated, and the latter one matches @{term "Some i"}
or @{const None} depending on whether its new value can be evaluated to an integer @{text i} at
compile time or not.

Apart from the aforesaid type change, the equations for the constructs included in the original
language IMP are the same as in my previous paper \<^cite>\<open>"Noce24"\<close>, whereas the equations for the
additional constructs of the considered language extension are as follows.

  \<^item> The equation for an input instruction @{text "IN x"}, like the one handling assignments, records
the update of variable @{text x} just in case it is a state variable (as otherwise its update cannot
change the applying interference relation). If so, its update is recorded with @{term "(x, None)"},
since input values cannot be evaluated at compile time.

  \<^item> The equation for an output instruction @{text "OUT x"} does not record any update, since output
instructions leave the program state unchanged.

  \<^item> The equation for a nondeterministic choice @{term "c\<^sub>1 OR c\<^sub>2"} sets the returned value to
@{text "\<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2"}, in the same way as the equation for a conditional statement
@{term "IF b THEN c\<^sub>1 ELSE c\<^sub>2"} whose boolean condition @{text b} cannot be evaluated at compile time.

As in my previous paper \<^cite>\<open>"Noce24"\<close>, the @{typ "state set"} returned by @{text ctyping1} is
defined so that any \emph{indeterminate} state variable (namely, any state variable @{text x} with a
latest recorded update @{term "(x, None)"}) may take an arbitrary value. Of course, a real-world
implementation of this type system would not need to actually return a distinct state for any such
value, but rather just to mark any indeterminate state variable in each returned state with some
special value standing for \emph{arbitrary}.

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


inductive_set ctyping1_merge_aux :: "state_upd list set \<Rightarrow>
  state_upd list set \<Rightarrow> (state_upd list \<times> bool) list set"
  (infix "\<Squnion>" 55) for A and B where

 "xs \<in> A \<Longrightarrow> [(xs, True)] \<in> A \<Squnion> B" |

 "ys \<in> B \<Longrightarrow> [(ys, False)] \<in> A \<Squnion> B" |

 "\<lbrakk>ws \<in> A \<Squnion> B; \<not> snd (hd ws); xs \<in> A; (xs, True) \<notin> set ws\<rbrakk> \<Longrightarrow>
    (xs, True) # ws \<in> A \<Squnion> B" |

 "\<lbrakk>ws \<in> A \<Squnion> B; snd (hd ws); ys \<in> B; (ys, False) \<notin> set ws\<rbrakk> \<Longrightarrow>
    (ys, False) # ws \<in> A \<Squnion> B"

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

"\<turnstile> x ::= a = (if x \<in> state
  then {[(x, if avars a = {} then Some (aval a (\<lambda>x. 0)) else None)]}
  else {[]})" |

"\<turnstile> IN x = (if x \<in> state then {[(x, None)]} else {[]})" |

"\<turnstile> OUT x = {[]}" |

"\<turnstile> c\<^sub>1;; c\<^sub>2 = \<turnstile> c\<^sub>1 \<squnion>\<^sub>@ \<turnstile> c\<^sub>2" |

"\<turnstile> c\<^sub>1 OR c\<^sub>2 = \<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2" |

"\<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 = (let f = \<turnstile> b in
  (if f \<in> {Some True, None} then \<turnstile> c\<^sub>1 else {}) \<squnion>
  (if f \<in> {Some False, None} then \<turnstile> c\<^sub>2 else {}))" |

"\<turnstile> WHILE b DO c = (let f = \<turnstile> b in
  (if f \<in> {Some False, None} then {[]} else {}) \<union>
  (if f \<in> {Some True, None} then \<turnstile> c else {}))"

definition ctyping1 :: "com \<Rightarrow> state set \<Rightarrow> vname set \<Rightarrow> config"
  ("(\<turnstile> _ '(\<subseteq> _, _'))" [51] 55) where
"\<turnstile> c (\<subseteq> A, X) \<equiv> let F = {\<lambda>x. [y\<leftarrow>ys. fst y = x] | ys. ys \<in> \<turnstile> c} in
  ({\<lambda>x. if f x = []
     then s x else case snd (last (f x)) of None \<Rightarrow> t x | Some i \<Rightarrow> i |
       f s t. f \<in> F \<and> s \<in> A},
   Univ?? A {x. \<forall>f \<in> F. if f x = []
     then x \<in> X else snd (last (f x)) \<noteq> None})"

text \<open>
\null

Finally, in the recursive definition of the main type system @{text ctyping2}, the equations dealing
with the constructs included in the original language IMP are the same as in my previous paper
\<^cite>\<open>"Noce24"\<close>, whereas the equations for the additional constructs of the considered language
extension are as follows.

  \<^item> The equation for an input instruction @{text "IN x"} sets the returned value to a \emph{pass}
verdict @{term "Some (B, Y)"} just in case each set of variables in the current scope is allowed to
affect variable @{text x} in the associated set of program states. If so, then the sets @{text B}
and @{text Y} are computed in the same way as with an assignment whose right-hand expression cannot
be evaluated at compile time, since input values cannot be evaluated at compile time, too.

  \<^item> The equation for an output instruction @{text "OUT x"} sets the returned value to a \emph{pass}
verdict @{term "Some (B, Y)"} just in case each set of variables in the current scope is allowed to
affect variable @{text x} in the associated set of program states. If so, then the sets @{text B}
and @{text Y} are computed in the same way as with a @{const SKIP} command, as output instructions
leave the program state unchanged, too.

  \<^item> The equation for a nondeterministic choice @{term "c\<^sub>1 OR c\<^sub>2"} sets the returned value to a
\emph{pass} verdict @{term "Some (B, Y)"} just in case \emph{pass} verdicts are returned for both
branches. If so, then the sets @{text B} and @{text Y} are computed in the same way as with a
conditional statement @{term "IF b THEN c\<^sub>1 ELSE c\<^sub>2"} whose boolean condition @{text b} cannot be
evaluated at compile time.

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

definition btyping2 ::
 "bexp \<Rightarrow> state set \<Rightarrow> vname set \<Rightarrow> state set \<times> state set"
  ("(\<Turnstile> _ '(\<subseteq> _, _'))" [51] 55) where
"\<Turnstile> b (\<subseteq> A, X) \<equiv> case \<TTurnstile> b (\<subseteq> A, X) of
  Some A' \<Rightarrow> (A', A - A') | _ \<Rightarrow> (A, A)"


abbreviation interf_set :: "state set \<Rightarrow> vname set \<Rightarrow> vname set \<Rightarrow> bool"
  ("(_: _ \<leadsto> _)" [51, 51, 51] 50) where
"A: X \<leadsto> Y \<equiv> \<forall>s \<in> A. \<forall>x \<in> X. \<forall>y \<in> Y. s: dom x \<leadsto> dom y"

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
 (if \<forall>(B, Y) \<in> insert (Univ? A X, avars a) U. B: Y \<leadsto> {x}
  then Some (if x \<in> state \<and> A \<noteq> {}
    then if v \<Turnstile> a (\<subseteq> X)
      then ({s(x := aval a s) | s. s \<in> A}, insert x X) else (A, X - {x})
    else (A, Univ?? A X))
  else None)" |

"(U, v) \<Turnstile> IN x (\<subseteq> A, X) =
 (if \<forall>(B, Y) \<in> U. B: Y \<leadsto> {x}
  then Some (if x \<in> state \<and> A \<noteq> {}
    then (A, X - {x}) else (A, Univ?? A X))
  else None)" |

"(U, v) \<Turnstile> OUT x (\<subseteq> A, X) =
 (if \<forall>(B, Y) \<in> U. B: Y \<leadsto> {x}
  then Some (A, Univ?? A X)
  else None)" |

"(U, v) \<Turnstile> c\<^sub>1;; c\<^sub>2 (\<subseteq> A, X) =
 (case (U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X) of
    Some (B, Y) \<Rightarrow> (U, v) \<Turnstile> c\<^sub>2 (\<subseteq> B, Y) | _ \<Rightarrow> None)" |

"(U, v) \<Turnstile> c\<^sub>1 OR c\<^sub>2 (\<subseteq> A, X) =
 (case ((U, v) \<Turnstile> c\<^sub>1 (\<subseteq> A, X), (U, v) \<Turnstile> c\<^sub>2 (\<subseteq> A, X)) of
    (Some (C\<^sub>1, Y\<^sub>1), Some (C\<^sub>2, Y\<^sub>2)) \<Rightarrow> Some (C\<^sub>1 \<union> C\<^sub>2, Y\<^sub>1 \<inter> Y\<^sub>2) |
    _ \<Rightarrow> None)" |

"(U, v) \<Turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2 (\<subseteq> A, X) =
 (case (insert (Univ? A X, bvars b) U, \<Turnstile> b (\<subseteq> A, X)) of (U', B\<^sub>1, B\<^sub>2) \<Rightarrow>
    case ((U', v) \<Turnstile> c\<^sub>1 (\<subseteq> B\<^sub>1, X), (U', v) \<Turnstile> c\<^sub>2 (\<subseteq> B\<^sub>2, X)) of
      (Some (C\<^sub>1, Y\<^sub>1), Some (C\<^sub>2, Y\<^sub>2)) \<Rightarrow> Some (C\<^sub>1 \<union> C\<^sub>2, Y\<^sub>1 \<inter> Y\<^sub>2) |
      _ \<Rightarrow> None)" |

"(U, v) \<Turnstile> WHILE b DO c (\<subseteq> A, X) = (case \<Turnstile> b (\<subseteq> A, X) of (B\<^sub>1, B\<^sub>2) \<Rightarrow>
  case \<turnstile> c (\<subseteq> B\<^sub>1, X) of (C, Y) \<Rightarrow> case \<Turnstile> b (\<subseteq> C, Y) of (B\<^sub>1', B\<^sub>2') \<Rightarrow>
    if \<forall>(B, W) \<in> insert (Univ? A X \<union> Univ? C Y, bvars b) U. B: W \<leadsto> UNIV
    then case (({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1, X), ({}, False) \<Turnstile> c (\<subseteq> B\<^sub>1', Y)) of
      (Some _, Some _) \<Rightarrow> Some (B\<^sub>2 \<union> B\<^sub>2', Univ?? B\<^sub>2 X \<inter> Y) |
      _ \<Rightarrow> None
    else None)"

end

end
