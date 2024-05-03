(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *)

(*<*)
theory Chapter2_HoareHeap
imports "AutoCorres2.AutoCorres"
begin

(*>*)

section  \<open>More Complex Functions with AutoCorres\<close>

text \<open>

  In the previous section we saw how to use the C-Parser and AutoCorres
  to prove properties about some very simple C programs.

  Real life C programs tend to be far more complex however; they
  read and write to local variables, have loops and use pointers to
  access the heap. In this section we will look at some simple programs
  which use loops and access the heap to show how AutoCorres can
  allow such constructs to be reasoned about.

\<close>

subsection \<open>A simple loop: \texttt{mult\_by\_add}\<close>

text \<open>

  Our C function \texttt{mult\_by\_add} implements a multiply operation
  by successive additions:

\lstinputlisting[language=C, firstline=11]{mult_by_add.c}

  We start by translating the program using the C parser and AutoCorres,
  and entering the generated locale \texttt{mult\_by\_add}.
\<close>

install_C_file "sources/mult_by_add.c"
autocorres [ts_rules = nondet] "mult_by_add.c"
(*<*)
context mult_by_add_all_corres begin
(*>*)

text \<open>
  The C parser produces the SIMPL output as follows:
\<close>

thm mult_by_add_body_def
text \<open>@{thm [display] mult_by_add_body_def}\<close>

text \<open>
  Which is abstracted by AutoCorres to the following:
\<close>

thm mult_by_add'_def
text \<open>@{thm [display] mult_by_add'_def }\<close>

text \<open>

  In this case AutoCorres has abstracted \texttt{mult\_by\_add} into a
  \emph{monadic} form. Monads are a pattern frequently used in
  functional programming to represent imperative-style control-flow; an
  in-depth introduction to monads can be found elsewhere.

  The monads used by AutoCorres in this example is a
  \emph{non-deterministic state monad};  program state is implicitly
  passed between each statement, and results of computations may produce
  more than one (or possibly zero) results\footnote{Non-determinism
  becomes useful when modelling hardware, for example, where the exact
  results of the hardware cannot be determined ahead of time.}.

  The HOL type is called specification monad: @{typ "('e, 'a, 's) spec_monad"}, where
  \<^item> \<^typ>\<open>'e\<close> type for exception / error results,
  \<^item> \<^typ>\<open>'r\<close> type of the result and
  \<^item> \<^typ>\<open>'s\<close> type of the state.

  When \<^typ>\<open>'e\<close> is instantiated with the unit type \<^typ>\<open>unit\<close>, there is an abbreviation
  @{typ "('a, 's) res_monad"}, for \<^emph>\<open>result monad\<close>, When it is instantiated with a proper
  type we have an abbreviation @{typ "('e, 'a, 's) exn_monad"}, for \<^emph>\<open>exception monad\<close>.

  To uniformly model results and exceptions as values the type 
  @{typ "('e, 'a) exception_or_result"} is used. It is constructed as a sum type where we
  exclude a default value from the exception type \<^typ>\<open>'e\<close>. So when \<^typ>\<open>'e\<close> is instantiated
  with \<^typ>\<open>unit\<close> the type is isomorphic to the result type \<^typ>\<open>'a\<close>. Type \<^typ>\<open>unit\<close> is only inhabited
  by the unique unit value \<^term>\<open>()\<close> which is also default value. This instance is abbreviated with
  \<^typ>\<open>'a val\<close>. For proper exceptions we instantiate \<^typ>\<open>'e\<close> with an option type \<^typ>\<open>'x option\<close>.
  This instance is abbreviated with \<^typ>\<open>('x, 'a) xval\<close>.

  Constructors and pattern matching:
  \<^item>\<^typ>\<open>('e, 'a) exception_or_result\<close>:\<^term>\<open>Exception e\<close>, \<^term>\<open>Result v\<close>, and pattern matching
    @{term [eta_contract=false] \<open>\<lambda>Exception e \<Rightarrow> f e | Result v \<Rightarrow> g v\<close>}
  \<^item>\<^typ>\<open>'a val\<close>:\<^term>\<open>Result v::'a val\<close>, with pattern matching 
    @{term [eta_contract=false] "\<lambda>Res v. g v"}
  \<^item>\<^typ>\<open>('e, 'a) xval\<close>: \<^term>\<open>Exn e\<close>, \<^term>\<open>Result v\<close>, and pattern matching
    @{term [eta_contract=false] \<open>\<lambda>Exn e \<Rightarrow> f e | Result v \<Rightarrow> g v\<close>}

  This enconding allows us to give a uniform definition of the monadic \<^const>\<open>bind\<close> which works for 
  the generic specification monad and thus also for its instances the result and the exception monad.
\<close>

subsubsection \<open>'Hoare Triples'\<close>

text \<open>
  The bulk of @{term "mult_by_add'"} is wrapped inside the @{term
  "whileLoop"} \emph{monad combinator}, which is really just a fancy way
  of describing the method used by AutoCorres to encode (potentially
  non-terminating) loops using monads.

  If we want to describe the behaviour of this program, we can use
  Hoare logic as follows:

    @{term [display] "P s \<Longrightarrow> mult_by_add' a b \<bullet> s \<lbrace> Q \<rbrace>"}

  This predicate states that, assuming @{term "P"} holds on the initial
  program state, if we execute @{term "mult_by_add' a b"}, then
  @{term "Q"} will hold on the final state of the program.

  There are a few details: while @{term "P"} has type
  @{typ "'s \<Rightarrow> bool"} (i.e., takes a state and returns true if
  it satisifies the precondition), @{term "Q"} has an additional
  parameter @{typ "'r \<Rightarrow> 's \<Rightarrow> bool"}. The additional parameter
  @{typ "'r"} is the \emph{return value} of the function; so, in
  our \<^const>\<open>mult_by_add'\<close> example, it will be the result of
  the multiplication. Note that the precondition is not part of the 'hoare-triple' but is
  an ordinary Isabelle assumption on the initial state \<^term>\<open>s\<close>. That way we can
  directly use Isabelle/Isar to decompose the precondition and can also refer to the initial state 
  within the postcondition.
  The foundational constant for this hoare triple is \<^const>\<open>runs_to\<close>
  which means total correctness: we have to proof that the program terminates and that
  there is no undefined behaviour (all guards must hold).
  There is also a weaker notion for partial correctness \<^const>\<open>runs_to_partial\<close> with syntax
  \<^term>\<open>f \<bullet> s ?\<lbrace> Q \<rbrace>\<close>. 

  For example one useful property to prove on our program would
  be:

    @{term [display] " mult_by_add' a b \<bullet> s \<lbrace> \<lambda>Res r _. r = a * b \<rbrace>"}

  That is, for all possible input states, our \texttt{mult\_by\_add'}
  function returns the product of @{term "a"} and @{term "b"}.
 
  Our proof of @{term mult_by_add'} could then proceed as follows:

\<close>

lemma mult_by_add_correct:
    "mult_by_add' a b \<bullet> s \<lbrace> \<lambda>Res r _. r = a * b \<rbrace>"
  txt \<open>Unfold abstracted definition\<close>
  apply (unfold mult_by_add'_def)
  txt \<open>Annotate the loop with an invariant and a measure, by adding a specialised rule
    to the verification condition generator.\<close>
  supply runs_to_whileLoop_res [where  
      I="\<lambda>(a', result) s. result = (a - a') * b" and 
      R="measure' (\<lambda>((a', result), s). a')", runs_to_vcg]
  txt \<open>Run the ``verification condition generator''.\<close>
  apply (runs_to_vcg)
  txt \<open>Solve the program correctness goals.\<close>
     apply (simp add: field_simps)
    apply unat_arith
   apply (auto simp: field_simps not_less)
  done


text \<open>
  The main tool is the proof method @{method runs_to_vcg}, a 
  verification condition generator for monadic programs. It uses
  weakest precondition style rules which are collected in named theorems collection
  @{thm[source] runs_to_vcg}.
  In that collection there is no rule for \<^const>\<open>whileLoop\<close>. The verification
  generator will stop there unless you specify a rule to use.
  This was done in the proof above by instantiating the rule @{thm[source] runs_to_whileLoop_res}
  with an invariant and a measure and by adding it to the verification condition generator
  via attribute @{attribute "runs_to_vcg"}.
  We finally discharge the remaining subgoals left from
  @{method runs_to_vcg} with standard proof tools of Isabelle.

  In the next section, we will look at how we can use AutoCorres to
  verify a C program that reads and writes to the heap.

\<close>

(*<*)
end
end
(*>*)
