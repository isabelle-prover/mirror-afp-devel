(*  Title:      manual.thy
    Author:     Andreas Viktor Hess, DTU
    Author:     Sebastian A. Mödersheim, DTU
    Author:     Achim D. Brucker, University of Exeter
    Author:     Anders Schlichtkrull, DTU
    SPDX-License-Identifier: BSD-3-Clause
*)

(*<*)
theory 
  "manual"
imports 
  "KeyserverEx"
begin 
(*>*)
section\<open>Common Pitfalls\label{sec:commonpitfalls}\<close>
text\<open>
This section explains some common pitfalls, along with solutions, that one may encounter when
writing trac specifications.
\<close>

subsection\<open>Not Including an Initial Value-Producing Transaction\<close>
text\<open>
Trac specifications that contain value-typed variables should also declare a transaction that
produces fresh values.
Take, for instance, a trac specification that contains only one transaction:

\begin{trac}
Transactions:
attackDef(PK:value)
    receive PK
    attack.
\end{trac}

This protocol is technically secure because no values are ever produced.
Similarly, if we just look at the protocol with the following transaction then we find that it is
also secure:
\begin{trac}
Transactions:
attackDef(PK:value)
    attack.
\end{trac}

The reason it is secure is because of the occurs-message transformation that is being applied to
each transaction $T$ of the protocol for technical reasons:
A \inlinetrac|receive occurs(PK)| action is added to $T$ for each value-typed variable PK declared in
$T$, and a \inlinetrac|send occurs(PK)| is added to $T$ for each \inlinetrac|new PK| action occurring in $T$.
Since no values are actually produced in any protocol run, then no occurs-message is produced, and
so the attackDef transaction cannot ever be applied.
One would, however, naturally expect that such a protocol is not secure.
For this reason we require that each trac specification includes a value-producing transaction if
there are any value-typed variables occurring in the trac specification at all.
For instance, when including such a transaction to our example we get a valid trac transaction
specification:
\begin{trac}
Transactions:
valueProducer()
    new PK
    send PK.

attackDef1(PK:value)
    attack.
\end{trac}

Another example is the following which is also a valid trac transaction specification because it
does not declare any value-typed variables:

\begin{trac}
Transactions:
attackDef2()
    attack.
\end{trac}

Both protocols have attacks, as expected.
Examining the generated Isabelle definitions reveals that the \inlinetrac|valueProducer| transaction
produces an occurs message while the \inlinetrac|attackDef1| transaction expects to receive an occurs
message:\<close>
trac\<open>
Protocol: ex1

Enumerations:
dummy_type = {dummy_constant}

Sets:
dummy_set/0

Transactions:
valueProducer()
    new PK
    send PK.

attackDef1(PK:value)
    attack.
\<close>
thm ex1_transaction_valueProducer_def
thm ex1_transaction_attackDef1_def

subsection\<open>Using Value-Typed Database-Parameters in Database-Expressions\<close>
text\<open>
Due to the nature of the abstraction that is at the core of our verification approach it is simply
not possible to use value-typed variables in parameters to databases.
Hence, a trac specification with the following transaction would be rejected:
\begin{trac}
f(PK:value,A:value)
    PK in db(A).
\end{trac}

As an alternative one could declare A with a type---say, \inlinetrac|agent|---that is itself declared in
the \inlinetrac|Enumerations| section of the trac specification:
\begin{trac}
Enumerations:
agent = {a,b,c}

Transactions:
f(PK:value,A:agent)
    PK in db(A).
\end{trac}
\<close>

subsection\<open>Not Ordering the Action Sequences in Transactions Correctly\<close>
text\<open>
The actions of a transaction should occur in the correct order; first receive actions, then
database checks, then new actions and database updates, and finally send actions.

Hence, the following is an invalid transaction:
\begin{trac}
invalid(PK:value)
    send f(PK)
    receive g(PK).
\end{trac}
whereas the following is valid:
\begin{trac}
valid(PK:value)
    receive f(PK)
    send g(PK).
\end{trac}
\<close>


subsection\<open>Declaring Ill-Formed Analysis Rules\<close>
text\<open>
Each analysis rule must either be of the form
\begin{trac}
Ana(f(X1,...,Xn)) ? t'1,...,t'k -> t1,...,tm
\end{trac}
or of the form
\begin{trac}
Ana(f(X1,...,Xn)) -> t1,...,tm
\end{trac}
where \inlinetrac|f| is a function symbol of arity \inlinetrac|n|, the variables \inlinetrac|Xi| are all distinct,
and the variables occurring in the \inlinetrac|ti| and \inlinetrac|t'i| terms are among the \inlinetrac|Xi| variables.
\<close>


subsection\<open>Declaring Public Constants of Type Value\<close>
text\<open>
It is not possible to directly refer to constants of type value. A possible workaround is to
instead add a transaction that generates fresh values and releases them to the intruder (thereby
making them ``public''):
\begin{trac}
freshPublicValues():
    new K
    send K.
\end{trac}
It is usually beneficial to ensure that all fresh values are inserted into a database before being
transmitted over the network. 
In this example one could use a database that is not used anywhere else:
\begin{trac}
freshPublicValues():
    new K
    insert K publicvalues
    send K.
\end{trac}
Under the set-based abstraction this prevents accidentally identifying values produced from this
transaction with values produced elsewhere in the protocol, since they are now identified with
their own unique abstract value \inlinetrac|{publicvalues}| instead of the more common ''empty``
abstract value \inlinetrac|{}|.
\<close>


subsection\<open>Forgetting to Terminate Transactions With a period\<close>
text\<open>
Transactions must end with a period.
Forgetting this period may result in a confusing error message from the parser.
For instance, suppose that we have the following \inlinetrac|Transaction| section
where we forgot to terminate the \inlinetrac|valueProducer| transaction:
\begin{trac}
valueProducer()
    new PK
    send PK

attackDef(PK:value)
    attack.
\end{trac}

This could result in an error message like the following:
\begin{trac}
Error, line .... 14.13, syntax error: deleting  COLON LOWER_STRING_LITERAL
\end{trac}
\<close>

section\<open>Reference Manual\label{sec:reference}\<close>
text\<open>In this section, we briefly introduce the syntax of the most important commands and 
methods of Isabelle/PSPSP. We follow, in our presentation, the style of the Isabelle/Isar
manual~\cite{isabelle:isar:2021}. For details about the standard Isabelle commands and methods, 
we refer to the reader to this manual~~\cite{isabelle:isar:2021}.
\<close>
subsection\<open>Top-Level Isabelle Commands\<close>
paragraph\<open>@{command "trac"}\<close>
text\<open> \<^rail>\<open> @@{command "trac"} trac_specification \<close>

This command takes a protocol in the trac language as argument. The command translates this 
high-level protocol specification into a family of HOL definitions and also proves already 
a number of properties basic properties over these definitions. The generated definitions 
are all prefixed with the name of the protocol, as given as part of the trac specification.
\<close>

paragraph\<open>@{command "protocol_model_setup"}\<close>
text\<open> \<^rail>\<open> @@{command "protocol_model_setup"} 'spm:' protocol_name\<close>

This command takes one argument, the name of the protocol (as given in the trac specification). 
In general, this command proves a large number of properties over the protocol specification that 
are later used by our security proof. In particular, the command does internally instantiation 
proofs showing, e.g., that the protocol specifications satisifies the requirements of the typing
results of~\cite{typingisabelle}.
\<close>
paragraph\<open>@{command "compute_fixpoint"}\<close>
text\<open> \<^rail>\<open> @@{command "compute_fixpoint"} protocol_name fixpoint_name\<close>

This command computes the fixed-point of the protocol. It takes two arguments, first the protocol 
name (as given in the trac specification) and, second, the name that should be used for constant 
to which the generated fixed point is bound. The algorithm for computing the fixed-point has 
been specified in HOL. Internally, Isabelle's code generator is used for deriving an SML implementation
that is actually used. Note that our approach \emph{does not} rely on the correctness of this 
algorithm neither on the correctness of the code generator. 
\<close>

paragraph\<open>@{command "compute_SMP"}\<close>
text\<open> \<^rail>\<open> @@{command "compute_SMP"} protocol_name SMP_set_name\<close>

This command computes the SMP set of the protocol. It takes two arguments, first the protocol 
name (as given in the trac specification) and, second, the name that should be used for constant 
to which the generated SMP set is bound.
\<close>

paragraph\<open>@{command"protocol_security_proof"}\<close>
text\<open> \<^rail>\<open> @@{command "protocol_security_proof"} '[' ( safe | nbe | unsafe ) ']' 'ssp:' protocol_name\<close>

This command executes the formal security proof for the given security protocol. Its internal 
behavior can be configured using one of the following three options:
\<^item> \textbf{[safe]} (default): use Isabelle's simplifier to prove the goal by symbolic evaluation. 
  In this mode, all proof steps are checked by Isabelle's LCF-style kernel. 
\<^item> \textbf{[nbe]}:  use normalization by evaluation, a partial symbolic evaluation which permits also 
  normalization of functions and uninterpreted symbols. This setup uses the well-tested default 
  configuration of Isabelle's code generator for HOL. While the stack of code to be trusted is 
  considerable, we consider this still a highly trustworthy setup, as it cannot be influenced by 
  end-user configurations of the code generator. 
\<^item> \textbf{[unsafe]}: use Isabelle's code-generator for evaluating the proof goal on the SML-level. While 
  this is, by far, the fastest setup, it depends on the full-blown code-generator setup. As we do 
  not modify the code-generator setup in our formalisation, we consider the setup to be nearly 
  as trustworthy as the normalization by evaluation setup. Still, end-user configurations of the 
  code generator could, inadvertently, introduce inconsistencies. 

For a detailed discussion of these three modes and the different software stacks that need to 
be trusted, we refer the reader to the tutorial describing the code 
generator~\cite[Section 5.1]{isabelle:codegen:2021}. 
\<close>

paragraph\<open>@{command"manual_protocol_security_proof"}\<close>
text\<open> \<^rail>\<open> @@{command "manual_protocol_security_proof"} 'ssp:' protocol_name\<close>

This command allows to interactively prove the security of a protocol. As the fully automated 
version, it takes the protocol name as argument but it does not execute a proof. Instead, it
generated a proof state with the necessary proof obligations. It is the responsibility of the 
user to discharge these proof obligations. Application of this command results in a regular 
Isabelle proof state and, hence, all proof methods of Isabelle can be used.
\<close>


subsection\<open>Proof Methods\<close>
text\<open>
 In addition to the Isar commands discussed in the previous section, Isabelle/PSPSP also provides 
 a number of proof methods such as @{method "check_protocol_intro"} or @{method "coverage_check_unfold"}. 
 These domain specific proof methods are used internally by, e.g., the command @{command "manual_protocol_security_proof"}
 and can also be used in interactive mode. \<close>

(*<*)
end
(*>*)
