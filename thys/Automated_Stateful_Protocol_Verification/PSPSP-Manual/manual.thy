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
Ana(f(X1,...,Xn)) ? t1,...,tk -> Y1,...,Ym
\end{trac}
or of the form
\begin{trac}
Ana(f(X1,...,Xn)) -> Y1,...,Ym
\end{trac}
where \inlinetrac|f| is a function symbol of arity \inlinetrac|n|, the variables \inlinetrac|Xi| are all distinct,
the variables occurring in the \inlinetrac|ti| terms are among the \inlinetrac|Xi| variables,
and the variables \inlinetrac|Yi| are among the \inlinetrac|Xi| variables.
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
text\<open> \<^rail>\<open> @@{command "trac"} trac_specification (fixpoint_specification ?) \<close>

This command takes a protocol in the trac language as argument. The command translates this 
high-level protocol specification into a family of HOL definitions and also proves already 
a number of basic properties over these definitions. The generated definitions are all prefixed
with the name of the protocol, as given as part of the trac specification (e.g., if
@{text "keyserver"} is the protocol name given in the trac specification, then
@{text "keyserver_protocol"} will refer to the generated HOL constant that represents the transactions
of the protocol).
As an optional argument the command can take a fixed point in the trac language and generate
HOL definitions for it as well.
\<close>

paragraph\<open>@{command "trac_import"}\<close>
text\<open> \<^rail>\<open> @@{command "trac_import"} trac_filename (fixpoint_filename ?) \<close>

This command takes the name of a trac protocol specification file as argument, and, optionally, the name of
a file with a fixed point in the trac language.
The command loads the protocol and (optionally) fixed-point specifications from the files and then
executes the @{command "trac"} command on these specifications.
\<close>

paragraph\<open>@{command "protocol_model_setup"}\<close>
text\<open> \<^rail>\<open> @@{command "protocol_model_setup"} instance_name ':' protocol_name\<close>

This command takes two arguments: the name that should be used to refer to the protocol model, and the
name of the protocol (as given in the trac specification). 
In general, this command proves a large number of properties over the protocol specification that 
are later used by our security proof. In particular, the command does internally instantiation 
proofs showing, e.g., that the protocol specification satisfies the requirements of the typed
model of~\cite{hess.ea:typing:2018}.
\<close>

paragraph\<open>@{command "manual_protocol_model_setup"}\<close>
text\<open> \<^rail>\<open> @@{command "manual_protocol_model_setup"} instance_name ':' protocol_name\<close>

This command allows to interactively set up the protocol model. As the fully automated 
version, it takes the name for the protocol model and the protocol name as arguments but it does not execute a
proof. Instead, it generates a proof state with the necessary proof obligations. It is the responsibility of the 
user to discharge these proof obligations. Application of this command results in a regular 
Isabelle proof state and, hence, all proof methods of Isabelle can be used.
\<close>

paragraph\<open>@{command "setup_protocol_checks"}\<close>
text\<open> \<^rail>\<open> @@{command "setup_protocol_checks"} instance_name (protocol_constant +)\<close>

This command declares attributes for the definitions of the @{text "protocol_constant"} HOL constants given as arguments (among other constants used in the automated proofs of protocol security).
This can later be used to expand the proof obligations when proving fixed-point coverage with @{command "manual_protocol_security_proof"} and using the proof methods @{method "coverage_check_intro"} and @{method "check_protocol_intro'"}.
The command takes as arguments the name of the protocol model instance given at an earlier point to the @{command "manual_protocol_model_setup"}
command, and a non-empty sequence of protocol HOL constant names for which the command will perform its setup.
\<close>

paragraph\<open>@{command "compute_fixpoint"}\<close>
text\<open> \<^rail>\<open> @@{command "compute_fixpoint"} protocol_constant fixpoint_constant (attack_trace_constant ?) \<close>

This command computes the fixed-point of a protocol. It takes two arguments, first the name of the HOL constant representing the
protocol (usually the name given in the trac specification suffixed with @{text "_protocol"}), second, the name that should be
used for the constant to which the generated fixed point is bound. The algorithm for computing the fixed-point has 
been specified in HOL. Internally, Isabelle's code generator is used for deriving an SML implementation
that is actually used. Note that our approach \emph{does not} rely on the correctness of this 
algorithm neither on the correctness of the code generator.

The command can optionally generate a HOL constant that represents an attack trace, bound to the HOL constant @{text "attack_trace_constant"}.
The attack trace can later be given to the @{command "print_attack_trace"} to print it.
This optional argument, @{text "attack_trace_constant"}, should only be given if the computed fixed point will contain an attack signal.
\<close>

paragraph\<open>@{command "compute_SMP"}\<close>
text\<open> \<^rail>\<open> @@{command "compute_SMP"} behavior protocol_constant smp_constant
;
behavior: ('[no_optimizations]' | '[optimized]' | '[GSMP]' | '[composition]' | '[composition_optimized]' ) ? \<close> 

This command computes a finite representation of the Sub-Message Patterns (SMP) set of the protocol.
This set is used to automatically prove the conditions of the typing result of~\cite{hess.ea:typing:2018} (named type-flaw resistance)
during a security proof.
It takes two mandatory arguments; first the protocol name (as given in the trac specification) and, second, the
name that should be used for the constant to which the generated SMP set is bound.

The optional argument can take the following values:
\<^item> @{text "[no_optimizations]"}:
  Computes the finite SMP representation set without any optimizations (this is the default setting).
\<^item> @{text "[optimized]"}:
  Applies optimizations to reduce the size of the computed set, but this might not be sound.
\<^item> @{text "[GSMP]"}:
  Computes a set suitable for use in checking GSMP disjointness (see the @{command "protocol_composition_proof"} command for further information).
\<^item> @{text "[composition]"}:
  Computes a set suitable for checking type-flaw resistance of composed protocols (see the @{command "protocol_composition_proof"} command for further information).
\<^item> @{text "[composition_optimized]"}:
  This is an optimized variant of the previous setting.
\<close>

paragraph\<open>@{command "protocol_security_proof"}\<close>
text\<open> \<^rail>\<open>
@@{command "protocol_security_proof"} behavior instance_name ':' protocol_name \<newline>
(('for' protocol_constant ((fixpoint_constant (smp_constant ?)) ?)) ?)
;
behavior: ('[safe]' | '[nbe]' | '[unsafe]' ) ? \<close>

This command executes the formal security proof for the given security protocol.
Its internal behavior can be configured using one of the following three options:
\<^item> @{text "[safe]"} (default): use Isabelle's simplifier to prove the goal by symbolic evaluation. 
  In this mode, all proof steps are checked by Isabelle's LCF-style kernel. 
\<^item> @{text "[nbe]"}: use normalization by evaluation, a partial symbolic evaluation which permits also 
  normalization of functions and uninterpreted symbols. This setup uses the well-tested default 
  configuration of Isabelle's code generator for HOL. While the stack of code to be trusted is 
  considerable, we consider this still a highly trustworthy setup, as it cannot be influenced by 
  end-user configurations of the code generator. 
\<^item> @{text "[unsafe]"}: use Isabelle's code-generator for evaluating the proof goal on the SML-level. While 
  this is, by far, the fastest setup, it depends on the full-blown code-generator setup. As we do 
  not modify the code-generator setup in our formalization, we consider the setup to be nearly 
  as trustworthy as the normalization by evaluation setup. Still, end-user configurations of the 
  code generator could, inadvertently, introduce inconsistencies. 
\<close>
text\<open>
For a detailed discussion of these three modes and the different software stacks that need to 
be trusted, we refer the reader to the tutorial describing the code 
generator~\cite[Section 5.1]{isabelle:codegen:2021}. 
\<close>
text\<open>
The remaining arguments are the following:
\<^item> @{text "instance_name"}: The name that should be used to refer to the instance of the @{text "secure_stateful_protocol"} locale that is interpreted by this command.
\<^item> @{text "protocol_name"}: The name of the trac protocol to be proven secure, as given in the protocol specification.
By default, if no other arguments are given, the command will use the HOL constants @{text "protocol_name_protocol"} and @{text "protocol_name_fixpoint"} for the protocol respectively fixed point used in the security proof.
\<^item> @{text "protocol_constant"} (optional): The name of the HOL constant that represents the protocol to be proven secure.
\<^item> @{text "fixpoint_constant"} (optional): The name of the HOL constant that represents the fixed point that is used in the security proof.
\<^item> @{text "smp_constant"} (optional): The name of the HOL constant that represents the SMP set of the protocol.
\<close>
text\<open>
After successful execution of this command, the security theorem of the protocol is available as
@{text "instance_name.protocol_secure"}.
The corollary @{text "instance_name.protocol_welltyped_secure"} is the version of the security theorem restricted to the typed model.
\<close>

paragraph\<open>@{command "manual_protocol_security_proof"}\<close>
text\<open> \<^rail>\<open> @@{command "manual_protocol_security_proof"} instance_name ':' protocol_name \<newline>
( ('for' protocol_constant ( (fixpoint_constant (smp_constant ?) ) ?) ) ?)\<close>

This command allows to interactively prove the security of a protocol. As the fully automated 
version, it takes the protocol name as argument but it does not execute a proof. Instead, it
generates a proof state with the necessary proof obligations. It is the responsibility of the 
user to discharge these proof obligations. Application of this command results in a regular 
Isabelle proof state and, hence, all proof methods of Isabelle can be used.
\<close>

paragraph\<open>@{command "print_fixpoint"}\<close>
text\<open> \<^rail>\<open> @@{command "print_fixpoint"} protocol_name fixpoint_constant \<close>

This command translates the given HOL constant fixed point into the trac-language and then prints it.
It takes as arguments, first, the name of the protocol (as given in the trac specification), and, second, the name of the HOL constant that represents a fixed point.
\<close>

paragraph\<open>@{command "save_fixpoint"}\<close>
text\<open> \<^rail>\<open> @@{command "save_fixpoint"} instance_name fixpoint_filename fixpoint_constant \<close>

This command translates the given HOL constant fixed point into the trac-language and then saves it to the file whose name is given as argument.
It takes as arguments the name of the interpreted protocol model, the name of the HOL constant for the fixed point, and the output filename.
\<close>

paragraph\<open>@{command "load_fixpoint"}\<close>
text\<open> \<^rail>\<open> @@{command "load_fixpoint"} instance_name fixpoint_filename fixpoint_constant \<close>

This command loads a trac fixed-point from a file.
It takes as arguments the name of the interpreted protocol model, the input filename, and the name of the HOL constant to be defined.
\<close>

paragraph\<open>@{command "print_transaction_strand"}\<close>
text\<open> \<^rail>\<open> @@{command "print_transaction_strand"} instance_name transaction_constant \<close>

This command takes a HOL constant that represents a transaction, translates it into a syntax that is similar to trac, and then prints it. 
It takes as arguments the name of the name of the trac specification and the HOL constant to be printed.
\<close>

paragraph\<open>@{command "print_transaction_strand_list"}\<close>
text\<open> \<^rail>\<open> @@{command "print_transaction_strand_list"} protocol_name protocol_constant \<close>

This command takes a HOL constant that represents a list of transactions (such as a protocol HOL constant), translates it into a syntax that is similar to trac, and then prints it. 
It takes as arguments the name of the name of the trac specification and the HOL constant to be printed.
\<close>

paragraph\<open>@{command "print_attack_trace"}\<close>
text\<open> \<^rail>\<open> @@{command "print_attack_trace"} protocol_name protocol_constant attack_trace_constant \<close>

This command takes a HOL constant that represents an attack trace, translates it into a syntax that is similar to trac, and then prints it. 
It takes as arguments the name of the trac specification, the protocol HOL constant that has an attack, and the HOL constant for the attack trace.
\<close>

paragraph\<open>@{command "compute_shared_secrets"}\<close>
text\<open> \<^rail>\<open> @@{command "compute_shared_secrets"} smp_constant (smp_constant +) secrets_constant \<close>

This command computes a finite representation of the terms that are in the intersection of two or more GSMP sets.
This is useful to compute the set of secrets that are shared between two or more protocols.
It takes as arguments a sequence of SMP HOL constants and the name of the HOL constant to which the output should be bound.
\<close>

paragraph\<open>@{command "protocol_composition_proof"}\<close>
text\<open> \<^rail>\<open> @@{command "protocol_composition_proof"} behavior instance_name ':' protocol_name \<newline>
'for' protocol_constant smp_constant secrets_constant \<newline>
'and' protocol_constant (protocol_constant +) \<newline>
'and' protocol_constant (protocol_constant +) \<newline>
'and' smp_constant (smp_constant +)
;
behavior: ('[safe]' | '[nbe]' | '[unsafe]' ) ? \<close>


This command applies the compositionality theorem of~\cite{hess.ea:stateful:2018} to the protocols given as arguments and automatically proves the syntactic conditions required for composition.

After successful execution of this command the theorem

@{text "instance_name.composed_protocol_preserves_component_goals"}

is available which states the following: if the nth component protocol is secure (in a typed model), and all component protocols are leakage-free, then the goals of the nth component protocol hold in the composed protocol as well (also in an untyped model).

The command takes the following arguments:
\<^item> An optional argument to set the behavior of the internal automated proof (see @{command "protocol_security_proof"} for an explanation).
\<^item> The name to which the interpreted locale for the composition should be bound.
\<^item> The name of the protocol as given in the trac-specification.
\<^item> The HOL constant representing the composed protocol. Usually @{text "protocol_name_protocol"} where @{text "protocol_name"} is the name of the protocol as given in the trac-specification.
\<^item> The HOL constant representing the SMP set of the composed protocol, usually computed using the @{command "compute_SMP"} command with the @{text "[composition]"} or @{text "[composition_optimized]"} optional argument.
\<^item> The HOL constant representing the shared secrets between the component protocols, usually computed with the @{command "compute_shared_secrets"} command.
\<^item> A sequence of two or more HOL constants representing the component protocols. Their union must evaluate to the same term as the composed protocol HOL constant given as an earlier argument.
Usually this sequence is of the form @{text "protocol_name_protocol_N"}, for each @{text "N"}, where @{text "N"} is the name of the nth component protocol as given in the trac-specification.
\<^item> A sequence of two or more HOL constants representing the composition of each component protocol composed with the abstractions of the other component protocols. It is important that the ordering of these arguments matches the ordering of the component protocols as given in the previous sequence of arguments, and that the length matches the length of the previous sequence: the nth element of this sequence must represent the composition of the nth element from the sequence of component protocols, composed with the abstraction of all the other component protocols.
Usually this sequence is of the form @{text "protocol_name_protocol_N_with_star_projs"}, for each @{text "N"}, where @{text "N"} is the name of the nth component protocol as given in the trac-specification.
\<^item> A sequence of two or more HOL constants that represent the Ground Sub-Message Patterns (GSMP) of the component protocols, usually computed using the @{command "compute_SMP"} with the @{text "[GSMP]"} optional argument. The number of elements in this sequence, and their ordering, must again match the previous sequence of arguments.

\<close>

paragraph\<open>@{command "manual_protocol_composition_proof"}\<close>
text\<open> \<^rail>\<open> @@{command "manual_protocol_composition_proof"} instance_name ':' protocol_name \<newline>
'for' protocol_constant smp_constant secrets_constant \<newline>
'and' protocol_constant (protocol_constant +) \<newline>
'and' protocol_constant (protocol_constant +) \<newline>
'and' smp_constant (smp_constant +) \<close>

This command allows to interactively prove the composition of protocols. As the fully automated 
version, it takes the protocol name as argument but it does not execute a proof. Instead, it
generates a proof state with the necessary proof obligations. It is the responsibility of the 
user to discharge these proof obligations. Application of this command results in a regular 
Isabelle proof state and, hence, all proof methods of Isabelle can be used.
\<close>

subsection\<open>Proof Methods\<close>
text\<open>
 In addition to the Isar commands discussed in the previous section, Isabelle/PSPSP also provides 
 a number of proof methods such as @{method "check_protocol_intro"} or @{method "coverage_check_unfold"} or @{method "composable_protocols_intro"}. 
 These domain specific proof methods are used internally by, e.g., the command @{command "protocol_security_proof"}
 and can also be used in interactive mode. \<close>

(*<*)
end
(*>*)
