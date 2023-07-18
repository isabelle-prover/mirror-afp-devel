(*  Title:      KeyserverEx.thy
    Author:     Andreas Viktor Hess, DTU
    Author:     Sebastian A. Mödersheim, DTU
    Author:     Achim D. Brucker, University of Exeter
    Author:     Anders Schlichtkrull, DTU
    SPDX-License-Identifier: BSD-3-Clause
*)

section\<open>A Brief Overview of Isabelle/PSPSP\label{sec:overview}\<close>
text\<open>
  In this section, we briefly explain how to use Isabelle/PSPSP for proving the security of 
  protocols. As Isabelle/PSPSP is build on top of Isabelle/HOL, the overall user interface
  and the high-level language (called Isar) are inherited from Isabelle. We refer the reader
  to \<^cite>\<open>"nipkow2002isabelle"\<close> and the system manuals that are part of the Isabelle 
  distribution. The latter are accessible within Isabelle/jEdit in the documentation pane 
  on the left-hand side of the main window . 
\<close>

text\<open>
  In the following, we will illustrate the use of our system by analyzing a simple keyserver 
  protocol (this theory is stored in the file \inlinebash|PSPSP-Manual/KeyserverEx.thy|. When 
  loading this theory in Isabelle/jEdit, please ensure that the 
  session @{session "Automated_Stateful_Protocol_Verification"} is active (this session provides
  Isabelle/PSPSP).

  When done, please move the text cursor to the section ``Proof of Security''. There are some 
  orange question marks at the side of some lines. These are the comments from Isabelle that 
  indicate the timing results we ask for: when moving the cursor to the corresponding line,
  and selecting the \verb|Output|-Tab on the bottom of the Isabelle window (ensure that there is 
  a tick-mark on ``Auto update''), you see the timing information provided by Isabelle for each step. 
  Your Isabelle should look similar to \autoref{fig:Keyserver}.
  \begin{figure}
  \centering
  \includegraphics[width=\textwidth]{jedit-keyserver.png}
  \caption{Opening \inlinebash|KeyserverEx.thy| in Isabelle/jEdit.}\label{fig:Keyserver}
  \end{figure}

  The Isabelle IDE (called Isabelle/jEdit) is a front-end for Isabelle that supports most features
  known from IDEs for programming languages. The input area (in the middle of the upper part of 
  the window) supports, e.g., auto completion, syntax highlighting, and automated proof generation 
  as well as interactive proof development. The lower part shows the current output (response)
  with respect to the cursor position.
\<close>

text\<open>
  We will now briefly explain this example in more detail. First, we start with the theory header: 
  As in Isabelle/HOL, formalization happens within theories. A theory is a unit with a name that 
  can import other theories. Consider the following theory header: \<close>
theory 
  KeyserverEx
imports 
  Automated_Stateful_Protocol_Verification.PSPSP
  (*<*)"introduction"(*>*)
begin
text\<open>which opens a new theory \texttt{KeyserverEx} that is based on the top-level theory of 
Isabelle/PSPSP, called @{theory "Automated_Stateful_Protocol_Verification.PSPSP"}. Within this 
theory, we can use all definitions and tools provided by Isabelle/PSPSP. For example, 
Isabelle/PSPSP provides a mechanism for measuring the run-time of certain commands. This 
mechanism can be turned on as follows:\<close>
declare [[pspsp_timing]]

subsection\<open>Protocol Specification\<close>
text\<open>
The protocol is specified using a domain-specific language that, e.g., could also be used by a 
security protocol model checker. We call this language ``trac'' and provide a dedicated environment 
(command) @{command "trac"} for it: \<close>
trac\<open>
Protocol: Keyserver

Enumerations:
honest = {a,b,c}
dishonest = {i}
agent = honest ++ dishonest

Sets:
ring/1 valid/1 revoked/1 deleted/1

Functions:
Public sign/2 crypt/2 pair/2
Private inv/1

Analysis:
sign(X,Y) -> Y
crypt(X,Y) ? inv(X) -> Y
pair(X,Y) -> X,Y

Transactions:
# Out-of-band registration
outOfBand(A:honest)
  new PK
  insert PK ring(A)
  insert PK valid(A)
  send PK.

# Out-of-band registration (for dishonest users; they reveal their private keys to the intruder)
outOfBandD(A:dishonest)
  new PK
  insert PK valid(A)
  send PK
  send inv(PK).

# User update key
keyUpdateUser(A:honest,PK:value)
  PK in ring(A)
  new NPK
  delete PK ring(A)
  insert PK deleted(A)
  insert NPK ring(A)
  send sign(inv(PK),pair(A,NPK)).

# Server update key
keyUpdateServer(A:agent,PK:value,NPK:value)
  receive sign(inv(PK),pair(A,NPK))
  PK in valid(A)
  NPK notin valid(_)
  NPK notin revoked(_)
  delete PK valid(A)
  insert PK revoked(A)
  insert NPK valid(A)
  send inv(PK).

# Attack definition
attackDef(A:honest,PK:value)
  receive inv(PK)
  PK in valid(A)
  attack.
\<close>


text\<open>
The command @{command "trac"} automatically translates this specification into a family of formal 
HOL definitions. Moreover, basic properties of these definitions are also already proven 
automatically (i.e., without any user interaction): for this simple example, already over 350 
definitions and theorems are automatically generated, respectively, formally proven. For example, 
the following induction rule is derived:
@{thm [display] "Keyserver_Ana.induct"}
\<close>

subsection \<open>Protocol Model Setup\<close>
text\<open>Next, we show that the defined protocol satisfies the requirement of our protocol model
(technically, this is done by instantiating several Isabelle locales, resulting in over 1750 
theorems ``for free.''). The underlying instantiation proofs are fully automated by our tool:\<close>
protocol_model_setup spm: Keyserver

subsection \<open>Fixed Point Computation\<close>
text\<open>Now we compute the fixed-point: \<close>
compute_fixpoint Keyserver_protocol Keyserver_fixpoint
text\<open>We can inspect the fixed-point with the following command: \<close> 
thm Keyserver_fixpoint_def
text\<open>Moreover, we can use Isabelle's @{command "value"}-command to compute its size:\<close>
value "let (FP,_,TI) = Keyserver_fixpoint in (size FP, size TI)"

subsection \<open>Proof of Security\<close>
text\<open> After these steps, all definitions and auxiliary lemmas for the security proof are available. 
Note that the security proof will fail, if any of the previous commands did fail. A failing command 
is sometimes hard to spot for non Isabelle experts: the status bar next to the scroll bar 
on the right-hand side of the window should not have any ```dark red'' markers.


We can do a fully automated security proof using a new command @{command "protocol_security_proof"}:\<close>
protocol_security_proof ssp: Keyserver 
text\<open>This command proves the security of the protocol using only Isabelle's simplifier (and, hence, everything 
is checked by Isabelle's LCF-style kernel).\<close>

text\<open>Moreover, we provide two alternative configuration, one using an approach called 
``normalization by evaluation'' (nbe) and one using Isabelle's code generator for direct code
evaluation (eval). Please see \autoref{sec:reference} and Isabelle's code generator 
manual~\<^cite>\<open>"isabelle:codegen:2021"\<close> for details.\<close>
protocol_security_proof [nbe] ssp: Keyserver

text\<open>While the stack of code that needs to be trusted for the normalization by evaluation is 
much smaller than for the direct code evaluation, direct code evaluation is usually much faster:\<close>
protocol_security_proof [unsafe] ssp: Keyserver

text\<open>Moreover, there is the option to only generate the proof obligations (as sub-goals) for an 
interactive security proof:\<close>
manual_protocol_security_proof ssp: Keyserver
  for Keyserver_protocol Keyserver_fixpoint 
  apply check_protocol_intro
  subgoal by (timeit code_simp)
  subgoal by (timeit eval)
  subgoal by (timeit code_simp)
  subgoal by (timeit normalization)
  subgoal by (timeit code_simp)
  done
text\<open>
Such an interactive proof allows us to interactively inspect intermediate proof states or to 
use protocol-specific proof strategies (e.g., only partially unfolding the fixed-point).
\<close>

subsection \<open>Inspecting the Generated Theorems and Definitions\<close>
text\<open>We can inspect the generated proofs using the @{command "thm"} command:\<close>
thm ssp.protocol_secure
thm spm.constraint_model_def
thm spm.reachable_constraints.simps

thm Keyserver_enum_consts.nchotomy
thm Keyserver_sets.nchotomy
thm Keyserver_fun.nchotomy
thm Keyserver_atom.nchotomy
thm Keyserver_arity.simps
thm Keyserver_sets_arity.simps
thm Keyserver_public.simps
thm Keyserver_\<Gamma>.simps
thm Keyserver_Ana.simps

thm Keyserver_protocol_def
thm Keyserver_transaction_intruderValueGen_def
thm Keyserver_transaction_outOfBand_def
thm Keyserver_transaction_outOfBandD_def
thm Keyserver_transaction_keyUpdateUser_def
thm Keyserver_transaction_keyUpdateServer_def
thm Keyserver_transaction_attackDef_def

thm Keyserver_fixpoint_def

text\<open>Finally, the theory needs to be closed:\<close>
end
