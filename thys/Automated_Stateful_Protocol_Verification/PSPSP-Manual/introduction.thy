(*  Title:      introduction.thy
    Author:     Andreas Viktor Hess, DTU
    Author:     Sebastian A. Mödersheim, DTU
    Author:     Achim D. Brucker, University of Exeter
    Author:     Anders Schlichtkrull, DTU
    SPDX-License-Identifier: BSD-3-Clause
*)

(*<*)
theory 
  "introduction"
imports 
  "../PSPSP"
begin 
(*>*)
section\<open>Introduction\label{sec:introduction}\<close>
text\<open>
In this section, we describe the installation and use of
Isabelle/PSPSP, the system implementing the approach described in our
CSF submission.

Isabelle/PSPSP is built on top of the latest version of Isabelle/HOL~\<^cite>\<open>"nipkow2002isabelle"\<close>. 
While Isabelle is widely perceived as an interactive theorem prover for HOL
(Higher-order Logic), we would mention that Isabelle can be understood
as a framework that provides various extension points. In our work, we
make use of this fact by extending Isabelle/HOL with:
\<^item> a formalization of the protocol-independent aspects of our approach that is based on a large
  formalization (the session is called @{session "Automated_Stateful_Protocol_Verification"}) of 
  security protocols in Isabelle/HOL that, among others, includes proofs for typing results and 
  protocol compositionality. The main entry for the security analysis of concrete protocols using Isabelle/PSPSP
  is the theory @{theory "Automated_Stateful_Protocol_Verification.PSPSP"}.
\<^item> an encoder (datatype package) that translates a high-level protocol specification (called 
  ``trac'') into HOL. This datatype package provides the high-level command @{command "trac"}. 
\<^item> a command (called @{command "compute_fixpoint"}) that computes an over-approximation of all 
  messages that a security protocol can generate. 
\<^item> a command that, for a specific class of protocols, can fully-automatically prove their security
  (@{command "protocol_security_proof"}).
\<^item> a command that generates a list of proof obligations (sub-goals) for proving the security
  of the specified protocol interactively (@{command "manual_protocol_security_proof"}).
\<^item> several proof methods that either can be used interactively or that are used internally
  by the fully automated poof setup (@{command "protocol_security_proof"}).
\<close>

section\<open>Installation\label{sec:installation}\<close>
text\<open>
Isabelle/PSPSP extends Isabelle/HOL. Thus, the first step is to install Isabelle. Moreover, 
we make use of the Archive of Formal Proofs (AFP), which needs to be installed in a second step. 
Finally, we need to register the new Isabelle components and compile the session heaps for faster
start up. 
\<close>

subsection\<open>Installing Isabelle\<close>
text\<open>
Isabelle can be downloaded from the Isabelle website (\url{http://isabelle.in.tum.de/}).
Detailed installation instructions for all supported operating systems are available at
\url{https://isabelle.in.tum.de/installation.html}.
\<close> 

subsection\<open>Installing the Archive of Formal Proofs\<close>
text\<open>
After installing Isabelle, we now need to install the AFP (Archive of Formal Proofs). The AFP 
(\url{https://www.isa-afp.org}) is a large library of Isabelle formalizations. Please install
the latest version, following the instructions from \url{https://www.isa-afp.org/using.html}.
\<close> 

subsection\<open>Compiling Session Heaps and Final Setup\<close>
text\<open>
We recommend\footnote{The sessions should also be build automatically on the start of 
Isabelle's graphical user interface Isabelle/jEdit. For this, it is important that
you select the session @{session "Automated_Stateful_Protocol_Verification"} as described
in the following paragraph and \emph{restart} Isabelle. For us, building on the command 
line has easier to reproduce on different machines.} to ``compile'' Isabelle/PSPSP (in 
Isabelle lingo: building the session heaps) on the command line. This can be done by 
executing (please take care of the full qualified path of the
\inlinebash|isabelle| binary for your operating system):
\begin{bash}
ë\prompt{}ë isabelle build -b Automated_Stateful_Protocol_Verification
Building Pure ...
Finished Pure (0:00:50 elapsed time, 0:00:50 cpu time, factor 1.00)
Building HOL ...
Finished HOL (0:09:50 elapsed time, 0:31:02 cpu time, factor 3.16)
Building HOL-Library ...
Finished HOL-Library (0:04:49 elapsed time, 0:24:43 cpu time, factor 5.13)
Building Abstract-Rewriting ...
Finished Abstract-Rewriting (0:01:28 elapsed time, 0:04:00 cpu time, factor 2.71)
Building First_Order_Terms ...
Finished First_Order_Terms (0:00:47 elapsed time, 0:01:54 cpu time, factor 2.39)
Building Stateful_Protocol_Composition_and_Typing ...
Finished Stateful_Protocol_Composition_and_Typing (0:08:18 elapsed time, 0:36:38 cpu time, factor 4.41)
Building Automated_Stateful_Protocol_Verification ...
Finished Automated_Stateful_Protocol_Verification (0:15:11 elapsed time, 0:50:57 cpu time, factor 3.36)
0:41:46 elapsed time, 2:30:06 cpu time, factor 3.59
ë\prompt{}ë
\end{bash}
Isabelle will build all sessions that are required. Note that you might have already some of the 
heaps available and, hence, only a subset of the list shown above might be build on your system.

Finally, please start the (graphical) Isabelle application by clicking on the Isabelle icon (macOS) 
or by starting \inlinebash|Isabelle2021-1| (this example is for Isabelle version 2021-1) on the 
command line (Linux and macOS):
\begin{bash}
ë\prompt{}ë ./Isabelle2021-1/Isabelle2021-1
\end{bash}
and select the session @{session "Automated_Stateful_Protocol_Verification"}. For doing so, you need 
to select the ``Theories''-pane on the right hand side and select the session from drop-down menu 
(see \autoref{fig:select-session}). To persist this configuration, you need to restart Isabelle, 
i.e., please close Isabelle/jEdit now. On the next start, 
@{session "Automated_Stateful_Protocol_Verification"} will be the default session. 
\begin{figure}
  \centering\includegraphics[width=\textwidth]{jedit-select-session}
  \caption{Isabelle/jEdit on its first startup. Please click on the
    ``Theories'' tab on the right hand side and select the session
    ``\inlineisar|Automated_Stateful_Protocol_Verification|.''}\label{fig:select-session}
\end{figure}
\<close>

(*<*)
end
(*>*)
