(***********************************************************************************
 * Copyright (c) 2025 Université Paris-Saclay
 *
 * Author: Benoît Ballenghien, Université Paris-Saclay,
 *         CNRS, ENS Paris-Saclay, LMF
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 ***********************************************************************************)


(*<*)
theory CSP_PTick_Introduction
  imports "HOL-CSP"
begin
  (*>*)

chapter \<open>Introduction\<close>

section \<open>Motivations\<close>

text \<open>
Recently, the question arose whether \<^session>\<open>HOL-CSP\<close> could accommodate
a parameterized notion of termination.\<^footnote>\<open>This idea was sparked by an innocent remark
from Simon Foster, which we later explored in depth.\<close>
The idea is very simple: replace at the very beginning of the formalization
@{theory_text [display] \<open>datatype 'a event = ev 'a | tick (\<open>\<checkmark>\<close>)\<close>}
(isomorphic to option type) by
@{theory_text [display] \<open>datatype ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k = ev 'a | tick 'r (\<open>\<checkmark>'(_')\<close>)\<close>}
(isomorphic to sum type), so that the explicit termination event carries a return value.
\<close>


text \<open>
Certain definitions must therefore be adapted
(mainly by replacing \<^term>\<open>\<checkmark>\<close> with \<^term>\<open>range tick\<close>).
For example, a trace \<^term>\<open>t\<close> was said to be tick-free if \<^term>\<open>\<checkmark> \<notin> set t\<close>.
In this new setup, such a trace instead satisfies @{thm (rhs) tickFree_def[of t]}.
Surprisingly, once these few intuitive adjustments have been made,
most of the existing Isar proofs remain valid with little to no modification.
This generalization has already been carried out, and the AFP entries for
\<^session>\<open>HOL-CSP\<close>, \<^session>\<open>HOL-CSPM\<close>, and \<^session>\<open>HOL-CSP_OpSem\<close>
have all been updated accordingly \<^cite>\<open>"HOL-CSP-AFP" and "HOL-CSPM-AFP" and "HOL-CSP_OpSem-AFP"\<close>.
More recently, \<^session>\<open>HOL-CSP_RS\<close> \<^cite>\<open>"HOL-CSP_RS-AFP"\<close> has been added as well.
However, two operators do not behave as satisfactorily as one might hope.
\<close>

text \<open>
Firstly, sequential composition no longer admits \<^const>\<open>SKIP\<close> as a neutral element.
In the classical theory, we have @{thm SKIP_Seq[of \<open>()\<close> P]} and @{thm Seq_SKIP[of P]}.
But in the generalized setting, \<^const>\<open>SKIP\<close> carries a value and
if the first law can still be adapted and proven: @{thm SKIP_Seq[of r P]},
the second one only holds when the return type is \<^typ>\<open>unit\<close>
(which amounts to ignoring the generalization).
From a broader perspective, one would in fact like the right-hand process
to depend on the return value of the left-hand process,
which is not the case in the current framework.
\<close>



text \<open>
Secondly, the synchronization product does not properly support synchronized termination.
Classically, we have
\<^term>\<open>Skip \<lbrakk>S\<rbrakk> Skip = Skip\<close>, adapted in the last version of \<^session>\<open>HOL-CSP\<close>
as @{thm SKIP_Sync_SKIP[of r A s]}.
When restricted to \<^typ>\<open>'a process\<close> (which is \<^typ>\<open>('a, unit) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>) the behavior is fine,
but with general return values deadlocks may occur.
One would rather expect a law like \<open>SKIP r \<lbrakk>A\<rbrakk> SKIP s = SKIP (r, s)\<close>,
yet defining such an operator raises non-trivial technical challenges.
\<close>

text \<open>
In this entry, we propose generalized definitions for
sequential composition and synchronization product
that not only respect the invariant \<^const>\<open>is_process\<close>
but also fulfill the expectations outlined above.
Beyond this substantial work, we establish algebraic
and operational properties of these operators,
as well as the lemmas required for fixed-point reasoning.
In particular, it can be pointed out that the resulting
sequential composition operator fulfills the laws of a monad.
\<close>


section\<open>The Global Architecture of \<^session>\<open>HOL-CSP_PTick\<close>\<close>

text\<open>
\begin{figure}[ht]
  \centering
  \includegraphics[width=\textwidth]{session_graph.pdf}
	\caption{The overall architecture}
	\label{fig:fig1}
\end{figure}
\<close>

text \<open>
Our formalization attempts to take full advantage of parallelization,
explaining the shape of the session graph shown in \autoref{fig:fig1}.
\<close>


(*<*)
end
  (*>*)