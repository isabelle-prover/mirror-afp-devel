(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSPM - Architectural operators for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff.
 *
 * This file       : Introduction
 *
 * Copyright (c) 2025 Université Paris-Saclay, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************\<close>
(*>*)


chapter\<open> Introduction \<close>

(*<*)
theory Introduction                                               
  imports "HOL-CSP.CSP"
begin 
  (*>*)

section\<open>Motivations\<close>

text \<open>\<^session>\<open>HOL-CSP\<close> \<^cite>\<open>"HOL-CSP-AFP"\<close> is a formalization in Isabelle/HOL of 
      the work of Hoare and Roscoe on the denotational semantics of the 
      Failure/Divergence Model of CSP. It follows essentially the presentation of CSP 
      in Roscoe's Book "Theory and Practice of Concurrency" \<^cite>\<open>"roscoe:csp:1998"\<close>
      and the semantic details in a joint Paper of Roscoe and Brooks
      "An improved failures model for communicating processes" \<^cite>\<open>"brookes-roscoe85"\<close>.\<close>

text \<open>In the session \<^session>\<open>HOL-CSP\<close> are introduced the type \<^typ>\<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>, several 
      classic CSP operators and number of laws that govern their interactions.

      Four of them are binary operators: the non-deterministic choice \<^term>\<open>P \<sqinter> Q\<close>, 
      the deterministic choice \<^term>\<open>P \<box> Q\<close>, the synchronization \<^term>\<open>P \<lbrakk>S\<rbrakk> Q\<close> and the
      sequential composition \<^term>\<open>P \<^bold>; Q\<close>.\<close>

text \<open>Analogously to the finite sum
      @{term [mode=latex_sum, eta_contract = false] \<open>\<Sum>i = 0::nat..n. a i\<close>} which is generalization
      of the addition \<^term>\<open>a + b\<close>, we define generalisations of the binary operators 
      of CSP.

      The most straight-forward way to do so would be a fold on a list of processes.
      However, in many cases, we have additional properties, like commutativity, idempotency, etc.
      that allow for stronger/more abstract constructions. In particular, in several cases,
      generalization to unbounded and even infinite index-sets are possible.

      The notations we choose are widely inspired by the CSP$_M$ syntax of FDR:
      \<^url>\<open>https://cocotec.io/fdr/manual/cspm.html\<close>.\<close>

text \<open>For the non-deterministic choice \<^term>\<open>P \<sqinter> Q\<close>, this is already done in \<^session>\<open>HOL-CSP\<close>.
      In this session we therefore introduce the multi-operators:
        \<^item> the global deterministic choice, written \<open>\<box> a \<in> A. P a\<close>, generalizing \<^term>\<open>P \<box> Q\<close>
        \<^item> the multi-synchronization product, written \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk> m \<in># M. P m\<close>, generalizing \<^term>\<open>P \<lbrakk>S\<rbrakk> Q\<close>
          with the two special cases \<open>\<^bold>|\<^bold>|\<^bold>| m \<in># M. P m\<close> and \<open>\<^bold>|\<^bold>| m \<in># M. P m\<close>
        \<^item> the multi-sequential composition, written \<open>SEQ l \<in>@ L. P l\<close>, generalizing \<^term>\<open>P \<^bold>; Q\<close>.
      We prove their continuity and refinements rules, 
      as well as some laws governing their interactions.\<close>

text \<open>We also provide the definitions of the POTS and Dining Philosophers examples,
      which greatly benefit from the newly introduced generalized operators.

      Since they appear naturally when modeling complex architectures,
      we may call them \<^emph>\<open>architectural operators\<close>:
      these multi-operators represent the heart of the architectural composition principles of CSP.\<close>

text \<open>Additionally, we developed the theory of the interrupt operators \<^emph>\<open>Sliding\<close>, \<^emph>\<open>Throw\<close> 
      and \<^emph>\<open>Interrupt\<close> \<^cite>\<open>"Roscoe2010UnderstandingCS"\<close>.
      This part of the present theory reintroduces denotational semantics for these operators and
      constructs on this basis the algebraic laws for them.

    In several places, our formalization efforts led to slight modifications of the original
      definitions in order to achieve the goal of a combined integrated theory.
      In some cases -- in particular in connection with the \<^emph>\<open>Interrupt\<close> operator definition --
      some corrections have been necessary since the fundamental invariants were not respected.\<close>

text \<open>Finally, his session includes a very powerful result about \<^const>\<open>deadlock_free\<close>
      and \<^const>\<open>Sync\<close>: the interleaving \<^term>\<open>P ||| Q\<close> is \<^const>\<open>deadlock_free\<close> if \<^term>\<open>P\<close> and \<^term>\<open>Q\<close> are,
      and so is the multi-interleaving of processes \<open>P m\<close> for \<open>m \<in># M\<close>.
      
       \newpage\<close>


section\<open>The Global Architecture of HOL-CSPM\<close>

text\<open>
\begin{figure}[ht]
  \centering
  \includegraphics[width=0.85\textwidth]{session_graph.pdf}
	\caption{The overall architecture}
	\label{fig:fig1}
\end{figure}
\<close>

text\<open>The global architecture of HOL-CSPM is shown in \autoref{fig:fig1}.
The entire package resides on: 
\<^enum> \<^session>\<open>HOL-Eisbach\<close> from the Isabelle/HOL distribution,
\<^enum> \<^session>\<open>HOLCF\<close> from the Isabelle/HOL distribution, and
\<^enum> \<^session>\<open>HOL-CSP\<close> 2.0 from the Isabelle Archive of Formal Proofs.
\<close>

(*<*)
end
  (*>*)