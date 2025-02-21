(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : HOL-CSP_OpSem - Operational semantics for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Burkhart Wolff.
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
  imports "HOL-CSPM.CSPM_Laws"
begin 
  (*>*)

section \<open>Motivations\<close>

text \<open>\<^session>\<open>HOL-CSP\<close> \<^cite>\<open>"HOL-CSP-AFP"\<close> is a formalization in Isabelle/HOL of 
      the work of Hoare and Roscoe on the denotational semantics of the 
      Failure/Divergence Model of CSP. It follows essentially the presentation of CSP 
      in Roscoe's Book "Theory and Practice of Concurrency" \<^cite>\<open>"roscoe:csp:1998"\<close>
      and the semantic details in a joint paper of Roscoe and Brooks
      "An improved failures model for communicating processes" \<^cite>\<open>"brookes-roscoe85"\<close>.\<close>

text \<open>Basically, the session \<^session>\<open>HOL-CSP\<close> introduces the type \<^typ>\<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>,
      several classic CSP operators and number of ``laws'' (i.e. derived equations)
      that govern their interactions.
      \<^session>\<open>HOL-CSP\<close> has been extended by a theory of architectural operators \<^session>\<open>HOL-CSPM\<close> 
      inspired by the \<open>CSP\<^sub>M\<close> language of the model-checker FDR. While in FDR these operators are 
      basically macros over finite lists and sets, the \<^session>\<open>HOL-CSPM\<close> theory treats them in their
      own right for the most general cases.\<close>

text \<open>The present work addresses the problem of operational semantics for CSP which are the
      foundations for finite model-checking and process simulation techniques.
      In the literature, there are a few versions of operational semantics for CSP,
      which lend themselves to the constructions of labelled transition systems (LTS).
      Of course, denotational and operational constructs are expected to coincide, 
      but this is not obvious at first glance.
      As a key contribution, we will define the operational derivation operators \<open>P \<leadsto>\<^sub>\<tau> Q\<close>
      (``\<open>P\<close> evolves internally to \<open>Q\<close>) and \<open>P \<leadsto>\<^sub>e Q\<close> (``\<open>P\<close> evolves to \<open>Q\<close> by emitting \<open>e\<close>'')
      in terms of the denotational semantics and derive the expected laws for
      operational semantics from these.
      It has been published in ITP24 \<^cite>\<open>"DBLP:conf/itp/BallenghienW24"\<close>\<close>


text \<open>The overall objective of this work is to provide a formal, machine checked foundation
      for the laws provided by Roscoe in \<^cite>\<open>"roscoe:csp:1998" and "DBLP:journals/entcs/Roscoe15"\<close>.\<close>

text \<open>\newpage\<close>





section\<open>The Global Architecture of \<^session>\<open>HOL-CSP_OpSem\<close>\<close>

text\<open>
\begin{figure}[ht]
  \centering
  \includegraphics[width=0.50\textwidth]{session_graph.pdf}
	\caption{The overall architecture}
	\label{fig:fig1}
\end{figure}
\<close>

text\<open>The global architecture of \<^session>\<open>HOL-CSP_OpSem\<close> is shown in \autoref{fig:fig1}.

     The package resides on:
     \<^item> \<^session>\<open>HOL-CSP\<close> 2.0 from the Isabelle Archive of Formal Proofs
     \<^item> \<^session>\<open>HOL-CSPM\<close> from the Isabelle Archive of Formal Proofs.
\<close>

(*<*)
end
  (*>*)