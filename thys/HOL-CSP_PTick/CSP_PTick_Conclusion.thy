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
theory CSP_PTick_Conclusion
  imports "HOL-CSP_PTick" "HOL-Library.LaTeXsugar"
begin
  (*>*)

section \<open>Conclusion\<close>

subsection \<open>Summary\<close>

text \<open>
In this session, we introduced generalized versions of the sequential composition
and synchronization operators, thus completing the generalization of \<^session>\<open>HOL-CSP\<close>
(and its extensions) to support parameterized termination.
The main motivation was to propagate return values across processes,
so that algebraic laws such as those involving \<^const>\<open>SKIP\<close> continue to hold
in a natural way.
While the sequential composition adapts relatively smoothly,
the synchronization product required a more substantial redesign:
the interleaving theory of the classical \<^const>\<open>Sync\<close> operator could not be reused,
and the failures specification had to be carefully adjusted.

Overall, the results confirm that the parameterized setting integrates well
with the broader CSP framework.
Most classical laws remain valid with only minor modifications,
and the new operators exhibit the algebraic and operational properties one expects.
The formalization is fairly extensive and provides a solid foundation
for further developments of CSP theories with enriched termination behavior.
\<close>

(* text \<open>
In this session, we gave generalizations for the sequential composition
product and the synchronization product that behave better with respect to
the parameterized termination recently introduced in \<^session>\<open>HOL-CSP\<close>.

Most of the work was dedicated to the synchronization product, mainly
because the trace interleaving theory of the already defined \<^const>\<open>Sync\<close>
operator could not be reused and had to be rebuilt from scratch,
but also because adapting the failures specification was not straightforward.

The formalization is quite consequent, so we will only mention below
a small number of the definitions and results that can found in this session.
\<close> *)


subsection \<open>Sequential Composition\<close>

text (in OpSemTransitionsSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<open>
The new version of the sequential composition is of type
\<^typ>\<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>,
so that the process on the right-hand side is now parameterized with the value
returned by the process on the left-hand side.
The main motivation for this generalization was to have \<^const>\<open>SKIP\<close>
as neutral element. This is now the case.

\begin{center}
@{thm Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP[of P]} \qquad
@{thm SKIP_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[of r Q]}
\end{center}

Additionally, with the following associativity property :
\begin{center}
@{thm Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc[of P Q R]}
\end{center}
we can conclude that this generalized sequential composition fulfills the monad laws.

Unsurprisingly, the correspondence with classical version is very intuitive.

\begin{center}
@{thm Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_const[of P Q]}
\end{center}

The expected step law has also been established.

\begin{center}
@{thm[eta_contract = false] Mprefix_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[of A P Q]}
\end{center}

Additionally, in the same way as described in \<^cite>\<open>ITP_OpSem\<close>, operational laws have been derived.

\begin{center}
@{thm[mode=Rule] Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_OpSem_rules(1)[of P P' Q]} \qquad
@{thm[mode=Rule] Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_OpSem_rules(2)[of a P P' Q]} \qquad
@{thm[mode=Rule] Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_OpSem_rules(3)[of r P P' Q Q']}
\end{center}

The continuity has only be obtained under a kind of finiteness assumption,
but non-destructiveness holds in general.

Finally, an architectural version is defined. It satisfies the following property.

\begin{center}
@{thm [eta_contract = false, break] MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_append[of L1 L2 P]}
\end{center}
\<close>


subsection \<open>Synchronization Product\<close>

text (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) \<open>
The main motivation for generalizing the synchronization product was to
have a satisfying handling of the synchronization of two terminations.
Indeed, with the \<^const>\<open>Sync\<close> operator inherited from \<^session>\<open>HOL-CSP\<close>,
the returned values were lost (most of the time).

\begin{center}
@{thm SKIP_Sync_SKIP[of r A s]}
\end{center}

With the new definition, this is not the case anymore.

\begin{center}
@{thm [display] SKIP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP[of r A s]}
\end{center}

This law is directly extracted from the core of the construction, which is done in a very
abstract way through a \<^theory_text>\<open>locale\<close> specification.
The operator is then declined in several variations, leading to the following rules.

\begin{center}
@{thm SKIP_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_SKIP[of r A s]}

@{thm SKIP_Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_SKIP[of r A s]}

@{thm SKIP_Sync\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_SKIP[of r A s]}

@{thm SKIP_Sync\<^sub>L\<^sub>l\<^sub>i\<^sub>s\<^sub>t_SKIP[of r A s]}

@{thm [break] SKIP_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_SKIP[of n r A s]}

@{thm [break] SKIP_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>R_SKIP[of n r A s]}

@{thm [break] SKIP_Sync\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s_SKIP[of n m r A s]}

@{thm SKIP_Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c_SKIP[of r A s]}

\end{center}

Moreover, the last declension is proved to be equal to the old version,
ensuring that this work is actually a generalization.

\begin{center}
@{thm Sync\<^sub>C\<^sub>l\<^sub>a\<^sub>s\<^sub>s\<^sub>i\<^sub>c_is_Sync[of P A Q]}
\end{center}

We also established commutativity and associativity, modulo renaming the ticks.
The underlying abstract setup is quite obscure, so we will only display here the pair versions.

\begin{center}
@{thm Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_commute[of P A Q]}

@{thm [break] Sync\<^sub>P\<^sub>a\<^sub>i\<^sub>r_assoc[of P A Q R]}
\end{center}

Again, the expected step law has been established.

\begin{center}
@{thm[eta_contract = false] Mprefix_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[of A P Q]}
\end{center}
\<close>

text (in OpSemTransitions_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) \<open>
In this abstract setup, the operational laws have also been derived.

\begin{center}
@{thm[mode=Rule, eta_contract=false] Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_OpSem_rules(1)[of P P' A Q]} \qquad
@{thm[mode=Rule, eta_contract=false] Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_OpSem_rules(2)[of Q Q' A P]}

@{thm[mode=Rule, eta_contract=false] Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_OpSem_rules(3)[of a A P P' Q]} \qquad
@{thm[mode=Rule, eta_contract=false] Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_OpSem_rules(4)[of a A Q Q' P]}

@{thm[mode=Rule, eta_contract=false] Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_OpSem_rules(5)[of a A P P' Q Q']}

@{thm[mode=Rule, eta_contract=false] Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_OpSem_rules(6)[of P r P' A Q]}

@{thm[mode=Rule, eta_contract=false] Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_OpSem_rules(7)[of Q s Q' P A]}

@{thm[mode=Rule] Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_OpSem_rules(8)[of r s r_s A]}
\end{center}
\<close>


text (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) \<open>
Continuity and non-destructiveness hold in general,
and an architectural version is defined. It satisfies the following property.

\begin{center}
@{thm [eta_contract = false, mode = Rule] MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_append[of L1 L2 S P]}
\end{center}

It is defined on a list (while its counterpart \<^const>\<open>MultiSync\<close> based on the \<^const>\<open>Sync\<close> operator
is defined on a multiset) because the order of appearance of the ticks matters.
However, as long as we keep track of the positions, we can permute the list.
This is summarized by the following theorem.

\begin{center}
@{thm [eta_contract = false, mode = Rule] MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_permute_list[of f L S P]}
\end{center}
\<close>



(*<*)
end
  (*>*)
