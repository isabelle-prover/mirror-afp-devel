(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff, Lina Ye.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : Conclusion
 *
 * Copyright (c) 2009 Université Paris-Sud, France
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

chapter\<open>Conclusion\<close>

(*<*)
theory Conclusion
  imports CSP
begin
  (*>*)

section\<open>Related Work\<close>
text\<open>As mentioned earlier, this work has its very ancient roots in a first formalization 
of A. Camilieri in the early 90s in HOL. This work was reformulated and substantially
extended in HOL-CSP 1.0 published in 1997. In 2005, Roggenbach and Isobe published 
CSP-Prover, a formal theory of a (fragment of) the Failures model of CSP. This work 
led to a couple of publications culminating in \<^cite>\<open>"IsobeRoggenbach2010"\<close>; emphasis was put
on actually completing the CSP theory up to the point where it is sufficiently tactically
supported to serve as a kind of tool. This theory is still maintained and last releases (the 
latest one was released on 18 February 2019) can be
found under \<^url>\<open>https://staff.aist.go.jp/y-isobe/CSP-Prover/CSP-Prover.html\<close>. This theory
represents the first half of Roscoes theory of a Failures/Divergence model, i.e. the Failures part.
More recently, Pasquale Noce 
\<^cite>\<open>"Noninterference_CSP-AFP" and "Noninterference_Sequential_Composition-AFP" and 
"Noninterference_Concurrent_Composition-AFP"\<close>
developed a theory of non interference notions based on an abstract denotational model fragment of 
the Failure/Divergence Model of CSP (without continuity and algebraic laws); this theory could 
probably be rebuilt on top of our work.

The present work could be another, more ``classic'' foundation of test-generation techniques
of this kind paving the way to an interaction with FDR and its possibility to generate
labelled transition systems as output that could drive specialized tactics in HOL-CSP 2.0.
\<close>

section\<open>Lessons learned\<close>
text\<open>We have ported a first formalization in Isabelle/HOL on the Failure/Divergence model of CSP, 
done with Isabelle93-7 in 1997, to a modern Isabelle version. Particularly, 
we use the modern declarative proof style available in Isabelle/Isar instead of imperative proof 
one, the latter being  used in the old version. On the one hand, it is worth noting that some of 
the old  theories still have a surprisingly high value: Actually it took time to develop the right 
granularity of abstraction in lemmas, which is thus still quite helpful and valuable to reconstruct 
the theory in the new version. If a substantially large body of lemmas is available, the degree of 
automation tends to increase. On the other hand, redevelopment from scratch is unavoidable in parts 
where basic libraries change. For example, this was a necessary consequence of our decision to base
HOL-CSP 2.0 on HOLCF instead of continuing the development of an older fixed-point theory; nearly
all continuity proofs had to be redeveloped. Moreover, a fresh look on old proof-obligations 
may incite unexpected generalizations and some newly proved lemmas that cannot be constructed in 
the old version even with several attempts. The influence of the chosen strategy (from scratch
or refactoring) on the proof length is inconclusive.

Note that our data does not allow to make a prediction on the length of a porting project --- 
the effort was distributed over a too long period and performed by a team with initially very 
different knowledge about CSP and interactive theorem proving.

It is also worth noting that the restructuring of the theory, as well as the proofs
(declarative Isar style), has substantially increased the possibility to parallelize
the proof checking process and makes the entire theory more maintainable. 

Finally, having the entire theory formalized makes extensions such as parametized ticks
possible since the effect of changes of basic definitions can be traced consequently.
This is an important aspect that extensions of this kind are not ad hoc and do not endanger
global consistency.
\<close>


section\<open>A Summary on New Results\<close>
text\<open>Compared to the original version of HOL-CSP 1.0, the present theory is complete relative to
Roscoe's Book\<^cite>\<open>"roscoe:csp:1998"\<close>. It contains a number of new theorems and some interesting
(and unexpected) generalizations: 
\<^enum> @{thm mono_Hiding} is now also valid for the infinite case (arbitrary hide-set A).
\<^enum> \<^term>\<open>P \ (A \<union> B) = (P \ A) \ B\<close> is true for \<^term>\<open>finite A\<close> (see @{thm Hiding_Un});
  this was not even proven in HOL-CSP 1.0 for the singleton case! It can be considered as the
  most complex theorem of this theory.
\<^enum> distribution laws of \<^const>\<open>Hiding\<close> over \<^const>\<open>Sync\<close> @{thm Hiding_Sync}; 
  however, this works only in the finite case. A true monster proof.
\<^enum> distribution of \<^const>\<open>Mprefix\<close> over \<^const>\<open>Sync\<close> @{thm Mprefix_Sync_Mprefix} in the most
  generalized case. Also a true monster proof, but reworked using symmetries and
  abstractions to be more reasonable (and faster) 
\<^enum> the synchronization operator is associative @{thm "Sync_assoc"}.
  (In HOL-CSP 1.0, this had only be shown for special cases like @{thm Sync_assoc[where S = \<open>UNIV\<close>]}).
\<^enum> the generalized non deterministic prefix choice operator --- relevant for proofs of deadlock-freeness ---
  has been added to the theory @{thm "Mndetprefix_def"}; it is proven monotone and
  continuous @{thm Mndetprefix_cont} in the general case
  (in contrast to the global choice without prefix, see @{thm GlobalNdet_cont}).
  This is relevant for the definition of the deadlock reference processes @{thm DF_def} and @{thm "DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def"}.
\<^enum> since Isabelle-2025, new support for read \<^term>\<open>c\<^bold>?a\<in>A \<rightarrow> P a\<close> and non deterministic write
  \<^term>\<open>c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a\<close> has been added. Also, sliding choice has been added and new algebraic
  laws involving this operator (see @{thm Hiding_Mprefix_non_disjoint}) have been proven.
\<close>

(*<*)
end
  (*>*)
