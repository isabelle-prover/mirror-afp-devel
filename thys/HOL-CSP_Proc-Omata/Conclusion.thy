(***********************************************************************************
 * Copyright (c) 2025 Université Paris-Saclay
 *
 * Author: Benoît Ballenghien, Université Paris-Saclay,
 *         CNRS, ENS Paris-Saclay, LMF
 * Author: Burkhart Wolff, Université Paris-Saclay,
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
theory Conclusion
  imports "HOL-CSP_Proc-Omata" Compactification_DiningPhilosophers "HOL-Library.LaTeXsugar"
begin
  (*>*)

section \<open>Conclusion\<close>


text \<open>
In this entry we have developed the Proc-Omata framework on top
of \<^session>\<open>HOL-CSP\<close> and its extensions.
Starting from functional automata, we introduced Proc-Omata in four variants:
deterministic, terminating deterministic, non-deterministic,
and terminating non-deterministic. They enjoy strong structural properties,
for example deadlocks can be characterized directly and established by invariant reasoning:
\begin{center}
@{thm deadlock_free_P_nd_iff[no_vars]}

@{thm [mode = Rule] deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_iff[no_vars]}
\end{center}

We then lifted sequential composition and synchronization product to the automata level,
by defining suitable combination functions and proving their correctness.
A major generalization of our development is the treatment of parameterized termination.
For sequential composition we worked directly with the generalized operator \<^term>\<open>(\<^bold>;\<^sub>\<checkmark>)\<close>,
since the standard one \<^term>\<open>(\<^bold>;)\<close> is easily recovered (indeed @{thm Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_const[no_vars]}).
In contrast, for synchronization product we had to provide two distinct versions,
as the handling of ticks prevents any straightforward reduction from \<^term>\<open>P \<lbrakk>A\<rbrakk> Q\<close> to \<open>P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q\<close>.

Another central ingredient is the library \<^session>\<open>Restriction_Spaces\<close>~\<^cite>\<open>"Restriction_Spaces-AFP"\<close>.
Proc-Omata are indeed defined as fixed points of endofunctions which,
in the non-deterministic case, are not always continuous due to global non-deterministic choice.
While deterministic prefix choice does not suffice to restore continuity under composition,
it does guarantee constructiveness, allowing us to rely on the fixed-point operator \<^term>\<open>\<upsilon> x. f x\<close> in all cases.

The resulting framework yields compactification theorems that support
invariant-based reasoning over large process architectures:
\begin{center}
@{thm [eta_contract = false, mode = Rule] P_nd_compactification_Sync[no_vars]}
\end{center}

Finally, we demonstrated the applicability of our approach with the Dining
Philosophers case study, where Proc-Omata compactification enables proofs that scale
to an arbitrary number of participants in this parameterized process architecture.
\<close>


(*<*)
end
  (*>*)
