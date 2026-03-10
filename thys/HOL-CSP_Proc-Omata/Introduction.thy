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

chapter \<open>Introduction\<close>

(*<*)
theory Introduction
  imports "HOL-CSP_PTick"
begin
  (*>*)


text \<open>
Communicating Sequential Processes (CSP) offers a rich and expressive
framework for modeling and reasoning about concurrent systems.
Its denotational, operational, and algebraic facets are covered by the
sessions \<^session>\<open>HOL-CSP\<close>~\<^cite>\<open>"HOL-CSP-AFP"\<close>, \<^session>\<open>HOL-CSPM\<close>~\<^cite>\<open>"HOL-CSPM-AFP"\<close>,
\<^session>\<open>HOL-CSP_OpSem\<close>~\<^cite>\<open>"HOL-CSP_OpSem-AFP"\<close>, \<^session>\<open>HOL-CSP_RS\<close>~ \<^cite>\<open>"HOL-CSP_RS-AFP"\<close>,
and \<^session>\<open>HOL-CSP_PTick\<close>.
These developments, initially following Roscoe’s presentation \<^cite>\<open>"roscoe:csp:1998"\<close>,
have since evolved considerably to admit arbitrary types, infinite sets,
parameterized termination, and more.

However, this expressiveness comes with a cost:
proofs about complex or parametric process architectures
often become intricate and hard to scale.
Proc-Omata address this issue by slightly constraining the class
of processes in order to benefit from more powerful proof techniques.
First sketched in \<^cite>\<open>IFM_Dining_Phil\<close> and properly
conceptualized in \<^cite>\<open>"ICTAC_Proc-Omata"\<close>, the Proc-Omata framework consists
in embedding functional automata into CSP.
The resulting subclass of processes combines the expressive and compositional
features of CSP with automata-like properties
(reachability, enableness, absence of divergences),
making it particularly amenable to invariant reasoning.

In this entry we start by formalizing the basic notions of
functional automata such as reachability and enableness,
before introducing the definitions of Proc-Omata themselves.
For synchronization product and sequential composition,
we then provide combination functions that realize the effect
of CSP operators at the level of the underlying automata.
These translations are formally proved correct,
and culminate in compactification theorems,
which generalize the constructions inductively to architectural operators.
\<close>


(*<*)
end
  (*>*)