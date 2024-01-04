(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSPM - Architectural operators for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff
 *
 * This file       : Conclusion
 *
 * Copyright (c) 2023 Université Paris-Saclay, France
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


chapter\<open> Conclusion \<close>

(*<*)
theory Conclusion                                               
  imports DeadlockResults "HOL-Library.LaTeXsugar"
begin 
(*>*)


text \<open>In this session, we defined five architectural operators: \<^const>\<open>MultiDet\<close>, \<^const>\<open>MultiNdet\<close>
      and \<^const>\<open>GlobalNdet\<close>, \<^const>\<open>MultiSync\<close>, and \<^const>\<open>MultiSeq\<close> as respective generalizations 
      of \<^term>\<open>P \<box> Q\<close>, \<^term>\<open>P \<sqinter> Q\<close>, \<^term>\<open>P \<lbrakk>S\<rbrakk> Q\<close>, and \<^term>\<open>P \<^bold>; Q\<close>.\<close>

text \<open>We did this in a fully-abstract way, that is:
      \<^item> \<^const>\<open>Det\<close> is commutative, idempotent and admits \<^const>\<open>STOP\<close> as a neutral element so
        we defined \<^const>\<open>MultiDet\<close> on a \<^const>\<open>finite\<close> \<^typ>\<open>'\<alpha> set\<close> \<^term>\<open>A\<close> by making it equal
        to \<^const>\<open>STOP\<close> when \<^term>\<open>A = {}\<close>.

      \<^item> \<^const>\<open>Ndet\<close> is also commutative and idempotent so we defined \<^const>\<open>MultiNdet\<close>
        on a \<^const>\<open>finite\<close> \<^typ>\<open>'\<alpha> set\<close> \<^term>\<open>A\<close> by making it equal 
        to \<^const>\<open>STOP\<close> when \<^term>\<open>A = {}\<close>. Beware of the fact that \<^const>\<open>STOP\<close> is not the
        neutral element for \<^const>\<open>Ndet\<close> (this operator does not admit a neutral element) so 
        we \<^bold>\<open>do not have\<close> the equality
        @{term [display, eta_contract = false] \<open>(\<Sqinter>p \<in> {a}. P p) = P a \<sqinter> (\<Sqinter>p \<in> {}. P p)\<close>}
        while this holds for \<^const>\<open>Det\<close> and \<^const>\<open>MultiDet\<close>).

        As its failures and divergences can easily be generalized to the infinite case,
        we also defined \<^const>\<open>GlobalNdet\<close> verifying
        @{thm [display, eta_contract = false] finite_GlobalNdet_is_MultiNdet[no_vars]}

      \<^item> \<^const>\<open>Sync\<close> is commutative but is not idempotent so we defined \<^const>\<open>MultiSync\<close>
        on a \<^typ>\<open>'\<alpha> multiset\<close> \<^term>\<open>M\<close> to keep the multiplicity of the processes.
        We made it equal to \<^const>\<open>STOP\<close> when \<^term>\<open>M = {#}\<close> but like \<^const>\<open>Ndet\<close>,
        \<^const>\<open>Sync\<close> does not admit a neutral element so beware of the fact that in general
        @{term [display, eta_contract = false] \<open>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk>p \<in># {#a#}. P p) \<noteq> P a \<lbrakk>S\<rbrakk> (\<^bold>\<lbrakk>S\<^bold>\<rbrakk>p \<in># {#}. P p)\<close>}

      \<^item> \<^const>\<open>Seq\<close> is neither commutative nor idempotent, so we defined \<^const>\<open>MultiSeq\<close>
        on a \<^typ>\<open>'\<alpha> list\<close> \<^term>\<open>L\<close> to keep the multiplicity and the order of the processes.
        Since \<^const>\<open>SKIP\<close> is the neutral element for \<^const>\<open>Seq\<close>, we have
        @{term [display, eta_contract = false] \<open>(SEQ p \<in>@ [a]. P p) = (SEQ p \<in>@ []. P p) \<^bold>; P a\<close>}
        @{term [display, eta_contract = false] \<open>(SEQ p \<in>@ [a]. P p) = P a \<^bold>; (SEQ p \<in>@ []. P p)\<close>}\<close>

text \<open>On our architectural operators we proved continuity (under weakest liberal assumptions),
      wrote refinements rules and obtained results about the behaviour with other
      operators inherited from the binary rules.\<close>

text \<open>We presented two examples: Dining Philosophers, and POTS.

      In both, we underlined the usefulness of the architectural operators
      for modeling complex systems.\<close>

text \<open>Finally we provided powerful results on \<^const>\<open>events_of\<close> and \<^const>\<open>deadlock_free\<close>
      among which the most important is undoubtedly :
      
         @{thm [display, eta_contract = false] MultiInter_deadlock_free[no_vars]}
      
      This theorem allows, for example, to establish:

         @{term [display, eta_contract = false]
             \<open>0 < n \<Longrightarrow> deadlock_free (\<^bold>|\<^bold>|\<^bold>| i \<in># mset [0..<n]. P i)\<close>}

      under the assumption that a family of processes parameterized by
      \<^term>\<open>i\<close> @{text "::"} \<^typ>\<open>nat\<close> verifies \<^term>\<open>\<forall>i < n::nat. deadlock_free (P i)\<close>.
      \<close>

(*<*)
end
(*>*)