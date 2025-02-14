(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSPM - Architectural operators for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff.
 *
 * This file       : Conclusion
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


chapter\<open> Conclusion \<close>

(*<*)
theory Conclusion                                               
  imports CSPM "HOL-Library.LaTeXsugar"
begin 
  (*>*)



text \<open>In this session, we defined three architectural operators: \<^const>\<open>GlobalDet\<close>,
      \<^const>\<open>MultiSync\<close>, and \<^const>\<open>MultiSeq\<close> as respective generalizations 
      of \<^term>\<open>P \<box> Q\<close>, \<^term>\<open>P \<lbrakk>S\<rbrakk> Q\<close>, and \<^term>\<open>P \<^bold>; Q\<close>.
      The generalization of \<^term>\<open>P \<sqinter> Q\<close>, \<^term>\<open>GlobalNdet\<close>, is already in
      \<^session>\<open>HOL-CSP\<close> since it is required for some algebraic laws.\<close>



text \<open>We did this in a fully-abstract way, that is:
      \<^item> \<^const>\<open>Det\<close> is commutative, idempotent and admits \<^const>\<open>STOP\<close> as a neutral element so
        we defined \<^const>\<open>GlobalDet\<close> on a \<^typ>\<open>'a set\<close> \<^term>\<open>A\<close> by making it equal
        to \<^const>\<open>STOP\<close> when \<^term>\<open>A = {}\<close>. Continuity only holds for finite cases,
        while the operator is always defined.

      \<^item> \<^const>\<open>Ndet\<close> is also commutative and idempotent so in \<^session>\<open>HOL-CSP\<close>
        \<^const>\<open>GlobalNdet\<close> has been defined
        on a \<^typ>\<open>'a set\<close> \<^term>\<open>A\<close> by making it equal to \<^const>\<open>STOP\<close> when \<^term>\<open>A = {}\<close>.
        Beware of the fact that \<^const>\<open>STOP\<close> is not the
        neutral element for \<^const>\<open>Ndet\<close> (this operator does not admit a neutral element) so 
        we \<^bold>\<open>do not have\<close> the equality
        @{term [display, eta_contract = false] \<open>(\<sqinter>p \<in> {a}. P p) = P a \<sqinter> (\<sqinter>p \<in> {}. P p)\<close>}
        while this holds for \<^const>\<open>Det\<close> and \<^const>\<open>GlobalDet\<close>).
        Again, continuity only holds for finite cases.

      \<^item> \<^const>\<open>Sync\<close> is commutative but is not idempotent so we defined \<^const>\<open>MultiSync\<close>
        on a \<^typ>\<open>'a multiset\<close> \<^term>\<open>M\<close> to keep the multiplicity of the processes.
        We made it equal to \<^const>\<open>STOP\<close> when \<^term>\<open>M = {#}\<close> but like \<^const>\<open>Ndet\<close>,
        \<^const>\<open>Sync\<close> does not admit a neutral element so beware of the fact that in general
        @{term [display, eta_contract = false] \<open>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk>p \<in># {#a#}. P p) \<noteq> P a \<lbrakk>S\<rbrakk> (\<^bold>\<lbrakk>S\<^bold>\<rbrakk>p \<in># {#}. P p)\<close>}.
        By construction, multiset are finite and therefore continuity holds.

      \<^item> \<^const>\<open>Seq\<close> is neither commutative nor idempotent, and \<^term>\<open>SKIP r\<close> is neutral only on
        the left hand side (note if the second type \<^typ>\<open>'r\<close> of \<^typ>\<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> is actually
        \<^typ>\<open>unit\<close>, that is to say we go back to the old version without parameterized termination,
        it is neutral element on both sides, see @{thm Seq_SKIP SKIP_Seq}).
        Therefore we defined \<^const>\<open>MultiSeq\<close> on a \<^typ>\<open>'a list\<close> \<^term>\<open>L\<close> to keep the multiplicity
        and the order of the processes, and the folding is done on the reversed list in order to
        enjoy the neutrality of \<^term>\<open>SKIP r\<close> on the left hand side.
        For example, proving
        @{term [eta_contract = false] \<open>SEQ p \<in>@ L1. P p \<^bold>; SEQ p \<in>@ L2. P p = SEQ p \<in>@ (L1 @ L2). P p\<close>}
        in general requires \<^term>\<open>L2 \<noteq> []\<close>.\<close>



text \<open>We presented two examples: Dining philosophers, and POTS.

      In both, we underlined the usefulness of the architectural operators
      for modeling complex systems.\<close>

text \<open>Finally we provided powerful results on \<^const>\<open>events_of\<close> and \<^const>\<open>deadlock_free\<close>
      among which the most important is undoubtedly:
      
         @{thm [display, eta_contract = false] MultiInter_deadlock_free[no_vars]}
      
      This theorem allows, for example, to establish:

         @{term [display, eta_contract = false]
             \<open>0 < n \<Longrightarrow> deadlock_free (\<^bold>|\<^bold>|\<^bold>| m \<in># mset [0..<n]. P m)\<close>}

      under the assumption that a family of processes parameterized by
      \<^term>\<open>m\<close> @{text "::"} \<^typ>\<open>nat\<close> verifies \<^term>\<open>\<forall>m < n::nat. deadlock_free (P m)\<close>.
      \<close>

text \<open>More recently, two operators \<^const>\<open>Throw\<close> and \<^const>\<open>Interrupt\<close> have been added.
      The corresponding continuities and algebraic laws can also be found
      in this session.\<close>

(*<*)
end
  (*>*)