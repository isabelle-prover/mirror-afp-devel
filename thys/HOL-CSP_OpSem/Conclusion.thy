(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : HOL-CSP_OpSem - Operational semantics for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Burkhart Wolff.
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

chapter \<open> Conclusion\<close>

(*<*)
theory  Conclusion
  imports Recovered_Laws CSP_New_Laws OpSem_Deadlock_Results
begin
  (*>*)

text \<open>We started by defining the operators \<^const>\<open>Sliding\<close>, \<^const>\<open>Throw\<close> and \<^const>\<open>Interrupt\<close>
      and provided on them several new laws, especially monotony, "step-law"
      (behaviour with @{term [source] \<open>\<box>a \<in> A \<rightarrow> P a\<close>}) and continuity.\<close>

text \<open>We defined the \<^const>\<open>initials\<close> notion, and described its behaviour with the reference
      processes and the operators of \<^session>\<open>HOL-CSP\<close> and \<^session>\<open>HOL-CSPM\<close>
      (which is already a minor contribution).\<close>

text \<open>As main contribution, we defined the @{const [source] \<open>After.After\<close>} operator which represents
      a bridge between the denotational and the versions of operational semantics for CSP.
      We made the construction as generic as possible, by exploiting the locale mechanism.
      Therefore we derive the correspondence between denotational and operational 
      semantics by construction. Based on failure divergence or trace divergence refinements, 
      the two operational semantics correspond to the versions described in
      \<^cite>\<open>"roscoe:csp:1998" and "DBLP:journals/entcs/Roscoe15"\<close>.

      We have slight variations that can open up for discussion.

      Thus, we provided a formal theory of operational behaviour for CSP, which is, to our
      knowledge, done for the first time for the entire language and the complete FD-Semantics
      model. Some of the proofs turned out to be extremely complex and out of reach of
      paper-and-pencil reasoning.\<close>

text \<open>A notable point is that the experimental order \<^term>\<open>(\<sqsubseteq>\<^sub>D\<^sub>T)\<close> behaves surprisingly well:
      initially pushed in \<^session>\<open>HOL-CSP\<close> for pure curiosity, it looks promising for future
      applications, since it gives a direct handle for an operational trace semantics for
      non-diverging processes which is executable.\<close>

text \<open>Another take-away is the development of alternatives with \<^term>\<open>(\<sqsubseteq>\<^sub>F)\<close> and
      \<^term>\<open>(\<sqsubseteq>\<^sub>T)\<close> orders but this remains a bit disappointing because their monotony w.r.t.
      to some operators does not allow to recover all the laws of 
      \<^cite>\<open>"roscoe:csp:1998" and "DBLP:journals/entcs/Roscoe15"\<close>.\<close>

text \<open>As a bonus we provided in \<^theory>\<open>HOL-CSP_OpSem.CSP_New_Laws\<close> some powerful laws for CSP.
      Here, we recall only the most important ones:
      
      \begin{center}  
      @{thm [mode = Rule, eta_contract = false] bij_Renaming_Hiding}

      @{thm [mode = Rule, eta_contract = false] bij_Renaming_Sync}

      @{thm [mode = Rule, eta_contract = false] Hiding_Mprefix_non_disjoint}
      \end{center}\<close>

text \<open>Finally, we discovered that the @{const [source] After.After} operator and its extensions
      @{const [source] AfterExt.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k} and @{const [source] AfterExt.After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e} have a real
      interest even without the construction of operational semantics.
      
      With induction rules based on @{const [source] AfterExt.After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e}, we could for
      example prove the following theorem:

      \begin{center}  
      @{thm [mode = Rule] AfterExt.data_independence_deadlock_free_Sync_bis}
      \end{center}\<close>

(*<*)
end
  (*>*)