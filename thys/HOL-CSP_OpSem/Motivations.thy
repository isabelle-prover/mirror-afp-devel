(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : HOL-CSP_OpSem - Operational semantics for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Burkhart Wolff
 *
 * This file       : Motivations for our future definitions
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

chapter \<open> Motivations for our Definitions \<close>

theory  Motivations
  imports AfterExt
begin


(*<*)
definition dummy_\<tau>_trans :: \<open>'\<alpha> process \<Rightarrow> '\<alpha> process \<Rightarrow> bool\<close> (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50)
  where \<open>P \<leadsto>\<^sub>\<tau> P' \<equiv> undefined\<close>

definition dummy_ev_trans :: \<open>'\<alpha> process \<Rightarrow> '\<alpha> event \<Rightarrow> '\<alpha> process \<Rightarrow> bool\<close> 
                             (\<open>_ \<leadsto>_/ _\<close> [50, 3, 51] 50)
  where \<open>P \<leadsto> e P' \<equiv> undefined\<close>
(*>*)


text \<open>To construct our bridge between denotational and operational semantics, we
      want to define two kind of transitions:  
      \<^item> without external event: \<^term>\<open>P \<leadsto>\<^sub>\<tau> P'\<close>
      \<^item> with an external event \<^term>\<open>e\<close> (which can possibly be \<^term>\<open>\<checkmark>\<close>): \<^term>\<open>P \<leadsto>e P'\<close>.

 
      We will discuss in this theory some fundamental properties that we want
     
      \<^term>\<open>P \<leadsto>\<^sub>\<tau> Q\<close> and \<^term>\<open>P \<leadsto>e Q\<close> to verify, and on the consequences that this will have.\<close>



text \<open>Let's say we want to define the \<open>\<tau>\<close> transition as an inductive
      predicate with three introduction rules:
      \<^item> we allow a process to make a \<open>\<tau>\<close> transition towards itself: \<^term>\<open>P \<leadsto>\<^sub>\<tau> P\<close>
      \<^item> the non-deterministic choice \<^const>\<open>Ndet\<close> can make a \<open>\<tau>\<close> transition to the 
        left side \<^term>\<open>P \<sqinter> Q \<leadsto>\<^sub>\<tau> P\<close>
      \<^item> the non-deterministic choice \<^const>\<open>Ndet\<close> can make a \<open>\<tau>\<close> transition to the
        right side \<^term>\<open>P \<sqinter> Q \<leadsto>\<^sub>\<tau> Q\<close>.\<close>

(*<*)
no_notation dummy_\<tau>_trans (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50)
(*>*)

inductive \<tau>_trans :: \<open>'\<alpha> process \<Rightarrow> '\<alpha> process \<Rightarrow> bool\<close> (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50)
  where \<tau>_trans_eq    : \<open>P \<leadsto>\<^sub>\<tau> P\<close>
  |     \<tau>_trans_NdetL : \<open>P \<sqinter> Q \<leadsto>\<^sub>\<tau> P\<close>
  |     \<tau>_trans_NdetR : \<open>P \<sqinter> Q \<leadsto>\<^sub>\<tau> Q\<close>

\<comment>\<open>We can obtain the same inductive predicate by removing 
   \<open>\<tau>_trans_eq\<close> and \<open>\<tau>_trans_NdetR\<close> clauses (because of \<^const>\<open>Ndet\<close> properties).\<close>


text \<open>With this definition, we immediately show that the \<open>\<tau>\<close>
      transition is the FD-refinement \<^term>\<open>(\<sqsubseteq>\<^sub>F\<^sub>D)\<close>.\<close>

lemma \<tau>_trans_is_FD: \<open>(\<leadsto>\<^sub>\<tau>) = (\<sqsubseteq>\<^sub>F\<^sub>D)\<close>
  apply (intro ext iffI)
  by (metis mono_Ndet_FD_left Ndet_commute \<tau>_trans.simps idem_FD)
     (metis mono_Ndet_FD mono_Ndet_FD_right 
            FD_antisym Ndet_id \<tau>_trans_NdetL idem_FD)



text \<open>The definition of the event transition will be a little bit more complex.

      First of all we want to prevent a process @{term [show_types] \<open>P::'\<alpha> process\<close>} to make a
      transition with @{term [show_types] \<open>e::'\<alpha> event\<close>} if \<^term>\<open>P\<close> can not begin with \<^term>\<open>e\<close>.

      More formally, we want \<^term>\<open>P \<leadsto>e P' \<Longrightarrow> e \<in> ready_set P\<close>.

      Moreover, we want the event transitions to absorb the \<open>\<tau>\<close> transitions.
      
      Finally, when \<^term>\<open>e \<in> ready_set P\<close>, we want to have \<^term>\<open>P \<leadsto>e (P afterExt e)\<close>.
    
      This brings us to the following inductive definition:\<close>

(*<*)
no_notation dummy_ev_trans (\<open>_ \<leadsto>_/ _\<close> [50, 3, 51] 50)
(*>*)

inductive event_trans_prem :: \<open>'\<alpha> process \<Rightarrow> '\<alpha> event \<Rightarrow> '\<alpha> process \<Rightarrow> bool\<close>
  where  
    \<tau>_left_absorb : \<open>\<lbrakk>e \<in> ready_set P'; P \<leadsto>\<^sub>\<tau> P'; event_trans_prem P' e P''\<rbrakk>
                     \<Longrightarrow> event_trans_prem P e P''\<close>
  | \<tau>_right_absorb : \<open>\<lbrakk>e \<in> ready_set P; event_trans_prem P e P'; P' \<leadsto>\<^sub>\<tau> P''\<rbrakk>
                      \<Longrightarrow> event_trans_prem P e P''\<close>
  | ready_trans_to_AfterExt : \<open>e \<in> ready_set P
                              \<Longrightarrow> event_trans_prem P e (P afterExt e)\<close>

abbreviation event_trans :: \<open>'\<alpha> process \<Rightarrow> '\<alpha> event \<Rightarrow> '\<alpha> process \<Rightarrow> bool\<close> 
             (\<open>_ \<leadsto>_/ _\<close> [50, 3, 51] 50)
  where \<open>P \<leadsto>e P' \<equiv> e \<in> ready_set P \<and> event_trans_prem P e P'\<close>



text \<open>We immediately show that this event transition definition is equivalent to the following:\<close>

lemma startable_imp_ev_trans_is_startable_and_FD_After: 
  \<open>(P \<leadsto>e P') \<longleftrightarrow> e \<in> ready_set P \<and> P afterExt e \<leadsto>\<^sub>\<tau> P'\<close>
proof safe
  show \<open>e \<in> ready_set P \<Longrightarrow> event_trans_prem P e P' \<Longrightarrow> P afterExt e \<leadsto>\<^sub>\<tau> P'\<close>
    apply (rotate_tac, induct rule: event_trans_prem.induct)
      apply (metis \<tau>_trans_is_FD mono_AfterExt_FD trans_FD)
     apply (metis \<tau>_trans_is_FD trans_FD)
    by (simp add: \<tau>_trans_is_FD)
next
  show \<open>e \<in> ready_set P \<Longrightarrow> P afterExt e \<leadsto>\<^sub>\<tau> P' \<Longrightarrow> event_trans_prem P e P'\<close>
    by (rule \<tau>_right_absorb[of e P \<open>P afterExt e\<close> P'])
       (simp_all add: ready_trans_to_AfterExt \<tau>_trans_is_FD)
qed



text \<open>With these two results, we are encouraged in the following theories to define:
      \<^item> \<^term>\<open>P \<leadsto>\<^sub>\<tau> Q \<equiv> P \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
      \<^item> \<^term>\<open>P \<leadsto>e Q \<equiv> e \<in> ready_set P \<and> P afterExt e \<leadsto>\<^sub>\<tau> Q\<close>


      and possible variations with other refinements.\<close>



end