(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : HOL-CSP_OpSem - Operational semantics for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Burkhart Wolff
 *
 * This file       : Motivations for our future definitions
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

chapter \<open> Motivations for our Definitions \<close>

(*<*)
theory  Motivations
  imports After_Ext_Operator
begin
  (*>*)

(*<*)
definition dummy_\<tau>_trans :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close> (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50)
  where \<open>P \<leadsto>\<^sub>\<tau> P' \<equiv> undefined\<close>

definition dummy_event_trans :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (\<open>_ \<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
  where \<open>P \<leadsto>\<^bsub>e\<^esub> P' \<equiv> undefined\<close>

definition dummy_tick_trans :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close> (\<open>_ \<leadsto>\<^sub>\<checkmark>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
  where \<open>P \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> P' \<equiv> undefined\<close>
    (*>*)


text \<open>To construct our bridge between denotational and operational semantics, we
      want to define two kind of transitions:  
      \<^item> without external event: \<^term>\<open>P \<leadsto>\<^sub>\<tau> P'\<close>
      \<^item> with the terminating event \<^term>\<open>\<checkmark>(r)\<close>: \<^term>\<open>P \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> P'\<close>
      \<^item> with a non terminating external event \<^term>\<open>ev e\<close>: \<^term>\<open>P \<leadsto>\<^bsub>e\<^esub> P'\<close>.

      We will discuss in this theory some fundamental properties that we want
     
      \<^term>\<open>P \<leadsto>\<^sub>\<tau> Q\<close>, \<^term>\<open>P \<leadsto>\<^bsub>e\<^esub> P'\<close> and \<^term>\<open>P \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> P'\<close> to verify, and the consequences that this will have.\<close>



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

inductive \<tau>_trans :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close> (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50)
  where \<tau>_trans_eq    : \<open>P \<leadsto>\<^sub>\<tau> P\<close>
  |     \<tau>_trans_NdetL : \<open>P \<sqinter> Q \<leadsto>\<^sub>\<tau> P\<close>
  |     \<tau>_trans_NdetR : \<open>P \<sqinter> Q \<leadsto>\<^sub>\<tau> Q\<close>

\<comment>\<open>We can obtain the same inductive predicate by removing 
   \<open>\<tau>_trans_eq\<close> and \<open>\<tau>_trans_NdetR\<close> clauses (because of \<^const>\<open>Ndet\<close> properties).\<close>


text \<open>With this definition, we immediately show that the \<open>\<tau>\<close>
      transition is the FD-refinement \<^term>\<open>(\<sqsubseteq>\<^sub>F\<^sub>D)\<close>.\<close>

lemma \<tau>_trans_is_FD: \<open>(\<leadsto>\<^sub>\<tau>) = (\<sqsubseteq>\<^sub>F\<^sub>D)\<close>
  apply (intro ext iffI)
  by (metis Ndet_FD_self_left Ndet_FD_self_right \<tau>_trans.simps order_class.order_eq_iff)
    (metis FD_antisym Ndet_FD_self_left Ndet_id \<tau>_trans_NdetR mono_Ndet_FD)


(*<*)
context AfterExt
begin
  (*>*)

text \<open>The definition of the event transition will be a little bit more complex.

      First of all we want to prevent a process @{term [show_types] \<open>P :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>}
      to make a transition with @{term [show_types] \<open>ev e :: ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>}
      (resp. @{term [show_types] \<open>\<checkmark>(r) :: ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>})
      if \<^term>\<open>P\<close> can not begin with \<^term>\<open>ev e\<close> (resp. \<^term>\<open>\<checkmark>(r)\<close>).

      More formally, we want \<^term>\<open>P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow> ev e \<in> initials P\<close> (resp. \<^term>\<open>P \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> P' \<Longrightarrow> \<checkmark>(r) \<in> P\<^sup>0\<close>).

      Moreover, we want the event transitions to absorb the \<open>\<tau>\<close> transitions.
      
      Finally, when \<^term>\<open>e \<in> P\<^sup>0\<close> (resp. \<^term>\<open>\<checkmark>(r) \<in> P\<^sup>0\<close>), we want to have
      \<^term>\<open>P \<leadsto>\<^bsub>e\<^esub> P after\<^sub>\<checkmark> ev e\<close> (resp. \<^term>\<open>P \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> P after\<^sub>\<checkmark> \<checkmark>(r)\<close>).
    
      This brings us to the following inductive definition:\<close>

(*<*)
no_notation dummy_event_trans (\<open>_ \<leadsto>\<^bsub>_\<^esub> _\<close>  [50, 3, 51] 50)
no_notation dummy_tick_trans  (\<open>_ \<leadsto>\<^sub>\<checkmark>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
  (*>*)

inductive event_trans_prem :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close>
  where  
    \<tau>_left_absorb : \<open>\<lbrakk>e \<in> initials P'; P \<leadsto>\<^sub>\<tau> P'; event_trans_prem P' e P''\<rbrakk>
                     \<Longrightarrow> event_trans_prem P e P''\<close>
  | \<tau>_right_absorb : \<open>\<lbrakk>e \<in> initials P; event_trans_prem P e P'; P' \<leadsto>\<^sub>\<tau> P''\<rbrakk>
                      \<Longrightarrow> event_trans_prem P e P''\<close>
  | initial_trans_to_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k : \<open>e \<in> initials P \<Longrightarrow> event_trans_prem P e (P after\<^sub>\<checkmark> e)\<close>

abbreviation event_trans :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> 'a \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close> 
  (\<open>_ \<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
  where \<open>P \<leadsto>\<^bsub>e\<^esub> P' \<equiv> ev e \<in> initials P \<and> event_trans_prem P (ev e) P'\<close>

abbreviation tick_trans :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> 'r \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close> (\<open>_ \<leadsto>\<^sub>\<checkmark>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
  where \<open>P \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> P' \<equiv> \<checkmark>(r) \<in> P\<^sup>0 \<and> event_trans_prem P \<checkmark>(r) P'\<close>



text \<open>We immediately show that, under the assumption of monotony of \<^term>\<open>\<Omega>\<close>,
      this event transition definition is equivalent to the following:\<close>

lemma startable_imp_ev_trans_is_startable_and_FD_After: 
  \<open>(case e of ev x \<Rightarrow> P \<leadsto>\<^bsub>x\<^esub> P' | \<checkmark>(r) \<Rightarrow> P \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> P') \<longleftrightarrow> e \<in> P\<^sup>0 \<and> P after\<^sub>\<checkmark> e \<leadsto>\<^sub>\<tau> P'\<close>
  if \<open>\<And>P Q. case e of \<checkmark>(r) \<Rightarrow> \<Omega> P r \<leadsto>\<^sub>\<tau> \<Omega> Q r\<close>
proof -
  have \<open>(case e of ev x \<Rightarrow> P \<leadsto>\<^bsub>x\<^esub> P' | \<checkmark>(r) \<Rightarrow> P \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> P') \<longleftrightarrow>
        e \<in> initials P \<and> event_trans_prem P e P'\<close> by (simp split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
  also have \<open>\<dots> \<longleftrightarrow> e \<in> initials P \<and> P after\<^sub>\<checkmark> e \<leadsto>\<^sub>\<tau> P'\<close>
  proof (insert that, safe)
    show \<open>event_trans_prem P e P' \<Longrightarrow> e \<in> P\<^sup>0 \<Longrightarrow>
          (\<And>P Q. case e of \<checkmark>(r) \<Rightarrow> \<Omega> P r \<leadsto>\<^sub>\<tau> \<Omega> Q r) \<Longrightarrow> P after\<^sub>\<checkmark> e \<leadsto>\<^sub>\<tau> P'\<close>
    proof (induct rule: event_trans_prem.induct)
      case (\<tau>_left_absorb e P' P P'')
      thus ?case 
        apply (cases e)
         apply (metis (mono_tags, lifting) \<tau>_trans_is_FD event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(5) mono_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD trans_FD)
        by (metis After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def FD_antisym \<tau>_trans_is_FD event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(6))
    next
      case (\<tau>_right_absorb e P P' P'')
      thus ?case by (metis \<tau>_trans_is_FD trans_FD)
    next
      case (initial_trans_to_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k e P)
      thus ?case by (simp add: \<tau>_trans_eq)
    qed
  next
    show \<open>e \<in> initials P \<Longrightarrow> P after\<^sub>\<checkmark> e \<leadsto>\<^sub>\<tau> P' \<Longrightarrow> event_trans_prem P e P'\<close>
      by (rule \<tau>_right_absorb[of e P \<open>P after\<^sub>\<checkmark> e\<close> P'])
        (simp_all add: initial_trans_to_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<tau>_trans_is_FD)
  qed
  finally show ?thesis .
qed



text \<open>With these two results, we are encouraged in the following theories to define:
       \<^item> \<^term>\<open>P \<leadsto>\<^sub>\<tau> Q \<equiv> P \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
       \<^item> \<^term>\<open>P \<leadsto>\<^bsub>e\<^esub> P' \<equiv> ev e \<in> initials P \<and> P after\<^sub>\<checkmark> (ev e) \<leadsto>\<^sub>\<tau> Q\<close>
       \<^item> \<^term>\<open>P \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> P' \<equiv> \<checkmark>(r) \<in> P\<^sup>0 \<and> P after\<^sub>\<checkmark> \<checkmark>(r) \<leadsto>\<^sub>\<tau> Q\<close>

      and possible variations with other refinements.\<close>

(*<*)

no_notation \<tau>_trans (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50)
no_notation event_trans (\<open>_ \<leadsto>\<^bsub>_\<^esub> _\<close>  [50, 3, 51] 50)
no_notation tick_trans  (\<open>_ \<leadsto>\<^sub>\<checkmark>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)

end 


(*>*)

text \<open>But we want to make the construction as general as possible.
      Therefore we will continue with the locale mechanism, eventually adding additional required
      assumptions for each operator, and we will instantiate with refinements at the end.\<close>


(*<*)
end
  (*>*)