\<comment>\<open> ******************************************************************** 
 * Project         : CSP-RefTK - A Refinement Toolkit for HOL-CSP
 * Version         : 1.0
 *
 * Author          : Burkhart Wolff, Safouan Taha, Lina Ye.
 *
 * This file       : Theorems on DF and LF
 *
 * Copyright (c) 2020 Université Paris-Saclay, France
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

theory Properties
  imports "HOL-CSP.Assertions"
begin



section \<open>Non-terminating Runs\<close>

definition non_terminating  :: "'a process \<Rightarrow> bool"
  where   "non_terminating P \<equiv> RUN UNIV \<sqsubseteq>\<^sub>T P"

corollary non_terminating_refine_DF: "non_terminating P = DF UNIV \<sqsubseteq>\<^sub>T P"
  and non_terminating_refine_CHAOS: "non_terminating P = CHAOS UNIV \<sqsubseteq>\<^sub>T P"
  by (simp_all add: DF_all_tickfree_traces1 RUN_all_tickfree_traces1 CHAOS_all_tickfree_traces1 
                    non_terminating_def trace_refine_def)

lemma non_terminating_is_right: "non_terminating (P::'a process) \<longleftrightarrow> (\<forall>s\<in>\<T> P. tickFree s)"
  apply (rule iffI)
  by (auto simp add:non_terminating_def trace_refine_def tickFree_def RUN_all_tickfree_traces1)[1]
     (auto simp add:non_terminating_def trace_refine_def RUN_all_tickfree_traces2)

lemma nonterminating_implies_div_free: "non_terminating P \<Longrightarrow> \<D> P = {}"
  unfolding non_terminating_is_right
  by (metis NT_ND equals0I front_tickFree_charn process_charn tickFree_Cons tickFree_append) 

lemma non_terminating_implies_F: "non_terminating P \<Longrightarrow> CHAOS UNIV \<sqsubseteq>\<^sub>F P"
  apply(auto simp add: non_terminating_is_right failure_refine_def)
  using CHAOS_has_all_tickFree_failures F_T by blast 

corollary non_terminating_F: "non_terminating P = CHAOS UNIV \<sqsubseteq>\<^sub>F P"
  by (auto simp add:non_terminating_implies_F non_terminating_refine_CHAOS leF_imp_leT)

corollary non_terminating_FD: "non_terminating P = CHAOS UNIV \<sqsubseteq>\<^sub>F\<^sub>D P"
  unfolding non_terminating_F
  using div_free_CHAOS nonterminating_implies_div_free leFD_imp_leF
        leF_leD_imp_leFD divergence_refine_def non_terminating_F 
  by fastforce 


section \<open>Lifelock Freeness\<close>

thm lifelock_free_def

corollary lifelock_free_is_non_terminating: "lifelock_free P = non_terminating P"
  unfolding lifelock_free_def non_terminating_FD by rule

lemma div_free_divergence_refine:
  "\<D> P = {} \<longleftrightarrow> CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV \<sqsubseteq>\<^sub>D P" 
  "\<D> P = {} \<longleftrightarrow> CHAOS UNIV    \<sqsubseteq>\<^sub>D P" 
  "\<D> P = {} \<longleftrightarrow> RUN UNIV      \<sqsubseteq>\<^sub>D P" 
  "\<D> P = {} \<longleftrightarrow> DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV    \<sqsubseteq>\<^sub>D P" 
  "\<D> P = {} \<longleftrightarrow> DF UNIV       \<sqsubseteq>\<^sub>D P" 
  by (simp_all add: div_free_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P div_free_CHAOS div_free_RUN div_free_DF 
                    div_free_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P divergence_refine_def)

definition lifelock_free_v2 :: "'a process \<Rightarrow> bool"
  where   "lifelock_free_v2 P \<equiv> CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV \<sqsubseteq>\<^sub>F\<^sub>D P"

lemma div_free_is_lifelock_free_v2: "lifelock_free_v2 P \<longleftrightarrow> \<D> P = {}"
  using CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_has_all_failures_Un leFD_imp_leD leF_leD_imp_leFD
        div_free_divergence_refine(1) lifelock_free_v2_def 
  by blast
  
lemma lifelock_free_is_lifelock_free_v2: "lifelock_free P \<Longrightarrow> lifelock_free_v2 P"
  by (simp add: leFD_imp_leD div_free_divergence_refine(2) div_free_is_lifelock_free_v2 lifelock_free_def)

corollary deadlock_free_v2_is_lifelock_free_v2: "deadlock_free_v2 P \<Longrightarrow> lifelock_free_v2 P"
  by (simp add: deadlock_free_v2_implies_div_free div_free_is_lifelock_free_v2)


section \<open>New laws\<close>

lemma non_terminating_Seq: 
  "non_terminating P \<Longrightarrow> (P \<^bold>; Q) = P"
  apply(auto simp add: non_terminating_is_right Process_eq_spec D_Seq F_Seq F_T is_processT7)
      using process_charn apply blast
    using process_charn apply blast
   using F_T is_processT5_S2a apply fastforce
  using D_T front_tickFree_Nil by blast

lemma non_terminating_Sync: 
  "non_terminating P \<Longrightarrow> lifelock_free_v2 Q \<Longrightarrow> non_terminating (P \<lbrakk>A\<rbrakk> Q)"
  apply(auto simp add: non_terminating_is_right div_free_is_lifelock_free_v2 T_Sync) 
  apply (metis equals0D ftf_Sync1 ftf_Sync21 insertI1 tickFree_def)
  apply (meson NT_ND is_processT7_S tickFree_append)
  by (metis D_T empty_iff ftf_Sync1 ftf_Sync21 insertI1 tickFree_def)

lemmas non_terminating_Par = non_terminating_Sync[where A = \<open>UNIV\<close>]
   and non_terminating_Inter = non_terminating_Sync[where A = \<open>{}\<close>]


end
