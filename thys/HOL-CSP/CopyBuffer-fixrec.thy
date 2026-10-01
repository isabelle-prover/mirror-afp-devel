(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in  Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff, Lina Ye.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : An experimental Version of the Copy Buffer Example
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

chapter\<open> Annex: Running Example with Buffer over infinite Alphabet\<close>

(*<*)
theory      "CopyBuffer-fixrec" 
  imports   "HOL-CSP"
begin 
(*>*)

text\<open> This file contains a version of the classical CopyBuffer Example
      with a (discouraged) use of the HOLCF - fixrec package. \<close>

section\<open> Defining Channels and Rewrite-sets of Events\<close>

text\<open>Note: This Approach is DISCOURAGED.\<close>

datatype 'a channel = left 'a | right 'a | mid 'a | ack

definition SYN  :: "'a channel set"
  where   "SYN  \<equiv> range mid \<union> {ack}"


lemma simplification_lemmas [simp] :
  \<open>range left \<inter> SYN = {}\<close>  \<open>range right \<inter> SYN = {}\<close>  \<open>ack \<in> SYN\<close>     \<open>range mid \<subseteq> SYN\<close> 
  \<open>mid x \<in> SYN\<close>            \<open>right x \<notin> SYN\<close>           \<open>left x \<notin> SYN\<close>  \<open>inj mid\<close>
  by (auto simp: SYN_def inj_on_def)

lemma "finite (SYN:: 'a channel set) \<Longrightarrow> finite {(t::'a). True}"
  by (metis (no_types) SYN_def UNIV_def channel.inject(3) finite_Un finite_imageD inj_on_def)

lemmas Sync_rules   = read_Sync_read_subset_forced_read_same_chan
                      read_Sync_read_left read_Sync_read_right
                      write_Sync_read_left write_Sync_read_right
                      read_Sync_write_left read_Sync_write_right
                      write_Sync_write_subset
                      write_Sync_read_subset read_Sync_write_subset
                      write0_Sync_write_right write0_Sync_write0

lemmas Hiding_rules = Hiding_read_disjoint Hiding_write_subset Hiding_write_disjoint
                      Hiding_write0_non_disjoint Hiding_write0_disjoint
 
lemmas mono_rules   = mono_read_FD mono_write_FD mono_write0_FD


section\<open> Process Definitions via HOLCF - fixrec-Package  \<close>

fixrec
  COPY::"'a channel process"  and  SEND::"'a channel process"  and  REC :: "'a channel process"
  where
     COPY_rec[simp del]:  "COPY = left\<^bold>?x \<rightarrow> right\<^bold>!x \<rightarrow> COPY"
   | SEND_rec[simp del]:  "SEND = left\<^bold>?x \<rightarrow> mid\<^bold>!x \<rightarrow> ack \<rightarrow> SEND"
   | REC_rec[simp del] :  "REC  = mid\<^bold>?x  \<rightarrow> right\<^bold>!x \<rightarrow> ack \<rightarrow> REC"

thm COPY_rec

definition SYSTEM :: "'a channel process"
  where     \<open>SYSTEM \<equiv> ((SEND \<lbrakk> SYN \<rbrakk> REC) \ SYN)\<close>

section\<open> Another Refinement Proof on fixrec-infrastructure \<close>

text\<open> Third part: No comes the proof by fixpoint induction. 
       Not too bad in automation considering what is inferred,
       but wouldn't scale for large examples. \<close>

thm COPY_SEND_REC.induct

lemma impl_refines_spec'' : "(COPY::'a channel process) \<sqsubseteq>\<^sub>F\<^sub>D SYSTEM"
  apply (unfold SYSTEM_def)
  apply (rule_tac P=\<open>\<lambda> a b c. a \<sqsubseteq>\<^sub>F\<^sub>D ((SEND \<lbrakk>SYN\<rbrakk> REC) \ SYN)\<close> in COPY_SEND_REC.induct)
    apply (subst case_prod_beta')+
    apply (intro le_FD_adm, simp_all add: monofunI)
  apply (subst SEND_rec, subst REC_rec)
  by (simp add: Sync_rules Hiding_rules mono_read_FD mono_write_FD)

lemma spec_refines_impl' : 
  assumes fin:  "finite (SYN::'a channel set)"
  shows         "SYSTEM \<sqsubseteq>\<^sub>F\<^sub>D (COPY::'a channel process)"
proof(unfold SYSTEM_def, rule_tac P=\<open>\<lambda> a b c. ((b \<lbrakk>SYN\<rbrakk> REC) \ SYN) \<sqsubseteq>\<^sub>F\<^sub>D COPY\<close> 
    in  COPY_SEND_REC.induct, goal_cases)
  case 1
  have aa:\<open>adm (\<lambda>(a::'a channel process). ((a \<lbrakk>SYN\<rbrakk> REC) \ SYN) \<sqsubseteq>\<^sub>F\<^sub>D COPY)\<close>
    apply (intro le_FD_adm)
    by (simp_all add: fin cont2mono)
  thus ?case using adm_subst[of "\<lambda>(a,b,c). b", simplified, OF aa] by (simp add: split_def)
next
  case 2
  then show ?case by (simp add: Sync_commute)
next
  case (3 a aa b)
  then show ?case 
    by (subst COPY_rec, subst REC_rec)
      (simp add: Sync_rules Hiding_rules mono_read_FD mono_write_FD)
qed

lemma spec_equal_impl' : 
  assumes fin:  "finite (SYN::('a channel)set)"
  shows         "SYSTEM = (COPY::'a channel process)"
  apply (rule FD_antisym)
   apply (rule spec_refines_impl'[OF fin])
  apply (rule impl_refines_spec'')
  done


(*<*)
end
(*>*)
