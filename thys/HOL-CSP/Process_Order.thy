(*<*)
\<comment>\<open> ********************************************************************
 * Project         : CSP-RefTK - A Refinement Toolkit for HOL-CSP
 * Version         : 1.0
 *
 * Author          : Burkhart Wolff, Safouan Taha, Lina Ye, Benoît Ballenghien, Catherine Dubois
 *
 * This file       : A Normalization Theory
 *
 * Copyright (c) 2022 Université Paris-Saclay, France
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


chapter \<open> Refinements \<close> (* find a better name *)

theory Process_Order
  imports Process Stop
begin


definition trace_refine :: \<open>'a process \<Rightarrow> 'a process \<Rightarrow> bool\<close>              (infix \<open>\<sqsubseteq>\<^sub>T\<close> 60)
  where \<open>P \<sqsubseteq>\<^sub>T Q \<equiv> \<T> Q \<subseteq> \<T> P\<close>

definition failure_refine :: \<open>'a process \<Rightarrow> 'a process \<Rightarrow> bool\<close>            (infix \<open>\<sqsubseteq>\<^sub>F\<close> 60)
  where \<open>P \<sqsubseteq>\<^sub>F Q \<equiv> \<F> Q \<subseteq> \<F> P\<close>

definition divergence_refine :: \<open>'a process \<Rightarrow> 'a process \<Rightarrow> bool\<close>         (infix \<open>\<sqsubseteq>\<^sub>D\<close> 53)
  where \<open>P \<sqsubseteq>\<^sub>D Q \<equiv> \<D> Q \<subseteq> \<D> P\<close>

definition failure_divergence_refine :: \<open>'a process \<Rightarrow> 'a process \<Rightarrow> bool\<close> (infix \<open>\<sqsubseteq>\<^sub>F\<^sub>D\<close> 60)
  where \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<equiv> P \<le> Q\<close>


definition trace_divergence_refine :: \<open>'a process \<Rightarrow> 'a process \<Rightarrow> bool\<close>   (infix \<open>\<sqsubseteq>\<^sub>D\<^sub>T\<close> 53)
  (* an experimental order considered also in our theories*)
  where \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<equiv> P \<sqsubseteq>\<^sub>T Q \<and> P \<sqsubseteq>\<^sub>D Q\<close>


section \<open>Idempotency\<close>

lemma  idem_F[simp]: \<open>P \<sqsubseteq>\<^sub>F P\<close>
  and  idem_D[simp]: \<open>P \<sqsubseteq>\<^sub>D P\<close>
  and  idem_T[simp]: \<open>P \<sqsubseteq>\<^sub>T P\<close>
  and idem_FD[simp]: \<open>P \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
  and idem_DT[simp]: \<open>P \<sqsubseteq>\<^sub>D\<^sub>T P\<close>
  by (simp_all add: failure_refine_def divergence_refine_def trace_refine_def
                    failure_divergence_refine_def trace_divergence_refine_def) 


section \<open>Some obvious refinements\<close>

lemma BOT_leF[simp]: \<open>\<bottom> \<sqsubseteq>\<^sub>F Q\<close>
  and BOT_leD[simp]: \<open>\<bottom> \<sqsubseteq>\<^sub>D Q\<close>
  and BOT_leT[simp]: \<open>\<bottom> \<sqsubseteq>\<^sub>T Q\<close>
  by (simp_all add: failure_refine_def le_approx_lemma_F trace_refine_def
                    le_approx1 divergence_refine_def le_approx_lemma_T)



section \<open>Antisymmetry\<close>

lemma FD_antisym: \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> Q \<sqsubseteq>\<^sub>F\<^sub>D P \<Longrightarrow> P = Q\<close>
  by (simp add: failure_divergence_refine_def)

lemma DT_antisym: \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> Q \<sqsubseteq>\<^sub>D\<^sub>T P \<Longrightarrow> P = Q\<close>
  apply (simp add: trace_divergence_refine_def)
  oops 



section \<open>Transitivity\<close>

lemma  trans_F: \<open>P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> Q \<sqsubseteq>\<^sub>F S \<Longrightarrow> P \<sqsubseteq>\<^sub>F S\<close>
  and  trans_D: \<open>P \<sqsubseteq>\<^sub>D Q \<Longrightarrow> Q \<sqsubseteq>\<^sub>D S \<Longrightarrow> P \<sqsubseteq>\<^sub>D S\<close>
  and  trans_T: \<open>P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> Q \<sqsubseteq>\<^sub>T S \<Longrightarrow> P \<sqsubseteq>\<^sub>T S\<close>
  and trans_FD: \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> Q \<sqsubseteq>\<^sub>F\<^sub>D S \<Longrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D S\<close>
  and trans_DT: \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> Q \<sqsubseteq>\<^sub>D\<^sub>T S \<Longrightarrow> P \<sqsubseteq>\<^sub>D\<^sub>T S\<close>
  by (meson failure_refine_def order_trans, meson divergence_refine_def order_trans,
      meson trace_refine_def order_trans, meson failure_divergence_refine_def order_trans,
      meson divergence_refine_def order_trans trace_divergence_refine_def trace_refine_def)



section \<open>Relations between refinements\<close>

lemma      leF_imp_leT: \<open>P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> P \<sqsubseteq>\<^sub>T Q\<close>
  and     leFD_imp_leF: \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> P \<sqsubseteq>\<^sub>F Q\<close>
  and     leFD_imp_leD: \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> P \<sqsubseteq>\<^sub>D Q\<close>
  and     leDT_imp_leD: \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> P \<sqsubseteq>\<^sub>D Q\<close>
  and     leDT_imp_leT: \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> P \<sqsubseteq>\<^sub>T Q\<close>
  and leF_leD_imp_leFD: \<open>P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> P \<sqsubseteq>\<^sub>D Q \<Longrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
  and leD_leT_imp_leDT: \<open>P \<sqsubseteq>\<^sub>D Q \<Longrightarrow> P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> P \<sqsubseteq>\<^sub>D\<^sub>T Q\<close>
  by (simp_all add: F_subset_imp_T_subset failure_refine_def trace_refine_def divergence_refine_def
                    trace_divergence_refine_def  failure_divergence_refine_def le_ref_def)
 


section \<open>More obvious refinements\<close>

lemma BOT_leFD[simp]: \<open>\<bottom> \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
  and BOT_leDT[simp]: \<open>\<bottom> \<sqsubseteq>\<^sub>D\<^sub>T Q\<close>
  by (simp_all add: leF_leD_imp_leFD leD_leT_imp_leDT)

lemma leDT_STOP[simp]: \<open>P \<sqsubseteq>\<^sub>D\<^sub>T STOP\<close>
  by (simp add: D_STOP leD_leT_imp_leDT Nil_elem_T T_STOP divergence_refine_def trace_refine_def)

lemma leD_STOP[simp]: \<open>P \<sqsubseteq>\<^sub>D STOP\<close>
  and leT_STOP[simp]: \<open>P \<sqsubseteq>\<^sub>T STOP\<close>
  by (simp_all add: leDT_imp_leD leDT_imp_leT)



section \<open>Admissibility\<close>

lemma le_F_adm[simp]:  \<open>cont (u::('a::cpo) \<Rightarrow> 'b process) \<Longrightarrow> monofun v \<Longrightarrow> adm(\<lambda>x. u x \<sqsubseteq>\<^sub>F v x)\<close>
proof(auto simp add:cont2contlubE adm_def failure_refine_def)
  fix Y a b
  assume 1: \<open>cont u\<close> 
     and 2: \<open>monofun v\<close> 
     and 3: \<open>chain Y\<close> 
     and 4: \<open>\<forall>i. \<F> (v (Y i)) \<subseteq> \<F> (u (Y i))\<close> 
     and 5: \<open>(a, b) \<in> \<F> (v (\<Squnion>x. Y x))\<close>
  hence \<open>v (Y i)  \<sqsubseteq> v (\<Squnion>i. Y i)\<close> for i by (simp add: is_ub_thelub monofunE)
  hence \<open>\<F> (v (\<Squnion>i. Y i)) \<subseteq> \<F> (u (Y i))\<close> for i using 4 le_approx_lemma_F by blast   
  then show \<open>(a, b) \<in> \<F> (\<Squnion>i. u (Y i))\<close>
    using F_LUB[OF ch2ch_cont[OF 1 3]] limproc_is_thelub[OF ch2ch_cont[OF 1 3]] 5 by force
qed

lemma le_T_adm[simp]: \<open>cont (u::('a::cpo) \<Rightarrow> 'b process) \<Longrightarrow> monofun v \<Longrightarrow> adm(\<lambda>x. u x \<sqsubseteq>\<^sub>T v x)\<close>
proof(auto simp add:cont2contlubE adm_def trace_refine_def)
  fix Y x
  assume 1: \<open>cont u\<close> 
     and 2: \<open>monofun v\<close> 
     and 3: \<open>chain Y\<close> 
     and 4: \<open>\<forall>i. \<T> (v (Y i)) \<subseteq> \<T> (u (Y i))\<close> 
     and 5: \<open>x \<in> \<T> (v (\<Squnion>i. Y i))\<close>
  hence \<open>v (Y i)  \<sqsubseteq> v (\<Squnion>i. Y i)\<close> for i by (simp add: is_ub_thelub monofunE)
  hence \<open>\<T> (v (\<Squnion>i. Y i)) \<subseteq> \<T> (u (Y i))\<close> for i using 4 le_approx_lemma_T by blast  
  then show \<open>x \<in> \<T> (\<Squnion>i. u (Y i))\<close>
    using T_LUB[OF ch2ch_cont[OF 1 3]] limproc_is_thelub[OF ch2ch_cont[OF 1 3]] 5 by force
qed

lemma le_D_adm[simp]: \<open>cont (u::('a::cpo) \<Rightarrow> 'b process) \<Longrightarrow> monofun v \<Longrightarrow> adm(\<lambda>x. u x \<sqsubseteq>\<^sub>D v x)\<close>
proof(auto simp add:cont2contlubE adm_def divergence_refine_def)
  fix Y x
  assume 1: \<open>cont u\<close> 
     and 2: \<open>monofun v\<close> 
     and 3: \<open>chain Y\<close> 
     and 4: \<open>\<forall>i. \<D> (v (Y i)) \<subseteq> \<D> (u (Y i))\<close> 
     and 5: \<open>x \<in> \<D> (v (\<Squnion>i. Y i))\<close>
  hence \<open>v (Y i)  \<sqsubseteq> v (\<Squnion>i. Y i)\<close> for i by (simp add: is_ub_thelub monofunE)
  hence \<open>\<D> (v (\<Squnion>i. Y i)) \<subseteq> \<D> (u (Y i))\<close> for i using 4 le_approx1 by blast  
  then show \<open>x \<in> \<D> (\<Squnion>i. u (Y i))\<close>
    using D_LUB[OF ch2ch_cont[OF 1 3]] limproc_is_thelub[OF ch2ch_cont[OF 1 3]] 5 by force
qed


lemmas le_FD_adm[simp] = le_adm[folded failure_divergence_refine_def]


lemma le_DT_adm[simp]: \<open>cont (u::('a::cpo) \<Rightarrow> 'b process) \<Longrightarrow> monofun v \<Longrightarrow> adm(\<lambda>x. u x \<sqsubseteq>\<^sub>D\<^sub>T v x)\<close>
  using adm_conj[OF le_T_adm[of u v] le_D_adm[of u v]] by (simp add: trace_divergence_refine_def)






end