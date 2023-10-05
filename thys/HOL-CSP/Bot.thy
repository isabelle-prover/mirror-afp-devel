(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in  Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Burkhart Wolff, Safouan Taha.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : A Combined CSP Theory
 *
 * Copyright (c) 2009 Université Paris-Sud, France
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

chapter\<open> The CSP Operators \<close>

section\<open>The Undefined Process\<close>

theory     Bot
imports    Process
begin 

lift_definition BOT :: \<open>'\<alpha> process\<close> 
  is \<open>({(s,X). front_tickFree s}, {d. front_tickFree d})\<close>
  unfolding is_process_def FAILURES_def DIVERGENCES_def
  by (auto simp: tickFree_implies_front_tickFree 
           elim: front_tickFree_dw_closed front_tickFree_append)


lemma F_BOT: "\<F> BOT = {(s,X). front_tickFree s}"
  by (simp add: BOT.rep_eq FAILURES_def Failures.rep_eq)

lemma D_BOT: "\<D> BOT = {d. front_tickFree d}"
  by (simp add: BOT.rep_eq DIVERGENCES_def Divergences.rep_eq)

lemma T_BOT: "\<T> BOT = {s. front_tickFree s}"
  by (simp add: Traces.rep_eq TRACES_def Failures.rep_eq[symmetric] F_BOT)


text\<open> This is the key result: @{term "\<bottom>"} --- which we know to exist 
from the process instantiation --- is equal \<^const>\<open>BOT\<close> .
\<close>

lemma BOT_is_UU[simp]: "BOT = \<bottom>"
apply(auto simp: Pcpo.eq_bottom_iff Process.le_approx_def Ra_def 
                 min_elems_Collect_ftF_is_Nil Process.Nil_elem_T 
                 F_BOT D_BOT T_BOT
           elim: D_imp_front_tickFree)
apply(metis Process.is_processT2)
done

lemma F_UU: "\<F> \<bottom> = {(s,X). front_tickFree s}"
  using F_BOT by auto

lemma D_UU: "\<D> \<bottom> = {d. front_tickFree d}"
  using D_BOT by auto

lemma T_UU: "\<T> \<bottom> = {s. front_tickFree s}"
  using T_BOT by auto


lemma BOT_iff_D: \<open>P = \<bottom> \<longleftrightarrow> [] \<in> \<D> P\<close>
  apply (intro iffI, simp add: D_UU)
  apply (subst Process_eq_spec, safe)
  by (simp_all add: F_UU D_UU is_processT2 D_imp_front_tickFree)
     (metis append_Nil is_processT tickFree_Nil)+


end

