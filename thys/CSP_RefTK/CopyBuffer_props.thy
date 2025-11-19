(*<*)
\<comment>\<open> ********************************************************************
 * Project         : CSP-RefTK - A Refinement Toolkit for HOL-CSP
 * Version         : 1.0
 *
 * Author          : Burkhart Wolff, Safouan Taha, Lina Ye.
 *
 * This file       : The Copy-Buffer Example Revisited
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
(*>*)

chapter\<open>Examples\<close>

section\<open>CopyBuffer Refinement over an infinite alphabet\<close>

theory     CopyBuffer_props
  imports   "HOL-CSP.CopyBuffer" "HOL-CSP.CSP"
begin 

subsection\<open> The Copy-Buffer vs. reference processes \<close>

thm DF_COPY

subsection\<open> ... and abstract consequences \<close>

corollary df_COPY: "deadlock_free COPY"
  and lf_COPY: "lifelock_free COPY"
   apply (meson DF_COPY DF_Univ_freeness UNIV_not_empty image_is_empty sup_eq_bot_iff)
  apply (rule deadlock_free_implies_lifelock_free)
  by (metis DF_COPY DF_Univ_freeness UNIV_I empty_iff image_eqI le_sup_iff subset_empty)

corollary df\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_COPY: "deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S COPY" 
  and lf\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_COPY: "lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S COPY"
  and nt_COPY: "non_terminating COPY"
    apply (simp add: df_COPY deadlock_free_imp_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S)
   apply (simp add: lf_COPY lifelock_free_imp_lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S)
  using lf_COPY lifelock_free_is_non_terminating by blast

lemma DF_SYSTEM: "DF UNIV \<sqsubseteq>\<^sub>F\<^sub>D SYSTEM"
  using deadlock_free_def df_COPY impl_refines_spec' trans_FD by blast

corollary df_SYSTEM: "deadlock_free SYSTEM"
  and lf_SYSTEM: "lifelock_free SYSTEM"
   apply (simp add: DF_SYSTEM deadlock_free_def)
  apply (rule deadlock_free_implies_lifelock_free)
  by (simp add: DF_SYSTEM deadlock_free_def)

corollary df\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_SYSTEM: "deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S SYSTEM" 
  and lf\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_SYSTEM: "lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S SYSTEM"
  and nt_SYSTEM: "non_terminating SYSTEM"
    apply (simp add: df_SYSTEM deadlock_free_imp_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S)
   apply (simp add: lf_SYSTEM lifelock_free_imp_lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S)
  using lf_SYSTEM lifelock_free_is_non_terminating by blast

end
