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
 imports   "HOL-CSP.CopyBuffer" "HOL-CSP.Assertions"
begin 

subsection\<open> The Copy-Buffer vs. reference processes \<close>

lemma DF_COPY: "(DF (range left \<union> range right)) \<sqsubseteq>\<^sub>F\<^sub>D COPY"
  by (simp add: DF_COPY)


subsection\<open> ... and abstract consequences \<close>

corollary df_COPY: "deadlock_free COPY"
      and lf_COPY: "lifelock_free COPY"
   apply (meson DF_COPY DF_Univ_freeness UNIV_not_empty image_is_empty sup_eq_bot_iff)
  by (meson CHAOS_DF_refine_FD DF_COPY DF_Univ_freeness UNIV_not_empty deadlock_free_def 
            image_is_empty lifelock_free_def sup_eq_bot_iff trans_FD)

corollary df_v2_COPY: "deadlock_free_v2 COPY" 
      and lf_v2_COPY: "lifelock_free_v2 COPY"
      and nt_COPY: "non_terminating COPY"
  apply (simp add: df_COPY deadlock_free_is_deadlock_free_v2)
  apply (simp add: lf_COPY lifelock_free_is_lifelock_free_v2)
  using lf_COPY lifelock_free_is_non_terminating by blast

lemma DF_SYSTEM: "DF UNIV \<sqsubseteq>\<^sub>F\<^sub>D SYSTEM"
  using DF_subset[of "(range left \<union> range right)" UNIV, simplified]
        DF_COPY impl_refines_spec trans_FD by blast

corollary df_SYSTEM: "deadlock_free SYSTEM"
      and lf_SYSTEM: "lifelock_free SYSTEM"
  apply (simp add: DF_SYSTEM deadlock_free_def)
  using CHAOS_DF_refine_FD DF_SYSTEM lifelock_free_def trans_FD by blast 

corollary df_v2_SYSTEM: "deadlock_free_v2 SYSTEM" 
      and lf_v2_SYSTEM: "lifelock_free_v2 SYSTEM"
      and nt_SYSTEM: "non_terminating SYSTEM"
  apply (simp add: df_SYSTEM deadlock_free_is_deadlock_free_v2)
  apply (simp add: lf_SYSTEM lifelock_free_is_lifelock_free_v2)
  using lf_SYSTEM lifelock_free_is_non_terminating by blast

end
