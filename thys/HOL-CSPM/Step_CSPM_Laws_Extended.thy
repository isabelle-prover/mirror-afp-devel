(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSPM - Architectural operators for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff.
 *
 * This file       : Extension of the step laws
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


(*<*)
theory Step_CSPM_Laws_Extended
  imports Non_Deterministic_CSPM_Distributivity Step_CSPM_Laws
begin
  (*>*)

subsection \<open>The Throw Operator\<close>

lemma Throw_Mndetprefix: 
  \<open>(\<sqinter>a \<in> A \<rightarrow> P a) \<Theta> b \<in> B. Q b =
    \<sqinter>a \<in> A \<rightarrow> (if a \<in> B then Q a else P a \<Theta> b \<in> B. Q b)\<close>
  by (auto simp add: Mndetprefix_GlobalNdet Throw_distrib_GlobalNdet_right
      write0_def Throw_Mprefix
      intro: mono_GlobalNdet_eq mono_Mprefix_eq)



subsection \<open>The Interrupt Operator\<close>

lemma Interrupt_Mndetprefix:
  \<open>(\<sqinter>a \<in> A \<rightarrow> P a) \<triangle> Q = Q \<box> (\<sqinter>a \<in> A \<rightarrow> P a \<triangle> Q)\<close>
  by (simp add: Mndetprefix_GlobalNdet Interrupt_distrib_GlobalNdet_right
      write0_def Interrupt_Mprefix Det_distrib_GlobalNdet_left)



(*<*)
end
  (*>*)