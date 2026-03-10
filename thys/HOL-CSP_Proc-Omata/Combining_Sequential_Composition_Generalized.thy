(***********************************************************************************
 * Copyright (c) 2025 Université Paris-Saclay
 *
 * Author: Benoît Ballenghien, Université Paris-Saclay,
 *         CNRS, ENS Paris-Saclay, LMF
 * Author: Burkhart Wolff, Université Paris-Saclay,
 *         CNRS, ENS Paris-Saclay, LMF
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 ***********************************************************************************)


chapter \<open>Combining Automata for Sequential Composition Generalized\<close>

(*<*)
theory Combining_Sequential_Composition_Generalized 
  imports Process_Normalization
begin
  (*>*)


section \<open>Definitions\<close>

section \<open>General Patterns\<close>

definition combine\<^sub>d_Seq_\<epsilon> ::
  \<open>[('\<sigma>\<^sub>0, 'a, 'r, '\<alpha>\<^sub>0) A\<^sub>d_scheme, 'r \<Rightarrow> ('\<sigma>\<^sub>1, 'a, 's, '\<alpha>\<^sub>1) A\<^sub>d_scheme, '\<sigma> \<Rightarrow> '\<sigma>\<^sub>0, '\<sigma> \<Rightarrow> '\<sigma>\<^sub>1, '\<sigma>] \<Rightarrow> 'a set\<close>
  where \<open>combine\<^sub>d_Seq_\<epsilon> A\<^sub>0 A\<^sub>1 i\<^sub>0 i\<^sub>1 \<sigma>s \<equiv>
           if i\<^sub>0 \<sigma>s \<in> \<rho> A\<^sub>0
         then   if i\<^sub>1 \<sigma>s \<in> \<rho> (A\<^sub>1 \<lceil>\<omega> A\<^sub>0 (i\<^sub>0 \<sigma>s)\<rceil>)
              then {}
              else \<epsilon> (A\<^sub>1 \<lceil>\<omega> A\<^sub>0 (i\<^sub>0 \<sigma>s)\<rceil>) (i\<^sub>1 \<sigma>s)
         else \<epsilon> A\<^sub>0 (i\<^sub>0 \<sigma>s)\<close>

definition combine\<^sub>n\<^sub>d_Seq_\<epsilon> ::
  \<open>[('\<sigma>\<^sub>0, 'a, 'r, '\<alpha>\<^sub>0) A\<^sub>n\<^sub>d_scheme, 'r \<Rightarrow> ('\<sigma>\<^sub>1, 'a, 's, '\<alpha>\<^sub>1) A\<^sub>n\<^sub>d_scheme, '\<sigma> \<Rightarrow> '\<sigma>\<^sub>0, '\<sigma> \<Rightarrow> '\<sigma>\<^sub>1, '\<sigma>] \<Rightarrow> 'a set\<close>
  where \<open>combine\<^sub>n\<^sub>d_Seq_\<epsilon> A\<^sub>0 A\<^sub>1 i\<^sub>0 i\<^sub>1 \<sigma>s \<equiv>
           if i\<^sub>0 \<sigma>s \<in> \<rho> A\<^sub>0
         then   if i\<^sub>1 \<sigma>s \<in> (\<Union>r\<in>\<omega> A\<^sub>0 (i\<^sub>0 \<sigma>s). \<rho> (A\<^sub>1 r))
              then {}
              else (\<Union>r \<in> \<omega> A\<^sub>0 (i\<^sub>0 \<sigma>s). \<epsilon> (A\<^sub>1 r) (i\<^sub>1 \<sigma>s))
         else \<epsilon> A\<^sub>0 (i\<^sub>0 \<sigma>s)\<close>

lemmas combine_Seq_\<epsilon>_defs = combine\<^sub>d_Seq_\<epsilon>_def combine\<^sub>n\<^sub>d_Seq_\<epsilon>_def


fun combine\<^sub>d_Seq :: 
  \<open>[('\<sigma>\<^sub>0, 'e, 'r, '\<alpha>\<^sub>0) A\<^sub>d_scheme, 'r \<Rightarrow> ('\<sigma>\<^sub>1, 'e, 's, '\<alpha>\<^sub>1) A\<^sub>d_scheme,
    '\<sigma> \<Rightarrow> '\<sigma>\<^sub>0, '\<sigma> \<Rightarrow> '\<sigma>\<^sub>1, '\<sigma>\<^sub>0 \<Rightarrow> '\<sigma>\<^sub>1 \<Rightarrow> '\<sigma>] \<Rightarrow> ('\<sigma>, 'e, 's) A\<^sub>d\<close>
  and combine\<^sub>n\<^sub>d_Seq ::
  \<open>[('\<sigma>\<^sub>0, 'e, 'r, '\<alpha>\<^sub>0) A\<^sub>n\<^sub>d_scheme, 'r \<Rightarrow> ('\<sigma>\<^sub>1, 'e, 's, '\<alpha>\<^sub>1) A\<^sub>n\<^sub>d_scheme,
     '\<sigma> \<Rightarrow> '\<sigma>\<^sub>0, '\<sigma> \<Rightarrow> '\<sigma>\<^sub>1, '\<sigma>\<^sub>0 \<Rightarrow> '\<sigma>\<^sub>1 \<Rightarrow> '\<sigma>] \<Rightarrow> ('\<sigma>, 'e, 's) A\<^sub>n\<^sub>d\<close>
  where \<open>combine\<^sub>d_Seq A\<^sub>0 A\<^sub>1 i\<^sub>0 i\<^sub>1 f =
         \<lparr>\<tau> = \<lambda>\<sigma>s e.  if i\<^sub>0 \<sigma>s \<in> \<rho> A\<^sub>0
                    then   if i\<^sub>1 \<sigma>s \<in> \<rho> (A\<^sub>1 \<lceil>\<omega> A\<^sub>0 (i\<^sub>0 \<sigma>s)\<rceil>)
                         then \<diamond>
                          else update_right (A\<^sub>1 \<lceil>\<omega> A\<^sub>0 (i\<^sub>0 \<sigma>s)\<rceil>) (i\<^sub>0 \<sigma>s) (i\<^sub>1 \<sigma>s) e (f_up_opt f) (\<lambda>\<sigma>. \<lfloor>\<sigma>\<rfloor>)
                    else update_left  A\<^sub>0 (i\<^sub>0 \<sigma>s) (i\<^sub>1 \<sigma>s) e (f_up_opt f) (\<lambda>\<sigma>. \<lfloor>\<sigma>\<rfloor>),
          \<omega> = \<lambda>\<sigma>s. case \<omega> A\<^sub>0 (i\<^sub>0 \<sigma>s) of \<diamond> \<Rightarrow> \<diamond> | \<lfloor>r\<rfloor> \<Rightarrow> \<omega> (A\<^sub>1 r) (i\<^sub>1 \<sigma>s)\<rparr>\<close>
  |     \<open>combine\<^sub>n\<^sub>d_Seq A\<^sub>0 A\<^sub>1 i\<^sub>0 i\<^sub>1 f = 
         \<lparr>\<tau> = \<lambda>\<sigma>s e. if i\<^sub>0 \<sigma>s \<in> \<rho> A\<^sub>0
                    then   if i\<^sub>1 \<sigma>s \<in> (\<Union>r\<in>\<omega> A\<^sub>0 (i\<^sub>0 \<sigma>s). \<rho> (A\<^sub>1 r))
                         then {}
                         else (\<Union>r\<in>\<omega> A\<^sub>0 (i\<^sub>0 \<sigma>s). update_right (A\<^sub>1 r) (i\<^sub>0 \<sigma>s) (i\<^sub>1 \<sigma>s) e (f_up_set f) (\<lambda>\<sigma>. {\<sigma>}))
                    else      update_left A\<^sub>0 (i\<^sub>0 \<sigma>s) (i\<^sub>1 \<sigma>s) e (f_up_set f) (\<lambda>\<sigma>. {\<sigma>}),
          \<omega> = \<lambda>\<sigma>s. \<Union>r\<in>\<omega> A\<^sub>0 (i\<^sub>0 \<sigma>s). \<omega> (A\<^sub>1 r) (i\<^sub>1 \<sigma>s)\<rparr>\<close>



section \<open>Specializations\<close> 

definition combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ::
  \<open>[('\<sigma>, 'e, 'r, '\<alpha>) A\<^sub>d_scheme, 'r \<Rightarrow> ('\<sigma>, 'e, 's, '\<beta>) A\<^sub>d_scheme] \<Rightarrow> ('\<sigma> list, 'e, 's) A\<^sub>d\<close>
  where \<open>combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k A\<^sub>0 A\<^sub>1 \<equiv> combine\<^sub>d_Seq A\<^sub>0 A\<^sub>1 hd (\<lambda>\<sigma>s. hd (tl \<sigma>s)) (\<lambda>s t. [s, t])\<close>
definition combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ::
  \<open>[('\<sigma>, 'e, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme, 'r \<Rightarrow> ('\<sigma>, 'e, 's, '\<beta>) A\<^sub>n\<^sub>d_scheme] \<Rightarrow> ('\<sigma> list, 'e, 's) A\<^sub>n\<^sub>d\<close> 
  where \<open>combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k A\<^sub>0 A\<^sub>1 \<equiv> combine\<^sub>n\<^sub>d_Seq A\<^sub>0 A\<^sub>1 hd (\<lambda>\<sigma>s. hd (tl \<sigma>s)) (\<lambda>s t. [s, t])\<close>

definition combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ::
  \<open>[('\<sigma>\<^sub>0, 'e, 'r, '\<alpha>) A\<^sub>d_scheme, 'r \<Rightarrow> ('\<sigma>\<^sub>1, 'e, 's, '\<beta>) A\<^sub>d_scheme] \<Rightarrow> ('\<sigma>\<^sub>0 \<times> '\<sigma>\<^sub>1, 'e, 's) A\<^sub>d\<close> 
  where \<open>combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k A\<^sub>0 A\<^sub>1 \<equiv> combine\<^sub>d_Seq A\<^sub>0 A\<^sub>1 fst snd Pair\<close>
definition combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ::
  \<open>[('\<sigma>\<^sub>0, 'e, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme, 'r \<Rightarrow> ('\<sigma>\<^sub>1, 'e, 's, '\<beta>) A\<^sub>n\<^sub>d_scheme] \<Rightarrow> ('\<sigma>\<^sub>0 \<times> '\<sigma>\<^sub>1, 'e, 's) A\<^sub>n\<^sub>d\<close> 
  where \<open>combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k A\<^sub>0 A\<^sub>1 \<equiv> combine\<^sub>n\<^sub>d_Seq A\<^sub>0 A\<^sub>1 fst snd Pair\<close>

definition combine\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ::
  \<open>[('\<sigma> list, 'e, 'r, '\<alpha>) A\<^sub>d_scheme, nat, 'r \<Rightarrow> ('\<sigma> list, 'e, 's, '\<beta>) A\<^sub>d_scheme] \<Rightarrow> ('\<sigma> list, 'e, 's) A\<^sub>d\<close> 
  where \<open>combine\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k A\<^sub>0 len\<^sub>0 A\<^sub>1 \<equiv> combine\<^sub>d_Seq A\<^sub>0 A\<^sub>1 (take len\<^sub>0) (drop len\<^sub>0) (@)\<close>
definition combine\<^sub>n\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ::
  \<open>[('\<sigma> list, 'e, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme, nat, 'r \<Rightarrow> ('\<sigma> list, 'e, 's, '\<beta>) A\<^sub>n\<^sub>d_scheme] \<Rightarrow> ('\<sigma> list, 'e, 's) A\<^sub>n\<^sub>d\<close> 
  where \<open>combine\<^sub>n\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k A\<^sub>0 len\<^sub>0 A\<^sub>1 \<equiv> combine\<^sub>n\<^sub>d_Seq A\<^sub>0 A\<^sub>1 (take len\<^sub>0) (drop len\<^sub>0) (@)\<close>

definition combine\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ::
  \<open>[('\<sigma>, 'e, 'r, '\<alpha>) A\<^sub>d_scheme, 'r \<Rightarrow> ('\<sigma> list, 'e, 's, '\<beta>) A\<^sub>d_scheme] \<Rightarrow> ('\<sigma> list, 'e, 's) A\<^sub>d\<close> 
  where \<open>combine\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k A\<^sub>0 A\<^sub>1 \<equiv> combine\<^sub>d_Seq A\<^sub>0 A\<^sub>1 hd tl (#)\<close>
definition combine\<^sub>n\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ::
  \<open>[('\<sigma>, 'e, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme, 'r \<Rightarrow> ('\<sigma> list, 'e, 's, '\<beta>) A\<^sub>n\<^sub>d_scheme]  \<Rightarrow> ('\<sigma> list, 'e, 's) A\<^sub>n\<^sub>d\<close> 
  where \<open>combine\<^sub>n\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k A\<^sub>0 A\<^sub>1 \<equiv> combine\<^sub>n\<^sub>d_Seq A\<^sub>0 A\<^sub>1 hd tl (#)\<close>


lemmas combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs = combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def
  and combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs = combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def
  and combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k = combine\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def combine\<^sub>n\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def
  and combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs = combine\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def combine\<^sub>n\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def

lemmas combine_Seq_defs =
  combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs


bundle combine_Seq_syntax begin

notation combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<open>\<llangle>_ \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t _\<rrangle>\<close> [0, 0])
notation combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<open>\<llangle>_ \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t _\<rrangle>\<close> [0, 0])
notation combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<open>\<llangle>_ \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r _\<rrangle>\<close> [0, 0])
notation combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<open>\<llangle>_ \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r _\<rrangle>\<close> [0, 0])
notation combine\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<open>\<llangle>_ \<^sub>d\<otimes>_\<^bold>;\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L _\<rrangle>\<close> [0, 0, 0])
notation combine\<^sub>n\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<open>\<llangle>_ \<^sub>n\<^sub>d\<otimes>_\<^bold>;\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L _\<rrangle>\<close> [0, 0, 0])
notation combine\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<open>\<llangle>_ \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t _\<rrangle>\<close> [0, 0])
notation combine\<^sub>n\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<open>\<llangle>_ \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t _\<rrangle>\<close> [0, 0])

end


unbundle combine_Seq_syntax



section \<open>First Properties\<close>

lemma \<epsilon>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>\<epsilon> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> \<sigma>s = combine\<^sub>d_Seq_\<epsilon> A\<^sub>0 A\<^sub>1 hd (hd \<circ> tl) \<sigma>s\<close>
  \<open>\<epsilon> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t B\<^sub>1\<rrangle> \<sigma>s = combine\<^sub>n\<^sub>d_Seq_\<epsilon> B\<^sub>0 B\<^sub>1 hd (hd \<circ> tl) \<sigma>s\<close>
  by (auto simp add: combine_Seq_\<epsilon>_defs combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs
      \<epsilon>_simps \<rho>_simps option.case_eq_if)

lemma \<epsilon>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : 
  \<open>\<epsilon> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle> \<sigma>s = combine\<^sub>d_Seq_\<epsilon> A\<^sub>0 A\<^sub>1 fst snd \<sigma>s\<close>
  \<open>\<epsilon> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r B\<^sub>1\<rrangle> \<sigma>s = combine\<^sub>n\<^sub>d_Seq_\<epsilon> B\<^sub>0 B\<^sub>1 fst snd \<sigma>s\<close>
  by (auto simp add: combine_Seq_\<epsilon>_defs combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs
      \<epsilon>_simps \<rho>_simps option.case_eq_if)

lemma \<epsilon>_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : 
  \<open>\<epsilon> \<llangle>A\<^sub>0 \<^sub>d\<otimes>len\<^sub>0\<^bold>;\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle> \<sigma>s = combine\<^sub>d_Seq_\<epsilon> A\<^sub>0 A\<^sub>1 (take len\<^sub>0) (drop len\<^sub>0) \<sigma>s\<close>
  \<open>\<epsilon> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>len\<^sub>0\<^bold>;\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L B\<^sub>1\<rrangle> \<sigma>s = combine\<^sub>n\<^sub>d_Seq_\<epsilon> B\<^sub>0 B\<^sub>1 (take len\<^sub>0) (drop len\<^sub>0) \<sigma>s\<close>
  by (auto simp add: combine_Seq_\<epsilon>_defs combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
      \<epsilon>_simps \<rho>_simps option.case_eq_if)

lemma \<epsilon>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>\<epsilon> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> \<sigma>s = combine\<^sub>d_Seq_\<epsilon> A\<^sub>0 A\<^sub>1 hd tl \<sigma>s\<close>
  \<open>\<epsilon> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t B\<^sub>1\<rrangle> \<sigma>s = combine\<^sub>n\<^sub>d_Seq_\<epsilon> B\<^sub>0 B\<^sub>1 hd tl \<sigma>s\<close>
  by (auto simp add: combine_Seq_\<epsilon>_defs combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs
      \<epsilon>_simps \<rho>_simps option.case_eq_if)



subsection \<open>Reachability\<close>

lemma \<R>\<^sub>d_combine\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset: 
  \<open>\<R>\<^sub>d \<llangle>A\<^sub>0 \<^sub>d\<otimes>len\<^sub>0\<^bold>;\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle> (s\<^sub>0 @ s\<^sub>1) \<subseteq> {t\<^sub>0 @ t\<^sub>1 |t\<^sub>0 t\<^sub>1. t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 s\<^sub>0}\<close> (is \<open>?S\<^sub>A \<subseteq> _\<close>)
  if same_length_\<R>\<^sub>d: \<open>\<And>t\<^sub>0. t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 s\<^sub>0 \<Longrightarrow> length t\<^sub>0 = len\<^sub>0\<close>
proof safe
  show \<open>t \<in> ?S\<^sub>A \<Longrightarrow> \<exists>t\<^sub>0 t\<^sub>1. t = t\<^sub>0 @ t\<^sub>1 \<and> t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 s\<^sub>0\<close> for t
  proof (induct rule: \<R>\<^sub>d.induct)
    case init show ?case by (metis \<R>\<^sub>d.init)
  next
    case (step \<sigma>' \<sigma>'' a)
    from step.hyps(2) same_length_\<R>\<^sub>d obtain t\<^sub>0 t\<^sub>1
      where \<open>\<sigma>' = t\<^sub>0 @ t\<^sub>1\<close> \<open>t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 s\<^sub>0\<close> \<open>length t\<^sub>0 = len\<^sub>0\<close> by blast
    with step.hyps(3) show ?case
      by (auto simp add: combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k map_option_case
          split: if_split_asm option.splits) (metis \<R>\<^sub>d.step)
  qed
qed

lemma \<R>\<^sub>n\<^sub>d_combine\<^sub>n\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset: 
  \<open>\<R>\<^sub>n\<^sub>d \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>len\<^sub>0\<^bold>;\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle> (s\<^sub>0 @ s\<^sub>1) \<subseteq> {t\<^sub>0 @ t\<^sub>1 |t\<^sub>0 t\<^sub>1. t\<^sub>0 \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 s\<^sub>0}\<close> (is \<open>?S\<^sub>A \<subseteq> _\<close>)
  if same_length_\<R>\<^sub>n\<^sub>d: \<open>\<And>t\<^sub>0. t\<^sub>0 \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 s\<^sub>0 \<Longrightarrow> length t\<^sub>0 = len\<^sub>0\<close>
proof safe
  show \<open>t \<in> ?S\<^sub>A \<Longrightarrow> \<exists>t\<^sub>0 t\<^sub>1. t = t\<^sub>0 @ t\<^sub>1 \<and> t\<^sub>0 \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 s\<^sub>0\<close> for t
  proof (induct rule: \<R>\<^sub>n\<^sub>d.induct)
    case init show ?case by (metis \<R>\<^sub>n\<^sub>d.init)
  next
    case (step \<sigma>' \<sigma>'' a)
    from step.hyps(2) same_length_\<R>\<^sub>n\<^sub>d obtain t\<^sub>0 t\<^sub>1
      where \<open>\<sigma>' = t\<^sub>0 @ t\<^sub>1\<close> \<open>t\<^sub>0 \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 s\<^sub>0\<close> \<open>length t\<^sub>0 = len\<^sub>0\<close> by blast
    with step.hyps(3) show ?case
      by (auto simp add: combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k split: if_split_asm) (metis \<R>\<^sub>n\<^sub>d.step)
  qed
qed


lemma \<R>\<^sub>d_combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset: 
  \<open>\<R>\<^sub>d \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> [s\<^sub>0, s\<^sub>1] \<subseteq> {[t\<^sub>0, t\<^sub>1] |t\<^sub>0 t\<^sub>1. t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 s\<^sub>0}\<close> (is \<open>?S\<^sub>A \<subseteq> _\<close>)
proof safe
  show \<open>t \<in> ?S\<^sub>A \<Longrightarrow> \<exists>t\<^sub>0 t\<^sub>1. t = [t\<^sub>0, t\<^sub>1] \<and> t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 s\<^sub>0 \<close> for t
  proof (induct rule: \<R>\<^sub>d.induct)
    case init show ?case by (metis \<R>\<^sub>d.init)
  next
    case (step \<sigma>' \<sigma>'' a)
    from step.hyps(2) obtain t\<^sub>0 t\<^sub>1 where \<open>\<sigma>' = [t\<^sub>0, t\<^sub>1]\<close> \<open>t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 s\<^sub>0\<close> by blast
    with step.hyps(3) show ?case
      by (auto simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs map_option_case
          split: if_split_asm option.split_asm) (metis \<R>\<^sub>d.step)
  qed
qed

lemma \<R>\<^sub>n\<^sub>d_combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset: 
  \<open>\<R>\<^sub>n\<^sub>d \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> [s\<^sub>0, s\<^sub>1] \<subseteq> {[t\<^sub>0, t\<^sub>1] |t\<^sub>0 t\<^sub>1. t\<^sub>0 \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 s\<^sub>0}\<close> (is \<open>?S\<^sub>A \<subseteq> _\<close>)
proof safe
  show \<open>t \<in> ?S\<^sub>A \<Longrightarrow> \<exists>t\<^sub>0 t\<^sub>1. t = [t\<^sub>0, t\<^sub>1] \<and> t\<^sub>0 \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 s\<^sub>0 \<close> for t
  proof (induct rule: \<R>\<^sub>n\<^sub>d.induct)
    case init show ?case by (metis \<R>\<^sub>n\<^sub>d.init)
  next
    case (step \<sigma>' \<sigma>'' a)
    from step.hyps(2) obtain t\<^sub>0 t\<^sub>1 where \<open>\<sigma>' = [t\<^sub>0, t\<^sub>1]\<close> \<open>t\<^sub>0 \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 s\<^sub>0\<close> by blast
    with step.hyps(3) show ?case
      by (auto simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs split: if_split_asm) (metis \<R>\<^sub>n\<^sub>d.step)
  qed
qed


lemma \<R>\<^sub>d_combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset: 
  \<open>\<R>\<^sub>d \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle> (s\<^sub>0, s\<^sub>1) \<subseteq> {(t\<^sub>0, t\<^sub>1) |t\<^sub>0 t\<^sub>1. t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 s\<^sub>0}\<close> (is \<open>?S\<^sub>A \<subseteq> _\<close>)
proof safe
  show \<open>t \<in> ?S\<^sub>A \<Longrightarrow> \<exists>t\<^sub>0 t\<^sub>1. t = (t\<^sub>0, t\<^sub>1) \<and> t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 s\<^sub>0 \<close> for t
  proof (induct rule: \<R>\<^sub>d.induct)
    case init show ?case by (metis \<R>\<^sub>d.init)
  next
    case (step \<sigma>' \<sigma>'' a)
    from step.hyps(2) obtain t\<^sub>0 t\<^sub>1 where \<open>\<sigma>' = (t\<^sub>0, t\<^sub>1)\<close> \<open>t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 s\<^sub>0\<close> by blast
    with step.hyps(3) show ?case
      by (auto simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs map_option_case
          split: if_split_asm option.split_asm) (metis \<R>\<^sub>d.step)
  qed
qed

lemma \<R>\<^sub>n\<^sub>d_combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset: 
  \<open>\<R>\<^sub>n\<^sub>d \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle> (s\<^sub>0, s\<^sub>1) \<subseteq> {(t\<^sub>0, t\<^sub>1) |t\<^sub>0 t\<^sub>1. t\<^sub>0 \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 s\<^sub>0}\<close> (is \<open>?S\<^sub>A \<subseteq> _\<close>)
proof safe
  show \<open>t \<in> ?S\<^sub>A \<Longrightarrow> \<exists>t\<^sub>0 t\<^sub>1. t = (t\<^sub>0, t\<^sub>1) \<and> t\<^sub>0 \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 s\<^sub>0 \<close> for t
  proof (induct rule: \<R>\<^sub>n\<^sub>d.induct)
    case init show ?case by (metis \<R>\<^sub>n\<^sub>d.init)
  next
    case (step \<sigma>' \<sigma>'' a)
    from step.hyps(2) obtain t\<^sub>0 t\<^sub>1 where \<open>\<sigma>' = (t\<^sub>0, t\<^sub>1)\<close> \<open>t\<^sub>0 \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 s\<^sub>0\<close> by blast
    with step.hyps(3) show ?case
      by (auto simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs split: if_split_asm) (metis \<R>\<^sub>n\<^sub>d.step)
  qed
qed


lemma \<R>\<^sub>d_combine\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset: 
  \<open>\<R>\<^sub>d \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> (s\<^sub>0 # s\<^sub>1) \<subseteq> {t\<^sub>0 # t\<^sub>1 |t\<^sub>0 t\<^sub>1. t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 s\<^sub>0}\<close> (is \<open>?S\<^sub>A \<subseteq> _\<close>)
proof safe
  show \<open>t \<in> ?S\<^sub>A \<Longrightarrow> \<exists>t\<^sub>0 t\<^sub>1. t = t\<^sub>0 # t\<^sub>1 \<and> t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 s\<^sub>0 \<close> for t
  proof (induct rule: \<R>\<^sub>d.induct)
    case init show ?case by (metis \<R>\<^sub>d.init)
  next
    case (step \<sigma>' \<sigma>'' a)
    from step.hyps(2) obtain t\<^sub>0 t\<^sub>1 where \<open>\<sigma>' = t\<^sub>0 # t\<^sub>1\<close> \<open>t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 s\<^sub>0\<close> by blast
    with step.hyps(3) show ?case
      by (auto simp add: combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs map_option_case
          split: if_split_asm option.split_asm) (metis \<R>\<^sub>d.step)
  qed
qed

lemma \<R>\<^sub>n\<^sub>d_combine\<^sub>n\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset: 
  \<open>\<R>\<^sub>n\<^sub>d \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> (s\<^sub>0 # s\<^sub>1) \<subseteq> {t\<^sub>0 # t\<^sub>1 |t\<^sub>0 t\<^sub>1. t\<^sub>0 \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 s\<^sub>0}\<close> (is \<open>?S\<^sub>A \<subseteq> _\<close>)
proof safe
  show \<open>t \<in> ?S\<^sub>A \<Longrightarrow> \<exists>t\<^sub>0 t\<^sub>1. t = t\<^sub>0 # t\<^sub>1 \<and> t\<^sub>0 \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 s\<^sub>0 \<close> for t
  proof (induct rule: \<R>\<^sub>n\<^sub>d.induct)
    case init show ?case by (metis \<R>\<^sub>n\<^sub>d.init)
  next
    case (step \<sigma>' \<sigma>'' a)
    from step.hyps(2) obtain t\<^sub>0 t\<^sub>1 where \<open>\<sigma>' = t\<^sub>0 # t\<^sub>1\<close> \<open>t\<^sub>0 \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 s\<^sub>0\<close> by blast
    with step.hyps(3) show ?case
      by (auto simp add: combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs split: if_split_asm) (metis \<R>\<^sub>n\<^sub>d.step)
  qed
qed



section \<open>Normalization\<close> 

lemma \<tau>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour:
  \<open>\<tau> \<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d [s\<^sub>0, s\<^sub>1] e = \<tau> \<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t (\<lambda>r. \<llangle>A\<^sub>1 r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d)\<rrangle> [s\<^sub>0, s\<^sub>1] e\<close>
  by (auto simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs det_ndet_conv_defs option.case_eq_if \<epsilon>_simps \<rho>_simps)

lemma \<tau>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour:
  \<open>\<tau> \<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d (s\<^sub>0, s\<^sub>1) e = \<tau> \<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r (\<lambda>r. \<llangle>A\<^sub>1 r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d)\<rrangle> (s\<^sub>0, s\<^sub>1) e\<close>
  by (auto simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs det_ndet_conv_defs option.case_eq_if \<epsilon>_simps \<rho>_simps)

lemma \<tau>_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour:
  \<open>\<tau> \<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>len\<^sub>0\<^bold>;\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d (\<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1) e = \<tau> \<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>len\<^sub>0\<^bold>;\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L (\<lambda>r. \<llangle>A\<^sub>1 r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d)\<rrangle> (\<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1) e\<close>
  by (auto simp add: combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k det_ndet_conv_defs option.case_eq_if \<epsilon>_simps \<rho>_simps)

lemma \<tau>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour:
  \<open>\<tau> \<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d (s\<^sub>0 # \<sigma>s\<^sub>1) e = \<tau> \<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t (\<lambda>r. \<llangle>A\<^sub>1 r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d)\<rrangle> (s\<^sub>0 # \<sigma>s\<^sub>1) e\<close>
  by (auto simp add: combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs det_ndet_conv_defs option.case_eq_if \<epsilon>_simps \<rho>_simps)


text \<open>Behaviour of normalisations\<close>

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour:
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d [s\<^sub>0, s\<^sub>1] = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t (\<lambda>r. \<llangle>A\<^sub>1 r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d)\<rrangle>\<rrangle>\<^sub>n\<^sub>d [s\<^sub>0, s\<^sub>1]\<close>
  by (fold P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_det_to_ndet_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d,
      rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_eqI_strong_id, unfold \<R>\<^sub>n\<^sub>d_from_det_to_ndet)
    (all \<open>drule set_mp[OF \<R>\<^sub>d_combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset]\<close>,
      auto simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs from_det_to_ndet_def \<rho>_simps split: option.split)

lemma P_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour:
  \<open>P\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d [s\<^sub>0, s\<^sub>1] = P\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t (\<lambda>r. \<llangle>A\<^sub>1 r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d)\<rrangle>\<rrangle>\<^sub>n\<^sub>d [s\<^sub>0, s\<^sub>1]\<close>
  by (fold P_nd_from_det_to_ndet_is_P_d,
      rule P_nd_eqI_strong_id, unfold \<R>\<^sub>n\<^sub>d_from_det_to_ndet)
    (drule set_mp[OF \<R>\<^sub>d_combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset],
      auto simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs from_det_to_ndet_def \<rho>_simps split: option.split)


lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour:
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (s\<^sub>0, s\<^sub>1) = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r (\<lambda>r. \<llangle>A\<^sub>1 r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d)\<rrangle>\<rrangle>\<^sub>n\<^sub>d (s\<^sub>0, s\<^sub>1)\<close>
  by (fold P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_det_to_ndet_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d,
      rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_eqI_strong_id, unfold \<R>\<^sub>n\<^sub>d_from_det_to_ndet)
    (all \<open>drule set_mp[OF \<R>\<^sub>d_combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset]\<close>,
      auto simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs from_det_to_ndet_def \<rho>_simps split: option.split)

lemma P_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour:
  \<open>P\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (s\<^sub>0, s\<^sub>1) = P\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r (\<lambda>r. \<llangle>A\<^sub>1 r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d)\<rrangle>\<rrangle>\<^sub>n\<^sub>d (s\<^sub>0, s\<^sub>1)\<close>
  by (fold P_nd_from_det_to_ndet_is_P_d,
      rule P_nd_eqI_strong_id, unfold \<R>\<^sub>n\<^sub>d_from_det_to_ndet)
    (drule set_mp[OF \<R>\<^sub>d_combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset],
      auto simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs from_det_to_ndet_def \<rho>_simps split: option.split)


lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour:
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (s\<^sub>0 # s\<^sub>1) = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t (\<lambda>r. \<llangle>A\<^sub>1 r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d)\<rrangle>\<rrangle>\<^sub>n\<^sub>d (s\<^sub>0 # s\<^sub>1)\<close>
  by (fold P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_det_to_ndet_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d,
      rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_eqI_strong_id, unfold \<R>\<^sub>n\<^sub>d_from_det_to_ndet)
    (all \<open>drule set_mp[OF \<R>\<^sub>d_combine\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset]\<close>,
      auto simp add: combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs from_det_to_ndet_def \<rho>_simps split: option.split)

lemma P_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour:
  \<open>P\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (s\<^sub>0 # s\<^sub>1) = P\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<^bold>;\<^sub>\<checkmark>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t (\<lambda>r. \<llangle>A\<^sub>1 r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d)\<rrangle>\<rrangle>\<^sub>n\<^sub>d (s\<^sub>0 # s\<^sub>1)\<close>
  by (fold P_nd_from_det_to_ndet_is_P_d,
      rule P_nd_eqI_strong_id, unfold \<R>\<^sub>n\<^sub>d_from_det_to_ndet)
    (drule set_mp[OF \<R>\<^sub>d_combine\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset],
      auto simp add: combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_defs from_det_to_ndet_def \<rho>_simps split: option.split)


lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour:
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>len\<^sub>0\<^bold>;\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (\<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1) = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>len\<^sub>0\<^bold>;\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L (\<lambda>r. \<llangle>A\<^sub>1 r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d)\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1)\<close>
  if \<open>\<And>\<sigma>s\<^sub>0'. \<sigma>s\<^sub>0' \<in> \<R>\<^sub>d A\<^sub>0 \<sigma>s\<^sub>0 \<Longrightarrow> length \<sigma>s\<^sub>0' = len\<^sub>0\<close>
  by (fold P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_det_to_ndet_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d,
      rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_eqI_strong_id, unfold \<R>\<^sub>n\<^sub>d_from_det_to_ndet)
    (all \<open>drule set_mp[OF \<R>\<^sub>d_combine\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset[OF that], rotated]\<close>,
      auto simp add: combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k from_det_to_ndet_def \<rho>_simps split: option.split)

lemma P_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_behaviour:
  \<open>P\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>len\<^sub>0\<^bold>;\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (\<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1) = P\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>len\<^sub>0\<^bold>;\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L (\<lambda>r. \<llangle>A\<^sub>1 r\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d)\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1)\<close>
  if \<open>\<And>\<sigma>t\<^sub>0. \<sigma>t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 \<sigma>s\<^sub>0 \<Longrightarrow> length \<sigma>t\<^sub>0 = len\<^sub>0\<close>
  by (fold P_nd_from_det_to_ndet_is_P_d,
      rule P_nd_eqI_strong_id, unfold \<R>\<^sub>n\<^sub>d_from_det_to_ndet)
    (drule set_mp[OF \<R>\<^sub>d_combine\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset[OF that], rotated],
      auto simp add: combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k from_det_to_ndet_def \<rho>_simps split: option.split)



(*<*)
end
  (*>*)