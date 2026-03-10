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


chapter \<open>Combining Automata for Synchronization Product\<close>

(*<*)
theory Combining_Synchronization_Product
  imports Process_Normalization
begin
  (*>*)


section \<open>Definitions\<close>

subsection \<open>General Patterns\<close>

abbreviation combine_sets_Sync :: \<open>'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set\<close>
  where \<open>combine_sets_Sync S\<^sub>0 E S\<^sub>1 \<equiv> (S\<^sub>0 - E - S\<^sub>1) \<union> (S\<^sub>1 - E - S\<^sub>0) \<union> (S\<^sub>0 \<inter> S\<^sub>1 - E) \<union> S\<^sub>0 \<inter> S\<^sub>1 \<inter> E\<close>

definition combine_Sync_\<epsilon> :: 
  \<open>[('\<sigma>\<^sub>0, 'e, '\<sigma>\<^sub>0', 'r\<^sub>0, '\<alpha>\<^sub>0) A_scheme, 'e set,
    ('\<sigma>\<^sub>1, 'e, '\<sigma>\<^sub>1', 'r\<^sub>1, '\<alpha>\<^sub>1) A_scheme, '\<sigma> \<Rightarrow> '\<sigma>\<^sub>0, '\<sigma> \<Rightarrow> '\<sigma>\<^sub>1, '\<sigma>] \<Rightarrow> 'e set\<close>
  where \<open>combine_Sync_\<epsilon> A\<^sub>0 E A\<^sub>1 i\<^sub>0 i\<^sub>1 \<sigma>s \<equiv> combine_sets_Sync (\<epsilon> A\<^sub>0 (i\<^sub>0 \<sigma>s)) E (\<epsilon> A\<^sub>1 (i\<^sub>1 \<sigma>s))\<close>

lemma combine_Sync_\<epsilon>_def_bis :
  \<open>combine_Sync_\<epsilon> A\<^sub>0 E A\<^sub>1 i\<^sub>0 i\<^sub>1 \<sigma>s =
   \<epsilon> A\<^sub>0 (i\<^sub>0 \<sigma>s) \<union> \<epsilon> A\<^sub>1 (i\<^sub>1 \<sigma>s) - E \<union> \<epsilon> A\<^sub>0 (i\<^sub>0 \<sigma>s) \<inter> \<epsilon> A\<^sub>1 (i\<^sub>1 \<sigma>s)\<close>
  by (auto simp add: combine_Sync_\<epsilon>_def)


fun combine\<^sub>d_Sync_\<tau> :: 
  \<open>[('\<sigma>\<^sub>0, 'e, 'r\<^sub>0, '\<alpha>\<^sub>0) A\<^sub>d_scheme, 'e set, ('\<sigma>\<^sub>1, 'e, 'r\<^sub>1, '\<alpha>\<^sub>1) A\<^sub>d_scheme,
    '\<sigma> \<Rightarrow> '\<sigma>\<^sub>0, '\<sigma> \<Rightarrow> '\<sigma>\<^sub>1, '\<sigma>\<^sub>0 \<Rightarrow> '\<sigma>\<^sub>1 \<Rightarrow> '\<sigma>] \<Rightarrow> ('\<sigma>, 'e) trans\<^sub>d\<close>
  and combine\<^sub>n\<^sub>d_Sync_\<tau> ::
  \<open>[('\<sigma>\<^sub>0, 'e, 'r\<^sub>0, '\<alpha>\<^sub>0) A\<^sub>n\<^sub>d_scheme, 'e set, ('\<sigma>\<^sub>1, 'e, 'r\<^sub>1, '\<alpha>\<^sub>1) A\<^sub>n\<^sub>d_scheme,
     '\<sigma> \<Rightarrow> '\<sigma>\<^sub>0, '\<sigma> \<Rightarrow> '\<sigma>\<^sub>1, '\<sigma>\<^sub>0 \<Rightarrow> '\<sigma>\<^sub>1 \<Rightarrow> '\<sigma>] \<Rightarrow> ('\<sigma>, 'e) trans\<^sub>n\<^sub>d\<close>
  where \<open>combine\<^sub>d_Sync_\<tau>  A\<^sub>0 E A\<^sub>1 i\<^sub>0 i\<^sub>1 f \<sigma>s e =
         (       if e \<in> \<epsilon> A\<^sub>0 (i\<^sub>0 \<sigma>s) \<inter> \<epsilon> A\<^sub>1 (i\<^sub>1 \<sigma>s)
               then update_both  A\<^sub>0 A\<^sub>1 (i\<^sub>0 \<sigma>s) (i\<^sub>1 \<sigma>s) e (f_up_opt f)
          else   if e \<in> \<epsilon> A\<^sub>0 (i\<^sub>0 \<sigma>s) - E - \<epsilon> A\<^sub>1 (i\<^sub>1 \<sigma>s)
               then update_left  A\<^sub>0    (i\<^sub>0 \<sigma>s) (i\<^sub>1 \<sigma>s) e (f_up_opt f) (\<lambda>s. \<lfloor>s\<rfloor>)
          else   if e \<in> \<epsilon> A\<^sub>1 (i\<^sub>1 \<sigma>s) - E - \<epsilon> A\<^sub>0 (i\<^sub>0 \<sigma>s)
               then update_right    A\<^sub>1 (i\<^sub>0 \<sigma>s) (i\<^sub>1 \<sigma>s) e (f_up_opt f) (\<lambda>s. \<lfloor>s\<rfloor>)
          else      \<diamond>)\<close>
  |     \<open>combine\<^sub>n\<^sub>d_Sync_\<tau>  A\<^sub>0 E A\<^sub>1 i\<^sub>0 i\<^sub>1 f \<sigma>s e = 
         (       if e \<in> \<epsilon> A\<^sub>0 (i\<^sub>0 \<sigma>s) \<inter> \<epsilon> A\<^sub>1 (i\<^sub>1 \<sigma>s) \<inter> E
               then update_both  A\<^sub>0 A\<^sub>1 (i\<^sub>0 \<sigma>s) (i\<^sub>1 \<sigma>s) e (f_up_set f)
          else   if e \<in> \<epsilon> A\<^sub>0 (i\<^sub>0 \<sigma>s) \<inter> \<epsilon> A\<^sub>1 (i\<^sub>1 \<sigma>s) - E
               then update_left  A\<^sub>0    (i\<^sub>0 \<sigma>s) (i\<^sub>1 \<sigma>s) e (f_up_set f) (\<lambda>s. {s})
                  \<union> update_right    A\<^sub>1 (i\<^sub>0 \<sigma>s) (i\<^sub>1 \<sigma>s) e (f_up_set f) (\<lambda>s. {s})
          else   if e \<in> \<epsilon> A\<^sub>0 (i\<^sub>0 \<sigma>s) - E - \<epsilon> A\<^sub>1 (i\<^sub>1 \<sigma>s)
               then update_left  A\<^sub>0    (i\<^sub>0 \<sigma>s) (i\<^sub>1 \<sigma>s) e (f_up_set f) (\<lambda>s. {s})
          else   if e \<in> \<epsilon> A\<^sub>1 (i\<^sub>1 \<sigma>s) - E - \<epsilon> A\<^sub>0 (i\<^sub>0 \<sigma>s)
               then update_right    A\<^sub>1 (i\<^sub>0 \<sigma>s) (i\<^sub>1 \<sigma>s) e (f_up_set f) (\<lambda>s. {s})
          else      {})\<close>

fun combine\<^sub>d_Sync_\<omega> :: 
  \<open>[('\<sigma>\<^sub>0, 'e, 'r\<^sub>0, '\<alpha>\<^sub>0) A\<^sub>d_scheme, 'e set, ('\<sigma>\<^sub>1, 'e, 'r\<^sub>1, '\<alpha>\<^sub>1) A\<^sub>d_scheme,
    '\<sigma> \<Rightarrow> '\<sigma>\<^sub>0, '\<sigma> \<Rightarrow> '\<sigma>\<^sub>1, 'r\<^sub>0 \<Rightarrow> 'r\<^sub>1 \<Rightarrow> 'r option] \<Rightarrow> ('\<sigma> \<Rightarrow> 'r option)\<close>
  and combine\<^sub>n\<^sub>d_Sync_\<omega> ::
  \<open>[('\<sigma>\<^sub>0, 'e, 'r\<^sub>0, '\<alpha>\<^sub>0) A\<^sub>n\<^sub>d_scheme, 'e set, ('\<sigma>\<^sub>1, 'e, 'r\<^sub>1, '\<alpha>\<^sub>1) A\<^sub>n\<^sub>d_scheme,
     '\<sigma> \<Rightarrow> '\<sigma>\<^sub>0, '\<sigma> \<Rightarrow> '\<sigma>\<^sub>1, 'r\<^sub>0 \<Rightarrow> 'r\<^sub>1 \<Rightarrow> 'r option] \<Rightarrow> ('\<sigma> \<Rightarrow> 'r set)\<close>
  where \<open>combine\<^sub>d_Sync_\<omega> A\<^sub>0 E A\<^sub>1 i\<^sub>0 i\<^sub>1 g \<sigma>s =
         (case \<omega> A\<^sub>0 (i\<^sub>0 \<sigma>s)
            of \<diamond> \<Rightarrow> \<diamond> | \<lfloor>r\<^sub>0\<rfloor> \<Rightarrow> (case \<omega> A\<^sub>1 (i\<^sub>1 \<sigma>s) of \<diamond> \<Rightarrow> \<diamond> | \<lfloor>r\<^sub>1\<rfloor> \<Rightarrow> g r\<^sub>0 r\<^sub>1))\<close>
  |     \<open>combine\<^sub>n\<^sub>d_Sync_\<omega> A\<^sub>0 E A\<^sub>1 i\<^sub>0 i\<^sub>1 g \<sigma>s =
         {r |r r\<^sub>0 r\<^sub>1. g r\<^sub>0 r\<^sub>1 = \<lfloor>r\<rfloor> \<and> r\<^sub>0 \<in> \<omega> A\<^sub>0 (i\<^sub>0 \<sigma>s) \<and> r\<^sub>1 \<in> \<omega> A\<^sub>1 (i\<^sub>1 \<sigma>s)}\<close>

fun combine\<^sub>d_Sync :: 
  \<open>[('\<sigma>\<^sub>0, 'e, 'r\<^sub>0, '\<alpha>\<^sub>0) A\<^sub>d_scheme, 'e set, ('\<sigma>\<^sub>1, 'e, 'r\<^sub>1, '\<alpha>\<^sub>1) A\<^sub>d_scheme,
    '\<sigma> \<Rightarrow> '\<sigma>\<^sub>0, '\<sigma> \<Rightarrow> '\<sigma>\<^sub>1, '\<sigma>\<^sub>0 \<Rightarrow> '\<sigma>\<^sub>1 \<Rightarrow> '\<sigma>, 'r\<^sub>0 \<Rightarrow> 'r\<^sub>1 \<Rightarrow> 'r option] \<Rightarrow> ('\<sigma>, 'e, 'r) A\<^sub>d\<close>
  and combine\<^sub>n\<^sub>d_Sync ::
  \<open>[('\<sigma>\<^sub>0, 'e, 'r\<^sub>0, '\<alpha>\<^sub>0) A\<^sub>n\<^sub>d_scheme, 'e set, ('\<sigma>\<^sub>1, 'e, 'r\<^sub>1, '\<alpha>\<^sub>1) A\<^sub>n\<^sub>d_scheme,
     '\<sigma> \<Rightarrow> '\<sigma>\<^sub>0, '\<sigma> \<Rightarrow> '\<sigma>\<^sub>1, '\<sigma>\<^sub>0 \<Rightarrow> '\<sigma>\<^sub>1 \<Rightarrow> '\<sigma>, 'r\<^sub>0 \<Rightarrow> 'r\<^sub>1 \<Rightarrow> 'r option] \<Rightarrow> ('\<sigma>, 'e, 'r) A\<^sub>n\<^sub>d\<close>
  where \<open>combine\<^sub>d_Sync A\<^sub>0 E A\<^sub>1 i\<^sub>0 i\<^sub>1 f g = 
         \<lparr>\<tau> = combine\<^sub>d_Sync_\<tau> A\<^sub>0 E A\<^sub>1 i\<^sub>0 i\<^sub>1 f, \<omega> = combine\<^sub>d_Sync_\<omega> A\<^sub>0 E A\<^sub>1 i\<^sub>0 i\<^sub>1 g\<rparr>\<close>
  |     \<open>combine\<^sub>n\<^sub>d_Sync A\<^sub>0 E A\<^sub>1 i\<^sub>0 i\<^sub>1 f g = 
         \<lparr>\<tau> = combine\<^sub>n\<^sub>d_Sync_\<tau> A\<^sub>0 E A\<^sub>1 i\<^sub>0 i\<^sub>1 f, \<omega> = combine\<^sub>n\<^sub>d_Sync_\<omega> A\<^sub>0 E A\<^sub>1 i\<^sub>0 i\<^sub>1 g\<rparr>\<close>



subsection \<open>Specializations\<close>

definition combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync ::
  \<open>[('\<sigma>, 'e, 'r, '\<alpha>) A\<^sub>d_scheme, 'e set, ('\<sigma>, 'e, 'r, '\<beta>) A\<^sub>d_scheme] \<Rightarrow> ('\<sigma> list, 'e, 'r) A\<^sub>d\<close>
  where \<open>combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync A\<^sub>0 E A\<^sub>1 \<equiv>
         combine\<^sub>d_Sync A\<^sub>0 E A\<^sub>1 hd (\<lambda>\<sigma>s. hd (tl \<sigma>s)) (\<lambda>s t. [s, t]) (\<lambda>s t. if s = t then \<lfloor>s\<rfloor> else \<diamond>)\<close>
definition combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync ::
  \<open>[('\<sigma>, 'e, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme, 'e set, ('\<sigma>, 'e, 'r, '\<beta>) A\<^sub>n\<^sub>d_scheme] \<Rightarrow> ('\<sigma> list, 'e, 'r) A\<^sub>n\<^sub>d\<close>
  where \<open>combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync A\<^sub>0 E A\<^sub>1 \<equiv>
         combine\<^sub>n\<^sub>d_Sync A\<^sub>0 E A\<^sub>1 hd (\<lambda>\<sigma>s. hd (tl \<sigma>s)) (\<lambda>s t. [s, t]) (\<lambda>s t. if s = t then \<lfloor>s\<rfloor> else \<diamond>)\<close>

definition combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync ::
  \<open>[('\<sigma>\<^sub>0, 'e, 'r, '\<alpha>) A\<^sub>d_scheme, 'e set, ('\<sigma>\<^sub>1, 'e, 'r, '\<beta>) A\<^sub>d_scheme] \<Rightarrow> ('\<sigma>\<^sub>0 \<times> '\<sigma>\<^sub>1, 'e, 'r) A\<^sub>d\<close>
  where \<open>combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync A\<^sub>0 E A\<^sub>1 \<equiv>
         combine\<^sub>d_Sync A\<^sub>0 E A\<^sub>1 fst snd Pair (\<lambda>s t. if s = t then \<lfloor>s\<rfloor> else \<diamond>)\<close>
definition combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync ::
  \<open>[('\<sigma>\<^sub>0, 'e, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme, 'e set, ('\<sigma>\<^sub>1, 'e, 'r, '\<beta>) A\<^sub>n\<^sub>d_scheme] \<Rightarrow> ('\<sigma>\<^sub>0 \<times> '\<sigma>\<^sub>1, 'e, 'r) A\<^sub>n\<^sub>d\<close>
  where \<open>combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync A\<^sub>0 E A\<^sub>1 \<equiv>
         combine\<^sub>n\<^sub>d_Sync A\<^sub>0 E A\<^sub>1 fst snd Pair (\<lambda>s t. if s = t then \<lfloor>s\<rfloor> else \<diamond>)\<close>

definition combine\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync ::
  \<open>[('\<sigma> list, 'e, 'r, '\<alpha>) A\<^sub>d_scheme, nat, 'e set, ('\<sigma> list, 'e, 'r, '\<beta>) A\<^sub>d_scheme] \<Rightarrow> ('\<sigma> list, 'e, 'r) A\<^sub>d\<close>
  where \<open>combine\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync A\<^sub>0 len\<^sub>0 E A\<^sub>1 \<equiv>
         combine\<^sub>d_Sync A\<^sub>0 E A\<^sub>1 (take len\<^sub>0) (drop len\<^sub>0) (@) (\<lambda>s t. if s = t then \<lfloor>s\<rfloor> else \<diamond>)\<close>
definition combine\<^sub>n\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync ::
  \<open>[('\<sigma> list, 'e, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme, nat, 'e set, ('\<sigma> list, 'e, 'r, '\<beta>) A\<^sub>n\<^sub>d_scheme] \<Rightarrow> ('\<sigma> list, 'e, 'r) A\<^sub>n\<^sub>d\<close>
  where \<open>combine\<^sub>n\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync A\<^sub>0 len\<^sub>0 E A\<^sub>1 \<equiv>
         combine\<^sub>n\<^sub>d_Sync A\<^sub>0 E A\<^sub>1 (take len\<^sub>0) (drop len\<^sub>0) (@) (\<lambda>s t. if s = t then \<lfloor>s\<rfloor> else \<diamond>)\<close>

definition combine\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync ::
  \<open>[('\<sigma>, 'e, 'r, '\<alpha>) A\<^sub>d_scheme, 'e set, ('\<sigma> list, 'e, 'r, '\<beta>) A\<^sub>d_scheme]  \<Rightarrow> ('\<sigma> list, 'e, 'r) A\<^sub>d\<close>
  where \<open>combine\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync A\<^sub>0 E A\<^sub>1 \<equiv>
         combine\<^sub>d_Sync A\<^sub>0 E A\<^sub>1 hd tl (#) (\<lambda>s t. if s = t then \<lfloor>s\<rfloor> else \<diamond>)\<close>
definition combine\<^sub>n\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync ::
  \<open>[('\<sigma>, 'e, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme, 'e set, ('\<sigma> list, 'e, 'r, '\<beta>) A\<^sub>n\<^sub>d_scheme]  \<Rightarrow> ('\<sigma> list, 'e, 'r) A\<^sub>n\<^sub>d\<close>
  where \<open>combine\<^sub>n\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync A\<^sub>0 E A\<^sub>1 \<equiv>
         combine\<^sub>n\<^sub>d_Sync A\<^sub>0 E A\<^sub>1 hd tl (#) (\<lambda>s t. if s = t then \<lfloor>s\<rfloor> else \<diamond>)\<close>

lemmas combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs = combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_def combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_def
  and combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_defs = combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_def combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_def
  and combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync_defs = combine\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync_def combine\<^sub>n\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync_def
  and combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs = combine\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_def combine\<^sub>n\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_def

lemmas combine_Sync_defs =
  combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_defs combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync_defs combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs


bundle combine\<^sub>n\<^sub>d_Sync_syntax begin

notation combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync (\<open>\<llangle>_ \<^sub>d\<otimes>\<lbrakk>_\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t _\<rrangle>\<close> [0, 0, 0])
notation combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync (\<open>\<llangle>_ \<^sub>n\<^sub>d\<otimes>\<lbrakk>_\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t _\<rrangle>\<close> [0, 0, 0])
notation combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync (\<open>\<llangle>_ \<^sub>d\<otimes>\<lbrakk>_\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r _\<rrangle>\<close> [0, 0, 0])
notation combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync (\<open>\<llangle>_ \<^sub>n\<^sub>d\<otimes>\<lbrakk>_\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r _\<rrangle>\<close> [0, 0, 0])
notation combine\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync (\<open>\<llangle>_ \<^sub>d\<otimes>\<lbrakk>_, _\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L _\<rrangle>\<close> [0, 0, 0, 0])
notation combine\<^sub>n\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync (\<open>\<llangle>_ \<^sub>n\<^sub>d\<otimes>\<lbrakk>_, _\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L _\<rrangle>\<close> [0, 0, 0, 0])
notation combine\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync (\<open>\<llangle>_ \<^sub>d\<otimes>\<lbrakk>_\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t _\<rrangle>\<close> [0, 0, 0])
notation combine\<^sub>n\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync (\<open>\<llangle>_ \<^sub>n\<^sub>d\<otimes>\<lbrakk>_\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t _\<rrangle>\<close> [0, 0, 0])

end

unbundle combine\<^sub>n\<^sub>d_Sync_syntax



section \<open>First Properties\<close>

lemma finite_trans_combine\<^sub>n\<^sub>d_Sync_simps [simp] : 
  \<open>finite_trans A\<^sub>0 \<Longrightarrow> finite_trans A\<^sub>1 \<Longrightarrow> finite_trans \<llangle>A\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<close>
  \<open>finite_trans B\<^sub>0 \<Longrightarrow> finite_trans B\<^sub>1 \<Longrightarrow> finite_trans \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r B\<^sub>1\<rrangle>\<close>
  \<open>finite_trans C\<^sub>0 \<Longrightarrow> finite_trans C\<^sub>1 \<Longrightarrow> finite_trans \<llangle>C\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L C\<^sub>1\<rrangle>\<close>
  \<open>finite_trans D\<^sub>0 \<Longrightarrow> finite_trans D\<^sub>1 \<Longrightarrow> finite_trans \<llangle>D\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t D\<^sub>1\<rrangle>\<close>
  unfolding combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_def combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_def combine\<^sub>n\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync_def combine\<^sub>n\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_def 
  by (simp_all add: finite_trans_def finite_image_set2)

lemma \<epsilon>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync:
  \<open>\<epsilon> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> \<sigma>s = combine_Sync_\<epsilon> A\<^sub>0 E A\<^sub>1 hd (hd \<circ> tl) \<sigma>s\<close>
  \<open>\<epsilon> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t B\<^sub>1\<rrangle> \<sigma>s = combine_Sync_\<epsilon> B\<^sub>0 E B\<^sub>1 hd (hd \<circ> tl) \<sigma>s\<close>
  by (auto simp add: combine_Sync_\<epsilon>_def_bis combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs \<epsilon>_simps)

lemma \<epsilon>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync:
  \<open>\<epsilon> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle> \<sigma>s = combine_Sync_\<epsilon> A\<^sub>0 E A\<^sub>1 fst snd \<sigma>s\<close>
  \<open>\<epsilon> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r B\<^sub>1\<rrangle> \<sigma>s = combine_Sync_\<epsilon> B\<^sub>0 E B\<^sub>1 fst snd \<sigma>s\<close>
  by (auto simp add: combine_Sync_\<epsilon>_def_bis combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_defs \<epsilon>_simps)

lemma \<epsilon>_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync: 
  \<open>\<epsilon> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle> \<sigma>s = combine_Sync_\<epsilon> A\<^sub>0 E A\<^sub>1 (take len\<^sub>0) (drop len\<^sub>0) \<sigma>s\<close>
  \<open>\<epsilon> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L B\<^sub>1\<rrangle> \<sigma>s = combine_Sync_\<epsilon> B\<^sub>0 E B\<^sub>1 (take len\<^sub>0) (drop len\<^sub>0) \<sigma>s\<close>
  by (auto simp add: combine_Sync_\<epsilon>_def_bis combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync_defs \<epsilon>_simps)

lemma \<epsilon>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync:
  \<open>\<epsilon> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> \<sigma>s = combine_Sync_\<epsilon> A\<^sub>0 E A\<^sub>1 hd tl \<sigma>s\<close>
  \<open>\<epsilon> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t B\<^sub>1\<rrangle> \<sigma>s = combine_Sync_\<epsilon> B\<^sub>0 E B\<^sub>1 hd tl \<sigma>s\<close>
  by (auto simp add: combine_Sync_\<epsilon>_def_bis combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs \<epsilon>_simps)


lemma \<rho>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync:
  \<open>\<rho> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> = {\<sigma>s. hd \<sigma>s \<in> \<rho> A\<^sub>0 \<and> hd (tl \<sigma>s) \<in> \<rho> A\<^sub>1 \<and> \<omega> A\<^sub>0 (hd \<sigma>s) = \<omega> A\<^sub>1 (hd (tl \<sigma>s))}\<close>
  \<open>\<rho> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t B\<^sub>1\<rrangle> = {\<sigma>s. hd \<sigma>s \<in> \<rho> B\<^sub>0 \<and> hd (tl \<sigma>s) \<in> \<rho> B\<^sub>1 \<and> \<omega> B\<^sub>0 (hd \<sigma>s) \<inter> \<omega> B\<^sub>1 (hd (tl \<sigma>s)) \<noteq> {}}\<close>
  by (auto simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs \<rho>_simps split: option.split)

lemma \<rho>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync:
  \<open>\<rho> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle> = {(\<sigma>\<^sub>0, \<sigma>\<^sub>1). \<sigma>\<^sub>0 \<in> \<rho> A\<^sub>0 \<and> \<sigma>\<^sub>1 \<in> \<rho> A\<^sub>1 \<and> \<omega> A\<^sub>0 \<sigma>\<^sub>0 = \<omega> A\<^sub>1 \<sigma>\<^sub>1}\<close>
  \<open>\<rho> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r B\<^sub>1\<rrangle> = {(\<sigma>\<^sub>0, \<sigma>\<^sub>1). \<sigma>\<^sub>0 \<in> \<rho> B\<^sub>0 \<and> \<sigma>\<^sub>1 \<in> \<rho> B\<^sub>1 \<and> \<omega> B\<^sub>0 \<sigma>\<^sub>0 \<inter> \<omega> B\<^sub>1 \<sigma>\<^sub>1 \<noteq> {}}\<close>
  by (auto simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_defs \<rho>_simps split: option.split)

lemma \<rho>_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync: 
  \<open>\<rho> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle> =
   {\<sigma>s. take len\<^sub>0 \<sigma>s \<in> \<rho> A\<^sub>0 \<and> drop len\<^sub>0 \<sigma>s \<in> \<rho> A\<^sub>1 \<and> \<omega> A\<^sub>0 (take len\<^sub>0 \<sigma>s) = \<omega> A\<^sub>1 (drop len\<^sub>0 \<sigma>s)}\<close>
  \<open>\<rho> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L B\<^sub>1\<rrangle> =
   {\<sigma>s. take len\<^sub>0 \<sigma>s \<in> \<rho> B\<^sub>0 \<and> drop len\<^sub>0 \<sigma>s \<in> \<rho> B\<^sub>1 \<and> \<omega> B\<^sub>0 (take len\<^sub>0 \<sigma>s) \<inter> \<omega> B\<^sub>1 (drop len\<^sub>0 \<sigma>s) \<noteq> {}}\<close>
  by (auto simp add: combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync_defs \<rho>_simps split: option.split)

lemma \<rho>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync:
  \<open>\<rho> \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> =
   {\<sigma>s. hd \<sigma>s \<in> \<rho> A\<^sub>0 \<and> tl \<sigma>s \<in> \<rho> A\<^sub>1 \<and> \<omega> A\<^sub>0 (hd \<sigma>s) = \<omega> A\<^sub>1 (tl \<sigma>s)}\<close>
  \<open>\<rho> \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t B\<^sub>1\<rrangle> =
   {\<sigma>s. hd \<sigma>s \<in> \<rho> B\<^sub>0 \<and> tl \<sigma>s \<in> \<rho> B\<^sub>1 \<and> \<omega> B\<^sub>0 (hd \<sigma>s) \<inter> \<omega> B\<^sub>1 (tl \<sigma>s) \<noteq> {}}\<close>
  by (auto simp add: combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs \<rho>_simps split: option.split)



lemma combine_Sync_\<tau> [simp] :
  \<open>combine\<^sub>d_Sync_\<tau> (A\<^sub>0\<lparr>\<omega> := some_\<omega>\<^sub>0\<rparr>) E (A\<^sub>1\<lparr>\<omega> := some_\<omega>\<^sub>1\<rparr>) = combine\<^sub>d_Sync_\<tau> A\<^sub>0 E A\<^sub>1\<close>
  \<open>combine\<^sub>n\<^sub>d_Sync_\<tau> (B\<^sub>0\<lparr>\<omega> := some_\<omega>\<^sub>0'\<rparr>) E (B\<^sub>1\<lparr>\<omega> := some_\<omega>\<^sub>1'\<rparr>) = combine\<^sub>n\<^sub>d_Sync_\<tau> B\<^sub>0 E B\<^sub>1\<close>
  for A :: \<open>('\<sigma>, 'a, '\<sigma> option, 'r option, '\<alpha>) A_scheme\<close>
    and B :: \<open>('\<sigma>, 'a, '\<sigma> set, 'r set, '\<alpha>) A_scheme\<close>
  by (intro ext, simp)+





section \<open>Reachability\<close>

lemma \<R>\<^sub>d_combine\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync_subset: 
  \<open>\<R>\<^sub>d \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle> (s\<^sub>0 @ s\<^sub>1) \<subseteq> {t\<^sub>0 @ t\<^sub>1| t\<^sub>0 t\<^sub>1. t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 s\<^sub>0 \<and> t\<^sub>1 \<in> \<R>\<^sub>d A\<^sub>1 s\<^sub>1}\<close> (is \<open>?S\<^sub>A \<subseteq> _\<close>)
  if same_length_\<R>\<^sub>d: \<open>\<And>t\<^sub>0. t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 s\<^sub>0 \<Longrightarrow> length t\<^sub>0 = len\<^sub>0\<close>
proof safe
  show \<open>t \<in> ?S\<^sub>A \<Longrightarrow> \<exists>t\<^sub>0 t\<^sub>1. t = t\<^sub>0 @ t\<^sub>1 \<and> t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 s\<^sub>0 \<and> t\<^sub>1 \<in> \<R>\<^sub>d A\<^sub>1 s\<^sub>1\<close> for t
    apply (induct rule: \<R>\<^sub>d.induct, metis \<R>\<^sub>d.init)
    by (simp_all add: combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync_defs same_length_\<R>\<^sub>d \<epsilon>_simps split: if_splits)
      (metis (no_types, opaque_lifting) \<R>\<^sub>d.simps)+
qed

lemma \<R>\<^sub>n\<^sub>d_combine\<^sub>n\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync_subset: 
  \<open>\<R>\<^sub>n\<^sub>d \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L B\<^sub>1\<rrangle> (s\<^sub>0 @ s\<^sub>1) \<subseteq> {t\<^sub>0 @ t\<^sub>1| t\<^sub>0 t\<^sub>1. t\<^sub>0 \<in> \<R>\<^sub>n\<^sub>d B\<^sub>0 s\<^sub>0 \<and> t\<^sub>1 \<in> \<R>\<^sub>n\<^sub>d B\<^sub>1 s\<^sub>1}\<close> (is \<open>?S\<^sub>B \<subseteq> _\<close>)
  if same_length_\<R>\<^sub>n\<^sub>d: \<open>\<And>t\<^sub>0. t\<^sub>0 \<in> \<R>\<^sub>n\<^sub>d B\<^sub>0 s\<^sub>0 \<Longrightarrow> length t\<^sub>0 = len\<^sub>0\<close>
proof safe
  show \<open>t \<in> ?S\<^sub>B \<Longrightarrow> \<exists>t\<^sub>0 t\<^sub>1. t = t\<^sub>0 @ t\<^sub>1 \<and> t\<^sub>0 \<in> \<R>\<^sub>n\<^sub>d B\<^sub>0 s\<^sub>0 \<and> t\<^sub>1 \<in> \<R>\<^sub>n\<^sub>d B\<^sub>1 s\<^sub>1\<close> for t
    apply (induct rule: \<R>\<^sub>n\<^sub>d.induct, metis \<R>\<^sub>n\<^sub>d.init)
    by (simp_all add: combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync_defs same_length_\<R>\<^sub>n\<^sub>d \<epsilon>_simps split: if_splits)
      (metis (no_types, opaque_lifting) \<R>\<^sub>n\<^sub>d.simps)+
qed


lemma \<R>\<^sub>d_combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_subset:
  \<open>\<R>\<^sub>d \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> [s\<^sub>0, s\<^sub>1] \<subseteq> {[t\<^sub>0, t\<^sub>1]| t\<^sub>0 t\<^sub>1. t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 s\<^sub>0 \<and> t\<^sub>1 \<in> \<R>\<^sub>d A\<^sub>1 s\<^sub>1}\<close> (is \<open>?S\<^sub>A \<subseteq> _\<close>)
  and \<R>\<^sub>n\<^sub>d_combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_subset:
  \<open>\<R>\<^sub>n\<^sub>d \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t B\<^sub>1\<rrangle> [s\<^sub>0, s\<^sub>1] \<subseteq> {[t\<^sub>0, t\<^sub>1]| t\<^sub>0 t\<^sub>1. t\<^sub>0 \<in> \<R>\<^sub>n\<^sub>d B\<^sub>0 s\<^sub>0 \<and> t\<^sub>1 \<in> \<R>\<^sub>n\<^sub>d B\<^sub>1 s\<^sub>1}\<close> (is \<open>?S\<^sub>B \<subseteq> _\<close>)
proof safe
  show \<open>t \<in> ?S\<^sub>A \<Longrightarrow> \<exists>t\<^sub>0 t\<^sub>1. t = [t\<^sub>0, t\<^sub>1] \<and> t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 s\<^sub>0 \<and> t\<^sub>1 \<in> \<R>\<^sub>d A\<^sub>1 s\<^sub>1\<close> for t
    by (\<R>\<^sub>d_subset_method defs: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs)
  show \<open>t \<in> ?S\<^sub>B \<Longrightarrow> \<exists>t\<^sub>0 t\<^sub>1. t = [t\<^sub>0, t\<^sub>1] \<and> t\<^sub>0 \<in> \<R>\<^sub>n\<^sub>d B\<^sub>0 s\<^sub>0 \<and> t\<^sub>1 \<in> \<R>\<^sub>n\<^sub>d B\<^sub>1 s\<^sub>1\<close> for t
    by (\<R>\<^sub>n\<^sub>d_subset_method defs: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs)
qed

lemma \<R>\<^sub>d_combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_subset:
  \<open>\<R>\<^sub>d \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle> (s\<^sub>0, s\<^sub>1) \<subseteq> \<R>\<^sub>d A\<^sub>0 s\<^sub>0 \<times> \<R>\<^sub>d A\<^sub>1 s\<^sub>1\<close> (is \<open>?S\<^sub>A \<subseteq> _\<close>)
  and \<R>\<^sub>n\<^sub>d_combine\<^sub>n\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_subset:
  \<open>\<R>\<^sub>n\<^sub>d \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r B\<^sub>1\<rrangle> (s\<^sub>0, s\<^sub>1) \<subseteq> \<R>\<^sub>n\<^sub>d B\<^sub>0 s\<^sub>0 \<times> \<R>\<^sub>n\<^sub>d B\<^sub>1 s\<^sub>1\<close> (is \<open>?S\<^sub>B \<subseteq> _\<close>)
proof -
  have \<open>t \<in> ?S\<^sub>A \<Longrightarrow> fst t \<in> \<R>\<^sub>d A\<^sub>0 s\<^sub>0 \<and> snd t \<in> \<R>\<^sub>d A\<^sub>1 s\<^sub>1\<close> for t 
    by (\<R>\<^sub>d_subset_method defs: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_defs)
  thus \<open>?S\<^sub>A \<subseteq> \<R>\<^sub>d A\<^sub>0 s\<^sub>0 \<times> \<R>\<^sub>d A\<^sub>1 s\<^sub>1\<close> by force
next
  have \<open>t \<in> ?S\<^sub>B \<Longrightarrow> fst t \<in> \<R>\<^sub>n\<^sub>d B\<^sub>0 s\<^sub>0 \<and> snd t \<in> \<R>\<^sub>n\<^sub>d B\<^sub>1 s\<^sub>1\<close> for t
    by (\<R>\<^sub>n\<^sub>d_subset_method defs: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_defs)
  thus \<open>?S\<^sub>B \<subseteq> \<R>\<^sub>n\<^sub>d B\<^sub>0 s\<^sub>0 \<times> \<R>\<^sub>n\<^sub>d B\<^sub>1 s\<^sub>1\<close> by force
qed


lemma \<R>\<^sub>d_combine\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_subset:
  \<open>\<R>\<^sub>d \<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle> (s\<^sub>0 # \<sigma>s) \<subseteq> {t\<^sub>0 # \<sigma>t| t\<^sub>0 \<sigma>t. t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 s\<^sub>0 \<and> \<sigma>t \<in> \<R>\<^sub>d A\<^sub>1 \<sigma>s}\<close> (is \<open>?S\<^sub>A \<subseteq> _\<close>)
  and \<R>\<^sub>n\<^sub>d_combine\<^sub>n\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_subset: 
  \<open>\<R>\<^sub>n\<^sub>d \<llangle>B\<^sub>0 \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t B\<^sub>1\<rrangle> (s\<^sub>0 # \<sigma>s) \<subseteq> {t\<^sub>0 # \<sigma>t| t\<^sub>0 \<sigma>t. t\<^sub>0 \<in> \<R>\<^sub>n\<^sub>d B\<^sub>0 s\<^sub>0 \<and> \<sigma>t \<in> \<R>\<^sub>n\<^sub>d B\<^sub>1 \<sigma>s}\<close> (is \<open>?S\<^sub>B \<subseteq> _\<close>)
proof safe
  show \<open>t \<in> ?S\<^sub>A \<Longrightarrow> \<exists>t\<^sub>0 \<sigma>t. t = t\<^sub>0 # \<sigma>t \<and> t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 s\<^sub>0 \<and> \<sigma>t \<in> \<R>\<^sub>d A\<^sub>1 \<sigma>s\<close> for t
    by (\<R>\<^sub>d_subset_method defs: combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs)
next
  show \<open>t \<in> ?S\<^sub>B \<Longrightarrow> \<exists>t\<^sub>0 \<sigma>t. t = t\<^sub>0 # \<sigma>t \<and> t\<^sub>0 \<in> \<R>\<^sub>n\<^sub>d B\<^sub>0 s\<^sub>0 \<and> \<sigma>t \<in> \<R>\<^sub>n\<^sub>d B\<^sub>1 \<sigma>s\<close> for t
    by (\<R>\<^sub>n\<^sub>d_subset_method defs: combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs)
qed



section \<open>Normalization\<close> 


lemma \<omega>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_behaviour:
  \<open>\<omega> \<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d [s\<^sub>0, s\<^sub>1] = \<omega> \<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle> [s\<^sub>0, s\<^sub>1]\<close>
  by (auto simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs det_ndet_conv_defs option.case_eq_if)

lemma \<omega>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_behaviour:
  \<open>\<omega> \<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d (s\<^sub>0, s\<^sub>1) = \<omega> \<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle> (s\<^sub>0, s\<^sub>1)\<close>
  by (auto simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_defs det_ndet_conv_defs option.case_eq_if)

lemma \<omega>_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync_behaviour:
  \<open>\<omega> \<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d (\<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1) = \<omega> \<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle> (\<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1)\<close>
  by (auto simp add: combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync_defs det_ndet_conv_defs option.case_eq_if)

lemma \<omega>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_behaviour:
  \<open>\<omega> \<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d (s\<^sub>0 # \<sigma>s\<^sub>1) = \<omega> \<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle> (s\<^sub>0 # \<sigma>s\<^sub>1)\<close>
  by (auto simp add: combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs det_ndet_conv_defs option.case_eq_if)


lemma \<tau>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_behaviour_when_indep:
  \<open>\<epsilon> A\<^sub>0 s\<^sub>0 \<inter> \<epsilon> A\<^sub>1 s\<^sub>1 \<subseteq> E \<Longrightarrow>
   \<tau> \<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d [s\<^sub>0, s\<^sub>1] e = \<tau> \<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle> [s\<^sub>0, s\<^sub>1] e\<close>
  by (auto simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs det_ndet_conv_defs option.case_eq_if \<epsilon>_simps)

lemma \<tau>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_behaviour_when_indep:
  \<open>\<epsilon> A\<^sub>0 s\<^sub>0 \<inter> \<epsilon> A\<^sub>1 s\<^sub>1 \<subseteq> E \<Longrightarrow> 
   \<tau> \<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d (s\<^sub>0, s\<^sub>1) e = \<tau> \<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle> (s\<^sub>0, s\<^sub>1) e\<close>
  by (auto simp add: combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_defs det_ndet_conv_defs option.case_eq_if \<epsilon>_simps)

lemma \<tau>_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync_behaviour_when_indep:
  \<open>\<epsilon> A\<^sub>0 \<sigma>s\<^sub>0 \<inter> \<epsilon> A\<^sub>1 \<sigma>s\<^sub>1 \<subseteq> E \<Longrightarrow> length \<sigma>s\<^sub>0 = len\<^sub>0 \<Longrightarrow> 
   \<tau> \<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d (\<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1) e = \<tau> \<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle> (\<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1) e\<close>
  by (auto simp add: combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync_defs det_ndet_conv_defs option.case_eq_if \<epsilon>_simps)

lemma \<tau>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_behaviour_when_indep:
  \<open>\<epsilon> A\<^sub>0 s\<^sub>0 \<inter> \<epsilon> A\<^sub>1 \<sigma>s\<^sub>1 \<subseteq> E \<Longrightarrow>
   \<tau> \<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d (s\<^sub>0 # \<sigma>s\<^sub>1) e = \<tau> \<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle> (s\<^sub>0 # \<sigma>s\<^sub>1) e\<close>
  by (auto simp add: combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_defs det_ndet_conv_defs option.case_eq_if \<epsilon>_simps)



method P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_when_indep_method uses R_d_subset = 
  fold P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_det_to_ndet_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d,
  rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_eqI_strong_id,
  unfold \<R>\<^sub>n\<^sub>d_from_det_to_ndet,
  all \<open>drule set_mp[OF R_d_subset, rotated]\<close>


method P_when_indep_method uses R_d_subset =
  fold P_nd_from_det_to_ndet_is_P_d,
  rule P_nd_eqI_strong_id,
  unfold \<R>\<^sub>n\<^sub>d_from_det_to_ndet,
  all \<open>drule set_mp[OF R_d_subset, rotated]\<close>


lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_behaviour_when_indep:
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d [s\<^sub>0, s\<^sub>1] = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<rrangle>\<^sub>n\<^sub>d [s\<^sub>0, s\<^sub>1]\<close>
  if \<open>indep_enabl A\<^sub>0 s\<^sub>0 E A\<^sub>1 s\<^sub>1\<close>
  by (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_when_indep_method R_d_subset: \<R>\<^sub>d_combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_subset, simp_all)
    (metis \<tau>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_behaviour_when_indep indep_enablD that,
      metis \<omega>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_behaviour)

lemma P_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_behaviour_when_indep:
  \<open>P\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d [s\<^sub>0, s\<^sub>1] = P\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<rrangle>\<^sub>n\<^sub>d [s\<^sub>0, s\<^sub>1]\<close>
  if \<open>indep_enabl A\<^sub>0 s\<^sub>0 E A\<^sub>1 s\<^sub>1\<close>
  by (P_when_indep_method R_d_subset: \<R>\<^sub>d_combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_subset, simp_all)
    (metis \<tau>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_behaviour_when_indep indep_enablD that)


lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_behaviour_when_indep:
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (s\<^sub>0, s\<^sub>1) = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<rrangle>\<^sub>n\<^sub>d (s\<^sub>0, s\<^sub>1)\<close>
  if \<open>indep_enabl A\<^sub>0 s\<^sub>0 E A\<^sub>1 s\<^sub>1\<close>
  by (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_when_indep_method R_d_subset: \<R>\<^sub>d_combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_subset, all \<open>elim SigmaE\<close>)
    (metis \<tau>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_behaviour_when_indep indep_enablD that,
      auto simp add: \<omega>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_behaviour option.case_eq_if)

lemma P_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_behaviour_when_indep:
  \<open>P\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (s\<^sub>0, s\<^sub>1) = P\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<rrangle>\<^sub>n\<^sub>d (s\<^sub>0, s\<^sub>1)\<close>
  if \<open>indep_enabl A\<^sub>0 s\<^sub>0 E A\<^sub>1 s\<^sub>1\<close>
  by (P_when_indep_method R_d_subset: \<R>\<^sub>d_combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_subset, elim SigmaE)
    (metis \<tau>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_behaviour_when_indep indep_enablD that)


lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync_behaviour_when_indep:
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (\<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1) = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1)\<close> 
  if \<open>indep_enabl A\<^sub>0 \<sigma>s\<^sub>0 E A\<^sub>1 \<sigma>s\<^sub>1\<close> and \<open>\<And>\<sigma>t\<^sub>0. \<sigma>t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 \<sigma>s\<^sub>0 \<Longrightarrow> length \<sigma>t\<^sub>0 = len\<^sub>0\<close>
  by (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_when_indep_method R_d_subset: \<R>\<^sub>d_combine\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync_subset, simp_all add: that(2))
    (metis \<tau>_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync_behaviour_when_indep indep_enablD that,
      metis \<omega>_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync_behaviour)

lemma P_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync_behaviour_when_indep:
  \<open>P\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (\<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1) = P\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>len\<^sub>0, E\<rbrakk>\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<rrangle>\<^sub>n\<^sub>d (\<sigma>s\<^sub>0 @ \<sigma>s\<^sub>1)\<close>
  if \<open>indep_enabl A\<^sub>0 \<sigma>s\<^sub>0 E A\<^sub>1 \<sigma>s\<^sub>1\<close> and \<open>\<And>\<sigma>t\<^sub>0. \<sigma>t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 \<sigma>s\<^sub>0 \<Longrightarrow> length \<sigma>t\<^sub>0 = len\<^sub>0\<close>
  by (P_when_indep_method R_d_subset: \<R>\<^sub>d_combine\<^sub>d\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync_subset, simp_all add: that(2))
    (metis \<tau>_combine\<^sub>L\<^sub>i\<^sub>s\<^sub>t\<^sub>s\<^sub>l\<^sub>e\<^sub>n\<^sub>L_Sync_behaviour_when_indep indep_enablD that)


lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_behaviour_when_indep:
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (s\<^sub>0 # \<sigma>s\<^sub>1) = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<rrangle>\<^sub>n\<^sub>d (s\<^sub>0 # \<sigma>s\<^sub>1)\<close>
  if \<open>indep_enabl A\<^sub>0 s\<^sub>0 E A\<^sub>1 \<sigma>s\<^sub>1\<close>
  by (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_when_indep_method R_d_subset: \<R>\<^sub>d_combine\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_subset, simp_all)
    (metis \<tau>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_behaviour_when_indep indep_enablD that,
      metis \<omega>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_behaviour)

lemma P_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_behaviour_when_indep:
  \<open>P\<llangle>\<llangle>A\<^sub>0 \<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t A\<^sub>1\<rrangle>\<rrangle>\<^sub>d (s\<^sub>0 # \<sigma>s\<^sub>1) = P\<llangle>\<llangle>\<llangle>A\<^sub>0\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<otimes>\<lbrakk>E\<rbrakk>\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<llangle>A\<^sub>1\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<rrangle>\<^sub>n\<^sub>d (s\<^sub>0 # \<sigma>s\<^sub>1)\<close>
  if \<open>indep_enabl A\<^sub>0 s\<^sub>0 E A\<^sub>1 \<sigma>s\<^sub>1\<close>
  by (P_when_indep_method R_d_subset: \<R>\<^sub>d_combine\<^sub>d\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_subset, simp)
    (metis \<tau>_combine\<^sub>R\<^sub>l\<^sub>i\<^sub>s\<^sub>t_Sync_behaviour_when_indep indep_enablD that)


(*<*)
end
  (*>*)