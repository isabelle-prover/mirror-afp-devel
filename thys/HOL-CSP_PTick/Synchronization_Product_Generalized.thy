(***********************************************************************************
 * Copyright (c) 2025 Université Paris-Saclay
 *
 * Author: Benoît Ballenghien, Université Paris-Saclay,
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


chapter \<open>Generalization of the Synchronization Product\<close>

(*<*)
theory  Synchronization_Product_Generalized
  imports "HOL-CSP"
begin
  (*>*)

section \<open>Trace Interleaving\<close>

subsection \<open>Motivation\<close>

text \<open>
The notion of trace interleaving found in \<^session>\<open>HOL-CSP\<close>
does not allow us to precisely handle termination.
Indeed, as soon as \<^term>\<open>r \<noteq> s\<close>, we cannot have
\<^term>\<open>t setinterleaves (([\<checkmark>(r)], [\<checkmark>(s)]), range tick \<union> ev ` A)\<close>.
\<close>


lemma \<open>r \<noteq> s \<Longrightarrow> \<not> t setinterleaves (([\<checkmark>(r)], [\<checkmark>(s)]), range tick \<union> ev ` A)\<close> by simp

text \<open>
The actual issue of this previous definition is that no distinction is done
between the ``regular'' events (like \<^term>\<open>ev a\<close>) and the terminations (like \<^term>\<open>\<checkmark>(r)\<close>).
Here, while we still want the same behaviour for regular events, we want instead
the interleaving of \<^term>\<open>\<checkmark>(r)\<close> and \<^term>\<open>\<checkmark>(s)\<close> to be \<^term>\<open>\<checkmark>((r, s))\<close>.
But we would also like this interleaving to generalize the old one,
i.e. be able to prevent sometimes two ticks from being combined.
Our solution is therefore to rely on a parameter:
\<^term>\<open>tick_join\<close> of type \<^typ>\<open>'r \<Rightarrow> 's \<Rightarrow> 't option\<close> whose role is to specify how
two ticks can be combined (or not).
\<close>


bundle option_type_syntax
begin

no_notation floor   (\<open>(\<open>open_block notation=\<open>mixfix floor\<close>\<close>\<lfloor>_\<rfloor>)\<close>)
no_notation ceiling (\<open>(\<open>open_block notation=\<open>mixfix ceiling\<close>\<close>\<lceil>_\<rceil>)\<close>)

notation Some       (\<open>(\<open>open_block notation=\<open>mixfix Some\<close>\<close>\<lfloor>_\<rfloor>)\<close>)
notation the        (\<open>(\<open>open_block notation=\<open>mixfix the\<close>\<close>\<lceil>_\<rceil>)\<close>)
notation None       (\<open>\<diamond>\<close>)

end

unbundle option_type_syntax



subsection \<open>Definition\<close>


type_synonym ('a, 'r, 's, 't) setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_args =
  \<open>('r \<Rightarrow> 's \<Rightarrow> 't option) \<times> ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<times> 'a set \<times> ('a, 's) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>

fun setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ::
  \<open>('a, 'r, 's, 't) setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_args \<Rightarrow> ('a, 't) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close>
  where Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil :
    \<open>setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, [], A, []) = {[]}\<close>

|       ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil :
  \<open>setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, ev a # u, A, []) =
   (  if a \<in> A then {}
    else {ev a # t| t. t \<in> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, u, A, [])})\<close>
|       tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil :
  \<open>setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, \<checkmark>(r) # u, A, []) = {}\<close>

|       Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev :
  \<open>setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, [], A, ev b # v) =
   (  if b \<in> A then {}
    else {ev b # t| t. t \<in> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, [], A, v)})\<close>
|       Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick  :
  \<open>setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, [], A, \<checkmark>(s) # v) = {}\<close>

|       ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev : 
  \<open>setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, ev a # u, A, ev b # v) =
   (  if a \<in> A
    then    if b \<in> A 
          then   if a = b
               then {ev a # t |t. t \<in> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, u, A, v)}
               else {}
          else {ev b # t |t. t \<in> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, ev a # u, A, v)}
     else   if b \<in> A
          then {ev a # t |t. t \<in> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, u, A, ev b # v)}
          else {ev a # t |t. t \<in> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, u, A, ev b # v)} \<union>
               {ev b # t |t. t \<in> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, ev a # u, A, v)})\<close>
|       ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick :
  \<open>setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, ev a # u, A, \<checkmark>(s) # v) =
   (  if a \<in> A then {}
    else {ev a # t |t. t \<in> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, u, A, \<checkmark>(s) # v)})\<close>
|       tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev :
  \<open>setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, \<checkmark>(r) # u, A, ev b # v) =
   (  if b \<in> A then {}
    else {ev b # t |t. t \<in> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, \<checkmark>(r) # u, A, v)})\<close>
|       tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick :
  \<open>setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, \<checkmark>(r) # u, A, \<checkmark>(s) # v) =
  (case tick_join r s
   of \<lfloor>r_s\<rfloor> \<Rightarrow> {\<checkmark>(r_s) # t |t. t \<in> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, u, A, v)}
      |  \<diamond> \<Rightarrow> {})\<close>


lemmas setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_induct
  [case_names Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil
    tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev
    Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev
    ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev
    tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick,
    induct type: setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_args] = setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.induct



lemma Cons_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil :
  \<open>setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, e # u, A, []) =
   (case e of ev a \<Rightarrow>
    (  if a \<in> A then {}
     else {ev a # t |t. t \<in> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, u, A, [])})
            | \<checkmark>(r) \<Rightarrow> {})\<close>
  by (cases e) simp_all

lemma Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Cons :
  \<open>setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, [], A, e # v) =
   (case e of ev a \<Rightarrow>
    (  if a \<in> A then {}
     else {ev a # t |t. t \<in> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, [], A, v)})
            | \<checkmark>(r) \<Rightarrow> {})\<close>
  by (cases e) simp_all

lemma Cons_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Cons :
  \<open>setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, e # u, A, f # v) =
   (case e of ev a \<Rightarrow>
    (case f of ev b \<Rightarrow> 
       if a \<in> A
     then   if b \<in> A 
           then   if a = b
                then {ev a # t |t. t \<in> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, u, A, v)}
                else {}
           else {ev b # t |t. t \<in> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, ev a # u, A, v)}
      else   if b \<in> A
           then {ev a # t |t. t \<in> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, u, A, ev b # v)}
           else {ev a # t |t. t \<in> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, u, A, ev b # v)} \<union>
                {ev b # t |t. t \<in> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, ev a # u, A, v)}
             | \<checkmark>(s) \<Rightarrow>   if a \<in> A then {}
                       else {ev a # t |t. t \<in> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, u, A, \<checkmark>(s) # v)})
            | \<checkmark>(r) \<Rightarrow>
    (case f of ev b \<Rightarrow>
         if b \<in> A then {}
       else {ev b # t| t. t \<in> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, \<checkmark>(r) # u, A, v)}
             | \<checkmark>(s) \<Rightarrow>
         (case tick_join r s of \<lfloor>r_s\<rfloor> \<Rightarrow>
            {\<checkmark>(r_s) # t |t. t \<in> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, u, A, v)}
                                |  \<diamond> \<Rightarrow> {})))\<close>
  by (cases e; cases f) simp_all


lemmas setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps =
  Cons_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Cons Cons_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Cons 



abbreviation setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ::
  \<open>[('a, 't) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r \<Rightarrow> 's \<Rightarrow> 't option,
    ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 's) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a set] \<Rightarrow> bool\<close>
  (\<open>(_ /(setinterleaves\<^sub>\<checkmark>)\<^bsub>_\<^esub>/ '(()'(_, _')(), _'))\<close> [63,0,0,0,0] 64)
  where \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<equiv>
         t \<in> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, u, A, v)\<close>



subsection \<open>First Properties\<close>

text \<open>First of all: this formalization may seem tricky,
      but is actually a generalization of the old setup.\<close>

theorem setinterleaves_is_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>t setinterleaves ((u, v), range tick \<union> ev ` A) \<longleftrightarrow>
   t setinterleaves\<^sub>\<checkmark>\<^bsub>\<lambda>r s. if r = s then \<lfloor>r\<rfloor> else \<diamond>\<^esub> ((u, v), A)\<close>
  for t :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  by (induct \<open>(\<lambda>r :: 'r. \<lambda>s :: 'r. if r = s then \<lfloor>r\<rfloor> else \<diamond>, u, A, v)\<close>
      arbitrary: t u v) (simp_all add: image_iff)

corollary setinterleaves_is_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_unit :
  \<open>t setinterleaves ((u, v), insert \<checkmark> (ev ` A)) \<longleftrightarrow>
   t setinterleaves\<^sub>\<checkmark>\<^bsub>\<lambda>r s. \<lfloor>r\<rfloor>\<^esub> ((u, v), A)\<close> (is \<open>?lhs \<longleftrightarrow> ?rhs\<close>)
proof -
  have \<open>?lhs \<longleftrightarrow> t setinterleaves ((u, v), range tick \<union> ev ` A)\<close>
    by (simp add: UNIV_unit)
  also have \<open>\<dots> \<longleftrightarrow> ?rhs\<close>
    by (simp add: setinterleaves_is_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  finally show \<open>?lhs \<longleftrightarrow> ?rhs\<close> .
qed




lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym :
  \<comment>\<open>Of course not suitable for simplifier.\<close>
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>\<lambda>s r. tick_join r s\<^esub> ((v, u), A) \<longleftrightarrow>
   t setinterleaves\<^sub>\<checkmark>\<^bsub>\<lambda>r s. tick_join r s\<^esub> ((u, v), A)\<close>
  by (induct \<open>(tick_join, u, A, v)\<close> arbitrary: t u v) (auto split: option.split)


lemma setinterleaves\<^sub>P\<^sub>a\<^sub>i\<^sub>r_UNIV_iff :
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>\<lambda>r s. \<lfloor>(r, s)\<rfloor>\<^esub> ((u, v), UNIV) \<longleftrightarrow>
   u = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id fst) t \<and>
   v = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id snd) t\<close> for t :: \<open>('a, 'r \<times> 's) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  by (induct \<open>(\<lambda>r :: 'r. \<lambda>s :: 's. \<lfloor>(r, s)\<rfloor>, u, UNIV :: 'a set, v)\<close> arbitrary: t u v)
    (auto simp add: ev_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff tick_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)

lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_empty :
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), {}) \<Longrightarrow>
   ev a \<in> set t \<longleftrightarrow> ev a \<in> set u \<or> ev a \<in> set v\<close>
  for u :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<close>
  by (induct \<open>(tick_join, u, {} :: 'a set, v)\<close> arbitrary: t u v)
    (auto split: option.split_asm)




lemma tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_any_tick_join :
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join \<^esub> ((u, v), A) \<longleftrightarrow>
   t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join'\<^esub> ((u, v), A)\<close>
  if \<open>tF t \<or> tF u \<or> tF v\<close>
proof (rule iffI)
  from \<open>tF t \<or> tF u \<or> tF v\<close>
  show \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<Longrightarrow>
        t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join'\<^esub> ((u, v), A)\<close>
    for tick_join tick_join'
    by (induct \<open>(tick_join, u, A, v)\<close> arbitrary: t u v)
      (auto split: if_split_asm option.split_asm)
  thus \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join'\<^esub> ((u, v), A) \<Longrightarrow>
        t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A)\<close> .
qed



lemma tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff :
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<Longrightarrow> tF t \<longleftrightarrow> tF u \<and> tF v\<close>
  by (induct \<open>(tick_join, u, A, v)\<close> arbitrary: t u v)
    (auto split: if_split_asm option.split_asm)

lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree_imp :
  \<open>tF u \<or> tF v \<Longrightarrow> t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<Longrightarrow> tF t \<and> tF u \<and> tF v\<close>
  by (induct \<open>(tick_join, u, A, v)\<close> arbitrary: t u v)
    (auto split: if_split_asm)



lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_NilL_iff :
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> (([], v), A) \<longleftrightarrow>
   tF v \<and> set v \<inter> ev ` A = {} \<and> t = map ev (map of_ev v)\<close>
  for tick_join :: \<open>'r \<Rightarrow> 's \<Rightarrow> 't option\<close>
  by (induct \<open>(tick_join, [] :: ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, A, v)\<close>
      arbitrary: t v) (auto split: if_split_asm)

lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_NilR_iff :
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, []), A) \<longleftrightarrow>
   tF u \<and> set u \<inter> ev ` A = {} \<and> t = map ev (map of_ev u)\<close>
  for tick_join :: \<open>'r \<Rightarrow> 's \<Rightarrow> 't option\<close>
  by (induct \<open>(tick_join, u, A, [] :: ('a, 's) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)\<close>
      arbitrary: t u) (auto split: if_split_asm)

lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subsetL :
  \<open>tF t \<Longrightarrow> {a. ev a \<in> set u} \<subseteq> A \<Longrightarrow>
   t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<Longrightarrow>
   t = map ev (map of_ev v)\<close>
  by (induct \<open>(tick_join, u, A, v)\<close> arbitrary: t u v)
    (auto simp add: subset_iff split: if_split_asm option.split_asm)

lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subsetR :
  \<open>tF t \<Longrightarrow> {a. ev a \<in> set v} \<subseteq> A \<Longrightarrow>
   t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<Longrightarrow>
   t = map ev (map of_ev u)\<close>
  by (induct \<open>(tick_join, u, A, v)\<close> arbitrary: t u v)
    (auto simp add: subset_iff split: if_split_asm option.split_asm)

lemma Nil_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>[] setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<Longrightarrow> u = [] \<and> v = []\<close>
  by (induct \<open>(tick_join, u, A, v)\<close> arbitrary: u v)
    (simp_all split: if_split_asm option.split_asm)


lemma front_tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff :
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<Longrightarrow> ftF t \<longleftrightarrow> ftF u \<and> ftF v\<close>
proof (induct \<open>(tick_join, u, A, v)\<close> arbitrary: t u v)
  case Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil thus ?case by simp
next
  case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil a u)
  thus ?case by (simp add: setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_NilR_iff split: if_split_asm)
next
  case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil r u) thus ?case by simp
next
  case (Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev b v) 
  thus ?case by (simp add: setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_NilL_iff split: if_split_asm)
next
  case (Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick s v) thus ?case by simp
next
  case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev a u b v)
  thus ?case by (simp split: if_split_asm)
      (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) front_tickFree_Cons_iff front_tickFree_Nil)+
next
  case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick a u s v)
  thus ?case by (simp split: if_split_asm)
      (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) front_tickFree_Cons_iff front_tickFree_Nil)
next
  case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev r u b v)
  thus ?case by (simp split: if_split_asm)
      (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) front_tickFree_Cons_iff front_tickFree_Nil)
next
  case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick r u s v) thus ?case
    by (simp split: option.split_asm) 
      (metis Nil_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil
        event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(2) front_tickFree_Cons_iff singletonD)
qed





lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_notinL :
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<Longrightarrow> a \<notin> A \<Longrightarrow>
   t @ [ev a] setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u @ [ev a], v), A)\<close>
  by (induct \<open>(tick_join, u, A, v)\<close> arbitrary: t u v)
    (auto split: if_split_asm option.split_asm)

lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_notinR :
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<Longrightarrow> a \<notin> A \<Longrightarrow>
   t @ [ev a] setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v @ [ev a]), A)\<close>
  by (induct \<open>(tick_join, u, A, v)\<close> arbitrary: t u v)
    (auto split: if_split_asm option.split_asm)

lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_inside :
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<Longrightarrow> a \<in> A \<Longrightarrow>
   t @ [ev a] setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u @ [ev a], v @ [ev a]), A)\<close>
  by (induct \<open>(tick_join, u, A, v)\<close> arbitrary: t u v)
    (auto split: if_split_asm option.split_asm)


lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_tick :
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<Longrightarrow> tick_join r s = \<lfloor>r_s\<rfloor> \<Longrightarrow>
   t @ [\<checkmark>(r_s)] setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u @ [\<checkmark>(r)], v @ [\<checkmark>(s)]), A)\<close>
  by (induct \<open>(tick_join, u, A, v)\<close> arbitrary: t u v)
    (auto split: if_split_asm option.split_asm)


lemma Cons_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE :
  \<open>\<checkmark>(r_s) # t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<Longrightarrow>
   (\<And>u' v' r s. \<lbrakk>tick_join r s = \<lfloor>r_s\<rfloor>; u = \<checkmark>(r) # u'; v = \<checkmark>(s) # v';
                 t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v'), A)\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
  by (induct \<open>(tick_join, u, A, v)\<close> arbitrary: t u v)
    (simp_all split: if_split_asm option.split_asm)

lemma Cons_ev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE :
  \<open>ev a # t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<Longrightarrow>
   (\<And>u'. a \<notin> A \<Longrightarrow> u = ev a # u' \<Longrightarrow> t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v), A) \<Longrightarrow> thesis) \<Longrightarrow>
   (\<And>v'. a \<notin> A \<Longrightarrow> v = ev a # v' \<Longrightarrow> t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v'), A) \<Longrightarrow> thesis) \<Longrightarrow>
   (\<And>u' v'. a \<in> A \<Longrightarrow> u = ev a # u' \<Longrightarrow> v = ev a # v' \<Longrightarrow>
             t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v'), A) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
proof (induct \<open>(tick_join, u, A, v)\<close> arbitrary: u v t)
  case Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil thus ?case by simp
next
  case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil b u)
  from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil.prems(1) show ?case
    by (simp add: ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil.prems(2) split: if_split_asm)
next
  case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil r u) thus ?case by simp
next
  case (Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev c v)
  from Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(1) show ?case
    by (simp add: Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(3) split: if_split_asm)
next
  case (Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick s v) thus ?case by simp
next
  case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev b u c v)
  from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(1) show ?case
    by (simp add: ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(2, 3, 4) split: if_split_asm)
      (use ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(2, 3) in presburger)
next
  case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick b u s v)
  from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems(1) show ?case
    by (simp add: ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems(2) split: if_split_asm)
next
  case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev r u c v)
  from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(1) show ?case
    by (simp add: tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(3) split: if_split_asm)
next
  case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick r u s v)
  thus ?case by (simp split: option.split_asm)
qed


lemma rev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_rev_rev_iff :
  \<open>rev t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((rev u, rev v), A)
   \<longleftrightarrow> t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A)\<close>
  for u :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and v :: \<open>('a, 's) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof (rule iffI)
  show \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<Longrightarrow>
        rev t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((rev u, rev v), A)\<close>
    for u :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and v :: \<open>('a, 's) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and t
  proof (induct \<open>(tick_join, u, A, v)\<close> arbitrary: t u v)
    case Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil thus ?case by simp
  next
    case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil a u)
    thus ?case by (auto simp add: setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_notinL split: if_split_asm )
  next
    case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil r v) thus ?case by simp
  next
    case (Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev b v)
    thus ?case by (auto simp add:  setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_notinR split: if_split_asm )
  next
    case (Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick s v) thus ?case by simp
  next
    case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev a u b v)
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems
    consider (both_in)   t' where \<open>a \<in> A\<close> \<open>a = b\<close> \<open>t = ev a # t'\<close>
      \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A)\<close>
    |        (inR_mvL)   t' where \<open>a \<notin> A\<close> \<open>b \<in> A\<close> \<open>t = ev a # t'\<close>
      \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, ev b # v), A)\<close>
    |        (inL_mvR)   t' where \<open>a \<in> A\<close> \<open>b \<notin> A\<close> \<open>t = ev b # t'\<close>
      \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u, v), A)\<close>
    |        (notin_mvL) t' where \<open>a \<notin> A\<close> \<open>b \<notin> A\<close> \<open>t = ev a # t'\<close>
      \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, ev b # v), A)\<close>
    |        (notin_mvR) t' where \<open>a \<notin> A\<close> \<open>b \<notin> A\<close> \<open>t = ev b # t'\<close>
      \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u, v), A)\<close>
      by (auto split: if_split_asm)
    thus ?case
    proof cases
      case both_in thus ?thesis
        by (simp add: ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(1) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_inside)
    next
      case inR_mvL thus ?thesis
        by (metis ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(3) rev.simps(2) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_notinL)
    next
      case inL_mvR thus ?thesis
        by (metis ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(2) rev.simps(2) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_notinR)
    next
      case notin_mvL thus ?thesis
        by (metis ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(4) rev.simps(2) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_notinL)
    next
      case notin_mvR thus ?thesis
        by (metis ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(5) rev.simps(2) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_notinR)
    qed
  next
    case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick a u s v) thus ?case
      by (auto simp add: setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_notinL split: if_split_asm)
  next
    case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev r u b v) thus ?case
      by (auto simp add: setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_notinR split: if_split_asm)
  next
    case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick r u s v)
    from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems
    obtain t' r_s where \<open>tick_join r s = \<lfloor>r_s\<rfloor>\<close> \<open>t = \<checkmark>(r_s) # t'\<close>
      \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A)\<close>
      by (auto split: option.split_asm)
    from \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A)\<close>
    have \<open>rev t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((rev u, rev v), A)\<close>
      by (simp add: \<open>tick_join r s = \<lfloor>r_s\<rfloor>\<close> tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.hyps)
    hence \<open>rev t' @ [\<checkmark>(r_s)] setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((rev u @ [\<checkmark>(r)], rev v @ [\<checkmark>(s)]), A)\<close>
      by (simp add: \<open>tick_join r s = \<lfloor>r_s\<rfloor>\<close> setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_tick)
    thus ?case by (simp add: \<open>t = \<checkmark>(r_s) # t'\<close> )
  qed
  from this[of \<open>rev t\<close> \<open>rev u\<close> \<open>rev v\<close>, simplified]
  show \<open>rev t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((rev u, rev v), A) \<Longrightarrow>
        t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A)\<close> .
qed


lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_preserves_ev_notin_set :
  \<open>\<lbrakk>ev a \<notin> set u; ev a \<notin> set v; t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A)\<rbrakk> \<Longrightarrow> ev a \<notin> set t\<close>
  by (induct \<open>(tick_join, u, A, v)\<close> arbitrary: t u v)
    (auto split: if_split_asm option.split_asm)

lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inj_preserves_tick_notin_set :
  \<open>\<lbrakk>tick_join r s = \<lfloor>r_s\<rfloor>; \<checkmark>(r) \<notin> set u \<or> \<checkmark>(s) \<notin> set v;
    t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A)\<rbrakk> \<Longrightarrow> \<checkmark>(r_s) \<notin> set t\<close>
  \<comment>\<open>This is a weakened injectivity property.\<close>
  if inj_tick_join : \<open>\<And>r' s'. tick_join r' s' = \<lfloor>r_s\<rfloor> \<Longrightarrow> r' = r \<and> s' = s\<close>
  by (induct \<open>(tick_join, u, A, v)\<close> arbitrary: t u v)
    (auto split: if_split_asm option.split_asm, (metis inj_tick_join)+)

lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_preserves_ev_inside_set :
  \<open>\<lbrakk>ev a \<in> set u; ev a \<in> set v; t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A)\<rbrakk> \<Longrightarrow> ev a \<in> set t\<close>
  by (induct \<open>(tick_join, u, A, v)\<close> arbitrary: t u v)
    (auto split: if_split_asm option.split_asm)

lemma ev_notin_both_sets_imp_empty_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>\<lbrakk>ev a \<in> set u \<and> ev a \<notin> set v \<or> ev a \<notin> set u \<and> ev a \<in> set v; a \<in> A\<rbrakk> \<Longrightarrow>
   setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (tick_join, u, A, v) = {}\<close>
  by (induct \<open>(tick_join, u, A, v)\<close> arbitrary: u v)
    (simp_all, safe, auto split: option.split_asm)



lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_tick_snoc_tickE:
  \<open>(\<And>t' r_s. tick_join r s = \<lfloor>r_s\<rfloor> \<Longrightarrow> t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<Longrightarrow>
              t = t' @ [\<checkmark>(r_s)] \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
  if \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u @ [\<checkmark>(r)], v @ [\<checkmark>(s)]), A)\<close>
proof -
  from that have \<open>rev t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((\<checkmark>(r) # rev u, \<checkmark>(s) # rev v), A)\<close>
    by (metis (no_types) rev.simps(2) rev_rev_ident rev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_rev_rev_iff)
  then obtain t' r_s where \<open>tick_join r s = \<lfloor>r_s\<rfloor>\<close> \<open>rev t = \<checkmark>(r_s) # t'\<close>
    \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((rev u, rev v), A)\<close>
    by (cases t rule: rev_cases) (simp_all split: option.split_asm)
  hence \<open>rev t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<and> t = rev t' @ [\<checkmark>(r_s)]\<close>
    using rev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_rev_rev_iff by force
  with \<open>tick_join r s = \<lfloor>r_s\<rfloor>\<close>
  show \<open>(\<And>t' r_s. tick_join r s = \<lfloor>r_s\<rfloor> \<Longrightarrow> t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<Longrightarrow>
                  t = t' @ [\<checkmark>(r_s)] \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> by blast
qed

lemma snoc_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE :
  \<open>(\<And>u' v' r s. \<lbrakk>tick_join r s = \<lfloor>r_s\<rfloor>; t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v'), A);
                 u = u' @ [\<checkmark>(r)]; v = v' @ [\<checkmark>(s)]\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
  if \<open>t @ [\<checkmark>(r_s)] setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A)\<close>
proof -
  from that have \<open>rev (t @ [\<checkmark>(r_s)]) setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((rev u, rev v), A)\<close>
    by (metis (no_types) rev.simps(2) rev_rev_ident rev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_rev_rev_iff)
  hence \<open>\<checkmark>(r_s) # rev t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((rev u, rev v), A)\<close> by simp
  then obtain u' v' r s where \<open>tick_join r s = \<lfloor>r_s\<rfloor>\<close>
    \<open>rev t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v'), A)\<close>
    \<open>rev u = \<checkmark>(r) # u'\<close> \<open>rev v = \<checkmark>(s) # v'\<close>
    by (elim Cons_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
  hence \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((rev u', rev v'), A) \<and>
         u = rev u' @ [\<checkmark>(r)] \<and> v = rev v' @ [\<checkmark>(s)]\<close>
    using rev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_rev_rev_iff by fastforce
  with \<open>tick_join r s = \<lfloor>r_s\<rfloor>\<close>
  show \<open>(\<And>u' v' r s. \<lbrakk>tick_join r s = \<lfloor>r_s\<rfloor>; t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v'), A);
                      u = u' @ [\<checkmark>(r)]; v = v' @ [\<checkmark>(s)]\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> by blast
qed




subsection \<open>Lengths\<close>


lemma length_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_sum_minus_filterL :
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<Longrightarrow>
   length t = length u + length v - length (filter (\<lambda>e. e \<in> range tick \<union> ev ` A) u)\<close>
proof (induct t arbitrary: u v)
  case Nil
  thus ?case by (auto dest: Nil_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
next
  note thms = Suc_diff_le le_add1 length_filter_le order_trans
  case (Cons e t)
  from Cons.prems consider (mv_left) a u' where \<open>a \<notin> A\<close> \<open>e = ev a\<close> \<open>u = ev a # u'\<close>
    \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v), A)\<close>
  | (mv_right) a v' where \<open>a \<notin> A\<close> \<open>e = ev a\<close> \<open>v = ev a # v'\<close>
    \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v'), A)\<close>
  | (mv_both_ev) a u' v' where \<open>a \<in> A\<close> \<open>e = ev a\<close> \<open>u = ev a # u'\<close> \<open>v = ev a # v'\<close>
    \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v'), A)\<close>
  | (mv_both_tick) r s r_s u' v' where \<open>tick_join r s = \<lfloor>r_s\<rfloor>\<close> \<open>e = \<checkmark>(r_s)\<close>
    \<open>u = \<checkmark>(r) # u'\<close> \<open>v = \<checkmark>(s) # v'\<close> \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v'), A)\<close>
    by (cases e) (auto elim: Cons_ev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE Cons_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
  thus ?case
  proof cases
    case mv_left
    from Cons.hyps[OF mv_left(4)] show ?thesis
      by (simp add: mv_left(1-3) image_iff) (metis (no_types, lifting) thms)
  next
    case mv_right
    from Cons.hyps[OF mv_right(4)] show ?thesis
      by (simp add: mv_right(1-3) image_iff) (metis (no_types, lifting) thms)
  next
    case mv_both_ev
    from Cons.hyps[OF mv_both_ev(5)] show ?thesis
      by (simp add: mv_both_ev(1, 3, 4) image_iff) (metis (no_types, lifting) thms)
  next
    case mv_both_tick
    from Cons.hyps[OF mv_both_tick(5)] show ?thesis
      by (simp add: mv_both_tick(3, 4) image_iff) (metis (no_types, lifting) thms)
  qed
qed

lemma length_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_sum_minus_filterR :
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<Longrightarrow>
   length t = length u + length v - length (filter (\<lambda>e. e \<in> range tick \<union> ev ` A) v)\<close>
  by (subst (asm) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym)
    (auto dest: length_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_sum_minus_filterL)


lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_length : 
  \<open>t  setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<Longrightarrow>
   t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<Longrightarrow> length t = length t'\<close>
  by (simp add: length_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_sum_minus_filterL)


lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_imp_lengthLR_le :
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<Longrightarrow>
   length u \<le> length t \<and> length v \<le> length t\<close>
  by (induct \<open>(tick_join, u, A, v)\<close> arbitrary: t u v)
    (fastforce split: if_split_asm option.split_asm)+



subsection \<open>Trace Prefix Interleaving\<close>

text \<open>We start with versions involving \<^term>\<open>(@)\<close>
      before giving corollaries about the prefix ordering on traces.\<close>

lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendL : 
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1 @ u2, v), A) \<Longrightarrow>
   \<exists>t1 t2 v1 v2. t = t1 @ t2 \<and> v = v1 @ v2 \<and>
                 t1 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1, v1), A) \<and>
                 t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u2, v2), A)\<close>
proof (induct \<open>(tick_join, u1, A, v)\<close> arbitrary: t u1 v)
  case Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil
  thus ?case by simp
next
  case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil a u1)
  from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil.prems
  have \<open>a \<notin> A\<close> \<open>t = ev a # map ev (map of_ev (u1 @ u2))\<close>
    \<open>map ev (map of_ev (u1 @ u2)) setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1 @ u2, []), A)\<close>
    by (simp_all add: setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_NilR_iff split: if_split_asm)
  from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil.hyps[OF \<open>a \<notin> A\<close> this(3)]
  obtain t1 t2 v1 v2 where \<open>map ev (map of_ev (u1 @ u2)) = t1 @ t2\<close>
    \<open>[] = v1 @ v2\<close> \<open>t1 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1, v1), A)\<close>
    \<open>t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u2, v2), A)\<close> by blast
  thus ?case
    by (simp add: \<open>a \<notin> A\<close> \<open>t = ev a # map ev (map of_ev (u1 @ u2))\<close>) 
      (metis append_Cons)
next
  case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil r u1)
  from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil.prems have False by simp
  thus ?case ..
next
  case (Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev b v)
  thus ?case
    by (cases u2, simp_all split: if_split_asm)
      (fastforce, metis Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil self_append_conv2 singleton_iff)
next
  case (Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick s v)
  thus ?case by (cases u2, simp_all add: setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps
        split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split_asm) fastforce+
next
  case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev a u1 b v)
  from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems [simplified]
  consider (mv_both)   t' where \<open>a \<in> A\<close> \<open>b \<in> A\<close> \<open>a = b\<close> \<open>t = ev b # t'\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1 @ u2, v), A)\<close>
    |    (mvR_inL)   t' where \<open>a \<in> A\<close> \<open>b \<notin> A\<close> \<open>t = ev b # t'\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> (((ev a # u1) @ u2, v), A)\<close>
    |    (mvL_inR)   t' where \<open>a \<notin> A\<close> \<open>b \<in> A\<close> \<open>t = ev a # t'\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1 @ u2, ev b # v), A)\<close>
    |    (mvR_notin) t' where \<open>a \<notin> A\<close> \<open>b \<notin> A\<close> \<open>t = ev b # t'\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> (((ev a # u1) @ u2, v), A)\<close>
    |    (mvL_notin) t' where \<open>a \<notin> A\<close> \<open>b \<notin> A\<close> \<open>t = ev a # t'\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1 @ u2, ev b # v), A)\<close>
    by (auto split: if_split_asm)
  thus ?case
  proof cases 
    case mv_both
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(1)[OF mv_both(1-3, 5)] obtain t1 t2 v1 v2
      where \<open>t' = t1 @ t2\<close> \<open>v = v1 @ v2\<close> \<open>t1 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1, v1), A)\<close>
        \<open>t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u2, v2), A)\<close> by blast
    hence \<open>t = (ev b # t1) @ t2 \<and> ev b # v = (ev b # v1) @ v2 \<and>
           ev b # t1 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u1, ev b # v1), A) \<and>
           t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u2, v2), A)\<close> by (simp add: mv_both(1-4))
    thus ?thesis by blast
  next
    case mvR_inL
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(2)[OF mvR_inL(1, 2, 4)] obtain t1 t2 v1 v2
      where \<open>t' = t1 @ t2\<close> \<open>v = v1 @ v2\<close> \<open>t1 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u1, v1), A)\<close>
        \<open>t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u2, v2), A)\<close> by blast
    hence \<open>t = (ev b # t1) @ t2 \<and> ev b # v = (ev b # v1) @ v2 \<and>
           ev b # t1 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u1, ev b # v1), A) \<and>
           t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u2, v2), A)\<close> by (simp add: mvR_inL(1-3))
    thus ?thesis by blast
  next
    case mvL_inR
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(3)[OF mvL_inR(1, 2, 4)] obtain t1 t2 v1 v2
      where \<open>t' = t1 @ t2\<close> \<open>ev b # v = v1 @ v2\<close> \<open>t1 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1, v1), A)\<close>
        \<open>t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u2, v2), A)\<close> by blast
    hence \<open>t = (ev a # t1) @ t2 \<and> ev b # v = v1 @ v2 \<and>
           ev a # t1 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u1, v1), A) \<and>
           t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u2, v2), A)\<close>
      by (cases v1, simp_all add: mvL_inR(1, 3))
    thus ?thesis by blast
  next
    case mvR_notin
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(5)[OF mvR_notin(1, 2, 4)] obtain t1 t2 v1 v2
      where \<open>t' = t1 @ t2\<close> \<open>v = v1 @ v2\<close> \<open>t1 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u1, v1), A)\<close>
        \<open>t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u2, v2), A)\<close> by blast
    hence \<open>t = (ev b # t1) @ t2 \<and> ev b # v = (ev b # v1) @ v2 \<and>
           ev b # t1 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u1, ev b # v1), A) \<and>
           t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u2, v2), A)\<close> by (simp add: mvR_notin(1-3))
    thus ?thesis by blast
  next
    case mvL_notin
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(4)[OF mvL_notin(1, 2, 4)] obtain t1 t2 v1 v2
      where \<open>t' = t1 @ t2\<close> \<open>ev b # v = v1 @ v2\<close> \<open>t1 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1, v1), A)\<close>
        \<open>t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u2, v2), A)\<close> by blast
    hence \<open>t = (ev a # t1) @ t2 \<and> ev b # v = v1 @ v2 \<and>
           ev a # t1 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u1, v1), A) \<and>
           t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u2, v2), A)\<close>
      by (cases v1, simp_all add: mvL_notin(1, 3))
    thus ?thesis by blast
  qed
next
  case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick a u1 s v)
  from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems obtain t'
    where \<open>a \<notin> A\<close> \<open>t = ev a # t'\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1 @ u2, \<checkmark>(s) # v), A)\<close>
    by (auto split: if_split_asm)
  from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.hyps[OF this(1, 3)] obtain t1 t2 v1 v2
    where \<open>t' = t1 @ t2\<close> \<open>\<checkmark>(s) # v = v1 @ v2\<close>
      \<open>t1 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1, v1), A)\<close>
      \<open>t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u2, v2), A)\<close> by blast
  hence \<open>t = (ev a # t1) @ t2 \<and> \<checkmark>(s) # v = v1 @ v2 \<and>
         ev a # t1 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u1, v1), A) \<and>
         t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u2, v2), A)\<close>
    by (cases v1, simp_all add: \<open>t = ev a # t'\<close> \<open>a \<notin> A\<close>)
  thus ?case by blast
next
  case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev r u1 b v)
  from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems obtain t'
    where \<open>b \<notin> A\<close> \<open>t = ev b # t'\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> (((\<checkmark>(r) # u1) @ u2, v), A)\<close>
    by (auto split: if_split_asm)
  from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps[OF this(1, 3)] obtain t1 t2 v1 v2
    where \<open>t' = t1 @ t2\<close> \<open>v = v1 @ v2\<close>
      \<open>t1 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((\<checkmark>(r) # u1, v1), A)\<close>
      \<open>t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u2, v2), A)\<close> by blast
  hence \<open>t = (ev b # t1) @ t2 \<and> ev b # v = (ev b # v1) @ v2 \<and>
         ev b # t1 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((\<checkmark>(r) # u1, ev b # v1), A) \<and>
         t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u2, v2), A)\<close>
    by (simp add: \<open>t = ev b # t'\<close> \<open>b \<notin> A\<close>)
  thus ?case by blast
next
  case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick r u1 s v)
  from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems obtain r_s t'
    where \<open>tick_join r s = \<lfloor>r_s\<rfloor>\<close> \<open>t = \<checkmark>(r_s) # t'\<close>
      \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1 @ u2, v), A)\<close> by (auto split: option.split_asm)
  from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.hyps[OF this(1, 3)] obtain t1 t2 v1 v2
    where \<open>t' = t1 @ t2\<close> \<open>v = v1 @ v2\<close> \<open>t1 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1, v1), A)\<close>
      \<open>t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u2, v2), A)\<close> by blast
  hence \<open>t = (\<checkmark>(r_s) # t1) @ t2 \<and> \<checkmark>(s) # v = (\<checkmark>(s) # v1) @ v2 \<and>
         \<checkmark>(r_s) # t1 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((\<checkmark>(r) # u1, \<checkmark>(s) # v1), A) \<and>
         t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u2, v2), A)\<close>
    by (simp add: \<open>tick_join r s = \<lfloor>r_s\<rfloor>\<close> \<open>t = \<checkmark>(r_s) # t'\<close>)
  thus ?case by blast
qed

corollary setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendR : 
  \<open>\<exists>t1 t2 u1 u2. t = t1 @ t2 \<and> u = u1 @ u2 \<and>
                 t1 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1, v1), A) \<and>
                 t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u2, v2), A)\<close>
  if \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v1 @ v2), A)\<close>
proof -
  from that have \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>\<lambda>s r. tick_join r s\<^esub> ((v1 @ v2, u), A)\<close>
    using setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym by blast
  from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendL[OF this]
  obtain t1 t2 u1 u2 where \<open>t = t1 @ t2\<close> \<open>u = u1 @ u2\<close>
    \<open>t1 setinterleaves\<^sub>\<checkmark>\<^bsub>\<lambda>s r. tick_join r s\<^esub> ((v1, u1), A)\<close>
    \<open>t2 setinterleaves\<^sub>\<checkmark>\<^bsub>\<lambda>s r. tick_join r s\<^esub> ((v2, u2), A)\<close> by blast
  from this(3, 4) have \<open>t1 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1, v1), A)\<close>
    \<open>t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u2, v2), A)\<close> 
    using setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym by blast+
  with \<open>t = t1 @ t2\<close> \<open>u = u1 @ u2\<close> show ?thesis by blast
qed



lemma append_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>t1 @ t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<Longrightarrow>
   \<exists>u1 u2 v1 v2. u = u1 @ u2 \<and> v = v1 @ v2 \<and>
                 t1 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1, v1), A) \<and>
                 t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u2, v2), A)\<close>
proof (induct t1 arbitrary: u v)
  case Nil
  hence \<open>u = [] @ u\<close> \<open>v = [] @ v\<close>
    \<open>[] setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> (([], []), A)\<close>
    \<open>t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A)\<close> by simp_all
  thus ?case by blast
next
  case (Cons e t1)
  from Cons.prems consider (mv_left) a u' where \<open>a \<notin> A\<close> \<open>e = ev a\<close> \<open>u = ev a # u'\<close>
    \<open>t1 @ t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v), A)\<close>
  | (mv_right) a v' where \<open>a \<notin> A\<close> \<open>e = ev a\<close> \<open>v = ev a # v'\<close>
    \<open>t1 @ t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v'), A)\<close>
  | (mv_both_ev) a u' v' where \<open>a \<in> A\<close> \<open>e = ev a\<close> \<open>u = ev a # u'\<close> \<open>v = ev a # v'\<close>
    \<open>t1 @ t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v'), A)\<close>
  | (mv_both_tick) r s r_s u' v' where \<open>tick_join r s = \<lfloor>r_s\<rfloor>\<close> \<open>e = \<checkmark>(r_s)\<close>
    \<open>u = \<checkmark>(r) # u'\<close> \<open>v = \<checkmark>(s) # v'\<close> \<open>t1 @ t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v'), A)\<close>
    by (cases e) (auto elim: Cons_ev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE Cons_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
  thus ?case
  proof cases
    case mv_left
    from Cons.hyps[OF mv_left(4)] obtain u1 u2 v1 v2
      where \<open>u' = u1 @ u2\<close> \<open>t1 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1, v1), A)\<close>
        and * : \<open>v = v1 @ v2\<close> \<open>t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u2, v2), A)\<close> by blast
    from this(2) have \<open>e # t1 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u1, v1), A)\<close>
      by (cases v1) (auto simp add: \<open>a \<notin> A\<close> \<open>e = ev a\<close> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps
          split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
    moreover from \<open>u' = u1 @ u2\<close> have \<open>u = (ev a # u1) @ u2\<close>
      by (simp add: mv_left(3))
    ultimately show ?thesis using "*"(1, 2) by blast
  next
    case mv_right
    from Cons.hyps[OF mv_right(4)] obtain u1 u2 v1 v2
      where \<open>v' = v1 @ v2\<close> \<open>t1 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1, v1), A)\<close>
        and * : \<open>u = u1 @ u2\<close> \<open>t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u2, v2), A)\<close> by blast
    from this(2) have \<open>e # t1 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1, ev a # v1), A)\<close>
      by (cases u1) (auto simp add: \<open>a \<notin> A\<close> \<open>e = ev a\<close> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps
          split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
    moreover from \<open>v' = v1 @ v2\<close> have \<open>v = (ev a # v1) @ v2\<close>
      by (simp add: mv_right(3))
    ultimately show ?thesis using "*"(1, 2) by blast
  next
    case mv_both_ev
    from Cons.hyps[OF mv_both_ev(5)] obtain u1 u2 v1 v2
      where \<open>u' = u1 @ u2\<close> \<open>v' = v1 @ v2\<close> \<open>t1 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1, v1), A)\<close>
        and * : \<open>t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u2, v2), A)\<close> by blast
    from this(3) have \<open>e # t1 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u1, ev a # v1), A)\<close>
      by (simp add: \<open>a \<in> A\<close> \<open>e = ev a\<close>)
    moreover from \<open>u' = u1 @ u2\<close> have \<open>u = (ev a # u1) @ u2\<close>
      by (simp add: mv_both_ev(3))
    moreover from \<open>v' = v1 @ v2\<close> have \<open>v = (ev a # v1) @ v2\<close>
      by (simp add: mv_both_ev(4))
    ultimately show ?thesis using "*" by blast
  next
    case mv_both_tick
    from Cons.hyps[OF mv_both_tick(5)] obtain u1 u2 v1 v2
      where \<open>u' = u1 @ u2\<close> \<open>v' = v1 @ v2\<close> \<open>t1 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1, v1), A)\<close>
        and * : \<open>t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u2, v2), A)\<close> by blast
    from this(3) have \<open>e # t1 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((\<checkmark>(r) # u1, \<checkmark>(s) # v1), A)\<close>
      by (simp add: mv_both_tick(1, 2))
    moreover from \<open>u' = u1 @ u2\<close> have \<open>u = (\<checkmark>(r) # u1) @ u2\<close>
      by (simp add: mv_both_tick(3))
    moreover from \<open>v' = v1 @ v2\<close> have \<open>v = (\<checkmark>(s) # v1) @ v2\<close>
      by (simp add: mv_both_tick(4))
    ultimately show ?thesis using "*" by blast
  qed
qed



corollary setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_le_prefixL :
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<Longrightarrow> u' \<le> u \<Longrightarrow>
   \<exists>t' \<le> t. \<exists>v' \<le> v. t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v'), A)\<close>
  by (auto elim!: prefixE dest!: setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendL intro: prefixI)

corollary setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_le_prefixR :
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<Longrightarrow> v' \<le> v \<Longrightarrow>
   \<exists>t' \<le> t. \<exists>u' \<le> u. t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v'), A)\<close>
  by (auto elim!: prefixE dest!: setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendR intro: prefixI)

corollary le_prefix_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<Longrightarrow> t' \<le> t \<Longrightarrow>
   \<exists>u' \<le> u. \<exists>v' \<le> v. t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v'), A)\<close>
  by (auto elim!: prefixE dest!: append_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k intro: prefixI)




lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_less_prefixL :
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<Longrightarrow> u' < u \<Longrightarrow>
   \<exists>t' v'. t' < t \<and> v' \<le> v \<and> t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v'), A)\<close>
proof (induct \<open>(tick_join, u, A, v)\<close> arbitrary: t u u' v)
  case Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil thus ?case by simp
next
  case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil a u)
  from \<open>u' < ev a # u\<close> consider \<open>u' = []\<close> | u'' where \<open>u' = ev a # u''\<close> \<open>u'' < u\<close>
    by (metis Prefix_Order.prefix_Cons less_list_def)
  thus ?case
  proof cases
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil.prems(1)
    show \<open>u' = [] \<Longrightarrow> ?case\<close> by (auto split: if_split_asm)
  next
    fix u'' assume \<open>u' = ev a # u''\<close> \<open>u'' < u\<close>
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil.prems(1)
    obtain t' where \<open>a \<notin> A\<close> \<open>t = ev a # t'\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, []), A)\<close>
      by (auto split: if_split_asm)
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil.hyps[OF \<open>a \<notin> A\<close> this(3) \<open>u'' < u\<close>]
    obtain t'' v' where \<open>t'' < t'\<close> \<open>v' \<le> []\<close> \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u'', v'), A)\<close> by blast
    hence \<open>ev a # t'' < t \<and> v' \<le> [] \<and> ev a # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v'), A)\<close>
      by (simp add: \<open>u' = ev a # u''\<close> \<open>t = ev a # t'\<close> \<open>a \<notin> A\<close>)
    thus ?case by blast    
  qed
next
  case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil r u) thus ?case by simp
next
  case (Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev b v) thus ?case by simp
next
  case (Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick s v) thus ?case by simp
next
  case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev a u b v)
  from \<open>u' < ev a # u\<close> consider \<open>u' = []\<close> | u'' where \<open>u' = ev a # u''\<close> \<open>u'' < u\<close>
    by (metis Prefix_Order.prefix_Cons less_list_def)
  thus ?case
  proof cases
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(1)
    show \<open>u' = [] \<Longrightarrow> ?case\<close> by (simp split: if_split_asm) force+
  next
    fix u'' assume \<open>u' = ev a # u''\<close> \<open>u'' < u\<close>
    hence \<open>ev a # u'' < ev a # u\<close> by simp
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(1)
    consider (both_in)   t' where \<open>a \<in> A\<close> \<open>b \<in> A\<close> \<open>a = b\<close> \<open>t = ev a # t'\<close>
      \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A)\<close>
    |      (inR_mvL)   t' where \<open>a \<notin> A\<close> \<open>b \<in> A\<close> \<open>t = ev a # t'\<close>
      \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, ev b # v), A)\<close>
    |      (inL_mvR)   t' where \<open>a \<in> A\<close> \<open>b \<notin> A\<close> \<open>t = ev b # t'\<close>
      \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u, v), A)\<close>
    |      (notin_mvL) t' where \<open>a \<notin> A\<close> \<open>b \<notin> A\<close> \<open>t = ev a # t'\<close>
      \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, ev b # v), A)\<close>
    |      (notin_mvR) t' where \<open>a \<notin> A\<close> \<open>b \<notin> A\<close> \<open>t = ev b # t'\<close>
      \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u, v), A)\<close>
      by (auto split: if_split_asm)
    thus ?case
    proof cases
      case both_in
      from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(1)[OF both_in(1-3, 5) \<open>u'' < u\<close>]
      obtain t'' v' where \<open>t'' < t' \<and> v' \<le> v \<and> t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u'', v'), A)\<close> by blast
      hence \<open>ev a # t'' < t \<and> ev b # v' \<le> ev b # v \<and>
             ev a # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', ev b # v'), A)\<close>
        by (simp add: both_in(2, 3, 4) \<open>u' = ev a # u''\<close>)
      thus ?thesis by blast
    next
      case inR_mvL
      from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(3)[OF inR_mvL(1, 2, 4) \<open>u'' < u\<close>]
      obtain t'' v' where \<open>t'' < t' \<and> v' \<le> ev b # v \<and> t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u'', v'), A)\<close> by blast
      hence \<open>ev a # t'' < t \<and> v' \<le> ev b # v \<and>
             ev a # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v'), A)\<close>
        by (cases v') (simp_all add: inR_mvL(1-3) \<open>u' = ev a # u''\<close>)
      thus ?thesis by blast
    next
      case inL_mvR
      from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(2)[OF inL_mvR(1, 2, 4) \<open>ev a # u'' < ev a # u\<close>]
      obtain t'' v' where \<open>t'' < t' \<and> v' \<le> v \<and> t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u'', v'), A)\<close> by blast
      hence \<open>ev b # t'' < t \<and> ev b # v' \<le> ev b # v \<and>
             ev b # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', ev b # v'), A)\<close>
        by (simp add: inL_mvR(1-3) \<open>u' = ev a # u''\<close>)
      thus ?thesis by blast
    next
      case notin_mvL
      from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(4)[OF notin_mvL(1, 2, 4) \<open>u'' < u\<close>]
      obtain t'' v' where \<open>t'' < t' \<and> v' \<le> ev b # v \<and> t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u'', v'), A)\<close> by blast
      hence \<open>ev a # t'' < t \<and> v' \<le> ev b # v \<and>
             ev a # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v'), A)\<close>
        by (cases v') (simp_all add: notin_mvL(1-3) \<open>u' = ev a # u''\<close>)
      thus ?thesis by blast
    next
      case notin_mvR
      from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(5)[OF notin_mvR(1, 2, 4) \<open>ev a # u'' < ev a # u\<close>]
      obtain t'' v' where \<open>t'' < t' \<and> v' \<le> v \<and> t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u'', v'), A)\<close> by blast
      hence \<open>ev b # t'' < t \<and> ev b # v' \<le> ev b # v \<and>
             ev b # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', ev b # v'), A)\<close>
        by (simp add: notin_mvR(1-3) \<open>u' = ev a # u''\<close>)
      thus ?thesis by blast
    qed
  qed
next
  case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick a u s v)
  from \<open>u' < ev a # u\<close> consider \<open>u' = []\<close> | u'' where \<open>u' = ev a # u''\<close> \<open>u'' < u\<close>
    by (metis Prefix_Order.prefix_Cons less_list_def)
  thus ?case
  proof cases
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems(1)
    show \<open>u' = [] \<Longrightarrow> ?case\<close> by (simp split: if_split_asm) force+
  next
    fix u'' assume \<open>u' = ev a # u''\<close> \<open>u'' < u\<close>
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems obtain t'
      where \<open>a \<notin> A\<close> \<open>t = ev a # t'\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, \<checkmark>(s) # v), A)\<close>
      by (auto split: if_split_asm)
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.hyps[OF \<open>a \<notin> A\<close> this(3) \<open>u'' < u\<close>]
    obtain t'' v' where \<open>t'' < t' \<and> v' \<le> \<checkmark>(s) # v \<and> t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u'', v'), A)\<close> by blast
    hence \<open>ev a # t'' < t \<and> v' \<le> \<checkmark>(s) # v \<and> ev a # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v'), A)\<close>
      by (cases v') (simp_all add: \<open>a \<notin> A\<close> \<open>u' = ev a # u''\<close> \<open>t = ev a # t'\<close>)
    thus ?case by blast
  qed
next
  case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev r u b v)
  from \<open>u' < \<checkmark>(r) # u\<close> consider \<open>u' = []\<close> | u'' where \<open>u' = \<checkmark>(r) # u''\<close> \<open>u'' < u\<close>
    by (metis Prefix_Order.prefix_Cons less_list_def)
  thus ?case
  proof cases
    from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(1)
    show \<open>u' = [] \<Longrightarrow> ?case\<close> by (simp split: if_split_asm) force+
  next
    fix u'' assume \<open>u' = \<checkmark>(r) # u''\<close> \<open>u'' < u\<close>
    hence \<open>\<checkmark>(r) # u'' < \<checkmark>(r) # u\<close> by simp
    from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems obtain t'
      where \<open>b \<notin> A\<close> \<open>t = ev b # t'\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((\<checkmark>(r) # u, v), A)\<close>
      by (auto split: if_split_asm)
    from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps[OF \<open>b \<notin> A\<close> this(3) \<open>\<checkmark>(r) # u'' < \<checkmark>(r) # u\<close>]
    obtain t'' v' where \<open>t'' < t' \<and> v' \<le> v \<and> t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((\<checkmark>(r) # u'', v'), A)\<close> by blast
    hence \<open>ev b # t'' < t \<and> ev b # v' \<le> ev b # v \<and>
           ev b # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', ev b # v'), A)\<close>
      by (simp add: \<open>b \<notin> A\<close> \<open>u' = \<checkmark>(r) # u''\<close> \<open>t = ev b # t'\<close>)
    thus ?case by blast
  qed
next
  case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick r u s v)
  from \<open>u' < \<checkmark>(r) # u\<close> consider \<open>u' = []\<close> | u'' where \<open>u' = \<checkmark>(r) # u''\<close> \<open>u'' < u\<close>
    by (metis Prefix_Order.prefix_Cons less_list_def)
  thus ?case
  proof cases
    from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems(1)
    show \<open>u' = [] \<Longrightarrow> ?case\<close> by (force split: option.split_asm)
  next
    fix u'' assume \<open>u' = \<checkmark>(r) # u''\<close> \<open>u'' < u\<close>
    from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems(1)
    obtain t' r_s
      where \<open>tick_join r s = \<lfloor>r_s\<rfloor>\<close> \<open>t = \<checkmark>(r_s) # t'\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A)\<close>
      by (auto split: option.split_asm)
    from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.hyps[OF this(1, 3) \<open>u'' < u\<close>]
    obtain t'' v' where \<open>t'' < t' \<and> v' \<le> v \<and> t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u'', v'), A)\<close> by blast
    hence \<open>\<checkmark>(r_s) # t'' < t \<and> \<checkmark>(s) # v' \<le> \<checkmark>(s) # v \<and> \<checkmark>(r_s) # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', \<checkmark>(s) # v'), A)\<close>
      by (simp add: \<open>tick_join r s = \<lfloor>r_s\<rfloor>\<close> \<open>u' = \<checkmark>(r) # u''\<close> \<open>t = \<checkmark>(r_s) # t'\<close>)
    thus ?case by blast
  qed
qed


corollary setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_less_prefixR :
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<Longrightarrow> v' < v \<Longrightarrow>
   \<exists>t' u'. t' < t \<and> u' \<le> u \<and> t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v'), A)\<close>
  using setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_less_prefixL setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym by blast



lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_le_prefixLR :
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<Longrightarrow> u' \<le> u \<Longrightarrow> v' \<le> v \<Longrightarrow>
   (\<exists>t' \<le> t. \<exists>v'' \<le> v'. t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v''), A)) \<or>
   (\<exists>t' \<le> t. \<exists>u'' \<le> u'. t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u'', v'), A))\<close>
proof (induct \<open>(tick_join, u, A, v)\<close> arbitrary: t u u' v v')
  case Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil thus ?case by simp
next
  case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil a u) thus ?case by simp fastforce
next
  case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil r u) thus ?case by simp
next
  case (Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev b v) thus ?case by simp fastforce
next
  case (Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick s v) thus ?case by simp
next
  case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev a u b v)
  show ?case
  proof (cases \<open>u' = [] \<or> v' = []\<close>)
    show \<open>u' = [] \<or> v' = [] \<Longrightarrow> ?case\<close> by force
  next
    assume \<open>\<not> (u' = [] \<or> v' = [])\<close>
    with ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(2, 3)
    obtain u'' v'' where \<open>u' = ev a # u''\<close> \<open>u'' \<le> u\<close> \<open>v' = ev b # v''\<close> \<open>v'' \<le> v\<close>
      by (meson Prefix_Order.prefix_Cons)
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(1)
    consider (both_in)   t' where \<open>a \<in> A\<close> \<open>b \<in> A\<close> \<open>a = b\<close> \<open>t = ev a # t'\<close>
      \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A)\<close>
    |      (inR_mvL)   t' where \<open>a \<notin> A\<close> \<open>b \<in> A\<close> \<open>t = ev a # t'\<close>
      \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, ev b # v), A)\<close>
    |      (inL_mvR)   t' where \<open>a \<in> A\<close> \<open>b \<notin> A\<close> \<open>t = ev b # t'\<close>
      \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u, v), A)\<close>
    |      (notin_mvL) t' where \<open>a \<notin> A\<close> \<open>b \<notin> A\<close> \<open>t = ev a # t'\<close>
      \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, ev b # v), A)\<close>
    |      (notin_mvR) t' where \<open>a \<notin> A\<close> \<open>b \<notin> A\<close> \<open>t = ev b # t'\<close>
      \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u, v), A)\<close>
      by (auto split: if_split_asm)
    thus ?case
    proof cases
      case both_in
      from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(1)[OF both_in(1-3, 5) \<open>u'' \<le> u\<close> \<open>v'' \<le> v\<close>]
      show ?thesis
      proof (elim disjE exE conjE)
        fix t'' v'''
        assume \<open>t'' \<le> t'\<close> \<open>v''' \<le> v''\<close> \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u'', v'''), A)\<close>
        hence \<open>ev b # t'' \<le> t \<and> ev b # v''' \<le> v' \<and>
             ev b # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', ev b # v'''), A)\<close>
          by (simp add: \<open>u' = ev a # u''\<close> \<open>v' = ev b # v''\<close> both_in(2-4))
        thus ?thesis by blast
      next
        fix t'' u'''
        assume \<open>t'' \<le> t'\<close> \<open>u''' \<le> u''\<close> \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u''', v''), A)\<close>
        hence \<open>ev a # t'' \<le> t \<and> ev a # u''' \<le> u' \<and>
             ev a # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u''', v'), A)\<close>
          by (simp add: \<open>u' = ev a # u''\<close> \<open>v' = ev b # v''\<close> both_in(2-4))
        thus ?thesis by blast
      qed
    next
      case inR_mvL
      from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(3)[OF inR_mvL(1, 2, 4) \<open>u'' \<le> u\<close> \<open>v' \<le> ev b # v\<close>]
      show ?thesis
      proof (elim disjE exE conjE)
        fix t'' v'''
        assume \<open>t'' \<le> t'\<close> \<open>v''' \<le> v'\<close> \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u'', v'''), A)\<close>
        hence \<open>ev a # t'' \<le> t \<and> v''' \<le> v' \<and>
             ev a # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v'''), A)\<close>
          by (cases v''') (simp_all add: \<open>u' = ev a # u''\<close> \<open>v' = ev b # v''\<close> inR_mvL(1, 3))
        thus ?thesis by blast
      next
        fix t'' u'''
        assume \<open>t'' \<le> t'\<close> \<open>u''' \<le> u''\<close> \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u''', v'), A)\<close>
        hence \<open>ev a # t'' \<le> t \<and> ev a # u''' \<le> u' \<and>
             ev a # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u''', v'), A)\<close>
          by (simp add: \<open>u' = ev a # u''\<close> \<open>v' = ev b # v''\<close> inR_mvL(1, 3))
        thus ?thesis by blast
      qed
    next
      case inL_mvR
      from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(2)[OF inL_mvR(1, 2, 4) \<open>u' \<le> ev a # u\<close> \<open>v'' \<le> v\<close>]
      show ?thesis
      proof (elim disjE exE conjE)
        fix t'' v'''
        assume \<open>t'' \<le> t'\<close> \<open>v''' \<le> v''\<close> \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v'''), A)\<close>
        hence \<open>ev b # t'' \<le> t \<and> ev b # v''' \<le> v' \<and>
             ev b # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', ev b # v'''), A)\<close>
          by (simp add: \<open>u' = ev a # u''\<close> \<open>v' = ev b # v''\<close> inL_mvR(2, 3))
        thus ?thesis by blast
      next
        fix t'' u'''
        assume \<open>t'' \<le> t'\<close> \<open>u''' \<le> u'\<close> \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u''', v''), A)\<close>
        hence \<open>ev b # t'' \<le> t \<and> u''' \<le> u' \<and>
             ev b # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u''', v'), A)\<close>
          by (cases u''') (simp_all add: \<open>u' = ev a # u''\<close> \<open>v' = ev b # v''\<close> inL_mvR(2, 3))
        thus ?thesis by blast
      qed
    next
      case notin_mvL
      from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(4)[OF notin_mvL(1, 2, 4) \<open>u'' \<le> u\<close> \<open>v' \<le> ev b # v\<close>]
      show ?thesis
      proof (elim disjE exE conjE)
        fix t'' v'''
        assume \<open>t'' \<le> t'\<close> \<open>v''' \<le> v'\<close> \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u'', v'''), A)\<close>
        hence \<open>ev a # t'' \<le> t \<and> v''' \<le> v' \<and>
             ev a # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v'''), A)\<close>
          by (cases v''') (simp_all add: \<open>u' = ev a # u''\<close> \<open>v' = ev b # v''\<close> notin_mvL(1, 3))
        thus ?thesis by blast
      next
        fix t'' u'''
        assume \<open>t'' \<le> t'\<close> \<open>u''' \<le> u''\<close> \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u''', v'), A)\<close>
        hence \<open>ev a # t'' \<le> t \<and> ev a # u''' \<le> u' \<and>
             ev a # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u''', v'), A)\<close>
          by (simp add: \<open>u' = ev a # u''\<close> \<open>v' = ev b # v''\<close> notin_mvL(1, 3))
        thus ?thesis by blast
      qed
    next
      case notin_mvR
      from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(5)[OF notin_mvR(1, 2, 4) \<open>u' \<le> ev a # u\<close> \<open>v'' \<le> v\<close>]
      show ?thesis
      proof (elim disjE exE conjE)
        fix t'' v'''
        assume \<open>t'' \<le> t'\<close> \<open>v''' \<le> v''\<close> \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v'''), A)\<close>
        hence \<open>ev b # t'' \<le> t \<and> ev b # v''' \<le> v' \<and>
             ev b # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', ev b # v'''), A)\<close>
          by (simp add: \<open>u' = ev a # u''\<close> \<open>v' = ev b # v''\<close> notin_mvR(2, 3))
        thus ?thesis by blast
      next
        fix t'' u'''
        assume \<open>t'' \<le> t'\<close> \<open>u''' \<le> u'\<close> \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u''', v''), A)\<close>
        hence \<open>ev b # t'' \<le> t \<and> u''' \<le> u' \<and>
             ev b # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u''', v'), A)\<close>
          by (cases u''') (simp_all add: \<open>u' = ev a # u''\<close> \<open>v' = ev b # v''\<close> notin_mvR(2, 3))
        thus ?thesis by blast
      qed
    qed
  qed
next
  case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick a u s v)
  show ?case
  proof (cases \<open>u' = [] \<or> v' = []\<close>)
    show \<open>u' = [] \<or> v' = [] \<Longrightarrow> ?case\<close> by force
  next
    assume \<open>\<not> (u' = [] \<or> v' = [])\<close>
    with ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems(2, 3)
    obtain u'' v'' where \<open>u' = ev a # u''\<close> \<open>u'' \<le> u\<close> \<open>v' = \<checkmark>(s) # v''\<close> \<open>v'' \<le> v\<close>
      by (meson Prefix_Order.prefix_Cons)
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems(1)
    obtain t' where \<open>a \<notin> A\<close> \<open>t = ev a # t'\<close>
      \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, \<checkmark>(s) # v), A)\<close>
      by (auto split: if_split_asm)
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.hyps[OF this(1, 3) \<open>u'' \<le> u\<close> \<open>v' \<le> \<checkmark>(s) # v\<close>]
    show ?case
    proof (elim disjE exE conjE)
      fix t'' v''' assume \<open>t'' \<le> t'\<close> \<open>v''' \<le> v'\<close> \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u'', v'''), A)\<close>
      hence \<open>ev a # t'' \<le> t \<and> v''' \<le> v' \<and> ev a # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v'''), A)\<close>
        by (cases v''') (simp_all add: \<open>a \<notin> A\<close> \<open>t = ev a # t'\<close> \<open>u' = ev a # u''\<close> \<open>v' = \<checkmark>(s) # v''\<close>)
      thus ?case by blast
    next
      fix t'' u''' assume \<open>t'' \<le> t'\<close> \<open>u''' \<le> u''\<close> \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u''', v'), A)\<close>
      hence \<open>ev a # t'' \<le> t \<and> ev a # u''' \<le> u' \<and> ev a # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u''', v'), A)\<close>
        by (simp add: \<open>a \<notin> A\<close> \<open>t = ev a # t'\<close> \<open>u' = ev a # u''\<close> \<open>v' = \<checkmark>(s) # v''\<close>)
      thus ?case by blast
    qed
  qed
next
  case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev r u b v)
  show ?case
  proof (cases \<open>u' = [] \<or> v' = []\<close>)
    show \<open>u' = [] \<or> v' = [] \<Longrightarrow> ?case\<close> by force
  next
    assume \<open>\<not> (u' = [] \<or> v' = [])\<close>
    with tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(2, 3)
    obtain u'' v'' where \<open>u' = \<checkmark>(r) # u''\<close> \<open>u'' \<le> u\<close> \<open>v' = ev b # v''\<close> \<open>v'' \<le> v\<close>
      by (meson Prefix_Order.prefix_Cons)
    from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(1)
    obtain t' where \<open>b \<notin> A\<close> \<open>t = ev b # t'\<close>
      \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((\<checkmark>(r) # u, v), A)\<close>
      by (auto split: if_split_asm)
    from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps[OF this(1, 3) \<open>u' \<le> \<checkmark>(r) # u\<close> \<open>v'' \<le> v\<close>]
    show ?case
    proof (elim disjE exE conjE)
      fix t'' v''' assume \<open>t'' \<le> t'\<close> \<open>v''' \<le> v''\<close> \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v'''), A)\<close>
      hence \<open>ev b # t'' \<le> t \<and> ev b # v''' \<le> v' \<and> ev b # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', ev b # v'''), A)\<close>
        by (simp add: \<open>b \<notin> A\<close> \<open>t = ev b # t'\<close> \<open>u' = \<checkmark>(r) # u''\<close> \<open>v' = ev b # v''\<close>)
      thus ?case by blast
    next
      fix t'' u''' assume \<open>t'' \<le> t'\<close> \<open>u''' \<le> u'\<close> \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u''', v''), A)\<close>
      hence \<open>ev b # t'' \<le> t \<and> u''' \<le> u' \<and> ev b # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u''', v'), A)\<close>
        by (cases u''') (simp_all add: \<open>b \<notin> A\<close> \<open>t = ev b # t'\<close> \<open>u' = \<checkmark>(r) # u''\<close> \<open>v' = ev b # v''\<close>)
      thus ?case by blast
    qed
  qed
next
  case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick r u s v)
  show ?case
  proof (cases \<open>u' = [] \<or> v' = []\<close>)
    show \<open>u' = [] \<or> v' = [] \<Longrightarrow> ?case\<close> by force
  next
    assume \<open>\<not> (u' = [] \<or> v' = [])\<close>
    with tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems(2, 3)
    obtain u'' v'' where \<open>u' = \<checkmark>(r) # u''\<close> \<open>u'' \<le> u\<close> \<open>v' = \<checkmark>(s) # v''\<close> \<open>v'' \<le> v\<close>
      by (meson Prefix_Order.prefix_Cons)
    from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems(1)
    obtain t' r_s where \<open>t = \<checkmark>(r_s) # t'\<close> \<open>tick_join r s = \<lfloor>r_s\<rfloor>\<close>
      \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A)\<close>
      by (auto split: option.split_asm)
    from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.hyps[OF this(2, 3) \<open>u'' \<le> u\<close> \<open>v'' \<le> v\<close>]
    show ?case
    proof (elim disjE exE conjE)
      fix t'' v'''
      assume \<open>t'' \<le> t'\<close> \<open>v''' \<le> v''\<close> \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u'', v'''), A)\<close>
      hence \<open>\<checkmark>(r_s) # t'' \<le> t \<and> \<checkmark>(s) # v''' \<le> v' \<and>
             \<checkmark>(r_s) # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', \<checkmark>(s) # v'''), A)\<close>
        by (simp add: \<open>tick_join r s = \<lfloor>r_s\<rfloor>\<close> \<open>t = \<checkmark>(r_s) # t'\<close>
            \<open>u' = \<checkmark>(r) # u''\<close> \<open>v' = \<checkmark>(s) # v''\<close>)
      thus ?case by blast
    next
      fix t'' u'''
      assume \<open>t'' \<le> t'\<close> \<open>u''' \<le> u''\<close> \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u''', v''), A)\<close>
      hence \<open>\<checkmark>(r_s) # t'' \<le> t \<and> \<checkmark>(r) # u''' \<le> u' \<and>
             \<checkmark>(r_s) # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((\<checkmark>(r) # u''', v'), A)\<close> 
        by (simp add: \<open>tick_join r s = \<lfloor>r_s\<rfloor>\<close> \<open>t = \<checkmark>(r_s) # t'\<close>
            \<open>u' = \<checkmark>(r) # u''\<close> \<open>v' = \<checkmark>(s) # v''\<close>)
      thus ?case by blast
    qed
  qed
qed



subsection \<open>Hiding Events\<close>

lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_trace_hide :
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), S) \<Longrightarrow>
   trace_hide t (ev ` A) setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub>
   ((trace_hide u (ev ` A), trace_hide v (ev ` A)), S)\<close>
proof (induct \<open>(tick_join, u, S, v)\<close> arbitrary: t u v)
  case Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil
  thus ?case by simp
next
  case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil a u)
  from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil.prems obtain t' where \<open>a \<notin> S\<close> \<open>t = ev a # t'\<close>
    \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, []), S)\<close> by (auto split: if_split_asm)
  from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil.hyps[OF this(1, 3)]
  show ?case by (simp add: image_iff[of \<open>ev _\<close>] \<open>a \<notin> S\<close> \<open>t = ev a # t'\<close>)
next
  case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil r u)
  from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil have False by simp
  thus ?case ..
next
  case (Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev b v)
  from Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems obtain t' where \<open>b \<notin> S\<close> \<open>t = ev b # t'\<close>
    \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> (([], v), S)\<close> by (auto split: if_split_asm)
  from Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps[OF this(1, 3)]
  show ?case by (simp add: image_iff[of \<open>ev _\<close>] \<open>b \<notin> S\<close> \<open>t = ev b # t'\<close>)
next
  case (Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick s v)
  from Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems have False by simp
  thus ?case ..
next
  case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev a u b v)
  from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems
  consider (both_in)   t' where \<open>a \<in> S\<close> \<open>b \<in> S\<close> \<open>a = b\<close> \<open>t = ev a # t'\<close>
    \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), S)\<close>
  |        (inR_mvL)   t' where \<open>a \<notin> S\<close> \<open>b \<in> S\<close> \<open>t = ev a # t'\<close>
    \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, ev b # v), S)\<close>
  |        (inL_mvR)   t' where \<open>a \<in> S\<close> \<open>b \<notin> S\<close> \<open>t = ev b # t'\<close>
    \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u, v), S)\<close>
  |        (notin_mvL) t' where \<open>a \<notin> S\<close> \<open>b \<notin> S\<close> \<open>t = ev a # t'\<close>
    \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, ev b # v), S)\<close>
  |        (notin_mvR) t' where \<open>a \<notin> S\<close> \<open>b \<notin> S\<close> \<open>t = ev b # t'\<close>
    \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u, v), S)\<close>
    by (auto split: if_split_asm)
  thus ?case
  proof cases
    case both_in
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(1)[OF both_in(1-3, 5)]
    show ?thesis by (simp add: both_in(2-5) image_iff[of \<open>ev _\<close>])
  next
    case inR_mvL
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(3)[OF inR_mvL(1, 2, 4)]
    show ?thesis by (cases \<open>trace_hide v (ev ` A)\<close>)
        (auto simp add: inR_mvL(1-3) setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps
          split: if_split_asm event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
  next
    case inL_mvR
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(2)[OF inL_mvR(1, 2, 4)]
    show ?thesis by (cases \<open>trace_hide u (ev ` A)\<close>)
        (auto simp add: inL_mvR(1-3) setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps
          split: if_split_asm event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
  next
    case notin_mvL
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(4)[OF notin_mvL(1, 2, 4)]
    show ?thesis by (cases \<open>trace_hide v (ev ` A)\<close>)
        (auto simp add: notin_mvL(1-3) setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps
          split: if_split_asm event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
  next
    case notin_mvR
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(5)[OF notin_mvR(1, 2, 4)]
    show ?thesis by (cases \<open>trace_hide u (ev ` A)\<close>)
        (auto simp add: notin_mvR(1-3) setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps
          split: if_split_asm event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
  qed
next
  case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick a u s v)
  from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems obtain t' where \<open>a \<notin> S\<close> \<open>t = ev a # t'\<close>
    \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, \<checkmark>(s) # v), S)\<close> by (auto split: if_split_asm)
  from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.hyps[OF this(1, 3)]
  show ?case by (simp add: image_iff[of \<open>ev _\<close>] image_iff[of \<open>\<checkmark>(_)\<close>] \<open>a \<notin> S\<close> \<open>t = ev a # t'\<close>)
next
  case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev r u b v)
  from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems obtain t' where \<open>b \<notin> S\<close> \<open>t = ev b # t'\<close>
    \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((\<checkmark>(r) # u, v), S)\<close> by (auto split: if_split_asm)
  from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps[OF this(1, 3)]
  show ?case by (simp add: image_iff[of \<open>ev _\<close>] image_iff[of \<open>\<checkmark>(_)\<close>] \<open>b \<notin> S\<close> \<open>t = ev b # t'\<close>)
next
  case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick r u s v)
  from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems
  obtain r_s t' where \<open>tick_join r s = \<lfloor>r_s\<rfloor>\<close> \<open>t = \<checkmark>(r_s) # t'\<close>
    \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), S)\<close> by (auto split: option.split_asm)
  from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.hyps[OF this(1, 3)]
  show ?case by (simp add: image_iff[of \<open>\<checkmark>(_)\<close>] \<open>tick_join r s = \<lfloor>r_s\<rfloor>\<close> \<open>t = \<checkmark>(r_s) # t'\<close>)
qed


lemma trace_hide_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>trace_hide (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t) S =
   map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (trace_hide t (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` S))\<close>
  by (induct t) simp_all


lemma tickFree_trace_hide_map_ev_comp_of_ev :
  \<open>tF t \<Longrightarrow> trace_hide (map (ev \<circ> of_ev) t) (ev ` A) =
            map (ev \<circ> of_ev) (trace_hide t (ev ` A))\<close>
  by (induct t) (auto simp add: image_iff)


lemma tickFree_disjoint_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendL :
  \<open>tF u1 \<Longrightarrow> {a. ev a \<in> set u1} \<inter> A = {} \<Longrightarrow> t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u2, v), A)
   \<Longrightarrow> map (ev \<circ> of_ev) u1 @ t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1 @ u2, v), A)\<close>
proof (induct u1)
  case Nil
  from Nil.prems(3) show ?case by simp
next
  case (Cons e u1)
  from Cons.prems(1, 2) obtain a
    where \<open>e = ev a\<close> \<open>a \<notin> A\<close> \<open>tF u1\<close> \<open>{a. ev a \<in> set u1} \<inter> A = {} \<close>
    by (auto simp add: disjoint_iff is_ev_def)
  from Cons.hyps[OF this(3, 4) Cons.prems(3)]
  have \<open>map (ev \<circ> of_ev) u1 @ t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1 @ u2, v), A)\<close> .
  with \<open>e = ev a\<close> \<open>a \<notin> A\<close>
  show ?case by (cases v)
      (auto simp add: setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps comp_def split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
qed

corollary tickFree_disjoint_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendR :
  \<open>\<lbrakk>tF v1; {a. ev a \<in> set v1} \<inter> A = {}; t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v2), A)\<rbrakk>
   \<Longrightarrow> map (ev \<circ> of_ev) v1 @ t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v1 @ v2), A)\<close>
  by (metis setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym tickFree_disjoint_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendL)


lemma tickFree_disjoint_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_append_tailL :
  \<open>t @ map (ev \<circ> of_ev) u2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1 @ u2, v), A)\<close>
  if \<open>tF u2\<close> \<open>{a. ev a \<in> set u2} \<inter> A = {}\<close> \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1, v), A)\<close>
proof -
  have \<open>t @ map (ev \<circ> of_ev) u2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1 @ u2, v), A) \<longleftrightarrow>
        map (ev \<circ> of_ev) (rev u2) @ rev t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((rev u2 @ rev u1, rev v), A)\<close>
    by (subst rev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_rev_rev_iff[symmetric])
      (simp add: rev_map)
  also have \<dots>
  proof (rule tickFree_disjoint_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendL)
    show \<open>tF (rev u2)\<close> by (simp add: that(1))
  next
    show \<open>{a. ev a \<in> set (rev u2)} \<inter> A = {}\<close> by (simp add: that(2))
  next
    show \<open>rev t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((rev u1, rev v), A)\<close>
      by (simp add: rev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_rev_rev_iff that(3))
  qed
  finally show ?thesis .
qed


corollary tickFree_disjoint_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_append_tailR :
  \<open>\<lbrakk>tF v2; {a. ev a \<in> set v2} \<inter> A = {}; t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v1), A)\<rbrakk>
   \<Longrightarrow> t @ map (ev \<circ> of_ev) v2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v1 @ v2), A)\<close>
  by (metis setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym tickFree_disjoint_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_append_tailL)


lemma disjoint_trace_hide_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub>
   ((trace_hide u (ev ` A), trace_hide v (ev ` A)), S) \<Longrightarrow>
   \<exists>t'. t = trace_hide t' (ev ` A) \<and>
   t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), S)\<close> if \<open>A \<inter> S = {}\<close>
  for t :: \<open>('a, 't) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and u :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and v :: \<open>('a, 's) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof -
  let ?th = trace_hide and ?A = \<open>ev ` A\<close>
  show \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub>
        ((?th u ?A, ?th v ?A), S) \<Longrightarrow> \<exists>t'. t = ?th t' ?A \<and> t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), S)\<close>
  proof (induct \<open>(tick_join, u, S, v)\<close> arbitrary: t u v)
    case Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil
    then show ?case by simp
  next
    case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil a u)
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil.prems
    consider t' where \<open>a \<notin> S\<close> \<open>a \<notin> A\<close> \<open>t = ev a # t'\<close>
      \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?th u ?A, ?th [] ?A), S)\<close>
    | \<open>a \<in> A\<close> \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?th u ?A, ?th [] ?A), S)\<close>
      by (auto split: if_split_asm)
    thus ?case
    proof cases
      fix t' assume \<open>a \<notin> S\<close> \<open>a \<notin> A\<close> \<open>t = ev a # t'\<close>
        \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?th u ?A, ?th [] ?A), S)\<close>
      from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil.hyps[OF this(1, 4)] obtain t''
        where \<open>t' = ?th t'' ?A \<and> t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, []), S)\<close> ..
      hence \<open>t = ?th (ev a # t'') ?A \<and> ev a # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u, []), S)\<close>
        by (simp add: \<open>a \<notin> A\<close> \<open>a \<notin> S\<close> \<open>t = ev a # t'\<close> image_iff[of \<open>ev _\<close>])
      thus ?case ..
    next
      assume \<open>a \<in> A\<close>
      with \<open>A \<inter> S = {}\<close> have \<open>a \<notin> S\<close> by blast
      moreover assume \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?th u ?A, ?th [] ?A), S)\<close>
      ultimately obtain t' where \<open>t = ?th t' ?A\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, []), S)\<close>
        using ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil.hyps by blast
      hence \<open>t = ?th (ev a # t') ?A \<and> ev a # t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u, []), S)\<close>
        by (simp add: \<open>a \<in> A\<close> \<open>a \<notin> S\<close>)
      thus ?case ..
    qed
  next
    case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil r u)
    from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil.prems have False by (simp add: image_iff[of \<open>\<checkmark>(_)\<close>])
    thus ?case ..
  next
    case (Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev b v)
    from Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems
    consider t' where \<open>b \<notin> S\<close> \<open>b \<notin> A\<close> \<open>t = ev b # t'\<close>
      \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?th [] ?A, ?th v ?A), S)\<close>
    | \<open>b \<in> A\<close> \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?th [] ?A, ?th v ?A), S)\<close>
      by (auto split: if_split_asm)
    thus ?case
    proof cases
      fix t' assume \<open>b \<notin> S\<close> \<open>b \<notin> A\<close> \<open>t = ev b # t'\<close>
        \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?th [] ?A, ?th v ?A), S)\<close>
      from Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps[OF this(1, 4)] obtain t''
        where \<open>t' = ?th t'' ?A \<and> t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> (([], v), S)\<close> ..
      hence \<open>t = ?th (ev b # t'') ?A \<and> ev b # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> (([], ev b # v), S)\<close>
        by (simp add: \<open>b \<notin> A\<close> \<open>b \<notin> S\<close> \<open>t = ev b # t'\<close> image_iff[of \<open>ev _\<close>])
      thus ?case ..
    next
      assume \<open>b \<in> A\<close>
      with \<open>A \<inter> S = {}\<close> have \<open>b \<notin> S\<close> by blast
      moreover assume \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?th [] ?A, ?th v ?A), S)\<close>
      ultimately obtain t' where \<open>t = ?th t' ?A\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> (([], v), S)\<close>
        using Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps by blast
      hence \<open>t = ?th (ev b # t') ?A \<and> ev b # t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> (([], ev b # v), S)\<close>
        by (simp add: \<open>b \<in> A\<close> \<open>b \<notin> S\<close>)
      thus ?case ..
    qed
  next
    case (Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick s v)
    from Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems have False by (simp add: image_iff[of \<open>\<checkmark>(_)\<close>])
    thus ?case ..
  next
    case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev a u b v)
    show ?case
    proof (cases \<open>a \<in> A\<close>; cases \<open>b \<in> A\<close>)
      assume \<open>a \<in> A\<close> \<open>b \<in> A\<close>
      with ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems
      have * : \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?th (ev a # u) ?A, ?th v ?A), S)\<close>
        \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?th u ?A, ?th (ev b # v) ?A), S)\<close> by simp_all
      from \<open>A \<inter> S = {}\<close> \<open>a \<in> A\<close> \<open>b \<in> A\<close> have \<open>a \<notin> S\<close> \<open>b \<notin> S\<close> by blast+
      from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(4)[OF this "*"(2)]
        ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(5)[OF this "*"(1)]
      obtain t' where \<open>t = ?th t' ?A\<close>
        \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u, v), S) \<or>
         t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, ev b # v), S)\<close> by blast
      hence \<open>t = ?th (ev b # t') ?A \<and> ev b # t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u, ev b # v), S) \<or>
             t = ?th (ev a # t') ?A \<and> ev a # t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u, ev b # v), S)\<close>
        by (auto simp add: \<open>a \<in> A\<close> \<open>b \<in> A\<close> \<open>a \<notin> S\<close> \<open>b \<notin> S\<close>)
      thus ?case by blast
    next
      assume \<open>a \<in> A\<close> \<open>b \<notin> A\<close>
      with ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems
      have * : \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?th u ?A, ?th (ev b # v) ?A), S)\<close> by simp
      from \<open>A \<inter> S = {}\<close> \<open>a \<in> A\<close> have \<open>a \<notin> S\<close> by blast
      from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(3)[OF \<open>a \<notin> S\<close> _ "*"(1)]
        ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(4)[OF \<open>a \<notin> S\<close> _ "*"] obtain t'
        where \<open>t = ?th t' ?A\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, ev b # v), S)\<close> by blast
      hence \<open>t = ?th (ev a # t') ?A \<and>
               ev a # t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u, ev b # v), S)\<close>
        by (simp add: \<open>a \<in> A\<close> \<open>a \<notin> S\<close>)
      thus ?case ..
    next
      assume \<open>a \<notin> A\<close> \<open>b \<in> A\<close>
      with ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems
      have * : \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?th (ev a # u) ?A, ?th v ?A), S)\<close> by simp
      from \<open>A \<inter> S = {}\<close> \<open>b \<in> A\<close> have \<open>b \<notin> S\<close> by blast
      from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(2)[OF _ \<open>b \<notin> S\<close> "*"]
        ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(5)[OF _ \<open>b \<notin> S\<close> "*"] obtain t'
        where \<open>t = ?th t' ?A\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u, v), S)\<close> by blast
      hence \<open>t = ?th (ev b # t') ?A \<and>
             ev b # t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u, ev b # v), S)\<close>
        by (simp add: \<open>b \<in> A\<close> \<open>b \<notin> S\<close>)
      thus ?case ..
    next
      assume \<open>a \<notin> A\<close> \<open>b \<notin> A\<close>
      hence \<open>?th (ev a # u) ?A = ev a # ?th u ?A\<close>
        \<open>?th (ev b # v) ?A = ev b # ?th v ?A\<close> by auto
      from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems[unfolded this]
      have \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # ?th u ?A, ev b # ?th v ?A), S)\<close> .
      then consider (mv_both) t' where \<open>a \<in> S\<close> \<open>b \<in> S\<close> \<open>a = b\<close> \<open>t = ev a # t'\<close>
        \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?th u ?A, ?th v ?A), S)\<close>
      | (mvL) t' where \<open>a \<notin> S\<close> \<open>t = ev a # t'\<close>
        \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?th u ?A, ev b # ?th v ?A), S)\<close>
      | (mvR) t' where \<open>b \<notin> S\<close> \<open>t = ev b # t'\<close>
        \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # ?th u ?A, ?th v ?A), S)\<close>
        by (auto split: if_split_asm)
      thus ?case
      proof cases
        case mv_both
        from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(1)[OF mv_both(1-3, 5)] obtain t''
          where \<open>t' = ?th t'' ?A \<and> t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), S)\<close> ..
        hence \<open>t = ?th (ev b # t'') ?A \<and> ev b # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u, ev b # v), S)\<close>
          by (simp add: mv_both(2-4) \<open>b \<notin> A\<close> image_iff[of \<open>ev _\<close>] )
        thus ?thesis ..
      next
        case mvL
        from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(3, 4)
          [OF mvL(1) _ mvL(3)[folded \<open>?th (ev b # v) ?A = ev b # ?th v ?A\<close>]]
        obtain t'' where \<open>t' = ?th t'' ?A\<close>
          \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, ev b # v), S)\<close> by blast
        hence \<open>t = ?th (ev a # t'') ?A \<and>
               ev a # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u, ev b # v), S)\<close>
          by (simp add: mvL(1, 2) \<open>a \<notin> A\<close> image_iff[of \<open>ev _\<close>]) 
        thus ?thesis ..
      next
        case mvR
        from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(2, 5)
          [OF _ mvR(1) mvR(3)[folded \<open>?th (ev a # u) ?A = ev a # ?th u ?A\<close>]]
        obtain t'' where \<open>t' = ?th t'' ?A\<close>
          \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u, v), S)\<close> by blast
        hence \<open>t = ?th (ev b # t'') ?A \<and>
               ev b # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u, ev b # v), S)\<close>
          by (simp add: mvR(1, 2) \<open>b \<notin> A\<close> image_iff[of \<open>ev _\<close>]) 
        thus ?thesis ..
      qed
    qed
  next
    case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick a u s v)
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems
    consider t' where \<open>a \<notin> S\<close> \<open>a \<notin> A\<close> \<open>t = ev a # t'\<close>
      \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?th u ?A, ?th (\<checkmark>(s) # v) ?A), S)\<close>
    | \<open>a \<in> A\<close> \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?th u ?A, ?th (\<checkmark>(s) # v) ?A), S)\<close>
      by (auto split: if_split_asm)
    thus ?case
    proof cases
      fix t' assume \<open>a \<notin> S\<close> \<open>a \<notin> A\<close> \<open>t = ev a # t'\<close>
        \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?th u ?A, ?th (\<checkmark>(s) # v) ?A), S)\<close>
      from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.hyps[OF this(1, 4)] obtain t''
        where \<open>t' = ?th t'' ?A\<close> \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, \<checkmark>(s) # v), S)\<close> by blast
      hence \<open>t = ?th (ev a # t'') ?A \<and>
             ev a # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u, \<checkmark>(s) # v), S)\<close>
        by (simp add: \<open>a \<notin> A\<close> \<open>a \<notin> S\<close> \<open>t = ev a # t'\<close> image_iff[of \<open>ev _\<close>])
      thus ?case ..
    next
      assume \<open>a \<in> A\<close>
      with \<open>A \<inter> S = {}\<close> have \<open>a \<notin> S\<close> by blast
      moreover assume \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?th u ?A, ?th (\<checkmark>(s) # v) ?A), S)\<close>
      ultimately obtain t' where \<open>t = ?th t' ?A\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, \<checkmark>(s) # v), S)\<close>
        using ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.hyps by blast
      hence \<open>t = ?th (ev a # t') ?A \<and> ev a # t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u, \<checkmark>(s) # v), S)\<close>
        by (simp add: \<open>a \<in> A\<close> \<open>a \<notin> S\<close>)
      thus ?case ..
    qed
  next
    case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev r u b v)
    from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems
    consider t' where \<open>b \<notin> S\<close> \<open>b \<notin> A\<close> \<open>t = ev b # t'\<close>
      \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?th (\<checkmark>(r) # u) ?A, ?th v ?A), S)\<close>
    | \<open>b \<in> A\<close> \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?th (\<checkmark>(r) # u) ?A, ?th v ?A), S)\<close>
      by (auto split: if_split_asm)
    thus ?case
    proof cases
      fix t' assume \<open>b \<notin> S\<close> \<open>b \<notin> A\<close> \<open>t = ev b # t'\<close>
        \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?th (\<checkmark>(r) # u) ?A, ?th v ?A), S)\<close>
      from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps[OF this(1, 4)] obtain t''
        where \<open>t' = ?th t'' ?A\<close> \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((\<checkmark>(r) # u, v), S)\<close> by blast
      hence \<open>t = ?th (ev b # t'') ?A \<and>
             ev b # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((\<checkmark>(r) # u, ev b # v), S)\<close>
        by (simp add: \<open>b \<notin> A\<close> \<open>b \<notin> S\<close> \<open>t = ev b # t'\<close> image_iff[of \<open>ev _\<close>])
      thus ?case ..
    next
      assume \<open>b \<in> A\<close>
      with \<open>A \<inter> S = {}\<close> have \<open>b \<notin> S\<close> by blast
      moreover assume \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?th (\<checkmark>(r) # u) ?A, ?th v ?A), S)\<close>
      ultimately obtain t' where \<open>t = ?th t' ?A\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((\<checkmark>(r) # u, v), S)\<close>
        using tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps by blast
      hence \<open>t = ?th (ev b # t') ?A \<and> ev b # t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((\<checkmark>(r) # u, ev b # v), S)\<close>
        by (simp add: \<open>b \<in> A\<close> \<open>b \<notin> S\<close>)
      thus ?case ..
    qed
  next
    case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick r u s v)
    from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems obtain r_s t'
      where \<open>tick_join r s = \<lfloor>r_s\<rfloor>\<close> \<open>t = \<checkmark>(r_s) # t'\<close>
        \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?th u ?A, ?th v ?A), S)\<close>
      by (auto split: if_split_asm option.split_asm)
    from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.hyps[OF this(1, 3)] obtain t''
      where \<open>t' = ?th t'' ?A\<close> \<open>t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), S)\<close> by blast
    hence \<open>t = ?th (\<checkmark>(r_s) # t'') ?A \<and>
           \<checkmark>(r_s) # t'' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((\<checkmark>(r) # u, \<checkmark>(s) # v), S)\<close>
      by (simp add: \<open>tick_join r s = \<lfloor>r_s\<rfloor>\<close> \<open>t = \<checkmark>(r_s) # t'\<close> image_iff[of \<open>\<checkmark>(_)\<close>])
    thus ?case ..
  qed
qed



lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inj_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff_weak :
  \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f id) t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub>
   ((map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f id) u, map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f id) v), f ` A) \<longleftrightarrow>
   t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A)\<close> if \<open>inj f\<close>
  by (induct \<open>(tick_join, u, A, v)\<close> arbitrary: t u v)
    (auto simp add: image_iff map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_ev_iff map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_tick_iff
      dest!: injD[OF \<open>inj f\<close>] split: option.split_asm)


lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inj_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff_strong :
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub>
   ((map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f id) u, map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f id) v), f ` A) \<longleftrightarrow>
    (\<exists>t'. t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f id) t' \<and>
    t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A))\<close> if \<open>inj f\<close>
  \<comment> \<open>We could probably prove a stronger version with
     \<^term>\<open>inj_on f (A \<union> {a. ev a \<in> set u \<or> ev a \<in> set v})\<close> instead of \<^term>\<open>inj f\<close>.\<close>
proof -
  let ?map = \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f id)\<close>
  have \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?map u, ?map v), f ` A) \<Longrightarrow> \<exists>t'. t = ?map t'\<close>
  proof (induct \<open>(tick_join, u, A, v)\<close> arbitrary: t u v)
    case Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil
    thus ?case by simp
  next
    case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil a u)
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil.prems obtain t'
      where \<open>a \<notin> A\<close> \<open>t = ev (f a) # t'\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?map u, ?map []), f ` A)\<close>
      by (auto split: if_split_asm)
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil.hyps[OF this(1, 3)]
    obtain t'' where \<open>t' = ?map t''\<close> ..
    hence \<open>t = ?map (ev a # t'')\<close> by (simp add: \<open>t = ev (f a) # t'\<close>)
    thus ?case ..
  next
    case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil r u)
    from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil.prems have False by simp
    thus ?case ..
  next
    case (Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev b v)
    from Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems obtain t'
      where \<open>b \<notin> A\<close> \<open>t = ev (f b) # t'\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?map [], ?map v), f ` A)\<close>
      by (auto split: if_split_asm)
    from Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps[OF this(1, 3)]
    obtain t'' where \<open>t' = ?map t''\<close> ..
    hence \<open>t = ?map (ev b # t'')\<close> by (simp add: \<open>t = ev (f b) # t'\<close>)
    thus ?case ..
  next
    case (Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick s v)
    from Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems have False by simp
    thus ?case ..
  next
    case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev a u b v)
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems
    consider (mv_left) t' where \<open>a \<notin> A\<close> \<open>t = ev (f a) # t'\<close>
      \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?map u, ?map (ev b # v)), f ` A)\<close>
    | (mv_right) t' where \<open>b \<notin> A\<close> \<open>t = ev (f b) # t'\<close>
      \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?map (ev a # u), ?map v), f ` A)\<close>
    | (mv_both) t' where \<open>a \<in> A\<close> \<open>b \<in> A\<close> \<open>a = b\<close> \<open>t = ev (f b) # t'\<close>
      \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?map u, ?map v), f ` A)\<close>
      by (auto simp add: image_iff split: if_split_asm dest!: injD[OF \<open>inj f\<close>])
    thus ?case
    proof cases
      case mv_left
      from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(3, 4)[OF mv_left(1) _ mv_left(3)]
      obtain t'' where \<open>t' = ?map t''\<close> by blast
      hence \<open>t = ?map (ev a # t'')\<close> by (simp add: mv_left(2))
      thus ?thesis ..
    next
      case mv_right
      from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(2, 5)[OF _ mv_right(1, 3)]
      obtain t'' where \<open>t' = ?map t''\<close> by blast
      hence \<open>t = ?map (ev b # t'')\<close> by (simp add: mv_right(2))
      thus ?thesis ..
    next
      case mv_both
      from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(1)[OF mv_both(1-3, 5)]
      obtain t'' where \<open>t' = ?map t''\<close> ..
      hence \<open>t = ?map (ev b # t'')\<close> by (simp add: mv_both(4))
      thus ?thesis ..
    qed
  next
    case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick a u s v)
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems obtain t'
      where \<open>a \<notin> A\<close> \<open>t = ev (f a) # t'\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?map u, ?map (\<checkmark>(s) # v)), f ` A)\<close>
      by (auto split: if_split_asm)
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.hyps[OF this(1, 3)]
    obtain t'' where \<open>t' = ?map t''\<close> ..
    hence \<open>t = ?map (ev a # t'')\<close> by (simp add: \<open>t = ev (f a) # t'\<close>)
    thus ?case ..
  next
    case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev r u b v)
    from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems obtain t'
      where \<open>b \<notin> A\<close> \<open>t = ev (f b) # t'\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?map (\<checkmark>(r) # u), ?map v), f ` A)\<close>
      by (auto split: if_split_asm)
    from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps[OF this(1, 3)]
    obtain t'' where \<open>t' = ?map t''\<close> ..
    hence \<open>t = ?map (ev b # t'')\<close> by (simp add: \<open>t = ev (f b) # t'\<close>)
    thus ?case ..
  next
    case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick r u s v)
    from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems obtain r_s t'
      where \<open>tick_join r s = \<lfloor>r_s\<rfloor>\<close> \<open>t = \<checkmark>(r_s) # t'\<close>
        \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((?map u, ?map v), f ` A)\<close>
      by (auto split: option.split_asm)
    from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.hyps[OF this(1, 3)]
    obtain t'' where \<open>t' = ?map t''\<close> ..
    hence \<open>t = ?map (\<checkmark>(r_s) # t'')\<close> by (simp add: \<open>t = \<checkmark>(r_s) # t'\<close>)
    thus ?case ..
  qed
  with setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inj_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff_weak[OF \<open>inj f\<close>]
  show ?thesis by blast
qed




lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_append_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>t1 @ t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1 @ u2, v1 @ v2), A)\<close>
  if \<open>t1 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1, v1), A)\<close>
    and \<open>t2 setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u2, v2), A)\<close>
  using that(1) proof (induct \<open>(tick_join, u1, A, v1)\<close> arbitrary: t1 u1 v1)
  case Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil
  from Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil.prems(1) have \<open>t1 = []\<close> by simp
  with that(2) show ?case by simp
next
  case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil a u1)
  from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil.prems(1) obtain t1' where \<open>a \<notin> A\<close> \<open>t1 = ev a # t1'\<close>
    \<open>t1' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1, []), A)\<close> by (auto split: if_split_asm)
  from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil.hyps[OF this(1, 3)]
  show ?case
    by (cases v2)
      (auto simp add: \<open>a \<notin> A\<close> \<open>t1 = ev a # t1'\<close> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps
        split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
next
  case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil r u1)
  from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil.prems(1) have False by simp
  thus ?case ..
next
  case (Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev b v1)
  from Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(1) obtain t1' where \<open>b \<notin> A\<close> \<open>t1 = ev b # t1'\<close>
    \<open>t1' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> (([], v1), A)\<close> by (auto split: if_split_asm)
  from Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps[OF this(1, 3)]
  show ?case
    by (cases u2)
      (auto simp add: \<open>b \<notin> A\<close> \<open>t1 = ev b # t1'\<close> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps
        split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
next
  case (Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick s v1)
  from Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems(1) have False by simp
  thus ?case ..
next
  case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev a u1 b v1)
  from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems
  consider (mv_both) t' where \<open>a \<in> A\<close> \<open>b \<in> A\<close> \<open>a = b\<close> \<open>t1 = ev a # t'\<close>
    \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1, v1), A)\<close>
  | (mvL) t' where \<open>a \<notin> A\<close> \<open>t1 = ev a # t'\<close>
    \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1, ev b # v1), A)\<close>
  | (mvR) t' where \<open>b \<notin> A\<close> \<open>t1 = ev b # t'\<close>
    \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev a # u1, v1), A)\<close>
    by (auto split: if_split_asm)
  thus ?case
  proof cases
    case mv_both
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(1)[OF mv_both(1-3, 5)]
    show ?thesis by (simp add: mv_both(2-4))
  next
    case mvL
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(3, 4)[OF mvL(1) _ mvL(3)]
    show ?thesis by (simp add: mvL(1, 2))
  next
    case mvR
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(2, 5)[OF _ mvR(1, 3)]
    show ?thesis by (simp add: mvR(1, 2))
  qed
next
  case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick a u1 s v1)
  from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems(1)
  obtain t1' where \<open>a \<notin> A\<close> \<open>t1 = ev a # t1'\<close>
    \<open>t1' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1, \<checkmark>(s) # v1), A)\<close> by (auto split: if_split_asm)
  from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.hyps[OF this(1, 3)]
  show ?case
    by (cases v2)
      (auto simp add: \<open>a \<notin> A\<close> \<open>t1 = ev a # t1'\<close> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps
        split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
next
  case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev r u1 b v1)
  from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(1) obtain t1' where \<open>b \<notin> A\<close> \<open>t1 = ev b # t1'\<close>
    \<open>t1' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((\<checkmark>(r) # u1, v1), A)\<close> by (auto split: if_split_asm)
  from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps[OF this(1, 3)]
  show ?case
    by (cases u2)
      (auto simp add: \<open>b \<notin> A\<close> \<open>t1 = ev b # t1'\<close> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps
        split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
next
  case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick r u1 s v1)
  from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems(1) obtain r_s t1'
    where \<open>tick_join r s = \<lfloor>r_s\<rfloor>\<close> \<open>t1 = \<checkmark>(r_s) # t1'\<close>
      \<open>t1' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u1, v1), A)\<close>
    by (auto split: option.split_asm)
  from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.hyps[OF this(1, 3)]
  show ?case by (simp add: \<open>tick_join r s = \<lfloor>r_s\<rfloor>\<close> \<open>t1 = \<checkmark>(r_s) # t1'\<close>)
qed




lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_set_subsetL :
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<Longrightarrow>
   {a. ev a \<in> set (drop n u)} \<subseteq> {a. ev a \<in> set (drop n t)}\<close>
proof (induct t arbitrary: n u v)
  case Nil
  thus ?case by (auto dest: Nil_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
next
  case (Cons e t)
  from Cons.prems consider (mv_left) a u' where \<open>a \<notin> A\<close> \<open>e = ev a\<close> \<open>u = ev a # u'\<close>
    \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v), A)\<close>
  | (mv_right) a v' where \<open>a \<notin> A\<close> \<open>e = ev a\<close> \<open>v = ev a # v'\<close>
    \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v'), A)\<close>
  | (mv_both_ev) a u' v' where \<open>a \<in> A\<close> \<open>e = ev a\<close> \<open>u = ev a # u'\<close> \<open>v = ev a # v'\<close>
    \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v'), A)\<close>
  | (mv_both_tick) r s r_s u' v' where \<open>tick_join r s = \<lfloor>r_s\<rfloor>\<close> \<open>e = \<checkmark>(r_s)\<close>
    \<open>u = \<checkmark>(r) # u'\<close> \<open>v = \<checkmark>(s) # v'\<close> \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u', v'), A)\<close>
    by (cases e) (auto elim: Cons_ev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE Cons_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
  thus ?case
  proof cases
    case mv_left
    from Cons.hyps[OF mv_left(4)] show ?thesis
      by (cases n, simp_all add: mv_left(2, 3) subset_iff) (metis drop0)
  next
    case mv_right
    from Cons.hyps[OF mv_right(4)] show ?thesis
      by (cases n, simp_all add: subset_iff)
        (metis drop0, meson Suc_n_not_le_n in_mono nle_le set_drop_subset_set_drop)
  next
    case mv_both_ev
    from Cons.hyps[OF mv_both_ev(5)] show ?thesis
      by (cases n, simp_all add: mv_both_ev(2, 3) subset_iff) (metis drop0)
  next
    case mv_both_tick
    from Cons.hyps[OF mv_both_tick(5)] show ?thesis
      by (cases n, simp_all add: mv_both_tick(3) subset_iff) (metis drop0)
  qed
qed

lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_set_subsetR :
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, v), A) \<Longrightarrow>
   {a. ev a \<in> set (drop n v)} \<subseteq> {a. ev a \<in> set (drop n t)}\<close>
  by (rule setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_set_subsetL)
    (fact setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym[THEN iffD2])









section \<open>Synchronization Product\<close>

subsection \<open>Definition\<close>

definition super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ::
  \<open>['r \<Rightarrow> 's \<Rightarrow> 't option, ('a, 'r) refusal\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a set, ('a, 's) refusal\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 't) refusal\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where \<open>super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join X_P A X_Q \<equiv>
         {ev a |a. ev a \<in> X_P \<and> ev a \<in> X_Q \<or> (a \<in> A \<and> (ev a \<in> X_P \<or> ev a \<in> X_Q))} \<union>
         {\<checkmark>(r_s) |r s r_s. tick_join r s = \<lfloor>r_s\<rfloor> \<and> (\<checkmark>(r) \<in> X_P \<or> \<checkmark>(s) \<in> X_Q)} \<union>
         \<comment>\<open>This is the last addition: since we generalize with the parameter \<^term>\<open>tick_join\<close>,
            we must add the following term to refuse the unreachable ticks.\<close>
         {\<checkmark>(r_s) |r_s. \<nexists>r s. tick_join r s = \<lfloor>r_s\<rfloor>}\<close>



text \<open>
For proving that the invariant \<^const>\<open>is_process\<close> is preserved, we will need a kind
of injectivity for the parameter \<^term>\<open>tick_join\<close>. We implement this through a \<^theory_text>\<open>locale\<close>.\<close>

locale Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale =
  fixes tick_join :: \<open>'r \<Rightarrow> 's \<Rightarrow> 't option\<close> (infixl \<open>\<otimes>\<checkmark>\<close> 100)
  assumes inj_tick_join :
    \<open>r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor> \<Longrightarrow> r' \<otimes>\<checkmark> s' = \<lfloor>r_s\<rfloor> \<Longrightarrow> r' = r \<and> s' = s\<close>
begin


sublocale Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym : Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale \<open>\<lambda>s r. r \<otimes>\<checkmark> s\<close>
  by unfold_locales (simp add: inj_tick_join)


lift_definition Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ::
  \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a set, ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 't) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  (\<open>(_ \<lbrakk>_\<rbrakk>\<^sub>\<checkmark> _)\<close> [70, 0, 71] 70)
  is \<open>\<lambda>P A Q.
      ({(t, X). \<exists>t_P t_Q X_P X_Q.
                (t_P, X_P) \<in> \<F> P \<and> (t_Q, X_Q) \<in> \<F> Q \<and>
                t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), A) \<and>
                X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P A X_Q} \<union>
       {(t @ u, X) |t u t_P t_Q X.
                    ftF u \<and> (tF t \<or> u = []) \<and> t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), A) \<and>
                    (t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q)},
       {t @ u |t u t_P t_Q.
               ftF u \<and> (tF t \<or> u = []) \<and> t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), A) \<and>
               (t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q)})\<close>
proof -
  show \<open>?thesis P A Q\<close>
    (is \<open>is_process(?f, ?d)\<close>) for P and Q :: \<open>('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and A
  proof (unfold is_process_def FAILURES_def DIVERGENCES_def fst_conv snd_conv, intro conjI impI allI)
    have \<open>([], {}) \<in> \<F> P\<close> and \<open>([], {}) \<in> \<F> Q\<close> by (simp_all add: is_processT1)
    with Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil show \<open>([], {}) \<in> ?f\<close> by fast
  next 
    show \<open>(t, X) \<in> ?f \<Longrightarrow> ftF t\<close> for t X
      by simp (metis (no_types, opaque_lifting) D_T F_imp_front_tickFree T_imp_front_tickFree
          append.right_neutral front_tickFree_append front_tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
  next
    fix t u assume \<open>(t @ u, {}) \<in> ?f\<close>
    then consider (fail) t_P t_Q X_P X_Q where 
      \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close> \<open>t @ u setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), A)\<close>
    | (div) t' u' t_P t_Q where
      \<open>t @ u = t' @ u'\<close> \<open>ftF u'\<close> \<open>tF t' \<or> u' = []\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), A)\<close>
      \<open>t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q\<close> by simp blast
    thus \<open>(t, {}) \<in> ?f\<close>
    proof cases
      case fail
      from fail(3) obtain t' u'
        where * : \<open>t' \<le> t_P\<close> \<open>u' \<le> t_Q\<close> \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t', u'), A)\<close>
        by (auto dest!: append_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k intro: prefixI)
      from fail(1, 2) "*"(1, 2) F_T is_processT3_TR have \<open>t' \<in> \<T> P\<close> \<open>u' \<in> \<T> Q\<close> by blast+
      thus \<open>(t, {}) \<in> ?f\<close> by simp (metis T_F_spec "*"(3))
    next
      case div
      show \<open>(t, {}) \<in> ?f\<close>
      proof (cases \<open>length t' \<le> length t\<close>)
        assume \<open>length t' \<le> length t\<close>
        with div(1-3) have \<open>ftF (take (length t - length t') u') \<and>
                            (tF t' \<or> take (length t - length t') u' = []) \<and>
                            t = t' @ take (length t - length t') u'\<close>
          by (simp add: append_eq_conv_conj)
            (metis append_take_drop_id front_tickFree_dw_closed)
        with div(4, 5) show \<open>(t, {}) \<in> ?f\<close> by blast
      next
        assume \<open>\<not> length t' \<le> length t\<close>
        with div obtain r' where \<open>t' = t @ r'\<close>
          by (metis append_eq_append_conv_if append_take_drop_id)
        with div(4) obtain t'' u''
          where * : \<open>t'' \<le> t_P\<close> \<open>u'' \<le> t_Q\<close> \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t'', u''), A)\<close>
          by (auto dest!: append_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k intro: prefixI)
        from "*"(1, 2) have \<open>t'' \<in> \<T> P \<and> u'' \<in> \<T> Q\<close> by (meson D_T div(5) is_processT3_TR)
        hence $ : \<open>(t'', {}) \<in> \<F> P\<close> \<open>(u'', {}) \<in> \<F> Q\<close> by (simp_all add: T_F)
        have $$ : \<open>{ev a| a. ev a \<in> {} \<and> ev a \<in> {} \<or> (a \<in> A \<and> (ev a \<in> {} \<or> ev a \<in> {}))} \<union>
                   {\<checkmark>(r \<otimes>\<checkmark> s)| r s. \<checkmark>(r) \<in> {} \<or> \<checkmark>(s) \<in> {}} = {}\<close> by simp
        show \<open>(t, {}) \<in> ?f\<close> by (auto intro!: "$" "*"(3))
      qed
    qed
  next
    { fix t X Y
      assume \<open>(t, Y) \<in> ?f \<and> X \<subseteq> Y\<close>
      then consider \<open>t \<in> ?d\<close>
        | (fail) t_P t_Q X_P X_Q where
          \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
          \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), A)\<close>
          \<open>Y \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P A X_Q\<close> by blast
      thus \<open>(t, X) \<in> ?f\<close>
      proof cases
        show \<open>t \<in> ?d \<Longrightarrow> (t, X) \<in> ?f\<close> by blast
      next
        case fail
        define X_P' where \<open>X_P' \<equiv> X_P \<inter> ({ev a| a. ev a \<in> X} \<union>
                                          {\<checkmark>(r)| r s r_s. r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor> \<and> \<checkmark>(r_s) \<in> X})\<close>
        define X_Q' where \<open>X_Q' \<equiv> X_Q \<inter> ({ev a| a. ev a \<in> X} \<union>
                                          {\<checkmark>(s)| r s r_s. r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor> \<and> \<checkmark>(r_s) \<in> X})\<close>
        have \<open>(t_P, X_P') \<in> \<F> P\<close> unfolding X_P'_def by (meson fail(1) inf_le1 process_charn)
        moreover have \<open>(t_Q, X_Q') \<in> \<F> Q\<close> unfolding X_Q'_def by (meson fail(2) inf_le1 process_charn)
        moreover have \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P' A X_Q'\<close>
          by (subst \<open>(t, Y) \<in> ?f \<and> X \<subseteq> Y\<close>[THEN conjunct2, THEN Int_absorb1, symmetric])
            (use fail(4) in \<open>fastforce simp add: X_P'_def X_Q'_def subset_iff super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def\<close>)
        ultimately show \<open>(t, X) \<in> ?f\<close> using fail(3) by simp blast
      qed } note processT4 = this

    fix t X Y
    assume \<open>(t, X) \<in> ?f \<and> (\<forall>e. e \<in> Y \<longrightarrow> (t @ [e], {}) \<notin> ?f)\<close>
    then consider \<open>t \<in> ?d\<close> | \<open>(t, X) \<in> ?f \<and> t \<notin> ?d\<close> by linarith
    thus \<open>(t, X \<union> Y) \<in> ?f\<close>
    proof cases
      show \<open>t \<in> ?d \<Longrightarrow> (t, X \<union> Y) \<in> ?f\<close> by blast
    next
      assume \<open>(t, X) \<in> ?f \<and> t \<notin> ?d\<close>
      then obtain t_P X_P t_Q X_Q
        where assms : \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
          \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), A)\<close>
          \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P A X_Q\<close> by blast
      have assms5 : \<open>e \<in> Y \<Longrightarrow> t @ [e] setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t', u'), A) \<Longrightarrow>
                     ((t', {}) \<in> \<F> P \<longrightarrow> (u', {}) \<notin> \<F> Q) \<and>
                     ((u', {}) \<in> \<F> Q \<longrightarrow> (t', {}) \<notin> \<F> P)\<close> for e t' u'
        using \<open>(t, X) \<in> ?f \<and> (\<forall>e. e \<in> Y \<longrightarrow> (t @ [e], {}) \<notin> ?f)\<close> by auto

      define Y_ev_inside and Y_ev_notin and Y_tick
        where * : \<open>Y_ev_inside \<equiv> {a. ev a \<in> Y \<and> a \<in> A}\<close>
          \<open>Y_ev_notin  \<equiv> {a. ev a \<in> Y \<and> a \<notin> A}\<close>
          \<open>Y_tick      \<equiv> {r_s |r s r_s. r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor> \<and> \<checkmark>(r_s) \<in> Y}\<close>

      define Y_ev_inside_P and Y_ev_inside_Q and Y_ev_notin_P
        and Y_ev_notin_Q and Y_tick_P and Y_tick_Q
        where ** : \<open>Y_ev_inside_P \<equiv> {a\<in>Y_ev_inside. (t_P @ [ev a], {}) \<notin> \<F> P}\<close>
          \<open>Y_ev_inside_Q \<equiv> {a\<in>Y_ev_inside. (t_Q @ [ev a], {}) \<notin> \<F> Q}\<close>
          \<open>Y_ev_notin_P  \<equiv> {a\<in>Y_ev_notin.  (t_P @ [ev a], {}) \<notin> \<F> P}\<close>
          \<open>Y_ev_notin_Q  \<equiv> {a\<in>Y_ev_notin.  (t_Q @ [ev a], {}) \<notin> \<F> Q}\<close>
          \<open>Y_tick_P      \<equiv> {r_s\<in>Y_tick. \<exists>r s. r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor> \<and> (t_P @ [\<checkmark>(r)], {}) \<notin> \<F> P}\<close>
          \<open>Y_tick_Q      \<equiv> {r_s\<in>Y_tick. \<exists>r s. r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor> \<and> (t_Q @ [\<checkmark>(s)], {}) \<notin> \<F> Q}\<close>

      have "\<euro>" : \<open>\<forall>a\<in>Y_ev_inside. (t_P @ [ev a], {}) \<notin> \<F> P \<or> (t_Q @ [ev a], {}) \<notin> \<F> Q\<close>
      proof (rule ccontr)
        assume \<open>\<not> (\<forall>a\<in>Y_ev_inside. (t_P @ [ev a], {}) \<notin> \<F> P \<or> (t_Q @ [ev a], {}) \<notin> \<F> Q)\<close>
        then obtain a where facts : \<open>a \<in> A\<close> \<open>ev a \<in> Y\<close> \<open>(t_P @ [ev a], {}) \<in> \<F> P\<close>
          \<open>(t_Q @ [ev a], {}) \<in> \<F> Q\<close>
          unfolding "*" by blast
        have \<open>t @ [ev a] setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P @ [ev a], t_Q @ [ev a]), A)\<close>
          by (simp add: facts(1) assms(3) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_inside)
        with facts(2-4) assms5 show False by blast
      qed
      hence "\<pounds>\<pounds>" : \<open>Y_ev_inside_P \<union> Y_ev_inside_Q = Y_ev_inside\<close> by (auto simp add: "**")

      have "\<euro>\<euro>" : \<open>\<forall>a\<in>Y_ev_notin. (t_P @ [ev a], {}) \<notin> \<F> P \<or> (t_Q @ [ev a], {}) \<notin> \<F> Q\<close>
      proof (rule ccontr)
        assume \<open>\<not> (\<forall>a\<in>Y_ev_notin. (t_P @ [ev a], {}) \<notin> \<F> P \<or> (t_Q @ [ev a], {}) \<notin> \<F> Q)\<close>
        then obtain a where facts : \<open>a \<notin> A\<close> \<open>ev a \<in> Y\<close> \<open>(t_P @ [ev a], {}) \<in> \<F> P\<close>
          \<open>(t_Q @ [ev a], {}) \<in> \<F> Q\<close> unfolding "*" by blast
        have \<open>t @ [ev a] setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q @ [ev a]), A) \<or>
              t @ [ev a] setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P @ [ev a], t_Q), A)\<close>
          by (simp add: facts(1) assms(3) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_notinL)
        with facts assms(1-3) assms5 show False by (metis is_processT4_empty)
      qed
      hence "\<pounds>\<pounds>\<pounds>" : \<open>Y_ev_notin_P \<union> Y_ev_notin_Q = Y_ev_notin\<close> by (auto simp add: "**")

      have "\<euro>\<euro>\<euro>" : \<open>\<forall>r_s\<in>Y_tick. \<exists>r s. r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor> \<and> ((t_P @ [\<checkmark>(r)], {}) \<notin> \<F> P \<or> (t_Q @ [\<checkmark>(s)], {}) \<notin> \<F> Q)\<close>
      proof (rule ccontr)
        assume \<open>\<not> (\<forall>r_s\<in>Y_tick. \<exists>r s. r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor> \<and>
                    ((t_P @ [\<checkmark>(r)], {}) \<notin> \<F> P \<or> (t_Q @ [\<checkmark>(s)], {}) \<notin> \<F> Q))\<close>
        then obtain r_s r s where facts : \<open>\<checkmark>(r_s) \<in> Y\<close> \<open>r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor>\<close>
          \<open>(t_P @ [\<checkmark>(r)], {}) \<in> \<F> P\<close> \<open>(t_Q @ [\<checkmark>(s)], {}) \<in> \<F> Q\<close>
          unfolding "*" by blast
        have \<open>t @ [\<checkmark>(r_s)] setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P @ [\<checkmark>(r)], t_Q @ [\<checkmark>(s)]), A)\<close>
          by (simp add: facts(2) assms(3) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_tick)
        with facts assms5 show False by blast
      qed
      hence "\<pounds>\<pounds>\<pounds>\<pounds>" : \<open>Y_tick_P \<union> Y_tick_Q = Y_tick\<close> unfolding "**" by blast

      define X_P' and X_Q'
        where *** : \<open>X_P' \<equiv> X_P \<union> ev ` Y_ev_inside_P \<union> ev ` Y_ev_notin_P \<union>
                            {\<checkmark>(r) |r s r_s. r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor> \<and> r_s \<in> Y_tick_P}\<close>
          \<open>X_Q' \<equiv> X_Q \<union> ev ` Y_ev_inside_Q \<union> ev ` Y_ev_notin_Q \<union>
                  {\<checkmark>(s) |r s r_s. r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor> \<and> r_s \<in> Y_tick_Q}\<close>

      have $ : \<open>(t_P, X_P') \<in> \<F> P\<close> \<open>(t_Q, X_Q') \<in> \<F> Q\<close>
        by (auto simp add: "**" "***" intro!: is_processT5 assms dest: inj_tick_join)

      have \<open>Y \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P' A X_Q'\<close>
      proof (rule subsetI)
        show \<open>e \<in> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P' A X_Q'\<close> if \<open>e \<in> Y\<close> for e
        proof (cases e)
          from \<open>e \<in> Y\<close> show \<open>e = ev a \<Longrightarrow> e \<in> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P' A X_Q'\<close> for a
            by (cases \<open>a \<in> A\<close>, simp_all add: "*" "**" "***" image_iff super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
              (use "*"(1) "\<euro>" in blast,
                meson "$"(2) assms(1, 3) assms5 is_processT4_empty
                setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_notinL setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_notinR)
        next
          show \<open>e \<in> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P' A X_Q'\<close> if \<open>e = \<checkmark>(r_s)\<close> for r_s
          proof (cases \<open>\<exists>r s. r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor>\<close>)
            assume \<open>\<exists>r s. r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor>\<close>
            then obtain r s where \<open>r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor>\<close> by blast
            with \<open>e \<in> Y\<close> \<open>e = \<checkmark>(r_s)\<close> have \<open>r_s \<in> Y_tick\<close>
              by (auto simp add: "*")
            thus \<open>e \<in> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P' A X_Q'\<close>
              by (simp add: "*" super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
                (metis (mono_tags, lifting) "*"(3) "***"(1,2) "\<pounds>\<pounds>\<pounds>\<pounds>"
                  Un_iff mem_Collect_eq \<open>e = \<checkmark>(r_s)\<close>)
          next
            show \<open>\<nexists>r s. r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor> \<Longrightarrow>
                  e \<in> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P' A X_Q'\<close>
              by (simp add: \<open>e = \<checkmark>(r_s)\<close> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
          qed
        qed
      qed
      moreover from assms(4) have \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P' A X_Q'\<close>
        by (fastforce simp add: "***" subset_iff super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
      ultimately show \<open>(t, X \<union> Y) \<in> ?f\<close> using "$" assms(3) by auto
    qed
  next
    show processT9: \<open>t \<in> ?d\<close> if \<open>t @ [\<checkmark>(r_s)] \<in> ?d\<close> for t r_s
    proof -
      from \<open>t @ [\<checkmark>(r_s)] \<in> ?d\<close> obtain u v t_P t_Q
        where assms : \<open>ftF v\<close> \<open>tF u \<or> v = []\<close>
          \<open>t @ [\<checkmark>(r_s)] = u @ v\<close>
          \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), A)\<close>
          \<open>t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q\<close> by blast
      from assms(2) show \<open>t \<in> ?d\<close>
      proof (elim disjE)
        assume \<open>tF u\<close>
        with assms(3) obtain v' where \<open>v = v' @ [\<checkmark>(r_s)]\<close> \<open>t = u @ v'\<close>
          by (cases v rule: rev_cases) auto
        from \<open>v = v' @ [\<checkmark>(r_s)]\<close> assms(1) front_tickFree_dw_closed
        have \<open>ftF v'\<close> by blast
        with \<open>t = u @ v'\<close> \<open>tF u\<close> assms(1, 4, 5) show \<open>t \<in> ?d\<close> by blast
      next
        assume \<open>v = []\<close>
        with assms(3) obtain u' where \<open>u = u' @ [\<checkmark>(r_s)]\<close> \<open>t = u'\<close> by auto
        from snoc_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE[OF assms(4)[unfolded this(1)]]
        obtain r s t_P' t_Q' where \<open>r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor>\<close>
          \<open>u' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P', t_Q'), A)\<close>
          \<open>t_P = t_P' @ [\<checkmark>(r)]\<close> \<open>t_Q = t_Q' @ [\<checkmark>(s)]\<close> by metis
        with assms(5) \<open>t = u'\<close> show \<open>t \<in> ?d\<close>
          by simp (metis append.right_neutral front_tickFree_Nil
              is_processT3_TR_append is_processT9)
      qed
    qed

    fix t X r_s
    assume \<open>(t @ [\<checkmark>(r_s)], {}) \<in> ?f\<close>
    then consider (div) \<open>t @ [\<checkmark>(r_s)] \<in> ?d\<close>
      | (fail) t_P t_Q X_P X_Q
      where \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
        \<open>(t @ [\<checkmark>(r_s)]) setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), A)\<close> by auto
    thus \<open>(t, X - {\<checkmark>(r_s)}) \<in> ?f\<close>
    proof cases
      show \<open>t @ [\<checkmark>(r_s)] \<in> ?d \<Longrightarrow> (t, X - {\<checkmark>(r_s)}) \<in> ?f\<close> by (drule processT9) simp
    next
      case fail
      from fail(3)[THEN snoc_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE]
      obtain r s t_P' t_Q' where * : \<open>r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor>\<close>
        \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P', t_Q'), A)\<close>
        \<open>t_P = t_P' @ [\<checkmark>(r)]\<close> \<open>t_Q = t_Q' @ [\<checkmark>(s)]\<close> by metis
      from fail(1, 2) have \<open>t_P' @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>t_Q' @ [\<checkmark>(s)] \<in> \<T> Q\<close>
        by (simp_all add: "*"(3, 4) F_T)
      hence \<open>(t_P', UNIV - {\<checkmark>(r)}) \<in> \<F> P\<close>
        \<open>(t_Q', UNIV - {\<checkmark>(s)}) \<in> \<F> Q\<close> by (meson is_processT6_TR)+
      moreover have \<open>X - {\<checkmark>(r_s)} \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) (UNIV - {\<checkmark>(r)}) A (UNIV - {\<checkmark>(s)})\<close>
        by (simp add: subset_iff super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
          (metis "*"(1) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust option.inject)
      ultimately show \<open>(t, X - {\<checkmark>(r_s)}) \<in> ?f\<close> using "*"(2) by fast
    qed
  next
    show \<open>s \<in> ?d \<and> tF s \<and> ftF t \<Longrightarrow> s @ t \<in> ?d\<close> for s t
      using front_tickFree_append by fastforce
  next  
    show \<open>s \<in> ?d \<Longrightarrow> (s, X) \<in> ?f\<close> for s X by blast
  qed
qed


text \<open>
Here \<^term>\<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P A X_Q\<close> may seem surprising
(instead of for example \<^term>\<open>X = super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P A X_Q\<close>,
closer to the specification of \<^const>\<open>Sync\<close>).
Actually, edge cases in the behaviour of \<^const>\<open>tick\<close> ensure that a definition
with the latter would violate the invariant.
\<close>

end

abbreviation (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ::
  \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow>
   ('a, 't) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (\<open>(_ |||\<^sub>\<checkmark> _)\<close> [72, 73] 72)
  where \<open>P |||\<^sub>\<checkmark> Q \<equiv> P \<lbrakk> {} \<rbrakk>\<^sub>\<checkmark> Q\<close>

abbreviation (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) Par\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ::
  \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow>
   ('a, 't) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (\<open>(_ ||\<^sub>\<checkmark> _)\<close> [74, 75] 74)
  where \<open>P ||\<^sub>\<checkmark> Q \<equiv> P \<lbrakk> UNIV \<rbrakk>\<^sub>\<checkmark> Q\<close>

notation (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
  (\<open>(_ \<lbrakk>_\<rbrakk>\<^sub>\<checkmark>\<^sub>s\<^sub>y\<^sub>m _)\<close> [70, 0, 71] 70)

notation (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
  (\<open>(_ |||\<^sub>\<checkmark>\<^sub>s\<^sub>y\<^sub>m _)\<close> [72, 73] 72)

notation (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Par\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
  (\<open>(_ ||\<^sub>\<checkmark>\<^sub>s\<^sub>y\<^sub>m _)\<close> [74, 75] 74)




subsection \<open>Projections\<close>

context Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale begin

lemma D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k' :
  \<open>\<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q) = 
   {t @ u |t u t_P t_Q.
           ftF u \<and> (tF t \<or> u = []) \<and> t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), A) \<and>
           (t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q)}\<close>
  by (simp add: Divergences.rep_eq Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.rep_eq DIVERGENCES_def)

corollary D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<comment>\<open>This version is easier to use.\<close>
  \<open>\<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q) = 
   {t @ u |t u t_P t_Q.
           tF t \<and> ftF u \<and> t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), A) \<and>
           (t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q)}\<close>
  (is \<open>_ = ?rhs\<close>)
proof (intro subset_antisym subsetI)
  show \<open>d \<in> ?rhs \<Longrightarrow> d \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close> for d
    by (auto simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k')
next
  fix d assume \<open>d \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close>
  then obtain t u t_P t_Q
    where * : \<open>d = t @ u\<close> \<open>ftF u\<close> \<open>tF t \<or> u = []\<close>
      \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), A)\<close>
      \<open>t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q\<close>
    unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k' by blast
  show \<open>d \<in> ?rhs\<close>
  proof (cases \<open>tF t\<close>)
    from "*" show \<open>tF t \<Longrightarrow> d \<in> ?rhs\<close> by blast
  next
    assume \<open>\<not> tF t\<close>
    with "*"(1, 3) have \<open>u = []\<close> \<open>d = t\<close> by simp_all
    from D_imp_front_tickFree \<open>d = t\<close> \<open>d \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close>
    have \<open>ftF t\<close> by blast
    with \<open>\<not> tF t\<close> obtain r_s t' where \<open>t = t' @ [\<checkmark>(r_s)]\<close>
      by (meson nonTickFree_n_frontTickFree)
    with "*"(4) obtain r t_P' s t_Q'
      where ** : \<open>r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor>\<close>
        \<open>t_P = t_P' @ [\<checkmark>(r)]\<close> \<open>t_Q = t_Q' @ [\<checkmark>(s)]\<close>
        \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P', t_Q'), A)\<close>
      by (auto simp add: \<open>t = t' @ [\<checkmark>(r_s)]\<close>
          elim: snoc_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
    have \<open>t_P' \<in> \<D> P \<and> t_Q' \<in> \<T> Q \<or> t_P' \<in> \<T> P \<and> t_Q' \<in> \<D> Q\<close>
      by (metis "*"(5) "**"(2, 3) is_processT3_TR_append is_processT9)
    with "**"(4) \<open>d = t\<close> \<open>ftF t\<close> \<open>t = t' @ [\<checkmark>(r_s)]\<close>
      front_tickFree_nonempty_append_imp show \<open>d \<in> ?rhs\<close> by blast
  qed
qed


lemma F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k' :
  \<open>\<F> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q) = 
   {(t, X). \<exists>t_P t_Q X_P X_Q.
            (t_P, X_P) \<in> \<F> P \<and> (t_Q, X_Q) \<in> \<F> Q \<and>
            t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), A) \<and>
            X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P A X_Q} \<union>
   {(t @ u, X) |t u t_P t_Q X.
                ftF u \<and> (tF t \<or> u = []) \<and> t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), A) \<and>
                (t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q)}\<close>
  by (simp add: Failures.rep_eq Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.rep_eq FAILURES_def)

lemma F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>\<F> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q) = 
   {(t, X). \<exists>t_P t_Q X_P X_Q.
            (t_P, X_P) \<in> \<F> P \<and> (t_Q, X_Q) \<in> \<F> Q \<and>
            t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), A) \<and>
            X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P A X_Q} \<union>
   {(t @ u, X) |t u t_P t_Q X.
                tF t \<and> ftF u \<and> t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), A) \<and>
                (t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q)}\<close>
  unfolding F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k' using D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[of P A Q, unfolded D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k']
  by (intro arg_cong2[where f = \<open>(\<union>)\<close>], simp)
    (simp add: set_eq_iff, blast)


lemma T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k' :
  \<open>\<T> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q) =
   {t. \<exists>t_P t_Q. t_P \<in> \<T> P \<and> t_Q \<in> \<T> Q \<and> t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), A)} \<union>
   {t @ u |t u t_P t_Q.
           ftF u \<and> (tF t \<or> u = []) \<and>
           t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), A) \<and>
           (t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q)}\<close>
  by (simp add: Traces.rep_eq TRACES_def Failures.rep_eq[symmetric] F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k') blast

lemma T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>\<T> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q) =
   {t. \<exists>t_P t_Q. t_P \<in> \<T> P \<and> t_Q \<in> \<T> Q \<and> t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), A)} \<union>
   {t @ u |t u t_P t_Q.
           tF t \<and> ftF u \<and> t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), A) \<and>
           (t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q)}\<close>
  unfolding T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k' using D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[of P A Q, unfolded D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k']
  by (intro arg_cong2[where f = \<open>(\<union>)\<close>]) (simp_all add: set_eq_iff)


lemmas Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs' = F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k' D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k' T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k'
  \<comment>\<open>Classical versions, but the ones below are often more convenient to use.\<close>

lemmas Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs  = F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k  D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k  T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k


lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_same_tick_join_on_strict_ticks_of :
  \<open>Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join' P S Q = P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q\<close>
  if \<open>Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale tick_join'\<close> and \<open>\<And>r s. r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<Longrightarrow> s \<in> \<^bold>\<checkmark>\<^bold>s(Q) \<Longrightarrow> tick_join' r s = r \<otimes>\<checkmark> s\<close>
proof -
  interpret tjoin_interpreted : Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale tick_join'
    by (fact \<open>Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale tick_join'\<close>)
  show \<open>Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join' P S Q = P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q\<close>
  proof (rule Process_eq_optimizedI)
    show \<open>t \<in> \<D> (tjoin_interpreted.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k P S Q) \<Longrightarrow> t \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> for t
      by (simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tjoin_interpreted.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        (metis tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_any_tick_join)
  next
    show \<open>t \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) \<Longrightarrow> t \<in> \<D> (tjoin_interpreted.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k P S Q)\<close> for t
      by (simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tjoin_interpreted.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        (metis tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_any_tick_join)
  next
    fix t X assume \<open>(t, X) \<in> \<F> (tjoin_interpreted.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k P S Q)\<close>
      \<open>t \<notin> \<D> (tjoin_interpreted.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k P S Q)\<close>
    then obtain t_P X_P t_Q X_Q where * : \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
      \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join'\<^esub> ((t_P, t_Q), S)\<close>
      \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join' X_P S X_Q\<close>
      unfolding tjoin_interpreted.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
    define X_P_plus where \<open>X_P_plus \<equiv> X_P \<union> {\<checkmark>(r) |r. t_P @ [\<checkmark>(r)] \<notin> \<T> P - \<D> P}\<close>
    define X_Q_plus where \<open>X_Q_plus \<equiv> X_Q \<union> {\<checkmark>(s) |s. t_Q @ [\<checkmark>(s)] \<notin> \<T> Q - \<D> Q}\<close>
    have \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<close>
    proof (cases \<open>tF t\<close>)
      show \<open>tF t \<Longrightarrow> t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<close>
        using "*"(3) tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_any_tick_join by blast
    next
      assume \<open>\<not> tF t\<close>
      then obtain t' r_s where \<open>tF t'\<close> \<open>t = t' @ [\<checkmark>(r_s)]\<close>
        by (metis F_imp_front_tickFree \<open>(t, X) \<in> \<F> (tjoin_interpreted.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k P S Q)\<close>
            front_tickFree_append_iff nonTickFree_n_frontTickFree not_Cons_self2)
      with "*"(3) obtain t_P' r t_Q' s where ** : \<open>tick_join' r s = \<lfloor>r_s\<rfloor>\<close>
        \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join'\<^esub> ((t_P', t_Q'), S)\<close>
        \<open>t_P = t_P' @ [\<checkmark>(r)]\<close> \<open>t_Q = t_Q' @ [\<checkmark>(s)]\<close>
        by (auto elim: snoc_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
      have \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<and> s \<in> \<^bold>\<checkmark>\<^bold>s(Q)\<close>
      proof (rule ccontr)
        assume \<open>\<not> (r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<and> s \<in> \<^bold>\<checkmark>\<^bold>s(Q))\<close>
        hence \<open>t_P' @ [\<checkmark>(r)] \<in> \<D> P \<or> t_Q' @ [\<checkmark>(s)] \<in> \<D> Q\<close>
          by (metis "*"(1, 2) "**"(3, 4) F_T strict_ticks_of_memI)
        with \<open>t \<notin> \<D> (tjoin_interpreted.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k P S Q)\<close> show False
          by (simp add: tjoin_interpreted.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k')
            (metis "*"(1-3) "**"(3, 4) F_T append.right_neutral front_tickFree_Nil)
      qed
      moreover from "**"(2) have \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P', t_Q'), S)\<close>
        using \<open>tF t'\<close> tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_any_tick_join by blast
      ultimately show \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<close>
        by (subst rev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_rev_rev_iff[symmetric],
            subst (asm) rev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_rev_rev_iff[symmetric])
          (use "**"(1) that(2) in \<open>auto simp add: \<open>t = t' @ [\<checkmark>(r_s)]\<close> "**"(3, 4)\<close>)
    qed
    moreover from "*"(1) is_processT5_S7' is_processT8 is_processT9
    have \<open>(t_P, X_P_plus) \<in> \<F> P\<close> by (fastforce simp add: X_P_plus_def)
    moreover from "*"(2) is_processT5_S7' is_processT8 is_processT9
    have \<open>(t_Q, X_Q_plus) \<in> \<F> Q\<close> by (fastforce simp add: X_Q_plus_def)
    moreover have \<open>e \<in> X \<Longrightarrow> e \<in> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P_plus S X_Q_plus\<close> for e
      using "*"(4)[THEN set_mp, of e]
      by (cases e, simp_all add: X_P_plus_def X_Q_plus_def super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def subset_iff)
        (metis strict_ticks_of_memI that(2) tjoin_interpreted.inj_tick_join)
    ultimately show \<open>(t, X) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> by (simp add: F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) blast
  next
    fix t X assume \<open>(t, X) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> \<open>t \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
    then obtain t_P X_P t_Q X_Q where * : \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
      \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<close>
      \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P S X_Q\<close>
      unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
    define X_P_plus where \<open>X_P_plus \<equiv> X_P \<union> {\<checkmark>(r) |r. t_P @ [\<checkmark>(r)] \<notin> \<T> P - \<D> P}\<close>
    define X_Q_plus where \<open>X_Q_plus \<equiv> X_Q \<union> {\<checkmark>(s) |s. t_Q @ [\<checkmark>(s)] \<notin> \<T> Q - \<D> Q}\<close>
    have \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join'\<^esub> ((t_P, t_Q), S)\<close>
    proof (cases \<open>tF t\<close>)
      show \<open>tF t \<Longrightarrow> t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join'\<^esub> ((t_P, t_Q), S)\<close>
        using "*"(3) tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_any_tick_join by blast
    next
      assume \<open>\<not> tF t\<close>
      then obtain t' r_s where \<open>tF t'\<close> \<open>t = t' @ [\<checkmark>(r_s)]\<close>
        by (metis F_imp_front_tickFree \<open>(t, X) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
            front_tickFree_append_iff nonTickFree_n_frontTickFree not_Cons_self2)
      with "*"(3) obtain t_P' r t_Q' s where ** : \<open>r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor>\<close>
        \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P', t_Q'), S)\<close>
        \<open>t_P = t_P' @ [\<checkmark>(r)]\<close> \<open>t_Q = t_Q' @ [\<checkmark>(s)]\<close>
        by (auto elim: snoc_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
      have \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<and> s \<in> \<^bold>\<checkmark>\<^bold>s(Q)\<close>
      proof (rule ccontr)
        assume \<open>\<not> (r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<and> s \<in> \<^bold>\<checkmark>\<^bold>s(Q))\<close>
        hence \<open>t_P' @ [\<checkmark>(r)] \<in> \<D> P \<or> t_Q' @ [\<checkmark>(s)] \<in> \<D> Q\<close>
          by (metis "*"(1, 2) "**"(3, 4) F_T strict_ticks_of_memI)
        with \<open>t \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> show False
          by (simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k')
            (metis "*"(1-3) "**"(3, 4) F_T append.right_neutral front_tickFree_Nil)
      qed
      moreover from "**"(2) have \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join'\<^esub> ((t_P', t_Q'), S)\<close>
        using \<open>tF t'\<close> tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_any_tick_join by blast
      ultimately show \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join'\<^esub> ((t_P, t_Q), S)\<close>
        by (subst rev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_rev_rev_iff[symmetric],
            subst (asm) rev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_rev_rev_iff[symmetric])
          (use "**"(1) that(2) in \<open>auto simp add: \<open>t = t' @ [\<checkmark>(r_s)]\<close> "**"(3, 4)\<close>)
    qed
    moreover from "*"(1) is_processT5_S7' is_processT8 is_processT9
    have \<open>(t_P, X_P_plus) \<in> \<F> P\<close> by (fastforce simp add: X_P_plus_def)
    moreover from "*"(2) is_processT5_S7' is_processT8 is_processT9
    have \<open>(t_Q, X_Q_plus) \<in> \<F> Q\<close> by (fastforce simp add: X_Q_plus_def)
    moreover have \<open>e \<in> X \<Longrightarrow> e \<in> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join' X_P_plus S X_Q_plus\<close> for e
      using "*"(4)[THEN set_mp, of e]
      by (cases e, simp_all add: X_P_plus_def X_Q_plus_def super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def subset_iff)
        (metis strict_ticks_of_memI that(2) inj_tick_join)
    ultimately show \<open>(t, X) \<in> \<F> (tjoin_interpreted.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k P S Q)\<close>
      by (simp add: tjoin_interpreted.F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) blast
  qed
qed




subsection \<open>First Properties\<close>

abbreviation range_tick_join :: \<open>'t set\<close>
  where \<open>range_tick_join \<equiv> {r_s |r_s r s. r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor>}\<close>

lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_imp_set_range_tick_join :
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((u, v), A) \<Longrightarrow>
   {r_s. \<checkmark>(r_s) \<in> set t} \<subseteq> range_tick_join\<close>
  by (induct \<open>((\<otimes>\<checkmark>), u, A, v)\<close> arbitrary: t u v)
    (auto simp add: subset_iff split: if_split_asm option.split_asm)+

end



lemma
  \<comment> \<open>Of course not suitable for simplifier.\<close>
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>\<lambda>s r. tick_join r s\<^esub> ((v, u), A) \<longleftrightarrow>
   t setinterleaves\<^sub>\<checkmark>\<^bsub>\<lambda>r s. tick_join r s\<^esub> ((u, v), A)\<close>
  by (fact setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym)

lemma super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym :
  \<comment> \<open>Of course not suitable for simplifier.\<close>
  \<open>super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<lambda>s r. tick_join r s) X_Q S X_P =
   super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<lambda>r s. tick_join r s) X_P S X_Q\<close>
  by (auto simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)


lemma super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_mono :
  \<open>A \<subseteq> A' \<Longrightarrow> X_P \<subseteq> X_P' \<Longrightarrow> X_Q \<subseteq> X_Q' \<Longrightarrow>
   super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join X_P A X_Q \<subseteq>
   super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join X_P' A' X_Q'\<close>
  by (auto simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)



context Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale begin

lemma Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym : \<open>Q \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>s\<^sub>y\<^sub>m P = P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q\<close>
proof (rule Process_eq_optimizedI)
  show \<open>t \<in> \<D> (Q \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>s\<^sub>y\<^sub>m P) \<Longrightarrow> t \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close> for t
    by (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      (subst setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym, blast)
next
  show \<open>t \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q) \<Longrightarrow> t \<in> \<D> (Q \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>s\<^sub>y\<^sub>m P)\<close> for t
    by (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      (subst setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym, blast)
next
  show \<open>(t, X) \<in> \<F> (Q \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>s\<^sub>y\<^sub>m P) \<Longrightarrow> (t, X) \<in> \<F> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close> for t X
    by (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      (subst (1 2) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym,
        subst super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym, blast)
next
  show \<open>(t, X) \<in> \<F> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q) \<Longrightarrow> (t, X) \<in> \<F> (Q \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>s\<^sub>y\<^sub>m P)\<close> for t X
    by (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      (subst (1 2) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym,
        subst super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym, blast)
qed


lemma interpretable_inj_on_range_tick_join :
  \<open>inj_on g range_tick_join \<Longrightarrow>
   Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale (\<lambda>r s. case r \<otimes>\<checkmark> s of \<lfloor>r_s\<rfloor> \<Rightarrow> \<lfloor>g r_s\<rfloor> | \<diamond> \<Rightarrow> \<diamond>)\<close>
  by (unfold_locales, simp split: option.split_asm)
    (metis (mono_tags, lifting) inj_onD inj_tick_join mem_Collect_eq)


lemma inj_on_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((u, v), A) \<Longrightarrow>
   map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g) t
   setinterleaves\<^sub>\<checkmark>\<^bsub>\<lambda>r s. case r \<otimes>\<checkmark> s of \<lfloor>r_s\<rfloor> \<Rightarrow> \<lfloor>g r_s\<rfloor> | \<diamond> \<Rightarrow> \<diamond>\<^esub> ((u, v), A)\<close>
  (is \<open>_ \<Longrightarrow> _ setinterleaves\<^sub>\<checkmark>\<^bsub>?tick_join'\<^esub> ((u, v), A)\<close>)
  if inj_on_g : \<open>inj_on g range_tick_join\<close>
proof (induct \<open>((\<otimes>\<checkmark>), u, A, v)\<close> arbitrary: t u v)
  case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick r u s v)
  from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems [simplified]
  obtain r_s t' where * : \<open>r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor>\<close> \<open>t = \<checkmark>(r_s) # t'\<close>
    \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((u, v), A)\<close>
    by (auto split: option.split_asm)
  from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.hyps[OF "*"(1, 3)]
  have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g) t'
        setinterleaves\<^sub>\<checkmark>\<^bsub>?tick_join'\<^esub> ((u, v), A)\<close> .
  thus ?case by (simp add: "*"(1, 2))
qed auto



lemma vimage_inj_on_subset_super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff :
  \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g -` X \<subseteq>
   super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P A X_Q \<longleftrightarrow>
   X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<lambda>r s. case r \<otimes>\<checkmark> s of \<lfloor>r_s\<rfloor> \<Rightarrow> \<lfloor>g r_s\<rfloor> | \<diamond> \<Rightarrow> \<diamond>) X_P A X_Q\<close>
  (is \<open>?lhs1 \<subseteq> ?lhs2 \<longleftrightarrow> X \<subseteq> ?rhs\<close>)
  if inj_on_g : \<open>inj_on g range_tick_join\<close>
proof -
  let ?tick_join' = \<open>\<lambda>r s. case r \<otimes>\<checkmark> s of \<lfloor>r_s\<rfloor> \<Rightarrow> \<lfloor>g r_s\<rfloor> | \<diamond> \<Rightarrow> \<diamond>\<close>
  interpret Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k' : Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale ?tick_join'
    by (intro interpretable_inj_on_range_tick_join inj_on_g)
  from inv_into_f_f inj_on_g have expanded_tick_join :
    \<open>tick_join =
     (\<lambda>r s. case ?tick_join' r s of \<diamond> \<Rightarrow> \<diamond> | \<lfloor>r_s\<rfloor> \<Rightarrow> \<lfloor>inv_into range_tick_join g r_s\<rfloor>)\<close>
    by (fastforce split: split: option.split)
  let ?f1 = \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g\<close>
  let ?f2 = \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id (inv_into range_tick_join g)\<close>
  show \<open>?lhs1 \<subseteq> ?lhs2 \<longleftrightarrow> X \<subseteq> ?rhs\<close>
  proof (intro iffI subsetI)
    show \<open>e \<in> ?rhs\<close> if \<open>?lhs1 \<subseteq> ?lhs2\<close> \<open>e \<in> X\<close> for e
    proof (cases e)
      fix a assume \<open>e = ev a\<close>
      with \<open>e \<in> X\<close> have \<open>?f2 e \<in> ?f1 -` X\<close> by simp
      with \<open>?lhs1 \<subseteq> ?lhs2\<close> have \<open>?f2 e \<in> ?lhs2\<close> by blast
      with \<open>e = ev a\<close> show \<open>e \<in> ?rhs\<close>
        by (auto simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
    next
      show \<open>e \<in> ?rhs\<close> if \<open>e = \<checkmark>(r_s)\<close> for r_s
      proof (cases \<open>\<exists>r s. ?tick_join' r s = \<lfloor>r_s\<rfloor>\<close>)
        from \<open>e = \<checkmark>(r_s)\<close> show \<open>\<nexists>r s. ?tick_join' r s = \<lfloor>r_s\<rfloor> \<Longrightarrow> e \<in> ?rhs\<close>
          by (simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
      next
        assume \<open>\<exists>r s. ?tick_join' r s = \<lfloor>r_s\<rfloor>\<close>
        with \<open>e = \<checkmark>(r_s)\<close> \<open>e \<in> X\<close>
        have \<open>?f2 e \<in> ?f1 -` X\<close>
          by (auto split: option.split_asm)
            (metis (no_types, lifting) expanded_tick_join option.simps(5))
        with \<open>?lhs1 \<subseteq> ?lhs2\<close> have \<open>?f2 e \<in> ?lhs2\<close> by blast
        with \<open>e = \<checkmark>(r_s)\<close> show \<open>e \<in> ?rhs\<close>
          by (simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
            (metis (no_types, lifting) expanded_tick_join option.simps(5))
      qed
    qed
  next
    show \<open>e \<in> ?lhs2\<close> if \<open>X \<subseteq> ?rhs\<close> and \<open>e \<in> ?lhs1\<close> for e
    proof (cases e)
      fix a assume \<open>e = ev a\<close>
      with \<open>e \<in> ?lhs1\<close> have \<open>ev a \<in> X\<close> by simp
      with \<open>X \<subseteq> ?rhs\<close> have \<open>ev a \<in> ?rhs\<close> by blast
      thus \<open>e \<in> ?lhs2\<close> by (auto simp add: \<open>e = ev a\<close> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
    next
      show \<open>e \<in> ?lhs2\<close> if \<open>e = \<checkmark>(s_r)\<close> for s_r
      proof (cases \<open>\<exists>s r. tick_join s r = \<lfloor>s_r\<rfloor>\<close>)
        from \<open>e = \<checkmark>(s_r)\<close> show \<open>\<nexists>s r. tick_join s r = \<lfloor>s_r\<rfloor> \<Longrightarrow> e \<in> ?lhs2\<close>
          by (simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
      next
        assume \<open>\<exists>s r. tick_join s r = \<lfloor>s_r\<rfloor>\<close>
        with \<open>e = \<checkmark>(s_r)\<close> \<open>e \<in> ?lhs1\<close>
        have \<open>\<checkmark>(g s_r) \<in> X\<close> by simp
        with \<open>X \<subseteq> ?rhs\<close> have \<open>\<checkmark>(g s_r) \<in> ?rhs\<close> by blast
        with \<open>e = \<checkmark>(s_r)\<close> show \<open>e \<in> ?lhs2\<close>
          by (simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
            (metis Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k'.inj_tick_join option.simps(5))
      qed
    qed
  qed
qed


text \<open>The two following lemmas are necessary for the proof of continuity.\<close>

lemma finite_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick_join :
  \<open>finite {(u, v). t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((u, v), A)}\<close>
  (is \<open>finite {(u, v). ?f t u v}\<close>)
proof (induct t)
  have \<open>{(u, v). ?f [] u v} = {([], [])}\<close> by (auto simp add: Nil_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  thus \<open>finite {(u, v). ?f [] u v}\<close> by simp
next
  fix e t assume \<open>finite {(u, v). ?f t u v}\<close>
  have * : \<open>{(x # u, v) | u v. ?f t u v} = (\<lambda>(u, v). (x # u, v)) ` {(u, v). ?f t u v}\<close>
    \<open>{(u, y # v) | u v. ?f t u v} = (\<lambda>(u, v). (u, y # v)) ` {(u, v). ?f t u v}\<close>
    \<open>{(x # u, y # v) | u v. ?f t u v} = (\<lambda>(u, v). (x # u, y # v)) ` {(u, v). ?f t u v}\<close>
    for x y by auto
  show \<open>finite {(u, v). ?f (e # t) u v}\<close>
  proof (cases e)
    fix a assume \<open>e = ev a\<close>
    hence \<open>?f (e # t) u v \<Longrightarrow>
           u \<noteq> [] \<and> hd u = ev a \<and> ?f t (tl u) v \<or>
           v \<noteq> [] \<and> hd v = ev a \<and> ?f t u (tl v) \<or>
           u \<noteq> [] \<and> hd u = ev a \<and> v \<noteq> [] \<and> hd v = ev a \<and> ?f t (tl u) (tl v)\<close> for u v
      by (cases e) (auto elim: Cons_ev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE Cons_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
    hence \<open>{(u, v). ?f (e # t) u v} \<subseteq>
           {(ev a # u, v) | u v. ?f t u v} \<union>
           {(u, ev a # v) | u v. ?f t u v} \<union>
           {(ev a # u, ev a # v) | u v. ?f t u v}\<close>
      by (simp add: subset_iff) (metis list.collapse)
    moreover have \<open>finite {(ev a # u, v) | u v. ?f t u v}\<close>
      by (simp add: "*"(1) \<open>finite {(u, v). ?f t u v}\<close>)
    moreover have \<open>finite {(u, ev a # v) | u v. ?f t u v}\<close>
      by (simp add: "*"(2) \<open>finite {(u, v). ?f t u v}\<close>)
    moreover have \<open>finite {(ev a # u, ev a # v) | u v. ?f t u v}\<close>
      by (simp add: "*"(3) \<open>finite {(u, v). ?f t u v}\<close>)
    ultimately show \<open>finite {(u, v). ?f (e # t) u v}\<close>
      by (simp add: finite_subset)
  next
    show \<open>finite {(u, v). ?f (e # t) u v}\<close> if \<open>e = \<checkmark>(r_s)\<close> for r_s
    proof (cases \<open>r_s \<in> range_tick_join\<close>)
      assume \<open>r_s \<in> range_tick_join\<close>
      then obtain r s where \<open>r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor>\<close> by blast
      hence \<open>?f (e # t) u v \<Longrightarrow>
             u \<noteq> [] \<and> hd u = \<checkmark>(r) \<and> v \<noteq> [] \<and> hd v = \<checkmark>(s) \<and> ?f t (tl u) (tl v)\<close> for u v
        by (cases u; cases v)
          (auto simp add: \<open>e = \<checkmark>(r_s)\<close> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps inj_tick_join
            split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.splits option.split_asm if_split_asm)
      hence \<open>{(u, v). ?f (e # t) u v} \<subseteq> {(\<checkmark>(r) # u, \<checkmark>(s) # v) |u v. ?f t u v}\<close>
        by (simp add: subset_iff) (metis list.collapse)
      moreover have \<open>finite {(\<checkmark>(r) # u, \<checkmark>(s) # v) |u v. ?f t u v}\<close>
        by (simp add: "*"(3) \<open>finite {(u, v). ?f t u v}\<close>)
      ultimately show \<open>finite {(u, v). ?f (e # t) u v}\<close>
        by (simp add: finite_subset)
    next
      assume \<open>r_s \<notin> range_tick_join\<close>
      hence \<open>\<not> ?f (e # t) u v\<close> for u v
        by (cases u; cases v)
          (auto simp add: \<open>e = \<checkmark>(r_s)\<close> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps
            split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.splits option.split_asm)
      thus \<open>finite {(u, v). ?f (e # t) u v}\<close> by simp
    qed
  qed
qed


lemma finite_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick_join_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>finite {(t_P, t_Q, u). u setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), A) \<and>
                          (\<exists>v. t = u @ v \<and> ftF v \<and> (tF u \<or> v = []))}\<close>
  (is \<open>finite {(t_P, t_Q, u). ?f u t_P t_Q \<and> ?g t u}\<close>)
proof -
  have \<open>{(t_P, t_Q, u) |t_P t_Q. ?f u t_P t_Q} \<subseteq>
        (\<lambda>(t_P, t_Q). (t_P, t_Q, u)) ` {(t_P, t_Q). ?f u t_P t_Q}\<close> for u by auto
  hence \<open>finite {(t_P, t_Q, u) |t_P t_Q. ?f u t_P t_Q}\<close> for u
    by (rule finite_subset) (simp add: finite_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick_join)
  moreover have \<open>{(t_P, t_Q, u). ?f u t_P t_Q \<and> ?g t u} \<subseteq>
                 (\<Union>u \<in> {u. u \<le> t}. {(t_P, t_Q, u) |t_P t_Q. ?f u t_P t_Q})\<close>
    unfolding less_eq_list_def prefix_def by blast
  moreover have \<open>finite {u. u \<le> t}\<close> by (prove_finite_subset_of_prefixes t)
  ultimately show ?thesis by (simp add: finite_subset)
qed


end



(*<*)
end
  (*>*)
