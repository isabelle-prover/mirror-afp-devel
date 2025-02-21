(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : HOL-CSP_OpSem - Operational semantics for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Burkhart Wolff.
 *
 * This file       : Extension of the After operator with a locale
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

chapter \<open>Extension of the After Operator\<close>

section\<open> The After\<open>\<^sub>\<checkmark>\<close> Operator \<close>

(*<*)
theory  After_Ext_Operator
  imports After_Operator 
begin
  (*>*)

locale AfterExt = After \<Psi>
  for \<Psi> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<close>
    \<comment>\<open>Just declaring the types \<^typ>\<open>'a\<close> and \<^typ>\<open>'r\<close>.\<close> +
  fixes \<Omega> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
begin


subsection \<open>Definition\<close>

text \<open>We just defined \<^term>\<open>P after e\<close> for @{term [show_types] \<open>P :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>} 
      and @{term [show_types] \<open>e :: 'a\<close>}; in other words we cannot handle \<^term>\<open>\<checkmark>(r)\<close>.
      We now introduce a generalisation for @{term [show_types] \<open>e :: ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>}.\<close>

text \<open>In the previous version, we agreed to get \<^const>\<open>STOP\<close> after a termination,
      but only if \<^term>\<open>P\<close> was not \<^term>\<open>\<bottom>\<close> since otherwise we kept \<^term>\<open>\<bottom>\<close>.
      We were not really sure about this choice, and we even introduced a variation
      where the result after a termination was always \<^const>\<open>STOP\<close>. 
      In this new version we use a placeholder instead: \<^term>\<open>\<Omega>\<close>.
      We define \<^term>\<open>P\<close> after \<^term>\<open>\<checkmark>(r)\<close> being equal to \<^term>\<open>\<Omega> P r\<close>.\<close>

text \<open>For the moment we have no additional assumption on \<^term>\<open>\<Omega>\<close>. This will be discussed later.\<close>


definition After\<^sub>t\<^sub>i\<^sub>c\<^sub>k :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (infixl \<open>after\<^sub>\<checkmark>\<close> 86)
  where \<open>P after\<^sub>\<checkmark> e \<equiv> case e of ev x \<Rightarrow> P after x | \<checkmark>(r) \<Rightarrow> \<Omega> P r\<close>


lemma not_initial_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>e \<notin> initials P \<Longrightarrow> P after\<^sub>\<checkmark> e = (case e of ev x \<Rightarrow> \<Psi> P x | \<checkmark>(r) \<Rightarrow> \<Omega> P r)\<close>
  by (auto simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After_BOT intro: not_initial_After split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)

lemma initials_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k: 
  \<open>(P after\<^sub>\<checkmark> e)\<^sup>0 =
   (case e of \<checkmark>(r) \<Rightarrow> (\<Omega> P r)\<^sup>0
            | ev a \<Rightarrow> if ev a \<in> P\<^sup>0 then {e. [ev a, e] \<in> \<T> P} else (\<Psi> P a)\<^sup>0)\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def initials_After split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split) 


subsection \<open>Projections\<close>

lemma F_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k: 
  \<open>\<F> (P after\<^sub>\<checkmark> e) =
   (case e of \<checkmark>(r) \<Rightarrow> \<F> (\<Omega> P r)
            | ev a \<Rightarrow> if ev a \<in> P\<^sup>0 then {(s, X). (ev a # s, X) \<in> \<F> P} else \<F> (\<Psi> P a))\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def F_After split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)

lemma D_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>\<D> (P after\<^sub>\<checkmark> e) =
   (case e of \<checkmark>(r) \<Rightarrow> \<D> (\<Omega> P r)
            | ev a \<Rightarrow> if ev a \<in> P\<^sup>0 then {s. ev a # s \<in> \<D> P} else \<D> (\<Psi> P a))\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def D_After split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)

lemma T_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>\<T> (P after\<^sub>\<checkmark> e) =
   (case e of \<checkmark>(r) \<Rightarrow> \<T> (\<Omega> P r)
            | ev a \<Rightarrow> if ev a \<in> P\<^sup>0 then {s. ev a # s \<in> \<T> P} else \<T> (\<Psi> P a))\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def T_After split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)



subsection \<open>Monotony\<close>

lemma mono_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_T  :
  \<open>e \<in> Q\<^sup>0 \<Longrightarrow> (case e of \<checkmark>(r) \<Rightarrow> \<Omega> P r \<sqsubseteq>\<^sub>T \<Omega> Q r)  \<Longrightarrow> P \<sqsubseteq>\<^sub>T Q  \<Longrightarrow> P after\<^sub>\<checkmark> e \<sqsubseteq>\<^sub>T Q after\<^sub>\<checkmark> e\<close>
  and mono_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_F  :
  \<open>e \<in> Q\<^sup>0 \<Longrightarrow> (case e of \<checkmark>(r) \<Rightarrow> \<Omega> P r \<sqsubseteq>\<^sub>F \<Omega> Q r)  \<Longrightarrow> P \<sqsubseteq>\<^sub>F Q  \<Longrightarrow> P after\<^sub>\<checkmark> e \<sqsubseteq>\<^sub>F Q after\<^sub>\<checkmark> e\<close>
  and mono_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_D  :
  \<open>e \<in> Q\<^sup>0 \<Longrightarrow> (case e of \<checkmark>(r) \<Rightarrow> \<Omega> P r \<sqsubseteq>\<^sub>D \<Omega> Q r)  \<Longrightarrow> P \<sqsubseteq>\<^sub>D Q  \<Longrightarrow> P after\<^sub>\<checkmark> e \<sqsubseteq>\<^sub>D Q after\<^sub>\<checkmark> e\<close>
  and mono_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD :
  \<open>e \<in> Q\<^sup>0 \<Longrightarrow> (case e of \<checkmark>(r) \<Rightarrow> \<Omega> P r \<sqsubseteq>\<^sub>F\<^sub>D \<Omega> Q r) \<Longrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> P after\<^sub>\<checkmark> e \<sqsubseteq>\<^sub>F\<^sub>D Q after\<^sub>\<checkmark> e\<close>
  and mono_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DT :
  \<open>e \<in> Q\<^sup>0 \<Longrightarrow> (case e of \<checkmark>(r) \<Rightarrow> \<Omega> P r \<sqsubseteq>\<^sub>D\<^sub>T \<Omega> Q r) \<Longrightarrow> P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> P after\<^sub>\<checkmark> e \<sqsubseteq>\<^sub>D\<^sub>T Q after\<^sub>\<checkmark> e\<close>
  using mono_After_T mono_After_F mono_After_D mono_After_FD mono_After_DT
  by (auto simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)

lemma mono_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>\<lbrakk>P \<sqsubseteq> Q;
    (case e of ev a \<Rightarrow> (ev a \<in> Q\<^sup>0 \<or> \<Psi> P a \<sqsubseteq> \<Psi> Q a));
    (case e of \<checkmark>(r) \<Rightarrow> \<Omega> P r \<sqsubseteq> \<Omega> Q r)\<rbrakk> \<Longrightarrow>
   P after\<^sub>\<checkmark> e \<sqsubseteq> Q after\<^sub>\<checkmark> e\<close>
  by (force simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split intro: mono_After)



subsection \<open>Behaviour of @{const [source] After\<^sub>t\<^sub>i\<^sub>c\<^sub>k} with \<^const>\<open>STOP\<close>, \<^const>\<open>SKIP\<close> and \<^term>\<open>\<bottom>\<close>\<close>

lemma After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP: \<open>STOP after\<^sub>\<checkmark> e = (case e of ev a \<Rightarrow> \<Psi> STOP a | \<checkmark>(r) \<Rightarrow> \<Omega> STOP r)\<close>
  and After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP: \<open>SKIP r after\<^sub>\<checkmark> e = (case e of ev a \<Rightarrow> \<Psi> (SKIP r) a | \<checkmark>(s) \<Rightarrow> \<Omega> (SKIP r) s)\<close>
  and After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_BOT : \<open>\<bottom> after\<^sub>\<checkmark> e = (case e of ev x \<Rightarrow> \<bottom> | \<checkmark>(r) \<Rightarrow> \<Omega> \<bottom> r)\<close>
  by (simp_all add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After_STOP After_SKIP After_BOT split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)


lemma After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_BOT_iff:
  \<open>P after\<^sub>\<checkmark> e = \<bottom> \<longleftrightarrow> 
   (case e of \<checkmark>(r) \<Rightarrow> \<Omega> P r = \<bottom>
            | ev a \<Rightarrow> if ev a \<in> P\<^sup>0 then [ev a] \<in> \<D> P else \<Psi> P a = \<bottom>)\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After_is_BOT_iff split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)



subsection \<open>Behaviour of @{const [source] After\<^sub>t\<^sub>i\<^sub>c\<^sub>k} with Operators of \<^session>\<open>HOL-CSP\<close>\<close>

text \<open>Here again, we lose determinism.\<close>

lemma After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix_is_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix: 
  \<open>a \<in> A \<Longrightarrow> (\<box>a \<in> A \<rightarrow> P a) after\<^sub>\<checkmark> ev a = (\<sqinter>a \<in> A \<rightarrow> P a) after\<^sub>\<checkmark> ev a\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After_Mprefix_is_After_Mndetprefix)

lemma After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Det_is_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Ndet:
  \<open>ev a \<in> P\<^sup>0 \<union> Q\<^sup>0 \<Longrightarrow> (P \<box> Q) after\<^sub>\<checkmark> ev a = (P \<sqinter> Q) after\<^sub>\<checkmark> ev a\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After_Det_is_After_Ndet)

lemma After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sliding_is_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Ndet:
  \<open>ev a \<in> P\<^sup>0 \<union> Q\<^sup>0 \<Longrightarrow> (P \<rhd> Q) after\<^sub>\<checkmark> ev a = (P \<sqinter> Q) after\<^sub>\<checkmark> ev a\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After_Sliding_is_After_Ndet)


lemma After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Ndet: 
  \<open>(P \<sqinter> Q) after\<^sub>\<checkmark> e =
   (case e of \<checkmark>(r) \<Rightarrow> \<Omega> (P \<sqinter> Q) r
            | ev a \<Rightarrow>   if ev a \<in> P\<^sup>0 \<inter> Q\<^sup>0
                      then P after\<^sub>\<checkmark> ev a \<sqinter> Q after\<^sub>\<checkmark> ev a
                      else   if ev a \<in> P\<^sup>0
                           then P after\<^sub>\<checkmark> ev a
                           else  if ev a \<in> Q\<^sup>0
                                then Q after\<^sub>\<checkmark> ev a
                                else \<Psi> (P \<sqinter> Q) a)\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After_Ndet split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)

lemma After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Det: 
  \<open>(P \<box> Q) after\<^sub>\<checkmark> e =
   (case e of \<checkmark>(r) \<Rightarrow> \<Omega> (P \<box> Q) r
            | ev a \<Rightarrow>   if ev a \<in> P\<^sup>0 \<inter> Q\<^sup>0
                      then P after\<^sub>\<checkmark> ev a \<sqinter> Q after\<^sub>\<checkmark> ev a
                      else   if ev a \<in> P\<^sup>0
                           then P after\<^sub>\<checkmark> ev a
                           else  if ev a \<in> Q\<^sup>0
                                then Q after\<^sub>\<checkmark> ev a
                                else \<Psi> (P \<box> Q) a)\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After_Det split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)

lemma After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sliding: 
  \<open>(P \<rhd> Q) after\<^sub>\<checkmark> e =
   (case e of \<checkmark>(r) \<Rightarrow> \<Omega> (P \<rhd> Q) r
            | ev a \<Rightarrow>   if ev a \<in> P\<^sup>0 \<inter> Q\<^sup>0
                      then P after\<^sub>\<checkmark> ev a \<sqinter> Q after\<^sub>\<checkmark> ev a
                      else   if ev a \<in> P\<^sup>0
                           then P after\<^sub>\<checkmark> ev a
                           else  if ev a \<in> Q\<^sup>0
                                then Q after\<^sub>\<checkmark> ev a
                                else \<Psi> (P \<rhd> Q) a)\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After_Sliding split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)


lemma After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix: 
  \<open>(\<box> a \<in> A \<rightarrow> P a) after\<^sub>\<checkmark> e =
   (case e of \<checkmark>(r) \<Rightarrow> \<Omega> (\<box> a \<in> A \<rightarrow> P a) r
            | ev a \<Rightarrow> if a \<in> A then P a else \<Psi> (\<box> a \<in> A \<rightarrow> P a) a)\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After_Mprefix split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)

lemma After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix: 
  \<open>(\<sqinter> a \<in> A \<rightarrow> P a) after\<^sub>\<checkmark> e =
   (case e of \<checkmark>(r) \<Rightarrow> \<Omega> (\<sqinter> a \<in> A \<rightarrow> P a) r
            | ev a \<Rightarrow> if a \<in> A then P a else \<Psi> (\<sqinter> a \<in> A \<rightarrow> P a) a)\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After_Mndetprefix split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)

corollary After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0:
  \<open>(a \<rightarrow> P) after\<^sub>\<checkmark> e =
   (case e of \<checkmark>(r) \<Rightarrow> \<Omega> (a \<rightarrow> P) r
            | ev b \<Rightarrow> if b = a then P else \<Psi> (a \<rightarrow> P) b)\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After_write0 split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)

corollary \<open>(a \<rightarrow> P) after\<^sub>\<checkmark> ev a = P\<close> by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0)

corollary After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read:
  \<open>(c\<^bold>?a\<in>A \<rightarrow> P a) after\<^sub>\<checkmark> e =
   (case e of \<checkmark>(r) \<Rightarrow> \<Omega> (c\<^bold>?a\<in>A \<rightarrow> P a) r
            | ev b \<Rightarrow> if b \<in> c ` A then P (inv_into A c b) else \<Psi> (c\<^bold>?a\<in>A \<rightarrow> P a) b)\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After_read split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)

corollary After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write:
  \<open>(c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) after\<^sub>\<checkmark> e =
   (case e of \<checkmark>(r) \<Rightarrow> \<Omega> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) r
            | ev b \<Rightarrow> if b \<in> c ` A then P (inv_into A c b) else \<Psi> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) b)\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After_ndet_write split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)


lemma After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq: 
  \<open>(P \<^bold>; Q) after\<^sub>\<checkmark> e =
   (case e of \<checkmark>(r) \<Rightarrow> \<Omega> (P \<^bold>; Q) r
            | ev a \<Rightarrow>   if range tick \<inter> P\<^sup>0 = {} \<or> (\<forall>r. \<checkmark>(r) \<in> P\<^sup>0 \<longrightarrow> ev a \<notin> Q\<^sup>0)
                      then if ev a \<in> P\<^sup>0 then P after\<^sub>\<checkmark> ev a \<^bold>; Q else \<Psi> (P \<^bold>; Q) a
                      else   if ev a \<in> P\<^sup>0 then (P after\<^sub>\<checkmark> ev a \<^bold>; Q) \<sqinter> Q after\<^sub>\<checkmark> ev a
                           else Q after\<^sub>\<checkmark> ev a)\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After_Seq split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)


lemma After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync: 
  \<open>(P \<lbrakk>S\<rbrakk> Q) after\<^sub>\<checkmark> e = 
   (case e of \<checkmark>(r) \<Rightarrow> \<Omega> (P \<lbrakk>S\<rbrakk> Q) r
            | ev a \<Rightarrow>   if P = \<bottom> \<or> Q = \<bottom> then \<bottom>
                      else   if ev a \<in> P\<^sup>0 \<inter> Q\<^sup>0
                           then   if a \<in> S then P after\<^sub>\<checkmark> ev a \<lbrakk>S\<rbrakk> Q after\<^sub>\<checkmark> ev a
                                else (P after\<^sub>\<checkmark> ev a \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after\<^sub>\<checkmark> ev a)
                           else   if ev a \<in> P\<^sup>0 \<and> a \<notin> S then P after\<^sub>\<checkmark> ev a \<lbrakk>S\<rbrakk> Q
                                else   if ev a \<in> Q\<^sup>0 \<and> a \<notin> S then P \<lbrakk>S\<rbrakk> Q after\<^sub>\<checkmark> ev a
                                     else \<Psi> (P \<lbrakk>S\<rbrakk> Q) a)\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After_Sync split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split) 


lemma Hiding_FD_Hiding_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_if_initial_inside:
  \<open>ev a \<in> P\<^sup>0 \<Longrightarrow> a \<in> A \<Longrightarrow> P \ A \<sqsubseteq>\<^sub>F\<^sub>D P after\<^sub>\<checkmark> ev a \ A\<close>
  and After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Hiding_FD_Hiding_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_if_initial_notin:
  \<open>ev a \<in> P\<^sup>0 \<Longrightarrow> a \<notin> A \<Longrightarrow> (P \ A) after\<^sub>\<checkmark> ev a \<sqsubseteq>\<^sub>F\<^sub>D P after\<^sub>\<checkmark> ev a \ A\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def Hiding_FD_Hiding_After_if_initial_inside)
    (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After_Hiding_FD_Hiding_After_if_initial_notin)


lemmas Hiding_F_Hiding_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_if_initial_inside = 
  Hiding_FD_Hiding_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_if_initial_inside[THEN leFD_imp_leF]
  and After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Hiding_F_Hiding_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_if_initial_notin = 
  After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Hiding_FD_Hiding_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_if_initial_notin[THEN leFD_imp_leF]
  and Hiding_D_Hiding_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_if_initial_inside = 
  Hiding_FD_Hiding_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_if_initial_inside[THEN leFD_imp_leD]
  and After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Hiding_D_Hiding_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_if_initial_notin = 
  After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Hiding_FD_Hiding_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_if_initial_notin[THEN leFD_imp_leD]
  and Hiding_T_Hiding_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_if_initial_inside = 
  Hiding_FD_Hiding_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_if_initial_inside[THEN leFD_imp_leF, THEN leF_imp_leT]   
  and After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Hiding_T_Hiding_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_if_initial_notin = 
  After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Hiding_FD_Hiding_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_if_initial_notin[THEN leFD_imp_leF, THEN leF_imp_leT]

corollary Hiding_DT_Hiding_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_if_initial_inside:
  \<open>ev a \<in> P\<^sup>0 \<Longrightarrow> a \<in> A \<Longrightarrow> P \ A \<sqsubseteq>\<^sub>D\<^sub>T P after\<^sub>\<checkmark> ev a \ A\<close>
  and After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Hiding_DT_Hiding_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_if_initial_notin: 
  \<open>ev a \<in> P\<^sup>0 \<Longrightarrow> a \<notin> A \<Longrightarrow> (P \ A) after\<^sub>\<checkmark> ev a \<sqsubseteq>\<^sub>D\<^sub>T P after\<^sub>\<checkmark> ev a \ A\<close>
  by (simp add: Hiding_D_Hiding_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_if_initial_inside 
      Hiding_T_Hiding_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_if_initial_inside leD_leT_imp_leDT)
    (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Hiding_D_Hiding_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_if_initial_notin 
      After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Hiding_T_Hiding_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_if_initial_notin leD_leT_imp_leDT)

end

text \<open>As with \<^locale>\<open>After\<close>, we need to "duplicate" the locale
      to formalize the result for the \<^const>\<open>Renaming\<close> operator.\<close>

locale AfterExtDuplicated = After\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>\<alpha>: AfterExt \<Psi>\<^sub>\<alpha> \<Omega>\<^sub>\<alpha> + After\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>\<beta>: AfterExt \<Psi>\<^sub>\<beta> \<Omega>\<^sub>\<beta>
  for \<Psi>\<^sub>\<alpha> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega>\<^sub>\<alpha> :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Psi>\<^sub>\<beta> :: \<open>[('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'b] \<Rightarrow> ('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and \<Omega>\<^sub>\<beta> :: \<open>[('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 's] \<Rightarrow> ('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> 

sublocale AfterExtDuplicated \<subseteq> AfterDuplicated .
    \<comment>\<open>Recovering @{thm [source] AfterDuplicated.After_Renaming}\<close>

context AfterExtDuplicated
begin 

notation After\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>\<alpha>.After (infixl \<open>after\<^sub>\<alpha>\<close> 86)
notation After\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>\<beta>.After (infixl \<open>after\<^sub>\<beta>\<close> 86)
notation After\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>\<alpha>.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k (infixl \<open>after\<^sub>\<checkmark>\<^sub>\<alpha>\<close> 86)
notation After\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>\<beta>.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k (infixl \<open>after\<^sub>\<checkmark>\<^sub>\<beta>\<close> 86)

lemma After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Renaming:
  \<open>Renaming P f g after\<^sub>\<checkmark>\<^sub>\<beta> e =
   (case e of \<checkmark>(s) \<Rightarrow> \<Omega>\<^sub>\<beta> (Renaming P f g) s
            | ev b \<Rightarrow>   if P = \<bottom> then \<bottom>
                      else   if \<exists>a. ev a \<in> P\<^sup>0 \<and> f a = b
                           then \<sqinter> a\<in>{a. ev a \<in> P\<^sup>0 \<and> f a = b}. Renaming (P after\<^sub>\<alpha> a) f g
                           else \<Psi>\<^sub>\<beta> (Renaming P f g) b)\<close>
  by (auto simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>\<alpha>.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>\<beta>.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def 
      After_Renaming split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)

end


context AfterExt \<comment>\<open>Back to \<^locale>\<open>AfterExt\<close>.\<close>
begin

subsection \<open>Behaviour of @{const [source] After\<^sub>t\<^sub>i\<^sub>c\<^sub>k} with Operators of \<^session>\<open>HOL-CSPM\<close>\<close>

lemma After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_GlobalDet_is_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_GlobalNdet:
  \<open>ev a \<in> (\<Union>a \<in> A. (P a)\<^sup>0) \<Longrightarrow>
   (\<box> a \<in> A. P a) after\<^sub>\<checkmark> ev a = (\<sqinter> a \<in> A. P a) after\<^sub>\<checkmark> ev a\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After_GlobalDet_is_After_GlobalNdet)

lemma After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_GlobalNdet: 
  \<open>(\<sqinter> a \<in> A. P a) after\<^sub>\<checkmark> e =
   (case e of \<checkmark>(r) \<Rightarrow> \<Omega> (\<sqinter> a \<in> A. P a) r
            | ev a \<Rightarrow>   if ev a \<in> (\<Union>a \<in> A. (P a)\<^sup>0)
                      then \<sqinter> x \<in> {x \<in> A. ev a \<in> (P x)\<^sup>0}. P x after\<^sub>\<checkmark> ev a
                      else \<Psi> (\<sqinter> a \<in> A. P a) a)\<close>
  and After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_GlobalDet: 
  \<open>(\<box> a \<in> A. P a) after\<^sub>\<checkmark> e = 
   (case e of \<checkmark>(r) \<Rightarrow> \<Omega> (\<box> a \<in> A. P a) r
            | ev a \<Rightarrow>   if ev a \<in> (\<Union>a \<in> A. (P a)\<^sup>0)
                      then \<sqinter> x \<in> {x \<in> A. ev a \<in> (P x)\<^sup>0}. P x after\<^sub>\<checkmark> ev a
                      else \<Psi> (\<box> a \<in> A. P a) a)\<close>
  by (simp_all add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After_GlobalNdet After_GlobalDet split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)


(* TODO: formulate and prove for MultiSync and MultiSeq *)


lemma After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Throw:
  \<open>(P \<Theta> a \<in> A. Q a) after\<^sub>\<checkmark> e = 
   (case e of \<checkmark>(r) \<Rightarrow> \<Omega> (P \<Theta> a \<in> A. Q a) r
            | ev a \<Rightarrow>   if P = \<bottom> then \<bottom>
                      else   if ev a \<in> P\<^sup>0
                           then   if a \<in> A
                                then Q a
                                else P after\<^sub>\<checkmark> ev a \<Theta> a \<in> A. Q a
                           else \<Psi> (P \<Theta> a \<in> A. Q a) a)\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After_Throw split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)


lemma After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Interrupt:
  \<open>(P \<triangle> Q) after\<^sub>\<checkmark> e = 
   (case e of \<checkmark>(r) \<Rightarrow> \<Omega> (P \<triangle> Q) r
            | ev a \<Rightarrow>   if ev a \<in> P\<^sup>0 \<inter> Q\<^sup>0
                      then Q after\<^sub>\<checkmark> ev a \<sqinter> (P after\<^sub>\<checkmark> ev a \<triangle> Q)
                      else   if ev a \<in> P\<^sup>0 \<and> ev a \<notin> Q\<^sup>0
                           then P after\<^sub>\<checkmark> ev a \<triangle> Q
                           else   if ev a \<notin> P\<^sup>0 \<and> ev a \<in> Q\<^sup>0
                                then Q after\<^sub>\<checkmark> ev a 
                                else \<Psi> (P \<triangle> Q) a)\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After_Interrupt split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)



subsection \<open>Behaviour of @{const [source] After\<^sub>t\<^sub>i\<^sub>c\<^sub>k} with Reference Processes\<close>

lemma After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DF: 
  \<open>DF A after\<^sub>\<checkmark> e =
   (case e of \<checkmark>(r) \<Rightarrow> \<Omega> (DF A) r
            | ev a \<Rightarrow> if a \<in> A then DF A else \<Psi> (DF A) a)\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After_DF split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)

lemma After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S:
  \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R after\<^sub>\<checkmark> e =
   (case e of \<checkmark>(r) \<Rightarrow> \<Omega> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) r
            | ev a \<Rightarrow> if a \<in> A then DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R else \<Psi> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) a)\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)

lemma After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_RUN:
  \<open>RUN A after\<^sub>\<checkmark> e =
   (case e of \<checkmark>(r) \<Rightarrow> \<Omega> (RUN A) r
            | ev a \<Rightarrow> if a \<in> A then RUN A else \<Psi> (RUN A) a)\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After_RUN split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)

lemma After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_CHAOS:
  \<open>CHAOS A after\<^sub>\<checkmark> e =
   (case e of \<checkmark>(r) \<Rightarrow> \<Omega> (CHAOS A) r
            | ev a \<Rightarrow> if a \<in> A then CHAOS A else \<Psi> (CHAOS A) a)\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After_CHAOS split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)

lemma After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S:
  \<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R after\<^sub>\<checkmark> e =
   (case e of \<checkmark>(r) \<Rightarrow> \<Omega> (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) r
            | ev a \<Rightarrow> if a \<in> A then CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R else \<Psi> (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R) a)\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def After_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)



lemma DF_FD_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>DF A \<sqsubseteq>\<^sub>F\<^sub>D P \<Longrightarrow> e \<in> P\<^sup>0 \<Longrightarrow> DF A \<sqsubseteq>\<^sub>F\<^sub>D P after\<^sub>\<checkmark> e\<close>
  by (cases e, simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def DF_FD_After)
    (metis anti_mono_initials_FD event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.distinct(1) image_iff initials_DF subsetD)

lemma DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R \<sqsubseteq>\<^sub>F\<^sub>D P \<Longrightarrow> ev a \<in> P\<^sup>0 \<Longrightarrow> DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S A R \<sqsubseteq>\<^sub>F\<^sub>D P after\<^sub>\<checkmark> ev a\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_FD_After)



lemma deadlock_free_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>e \<in> P\<^sup>0 \<Longrightarrow> deadlock_free P \<Longrightarrow>
    deadlock_free (P after\<^sub>\<checkmark> e) \<longleftrightarrow>
    (case e of ev a \<Rightarrow> True | \<checkmark>(r) \<Rightarrow> deadlock_free (\<Omega> P r))\<close>
  using deadlock_free_After by (auto simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)

lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>e \<in> P\<^sup>0 \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<Longrightarrow>
    deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P after\<^sub>\<checkmark> e) \<longleftrightarrow>
    (case e of ev a \<Rightarrow> True  | \<checkmark>(r) \<Rightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (\<Omega> P r))\<close>
  using deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_After by (auto simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)



subsection \<open>Characterizations for Deadlock Freeness\<close> 

lemma deadlock_free_imp_not_initial_tick: \<open>deadlock_free P \<Longrightarrow> range tick \<inter> P\<^sup>0 = {}\<close>
  by (rule ccontr, simp add: disjoint_iff)
    (meson anti_mono_initials_FD deadlock_free_def initial_tick_iff_FD_SKIP non_deadlock_free_SKIP subsetD)

lemma initial_tick_imp_range_ev_in_refusals: \<open>\<checkmark>(r) \<in> P\<^sup>0 \<Longrightarrow> range ev \<in> \<R> P\<close>
  unfolding initials_def image_def
  by (simp add: Refusals_iff is_processT6_TR_notin)

lemma deadlock_free_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_characterization: 
  \<open>deadlock_free P \<longleftrightarrow> range ev \<notin> \<R> P \<and> (\<forall>e. ev e \<in> P\<^sup>0 \<longrightarrow> deadlock_free (P after\<^sub>\<checkmark> ev e))\<close>
  (is \<open>deadlock_free P \<longleftrightarrow> ?rhs\<close>)
proof (intro iffI)
  from event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust_sel have \<open>range ev = UNIV - range tick\<close> by blast
  hence \<open>range ev \<notin> \<R> P \<longleftrightarrow> UNIV - range tick \<notin> \<R> P\<close> by metis
  thus \<open>deadlock_free P \<Longrightarrow> ?rhs\<close>
    by (intro conjI)
      (solves \<open>simp add: deadlock_free_F failure_refine_def,
                subst (asm) F_DF, auto simp add: Refusals_iff\<close>,
        use DF_FD_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k deadlock_free_def in blast)
next
  assume \<open>?rhs\<close>
  hence * : \<open>range ev \<notin> \<R> P\<close>
    \<open>ev e \<in> P\<^sup>0 \<Longrightarrow> {(s, X) |s X. (ev e # s, X) \<in> \<F> P} \<subseteq> \<F> (DF UNIV)\<close> for e
    by (simp_all add: deadlock_free_F failure_refine_def F_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k subset_iff)
  show \<open>deadlock_free P\<close>
  proof (unfold deadlock_free_F failure_refine_def, safe)
    fix s X
    assume ** : \<open>(s, X) \<in> \<F> P\<close>
    show \<open>(s, X) \<in> \<F> (DF UNIV)\<close>
    proof (cases s)
      show \<open>s = [] \<Longrightarrow> (s, X) \<in> \<F> (DF UNIV)\<close>
        by (subst F_DF, simp)
          (metis "*"(1) "**" Refusals_iff image_subset_iff is_processT4)
    next
      fix e s'
      assume *** : \<open>s = e # s'\<close>
      from "**"[THEN F_T, simplified this, THEN initials_memI]
        initial_tick_imp_range_ev_in_refusals "*"(1)
      obtain x where \<open>e = ev x\<close> \<open>ev x \<in> P\<^sup>0\<close>
        by (cases e) (simp_all add: initial_tick_imp_range_ev_in_refusals)
      with "*"(2)[OF this(2)] "**" "***" show \<open>(s, X) \<in> \<F> (DF UNIV)\<close>
        by (subst F_DF) (simp add: subset_iff)
    qed
  qed
qed



lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_characterization: 
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<longleftrightarrow> 
   UNIV \<notin> \<R> P \<and> (\<forall>e \<in> P\<^sup>0 - range tick. deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P after\<^sub>\<checkmark> e))\<close>
  (is \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P \<longleftrightarrow> ?rhs\<close>)
proof (intro iffI)
  show ?rhs if \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close>
  proof (intro conjI)
    from \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close> show \<open>UNIV \<notin> \<R> P\<close>
      by (simp add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def failure_refine_def)
        (subst (asm) F_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S, auto simp add: Refusals_iff)
  next
    from \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close> show \<open>\<forall>e\<in>P\<^sup>0 - range tick. deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S (P after\<^sub>\<checkmark> e)\<close>
      by (auto simp add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
  qed
next
  assume assm : \<open>?rhs\<close>
  have * : \<open>ev e \<in> P\<^sup>0 \<Longrightarrow> {(s, X) |s X. (ev e # s, X) \<in> \<F> P} \<subseteq> \<F> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S UNIV UNIV)\<close> for e
    using assm[THEN conjunct2, rule_format, of \<open>ev e\<close>, simplified]
    by (simp add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def failure_refine_def F_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k image_iff)
  show \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S P\<close>
  proof (unfold deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_def failure_refine_def, safe)
    fix s X
    assume ** : \<open>(s, X) \<in> \<F> P\<close>
    show \<open>(s, X) \<in> \<F> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S UNIV UNIV)\<close>
    proof (cases s)
      from assm[THEN conjunct1] "**" show \<open>s = [] \<Longrightarrow> (s, X) \<in> \<F> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S UNIV UNIV)\<close>
        by (subst F_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S, simp add: Refusals_iff)
          (metis UNIV_eq_I event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust)
    next
      fix e s'
      assume *** : \<open>s = e # s'\<close>
      show \<open>(s, X) \<in> \<F> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S UNIV UNIV)\<close>
      proof (cases e)
        fix a assume \<open>e = ev a\<close>
        with "**" "***" initials_memI F_T have \<open>ev a \<in> P\<^sup>0\<close> by blast
        with "*"[OF this] "**" "***" \<open>e = ev a\<close> show \<open>(s, X) \<in> \<F> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S UNIV UNIV)\<close>
          by (subst F_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S) (simp add: subset_iff)
      next
        fix r assume \<open>e = \<checkmark>(r)\<close>
        hence \<open>s = [\<checkmark>(r)]\<close>
          by (metis "**" "***" event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(2) front_tickFree_Cons_iff is_processT2)
        thus \<open>(s, X) \<in> \<F> (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S UNIV UNIV)\<close>
          by (subst F_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S, simp)
      qed
    qed
  qed
qed



subsection \<open>Continuity\<close>

lemma After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_cont [simp] : 
  assumes cont_\<Psi>\<Omega> : \<open>case e of ev a \<Rightarrow> cont (\<lambda>P. \<Psi> P a) | \<checkmark>(r) \<Rightarrow> cont (\<lambda>P. \<Omega> P r)\<close>
    and cont_f : \<open>cont f\<close>
  shows \<open>cont (\<lambda>x. f x after\<^sub>\<checkmark> e)\<close>
  by (cases e, simp_all add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
    (use After_cont cont_\<Psi>\<Omega> cont_f in \<open>auto intro: cont_compose\<close>)



end


(*<*)
end
  (*>*)