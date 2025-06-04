(***********************************************************************************
 * Copyright (c) 2025 Université Paris-Saclay
 *
 * Author: Benoît Ballenghien, Université Paris-Saclay,
           CNRS, ENS Paris-Saclay, LMF
 * Author: Burkhart Wolff, Université Paris-Saclay,
           CNRS, ENS Paris-Saclay, LMF
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


section \<open>Constructiveness of Prefixes\<close>

(*<*)
theory Prefixes_Constructive
  imports Process_Restriction_Space
begin
  (*>*)

subsection \<open>Equality\<close>

lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix :
  \<open>\<box>a \<in> A \<rightarrow> P a \<down> n = (case n of 0 \<Rightarrow> \<bottom> | Suc m \<Rightarrow> \<box>a\<in>A \<rightarrow> (P a \<down> m))\<close> (is \<open>?lhs = ?rhs\<close>)
proof (cases n)
  show \<open>n = 0 \<Longrightarrow> ?lhs = ?rhs\<close> by simp
next
  fix m assume \<open>n = Suc m\<close>
  show \<open>?lhs = ?rhs\<close>
  proof (rule Process_eq_optimizedI)
    show \<open>t \<in> \<D> ?lhs \<Longrightarrow> t \<in> \<D> ?rhs\<close> for t
      by (auto simp add: \<open>n = Suc m\<close> Mprefix_projs D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) blast
  next
    fix t assume \<open>t \<in> \<D> ?rhs\<close>
    with D_imp_front_tickFree obtain a t'
      where \<open>a \<in> A\<close> \<open>t = ev a # t'\<close> \<open>ftF t'\<close> \<open>t' \<in> \<D> (P a \<down> m)\<close>
      by (auto simp add: \<open>n = Suc m\<close> D_Mprefix)
    thus \<open>t \<in> \<D> ?lhs\<close>
      by (simp add: \<open>n = Suc m\<close> D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Mprefix_projs)
        (metis append_Cons event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) length_Cons tickFree_Cons_iff)
  next
    show \<open>(t, X) \<in> \<F> ?lhs \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> for t X
      by (auto simp add: \<open>n = Suc m\<close> restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs Mprefix_projs)
  next
    show \<open>(t, X) \<in> \<F> ?rhs \<Longrightarrow> t \<notin> \<D> ?rhs \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for t X
      by (auto simp add: \<open>n = Suc m\<close> restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs Mprefix_projs)
  qed
qed


lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix :
  \<open>\<sqinter>a \<in> A \<rightarrow> P a \<down> n = (case n of 0 \<Rightarrow> \<bottom> | Suc m \<Rightarrow> \<sqinter>a\<in>A \<rightarrow> (P a \<down> m))\<close> (is \<open>?lhs = ?rhs\<close>)
proof (cases n)
  show \<open>n = 0 \<Longrightarrow> ?lhs = ?rhs\<close> by simp
next
  fix m assume \<open>n = Suc m\<close>
  show \<open>?lhs = ?rhs\<close>
  proof (rule Process_eq_optimizedI)
    show \<open>t \<in> \<D> ?lhs \<Longrightarrow> t \<in> \<D> ?rhs\<close> for t
      by (auto simp add: \<open>n = Suc m\<close> Mndetprefix_projs D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) blast
  next
    fix t assume \<open>t \<in> \<D> ?rhs\<close>
    with D_imp_front_tickFree obtain a t'
      where \<open>a \<in> A\<close> \<open>t = ev a # t'\<close> \<open>ftF t'\<close> \<open>t' \<in> \<D> (P a \<down> m)\<close>
      by (auto simp add: \<open>n = Suc m\<close> D_Mndetprefix')
    thus \<open>t \<in> \<D> ?lhs\<close>
      by (simp add: \<open>n = Suc m\<close> D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Mndetprefix_projs)
        (metis append_Cons event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) length_Cons tickFree_Cons_iff)
  next
    show \<open>(t, X) \<in> \<F> ?lhs \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> for t X
      by (auto simp add: \<open>n = Suc m\<close> restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs
          Mndetprefix_projs split: if_split_asm)
  next
    show \<open>(t, X) \<in> \<F> ?rhs \<Longrightarrow> t \<notin> \<D> ?rhs \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for t X
      by (auto simp add: \<open>n = Suc m\<close> restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs
          Mndetprefix_projs split: if_split_asm)
  qed
qed


corollary restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0 :
  \<open>a \<rightarrow> P \<down> n = (case n of 0 \<Rightarrow> \<bottom> | Suc m \<Rightarrow> a \<rightarrow> (P \<down> m))\<close>
  unfolding write0_def by (simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix)


corollary restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write :
  \<open>c\<^bold>!a \<rightarrow> P \<down> n = (case n of 0 \<Rightarrow> \<bottom> | Suc m \<Rightarrow> c\<^bold>!a \<rightarrow> (P \<down> m))\<close>
  unfolding write_def by (simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix)


corollary restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read :
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<down> n = (case n of 0 \<Rightarrow> \<bottom> | Suc m \<Rightarrow> c\<^bold>?a\<in>A \<rightarrow> (P a \<down> m))\<close>
  unfolding read_def comp_def by (simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix)


corollary restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write :
  \<open>c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<down> n = (case n of 0 \<Rightarrow> \<bottom> | Suc m \<Rightarrow> c\<^bold>!\<^bold>!a\<in>A \<rightarrow> (P a \<down> m))\<close>
  unfolding ndet_write_def comp_def by (simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix)



subsection \<open>Constructiveness\<close>

lemma Mprefix_constructive : \<open>constructive (\<lambda>P. \<box>a \<in> A \<rightarrow> P a)\<close>
  by (auto intro: constructiveI
      simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix restriction_fun_def)

lemma Mndetprefix_constructive : \<open>constructive (\<lambda>P. \<sqinter>a \<in> A \<rightarrow> P a)\<close>
  by (auto intro: constructiveI
      simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mndetprefix restriction_fun_def)

lemma write0_constructive : \<open>constructive (\<lambda>P. a \<rightarrow> P)\<close>
  by (auto intro: constructiveI simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0)

lemma write_constructive : \<open>constructive (\<lambda>P. c\<^bold>!a \<rightarrow> P)\<close>
  by (auto intro: constructiveI simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write)

lemma read_constructive : \<open>constructive (\<lambda>P. c\<^bold>?a \<in> A \<rightarrow> P a)\<close>
  by (auto intro: constructiveI
      simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_read restriction_fun_def)

lemma ndet_write_constructive : \<open>constructive (\<lambda>P. c\<^bold>!\<^bold>!a \<in> A \<rightarrow> P a)\<close>
  by (auto intro: constructiveI
      simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ndet_write restriction_fun_def)


(*<*)
end
  (*>*)