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


section \<open>Non Destructiveness of Synchronization Product\<close>

(*<*)
theory Synchronization_Product_Non_Destructive
  imports Process_Restriction_Space "HOL-CSPM.CSPM"
begin
  (*>*)

subsection \<open>Preliminaries\<close>

lemma D_Sync_optimized :
  \<open>\<D> (P \<lbrakk>A\<rbrakk> Q) =
   {v @ w |t u v w. tF v \<and> ftF w \<and>
                    v setinterleaves ((t, u), range tick \<union> ev ` A) \<and>
                    (t \<in> \<D> P \<and> u \<in> \<T> Q \<or> t \<in> \<D> Q \<and> u \<in> \<T> P)}\<close>
  (is \<open>_ = ?rhs\<close>)
proof (intro subset_antisym subsetI)
  show \<open>d \<in> ?rhs \<Longrightarrow> d \<in> \<D> (P \<lbrakk>A\<rbrakk> Q)\<close> for d
    by (auto simp add: D_Sync)
next
  fix d assume \<open>d \<in> \<D> (P \<lbrakk>A\<rbrakk> Q)\<close>
  then obtain t u v w
    where * : \<open>d = v @ w\<close> \<open>ftF w\<close> \<open>tF v \<or> w = []\<close>
      \<open>v setinterleaves ((t, u), range tick \<union> ev ` A)\<close>
      \<open>t \<in> \<D> P \<and> u \<in> \<T> Q \<or> t \<in> \<D> Q \<and> u \<in> \<T> P\<close>
    unfolding D_Sync by blast
  show \<open>d \<in> ?rhs\<close>
  proof (cases \<open>tF v\<close>)
    from "*" show \<open>tF v \<Longrightarrow> d \<in> ?rhs\<close> by blast
  next
    assume \<open>\<not> tF v\<close>
    with "*"(1, 3) have \<open>w = []\<close> \<open>d = v\<close> by simp_all
    from D_imp_front_tickFree \<open>d = v\<close> \<open>d \<in> \<D> (P \<lbrakk>A\<rbrakk> Q)\<close>
    have \<open>ftF v\<close> by blast
    with \<open>\<not> tF v\<close> obtain r v' where \<open>v = v' @ [\<checkmark>(r)]\<close>
      by (meson nonTickFree_n_frontTickFree)
    with "*"(4) obtain t' u'
      where ** : \<open>t = t' @ [\<checkmark>(r)]\<close> \<open>u = u' @ [\<checkmark>(r)]\<close>
        \<open>v' setinterleaves ((t', u'), range tick \<union> ev ` A)\<close>
      by (simp add: \<open>v = v' @ [\<checkmark>(r)]\<close>)
        (meson "*"(5) D_imp_front_tickFree SyncWithTick_imp_NTF T_imp_front_tickFree)
    have \<open>t' \<in> \<D> P \<and> u' \<in> \<T> Q \<or> t' \<in> \<D> Q \<and> u' \<in> \<T> P\<close>
      by (metis "*"(5) "**"(1,2) is_processT3_TR_append is_processT9)
    with "**"(3) \<open>d = v\<close> \<open>ftF v\<close> \<open>v = v' @ [\<checkmark>(r)]\<close>
      front_tickFree_nonempty_append_imp show \<open>d \<in> ?rhs\<close> by blast
  qed
qed

lemma tickFree_interleave_iff :
  \<open>t setinterleaves ((u, v), S) \<Longrightarrow> tF t \<longleftrightarrow> tF u \<and> tF v\<close>
  by (induct \<open>(u, S, v)\<close> arbitrary: t u v rule: setinterleaving.induct)
    (auto split: if_split_asm option.split_asm)

lemma interleave_subsetL :
  \<open>tF t \<Longrightarrow> {a. ev a \<in> set u} \<subseteq> A \<Longrightarrow>
   t setinterleaves ((u, v), range tick \<union> ev ` A) \<Longrightarrow> t = v\<close>
  for t u v :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof (induct \<open>(u, range tick \<union> ev ` A :: ('a, 'r) refusal\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, v)\<close>
    arbitrary: t u v rule: setinterleaving.induct)
  case 1 thus ?case by simp
next
  case (2 y v) thus ?case by (auto simp add: image_iff split: if_split_asm)
next
  case (3 x u) thus ?case
    by (simp add: image_iff subset_iff split: if_split_asm)
      (metis (mono_tags, lifting) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust)
next
  case (4 x u y v)
  from "4.prems" show ?case
    apply (simp add: subset_iff split: if_split_asm)
       apply (metis (no_types, lifting) "4.hyps"(1) Un_iff
        mem_Collect_eq subsetI tickFree_Cons_iff)
      apply (metis (no_types, lifting) "4.hyps"(2,4) "4.prems"(2,3) SyncHd_Tl
        SyncSameHdTl list.sel(1) setinterleaving_sym tickFree_Cons_iff)
    by (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust imageI rangeI)+
qed

lemma interleave_subsetR :
  \<open>tF t \<Longrightarrow> {a. ev a \<in> set v} \<subseteq> A \<Longrightarrow>
   t setinterleaves ((u, v), range tick \<union> ev ` A) \<Longrightarrow> t = u\<close>
  by (simp add: interleave_subsetL setinterleaving_sym)


lemma interleave_imp_lengthLR_le :
  \<open>t setinterleaves ((u, v), S) \<Longrightarrow>
   length u \<le> length t \<and> length v \<le> length t\<close>
  by (induct \<open>(u, S, v)\<close> arbitrary: t u v rule: setinterleaving.induct;
      simp split: if_split_asm; use nat_le_linear not_less_eq_eq in fastforce)

lemma interleave_le_prefixLR :
  \<open>t setinterleaves ((u, v), S) \<Longrightarrow> u' \<le> u \<Longrightarrow> v' \<le> v \<Longrightarrow>
   (\<exists>t' \<le> t. \<exists>v'' \<le> v'. t' setinterleaves ((u', v''), S)) \<or>
   (\<exists>t' \<le> t. \<exists>u'' \<le> u'. t' setinterleaves ((u'', v'), S))\<close>
proof (induct \<open>(u, S, v)\<close>
    arbitrary: t u u' v v' rule: setinterleaving.induct)
  case 1
  then show ?case by simp
next
  case (2 y v)
  thus ?case by (simp split: if_split_asm)
      (metis si_empty1 insert_iff nil_le)
next
  case (3 x u)
  thus ?case by (simp split: if_split_asm)
      (metis si_empty1 insert_iff nil_le)
next
  case (4 x u y v)
  show ?case
  proof (cases \<open>u' = [] \<or> v' = []\<close>)
    show \<open>u' = [] \<or> v' = [] \<Longrightarrow> ?case\<close> by force
  next
    assume \<open>\<not> (u' = [] \<or> v' = [])\<close>
    with "4.prems"(2, 3)
    obtain u'' v'' where \<open>u' = x # u''\<close> \<open>u'' \<le> u\<close> \<open>v' = y # v''\<close> \<open>v'' \<le> v\<close>
      by (meson Prefix_Order.prefix_Cons)
    with "4.prems"(1) consider (both_in)   t' where \<open>x \<in> S\<close> \<open>y \<in> S\<close> \<open>x = y\<close> \<open>t = x # t'\<close>
      \<open>t' setinterleaves ((u, v), S)\<close>
    |      (inR_mvL)   t' where \<open>x \<notin> S\<close> \<open>y \<in> S\<close> \<open>t = x # t'\<close>
      \<open>t' setinterleaves ((u, y # v), S)\<close>
    |      (inL_mvR)   t' where \<open>x \<in> S\<close> \<open>y \<notin> S\<close> \<open>t = y # t'\<close>
      \<open>t' setinterleaves ((x # u, v), S)\<close>
    |      (notin_mvL) t' where \<open>x \<notin> S\<close> \<open>y \<notin> S\<close> \<open>t = x # t'\<close>
      \<open>t' setinterleaves ((u, y # v), S)\<close>
    |      (notin_mvR) t' where \<open>x \<notin> S\<close> \<open>y \<notin> S\<close> \<open>t = y # t'\<close>
      \<open>t' setinterleaves ((x # u, v), S)\<close>
      by (auto split: if_split_asm)
    thus ?case
    proof cases
      case both_in
      from "4.hyps"(1)[OF both_in(1-3, 5) \<open>u'' \<le> u\<close> \<open>v'' \<le> v\<close>]
      show ?thesis
      proof (elim disjE exE conjE)
        fix t'' v'''
        assume \<open>t'' \<le> t'\<close> \<open>v''' \<le> v''\<close> \<open>t'' setinterleaves ((u'', v'''), S)\<close>
        hence \<open>y # t'' \<le> t \<and> y # v''' \<le> v' \<and>
              (y # t'') setinterleaves ((u', y # v'''), S)\<close>
          by (simp add: \<open>u' = x # u''\<close> \<open>v' = y # v''\<close> both_in(2-4))
        thus ?thesis by blast
      next
        fix t'' u'''
        assume \<open>t'' \<le> t'\<close> \<open>u''' \<le> u''\<close> \<open>t'' setinterleaves ((u''', v''), S)\<close>
        hence \<open>x # t'' \<le> t \<and> x # u''' \<le> u' \<and>
              (x # t'') setinterleaves ((x # u''', v'), S)\<close>
          by (simp add: \<open>u' = x # u''\<close> \<open>v' = y # v''\<close> both_in(2-4))
        thus ?thesis by blast
      qed
    next
      case inR_mvL
      from "4.hyps"(5)[simplified, OF inR_mvL(1, 2 ,4) \<open>u'' \<le> u\<close> \<open>v' \<le> y # v\<close>]
      show ?thesis
      proof (elim disjE exE conjE)
        fix t'' v'''
        assume \<open>t'' \<le> t'\<close> \<open>v''' \<le> v'\<close> \<open>t'' setinterleaves ((u'', v'''), S)\<close>
        hence \<open>x # t'' \<le> t \<and> v''' \<le> v' \<and>
              (x # t'') setinterleaves ((u', v'''), S)\<close>
          by (cases v''') (simp_all add: \<open>u' = x # u''\<close> \<open>v' = y # v''\<close> inR_mvL(1, 3))
        thus ?thesis by blast
      next
        fix t'' u'''
        assume \<open>t'' \<le> t'\<close> \<open>u''' \<le> u''\<close> \<open>t'' setinterleaves ((u''', v'), S)\<close>
        hence \<open>x # t'' \<le> t \<and> x # u''' \<le> u' \<and>
              (x # t'') setinterleaves ((x # u''', v'), S)\<close>
          by (simp add: \<open>u' = x # u''\<close> \<open>v' = y # v''\<close> inR_mvL(1, 3))
        thus ?thesis by blast
      qed
    next
      case inL_mvR
      from "4.hyps"(2)[OF inL_mvR(1, 2, 4) \<open>u' \<le> x # u\<close> \<open>v'' \<le> v\<close>]
      show ?thesis
      proof (elim disjE exE conjE)
        fix t'' v'''
        assume \<open>t'' \<le> t'\<close> \<open>v''' \<le> v''\<close> \<open>t'' setinterleaves ((u', v'''), S)\<close>
        hence \<open>y # t'' \<le> t \<and> y # v''' \<le> v' \<and>
               (y # t'') setinterleaves ((u', y # v'''), S)\<close>
          by (simp add: \<open>u' = x # u''\<close> \<open>v' = y # v''\<close> inL_mvR(2, 3))
        thus ?thesis by blast
      next
        fix t'' u'''
        assume \<open>t'' \<le> t'\<close> \<open>u''' \<le> u'\<close> \<open>t'' setinterleaves ((u''', v''), S)\<close>
        hence \<open>y # t'' \<le> t \<and> u''' \<le> u' \<and>
               (y # t'') setinterleaves ((u''', v'), S)\<close>
          by (cases u''') (simp_all add: \<open>u' = x # u''\<close> \<open>v' = y # v''\<close> inL_mvR(2, 3))
        thus ?thesis by blast
      qed
    next
      case notin_mvL
      from "4.hyps"(3)[OF notin_mvL(1, 2, 4) \<open>u'' \<le> u\<close> \<open>v' \<le> y # v\<close>]
      show ?thesis
      proof (elim disjE exE conjE)
        fix t'' v'''
        assume \<open>t'' \<le> t'\<close> \<open>v''' \<le> v'\<close> \<open>t'' setinterleaves ((u'', v'''), S)\<close>
        hence \<open>x # t'' \<le> t \<and> v''' \<le> v' \<and>
               (x # t'') setinterleaves ((u', v'''), S)\<close>
          by (cases v''') (simp_all add: \<open>u' = x # u''\<close> \<open>v' = y # v''\<close> notin_mvL(1, 3))
        thus ?thesis by blast
      next
        fix t'' u'''
        assume \<open>t'' \<le> t'\<close> \<open>u''' \<le> u''\<close> \<open>t'' setinterleaves ((u''', v'), S)\<close>
        hence \<open>x # t'' \<le> t \<and> x # u''' \<le> u' \<and>
               (x # t'') setinterleaves ((x # u''', v'), S)\<close>
          by (simp add: \<open>u' = x # u''\<close> \<open>v' = y # v''\<close> notin_mvL(1, 3))
        thus ?thesis by blast
      qed
    next
      case notin_mvR
      from "4.hyps"(4)[OF notin_mvR(1, 2, 4) \<open>u' \<le> x # u\<close> \<open>v'' \<le> v\<close>]
      show ?thesis
      proof (elim disjE exE conjE)
        fix t'' v'''
        assume \<open>t'' \<le> t'\<close> \<open>v''' \<le> v''\<close> \<open>t'' setinterleaves ((u', v'''), S)\<close>
        hence \<open>y # t'' \<le> t \<and> y # v''' \<le> v' \<and>
               (y # t'') setinterleaves ((u', y # v'''), S)\<close>
          by (simp add: \<open>u' = x # u''\<close> \<open>v' = y # v''\<close> notin_mvR(2, 3))
        thus ?thesis by blast
      next
        fix t'' u'''
        assume \<open>t'' \<le> t'\<close> \<open>u''' \<le> u'\<close> \<open>t'' setinterleaves ((u''', v''), S)\<close>
        hence \<open>y # t'' \<le> t \<and> u''' \<le> u' \<and>
               (y # t'') setinterleaves ((u''', v'), S)\<close>
          by (cases u''') (simp_all add: \<open>u' = x # u''\<close> \<open>v' = y # v''\<close> notin_mvR(2, 3))
        thus ?thesis by blast
      qed
    qed
  qed
qed


lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync_FD_div_oneside :
  assumes \<open>tF u\<close> \<open>ftF v\<close> \<open>t_P \<in> \<D> (P \<down> n)\<close> \<open>t_Q \<in> \<T> (Q \<down> n)\<close>
    \<open>u setinterleaves ((t_P, t_Q), range tick \<union> ev ` A)\<close>
  shows \<open>u @ v \<in> \<D> (P \<lbrakk>A\<rbrakk> Q \<down> n)\<close>
proof (insert assms(3, 4), elim D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
  from assms(1, 2, 5) show \<open>t_P \<in> \<D> P \<Longrightarrow> t_Q \<in> \<T> Q \<Longrightarrow> u @ v \<in> \<D> (P \<lbrakk>A\<rbrakk> Q \<down> n)\<close>
    by (auto simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k D_Sync)
next
  fix t_Q' t_Q''
  assume * : \<open>t_P \<in> \<D> P\<close> \<open>length t_P \<le> n\<close> \<open>t_Q = t_Q' @ t_Q''\<close>
    \<open>t_Q' \<in> \<T> Q\<close> \<open>length t_Q' = n\<close> \<open>tF t_Q'\<close> \<open>ftF t_Q''\<close>
  from \<open>t_Q = t_Q' @ t_Q''\<close> have \<open>t_Q' \<le> t_Q\<close> by simp
  from interleave_le_right[OF assms(5) this]
  obtain t_P' t_P'' u' u''
    where ** : \<open>u = u' @ u''\<close> \<open>t_P = t_P' @ t_P''\<close>
      \<open>u' setinterleaves ((t_P', t_Q'), range tick \<union> ev ` A)\<close>
    by (meson Prefix_Order.prefixE)
  from assms(1) \<open>u = u' @ u''\<close> have \<open>tF u'\<close> by auto
  moreover from "*"(1,4) "**"(2,3) have \<open>u' \<in> \<T> (P \<lbrakk>A\<rbrakk> Q)\<close>
    by (simp add: T_Sync) (metis D_T is_processT3_TR_append)
  moreover have \<open>length t_Q' \<le> length u'\<close>
    using "**"(3) interleave_imp_lengthLR_le by blast
  ultimately have \<open>u' \<in> \<D> (P \<lbrakk>A\<rbrakk> Q \<down> n)\<close>
    by (metis "*"(5) D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI nless_le)
  with "**"(1) assms(1, 2) show \<open>u @ v \<in> \<D> (P \<lbrakk>A\<rbrakk> Q \<down> n)\<close>
    by (metis is_processT7 tickFree_append_iff tickFree_imp_front_tickFree)
next
  fix t_P' t_P''
  assume * : \<open>t_P = t_P' @ t_P''\<close> \<open>t_P' \<in> \<T> P\<close> \<open>length t_P' = n\<close>
    \<open>tF t_P'\<close> \<open>ftF t_P''\<close> \<open>t_Q \<in> \<T> Q\<close> \<open>length t_Q \<le> n\<close>
  from \<open>t_P = t_P' @ t_P''\<close> have \<open>t_P' \<le> t_P\<close> by simp
  from interleave_le_left[OF assms(5) this]
  obtain t_Q' t_Q'' u' u''
    where ** : \<open>u = u' @ u''\<close> \<open>t_Q = t_Q' @ t_Q''\<close>
      \<open>u' setinterleaves ((t_P', t_Q'), range tick \<union> ev ` A)\<close>
    by (meson Prefix_Order.prefixE)
  from assms(1) \<open>u = u' @ u''\<close> have \<open>tF u'\<close> by auto
  moreover from "*"(2,6) "**"(2,3) have \<open>u' \<in> \<T> (P \<lbrakk>A\<rbrakk> Q)\<close>
    by (simp add: T_Sync) (metis is_processT3_TR_append)
  moreover have \<open>length t_P' \<le> length u'\<close>
    using "**"(3) interleave_imp_lengthLR_le by blast
  ultimately have \<open>u' \<in> \<D> (P \<lbrakk>A\<rbrakk> Q \<down> n)\<close>
    by (metis "*"(3) D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI nless_le)
  with "**"(1) assms(1, 2) show \<open>u @ v \<in> \<D> (P \<lbrakk>A\<rbrakk> Q \<down> n)\<close>
    by (metis is_processT7 tickFree_append_iff tickFree_imp_front_tickFree)
next
  fix t_P' t_P'' t_Q' t_Q''
  assume $ : \<open>t_P = t_P' @ t_P''\<close> \<open>t_P' \<in> \<T> P\<close> \<open>length t_P' = n\<close>
    \<open>tF t_P'\<close> \<open>ftF t_P''\<close> \<open>t_Q = t_Q' @ t_Q''\<close> \<open>t_Q' \<in> \<T> Q\<close>
    \<open>length t_Q' = n\<close> \<open>tF t_Q'\<close> \<open>ftF t_Q''\<close>
  from "$"(1, 6) have \<open>t_P' \<le> t_P\<close> \<open>t_Q' \<le> t_Q\<close> by simp_all
  from interleave_le_prefixLR[OF assms(5) this]
  show \<open>u @ v \<in> \<D> (P \<lbrakk>A\<rbrakk> Q \<down> n)\<close>
  proof (elim disjE conjE exE)
    fix u' t_Q''' assume $$ : \<open>u' \<le> u\<close> \<open>t_Q''' \<le> t_Q'\<close>
      \<open>u' setinterleaves ((t_P', t_Q'''), range tick \<union> ev ` A)\<close>
    from "$"(7) "$$"(2) is_processT3_TR have \<open>t_Q''' \<in> \<T> Q\<close> by blast
    with $$(3) \<open>t_P' \<in> \<T> P\<close> have \<open>u' \<in> \<T> (P \<lbrakk>A\<rbrakk> Q)\<close>
      by (auto simp add: T_Sync)
    moreover have \<open>n \<le> length u'\<close>
      using "$"(3) "$$"(3) interleave_imp_lengthLR_le by blast
    ultimately have \<open>u' \<in> \<D> (P \<lbrakk>A\<rbrakk> Q \<down> n)\<close>
      by (metis "$$"(1) D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI Prefix_Order.prefixE
          assms(1) nless_le tickFree_append_iff)
    thus \<open>u @ v \<in> \<D> (P \<lbrakk>A\<rbrakk> Q \<down> n)\<close>
      by (metis "$$"(1) Prefix_Order.prefixE assms(1,2) is_processT7
          tickFree_append_iff tickFree_imp_front_tickFree)
  next
    fix u' t_P''' assume $$ : \<open>u' \<le> u\<close> \<open>t_P''' \<le> t_P'\<close>
      \<open>u' setinterleaves ((t_P''', t_Q'), range tick \<union> ev ` A)\<close>
    from "$"(2) "$$"(2) is_processT3_TR have \<open>t_P''' \<in> \<T> P\<close> by blast
    with $$(3) \<open>t_Q' \<in> \<T> Q\<close> have \<open>u' \<in> \<T> (P \<lbrakk>A\<rbrakk> Q)\<close>
      by (auto simp add: T_Sync)
    moreover have \<open>n \<le> length u'\<close>
      using "$"(8) "$$"(3) interleave_imp_lengthLR_le by blast
    ultimately have \<open>u' \<in> \<D> (P \<lbrakk>A\<rbrakk> Q \<down> n)\<close>
      by (metis "$$"(1) D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI Prefix_Order.prefixE
          assms(1) nless_le tickFree_append_iff)
    thus \<open>u @ v \<in> \<D> (P \<lbrakk>A\<rbrakk> Q \<down> n)\<close>
      by (metis "$$"(1) Prefix_Order.prefixE assms(1,2) is_processT7
          tickFree_append_iff tickFree_imp_front_tickFree)
  qed
qed


subsection \<open>Refinement\<close>



lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync_FD :
  \<open>P \<lbrakk>A\<rbrakk> Q \<down> n \<sqsubseteq>\<^sub>F\<^sub>D (P \<down> n) \<lbrakk>A\<rbrakk> (Q \<down> n)\<close> (is \<open>?lhs \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close>)
proof (unfold refine_defs, safe)
  show \<open>t \<in> \<D> ?rhs \<Longrightarrow> t \<in> \<D> ?lhs\<close> for t
    by (unfold D_Sync_optimized, safe)
      (solves \<open>simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync_FD_div_oneside\<close>,
        metis Sync_commute restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync_FD_div_oneside)
  thus \<open>(t, X) \<in> \<F> ((P \<down> n) \<lbrakk>A\<rbrakk> (Q \<down> n)) \<Longrightarrow> (t, X) \<in> \<F> (P \<lbrakk>A\<rbrakk> Q \<down> n)\<close> for t X
    by (meson is_processT8 le_approx2 mono_Sync restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_approx_self)
qed

text \<open>The equality does not hold in general, but we can establish it
      by adding an assumption over the strict alphabets of the processes.\<close>

lemma strict_events_of_subset_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync :
  \<open>P \<lbrakk>A\<rbrakk> Q \<down> n = (P \<down> n) \<lbrakk>A\<rbrakk> (Q \<down> n)\<close> (is \<open>?lhs = ?rhs\<close>)
  if \<open>\<^bold>\<alpha>(P) \<subseteq> A \<or> \<^bold>\<alpha>(Q) \<subseteq> A\<close>
proof (rule FD_antisym)
  show \<open>?lhs \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close> by (fact restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync_FD)
next
  have div : \<open>t \<in> \<D> (P \<lbrakk>A\<rbrakk> Q) \<Longrightarrow> t \<in> \<D> ?rhs\<close> for t
    by (auto simp add: D_Sync restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)

  { fix t u v assume \<open>t = u @ v\<close> \<open>u \<in> \<T> (P \<lbrakk>A\<rbrakk> Q)\<close> \<open>length u = n\<close> \<open>tF u\<close> \<open>ftF v\<close>
    from this(2) consider \<open>u \<in> \<D> (P \<lbrakk>A\<rbrakk> Q)\<close>
      | t_P t_Q where \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close>
        \<open>u setinterleaves ((t_P, t_Q), range tick \<union> ev ` A)\<close>
      unfolding Sync_projs by blast
    hence \<open>t \<in> \<D> ?rhs\<close>
    proof cases
      show \<open>u \<in> \<D> (P \<lbrakk>A\<rbrakk> Q) \<Longrightarrow> t \<in> \<D> ?rhs\<close>
        by (simp add: \<open>ftF v\<close> \<open>t = u @ v\<close> \<open>tF u\<close> div is_processT7)
    next
      fix t_P t_Q assume \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close>
        and setinter : \<open>u setinterleaves ((t_P, t_Q), range tick \<union> ev ` A)\<close>
      consider \<open>t_P \<in> \<D> P \<or> t_Q \<in> \<D> Q\<close> | \<open>t_P \<notin> \<D> P\<close> \<open>t_Q \<notin> \<D> Q\<close> by blast
      thus \<open>t \<in> \<D> ?rhs\<close>
      proof cases
        assume \<open>t_P \<in> \<D> P \<or> t_Q \<in> \<D> Q\<close>
        with \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close> setinter \<open>ftF v\<close> \<open>t = u @ v\<close> \<open>tF u\<close>
        have \<open>t \<in> \<D> (P \<lbrakk>A\<rbrakk> Q)\<close>
          using setinterleaving_sym by (simp add: D_Sync) blast
        thus \<open>t \<in> \<D> ?rhs\<close> by (fact div)
      next
        assume \<open>t_P \<notin> \<D> P\<close> \<open>t_Q \<notin> \<D> Q\<close>
        with \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close> \<open>\<^bold>\<alpha>(P) \<subseteq> A \<or> \<^bold>\<alpha>(Q) \<subseteq> A\<close>
        have \<open>{a. ev a \<in> set t_P} \<subseteq> A \<or> {a. ev a \<in> set t_Q} \<subseteq> A\<close>
          by (auto dest: subsetD intro: strict_events_of_memI)
        with interleave_subsetL[OF \<open>tF u\<close> _ setinter]
          interleave_subsetR[OF \<open>tF u\<close> _ setinter]
        have \<open>u = t_P \<or> u = t_Q\<close> by blast
        with \<open>length u = n\<close> have \<open>length t_P = n \<or> length t_Q = n\<close> by auto
        moreover from \<open>tF u\<close> tickFree_interleave_iff[OF setinter]
        have \<open>tF t_P\<close> \<open>tF t_Q\<close> by simp_all
        ultimately have \<open>t_P \<in> \<D> (P \<down> n) \<or> t_Q \<in> \<D> (Q \<down> n)\<close>
          using \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close> by (metis D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
        moreover from \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close>
        have \<open>t_P \<in> \<T> (P \<down> n)\<close> \<open>t_Q \<in> \<T> (Q \<down> n)\<close>
          by (simp_all add: T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
        ultimately show \<open>t \<in> \<D> ?rhs\<close>
          using \<open>ftF v\<close> \<open>t = u @ v\<close> \<open>tF u\<close> setinter
          by (simp add: D_Sync_optimized)
            (metis setinterleaving_sym)
      qed
    qed
  } note * = this

  show \<open>?rhs \<sqsubseteq>\<^sub>F\<^sub>D ?lhs\<close>
  proof (unfold refine_defs, safe)
    show \<open>t \<in> \<D> ?lhs \<Longrightarrow> t \<in> \<D> ?rhs\<close> for t
    proof (elim D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
      show \<open>t \<in> \<D> (P \<lbrakk>A\<rbrakk> Q) \<Longrightarrow> t \<in> \<D> ?rhs\<close> by (fact div)
    next
      show \<open>\<lbrakk>t = u @ v; u \<in> \<T> (P \<lbrakk>A\<rbrakk> Q); length u = n; tF u; ftF v\<rbrakk>
            \<Longrightarrow> t \<in> \<D> ?rhs\<close> for u v by (fact "*")
    qed
  next
    show \<open>(t, X) \<in> \<F> ?lhs \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> for t X
    proof (elim F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
      assume \<open>(t, X) \<in> \<F> (P \<lbrakk>A\<rbrakk> Q)\<close>
      then consider \<open>t \<in> \<D> (P \<lbrakk>A\<rbrakk> Q)\<close>
        | (fail) t_P t_Q X_P X_Q where \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
          \<open>t setinterleaves ((t_P, t_Q), range tick \<union> ev ` A)\<close>
          \<open>X = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` A) \<union> X_P \<inter> X_Q\<close>
        unfolding Sync_projs by blast
      thus \<open>(t, X) \<in> \<F> ?rhs\<close>
      proof cases
        from div D_F show \<open>t \<in> \<D> (P \<lbrakk>A\<rbrakk> Q) \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> by blast
      next
        case fail
        thus \<open>(t, X) \<in> \<F> ?rhs\<close>
          by (auto simp add: F_Sync F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      qed
    next
      show \<open>\<lbrakk>t = u @ v; u \<in> \<T> (P \<lbrakk>A\<rbrakk> Q); length u = n; tF u; ftF v\<rbrakk>
            \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> for u v by (simp add: "*" is_processT8)
    qed
  qed
qed


corollary restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_MultiSync_FD :
  \<open>\<^bold>\<lbrakk>A\<^bold>\<rbrakk> m \<in># M. P l \<down> n \<sqsubseteq>\<^sub>F\<^sub>D \<^bold>\<lbrakk>A\<^bold>\<rbrakk> m \<in># M. (P l \<down> n)\<close>
proof (induct M rule: induct_subset_mset_empty_single)
  case 1 show ?case by simp
next
  case (2 m) show ?case by simp
next
  case (3 N m)
  show ?case
    by (simp add: \<open>N \<noteq> {#}\<close>)
      (fact trans_FD[OF restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync_FD mono_Sync_FD[OF idem_FD "3.hyps"(4)]])
qed



text \<open>In the following corollary, we could be more precise by having
      the condition on at least \<^term>\<open>size M - 1\<close> processes.\<close>

corollary strict_events_of_subset_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_MultiSync :
  \<open>\<^bold>\<lbrakk>A\<^bold>\<rbrakk> m \<in># M. P m \<down> n = (if n = 0 then \<bottom> else \<^bold>\<lbrakk>A\<^bold>\<rbrakk> m \<in># M. (P m \<down> n))\<close>
  \<comment>\<open>\<open>if n = 0 then \<bottom> else _\<close> is necessary because we can have \<^term>\<open>M = {#}\<close>.\<close>
  if \<open>\<And>m. m \<in># M \<Longrightarrow> \<^bold>\<alpha>(P m) \<subseteq> A\<close>
proof (split if_split, intro conjI impI)
  show \<open>n = 0 \<Longrightarrow> \<^bold>\<lbrakk>A\<^bold>\<rbrakk> m \<in># M. P m \<down> n = \<bottom>\<close> by simp
next
  show \<open>\<^bold>\<lbrakk>A\<^bold>\<rbrakk> m \<in># M. P m \<down> n = \<^bold>\<lbrakk>A\<^bold>\<rbrakk> m \<in># M. (P m \<down> n)\<close> if \<open>n \<noteq> 0\<close>
  proof (induct M rule: induct_subset_mset_empty_single)
    case 1 from \<open>n \<noteq> 0\<close> show ?case by simp
  next
    case (2 m) show ?case by simp
  next
    case (3 N m)
    have \<open>(\<^bold>\<lbrakk>A\<^bold>\<rbrakk> n\<in>#add_mset m N. P n) \<down> n = (P m \<lbrakk>A\<rbrakk> \<^bold>\<lbrakk>A\<^bold>\<rbrakk> n\<in>#N. P n) \<down> n\<close>
      by (simp add: \<open>N \<noteq> {#}\<close>)
    also have \<open>\<dots> = (P m \<down> n) \<lbrakk>A\<rbrakk> (\<^bold>\<lbrakk>A\<^bold>\<rbrakk> n\<in>#N. P n \<down> n)\<close>
      by (rule strict_events_of_subset_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync)
        (simp add: "3.hyps"(1) \<open>\<And>m. m \<in># M \<Longrightarrow> \<^bold>\<alpha>(P m) \<subseteq> A\<close>)
    also have \<open>(\<^bold>\<lbrakk>A\<^bold>\<rbrakk> m\<in>#N. P m) \<down> n = \<^bold>\<lbrakk>A\<^bold>\<rbrakk> m\<in>#N. (P m \<down> n)\<close> by (fact "3.hyps"(4))
    finally show ?case by (simp add: \<open>N \<noteq> {#}\<close>)
  qed
qed



corollary restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Par :
  \<open>P || Q \<down> n = (P \<down> n) || (Q \<down> n)\<close>
  by (simp add: strict_events_of_subset_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Sync)

corollary restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_MultiPar :
  \<open>\<^bold>|\<^bold>| m \<in># M. P l \<down> n = (if n = 0 then \<bottom> else \<^bold>|\<^bold>| m \<in># M. (P l \<down> n))\<close>
  by (simp add: strict_events_of_subset_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_MultiSync)




subsection \<open>Non Destructiveness\<close>

lemma Sync_non_destructive :
  \<open>non_destructive (\<lambda>(P, Q). P \<lbrakk>A\<rbrakk> Q)\<close>
proof (rule order_non_destructiveI, clarify)
  fix P P' Q Q' :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and n
  assume \<open>(P, Q) \<down> n = (P', Q') \<down> n\<close>
  hence \<open>P \<down> n = P' \<down> n\<close> \<open>Q \<down> n = Q' \<down> n\<close>
    by (simp_all add: restriction_prod_def)
  show \<open>P \<lbrakk>A\<rbrakk> Q \<down> n \<sqsubseteq>\<^sub>F\<^sub>D P' \<lbrakk>A\<rbrakk> Q' \<down> n\<close>
  proof (rule leFD_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
    show div : \<open>t \<in> \<D> (P' \<lbrakk>A\<rbrakk> Q') \<Longrightarrow> t \<in> \<D> (P \<lbrakk>A\<rbrakk> Q \<down> n)\<close> if \<open>length t \<le> n\<close> for t
    proof (unfold D_Sync_optimized, safe)
      fix u v t_P t_Q
      assume * : \<open>t = u @ v\<close> \<open>tF u\<close> \<open>ftF v\<close>
        \<open>u setinterleaves ((t_P, t_Q), range tick \<union> ev ` A)\<close>
        \<open>t_P \<in> \<D> P'\<close> \<open>t_Q \<in> \<T> Q'\<close>
      from "*"(1) \<open>length t \<le> n\<close> have \<open>length u \<le> n\<close> by simp
      from \<open>length u \<le> n\<close> interleave_imp_lengthLR_le[OF "*"(4)]
      have \<open>length t_P \<le> n\<close> \<open>length t_Q \<le> n\<close> by simp_all
      from \<open>t_Q \<in> \<T> Q'\<close> \<open>length t_Q \<le> n\<close> \<open>Q \<down> n = Q' \<down> n\<close> have \<open>t_Q \<in> \<T> Q\<close>
        by (metis T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      show \<open>u @ v \<in> \<D> (P \<lbrakk>A\<rbrakk> Q \<down> n)\<close>
      proof (cases \<open>length u = n\<close>)
        assume \<open>length u = n\<close>
        from \<open>t_P \<in> \<D> P'\<close> \<open>length t_P \<le> n\<close> \<open>P \<down> n = P' \<down> n\<close> have \<open>t_P \<in> \<T> P\<close>
          by (simp add: D_T D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        with \<open>t_Q \<in> \<T> Q\<close> "*"(4) have \<open>u \<in> \<T> (P \<lbrakk>A\<rbrakk> Q)\<close>
          unfolding T_Sync by blast
        with \<open>length u = n\<close> "*"(2, 3) show \<open>u @ v \<in> \<D> (P \<lbrakk>A\<rbrakk> Q \<down> n)\<close>
          by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI is_processT7)
      next
        assume \<open>length u \<noteq> n\<close>
        with \<open>length u \<le> n\<close> have \<open>length u < n\<close> by simp
        with interleave_imp_lengthLR_le[OF "*"(4)]
        have \<open>length t_P < n\<close> by simp
        with \<open>t_P \<in> \<D> P'\<close> \<open>P \<down> n = P' \<down> n\<close> have \<open>t_P \<in> \<D> P\<close>
          by (metis D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI
              length_less_in_D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        with \<open>t_Q \<in> \<T> Q\<close> "*"(2-4) have \<open>u @ v \<in> \<D> (P \<lbrakk>A\<rbrakk> Q)\<close>
          unfolding D_Sync by blast
        thus \<open>u @ v \<in> \<D> (P \<lbrakk>A\<rbrakk> Q \<down> n)\<close>
          by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
      qed
    next
      fix u v t_P t_Q
      assume * : \<open>t = u @ v\<close> \<open>tF u\<close> \<open>ftF v\<close>
        \<open>u setinterleaves ((t_Q, t_P), range tick \<union> ev ` A)\<close>
        \<open>t_P \<in> \<T> P'\<close> \<open>t_Q \<in> \<D> Q'\<close>
      from "*"(1) \<open>length t \<le> n\<close> have \<open>length u \<le> n\<close> by simp
      from \<open>length u \<le> n\<close> interleave_imp_lengthLR_le[OF "*"(4)]
      have \<open>length t_P \<le> n\<close> \<open>length t_Q \<le> n\<close> by simp_all
      from \<open>t_P \<in> \<T> P'\<close> \<open>length t_P \<le> n\<close> \<open>P \<down> n = P' \<down> n\<close> have \<open>t_P \<in> \<T> P\<close>
        by (metis T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      show \<open>u @ v \<in> \<D> (P \<lbrakk>A\<rbrakk> Q \<down> n)\<close>
      proof (cases \<open>length u = n\<close>)
        assume \<open>length u = n\<close>
        from \<open>t_Q \<in> \<D> Q'\<close> \<open>length t_Q \<le> n\<close> \<open>Q \<down> n = Q' \<down> n\<close> have \<open>t_Q \<in> \<T> Q\<close>
          by (simp add: D_T D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        with \<open>t_P \<in> \<T> P\<close> "*"(4) have \<open>u \<in> \<T> (P \<lbrakk>A\<rbrakk> Q)\<close>
          unfolding T_Sync using setinterleaving_sym by blast
        with \<open>length u = n\<close> "*"(2, 3) show \<open>u @ v \<in> \<D> (P \<lbrakk>A\<rbrakk> Q \<down> n)\<close>
          by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI is_processT7)
      next
        assume \<open>length u \<noteq> n\<close>
        with \<open>length u \<le> n\<close> have \<open>length u < n\<close> by simp
        with interleave_imp_lengthLR_le[OF "*"(4)]
        have \<open>length t_Q < n\<close> by simp
        with \<open>t_Q \<in> \<D> Q'\<close> \<open>Q \<down> n = Q' \<down> n\<close> have \<open>t_Q \<in> \<D> Q\<close>
          by (metis D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI
              length_less_in_D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        with \<open>t_P \<in> \<T> P\<close> "*"(2-4) have \<open>u @ v \<in> \<D> (P \<lbrakk>A\<rbrakk> Q)\<close>
          unfolding D_Sync by blast
        thus \<open>u @ v \<in> \<D> (P \<lbrakk>A\<rbrakk> Q \<down> n)\<close>
          by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
      qed
    qed

    fix t X assume \<open>(t, X) \<in> \<F> (P' \<lbrakk>A\<rbrakk> Q')\<close> \<open>length t \<le> n\<close>
    then consider \<open>t \<in> \<D> (P' \<lbrakk>A\<rbrakk> Q')\<close>
      | (fail) t_P t_Q X_P X_Q
      where \<open>(t_P, X_P) \<in> \<F> P'\<close> \<open>(t_Q, X_Q) \<in> \<F> Q'\<close>
        \<open>t setinterleaves ((t_P, t_Q), range tick \<union> ev ` A)\<close>
        \<open>X = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` A) \<union> X_P \<inter> X_Q\<close>
      unfolding Sync_projs by blast
    thus \<open>(t, X) \<in> \<F> (P \<lbrakk>A\<rbrakk> Q \<down> n)\<close>
    proof cases
      from div \<open>length t \<le> n\<close> D_F
      show \<open>t \<in> \<D> (P' \<lbrakk>A\<rbrakk> Q') \<Longrightarrow> (t, X) \<in> \<F> (P \<lbrakk>A\<rbrakk> Q \<down> n)\<close> by blast
    next
      case fail
      show \<open>(t, X) \<in> \<F> (P \<lbrakk>A\<rbrakk> Q \<down> n)\<close>
      proof (cases \<open>length t = n\<close>)
        assume \<open>length t = n\<close>
        from \<open>length t \<le> n\<close> interleave_imp_lengthLR_le[OF fail(3)]
        have \<open>length t_P \<le> n\<close> \<open>length t_Q \<le> n\<close> by simp_all
        with fail(1, 2) \<open>P \<down> n = P' \<down> n\<close> \<open>Q \<down> n = Q' \<down> n\<close>
        have \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close>
          by (metis F_T T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI
              length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)+
        from F_imp_front_tickFree \<open>(t, X) \<in> \<F> (P' \<lbrakk>A\<rbrakk> Q')\<close>
        have \<open>ftF t\<close> by blast
        with fail(3) consider \<open>tF t\<close>
          | r s t_P' t_Q' where \<open>t_P = t_P' @ [\<checkmark>(r)]\<close> \<open>t_Q = t_Q' @ [\<checkmark>(s)]\<close>
          by (metis F_imp_front_tickFree SyncWithTick_imp_NTF
              fail(1-2) nonTickFree_n_frontTickFree)
        thus \<open>(t, X) \<in> \<F> (P \<lbrakk>A\<rbrakk> Q \<down> n)\<close>
        proof cases
          assume \<open>tF t\<close>
          from \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close> fail(3)
          have \<open>t \<in> \<T> (P \<lbrakk>A\<rbrakk> Q)\<close> unfolding T_Sync by blast
          hence \<open>t \<in> \<D> (P \<lbrakk>A\<rbrakk> Q \<down> n)\<close>
            by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI \<open>length t = n\<close> \<open>tF t\<close>)
          thus \<open>(t, X) \<in> \<F> (P \<lbrakk>A\<rbrakk> Q \<down> n)\<close> by (simp add: is_processT8)
        next
          fix r s t_P' t_Q' assume \<open>t_P = t_P' @ [\<checkmark>(r)]\<close> \<open>t_Q = t_Q' @ [\<checkmark>(s)]\<close>
          have \<open>(t_P, X_P) \<in> \<F> P\<close>
            by (metis \<open>t_P \<in> \<T> P\<close> \<open>t_P = t_P' @ [\<checkmark>(r)]\<close> tick_T_F)
          moreover have \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
            by (metis \<open>t_Q \<in> \<T> Q\<close> \<open>t_Q = t_Q' @ [\<checkmark>(s)]\<close> tick_T_F)
          ultimately have \<open>(t, X) \<in> \<F> (P \<lbrakk>A\<rbrakk> Q)\<close>
            using fail(3, 4) unfolding F_Sync by fast
          thus \<open>(t, X) \<in> \<F> (P \<lbrakk>A\<rbrakk> Q \<down> n)\<close>
            by (simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
        qed
      next
        assume \<open>length t \<noteq> n\<close>
        with \<open>length t \<le> n\<close> have \<open>length t < n\<close> by simp
        with interleave_imp_lengthLR_le[OF fail(3)]
        have \<open>length t_P < n\<close> \<open>length t_Q < n\<close> by simp_all
        with fail(1, 2) \<open>P \<down> n = P' \<down> n\<close> \<open>Q \<down> n = Q' \<down> n\<close>
        have \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
          by (metis F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI
              length_less_in_F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)+
        with fail(3, 4) have \<open>(t, X) \<in> \<F> (P \<lbrakk>A\<rbrakk> Q)\<close>
          unfolding F_Sync by fast
        thus \<open>(t, X) \<in> \<F> (P \<lbrakk>A\<rbrakk> Q \<down> n)\<close>
          by (simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
      qed
    qed
  qed
qed


(*>*)
end
  (*>*)