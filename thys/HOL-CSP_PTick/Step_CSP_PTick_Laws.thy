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


chapter \<open>Communications\<close>

(*<*)
theory Step_CSP_PTick_Laws
  imports Sequential_Composition_Generalized
    Synchronization_Product_Generalized
begin
  (*>*)

section \<open>Step Laws\<close>

subsection \<open>Sequential Composition\<close>

lemma Mprefix_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k: \<open>\<box>a \<in> A \<rightarrow> P a \<^bold>;\<^sub>\<checkmark> Q = \<box>a \<in> A \<rightarrow> (P a \<^bold>;\<^sub>\<checkmark> Q)\<close> (is \<open>?lhs = ?rhs\<close>)
proof (rule Process_eq_optimizedI)
  show \<open>t \<in> \<D> ?lhs \<Longrightarrow> t \<in> \<D> ?rhs\<close> for t
    by (cases t, auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs Mprefix_projs image_iff Cons_eq_append_conv) blast
next
  show \<open>t \<in> \<D> ?rhs \<Longrightarrow> t \<in> \<D> ?lhs\<close> for t
    by (cases t, auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs Mprefix_projs image_iff Cons_eq_map_conv Cons_eq_append_conv)
      (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) tickFree_Cons_iff,
        metis append_Cons event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.discI(1) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) tickFree_Cons_iff)
next
  fix t X assume \<open>(t, X) \<in> \<F> ?lhs\<close> \<open>t \<notin> \<D> ?lhs\<close>
  then consider (F_P) t' where \<open>t = map (ev \<circ> of_ev) t'\<close>
    \<open>(t', ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<in> \<F> (\<box>a \<in> A \<rightarrow> P a)\<close> \<open>tF t'\<close>
  | (F_Q) t' r u where \<open>t = map (ev \<circ> of_ev) t' @ u\<close> \<open>t' @ [\<checkmark>(r)] \<in> \<T> (\<box>a \<in> A \<rightarrow> P a)\<close> \<open>tF t'\<close> \<open>(u, X) \<in> \<F> (Q r)\<close>
    unfolding Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by fast
  thus \<open>(t, X) \<in> \<F> ?rhs\<close>
  proof cases
    case F_P thus \<open>(t, X) \<in> \<F> ?rhs\<close>
      by (cases t'; simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def Mprefix_projs disjoint_iff image_iff)
        (metis IntI event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) rangeI, metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1))
  next
    case F_Q thus \<open>(t, X) \<in> \<F> ?rhs\<close>
      by (cases t) (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs Mprefix_projs Cons_eq_append_conv)+
  qed
next
  fix t X assume \<open>(t, X) \<in> \<F> ?rhs\<close> \<open>t \<notin> \<D> ?rhs\<close>
  from \<open>(t, X) \<in> \<F> ?rhs\<close> consider \<open>t = []\<close> \<open>X \<inter> ev ` A = {}\<close>
    | a t' where \<open>t = ev a # t'\<close> \<open>a \<in> A\<close> \<open>(t', X) \<in> \<F> (P a \<^bold>;\<^sub>\<checkmark> Q)\<close>
    unfolding F_Mprefix by blast
  thus \<open>(t, X) \<in> \<F> ?lhs\<close>
  proof cases
    show \<open>t = [] \<Longrightarrow> X \<inter> ev ` A = {} \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close>
      by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def F_Mprefix)
  next
    fix a t' assume \<open>t = ev a # t'\<close> \<open>a \<in> A\<close> \<open>(t', X) \<in> \<F> (P a \<^bold>;\<^sub>\<checkmark> Q)\<close>
    from \<open>(t', X) \<in> \<F> (P a \<^bold>;\<^sub>\<checkmark> Q)\<close> \<open>t \<notin> \<D> ?rhs\<close> \<open>a \<in> A\<close> \<open>t = ev a # t'\<close>
    consider (F_P) t'' where \<open>t' = map (ev \<circ> of_ev) t''\<close> \<open>(t'', ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<in> \<F> (P a)\<close> \<open>tF t''\<close>
      | (F_Q) t'' r u where \<open>t' = map (ev \<circ> of_ev) t'' @ u\<close> \<open>t'' @ [\<checkmark>(r)] \<in> \<T> (P a)\<close> \<open>tF t''\<close> \<open>(u, X) \<in> \<F> (Q r)\<close>
      by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs D_Mprefix) 
    thus \<open>(t, X) \<in> \<F> ?lhs\<close>
    proof cases
      case F_P thus \<open>(t, X) \<in> \<F> ?lhs\<close>
        by (simp add: Mprefix_projs Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs \<open>t = ev a # t'\<close> Cons_eq_map_conv)
          (metis \<open>a \<in> A\<close> event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) tickFree_Cons_iff)
    next
      case F_Q thus \<open>(t, X) \<in> \<F> ?lhs\<close>
        by (simp add: Mprefix_projs Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs \<open>t = ev a # t'\<close> Cons_eq_map_conv append_eq_Cons_conv)
          (metis (no_types, lifting) \<open>a \<in> A\<close> append_Cons comp_apply event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1)
            event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) list.simps(9) tickFree_Cons_iff)
    qed
  qed
qed




subsection \<open>Synchronization Product\<close>

lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix_bis :
  \<open>\<box>a\<in>(A \<union> A') \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b\<in>(B \<union> B') \<rightarrow> Q b =
   (\<box>a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b\<in>(B \<union> B') \<rightarrow> Q b)) \<box>
   (\<box>b\<in>B \<rightarrow> (\<box>a\<in>(A \<union> A') \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)) \<box>
   (\<box>x\<in>(A' \<inter> B') \<rightarrow> (P x \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q x))\<close>
  (is \<open>?lhs1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> ?lhs2 = ?rhs1 \<box> ?rhs2 \<box> ?rhs3\<close>) 
  if sets_assms: \<open>A \<inter> S = {}\<close> \<open>A' \<subseteq> S\<close> \<open>B \<inter> S = {}\<close> \<open>B' \<subseteq> S\<close>
proof (rule Process_eq_optimizedI)
  fix t assume \<open>t \<in> \<D> (?lhs1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> ?lhs2)\<close>
  then obtain u v t_P t_Q
    where * : \<open>t = u @ v\<close> \<open>tF u\<close> \<open>ftF v\<close>
      \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close>
      \<open>t_P \<in> \<D> ?lhs1 \<and> t_Q \<in> \<T> ?lhs2 \<or>
               t_P \<in> \<T> ?lhs1 \<and> t_Q \<in> \<D> ?lhs2\<close>
    unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
  from "*"(5) show \<open>t \<in> \<D> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close>
  proof (elim disjE conjE)
    assume \<open>t_P \<in> \<D> ?lhs1\<close> \<open>t_Q \<in> \<T> ?lhs2\<close>
    from \<open>t_P \<in> \<D> ?lhs1\<close> obtain a t_P'
      where ** : \<open>a \<in> A \<or> a \<in> A'\<close> \<open>t_P = ev a # t_P'\<close> \<open>t_P' \<in> \<D> (P a)\<close>
      unfolding D_Mprefix by blast
    from \<open>t_Q \<in> \<T> ?lhs2\<close> consider \<open>t_Q = []\<close>
      | b t_Q' where \<open>b \<in> B \<or> b \<in> B'\<close> \<open>t_Q = ev b # t_Q'\<close> \<open>t_Q' \<in> \<T> (Q b)\<close>
      unfolding T_Mprefix by blast
    thus \<open>t \<in> \<D> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close>
    proof cases
      assume \<open>t_Q = []\<close>
      with "*"(4) obtain u' where \<open>a \<notin> S\<close> \<open>u = ev a # u'\<close>
        \<open>u' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P', t_Q), S)\<close>
        by (auto simp add: "**"(2) split: if_split_asm)
      moreover from \<open>u = ev a # u'\<close> "*"(2) have \<open>tF u'\<close> by simp
      ultimately have \<open>t \<in> \<D> ?rhs1\<close>
        using "*"(1, 3) "**"(1, 3) \<open>t_Q \<in> \<T> ?lhs2\<close> \<open>A' \<subseteq> S\<close>
        by (auto simp add: simp add: D_Mprefix D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      thus \<open>t \<in> \<D> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close> by (simp add: D_Det)
    next
      fix b t_Q' assume *** : \<open>b \<in> B \<or> b \<in> B'\<close> \<open>t_Q = ev b # t_Q'\<close> \<open>t_Q' \<in> \<T> (Q b)\<close>
      from "*"(2) have $ : \<open>u = ev x # u' \<Longrightarrow> tF u'\<close> for x u' by simp
      from "*"(4) sets_assms "**"(1) "***"(1)
      consider (mv_both)  u' where \<open>a \<in> S\<close> \<open>b = a\<close> \<open>a \<in> A'\<close> \<open>a \<in> B'\<close> \<open>u = ev a # u'\<close>
        \<open>u' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P', t_Q'), S)\<close>
      |        (mv_left)  u' where \<open>a \<notin> S\<close> \<open>a \<in> A\<close> \<open>u = ev a # u'\<close>
        \<open>u' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P', t_Q), S)\<close>
      |        (mv_right) u' where \<open>b \<notin> S\<close> \<open>b \<in> B\<close> \<open>u = ev b # u'\<close>
        \<open>u' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q'), S)\<close>
        by (auto simp add: "**"(2) "***"(2) disjoint_iff
            split: if_split_asm)
      thus \<open>t \<in> \<D> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close>
      proof cases
        case mv_both
        have \<open>tF u'\<close> by (simp add: "$" mv_both(5))
        with "*"(3) "**"(3) "***"(3) mv_both(2, 6)
        have \<open>u' @ v \<in> \<D> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q a)\<close> by (auto simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        hence \<open>t \<in> \<D> ?rhs3\<close> by (simp add: D_Mprefix "*"(1) mv_both(3-5))
        thus \<open>t \<in> \<D> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close> by (simp add: D_Det)
      next
        case mv_left
        have \<open>tF u'\<close> by (simp add: "$" mv_left(3))
        with "*"(3) "**"(3) \<open>t_Q \<in> \<T> ?lhs2\<close> mv_left(4)
        have \<open>u' @ v \<in> \<D> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b\<in>(B \<union> B') \<rightarrow> Q b)\<close> by (auto simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        hence \<open>t \<in> \<D> ?rhs1\<close> by (simp add: D_Mprefix "*"(1) mv_left(2, 3))
        thus \<open>t \<in> \<D> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close> by (simp add: D_Det)
      next
        case mv_right
        have \<open>tF u'\<close> by (simp add: "$" mv_right(3))
        with "*"(3) "***"(3) mv_right(4) \<open>t_P \<in> \<D> ?lhs1\<close>
        have \<open>u' @ v \<in> \<D> (\<box>a\<in>(A \<union> A') \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)\<close>
          by (auto simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        hence \<open>t \<in> \<D> ?rhs2\<close> by (simp add: D_Mprefix "*"(1) mv_right(2, 3))
        thus \<open>t \<in> \<D> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close> by (simp add: D_Det)
      qed
    qed
  next
    assume \<open>t_P \<in> \<T> ?lhs1\<close> \<open>t_Q \<in> \<D> ?lhs2\<close>
    from \<open>t_Q \<in> \<D> ?lhs2\<close> obtain b t_Q'
      where ** : \<open>b \<in> B \<or> b \<in> B'\<close> \<open>t_Q = ev b # t_Q'\<close> \<open>t_Q' \<in> \<D> (Q b)\<close>
      unfolding D_Mprefix by blast
    from \<open>t_P \<in> \<T> ?lhs1\<close> consider \<open>t_P = []\<close>
      | a t_P' where \<open>a \<in> A \<or> a \<in> A'\<close> \<open>t_P = ev a # t_P'\<close> \<open>t_P' \<in> \<T> (P a)\<close>
      unfolding T_Mprefix by blast
    thus \<open>t \<in> \<D> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close>
    proof cases
      assume \<open>t_P = []\<close>
      with "*"(4) obtain u' where \<open>b \<notin> S\<close> \<open>u = ev b # u'\<close>
        \<open>u' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q'), S)\<close>
        by (auto simp add: "**"(2) split: if_split_asm)
      moreover from \<open>u = ev b # u'\<close> \<open>tF u\<close> have \<open>tF u'\<close> by simp
      ultimately have \<open>t \<in> \<D> ?rhs2\<close>
        using "*"(1, 3) "**"(1, 3) \<open>t_P \<in> \<T> ?lhs1\<close> \<open>B' \<subseteq> S\<close>
        by (auto simp add: simp add: D_Mprefix D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      thus \<open>t \<in> \<D> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close> by (simp add: D_Det)
    next
      fix a t_P' assume *** : \<open>a \<in> A \<or> a \<in> A'\<close> \<open>t_P = ev a # t_P'\<close> \<open>t_P' \<in> \<T> (P a)\<close>
      from \<open>tF u\<close> have $ : \<open>u = ev x # u' \<Longrightarrow> tF u'\<close> for x u' by simp
      from "*"(4) sets_assms "**"(1) "***"(1)
      consider (mv_both)  u' where \<open>a \<in> S\<close> \<open>b = a\<close> \<open>a \<in> A'\<close> \<open>a \<in> B'\<close>
        \<open>u = ev a # u'\<close> \<open>u' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P', t_Q'), S)\<close>
      |        (mv_left)  u' where \<open>a \<notin> S\<close> \<open>a \<in> A\<close> \<open>u = ev a # u'\<close>
        \<open>u' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P', t_Q), S)\<close>
      |        (mv_right) u' where \<open>b \<notin> S\<close> \<open>b \<in> B\<close> \<open>u = ev b # u'\<close>
        \<open>u' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q'), S)\<close>
        by (auto simp add: "**"(2) "***"(2) disjoint_iff split: if_split_asm)
      thus \<open>t \<in> \<D> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close>
      proof cases
        case mv_both
        have \<open>tF u'\<close> by (simp add: "$" mv_both(5))
        with "*"(3) "**"(3) "***"(3) mv_both(2, 6)
        have \<open>u' @ v \<in> \<D> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q a)\<close> by (auto simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        hence \<open>t \<in> \<D> ?rhs3\<close> by (simp add: D_Mprefix "*"(1) mv_both(3-5))
        thus \<open>t \<in> \<D> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close> by (simp add: D_Det)
      next
        case mv_left
        have \<open>tF u'\<close> by (simp add: "$" mv_left(3))
        with "*"(3) "***"(3) mv_left(4) \<open>t_Q \<in> \<D> ?lhs2\<close>
        have \<open>u' @ v \<in> \<D> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b\<in>(B \<union> B') \<rightarrow> Q b)\<close> by (auto simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        hence \<open>t \<in> \<D> ?rhs1\<close> by (simp add: D_Mprefix "*"(1) mv_left(2, 3))
        thus \<open>t \<in> \<D> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close> by (simp add: D_Det)
      next
        case mv_right
        have \<open>tF u'\<close> by (simp add: "$" mv_right(3))
        with "*"(3) "**"(3) \<open>t_P \<in> \<T> ?lhs1\<close> mv_right(4)
        have \<open>u' @ v \<in> \<D> (\<box>a\<in>(A \<union> A') \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)\<close>
          by (auto simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        hence \<open>t \<in> \<D> ?rhs2\<close> by (simp add: D_Mprefix "*"(1) mv_right(2, 3))
        thus \<open>t \<in> \<D> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close> by (simp add: D_Det)
      qed
    qed
  qed
next

  fix t assume \<open>t \<in> \<D> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close>
  consider \<open>t = []\<close> | r_s t' where \<open>t = \<checkmark>(r_s) # t'\<close> | x t' where \<open>t = ev x # t'\<close>
    by (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust neq_Nil_conv)
  thus \<open>t \<in> \<D> (?lhs1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> ?lhs2)\<close>
  proof cases
    assume \<open>t = []\<close>
    with \<open>t \<in> \<D> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close> have False
      by (simp add: D_Det D_Mprefix)
    thus \<open>t \<in> \<D> (?lhs1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> ?lhs2)\<close> ..
  next
    fix r_s t' assume \<open>t = \<checkmark>(r_s) # t'\<close>
    with \<open>t \<in> \<D> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close> have False
      by (simp add: D_Det D_Mprefix)
    thus \<open>t \<in> \<D> (?lhs1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> ?lhs2)\<close> ..
  next
    fix x t' assume \<open>t = ev x # t'\<close>
    with \<open>t \<in> \<D> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close> consider
      (mv_left)  \<open>x \<in> A\<close> \<open>t' \<in> \<D> (P x \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> ?lhs2)\<close>
      | (mv_right) \<open>x \<in> B\<close> \<open>t' \<in> \<D> (?lhs1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q x)\<close>
      | (mv_both)  \<open>x \<in> A'\<close> \<open>x \<in> B'\<close> \<open>t' \<in> \<D> (P x \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q x)\<close>
      by (auto simp add: D_Det D_Mprefix)
    thus \<open>t \<in> \<D> (?lhs1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> ?lhs2)\<close>
    proof cases
      case mv_left
      from \<open>x \<in> A\<close> \<open>A \<inter> S = {}\<close> have \<open>x \<notin> S\<close> by blast
      from mv_left(2) obtain u v t_P t_Q
        where * : \<open>t' = u @ v\<close> \<open>tF u\<close> \<open>ftF v\<close>
          \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close>
          \<open>t_P \<in> \<D> (P x) \<and> t_Q \<in> \<T> ?lhs2 \<or>
                   t_P \<in> \<T> (P x) \<and> t_Q \<in> \<D> ?lhs2\<close>
        unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
      have \<open>t = (ev x # u) @ v\<close> by (simp add: "*"(1) \<open>t = ev x # t'\<close>)
      moreover have \<open>tF (ev x # u)\<close> by (simp add: "*"(2))
      moreover from "*"(4) have \<open>ev x # u setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev x # t_P, t_Q), S)\<close>
        by (cases t_Q) (auto simp add: \<open>x \<notin> S\<close> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
      moreover from "*"(5) mv_left(1)
      have \<open>ev x # t_P \<in> \<D> ?lhs1 \<and> t_Q \<in> \<T> ?lhs2 \<or>
            ev x # t_P \<in> \<T> ?lhs1 \<and> t_Q \<in> \<D> ?lhs2\<close> by (simp add: Mprefix_projs)
      ultimately show \<open>t \<in> \<D> (?lhs1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> ?lhs2)\<close>
        using "*"(3) by (simp (no_asm) add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) blast
    next
      case mv_right
      from \<open>x \<in> B\<close> \<open>B \<inter> S = {}\<close> have \<open>x \<notin> S\<close> by blast
      from mv_right(2) obtain u v t_P t_Q
        where * : \<open>t' = u @ v\<close> \<open>tF u\<close> \<open>ftF v\<close>
          \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close>
          \<open>t_P \<in> \<D> ?lhs1 \<and> t_Q \<in> \<T> (Q x) \<or>
                   t_P \<in> \<T> ?lhs1 \<and> t_Q \<in> \<D> (Q x)\<close>
        unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
      have \<open>t = (ev x # u) @ v\<close> by (simp add: "*"(1) \<open>t = ev x # t'\<close>)
      moreover have \<open>tF (ev x # u)\<close> by (simp add: "*"(2))
      moreover from "*"(4) have \<open>ev x # u setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, ev x # t_Q), S)\<close>
        by (cases t_P) (auto simp add: \<open>x \<notin> S\<close> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
      moreover from "*"(5) mv_right(1)
      have \<open>t_P \<in> \<D> ?lhs1 \<and> ev x # t_Q \<in> \<T> ?lhs2 \<or>
            t_P \<in> \<T> ?lhs1 \<and> ev x # t_Q \<in> \<D> ?lhs2\<close> by (simp add: Mprefix_projs)
      ultimately show \<open>t \<in> \<D> (?lhs1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> ?lhs2)\<close>
        using "*"(3) by (simp (no_asm) add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) blast
    next
      case mv_both
      from \<open>x \<in> A'\<close> \<open>A' \<subseteq> S\<close> have \<open>x \<in> S\<close> by blast
      from mv_both(3) obtain u v t_P t_Q
        where * : \<open>t' = u @ v\<close> \<open>tF u\<close> \<open>ftF v\<close>
          \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close>
          \<open>t_P \<in> \<D> (P x) \<and> t_Q \<in> \<T> (Q x) \<or>
                   t_P \<in> \<T> (P x) \<and> t_Q \<in> \<D> (Q x)\<close>
        unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
      have \<open>t = (ev x # u) @ v\<close> by (simp add: "*"(1) \<open>t = ev x # t'\<close>)
      moreover have \<open>tF (ev x # u)\<close> by (simp add: "*"(2))
      moreover from "*"(4) have \<open>ev x # u setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev x # t_P, ev x # t_Q), S)\<close>
        by (auto simp add: \<open>x \<in> S\<close>)
      moreover from "*"(5) mv_both(1, 2)
      have \<open>ev x # t_P \<in> \<D> ?lhs1 \<and> ev x # t_Q \<in> \<T> ?lhs2 \<or>
            ev x # t_P \<in> \<T> ?lhs1 \<and> ev x # t_Q \<in> \<D> ?lhs2\<close> by (simp add: Mprefix_projs)
      ultimately show \<open>t \<in> \<D> (?lhs1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> ?lhs2)\<close>
        using "*"(3) by (simp (no_asm) add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) blast
    qed
  qed
next

  fix t X assume \<open>(t, X) \<in> \<F> (?lhs1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> ?lhs2)\<close> \<open>t \<notin> \<D> (?lhs1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> ?lhs2)\<close>
  then obtain t_P t_Q X_P X_Q
    where fail : \<open>(t_P, X_P) \<in> \<F> ?lhs1\<close> \<open>(t_Q, X_Q) \<in> \<F> ?lhs2\<close>
      \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close>
      \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join X_P S X_Q\<close>
    unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
  consider \<open>t = []\<close> | r_s t' where \<open>t = \<checkmark>(r_s) # t'\<close> | a t' where \<open>t = ev a # t'\<close>
    by (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust neq_Nil_conv)
  thus \<open>(t, X) \<in> \<F> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close>
  proof cases
    assume \<open>t = []\<close>
    with Nil_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k fail(3) have \<open>t_P = []\<close> \<open>t_Q = []\<close> by blast+
    with fail(1, 2) have \<open>X_P \<inter> ev ` (A \<union> A') = {}\<close> \<open>X_Q \<inter> ev ` (B \<union> B') = {}\<close> 
      by (simp_all add: F_Mprefix)
    with fail(4) \<open>A \<inter> S = {}\<close> \<open>B \<inter> S = {}\<close> show \<open>(t, X) \<in> \<F> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close>
      by (simp add: \<open>t = []\<close> Det_projs Mprefix_projs super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
        (use event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.distinct(1) in blast)
  next
    fix r_s t' assume \<open>t = \<checkmark>(r_s) # t'\<close>
    hence \<open>t = [\<checkmark>(r_s)]\<close>
      by (metis F_imp_front_tickFree \<open>(t, X) \<in> \<F> (?lhs1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> ?lhs2)\<close>
          event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(2) front_tickFree_Cons_iff)
    with fail(3) obtain r s where \<open>tick_join r s = Some r_s\<close>
      by (auto elim: Cons_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
    from \<open>t = [\<checkmark>(r_s)]\<close> fail(3) \<open>tick_join r s = Some r_s\<close>
    have \<open>t_P = [\<checkmark>(r)]\<close>
      by (auto dest: inj_tick_join Nil_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
          elim: Cons_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
    with fail(1) \<open>t = [\<checkmark>(r_s)]\<close> have False by (simp add: F_Mprefix)
    thus \<open>(t, X) \<in> \<F> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close> ..
  next
    fix a t' assume \<open>t = ev a # t'\<close>
    from fail(1-3) sets_assms consider
      (mv_left)  t_P' where
      \<open>a \<notin> S\<close> \<open>a \<in> A\<close> \<open>t_P = ev a # t_P'\<close> \<open>(t_P', X_P) \<in> \<F> (P a)\<close>
      \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P', t_Q), S)\<close>
    | (mv_right) t_Q' where
      \<open>a \<notin> S\<close> \<open>a \<in> B\<close> \<open>t_Q = ev a # t_Q'\<close> \<open>(t_Q', X_Q) \<in> \<F> (Q a)\<close>
      \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q'), S)\<close>
    | (mv_both) t_P' t_Q' where
      \<open>a \<in> S\<close> \<open>a \<in> A'\<close> \<open>a \<in> B'\<close> \<open>t_P = ev a # t_P'\<close> \<open>t_Q = ev a # t_Q'\<close>
      \<open>(t_P', X_P) \<in> \<F> (P a)\<close> \<open>(t_Q', X_Q) \<in> \<F> (Q a)\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P', t_Q'), S)\<close>
      by (unfold \<open>t = ev a # t'\<close>, elim Cons_ev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
        (simp_all add: F_Mprefix subset_iff disjoint_iff, blast+)
    thus \<open>(t, X) \<in> \<F> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close>
    proof cases
      case mv_left
      with fail(2, 4) have \<open>(t, X) \<in> \<F> ?rhs1\<close>
        by (subst F_Mprefix) (auto simp add: F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<open>t = ev a # t'\<close>)
      thus \<open>(t, X) \<in> \<F> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close>
        by (simp add: F_Det \<open>t = ev a # t'\<close>)
    next
      case mv_right
      with fail(1, 4) have \<open>(t, X) \<in> \<F> ?rhs2\<close>
        by (subst F_Mprefix) (auto simp add: F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<open>t = ev a # t'\<close>)
      thus \<open>(t, X) \<in> \<F> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close>
        by (simp add: F_Det \<open>t = ev a # t'\<close>)
    next
      case mv_both
      with fail(4) have \<open>(t, X) \<in> \<F> ?rhs3\<close>
        by (auto simp add: F_Mprefix F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<open>t = ev a # t'\<close>)
      thus \<open>(t, X) \<in> \<F> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close>
        by (simp add: F_Det \<open>t = ev a # t'\<close>)
    qed
  qed
next

  fix t X assume \<open>(t, X) \<in> \<F> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close>
    \<open>t \<notin> \<D> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close>
  consider \<open>t = []\<close> | r_s t' where \<open>t = \<checkmark>(r_s) # t'\<close> | a t' where \<open>t = ev a # t'\<close>
    by (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust neq_Nil_conv)
  thus \<open>(t, X) \<in> \<F> (?lhs1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> ?lhs2)\<close>
  proof cases
    define X_P where \<open>X_P \<equiv> {ev a |a. ev a \<in> X \<and> a \<in> - (A \<union> A')} \<union>
                             {\<checkmark>(r) |r_s r s. tick_join r s = Some r_s \<and> \<checkmark>(r_s) \<in> X}\<close>
    define X_Q where \<open>X_Q \<equiv> {ev b |b. ev b \<in> X \<and> b \<in> - (B \<union> B')} \<union>
                             {\<checkmark>(s) |r_s r s. tick_join r s = Some r_s \<and> \<checkmark>(r_s) \<in> X}\<close>
    assume \<open>t = []\<close>
    with \<open>(t, X) \<in> \<F> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close>
    have \<open>X \<inter> ev ` A = {} \<and> X \<inter> ev ` B = {} \<and> X \<inter> ev ` (A' \<inter> B') = {}\<close>
      unfolding Det_projs F_Mprefix by auto
    with sets_assms(2, 4) have \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join X_P S X_Q\<close>
      by (simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def X_P_def X_Q_def
          subset_iff disjoint_iff image_iff)
        (metis IntI event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust)
    moreover have \<open>([], X_P) \<in> \<F> ?lhs1\<close> by (auto simp add: F_Mprefix X_P_def)
    moreover have \<open>([], X_Q) \<in> \<F> ?lhs2\<close> by (auto simp add: F_Mprefix X_Q_def)
    ultimately show \<open>(t, X) \<in> \<F> (?lhs1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> ?lhs2)\<close>
      by (simp add: \<open>t = []\<close> F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) (use Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil in blast)
  next
    fix r_s t' assume \<open>t = \<checkmark>(r_s) # t'\<close>
    with \<open>(t, X) \<in> \<F> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close>
    have False by (simp add: F_Det F_Mprefix)
    thus \<open>(t, X) \<in> \<F> (?lhs1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> ?lhs2)\<close> ..
  next
    fix x t' assume \<open>t = ev x # t'\<close>
    with \<open>(t, X) \<in> \<F> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close>
    consider (mv_left)  \<open>x \<in> A\<close> \<open>(t', X) \<in> \<F> (P x \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> ?lhs2)\<close>
      |      (mv_right) \<open>x \<in> B\<close> \<open>(t', X) \<in> \<F> (?lhs1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q x)\<close>
      |      (mv_both)  \<open>x \<in> A'\<close> \<open>x \<in> B'\<close> \<open>(t', X) \<in> \<F> (P x \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q x)\<close>
      unfolding F_Det F_Mprefix by auto
    thus \<open>(t, X) \<in> \<F> (?lhs1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> ?lhs2)\<close>
    proof cases
      case mv_left
      from mv_left(2) consider \<open>t' \<in> \<D> (P x \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> ?lhs2)\<close>
        | (fail) t_P t_Q X_P X_Q where
          \<open>(t_P, X_P) \<in> \<F> (P x)\<close> \<open>(t_Q, X_Q) \<in> \<F> ?lhs2\<close>
          \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close>
          \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join X_P S X_Q\<close>
        unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
      thus \<open>(t, X) \<in> \<F> (?lhs1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> ?lhs2)\<close>
      proof cases
        assume \<open>t' \<in> \<D> (P x \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> ?lhs2)\<close>
        hence \<open>t \<in> \<D> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close>
          by (simp add: D_Det D_Mprefix \<open>t = ev x # t'\<close> mv_left(1))
        with \<open>t \<notin> \<D> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close> have False ..
        thus \<open>(t, X) \<in> \<F> (?lhs1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> ?lhs2)\<close> ..
      next
        case fail
        have \<open>(ev x # t_P, X_P) \<in> \<F> ?lhs1\<close>  
          by (simp add: F_Mprefix fail(1) mv_left(1))
        moreover from \<open>t = ev x # t'\<close> fail(3) mv_left(1) \<open>A \<inter> S = {}\<close>
        have \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev x # t_P, t_Q), S)\<close>
          by (cases t_Q) (auto simp add: setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
        ultimately show \<open>(t, X) \<in> \<F> (?lhs1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> ?lhs2)\<close>
          using fail(2, 4) by (auto simp add: F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      qed
    next
      case mv_right
      from mv_right(2) consider \<open>t' \<in> \<D> (?lhs1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q x)\<close>
        | (fail) t_P t_Q X_P X_Q where
          \<open>(t_P, X_P) \<in> \<F> ?lhs1\<close> \<open>(t_Q, X_Q) \<in> \<F> (Q x)\<close>
          \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close>
          \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join X_P S X_Q\<close>
        unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
      thus \<open>(t, X) \<in> \<F> (?lhs1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> ?lhs2)\<close>
      proof cases
        assume \<open>t' \<in> \<D> (?lhs1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q x)\<close>
        hence \<open>t \<in> \<D> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close>
          by (simp add: D_Det D_Mprefix \<open>t = ev x # t'\<close> mv_right(1))
        with \<open>t \<notin> \<D> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close> have False ..
        thus \<open>(t, X) \<in> \<F> (?lhs1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> ?lhs2)\<close> ..
      next
        case fail
        have \<open>(ev x # t_Q, X_Q) \<in> \<F> ?lhs2\<close>  
          by (simp add: F_Mprefix fail(2) mv_right(1))
        moreover from \<open>t = ev x # t'\<close> fail(3) mv_right(1) \<open>B \<inter> S = {}\<close>
        have \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, ev x # t_Q), S)\<close>
          by (cases t_P) (auto simp add: setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
        ultimately show \<open>(t, X) \<in> \<F> (?lhs1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> ?lhs2)\<close>
          using fail(1, 4) by (auto simp add: F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      qed
    next
      case mv_both
      from mv_both(3) consider \<open>t' \<in> \<D> (P x \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q x)\<close>
        | (fail) t_P t_Q X_P X_Q where
          \<open>(t_P, X_P) \<in> \<F> (P x)\<close> \<open>(t_Q, X_Q) \<in> \<F> (Q x)\<close>
          \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), S)\<close> \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join X_P S X_Q\<close>
        unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
      thus \<open>(t, X) \<in> \<F> (?lhs1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> ?lhs2)\<close>
      proof cases
        assume \<open>t' \<in> \<D> (P x \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q x)\<close>
        hence \<open>t \<in> \<D> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close>
          by (simp add: D_Det D_Mprefix \<open>t = ev x # t'\<close> mv_both(1, 2))
        with \<open>t \<notin> \<D> (?rhs1 \<box> ?rhs2 \<box> ?rhs3)\<close> have False ..
        thus \<open>(t, X) \<in> \<F> (?lhs1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> ?lhs2)\<close> ..
      next
        case fail
        have \<open>(ev x # t_P, X_P) \<in> \<F> ?lhs1\<close>  
          by (simp add: F_Mprefix fail(1) mv_both(1))
        moreover have \<open>(ev x # t_Q, X_Q) \<in> \<F> ?lhs2\<close>  
          by (simp add: F_Mprefix fail(2) mv_both(2))
        moreover from \<open>t = ev x # t'\<close> fail(3) mv_both(1) \<open>A' \<subseteq> S\<close>
        have \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((ev x # t_P, ev x # t_Q), S)\<close> by auto
        ultimately show \<open>(t, X) \<in> \<F> (?lhs1 \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> ?lhs2)\<close>
          using fail(4) by (simp (no_asm) add: F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) blast
      qed
    qed
  qed
qed


corollary (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix:
  \<comment>\<open>This version is easier to use.\<close>
  \<open>\<box>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b\<in>B \<rightarrow> Q b =
   (\<box>a\<in>(A - S) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b\<in>B \<rightarrow> Q b)) \<box>
   (\<box>b\<in>(B - S) \<rightarrow> (\<box>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)) \<box>
   (\<box>x\<in>(A \<inter> B \<inter> S) \<rightarrow> (P x \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q x))\<close>
  by (subst Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix_bis
      [of \<open>A - S\<close> S \<open>A \<inter> S\<close> \<open>B - S\<close> \<open>B \<inter> S\<close>, simplified Un_Diff_Int])
    (simp_all add: Int_commute inf_left_commute)


corollary (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix_for_procomata:
  \<comment> \<open>Specialized version for Proc-Omata.\<close>
  \<open>\<box>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b\<in>B \<rightarrow> Q b =
   (\<box>a\<in>(A - S - B) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b\<in>B \<rightarrow> Q b))                          \<box>
   (\<box>b\<in>(B - S - A) \<rightarrow> (\<box>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b))                          \<box>
   (\<box>x\<in>(A \<inter> B - S) \<rightarrow> (P x \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b\<in>B \<rightarrow> Q b) \<sqinter> (\<box>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q x)) \<box>
   (\<box>x\<in>(A \<inter> B \<inter> S) \<rightarrow> (P x \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q x))\<close>
proof -
  have  * : \<open>\<box>a\<in>(A - S) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b\<in>B \<rightarrow> Q b) =
            (\<box>a\<in>(A - S - B) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b\<in>B \<rightarrow> Q b)) \<box>
            (\<box>a\<in>(A \<inter> B - S) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b\<in>B \<rightarrow> Q b))\<close>
    by (metis Diff_Int2 Diff_Int_distrib2 Mprefix_Un_distrib Un_Diff_Int)
  have ** : \<open>\<box>b\<in>(B - S) \<rightarrow> (\<box>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b) =
            (\<box>b\<in>(B - S - A) \<rightarrow> (\<box>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)) \<box>
            (\<box>b\<in>(A \<inter> B - S) \<rightarrow> (\<box>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b))\<close>
    by (metis (no_types) Int_Diff Int_commute Mprefix_Un_distrib Un_Diff_Int)
  have \<open>\<box>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b\<in>B \<rightarrow> Q b =
        (\<box>a\<in>(A - S - B) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b\<in>B \<rightarrow> Q b))    \<box>
        (\<box>b\<in>(B - S - A) \<rightarrow> (\<box>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b))    \<box>
        ((\<box>a\<in>(A \<inter> B - S) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b\<in>B \<rightarrow> Q b))   \<box>
         (\<box>b\<in>(A \<inter> B - S) \<rightarrow> (\<box>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)))  \<box>
        (\<box>x\<in>(A \<inter> B \<inter> S) \<rightarrow> (P x \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q x))\<close>
    unfolding Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix
    by (auto simp add: "**" Det_assoc intro!: arg_cong[where f = \<open>\<lambda>P. P \<box> _\<close>])
      (subst (3) Det_commute, subst Det_assoc,
        auto simp add: "*" Det_commute intro: arg_cong[where f = \<open>\<lambda>P. P \<box> _\<close>])
  also have \<open>(\<box>a\<in>(A \<inter> B - S) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b\<in>B \<rightarrow> Q b)) \<box>
             (\<box>b\<in>(A \<inter> B - S) \<rightarrow> (\<box>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)) =
             \<box>x\<in>(A \<inter> B - S) \<rightarrow> ((P x \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b\<in>B \<rightarrow> Q b)) \<sqinter> (\<box>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q x)\<close>
    by (simp add: Mprefix_Det_Mprefix, rule mono_Mprefix_eq, simp)
  finally show ?thesis .
qed


(*<*)
end
  (*>*)