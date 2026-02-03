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

(*<*)
theory Synchronization_Product_Generalized_Cont
  imports Multi_Synchronization_Product_Generalized
begin
  (*>*)


section \<open>Synchronization Product\<close>


context Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale begin


subsection \<open>Monotonicity\<close>

lemma mono_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : \<open>P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q \<sqsubseteq> P' \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q'\<close> if \<open>P \<sqsubseteq> P'\<close> and \<open>Q \<sqsubseteq> Q'\<close>
proof (unfold le_approx_def Refusals_after_def, safe)
  from le_approx1[OF \<open>P \<sqsubseteq> P'\<close>] le_approx_lemma_T[OF \<open>P \<sqsubseteq> P'\<close>]
    le_approx1[OF \<open>Q \<sqsubseteq> Q'\<close>] le_approx_lemma_T[OF \<open>Q \<sqsubseteq> Q'\<close>]
  show \<open>t \<in> \<D> (P' \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q') \<Longrightarrow> t \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close> for t
    by (simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) fast
next
  from le_approx2[OF \<open>P \<sqsubseteq> P'\<close>] le_approx2[OF \<open>Q \<sqsubseteq> Q'\<close>]
  show \<open>t \<notin> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q) \<Longrightarrow> (t, X) \<in> \<F> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q) \<Longrightarrow>
        (t, X) \<in> \<F> (P' \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q')\<close> for t X
    by (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs', elim disjE)
      (metis F_T front_tickFree_Nil self_append_conv, metis)
next
  from le_approx_lemma_F[OF \<open>P \<sqsubseteq> P'\<close>] le_approx_lemma_F[OF \<open>Q \<sqsubseteq> Q'\<close>]
    le_approx1[OF \<open>P \<sqsubseteq> P'\<close>] le_approx_lemma_T[OF \<open>P \<sqsubseteq> P'\<close>] 
    le_approx1[OF \<open>Q \<sqsubseteq> Q'\<close>] le_approx_lemma_T[OF \<open>Q \<sqsubseteq> Q'\<close>]
  show \<open>t \<notin> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q) \<Longrightarrow> (t, X) \<in> \<F> (P' \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q') \<Longrightarrow>
        (t, X) \<in> \<F> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close> for t X
    by (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs subset_iff, elim disjE) metis+
next
  fix t assume \<open>t \<in> min_elems (\<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q))\<close>
  hence \<open>t \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close> by (fact elem_min_elems)
  then obtain u v t_P t_Q
    where * : \<open>t = u @ v\<close> \<open>tF u\<close> \<open>ftF v\<close>
      \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), A)\<close>
      \<open>t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q\<close>
    unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
  have \<open>v = []\<close>
  proof (rule ccontr)
    assume \<open>v \<noteq> []\<close>
    with "*"(1) have \<open>u < t\<close> by (simp add: dual_order.strict_iff_not)
    moreover from "*"(2,4,5) have \<open>u \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      by (simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) (use front_tickFree_Nil in blast)
    ultimately show False
      using \<open>t \<in> min_elems (\<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q))\<close> min_elems_no order_less_imp_le by blast
  qed

  have \<open>t_P \<in> min_elems (\<D> P)\<close> if \<open>t_P \<in> \<D> P\<close>
  proof (rule ccontr)
    assume \<open>t_P \<notin> min_elems (\<D> P)\<close>
    with \<open>t_P \<in> \<D> P\<close> obtain t_P' where \<open>t_P' < t_P\<close> \<open>t_P' \<in> \<D> P\<close>
      by (metis antisym_conv2 elem_min_elems min_elems5)
    from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_less_prefixL[OF "*"(4) \<open>t_P' < t_P\<close>]
    obtain u' t_Q'
      where $ : \<open>u' < u\<close> \<open>t_Q' \<le> t_Q\<close>
        \<open>u' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P', t_Q'), A)\<close> by blast
    from "*"(5) D_T have \<open>t_Q \<in> \<T> Q\<close> by blast
    with "$"(2,3) \<open>t_P' \<in> \<D> P\<close> have \<open>u' \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      by (simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k')
        (metis append.right_neutral front_tickFree_Nil is_processT3_TR)
    moreover from \<open>u' < u\<close> have \<open>u' < t\<close>
      by (simp add: "*"(1)) (meson Prefix_Order.prefixI dual_order.strict_trans1)
    ultimately show False
      using \<open>t \<in> min_elems (\<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q))\<close> min_elems_no nless_le by blast
  qed
  with "*"(5) have \<open>t_P \<in> \<T> P'\<close>
    by (meson in_mono le_approx2T le_approx3 \<open>P \<sqsubseteq> P'\<close>)

  have \<open>t_Q \<in> min_elems (\<D> Q)\<close> if \<open>t_Q \<in> \<D> Q\<close>
  proof (rule ccontr)
    assume \<open>t_Q \<notin> min_elems (\<D> Q)\<close>
    with \<open>t_Q \<in> \<D> Q\<close> obtain t_Q' where \<open>t_Q' < t_Q\<close> \<open>t_Q' \<in> \<D> Q\<close>
      by (metis antisym_conv2 elem_min_elems min_elems5)
    from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_less_prefixR[OF "*"(4) \<open>t_Q' < t_Q\<close>]
    obtain u' t_P'
      where $ : \<open>u' < u\<close> \<open>t_P' \<le> t_P\<close>
        \<open>u' setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P', t_Q'), A)\<close> by blast
    from "*"(5) D_T have \<open>t_P \<in> \<T> P\<close> by blast
    with "$"(2,3) \<open>t_Q' \<in> \<D> Q\<close> have \<open>u' \<in> \<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      by (simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k')
        (metis append.right_neutral front_tickFree_Nil is_processT3_TR)
    moreover from \<open>u' < u\<close> have \<open>u' < t\<close>
      by (simp add: "*"(1)) (meson Prefix_Order.prefixI dual_order.strict_trans1)
    ultimately show False
      using \<open>t \<in> min_elems (\<D> (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q))\<close> min_elems_no nless_le by blast
  qed
  with "*"(5) have \<open>t_Q \<in> \<T> Q'\<close>
    by (meson in_mono le_approx2T le_approx3 \<open>Q \<sqsubseteq> Q'\<close>)

  from \<open>t_P \<in> \<T> P'\<close> \<open>t_Q \<in> \<T> Q'\<close> "*"(4) show \<open>t \<in> \<T> (P' \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q')\<close>
    by (auto simp add: "*"(1) \<open>v = []\<close> T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
qed



subsection \<open>Preliminaries\<close>

lemma chain_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_left  : \<open>chain Y \<Longrightarrow> chain (\<lambda>i. Y i \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close>
  and chain_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_right : \<open>chain Z \<Longrightarrow> chain (\<lambda>i. P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Z i)\<close>
  by (simp_all add: chain_def mono_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) 


lemma cont_left_prem_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>(\<Squnion>i. Y i) \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q = (\<Squnion>i. Y i \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close> if chain: \<open>chain Y\<close>
proof (rule Process_eq_optimizedI)
  show \<open>t \<in> \<D> ((\<Squnion>i. Y i) \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q) \<Longrightarrow> t \<in> \<D> (\<Squnion>i. Y i \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close> for t
    by (simp add: limproc_is_thelub chain chain_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_left D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k D_LUB T_LUB) blast
next
  show \<open>(t, X) \<in> \<F> ((\<Squnion>i. Y i) \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q) \<Longrightarrow> (t, X) \<in> \<F> (\<Squnion>i. Y i \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close> for t X
    by (simp add: limproc_is_thelub chain chain_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_left F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k D_LUB T_LUB F_LUB) blast
next
  fix t
  assume \<open>t \<in> \<D> (\<Squnion>i. Y i \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close>
  define S
    where \<open>S i \<equiv> {(t_Y, t_Q, u). \<exists>v. tF u \<and> ftF v \<and> t = u @ v \<and>
                                      u setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_Y, t_Q), A) \<and>
                                      (t_Y \<in> \<D> (Y i) \<and> t_Q \<in> \<T> Q \<or> t_Y \<in> \<T> (Y i) \<and> t_Q \<in> \<D> Q)}\<close> for i
  from \<open>t \<in> \<D> (\<Squnion>i. Y i \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close> have \<open>S i \<noteq> {}\<close> for i
    by (simp add: S_def limproc_is_thelub chain chain_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_left D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k D_LUB) fast
  moreover have \<open>finite (S 0)\<close>
    by (rule finite_subset[OF _ finite_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick_join_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k])
      (auto simp add: S_def)
  moreover from le_approx1[OF po_class.chainE[OF chain]] D_T
    le_approx2T[OF po_class.chainE[OF chain]]
  have \<open>S (Suc i) \<subseteq> S i\<close> for i by (simp add: S_def) blast
  ultimately have \<open>(\<Inter>i. S i) \<noteq> {}\<close> by (rule Inter_nonempty_finite_chained_sets)
  then obtain t_Y t_Q u where \<open>(t_Y, t_Q, u) \<in> (\<Inter>i. S i)\<close> by auto
  hence \<open>tF u \<and> ftF (drop (length u) t) \<and>
         t = u @ drop (length u) t \<and> u setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_Y, t_Q), A) \<and> 
         ((\<forall>i. t_Y \<in> \<D> (Y i)) \<and> t_Q \<in> \<T> Q \<or> (\<forall>i. t_Y \<in> \<T> (Y i)) \<and> t_Q \<in> \<D> Q)\<close>
    by (auto simp add: S_def) (meson chain_lemma le_approx1 le_approx_lemma_T subsetD chain)
  show \<open>t \<in> \<D> ((\<Squnion>i. Y i) \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close>
    by (simp add: limproc_is_thelub chain D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k T_LUB D_LUB)
      (use \<open>?this\<close> in blast)
next
  fix t X assume \<open>(t, X) \<in> \<F> (\<Squnion>i. Y i \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close> \<open>t \<notin> \<D>(\<Squnion>i. Y i \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close>
  have \<open>Y i \<sqsubseteq> (\<Squnion>i. Y i)\<close> for i by (simp add: is_ub_thelub \<open>chain Y\<close>)
  moreover from \<open>t \<notin> \<D>(\<Squnion>i. Y i \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close> obtain j where \<open>t \<notin> \<D> (Y j \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close>
    by (auto simp add: limproc_is_thelub chain_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_left \<open>chain Y\<close> D_LUB)
  moreover from \<open>(t, X) \<in> \<F> (\<Squnion>i. Y i \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close> have \<open>(t, X) \<in> \<F> (Y j \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close>
    by (simp add: limproc_is_thelub chain_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_left \<open>chain Y\<close> F_LUB)
  ultimately show \<open>(t, X) \<in> \<F> ((\<Squnion>i. Y i) \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q)\<close>
    by (metis (mono_tags, lifting) below_refl le_approx2 mono_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
qed


lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) cont_right_prem_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> (\<Squnion>i. Z i) = (\<Squnion>i. P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Z i)\<close> if \<open>chain Z\<close>
  by (subst (1 2) Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym)
    (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.cont_left_prem_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF \<open>chain Z\<close>])



subsection \<open>Continuity\<close>

lemma Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_cont[simp]: \<open>cont (\<lambda>x. f x \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> g x)\<close> if \<open>cont f\<close> \<open>cont g\<close>
proof (rule cont_apply[where f = \<open>\<lambda>x y. y \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> g x\<close>])
  from \<open>cont f\<close> show \<open>cont f\<close> .
next
  show \<open>cont (\<lambda>y. y \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> g x)\<close> for x
  proof (rule contI2)
    show \<open>monofun (\<lambda>y. y \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> g x)\<close> by (simp add: monofunI mono_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  next
    show \<open>chain Y \<Longrightarrow> (\<Squnion>i. Y i) \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> g x \<sqsubseteq> (\<Squnion>i. Y i \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> g x)\<close> for Y
      by (simp add: cont_left_prem_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  qed
next
  show \<open>cont (\<lambda>x. y \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> g x)\<close> for y
  proof (rule cont_compose[of \<open>\<lambda>x. y \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> x\<close>])
    show \<open>cont (\<lambda>x. y \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> x)\<close>
    proof (rule contI2)
      show \<open>monofun (Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k y A)\<close> by (simp add: monofunI mono_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    next
      show \<open>chain Z \<Longrightarrow> y \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> (\<Squnion>i. Z i) \<sqsubseteq> (\<Squnion>i. y \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Z i)\<close> for Z
        by (simp add: cont_right_prem_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    qed
  next
    from \<open>cont g\<close> show \<open>cont g\<close> .
  qed
qed

end



lemma MultiSync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_cont [simp] :
  \<open>(\<And>l. l \<in> set L \<Longrightarrow> cont (P l)) \<Longrightarrow> cont (\<lambda>x. \<^bold>\<lbrakk>S\<^bold>\<rbrakk>\<^sub>\<checkmark> l \<in>@ L. P l x)\<close>
  by (induct L rule: induct_list012)
    (auto intro: RenamingTick_cont inj_imp_finitary injI)



(*<*)
end
  (*>*)