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

chapter \<open>Continuity Rules\<close>

(*<*)
theory Sequential_Composition_Generalized_Cont
  imports Multi_Sequential_Composition_Generalized 
begin
  (*>*)


section \<open>Sequential Composition\<close>

subsection \<open>Monotonicity\<close>

lemma tickFree_mem_min_elems_D : \<open>t \<in> min_elems (\<D> P) \<Longrightarrow> tF t\<close>
  by (metis D_imp_front_tickFree Prefix_Order.prefixI append_self_conv elem_min_elems
            is_processT9 min_elems_no nonTickFree_n_frontTickFree not_Cons_self2)


lemma mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : \<open>P \<^bold>;\<^sub>\<checkmark> R \<sqsubseteq> Q \<^bold>;\<^sub>\<checkmark> S\<close> if \<open>P \<sqsubseteq> Q\<close> and \<open>R \<sqsubseteq> S\<close>
  for P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and R S :: \<open>'r \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof -
  let ?S = \<open>\<lambda>P R. map (ev \<circ> of_ev) ` min_elems (\<D> P) \<union>
                  {map (ev \<circ> of_ev) t @ u| t r u. t @ [\<checkmark>(r)] \<in> \<T> P \<and> t \<notin> \<D> P \<and>
                                                  tF t \<and> u \<in> min_elems (\<D> (R r))}\<close>
  { fix P and R :: \<open>'r \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and t
    assume \<open>t \<in> min_elems (\<D> (P \<^bold>;\<^sub>\<checkmark> R))\<close>
    hence * : \<open>t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> R)\<close> and ** : \<open>\<And>t'. t' \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> R) \<Longrightarrow> \<not> t' < t\<close>
      by (simp_all add: min_elems_def)
    from "*" consider (D_P) t' u where \<open>t = map (ev \<circ> of_ev) t' @ u\<close> \<open>t' \<in> \<D> P\<close> \<open>tF t'\<close> \<open>ftF u\<close>
      | (D_R) t' r u where \<open>t = map (ev \<circ> of_ev) t' @ u\<close> \<open>t' @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>t' \<notin> \<D> P\<close> \<open>tF t'\<close> \<open>u \<in> \<D> (R r)\<close>
      by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (metis D_imp_front_tickFree)
    hence \<open>t \<in> ?S P R\<close>
    proof cases
      case D_P
      from D_P(1-3) "**"[of \<open>map (ev \<circ> of_ev) t'\<close>] have \<open>u = []\<close>
        by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
          (metis strict_prefixI' append.right_neutral front_tickFree_Nil neq_Nil_conv)
      have \<open>t' \<in> min_elems (\<D> P)\<close>
      proof (rule ccontr)
        assume \<open>t' \<notin> min_elems (\<D> P)\<close>
        with D_P(2) obtain t'' where \<open>t'' \<in> \<D> P\<close> \<open>t'' < t'\<close> unfolding min_elems_def by fast
        with D_P(1, 3) "**"[of \<open>map (ev \<circ> of_ev) t''\<close>] show False
          by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs \<open>u = []\<close>)
            (metis (no_types, lifting) strict_prefixE' strict_prefix_simps(2) front_tickFree_Nil
              less_append list.simps(9) map_append self_append_conv tickFree_append_iff)
      qed
      thus \<open>t \<in> ?S P R\<close> by (simp add: D_P(1) \<open>u = []\<close>)
    next
      case D_R
      have \<open>u \<in> min_elems (\<D> (R r))\<close>
      proof (rule ccontr)
        assume \<open>u \<notin> min_elems (\<D> (R r))\<close>
        with D_R(5) obtain u' where \<open>u' \<in> \<D> (R r)\<close> \<open>u' < u\<close> unfolding min_elems_def by fast
        with D_R(1, 2, 4) "**"[of \<open>map (ev \<circ> of_ev) t' @ u'\<close>] show False
          by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (use less_append in blast)
      qed
      with D_R(1-4) show \<open>t \<in> ?S P R\<close> by auto
    qed
  } note "$" = this

  show \<open>P \<^bold>;\<^sub>\<checkmark> R \<sqsubseteq> Q \<^bold>;\<^sub>\<checkmark> S\<close>
  proof (rule below_trans)
    show \<open>P \<^bold>;\<^sub>\<checkmark> R \<sqsubseteq> Q \<^bold>;\<^sub>\<checkmark> R\<close>
    proof (unfold le_approx_def, safe)
      from le_approx1[OF \<open>P \<sqsubseteq> Q\<close>] le_approx_lemma_T[OF \<open>P \<sqsubseteq> Q\<close>]
      show \<open>t \<in> \<D> (Q \<^bold>;\<^sub>\<checkmark> R) \<Longrightarrow> t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> R)\<close> for t
        unfolding Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
    next
      from le_approx2[OF \<open>P \<sqsubseteq> Q\<close>] le_approx2T[OF \<open>P \<sqsubseteq> Q\<close>]
      show \<open>t \<notin> \<D> (P \<^bold>;\<^sub>\<checkmark> R) \<Longrightarrow> X \<in> \<R>\<^sub>a (P \<^bold>;\<^sub>\<checkmark> R) t \<Longrightarrow> X \<in> \<R>\<^sub>a (Q \<^bold>;\<^sub>\<checkmark> R) t\<close> for t X
        by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs Refusals_after_def)
          (metis F_imp_front_tickFree append.right_neutral front_tickFree_Nil is_processT9)
    next
      from le_approx2[OF \<open>P \<sqsubseteq> Q\<close>] le_approx2T[OF \<open>P \<sqsubseteq> Q\<close>] le_approx1[OF \<open>P \<sqsubseteq> Q\<close>]
      show \<open>t \<notin> \<D> (P \<^bold>;\<^sub>\<checkmark> R) \<Longrightarrow> X \<in> \<R>\<^sub>a (Q \<^bold>;\<^sub>\<checkmark> R) t \<Longrightarrow> X \<in> \<R>\<^sub>a (P \<^bold>;\<^sub>\<checkmark> R) t\<close> for t X
        by (simp add: subset_iff Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs Refusals_after_def)
          (metis D_T is_processT8)
    next

      show \<open>t \<in> min_elems (\<D> (P \<^bold>;\<^sub>\<checkmark> R)) \<Longrightarrow> t \<in> \<T> (Q \<^bold>;\<^sub>\<checkmark> R)\<close> for t
      proof (rule set_mp[OF _ "$"])
        from le_approx2T[OF \<open>P \<sqsubseteq> Q\<close>] le_approx3[OF \<open>P \<sqsubseteq> Q\<close>] show \<open>?S P R \<subseteq> \<T> (Q \<^bold>;\<^sub>\<checkmark> R)\<close>
          by (simp add: subset_iff Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
            (meson D_T elem_min_elems image_iff is_processT9 tickFree_mem_min_elems_D)
      qed
    qed
  next
    show \<open>Q \<^bold>;\<^sub>\<checkmark> R \<sqsubseteq> Q \<^bold>;\<^sub>\<checkmark> S\<close>
    proof (unfold le_approx_def, safe)
      from le_approx1[OF fun_belowD[OF \<open>R \<sqsubseteq> S\<close>]]
      show \<open>t \<in> \<D> (Q \<^bold>;\<^sub>\<checkmark> S) \<Longrightarrow> t \<in> \<D> (Q \<^bold>;\<^sub>\<checkmark> R)\<close> for t
        unfolding Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
    next
      from proc_ord2a[OF fun_belowD[OF \<open>R \<sqsubseteq> S\<close>]]
      show \<open>t \<notin> \<D> (Q \<^bold>;\<^sub>\<checkmark> R) \<Longrightarrow> X \<in> \<R>\<^sub>a (Q \<^bold>;\<^sub>\<checkmark> R) t \<Longrightarrow> X \<in> \<R>\<^sub>a (Q \<^bold>;\<^sub>\<checkmark> S) t\<close>
        \<open>t \<notin> \<D> (Q \<^bold>;\<^sub>\<checkmark> R) \<Longrightarrow> X \<in> \<R>\<^sub>a (Q \<^bold>;\<^sub>\<checkmark> S) t \<Longrightarrow> X \<in> \<R>\<^sub>a (Q \<^bold>;\<^sub>\<checkmark> R) t\<close> for t X
        by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs Refusals_after_def, metis)+
    next
      show \<open>t \<in> min_elems (\<D> (Q \<^bold>;\<^sub>\<checkmark> R)) \<Longrightarrow> t \<in> \<T> (Q \<^bold>;\<^sub>\<checkmark> S)\<close> for t
      proof (rule set_mp[OF _ "$"])
        from le_approx3[OF fun_belowD[OF \<open>R \<sqsubseteq> S\<close>]] show \<open>?S Q R \<subseteq> \<T> (Q \<^bold>;\<^sub>\<checkmark> S)\<close>
          by (simp add: subset_iff Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
            (meson D_T elem_min_elems image_iff tickFree_mem_min_elems_D)
      qed
    qed
  qed
qed



subsection \<open>Preliminaries\<close>

context begin

private lemma chain_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_left: \<open>chain Y \<Longrightarrow> chain (\<lambda>i. Y i \<^bold>;\<^sub>\<checkmark> S)\<close>
  by (simp add: mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k po_class.chain_def)

private lemma chain_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_right: \<open>chain Y \<Longrightarrow> chain (\<lambda>i. S \<^bold>;\<^sub>\<checkmark> Y i)\<close>
  by (simp add: mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k po_class.chain_def)


private lemma cont_left_prem_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>(\<Squnion>i. Y i) \<^bold>;\<^sub>\<checkmark> S = (\<Squnion>i. Y i \<^bold>;\<^sub>\<checkmark> S)\<close> (is \<open>?lhs = ?rhs\<close>) if \<open>chain Y\<close>
  \<comment> \<open>We have to add this hypothesis in the generalization.\<close>
proof (rule Process_eq_optimizedI)
  show \<open>t \<in> \<D> ?lhs \<Longrightarrow> t \<in> \<D> ?rhs\<close> for t
    by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs limproc_is_thelub ch2ch_fun \<open>chain Y\<close> lub_fun chain_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_left LUB_projs) blast
next
  have \<open>t \<in> \<D> ?lhs\<close> if \<open>t \<in> \<D> ?rhs\<close> and \<open>tF t\<close> for t
  proof (cases \<open>map (ev \<circ> of_ev) t \<in> \<D> (\<Squnion>i. Y i)\<close>)
    show \<open>map (ev \<circ> of_ev) t \<in> \<D> (\<Squnion>i. Y i) \<Longrightarrow> t \<in> \<D> ?lhs\<close>
      by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
        (metis append.right_neutral front_tickFree_Nil \<open>tF t\<close> tickFree_map_ev_comp tickFree_map_ev_of_ev_eq_iff)
  next
    define T1 and T2
      where \<open>T1 i \<equiv> {t1. \<exists>t2. t = map (ev \<circ> of_ev) t1 @ t2 \<and> t1 \<in> \<D> (Y i) \<and> tF t1 \<and> ftF t2}\<close>
        and \<open>T2 i \<equiv> {t1. \<exists>t2 r. t = map (ev \<circ> of_ev) t1 @ t2 \<and> t1 @ [\<checkmark>(r)] \<in> \<T> (Y i) \<and> tF t1 \<and> t2 \<in> \<D> (S r)}\<close> for i
    assume \<open>map (ev \<circ> of_ev) t \<notin> \<D> (\<Squnion>i. Y i)\<close>
    with \<open>t \<in> \<D> ?rhs\<close> have \<open>T1 i \<union> T2 i \<noteq> {}\<close> for i
      by (simp add: T1_def T2_def limproc_is_thelub chain_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_left \<open>chain Y\<close>
                    LUB_projs Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) fast
    moreover have \<open>finite (T1 0 \<union> T2 0)\<close>
      unfolding T1_def T2_def
      by (rule finite_subset[of _ \<open>{u. u \<le> map (ev \<circ> of_ev) t}\<close>])
        (use tickFree_map_ev_of_ev_eq_iff in \<open>force simp add: prefixes_fin\<close>)+
    moreover have \<open>T1 (Suc i) \<union> T2 (Suc i) \<subseteq> T1 i \<union> T2 i\<close> for i
      unfolding T1_def T2_def by (intro allI subsetI; simp)
        (metis (no_types, lifting) \<open>chain Y\<close> po_class.chainE le_approx_lemma_T le_approx1
          subsetD[of \<open>\<D> (Y (Suc i))\<close> \<open>\<D> (Y i)\<close>] subsetD[of \<open>\<T> (Y (Suc i))\<close> \<open>\<T> (Y i)\<close> \<open>_ @ [\<checkmark>(_)]\<close>])
    ultimately have \<open>(\<Inter>i. T1 i \<union> T2 i) \<noteq> {}\<close> by (rule Inter_nonempty_finite_chained_sets)
    then obtain t1 where * : \<open>\<forall>i. t1 \<in> T1 i \<union> T2 i\<close> by auto
    then obtain t2 where ** : \<open>t = map (ev \<circ> of_ev) t1 @ t2\<close> \<open>tF t1\<close> \<open>ftF t2\<close>
      by (auto simp add: T1_def T2_def dest: D_imp_front_tickFree)
    show \<open>t \<in> \<D> ?lhs\<close>
    proof (cases \<open>\<forall>i. t1 \<in> \<D> (Y i)\<close>)
      from "**" show \<open>\<forall>i. t1 \<in> \<D> (Y i) \<Longrightarrow> t \<in> \<D> ?lhs\<close>
        by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs limproc_is_thelub \<open>chain Y\<close> LUB_projs)
    next
      assume \<open>\<not> (\<forall>i. t1 \<in> \<D> (Y i))\<close>
      then obtain j where *** : \<open>j \<le> i \<Longrightarrow> t1 \<notin> \<D> (Y i)\<close> for i
        by (meson \<open>chain Y\<close> in_mono le_approx_def po_class.chain_mono)
      hence \<open>j \<le> i \<Longrightarrow> t1 \<notin> T1 i\<close> for i by (simp add: T1_def)
      with "*" have \<open>j \<le> i \<Longrightarrow> t1 \<in> T2 i\<close> for i by blast
      then obtain r where \<open>t1 @ [\<checkmark>(r)] \<in> \<T> (Y j)\<close> \<open>t2 \<in> \<D> (S r)\<close>
        unfolding T2_def by (auto simp add: "**"(1))
      from this(1) \<open>chain Y\<close> "***" have \<open>j \<le> i \<Longrightarrow> t1 @ [\<checkmark>(r)] \<in> \<T> (Y i)\<close> for i
        by (metis eq_imp_le is_processT9 le_approx2T po_class.chain_mono)
      hence \<open>t1 @ [\<checkmark>(r)] \<in> \<T> (\<Squnion>i. Y i)\<close>
        by (meson "***" \<open>chain Y\<close> dual_order.refl is_processT9 is_ub_thelub le_approx2T)
      with \<open>t2 \<in> \<D> (S r)\<close> "**"(1, 2) show \<open>t \<in> \<D> ?lhs\<close>
        by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
    qed
  qed
  thus \<open>t \<in> \<D> ?rhs \<Longrightarrow> t \<in> \<D> ?lhs\<close> for t
    by (meson D_imp_front_tickFree div_butlast_when_non_tickFree_iff front_tickFree_iff_tickFree_butlast)
next
  show \<open>(t, X) \<in> \<F> ?lhs \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> for t X
    by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs limproc_is_thelub ch2ch_fun \<open>chain Y\<close> lub_fun chain_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_left LUB_projs) blast
next
  fix t X assume \<open>(t, X) \<in> \<F> ?rhs\<close> \<open>t \<notin> \<D> ?rhs\<close>
  from \<open>t \<notin> \<D> ?rhs\<close> obtain j where \<open>t \<notin> \<D> (Y j \<^bold>;\<^sub>\<checkmark> S)\<close>
    by (auto simp add: limproc_is_thelub chain_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_left \<open>chain Y\<close> LUB_projs)
  moreover from \<open>(t, X) \<in> \<F> ?rhs\<close> have \<open>(t, X) \<in> \<F> (Y j \<^bold>;\<^sub>\<checkmark> S)\<close>
    by (simp add: limproc_is_thelub chain_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_left \<open>chain Y\<close> F_LUB)
  ultimately show \<open>(t, X) \<in> \<F> ?lhs\<close>
    by (fact le_approx2[OF mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF is_ub_thelub[OF \<open>chain Y\<close>] below_refl], THEN iffD2])
qed



lemma \<open>finite R \<Longrightarrow> chain Y \<Longrightarrow> \<sqinter>r \<in> R. (\<Squnion>i. Y i r) = (\<Squnion>i. \<sqinter>r \<in> R. Y i r)\<close>
  by (subst cont2contlubE[of \<open>GlobalNdet R\<close>, symmetric])
    (simp_all add: lub_fun)


lemma infinite_GlobalNdet_not_cont :
  \<comment> \<open>This is a counter example.\<close>
  defines Y_def : \<open>Y \<equiv> \<lambda>i r :: nat. if r \<le> i then STOP else \<bottom> :: (nat, nat) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  shows \<open>chain Y\<close> \<open>\<sqinter>r \<in> UNIV. (\<Squnion>i. Y i r) \<noteq> (\<Squnion>i. \<sqinter>r \<in> UNIV. Y i r)\<close>
proof -
  show *  : \<open>chain Y\<close> unfolding Y_def by (auto intro!: chainI fun_belowI)
  have ** : \<open>chain (\<lambda>i. Y i r)\<close> for r by (simp add: \<open>chain Y\<close> ch2ch_fun)

  have \<open>(\<Squnion>i. Y i) = (\<lambda>r. STOP)\<close>
    by (rule ext, simp add: STOP_iff_T lub_fun limproc_is_thelub T_LUB "*" "**")
      (auto simp add: Y_def T_STOP split: if_split_asm)
  hence $ : \<open>\<sqinter>r \<in> UNIV. (\<Squnion>i. Y i r) = STOP\<close>
    by (simp add: GlobalNdet_is_STOP_iff "*" lub_fun)

  have \<open>\<sqinter>r \<in> UNIV. Y i r = \<bottom>\<close> for i
    by (simp add: BOT_iff_Nil_D D_GlobalNdet Y_def D_BOT)
      (use Suc_n_not_le_n in blast)
  hence $$ : \<open>(\<Squnion>i. \<sqinter>r \<in> UNIV. Y i r) = \<bottom>\<close> by simp

  from $ $$ show \<open>\<sqinter>r \<in> UNIV. (\<Squnion>i. Y i r) \<noteq> (\<Squnion>i. \<sqinter>r \<in> UNIV. Y i r)\<close> by simp
qed

text \<open>The same counter-example works for @{const [source] Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k}.\<close>

lemma infinite_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_not_cont :
  \<comment> \<open>This is a counter example.\<close>
  defines P_def : \<open>P \<equiv> SKIPS UNIV :: (nat, nat) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and Y_def : \<open>Y \<equiv> \<lambda>i r :: nat. if r \<le> i then STOP else \<bottom> :: (nat, nat) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  shows \<open>chain Y\<close> \<open>P \<^bold>;\<^sub>\<checkmark> (\<Squnion>i. Y i) \<noteq> (\<Squnion>i. P \<^bold>;\<^sub>\<checkmark> Y i)\<close>
proof -
  show *  : \<open>chain Y\<close> unfolding Y_def by (auto intro!: chainI fun_belowI)
  have \<open>P \<^bold>;\<^sub>\<checkmark> (\<Squnion>i. Y i) = \<sqinter>r \<in> UNIV. (\<Squnion>i. Y i r)\<close>
    by (simp add: P_def "*" lub_fun)
  also have \<open>\<dots> \<noteq> (\<Squnion>i. \<sqinter>r \<in> UNIV. Y i r)\<close>
    unfolding P_def Y_def by (fact infinite_GlobalNdet_not_cont(2))
  also have \<open>(\<Squnion>i. \<sqinter>r \<in> UNIV. Y i r) = (\<Squnion>i. P \<^bold>;\<^sub>\<checkmark> Y i)\<close>
    by (simp add: P_def)
  finally show \<open>P \<^bold>;\<^sub>\<checkmark> (\<Squnion>i. Y i) \<noteq> (\<Squnion>i. P \<^bold>;\<^sub>\<checkmark> Y i)\<close> .
qed


text \<open>We must therefore find a condition under which @{const [source] Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k} is continuous.\<close>

private lemma cont_right_prem_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>S \<^bold>;\<^sub>\<checkmark> (\<Squnion>i. Y i) = (\<Squnion>i. S \<^bold>;\<^sub>\<checkmark> Y i)\<close> (is \<open>?lhs = ?rhs\<close>) if \<open>chain Y\<close> and \<open>\<bbbF>\<^sub>\<checkmark>(S)\<close>
  \<comment> \<open>We have to add this hypothesis in the generalization.\<close>
proof (rule Process_eq_optimizedI)
  show \<open>t \<in> \<D> ?lhs \<Longrightarrow> t \<in> \<D> ?rhs\<close> for t
    by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs limproc_is_thelub ch2ch_fun \<open>chain Y\<close> lub_fun chain_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_right D_LUB) blast
next
  have \<open>t \<in> \<D> ?lhs\<close> if \<open>t \<in> \<D> ?rhs\<close> and \<open>tF t\<close> for t
  proof (cases \<open>map (ev \<circ> of_ev) t \<in> \<D> S\<close>)
    show \<open>map (ev \<circ> of_ev) t \<in> \<D> S \<Longrightarrow> t \<in> \<D> ?lhs\<close>
      by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
        (metis append.right_neutral front_tickFree_Nil \<open>tF t\<close> tickFree_map_ev_comp tickFree_map_ev_of_ev_eq_iff)
  next
    define T where \<open>T i \<equiv> {t1. \<exists>t2 r. t = map (ev \<circ> of_ev) t1 @ t2 \<and> t1 @ [\<checkmark>(r)] \<in> \<T> S \<and> tF t1 \<and> t2 \<in> \<D> (Y i r)}\<close> for i
    assume \<open>map (ev \<circ> of_ev) t \<notin> \<D> S\<close>
    with \<open>t \<in> \<D> ?rhs\<close> have \<open>T i \<noteq> {}\<close> for i
      by (fastforce simp add: T_def limproc_is_thelub chain_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_right \<open>chain Y\<close>
                    D_LUB Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs is_processT7 tickFree_map_ev_of_ev_same_type_is)
    moreover have \<open>finite (T 0)\<close>
      unfolding T_def
      by (rule finite_subset[of _ \<open>{u. u \<le> map (ev \<circ> of_ev) t}\<close>])
        (use tickFree_map_ev_of_ev_eq_iff in \<open>force simp add: prefixes_fin\<close>)+
    moreover have \<open>T (Suc i) \<subseteq> T i\<close> for i
      unfolding T_def by (intro allI Un_mono subsetI; simp)
        (metis \<open>chain Y\<close> fun_below_iff subset_iff[of \<open>\<D> (Y (Suc i) _)\<close> \<open>\<D> (Y i _)\<close>]
               po_class.chainE le_approx1)
    ultimately have \<open>(\<Inter>i. T i) \<noteq> {}\<close> by (rule Inter_nonempty_finite_chained_sets)
    then obtain t1 where \<open>\<forall>i. t1 \<in> T i\<close> by auto
    then obtain t2 where * : \<open>t = map (ev \<circ> of_ev) t1 @ t2\<close>
      \<open>tF t1\<close> \<open>\<forall>i. \<exists>r. t1 @ [\<checkmark>(r)] \<in> \<T> S \<and> t2 \<in> \<D> (Y i r)\<close>
      by (simp add: T_def) blast
    have \<open>t1 \<in> \<T> S\<close> by (meson "*"(3) prefixI is_processT3_TR)
    from "*"(1, 2) \<open>map (ev \<circ> of_ev) t \<notin> \<D> S\<close>
    have \<open>t1 \<notin> \<D> S\<close> using is_processT7 tickFree_map_ev_of_ev_eq_iff by fastforce
    define U where \<open>U i \<equiv> {r. t1 @ [\<checkmark>(r)] \<in> \<T> S \<and> t2 \<in> \<D> (Y i r)}\<close> for i
    from "*"(3) have \<open>U i \<noteq> {}\<close> for i by (simp add: U_def)
    moreover have \<open>finite (U 0)\<close>
    proof (rule finite_subset[of _ \<open>{r. t1 @ [\<checkmark>(r)] \<in> \<T> S}\<close>])
      show \<open>U 0 \<subseteq> {r. t1 @ [\<checkmark>(r)] \<in> \<T> S}\<close> unfolding U_def by blast
    next
      show \<open>finite {r. t1 @ [\<checkmark>(r)] \<in> \<T> S}\<close>
        by (simp add: \<open>\<bbbF>\<^sub>\<checkmark>(S)\<close> \<open>t1 \<notin> \<D> S\<close> finite_ticksD)
    qed
    moreover have \<open>U (Suc i) \<subseteq> U i\<close> for i
      by (simp add: U_def subset_iff)
        (meson fun_below_iff in_mono le_approx1 chainE \<open>chain Y\<close>)
    ultimately have \<open>(\<Inter>i. U i) \<noteq> {}\<close> by (rule Inter_nonempty_finite_chained_sets)
    then obtain r where ** : \<open>\<forall>i. r \<in> U i\<close> by auto
    with "*" show \<open>t \<in> \<D> ?lhs\<close>
      by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs U_def \<open>chain Y\<close> ch2ch_fun limproc_is_thelub D_LUB lub_fun) blast
  qed
  thus \<open>t \<in> \<D> ?rhs \<Longrightarrow> t \<in> \<D> ?lhs\<close> for t
    by (meson D_imp_front_tickFree div_butlast_when_non_tickFree_iff front_tickFree_iff_tickFree_butlast)
next
  show \<open>(t, X) \<in> \<F> ?lhs \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> for t X
    by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs limproc_is_thelub ch2ch_fun \<open>chain Y\<close> lub_fun chain_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_right F_LUB) blast
next
  fix t X assume \<open>(t, X) \<in> \<F> ?rhs\<close> \<open>t \<notin> \<D> ?rhs\<close>
  from \<open>t \<notin> \<D> ?rhs\<close> obtain j where \<open>t \<notin> \<D> (S \<^bold>;\<^sub>\<checkmark> Y j)\<close>
    by (auto simp add: limproc_is_thelub chain_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_right \<open>chain Y\<close> D_LUB)
  moreover from \<open>(t, X) \<in> \<F> ?rhs\<close> have \<open>(t, X) \<in> \<F> (S \<^bold>;\<^sub>\<checkmark> Y j)\<close>
    by (simp add: limproc_is_thelub chain_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_right \<open>chain Y\<close> F_LUB)
  ultimately show \<open>(t, X) \<in> \<F> ?lhs\<close>
    by (fact le_approx2[OF mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF below_refl is_ub_thelub[OF \<open>chain Y\<close>]], THEN iffD2])
qed



subsection \<open>Continuity\<close>

text \<open>
We then spent a lot of time trying to prove the continuity
under the assumption of \<^const>\<open>finite_ticks_fun\<close>.
\<close>


lemma Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_cont [simp] : \<open>cont (\<lambda>x. f x \<^bold>;\<^sub>\<checkmark> g x)\<close>
  if \<open>cont f\<close> and \<open>cont g\<close> and \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f)\<close>
  for g :: \<open>_ \<Rightarrow> _ \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof (rule cont_apply[where f = \<open>\<lambda>x y. f x \<^bold>;\<^sub>\<checkmark> y\<close>])
  show \<open>cont g\<close> by (fact \<open>cont g\<close>)
next
  show \<open>cont (\<lambda>x. f x \<^bold>;\<^sub>\<checkmark> y)\<close> for y :: \<open>_ \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  proof (rule contI2)
    show \<open>monofun (\<lambda>x. f x \<^bold>;\<^sub>\<checkmark> y)\<close> by (simp add: cont2monofunE mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k monofunI \<open>cont f\<close>)
  next
    show \<open>chain Y \<Longrightarrow> f (\<Squnion>i. Y i) \<^bold>;\<^sub>\<checkmark> y \<sqsubseteq> (\<Squnion>i. f (Y i) \<^bold>;\<^sub>\<checkmark> y)\<close> for Y
      by (simp add: ch2ch_cont cont2contlubE cont_left_prem_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<open>cont f\<close>)
  qed
next
  show \<open>cont (\<lambda>y :: _ \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k. f x \<^bold>;\<^sub>\<checkmark> y)\<close> for x
  proof (rule contI2)
    show \<open>monofun ((\<^bold>;\<^sub>\<checkmark>) (f x))\<close> by (simp add: mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k monofunI)
  next
    show \<open>chain Y \<Longrightarrow> f x \<^bold>;\<^sub>\<checkmark> (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. f x \<^bold>;\<^sub>\<checkmark> Y i)\<close>
    for Y :: \<open>_ \<Rightarrow> _ \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
      oops
        \<comment> \<open>Unfortunately here, we cannot use @{thm [source] cont_right_prem_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k}
    since there is no reason for \<^term>\<open>\<bbbF>\<^sub>\<checkmark>(x)\<close> to hold.
    Actually, we can find a counter example.\<close>


text \<open>
We could therefore only prove the weaker following version.
\<close>


lemma Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_cont [simp] : \<open>cont (\<lambda>x. f x \<^bold>;\<^sub>\<checkmark> g x)\<close>
  if \<open>cont f\<close> and \<open>cont g\<close> and \<open>\<And>x. \<bbbF>\<^sub>\<checkmark>(f x)\<close>
  for g :: \<open>_ \<Rightarrow> _ \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof (rule cont_apply[where f = \<open>\<lambda>x y. f x \<^bold>;\<^sub>\<checkmark> y\<close>])
  show \<open>cont g\<close> by (fact \<open>cont g\<close>)
next
  show \<open>cont (\<lambda>x. f x \<^bold>;\<^sub>\<checkmark> y)\<close> for y :: \<open>_ \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  proof (rule contI2)
    show \<open>monofun (\<lambda>x. f x \<^bold>;\<^sub>\<checkmark> y)\<close> by (simp add: cont2monofunE mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k monofunI \<open>cont f\<close>)
  next
    show \<open>chain Y \<Longrightarrow> f (\<Squnion>i. Y i) \<^bold>;\<^sub>\<checkmark> y \<sqsubseteq> (\<Squnion>i. f (Y i) \<^bold>;\<^sub>\<checkmark> y)\<close> for Y
      by (simp add: ch2ch_cont cont2contlubE cont_left_prem_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<open>cont f\<close>)
  qed
next
  show \<open>cont (\<lambda>y :: _ \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k. f x \<^bold>;\<^sub>\<checkmark> y)\<close> for x
  proof (rule contI2)
    show \<open>monofun ((\<^bold>;\<^sub>\<checkmark>) (f x))\<close> by (simp add: mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k monofunI)
  next
    show \<open>chain Y \<Longrightarrow> f x \<^bold>;\<^sub>\<checkmark> (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. f x \<^bold>;\<^sub>\<checkmark> Y i)\<close>
      for Y :: \<open>_ \<Rightarrow> _ \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
      by (simp add: cont_right_prem_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<open>\<And>x. \<bbbF>\<^sub>\<checkmark>(f x)\<close>)
  qed
qed

end (* private context *)


corollary \<open>cont f \<Longrightarrow> cont g \<Longrightarrow> cont (\<lambda>x. f x \<^bold>;\<^sub>\<checkmark> g x)\<close>
  for f :: \<open>'b :: cpo \<Rightarrow> ('a, 'r :: finite) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> 
  by (simp add: finite_ticks_simps(5))




lemma MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_cont[simp]:
  \<open>\<lbrakk>\<And>l. l \<in> set L \<Longrightarrow> cont (f l); \<And>l r x. l \<in> set (butlast L) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(f l x r)\<rbrakk>
   \<Longrightarrow> cont (\<lambda>x. (SEQ\<^sub>\<checkmark> l \<in>@ L. f l x) r)\<close>
proof (induct L arbitrary: r)
  show \<open>\<And>r. cont (\<lambda>x. (SEQ\<^sub>\<checkmark> l \<in>@ []. f l x) r)\<close> by simp
next
  case (Cons l0 L)
  show \<open>cont (\<lambda>x. (SEQ\<^sub>\<checkmark> l \<in>@ (l0 # L). f l x) r)\<close>
  proof (cases \<open>L = []\<close>)
    show \<open>L = [] \<Longrightarrow> cont (\<lambda>x. (SEQ\<^sub>\<checkmark> l \<in>@ (l0 # L). f l x) r)\<close>
      by (simp add: Cons.prems(1) cont2cont_fun)
  next
    show \<open>cont (\<lambda>x. (SEQ\<^sub>\<checkmark> l \<in>@ (l0 # L). f l x) r)\<close> if \<open>L \<noteq> []\<close>
    proof (subst MultiSeq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Cons, intro cont2cont_lambda Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_cont)
      show \<open>cont (\<lambda>x. f l0 x r)\<close> by (simp add: Cons.prems(1) cont2cont_fun)
    next
      have \<open>cont (\<lambda>x. (SEQ\<^sub>\<checkmark> l \<in>@ L. f l x))\<close>
        by (rule cont2cont_lambda, rule Cons.hyps)
          (simp_all add: Cons.prems(1, 2) \<open>L \<noteq> []\<close>)
      thus \<open>cont (\<lambda>x. (SEQ\<^sub>\<checkmark> l \<in>@ L. f l x) y)\<close> for y
        by (fact cont2cont_fun)
    next
      show \<open>\<bbbF>\<^sub>\<checkmark>(f l0 x r)\<close> for x by (simp add: Cons.prems(2) that)
    qed
  qed
qed



(*<*)
end
  (*>*)