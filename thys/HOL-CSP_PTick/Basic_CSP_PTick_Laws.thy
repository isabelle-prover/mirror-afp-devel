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


chapter \<open>First Laws\<close>

(*<*)
theory Basic_CSP_PTick_Laws
  imports Sequential_Composition_Generalized CSP_PTick_Renaming Finite_Ticks
begin
  (*>*)

unbundle option_type_syntax


section \<open>Behaviour with Constant Processes\<close>

text \<open>By ``basic'' laws we mean the behaviour of \<^term>\<open>\<bottom>\<close>, \<^const>\<open>STOP\<close> and \<^const>\<open>SKIP\<close>,
      plus the associativity of some concerned operators.\<close>


lemma Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_const [simp] : \<open>P \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q) = P \<^bold>; Q\<close>
  \<comment> \<open>Very basic law.\<close>
  by (simp add: Process_eq_spec Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_same_type_projs Seq_projs)



subsection \<open>The Laws of \<^term>\<open>\<bottom>\<close>\<close>

lemma Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_BOT_iff : \<open>P \<^bold>;\<^sub>\<checkmark> Q = \<bottom> \<longleftrightarrow> P = \<bottom> \<or> (\<exists>r. [\<checkmark>(r)] \<in> \<T> P \<and> Q r = \<bottom>)\<close>
  by (simp add: BOT_iff_Nil_D Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)

lemma BOT_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [simp] : \<open>\<bottom> \<^bold>;\<^sub>\<checkmark> P = \<bottom>\<close> by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_BOT_iff)


lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_BOT_iff : \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q = \<bottom> \<longleftrightarrow> P = \<bottom> \<or> Q = \<bottom>\<close>
  by (simp add: BOT_iff_Nil_D D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    (metis Nil_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil insertCI is_processT1_TR)

lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_BOT [simp] : \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<bottom> = \<bottom>\<close> and BOT_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [simp] : \<open>\<bottom> \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q = \<bottom>\<close>
  by (simp_all add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_BOT_iff)



subsection \<open>The Laws of \<^const>\<open>STOP\<close>\<close>

lemma Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_STOP_iff :
  \<open>P \<^bold>;\<^sub>\<checkmark> Q = STOP \<longleftrightarrow> \<T> P \<subseteq> insert [] {[\<checkmark>(r)]| r. True} \<and>
                     (\<forall>r. [\<checkmark>(r)] \<in> \<T> P \<longrightarrow> Q r = STOP)\<close> (is \<open>?lhs \<longleftrightarrow> ?rhs\<close>)
proof (intro iffI conjI subsetI allI impI)
  show \<open>?lhs \<Longrightarrow> t \<in> \<T> P \<Longrightarrow> t \<in> insert [] {[\<checkmark>(r)] |r. True}\<close> for t
    by (simp add: STOP_iff_T Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs set_eq_iff)
      (metis Prefix_Order.prefixI T_nonTickFree_imp_decomp append_Nil
        append_T_imp_tickFree is_processT3_TR length_0_conv length_map list.distinct(1))
next
  show \<open>?lhs \<Longrightarrow> [\<checkmark>(r)] \<in> \<T> P \<Longrightarrow> Q r = STOP\<close> for r
    by (force simp add: STOP_iff_T Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs set_eq_iff)
next
  show \<open>?rhs \<Longrightarrow> P \<^bold>;\<^sub>\<checkmark> Q = STOP\<close>
    by (auto simp add: STOP_iff_T Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs subset_iff)
      (metis D_T non_tickFree_tick,
        metis BOT_iff_Nil_D D_T D_BOT append_Nil event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.distinct(1) mem_Collect_eq
        front_tickFree_single is_processT9 list.distinct(1) list.inject)
qed

lemma Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_STOP_iff_bis :
  \<open>P \<^bold>;\<^sub>\<checkmark> Q = STOP \<longleftrightarrow> SKIPS {r. [\<checkmark>(r)] \<in> \<T> P} \<sqsubseteq>\<^sub>D\<^sub>T P \<and> (\<forall>r. [\<checkmark>(r)] \<in> \<T> P \<longrightarrow> Q r = STOP)\<close>
  (is \<open>?lhs \<longleftrightarrow> ?rhs\<close>)
proof (rule iffI)
  assume ?lhs
  from this[THEN arg_cong, where f = \<D>]
  have \<open>\<D> P = {}\<close>
    by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs D_STOP)
      (metis front_tickFree_Nil nonempty_divE[of P])
  with \<open>?lhs\<close> show ?rhs
    by (subst (asm) Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_STOP_iff)
      (auto simp add: refine_defs SKIPS_projs)
next
  show \<open>?rhs \<Longrightarrow> ?lhs\<close>
    unfolding Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_STOP_iff by (auto simp add: refine_defs SKIPS_projs)
qed


corollary STOP_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [simp] : \<open>STOP \<^bold>;\<^sub>\<checkmark> P = STOP\<close>
  by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_STOP_iff T_STOP)


lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) STOP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP [simp] : \<open>STOP \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> STOP = STOP\<close>
  by (simp add: STOP_iff_T T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k STOP_projs)



paragraph \<open>More powerful Laws\<close>

lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP :
  \<comment> \<open>Here, \<^term>\<open>g\<close> is a free parameter.\<close>
  \<open>P |||\<^sub>\<checkmark> STOP = RenamingTick (P \<^bold>; STOP)
                 (\<lambda>r. the (tick_join r (g r)))\<close> (is \<open>?lhs = ?rhs\<close>)
proof -
  let ?f = \<open>\<lambda>r. the (tick_join r (g r))\<close>
  have * : \<open>tF t \<Longrightarrow> map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id ?f) t
                     = map ev (map of_ev t)\<close> for t :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (induct t, simp_all)
      (metis (no_types, lifting) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.collapse(1) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(9) id_apply)
  show \<open>?lhs = ?rhs\<close>
  proof (rule Process_eq_optimizedI)
    fix t assume \<open>t \<in> \<D> ?lhs\<close>
    then obtain u v t_P
      where \<open>t = u @ v\<close> \<open>ftF v\<close> \<open>tF u \<or> v = []\<close>
        \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, []), {})\<close> \<open>t_P \<in> \<D> P\<close>
      unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k STOP_projs by blast
    from this(4) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_NilR_iff
    have \<open>tF t_P\<close> \<open>u = map ev (map of_ev t_P)\<close> by auto

    from "*" \<open>tF t_P\<close> have \<open>u @ v = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id ?f) t_P @ v\<close>
      by (simp add: \<open>u = map ev (map of_ev t_P)\<close>)
    moreover have \<open>t_P \<in> \<D> (P \<^bold>; STOP)\<close> by (simp add: D_Seq \<open>t_P \<in> \<D> P\<close>)
    ultimately show \<open>t \<in> \<D> ?rhs\<close>
      using \<open>ftF v\<close> \<open>tF t_P\<close> by (auto simp add: D_Renaming \<open>t = u @ v\<close>)
  next
    fix t assume \<open>t \<in> \<D> ?rhs\<close>
    then obtain u v
      where $ : \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id ?f) u @ v\<close>
        and \<open>tF u\<close> \<open>ftF v\<close> \<open>u \<in> \<D> P\<close> unfolding D_Renaming D_Seq D_STOP by blast
    have \<open>tF (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id ?f) u)\<close>
      by (simp add: \<open>tF u\<close> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree)
    moreover from \<open>tF u\<close>
    have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id ?f) u
          setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, []), {})\<close>
    proof (induct u)
      case Nil show ?case by simp
    next
      case (Cons e u)
      obtain a where \<open>e = ev a\<close> \<open>tF u\<close> by (meson Cons.prems is_ev_def tickFree_Cons_iff)
      from Cons.hyps[OF \<open>tF u\<close>] show ?case by (simp add: \<open>e = ev a\<close>)
    qed
    ultimately show \<open>t \<in> \<D> (P |||\<^sub>\<checkmark> STOP)\<close>
      using \<open>ftF v\<close> \<open>u \<in> \<D> P\<close> by (auto simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k STOP_projs "$")
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?lhs\<close> \<open>t \<notin> \<D> ?lhs\<close>
    then obtain t_P X_P X_Q
      where \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, []), {})\<close>
        \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join X_P {} X_Q\<close>
      unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs F_STOP by blast

    from \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join X_P {} X_Q\<close>
    have $ : \<open>e \<in> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id ?f -` X \<union> range tick
              \<Longrightarrow> e \<in> X_P \<union> range tick\<close> for e
      by (cases e) (auto simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
    from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_NilR_iff
      [THEN iffD1, OF \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, []), {})\<close>]
    have \<open>tF t_P\<close> \<open>t = map ev (map of_ev t_P)\<close> by simp_all
    have $$ : \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id ?f) t_P\<close>
      by (simp add: "*" \<open>t = map ev (map of_ev t_P)\<close> \<open>tF t_P\<close>)
    show \<open>(t, X) \<in> \<F> ?rhs\<close>
    proof (cases \<open>\<exists>r. t_P @ [\<checkmark>(r)] \<in> \<T> P\<close>)
      show \<open>\<exists>r. t_P @ [\<checkmark>(r)] \<in> \<T> P \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close>
        by (auto simp add: F_Renaming F_Seq F_STOP "$$")
    next
      assume \<open>\<nexists>r. t_P @ [\<checkmark>(r)] \<in> \<T> P\<close>
      hence \<open>(t_P, X_P \<union> range tick) \<in> \<F> P\<close>
        by (auto intro!: is_processT5 \<open>(t_P, X_P) \<in> \<F> P\<close> F_T)
      with "$" have \<open>(t_P, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id ?f -` X \<union> range tick) \<in> \<F> P\<close>
        by (meson is_processT4 subsetI)
      with \<open>tF t_P\<close> show \<open>(t, X) \<in> \<F> ?rhs\<close> by (auto simp add: F_Renaming F_Seq "$$")
    qed
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?rhs\<close> \<open>t \<notin> \<D> ?rhs\<close>
    then obtain u where $ : \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id ?f) u\<close>
      \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id ?f -` X) \<in> \<F> (P \<^bold>; STOP)\<close>
      unfolding Renaming_projs by blast
    from "$"(2) consider \<open>u \<in> \<D> P\<close> | r where \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close>
      | \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id ?f -` X \<union> range tick) \<in> \<F> P\<close> \<open>tF u\<close>
      by (auto simp add: Seq_projs F_STOP)
    thus \<open>(t, X) \<in> \<F> ?lhs\<close>
    proof cases
      let ?u' = \<open>if tF u then u else butlast u\<close>
      let ?v' = \<open>if tF u then [] else [\<checkmark>(?f (of_tick (last u)))]\<close>
      assume \<open>u \<in> \<D> P\<close>
      hence \<open>?u' \<in> \<D> P\<close> by (simp add: D_imp_front_tickFree div_butlast_when_non_tickFree_iff)
      moreover from D_imp_front_tickFree \<open>u \<in> \<D> P\<close> front_tickFree_iff_tickFree_butlast
      have \<open>tF ?u'\<close> by auto
      moreover have \<open>ftF ?v'\<close> by simp
      moreover from \<open>tF ?u'\<close> have \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id ?f) ?u' @ ?v'\<close>
        by (cases u rule: rev_cases, auto simp add: "$"(1) split: if_split_asm)
          (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.collapse(2) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(10))
      ultimately have \<open>t \<in> \<D> ?rhs\<close> unfolding D_Renaming D_Seq by blast
      with \<open>t \<notin> \<D> ?rhs\<close> show \<open>(t, X) \<in> \<F> ?lhs\<close> ..
    next
      fix r assume \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close>
      hence \<open>(u, UNIV - {\<checkmark>(r)}) \<in> \<F> P\<close> by (simp add: is_processT6_TR)
      moreover from "$"(1) "*" \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close> append_T_imp_tickFree
      have \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, []), {})\<close>
        by (auto simp add: setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_NilR_iff)
      moreover have \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join (UNIV - {\<checkmark>(r)}) {} UNIV\<close>
        by (simp add: subset_iff super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def) (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust)
      ultimately show \<open>(t, X) \<in> \<F> ?lhs\<close> unfolding F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k F_STOP by clarify blast
    next
      assume \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id ?f -` X \<union> range tick) \<in> \<F> P\<close> \<open>tF u\<close>
      moreover from "$"(1) "*" \<open>tF u\<close> have \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((u, []), {})\<close>
        by (auto simp add: setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_NilR_iff)
      moreover have \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id ?f -` X \<union> range tick) {} UNIV\<close>
        by (simp add: subset_iff super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def) (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust)
      ultimately show \<open>(t, X) \<in> \<F> ?lhs\<close> unfolding F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k F_STOP by clarify blast
    qed
  qed
qed



lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) STOP_Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>STOP |||\<^sub>\<checkmark> Q = RenamingTick (Q \<^bold>; STOP)
                 (\<lambda>s. the (tick_join (g s) s))\<close>
  by (metis Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym)



lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) Par\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP [simp] : \<open>P ||\<^sub>\<checkmark> STOP = (if P = \<bottom> then \<bottom> else STOP)\<close>
proof (split if_split, intro conjI impI)
  show \<open>P = \<bottom> \<Longrightarrow> P ||\<^sub>\<checkmark> STOP = \<bottom>\<close> by simp
next
  show \<open>P \<noteq> \<bottom> \<Longrightarrow> P ||\<^sub>\<checkmark> STOP = STOP\<close>
    by (auto simp add: STOP_iff_T T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k STOP_projs set_eq_iff
        BOT_iff_Nil_D setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_NilR_iff image_iff)
      (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.collapse(1) last_in_set tickFree_butlast)+
qed

lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) STOP_Par\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [simp] : \<open>STOP ||\<^sub>\<checkmark> P = (if P = \<bottom> then \<bottom> else STOP)\<close>
proof (split if_split, intro conjI impI)
  show \<open>P = \<bottom> \<Longrightarrow> STOP ||\<^sub>\<checkmark> P = \<bottom>\<close> by simp
next
  show \<open>P \<noteq> \<bottom> \<Longrightarrow> STOP ||\<^sub>\<checkmark> P = STOP\<close>
    by (auto simp add: STOP_iff_T T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k STOP_projs set_eq_iff
        BOT_iff_Nil_D setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_NilL_iff image_iff)
      (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.collapse(1) last_in_set tickFree_butlast)+
qed



subsection \<open>The Laws of \<^const>\<open>SKIP\<close>\<close>

subsubsection \<open>Sequential Composition\<close>

text \<open>\<^const>\<open>SKIP\<close> is neutral for @{const [source] Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k}!\<close>

lemma SKIP_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [simp] : \<open>SKIP r \<^bold>;\<^sub>\<checkmark> P = P r\<close>
  by (simp add: Process_eq_spec Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def SKIP_projs)

lemma Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP [simp] : \<open>P \<^bold>;\<^sub>\<checkmark> SKIP = P\<close>
proof (subst Process_eq_spec_optimized, safe)
  show \<open>s \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> SKIP) \<Longrightarrow> s \<in> \<D> P\<close>
    and \<open>s \<in> \<D> P \<Longrightarrow> s \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> SKIP)\<close> for s
    by (simp_all add: D_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_same_type D_SKIP)
next
  show \<open>(s, X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> SKIP) \<Longrightarrow> (s, X) \<in> \<F> P\<close> for s X
    by (auto simp add : F_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_same_type F_SKIP is_processT6_TR_notin tick_T_F
        intro : is_processT4 is_processT8)
next
  show \<open>(s, X) \<in> \<F> P \<Longrightarrow> (s, X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> SKIP)\<close> for s X
    by (simp add : F_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_same_type F_SKIP)
      (metis (mono_tags, opaque_lifting) F_T T_nonTickFree_imp_decomp
        append.right_neutral f_inv_into_f is_processT5_S7')
qed

lemma SKIPS_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [simp] : \<open>SKIPS R \<^bold>;\<^sub>\<checkmark> P = \<sqinter>r \<in> R. P r\<close>
  by (auto simp add: Process_eq_spec GlobalNdet_projs Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs
                     STOP_projs SKIPS_projs ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)


lemma finite_ticks_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [finite_ticks_simps] : \<open>\<bbbF>\<^sub>\<checkmark>(P \<^bold>;\<^sub>\<checkmark> Q)\<close>
  if \<open>\<bbbF>\<^sub>\<checkmark>(P)\<close> and \<open>(\<And>r. r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(Q r))\<close>
proof (rule finite_ticksI)
  fix t assume \<open>t \<in> \<T> (P \<^bold>;\<^sub>\<checkmark> Q)\<close> \<open>t \<notin> \<D> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
  have \<open>{r'. t @ [\<checkmark>(r')] \<in> \<T> (P \<^bold>;\<^sub>\<checkmark> Q)} \<subseteq>
        (\<Union>u \<in> {u. \<exists>v r. t = map (ev \<circ> of_ev) u @ v \<and> u @ [\<checkmark>(r)] \<in> \<T> P \<and> u \<notin> \<D> P \<and> tF u \<and> ftF v}.
         \<Union>r \<in> {r. u @ [\<checkmark>(r)] \<in> \<T> P}. {s. drop (length u) t @ [\<checkmark>(s)] \<in> \<T> (Q r)})\<close> (is \<open>?lhs \<subseteq> ?rhs\<close>)
  proof (rule subsetI)
    fix r' assume \<open>r' \<in> ?lhs\<close>
    hence \<open>t @ [\<checkmark>(r')] \<in> \<T> (P \<^bold>;\<^sub>\<checkmark> Q)\<close> by simp
    with \<open>t \<notin> \<D> (P \<^bold>;\<^sub>\<checkmark> Q)\<close> obtain t' r u'
      where \<open>t @ [\<checkmark>(r')] = map (ev \<circ> of_ev) t' @ u'\<close> \<open>t' @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>t' \<notin> \<D> P\<close> \<open>tF t'\<close> \<open>u' \<in> \<T> (Q r)\<close>
      by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
        (metis non_tickFree_tick tickFree_append_iff tickFree_map_ev_comp,
          metis (no_types, opaque_lifting) T_imp_front_tickFree butlast_append butlast_snoc
                front_tickFree_iff_tickFree_butlast non_tickFree_tick tickFree_append_iff
                tickFree_imp_front_tickFree tickFree_map_ev_comp,
          metis (no_types, opaque_lifting) append.assoc butlast_snoc front_tickFree_charn non_tickFree_tick
                tickFree_Nil tickFree_append_iff tickFree_imp_front_tickFree tickFree_map_ev_comp)
      
      thus \<open>r' \<in> ?rhs\<close>
      apply auto
      by (smt (verit, ccfv_SIG) Prefix_Order.same_prefix_nil T_imp_front_tickFree append_eq_append_conv2 append_eq_append_conv_if append_eq_conv_conj
          append_eq_first_pref_spec append_same_eq event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(2) front_tickFree_dw_closed length_map tickFree_Cons_iff tickFree_append_iff
          tickFree_map_ev_comp)
  qed
  moreover have \<open>finite \<dots>\<close>
  proof (rule finite_UN_I)
    show \<open>finite {u. \<exists>v r. t = map (ev \<circ> of_ev) u @ v \<and> u @ [\<checkmark>(r)] \<in> \<T> P \<and> u \<notin> \<D> P \<and> tF u \<and> ftF v}\<close>
      by (rule finite_subset[of _ \<open>{u. u \<le> map (ev \<circ> of_ev) (if tF t then t else butlast t)}\<close>])
        (auto simp add: append_T_imp_tickFree tickFree_map_ev_of_ev_same_type_is prefixes_fin,
          metis prefixI append_T_imp_tickFree butlast_append map_append
                not_Cons_self2 tickFree_Nil tickFree_map_ev_of_ev_eq_iff)
  next
    fix u assume \<open>u \<in> {u. \<exists>v r. t = map (ev \<circ> of_ev) u @ v \<and> u @ [\<checkmark>(r)] \<in> \<T> P \<and> u \<notin> \<D> P \<and> tF u \<and> ftF v}\<close>
    then obtain r v where \<open>t = map (ev \<circ> of_ev) u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>u \<notin> \<D> P\<close> \<open>tF u\<close> \<open>ftF v\<close> by blast
    show \<open>finite (\<Union>r\<in>{r. u @ [\<checkmark>(r)] \<in> \<T> P}. {s. drop (length u) t @ [\<checkmark>(s)] \<in> \<T> (Q r)})\<close>
    proof (rule finite_UN_I)
      show \<open>finite {r. u @ [\<checkmark>(r)] \<in> \<T> P}\<close>
        by (simp add: \<open>\<bbbF>\<^sub>\<checkmark>(P)\<close> \<open>u \<notin> \<D> P\<close> finite_ticksD)
    next
      fix r assume \<open>r \<in> {r. u @ [\<checkmark>(r)] \<in> \<T> P}\<close>
      hence \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close> ..
      with \<open>t \<notin> \<D> (P \<^bold>;\<^sub>\<checkmark> Q)\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>tF u\<close> have \<open>v \<notin> \<D> (Q r)\<close>
        by (auto simp add: \<open>t = map (ev \<circ> of_ev) u @ v\<close> Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
      show \<open>finite {s. drop (length u) t @ [\<checkmark>(s)] \<in> \<T> (Q r)}\<close>
        by (simp add: \<open>t = map (ev \<circ> of_ev) u @ v\<close>)
          (metis \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>u \<notin> \<D> P\<close> \<open>v \<notin> \<D> (Q r)\<close> finite_ticksD
                 is_processT9 strict_ticks_of_memI \<open>(\<And>r. r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(Q r))\<close>)
    qed
  qed
  ultimately show \<open>finite {r. t @ [\<checkmark>(r)] \<in> \<T> (P \<^bold>;\<^sub>\<checkmark> Q)}\<close> by (fact finite_subset)
qed



lemma finite_ticks_fun_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_bis :
  \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f) \<Longrightarrow> (\<And>x r. r \<in> \<^bold>\<checkmark>\<^bold>s(f x) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(x) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(g x r)) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. f x \<^bold>;\<^sub>\<checkmark> g x)\<close>
  by (simp add: finite_ticks_fun_def finite_ticks_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)

lemma finite_ticks_fun_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [finite_ticks_fun_simps] :
  \<comment> \<open>Big approximation.\<close>
  \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f) \<Longrightarrow> (\<And>r. r \<in> (\<Union>x. \<^bold>\<checkmark>\<^bold>s(f x)) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. g x r)) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. f x \<^bold>;\<^sub>\<checkmark> g x)\<close>
  by (rule finite_ticks_fun_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_bis)
    (auto simp add: finite_ticks_fun_def)



subsubsection \<open>Synchronization Product\<close>

text \<open>The generalization of the synchronization product was essentially motivated by
      the following theorem (in comparison to @{thm SKIP_Sync_SKIP[of r A s]}).\<close>

theorem (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) SKIP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP [simp] :
  \<open>SKIP r \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> SKIP s = (case tick_join r s of \<lfloor>r_s\<rfloor> \<Rightarrow> SKIP r_s | \<diamond> \<Rightarrow> STOP)\<close>
proof (split option.split, intro conjI impI allI)
  show \<open>tick_join r s = \<diamond> \<Longrightarrow> SKIP r \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> SKIP s = STOP\<close>
    unfolding STOP_iff_T T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k SKIP_projs set_eq_iff
    by (safe, simp_all, metis Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil insertCI)
next
  show \<open>SKIP r \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> SKIP s = SKIP r_s\<close> if \<open>tick_join r s = \<lfloor>r_s\<rfloor>\<close> for r_s
  proof (rule Process_eq_optimizedI)
    show \<open>t \<in> \<D> (SKIP r \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> SKIP s) \<Longrightarrow> t \<in> \<D> (SKIP r_s)\<close> for t
      by (simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k SKIP_projs)
  next
    show \<open>t \<in> \<D> (SKIP r_s) \<Longrightarrow> t \<in> \<D> (SKIP r \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> SKIP s)\<close> for t
      by (simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k SKIP_projs)
  next
    fix t X assume \<open>(t, X) \<in> \<F> (SKIP r \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> SKIP s)\<close> \<open>t \<notin> \<D> (SKIP r \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> SKIP s)\<close>
    then obtain t_P t_Q X_P X_Q
      where fail: \<open>(t_P, X_P) \<in> \<F> (SKIP r)\<close> \<open>(t_Q, X_Q) \<in> \<F> (SKIP s)\<close>
        \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> ((t_P, t_Q), A)\<close>
        \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join X_P A X_Q\<close>
      unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
    from fail(1-3) consider \<open>t = []\<close> \<open>\<checkmark>(r) \<notin> X_P\<close> \<open>\<checkmark>(s) \<notin> X_Q\<close> | \<open>t = [\<checkmark>(r_s)]\<close>
      by (cases t_P; cases t_Q) (simp_all add: F_SKIP \<open>tick_join r s = \<lfloor>r_s\<rfloor>\<close>)
    thus \<open>(t, X) \<in> \<F> (SKIP r_s)\<close>
    proof cases
      assume \<open>t = []\<close> \<open>\<checkmark>(r) \<notin> X_P\<close> \<open>\<checkmark>(s) \<notin> X_Q\<close>
      from \<open>\<checkmark>(r) \<notin> X_P\<close> \<open>\<checkmark>(s) \<notin> X_Q\<close> fail(4) \<open>tick_join r s = \<lfloor>r_s\<rfloor>\<close>
      have \<open>\<checkmark>(r_s) \<notin> X\<close>
        by (simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def subset_iff)
          (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.distinct(1) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inject(2) inj_tick_join)
      with \<open>t = []\<close> show \<open>(t, X) \<in> \<F> (SKIP r_s)\<close> by (simp add: F_SKIP)
    next
      show \<open>t = [\<checkmark>(r_s)] \<Longrightarrow> (t, X) \<in> \<F> (SKIP r_s)\<close> by (simp add: F_SKIP)
    qed
  next
    fix t :: \<open>('a, _) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and X assume \<open>(t, X) \<in> \<F> (SKIP r_s)\<close>
    then consider \<open>t = []\<close> \<open>\<checkmark>(r_s) \<notin> X\<close> | \<open>t = [\<checkmark>(r_s)]\<close>
      unfolding F_SKIP by blast
    thus \<open>(t, X) \<in> \<F> (SKIP r \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> SKIP s)\<close>
    proof cases
      assume \<open>t = []\<close> \<open>\<checkmark>(r_s) \<notin> X\<close>
      have \<open>([], - {\<checkmark>(r)}) \<in> \<F> (SKIP r)\<close>
        by (simp add: F_SKIP)
      moreover have \<open>([], - {\<checkmark>(s)}) \<in> \<F> (SKIP s)\<close>
        by (simp add: F_SKIP)
      moreover have  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> (([], []), A)\<close>
        by (simp add: \<open>t = []\<close>)
      moreover have \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join (- {\<checkmark>(r)}) A (- {\<checkmark>(s)})\<close>
        using \<open>\<checkmark>(r_s) \<notin> X\<close> \<open>tick_join r s = \<lfloor>r_s\<rfloor>\<close>
        by (simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def subset_iff)
          (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust option.inject)
      ultimately show \<open>(t, X) \<in> \<F> (SKIP r \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> SKIP s)\<close>
        by (simp (no_asm) add: F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) blast
    next
      assume \<open>t = [\<checkmark>(r_s)]\<close>
      have \<open>([\<checkmark>(r)], UNIV) \<in> \<F> (SKIP r)\<close>
        by (simp add: F_SKIP)
      moreover have \<open>([\<checkmark>(s)], UNIV) \<in> \<F> (SKIP s)\<close>
        by (simp add: F_SKIP)
      moreover have \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>tick_join\<^esub> (([\<checkmark>(r)], [\<checkmark>(s)]), A)\<close>
        by (simp add: \<open>t = [\<checkmark>(r_s)]\<close> \<open>tick_join r s = \<lfloor>r_s\<rfloor>\<close>)
      moreover have \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k tick_join UNIV A UNIV\<close>
        by (simp add: super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def subset_iff)
          (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust)
      ultimately show \<open>(t, X) \<in> \<F> (SKIP r \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> SKIP s)\<close>
        by (simp (no_asm) add: F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) blast
    qed
  qed
qed



lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) STOP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP [simp] : \<open>STOP \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> SKIP s = STOP\<close>
  and SKIP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP [simp] : \<open>SKIP r \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> STOP = STOP\<close>
  by (force simp add: STOP_iff_T T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k STOP_projs SKIP_projs)+


lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP :
  \<open>\<box>a \<in> A \<rightarrow> P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> SKIP r =
   \<box>a \<in> (A - S) \<rightarrow> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> SKIP r)\<close> (is \<open>?lhs = ?rhs\<close>)
proof (rule Process_eq_optimizedI)
  fix t assume \<open>t \<in> \<D> ?lhs\<close>
  then obtain u v t_P a t_Q
    where * : \<open>t = u @ v\<close> \<open>tF u\<close> \<open>ftF v\<close> \<open>a \<in> A\<close> \<open>t_P \<in> \<D> (P a)\<close>
      \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((ev a # t_P, t_Q), S)\<close> \<open>t_Q = [] \<or> t_Q = [\<checkmark>(r)]\<close>
    unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k SKIP_projs Mprefix_projs by blast
  from "*"(6, 7) obtain u'
    where \<open>a \<notin> S\<close> \<open>u = ev a # u'\<close> \<open>u' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<close>
    by (auto split: if_split_asm)
  from this(2, 3) "*"(2, 5, 7) front_tickFree_charn have \<open>u' \<in> \<D> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> SKIP r)\<close>
    by (auto simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k SKIP_projs)
  with "*"(1-4) \<open>a \<notin> S\<close> \<open>u = ev a # u'\<close> is_processT7 show \<open>t \<in> \<D> ?rhs\<close>
    by (auto simp add: D_Mprefix)
next
  fix t assume \<open>t \<in> \<D> ?rhs\<close>
  then obtain a t' where \<open>t = ev a # t'\<close> \<open>a \<in> A\<close> \<open>a \<notin> S\<close> \<open>t' \<in> \<D> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> SKIP r)\<close>
    unfolding D_Mprefix by blast
  then obtain u v t_P t_Q
    where * : \<open>t' = u @ v\<close> \<open>tF u\<close> \<open>ftF v\<close> \<open>t_P \<in> \<D> (P a)\<close>
      \<open>u setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<close> \<open>t_Q = [] \<or> t_Q = [\<checkmark>(r)]\<close>
    unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k SKIP_projs by blast
  have \<open>t = (ev a # u) @ v\<close> by (simp add: "*"(1) \<open>t = ev a # t'\<close>)
  moreover from "*"(2) have \<open>tF (ev a # u)\<close> by simp
  moreover from "*"(5, 6) have \<open>ev a # u setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((ev a # t_P, t_Q), S)\<close>
    by (cases t_Q) (simp_all add: \<open>a \<notin> S\<close> Cons_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Cons)
  moreover have \<open>ev a # t_P \<in> \<D> (\<box>a \<in> A \<rightarrow> P a)\<close>
    by (simp add: "*"(4) D_Mprefix \<open>a \<in> A\<close>)
  ultimately show \<open>t \<in> \<D> ?lhs\<close>
    unfolding D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k SKIP_projs using "*"(3, 6) by blast
next
  fix t X assume \<open>(t, X) \<in> \<F> ?lhs\<close> \<open>t \<notin> \<D> ?lhs\<close>
  then obtain t_P t_Q X_P X_Q
    where * : \<open>(t_P, X_P) \<in> \<F> (\<box>a \<in> A \<rightarrow> P a)\<close> \<open>(t_Q, X_Q) \<in> \<F> (SKIP r)\<close>
      \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<close>
      \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P S X_Q\<close>
    unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
  from "*"(1) consider \<open>t_P = []\<close> \<open>X_P \<inter> ev ` A = {}\<close>
    | a t_P' where \<open>t_P = ev a # t_P'\<close> \<open>a \<in> A\<close> \<open>(t_P', X_P) \<in> \<F> (P a)\<close>
    unfolding F_Mprefix by blast
  thus \<open>(t, X) \<in> \<F> ?rhs\<close>
  proof cases
    assume \<open>t_P = []\<close> \<open>X_P \<inter> ev ` A = {}\<close>
    from \<open>t_P = []\<close> "*"(2, 3) have \<open>t = []\<close> \<open>t_Q = []\<close> \<open>\<checkmark>(r) \<notin> X_Q\<close>
      by (auto simp add: F_SKIP)
    with "*"(4) show \<open>t_P = [] \<Longrightarrow> X_P \<inter> ev ` A = {} \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close>
      by (auto simp add: F_Mprefix super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
  next
    fix a t_P' assume \<open>t_P = ev a # t_P'\<close> \<open>a \<in> A\<close> \<open>(t_P', X_P) \<in> \<F> (P a)\<close>
    from "*"(2, 3) obtain t'
      where \<open>t = ev a # t'\<close> \<open>a \<notin> S\<close> \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P', t_Q), S)\<close>
      by (auto simp add: \<open>t_P = ev a # t_P'\<close> F_SKIP split: if_split_asm)
    from "*"(2, 4) \<open>(t_P', X_P) \<in> \<F> (P a)\<close> this(3)
    have \<open>(t', X) \<in> \<F> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> SKIP r)\<close> by (auto simp add: F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    thus \<open>(t, X) \<in> \<F> ?rhs\<close> by (simp add: \<open>t = ev a # t'\<close> F_Mprefix \<open>a \<in> A\<close> \<open>a \<notin> S\<close>)
  qed
next
  fix t X assume \<open>(t, X) \<in> \<F> ?rhs\<close> \<open>t \<notin> \<D> ?rhs\<close>
  from \<open>(t, X) \<in> \<F> ?rhs\<close> consider \<open>t = []\<close> \<open>X \<inter> ev ` (A - S) = {}\<close>
    | a t' where \<open>t = ev a # t'\<close> \<open>a \<in> A\<close> \<open>a \<notin> S\<close> \<open>(t', X) \<in> \<F> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> SKIP r)\<close>
    unfolding F_Mprefix by blast
  thus \<open>(t, X) \<in> \<F> ?lhs\<close>
  proof cases
    assume \<open>t = []\<close> \<open>X \<inter> ev ` (A - S) = {}\<close>
    from \<open>X \<inter> ev ` (A - S) = {}\<close>
    have \<open>([], range tick \<union> {ev a |a. ev a \<in> X \<and> a \<notin> S}) \<in> \<F> (\<box>a \<in> A \<rightarrow> P a)\<close>
      by (auto simp add: F_Mprefix)
    moreover have \<open>([], UNIV - {\<checkmark>(r)}) \<in> \<F> (SKIP r)\<close> by (simp add: F_SKIP)
    moreover have \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) 
                       (range tick \<union> {ev a |a. ev a \<in> X \<and> a \<notin> S}) S (UNIV - {\<checkmark>(r)})\<close>
      by (simp add: subset_iff super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def) (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust)
    moreover have \<open>[] setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> (([], []), S)\<close> by simp
    ultimately show \<open>(t, X) \<in> \<F> ?lhs\<close> by (simp (no_asm) add: \<open>t = []\<close> F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) blast
  next
    fix a t' assume \<open>t = ev a # t'\<close> \<open>a \<in> A\<close> \<open>a \<notin> S\<close> \<open>(t', X) \<in> \<F> (P a \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> SKIP r)\<close>
    from this(1, 4) \<open>t \<notin> \<D> ?rhs\<close> \<open>a \<in> A\<close> \<open>a \<notin> S\<close>
    obtain t_P t_Q X_P X_Q
      where * : \<open>(t_P, X_P) \<in> \<F> (P a)\<close> \<open>(t_Q, X_Q) \<in> \<F> (SKIP r)\<close>
        \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<close>
        \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P S X_Q\<close>
      unfolding D_Mprefix Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by force
    have \<open>(ev a # t_P, X_P) \<in> \<F> (\<box>a \<in> A \<rightarrow> P a)\<close>
      by (simp add: "*"(1) F_Mprefix \<open>a \<in> A\<close>)
    moreover from "*"(2, 3) have \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((ev a # t_P, t_Q), S)\<close>
      by (auto simp add: \<open>t = ev a # t'\<close> F_SKIP \<open>a \<notin> S\<close>)
    ultimately show \<open>(t, X) \<in> \<F> ?lhs\<close> unfolding F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k using "*"(2, 4) by auto
  qed
qed


corollary (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) SKIP_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Mprefix :
  \<open>SKIP r \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> \<box>b \<in> B \<rightarrow> Q b = \<box>b \<in> (B - S) \<rightarrow> (SKIP r \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q b)\<close> (is \<open>?lhs = ?rhs\<close>)
  by (subst (1 2) Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym mono_Mprefix_eq)
    (fact Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Mprefix_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP)


lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) finite_ticks_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [finite_ticks_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>(P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> if \<open>\<bbbF>\<^sub>\<checkmark>(P)\<close> and \<open>\<bbbF>\<^sub>\<checkmark>(Q)\<close>
proof (rule finite_ticksI)
  fix t assume \<open>t \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
  have \<open>{r_s. t @ [\<checkmark>(r_s)] \<in> \<T> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)} \<subseteq>
        (\<Union>(t_P, t_Q)\<in>{(t_P, t_Q). t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)}.
                      {r_s. \<exists>r s. r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor> \<and>
                                  t_P @ [\<checkmark>(r)] \<in> \<T> P \<and> t_P \<notin> \<D> P \<and>
                                  t_Q @ [\<checkmark>(s)] \<in> \<T> Q \<and> t_Q \<notin> \<D> Q})\<close>
    (is \<open>_ \<subseteq> ?rhs\<close>)
  proof (rule subsetI)
    fix r_s assume \<open>r_s \<in> {r_s. t @ [\<checkmark>(r_s)] \<in> \<T> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)}\<close>
    hence \<open>t @ [\<checkmark>(r_s)] \<in> \<T> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> ..
    moreover from \<open>t \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> have \<open>t @ [\<checkmark>(r_s)] \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
      by (meson is_processT9)
    ultimately obtain t_P t_Q where \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close> \<open>t_P \<notin> \<D> P\<close> \<open>t_Q \<notin> \<D> Q\<close>
      \<open>t @ [\<checkmark>(r_s)] setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<close>
      by (simp add: T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k') (use front_tickFree_Nil in blast)
    from this(5) show \<open>r_s \<in> ?rhs\<close>
    proof (elim snoc_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
      fix r s t_P' t_Q'
      assume assms : \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P', t_Q'), S)\<close>
        \<open>r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor>\<close> \<open>t_P = t_P' @ [\<checkmark>(r)]\<close> \<open>t_Q = t_Q' @ [\<checkmark>(s)]\<close>
      from \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close> \<open>t_P \<notin> \<D> P\<close> \<open>t_Q \<notin> \<D> Q\<close> assms(3, 4)
      have \<open>t_P' \<notin> \<D> P\<close> \<open>t_Q' \<notin> \<D> Q\<close>
        by (meson T_imp_front_tickFree front_tickFree_append_iff is_processT7 not_Cons_self2)+
      with \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close> assms show \<open>r_s \<in> ?rhs\<close> by auto
    qed
  qed
  moreover have \<open>finite \<dots>\<close>
  proof (rule finite_UN_I, safe)
    show \<open>finite {(t_P, t_Q). t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)}\<close>
      by (fact finite_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick_join)
  next
    fix t_P t_Q
    let ?S = \<open>{r_s. \<exists>r s. r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor> \<and>
                          t_P @ [\<checkmark>(r)] \<in> \<T> P \<and> t_P \<notin> \<D> P \<and>
                          t_Q @ [\<checkmark>(s)] \<in> \<T> Q \<and> t_Q \<notin> \<D> Q}\<close>
    have \<open>Some ` ?S \<subseteq> (\<lambda>(r, s). r \<otimes>\<checkmark> s) `
                       ({r. t_P @ [\<checkmark>(r)] \<in> \<T> P \<and> t_P \<notin> \<D> P} \<times>
                        {s. t_Q @ [\<checkmark>(s)] \<in> \<T> Q \<and> t_Q \<notin> \<D> Q})\<close> by force
    moreover have \<open>finite \<dots>\<close> by (simp add: finite_ticksD \<open>\<bbbF>\<^sub>\<checkmark>(P)\<close> \<open>\<bbbF>\<^sub>\<checkmark>(Q)\<close>)
    ultimately have \<open>finite (Some ` ?S)\<close> by (fact finite_subset)
    thus \<open>finite ?S\<close> by (simp add: finite_image_iff)
  qed
  ultimately show \<open>finite {r_s. t @ [\<checkmark>(r_s)] \<in> \<T> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)}\<close> by (fact finite_subset)
qed

lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) finite_ticks_fun_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k [finite_ticks_fun_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(g) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. f x \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> g x)\<close>
  by (simp add: finite_ticks_fun_def finite_ticks_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)



section \<open>Associativity of Sequential Composition\<close>

lemma Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc : \<open>P \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q r \<^bold>;\<^sub>\<checkmark> R) = P \<^bold>;\<^sub>\<checkmark> Q \<^bold>;\<^sub>\<checkmark> R\<close>
  for P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and Q :: \<open>'r \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    and R :: \<open>'s \<Rightarrow> ('a, 't) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof (rule Process_eq_optimizedI)
  fix t assume \<open>t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q r \<^bold>;\<^sub>\<checkmark> R))\<close>
  then consider (D_P) t' u where \<open>t = map (ev \<circ> of_ev) t' @ u\<close> \<open>t' \<in> \<D> P\<close> \<open>tF t'\<close> \<open>ftF u\<close>
    | (D_Q_R) t' r u where \<open>t = map (ev \<circ> of_ev) t' @ u\<close> \<open>t' @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>u \<in> \<D> (Q r \<^bold>;\<^sub>\<checkmark> R)\<close>
    unfolding Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs[of P] by fast
  thus \<open>t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q \<^bold>;\<^sub>\<checkmark> R)\<close>
  proof cases
    case D_P
    define t'' :: \<open>('a, 's) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> where \<open>t'' = map (ev \<circ> of_ev) t'\<close>
    from D_P have \<open>t'' \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
      by (auto simp add: t''_def Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs intro: front_tickFree_Nil)
    moreover have \<open>tF t''\<close> by (simp add: t''_def)
    ultimately have \<open>map (ev \<circ> of_ev) t'' \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q \<^bold>;\<^sub>\<checkmark> R)\<close>
      by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs[of \<open>P \<^bold>;\<^sub>\<checkmark> Q\<close>])
        (metis append.right_neutral front_tickFree_Nil)
    also have \<open>map (ev \<circ> of_ev) t'' = map (ev \<circ> of_ev) t'\<close>
      by (simp add: t''_def)
    finally have \<open>map (ev \<circ> of_ev) t' \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q \<^bold>;\<^sub>\<checkmark> R)\<close> .
    with D_P(1, 3, 4) show \<open>t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q \<^bold>;\<^sub>\<checkmark> R)\<close> by (simp add: is_processT7)
  next
    case D_Q_R
    from D_Q_R(3) consider (D_Q) u' v where \<open>u = map (ev \<circ> of_ev) u' @ v\<close> \<open>u' \<in> \<D> (Q r)\<close> \<open>tF u'\<close> \<open>ftF v\<close>
      | (D_R) u' s v where \<open>u = map (ev \<circ> of_ev) u' @ v\<close> \<open>u' @ [\<checkmark>(s)] \<in> \<T> (Q r)\<close> \<open>tF u'\<close> \<open>v \<in> \<D> (R s)\<close>
      unfolding Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
    thus \<open>t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q \<^bold>;\<^sub>\<checkmark> R)\<close>
    proof cases
      case D_Q
      define t'' :: \<open>('a, 's) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> where \<open>t'' = map (ev \<circ> of_ev) t' @ map (ev \<circ> of_ev) u'\<close>
      have \<open>t'' \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
        by (simp add: t''_def Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
          (metis D_Q(2,3) D_Q_R(2) append_T_imp_tickFree list.distinct(1)
                 tickFree_map_ev_of_ev_same_type_is)
      moreover have \<open>tF t''\<close> by (simp add: t''_def)
      ultimately have \<open>map (ev \<circ> of_ev) t'' \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q \<^bold>;\<^sub>\<checkmark> R)\<close>
        by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs[of \<open>P \<^bold>;\<^sub>\<checkmark> Q\<close>])
          (metis append.right_neutral front_tickFree_Nil)
      also have \<open>map (ev \<circ> of_ev) t'' = map (ev \<circ> of_ev) t' @ map (ev \<circ> of_ev) u'\<close>
        by (simp add: t''_def)
      finally have \<open>map (ev \<circ> of_ev) t' @ map (ev \<circ> of_ev) u' \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q \<^bold>;\<^sub>\<checkmark> R)\<close> .
      with D_Q(1,4) D_Q_R(1) is_processT7 show \<open>t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q \<^bold>;\<^sub>\<checkmark> R)\<close> by fastforce
    next
      case D_R
      define t'' :: \<open>('a, 's) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> where \<open>t'' = map (ev \<circ> of_ev) (map (ev \<circ> of_ev) t' @ u')\<close>
      have \<open>t'' @ [\<checkmark>(s)] \<in> \<T> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
        by (simp add: t''_def Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs[of P] del: map_map)
          (metis D_Q_R(2) D_R(2) append_T_imp_tickFree not_Cons_self2
                 tickFree_map_ev_of_ev_same_type_is)
      moreover have \<open>tF t''\<close> unfolding t''_def by (blast intro: tickFree_map_ev_comp)

      ultimately have \<open>map (ev \<circ> of_ev) t'' @ v \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q \<^bold>;\<^sub>\<checkmark> R)\<close>
        unfolding Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs[of \<open>P \<^bold>;\<^sub>\<checkmark> Q\<close>] using D_R(4) by blast
      also have \<open>map (ev \<circ> of_ev) t'' @ v = t\<close>
        by (simp add: D_Q_R(1) D_R(1) t''_def)
      finally show \<open>t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q \<^bold>;\<^sub>\<checkmark> R)\<close> .
    qed
  qed
next

  fix t assume \<open>t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q \<^bold>;\<^sub>\<checkmark> R)\<close>
  then consider (D_P_Q) t' u where \<open>t = map (ev \<circ> of_ev) t' @ u\<close> \<open>t' \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q)\<close> \<open>tF t'\<close> \<open>ftF u\<close>
    | (D_R) t' s u where \<open>t = map (ev \<circ> of_ev) t' @ u\<close> \<open>t' @ [\<checkmark>(s)] \<in> \<T> (P \<^bold>;\<^sub>\<checkmark> Q)\<close> \<open>u \<in> \<D> (R s)\<close>
    unfolding Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs[of \<open>P \<^bold>;\<^sub>\<checkmark> Q\<close>] by blast
  thus \<open>t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q r \<^bold>;\<^sub>\<checkmark> R))\<close>
  proof cases
    case D_P_Q
    from D_P_Q(2) consider (D_P) t'' u' where \<open>t' = map (ev \<circ> of_ev) t'' @ u'\<close> \<open>t'' \<in> \<D> P\<close> \<open>tF t''\<close> \<open>ftF u'\<close>
      | (D_Q) t'' r u' where \<open>t' = map (ev \<circ> of_ev) t'' @ u'\<close> \<open>t'' @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>tF t''\<close> \<open>u' \<in> \<D> (Q r)\<close>
      unfolding Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
    thus \<open>t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q r \<^bold>;\<^sub>\<checkmark> R))\<close>
    proof cases
      case D_P
      from D_P(2, 3) have \<open>map (ev \<circ> of_ev) t'' \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q r \<^bold>;\<^sub>\<checkmark> R))\<close>
        by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs[of P] intro: front_tickFree_Nil)
      thus \<open>t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q r \<^bold>;\<^sub>\<checkmark> R))\<close>
        by (simp add: D_P_Q(1) D_P(1))
          (metis (mono_tags, lifting) D_P_Q(4) front_tickFree_append
            is_processT7 tickFree_map_ev_comp)
    next
      case D_Q
      from D_P_Q(3) D_Q(1, 4) have \<open>map (ev \<circ> of_ev) u' \<in> \<D> (Q r \<^bold>;\<^sub>\<checkmark> R)\<close>
        by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (metis append.right_neutral front_tickFree_Nil)
      with D_Q(2, 3) have \<open>map (ev \<circ> of_ev) (map (ev \<circ> of_ev) t'' @ u') \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q r \<^bold>;\<^sub>\<checkmark> R))\<close>
        by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs[of P])
      with D_P_Q(4) is_processT7 show \<open>t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q r \<^bold>;\<^sub>\<checkmark> R))\<close>
        by (fastforce simp add: D_P_Q(1) D_Q(1))
    qed
  next
    case D_R
    then consider (T_P) t'' r u' where \<open>t' = map (ev \<circ> of_ev) t'' @ u'\<close>
      \<open>t'' @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>tF t''\<close> \<open>u' @ [\<checkmark>(s)] \<in> \<T> (Q r)\<close>
    | (D_P) t'' u' where \<open>t' = map (ev \<circ> of_ev) t'' @ u'\<close> \<open>t'' \<in> \<D> P\<close> \<open>tF t''\<close> \<open>tF u'\<close>
      by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs append_eq_append_conv2 append_eq_map_conv
          Cons_eq_append_conv front_tickFree_append_iff intro: D_P T_P)
    thus \<open>t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q r \<^bold>;\<^sub>\<checkmark> R))\<close>
    proof cases
      case T_P
      from D_R(3) T_P(4) have \<open>map (ev \<circ> of_ev) u' @ u \<in> \<D> (Q r \<^bold>;\<^sub>\<checkmark> R)\<close>
        by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (metis append_T_imp_tickFree not_Cons_self2)
      with T_P(2, 3) have \<open>map (ev \<circ> of_ev) t'' @ map (ev \<circ> of_ev) u' @ u \<in>
                           \<D> (P \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q r \<^bold>;\<^sub>\<checkmark> R))\<close>
        by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs[of P])
      also have \<open>map (ev \<circ> of_ev) t'' @ map (ev \<circ> of_ev) u' @ u = t\<close>
        by (simp add: D_R(1) T_P(1))
      finally show \<open>t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q r \<^bold>;\<^sub>\<checkmark> R))\<close> .
    next
      case D_P
      from D_P(2, 3) have \<open>map (ev \<circ> of_ev) t'' \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q r \<^bold>;\<^sub>\<checkmark> R))\<close>
        by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs[of P] intro: front_tickFree_Nil)
      with D_R(3) show \<open>t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q r \<^bold>;\<^sub>\<checkmark> R))\<close>
        by (simp add: D_R(1) D_P(1))
          (metis (mono_tags, lifting) D_imp_front_tickFree
            front_tickFree_append is_processT7 tickFree_map_ev_comp)
    qed
  qed
next

  fix t X assume \<open>(t, X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q r \<^bold>;\<^sub>\<checkmark> R))\<close> \<open>t \<notin> \<D> (P \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q r \<^bold>;\<^sub>\<checkmark> R))\<close>
  then consider (F_P) t' where \<open>t = map (ev \<circ> of_ev) t'\<close> \<open>(t', ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<in> \<F> P\<close> \<open>tF t'\<close>
    | (F_Q_R) t' r u where \<open>t = map (ev \<circ> of_ev) t' @ u\<close> \<open>t' @ [\<checkmark>(r)] \<in> \<T> P\<close>
      \<open>tF t'\<close> \<open>(u, X) \<in> \<F> (Q r \<^bold>;\<^sub>\<checkmark> R)\<close>
    unfolding Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs[of P] by fast
  thus \<open>(t, X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q \<^bold>;\<^sub>\<checkmark> R)\<close>
  proof cases
    case F_P
    from F_P(2) have \<open>(t', ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X)) \<in> \<F> P\<close>
      by (simp add: ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_idem)
    with F_P(3) have \<open>(map (ev \<circ> of_ev) t', ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
      by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
    thus \<open>(t, X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q \<^bold>;\<^sub>\<checkmark> R)\<close>
      by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs[of \<open>P \<^bold>;\<^sub>\<checkmark> Q\<close>] F_P(1))
        (metis map_ev_of_ev_map_ev_of_ev tickFree_map_ev_comp)
  next
    case F_Q_R
    from F_Q_R(4)
    consider (F_Q) u' where \<open>u = map (ev \<circ> of_ev) u'\<close>
      \<open>(u', ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<in> \<F> (Q r)\<close> \<open>tF u'\<close>
    | (F_R) u' s u'' where \<open>u = map (ev \<circ> of_ev) u' @ u''\<close> \<open>u' @ [\<checkmark>(s)] \<in> \<T> (Q r)\<close> \<open>tF u'\<close> \<open>(u'', X) \<in> \<F> (R s)\<close>
    | (D_Q) u' u'' where \<open>u = map (ev \<circ> of_ev) u' @ u''\<close> \<open>u' \<in> \<D> (Q r)\<close> \<open>tF u'\<close> \<open>ftF u''\<close>
      unfolding Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
    thus \<open>(t, X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q \<^bold>;\<^sub>\<checkmark> R)\<close>
    proof cases
      case F_Q
      from F_Q(2) F_Q_R(2, 3)
      have \<open>(map (ev \<circ> of_ev) t' @ u',ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
        by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
      with F_Q(1,3) F_Q_R(1) show \<open>(t, X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q \<^bold>;\<^sub>\<checkmark> R)\<close>
        by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs[of \<open>P \<^bold>;\<^sub>\<checkmark> Q\<close>])
          (metis map_append map_ev_of_ev_map_ev_of_ev tickFree_append_iff tickFree_map_ev_comp)
    next
      case F_R
      from F_Q_R(2, 3) F_R(2) have $ : \<open>map (ev \<circ> of_ev) t' @ u' @ [\<checkmark>(s)] \<in> \<T> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
        by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
      have $$ : \<open>tF (map (ev \<circ> of_ev) t' @ u')\<close> by (simp add: F_R(3))
      show \<open>(t, X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q \<^bold>;\<^sub>\<checkmark> R)\<close>
        by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs[of \<open>P \<^bold>;\<^sub>\<checkmark> Q\<close>])
          (metis map_append[of \<open>ev \<circ> of_ev\<close> \<open>map (ev \<circ> of_ev) t'\<close> u']
            F_Q_R(1) F_R(1, 4) "$" "$$" append_eq_appendI map_ev_of_ev_map_ev_of_ev)
    next
      case D_Q
      from D_Q(2) F_Q_R(2, 3) have $ : \<open>map (ev \<circ> of_ev) t' @ u' \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
        by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
      have $$ : \<open>tF (map (ev \<circ> of_ev) t' @ u')\<close> by (simp add: D_Q(3))
      have \<open>t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q \<^bold>;\<^sub>\<checkmark> R)\<close>
        by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs[of \<open>P \<^bold>;\<^sub>\<checkmark> Q\<close>])
          (metis D_Q(1, 4) F_Q_R(1) "$" "$$" append_assoc map_append map_ev_of_ev_map_ev_of_ev)
      thus \<open>(t, X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q \<^bold>;\<^sub>\<checkmark> R)\<close> by (fact is_processT8)
    qed
  qed
next
  fix t X assume \<open>(t, X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q \<^bold>;\<^sub>\<checkmark> R)\<close> \<open>t \<notin> \<D> (P \<^bold>;\<^sub>\<checkmark> Q \<^bold>;\<^sub>\<checkmark> R)\<close>
  then consider (F_P_Q) t' where \<open>t = map (ev \<circ> of_ev) t'\<close>
    \<open>(t', ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q)\<close> \<open>tF t'\<close>
  | (F_R) t' s u where \<open>t = map (ev \<circ> of_ev) t' @ u\<close>
    \<open>t' @ [\<checkmark>(s)] \<in> \<T> (P \<^bold>;\<^sub>\<checkmark> Q)\<close> \<open>tF t'\<close> \<open>(u, X) \<in> \<F> (R s)\<close>
    unfolding Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs[of \<open>P \<^bold>;\<^sub>\<checkmark> Q\<close>] by fast
  thus \<open>(t, X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q r \<^bold>;\<^sub>\<checkmark> R))\<close>
  proof cases
    case F_P_Q
    from F_P_Q(1, 3) \<open>t \<notin> \<D> (P \<^bold>;\<^sub>\<checkmark> Q \<^bold>;\<^sub>\<checkmark> R)\<close> have \<open>t' \<notin> \<D> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
      by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) (metis front_tickFree_Nil self_append_conv)
    with F_P_Q(2) consider (F_P) t'' where \<open>t' = map (ev \<circ> of_ev) t''\<close>
      \<open>(t'', ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X :: ('a, 's) refusal\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)) \<in> \<F> P\<close> \<open>tF t''\<close>
    | (F_Q) t'' r u where \<open>t' = map (ev \<circ> of_ev) t'' @ u\<close> \<open>t'' @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>tF t''\<close>
      \<open>(u, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<in> \<F> (Q r)\<close>
      unfolding Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by fast
    thus \<open>(t, X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q r \<^bold>;\<^sub>\<checkmark> R))\<close>
    proof cases
      case F_P
      from F_P(2, 3) have \<open>(t'',ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<in> \<F> P\<close>
        by (simp add: ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_idem)
      moreover have \<open>t = map (ev \<circ> of_ev) t''\<close>
        by (simp add: F_P_Q(1) F_P(1))
      ultimately show \<open>(t, X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q r \<^bold>;\<^sub>\<checkmark> R))\<close>
        by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs[of P] F_P(3))
    next
      case F_Q
      from F_P_Q(3) F_Q(1, 4) have \<open>(map (ev \<circ> of_ev) u, X) \<in> \<F> (Q r \<^bold>;\<^sub>\<checkmark> R)\<close>
        by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
      with F_Q(2, 3) show \<open>(t, X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q r \<^bold>;\<^sub>\<checkmark> R))\<close>
        by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs[of P] F_P_Q(1) F_Q(1))
    qed
  next
    case F_R
    from F_R(2) consider (T_P) t'' r u' where \<open>t' = map (ev \<circ> of_ev) t'' @ u'\<close>
      \<open>t'' @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>tF t''\<close> \<open>u' @ [\<checkmark>(s)] \<in> \<T> (Q r)\<close>
    | (D_P) t'' u' where \<open>t' = map (ev \<circ> of_ev) t'' @ u'\<close> \<open>t'' \<in> \<D> P\<close> \<open>tF t''\<close> \<open>tF u'\<close>
      by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs append_eq_append_conv2 Cons_eq_append_conv)
        (auto simp add: append_eq_map_conv front_tickFree_append_iff intro: D_P T_P)
    thus \<open>(t, X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q r \<^bold>;\<^sub>\<checkmark> R))\<close>
    proof cases
      case T_P
      with F_R(3, 4) T_P(1, 4) have \<open>(map (ev \<circ> of_ev) u' @ u, X) \<in> \<F> (Q r \<^bold>;\<^sub>\<checkmark> R)\<close>
        by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
      with T_P(2, 3) show \<open>(t, X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q r \<^bold>;\<^sub>\<checkmark> R))\<close>
        by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs[of P] F_R(1) T_P(1))
    next
      case D_P
      with D_P(2,3) F_R(4) have \<open>t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q r \<^bold>;\<^sub>\<checkmark> R))\<close>
        by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs F_R(1) D_P(1))
          (metis F_imp_front_tickFree front_tickFree_append tickFree_map_ev_comp)
      thus \<open>(t, X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> (\<lambda>r. Q r \<^bold>;\<^sub>\<checkmark> R))\<close> by (fact is_processT8)
    qed
  qed
qed



(*<*)
end
  (*>*)