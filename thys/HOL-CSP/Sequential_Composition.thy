(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff, Lina Ye.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : Sequential composition
 *
 * Copyright (c) 2009 Université Paris-Sud, France
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

chapter \<open>The Sequential Composition\<close>

(*<*)
theory  Sequential_Composition
  imports Process
begin 
  (*>*)

section\<open>Definition\<close>

lift_definition  Seq :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (infixl \<open>\<^bold>;\<close> 74)
  is \<open>\<lambda>P Q. ({(t, X) |t X. (t, X \<union> range tick) \<in> \<F> P \<and> tF t} \<union>
             {(t @ u, X) |t u r X. t @ [\<checkmark>(r)] \<in> \<T> P \<and> (u, X) \<in> \<F> Q} \<union>
             {(t, X). t \<in> \<D> P},
             \<D> P \<union> {t @ u |t u r. t @ [\<checkmark>(r)] \<in> \<T> P \<and> u \<in> \<D> Q})\<close>
proof -
  show \<open>?thesis P Q\<close> (is \<open>is_process(?f, ?d)\<close>) for P and Q
  proof (unfold is_process_def FAILURES_def DIVERGENCES_def fst_conv snd_conv, intro conjI allI impI)
    show \<open>([], {}) \<in> ?f\<close>
      by simp (metis (no_types, opaque_lifting) T_F_spec append_Nil f_inv_into_f
          is_processT1 is_processT5_S7)
  next
    show \<open>(s, X) \<in> ?f \<Longrightarrow> front_tickFree s\<close> for s X
      by (auto simp: is_processT2 append_T_imp_tickFree front_tickFree_append D_imp_front_tickFree)   
  next
    show \<open>(s @ t, {}) \<in> ?f \<Longrightarrow> (s, {}) \<in> ?f\<close> for s t
    proof (induct t arbitrary: s)
      show \<open>(s @ [], {}) \<in> ?f \<Longrightarrow> (s, {}) \<in> ?f\<close> for s by simp
    next
      fix s e t assume prem : \<open>(s @ e # t, {}) \<in> ?f\<close>
      assume hyp : \<open>(s @ t, {}) \<in> ?f \<Longrightarrow> (s, {}) \<in> ?f\<close> for s
      from prem have \<open>((s @ [e]) @ t, {}) \<in> ?f\<close> by simp
      with hyp have \<open>(s @ [e], {}) \<in> ?f\<close> by presburger
      then consider (F_P) \<open>(s @ [e], range tick) \<in> \<F> P\<close> \<open>tF s\<close>
        | (F_Q) t u r where \<open>s @ [e] = t @ u\<close> \<open>t @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>(u, {}) \<in> \<F> Q\<close>
        by (auto intro: is_processT8)
          (meson F_T append_T_imp_tickFree is_processT8 not_Cons_self2)
      thus \<open>(s, {}) \<in> ?f\<close>
      proof cases
        case F_P
        from F_P(1) is_processT3 is_processT4_empty have \<open>(s, {}) \<in> \<F> P\<close> by blast
        with F_P(2) show \<open>(s, {}) \<in> ?f\<close>
          by (elim trace_tick_continuation_or_all_tick_failuresE)
            (simp_all, metis append.right_neutral is_processT1)
      next
        case F_Q
        show \<open>(s, {}) \<in> ?f\<close>
        proof (cases u rule: rev_cases)
          assume \<open>u = []\<close>
          with F_Q(1) have \<open>s @ [e] = t\<close> by simp
          with F_Q(2) T_F is_processT3 have \<open>(s, {}) \<in> \<F> P\<close> by blast
          with F_Q(2) \<open>s @ [e] = t\<close> show \<open>(s, {}) \<in> ?f\<close>
            by (elim trace_tick_continuation_or_all_tick_failuresE, simp_all)
              (metis append.right_neutral is_processT1,
                metis append_T_imp_tickFree not_Cons_self2 tickFree_append_iff)
        next
          from F_Q show \<open>u = u' @ [e'] \<Longrightarrow> (s, {}) \<in> ?f\<close> for u' e'
            by simp (metis is_processT3)
        qed
      qed
    qed
  next
    show \<open>(s, Y) \<in> ?f \<and> X \<subseteq> Y \<Longrightarrow> (s, X) \<in> ?f\<close> for s X Y
      by simp (metis Un_mono image_mono is_processT4 top.extremum_unique)
  next
    fix s X Y assume * : \<open>(s, X) \<in> ?f \<and> (\<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> ?f)\<close>
    from "*" consider \<open>s \<in> ?d\<close>
      | (F_P) \<open>(s, X \<union> range tick) \<in> \<F> P\<close> \<open>tickFree s\<close>
      | (F_Q) t u r where \<open>s = t @ u\<close> \<open>t @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>(u, X) \<in> \<F> Q\<close> by fast
    thus \<open>(s, X \<union> Y) \<in> ?f\<close>
    proof cases
      from is_processT8 show \<open>s \<in> ?d \<Longrightarrow> (s, X \<union> Y) \<in> ?f\<close> by simp blast
    next
      case F_P
      let ?Y_evs = \<open>Y - range tick\<close>
      have \<open>(s, X \<union> range tick \<union> ?Y_evs) \<in> \<F> P\<close>
      proof (intro is_processT5[OF F_P(1)] allI impI)
        fix c assume \<open>c \<in> ?Y_evs\<close>
        then obtain r where \<open>c = ev r\<close> \<open>ev r \<in> Y\<close>
          by (metis Diff_iff event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust rangeI)
        from "*"[THEN conjunct2, rule_format, OF \<open>ev r \<in> Y\<close>]
        show \<open>(s @ [c], {}) \<notin> \<F> P\<close>
          by (simp add: \<open>c = ev r\<close> \<open>tickFree s\<close> image_iff)
            (metis append_Nil2 is_processT1 trace_tick_continuation_or_all_tick_failuresE)
      qed
      also have \<open>X \<union> range tick \<union> ?Y_evs = X \<union> Y \<union> range tick\<close> by fast
      finally have \<open>(s, X \<union> Y \<union> range tick) \<in> \<F> P\<close> .
      with F_P(2) show \<open>(s, X \<union> Y) \<in> ?f\<close> by simp
    next
      case F_Q
      from "*" have \<open>\<forall>c. c \<in> Y \<longrightarrow> (u @ [c], {}) \<notin> \<F> Q\<close>
        by (simp add: F_Q(1)) (metis F_Q(2))
      with F_Q(3) have \<open>(u, X \<union> Y) \<in> \<F> Q\<close> by (simp add: is_processT5)
      with F_Q(1, 2) show \<open>(s, X \<union> Y) \<in> ?f\<close> by auto
    qed
  next
    show \<open>s \<in> ?d \<and> tF s \<and> ftF t \<Longrightarrow> s @ t \<in> ?d\<close> for s t
      by (simp, elim conjE disjE exE)
        (metis is_processT7, meson append_assoc is_processT7 tickFree_append_iff)
  next  
    from is_processT8 show \<open>s \<in> ?d \<Longrightarrow> (s, X) \<in> ?f\<close> for s X by simp blast
  next
    show \<open>s @ [\<checkmark>(r)] \<in> ?d \<Longrightarrow> s \<in> ?d\<close> for s r
      by (simp, elim conjE disjE exE)
        (meson is_processT9,
          metis (no_types) D_T T_nonTickFree_imp_decomp append.assoc append_T_imp_tickFree
          butlast_snoc is_processT9 non_tickFree_tick not_Cons_self2 tickFree_append_iff)
    fix s r X assume \<open>(s @ [\<checkmark>(r)], {}) \<in> ?f\<close>
    then consider \<open>s @ [\<checkmark>(r)] \<in> ?d\<close>
      | (F_Q) t u r' where \<open>s @ [\<checkmark>(r)] = t @ u\<close> \<open>t @ [\<checkmark>(r')] \<in> \<T> P\<close> \<open>(u, X) \<in> \<F> Q\<close>
      by (auto simp add: is_processT8)
        (metis F_T append_T_imp_tickFree is_processT5_S7
          non_tickFree_tick not_Cons_self2 tickFree_append_iff)
    thus \<open>(s, X - {\<checkmark>(r)}) \<in> ?f\<close>
    proof cases
      assume \<open>s @ [\<checkmark>(r)] \<in> ?d\<close>
      hence \<open>s \<in> ?d\<close> by (fact \<open>s @ [\<checkmark>(r)] \<in> ?d \<Longrightarrow> s \<in> ?d\<close>)
      with is_processT8 show \<open>(s, X - {\<checkmark>(r)}) \<in> ?f\<close> by simp blast
    next
      case F_Q
      from F_Q(1, 2) obtain u' where \<open>u = u' @ [\<checkmark>(r)]\<close>
        by (cases u rule: rev_cases, simp_all)
          (meson append_T_imp_tickFree non_tickFree_tick not_Cons_self2 tickFree_append_iff)
      with F_Q(3) have \<open>(u', X - {\<checkmark>(r)}) \<in> \<F> Q\<close> by (simp add: F_T is_processT6_TR)
      with F_Q(1, 2) \<open>u = u' @ [\<checkmark>(r)]\<close> show \<open>(s, X - {\<checkmark>(r)}) \<in> ?f\<close> by auto
    qed
  qed
qed



section\<open>The Projections\<close>

lemma F_Seq : \<open>\<F> (P \<^bold>; Q) = {(t, X) |t X. (t, X \<union> range tick) \<in> \<F> P \<and> tF t} \<union>
                           {(t @ u, X) |t u r X. t @ [\<checkmark>(r)] \<in> \<T> P \<and> (u, X) \<in> \<F> Q} \<union>
                           {(t, X). t \<in> \<D> P}\<close>
  by (simp add: Failures.rep_eq FAILURES_def Seq.rep_eq)


lemma D_Seq : \<open>\<D> (P \<^bold>; Q) = \<D> P \<union> {t @ u |t u r. t @ [\<checkmark>(r)] \<in> \<T> P \<and> u \<in> \<D> Q}\<close>
  by (simp add: Divergences.rep_eq DIVERGENCES_def Seq.rep_eq)


lemma T_Seq_bis :
  \<open>\<T> (P \<^bold>; Q) = {t. (t, range tick) \<in> \<F> P \<and> tF t} \<union>
               {t @ u |t u r. t @ [\<checkmark>(r)] \<in> \<T> P \<and> u \<in> \<T> Q} \<union>
               \<D> P\<close>
  by (auto simp add: Traces.rep_eq TRACES_def F_Seq simp flip: Failures.rep_eq)
    (meson is_processT4 sup_ge2, meson is_processT5_S7', blast)


lemma T_Seq :
  \<open>\<T> (P \<^bold>; Q) = {t \<in> \<T> P. tF t} \<union> {t @ u |t u r. t @ [\<checkmark>(r)] \<in> \<T> P \<and> u \<in> \<T> Q} \<union> \<D> P\<close>
  \<comment>\<open>Often easier to use\<close>
  by (auto simp add: T_Seq_bis F_T)
    (metis T_F_spec append.right_neutral is_processT1_TR
      trace_tick_continuation_or_all_tick_failuresE)

lemmas Seq_projs = F_Seq D_Seq T_Seq



section\<open> Continuity Rule \<close>

lemma mono_Seq : \<open>P \<sqsubseteq> Q \<Longrightarrow> R \<sqsubseteq> S \<Longrightarrow> P \<^bold>; R \<sqsubseteq> Q \<^bold>; S\<close> for P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof -
  have \<open>P \<^bold>; S \<sqsubseteq> Q \<^bold>; S\<close> if \<open>P \<sqsubseteq> Q\<close> for P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and S
  proof (unfold le_approx_def, intro conjI allI impI subset_antisym)
    show \<open>\<D> (Q \<^bold>; S) \<subseteq> \<D> (P \<^bold>; S)\<close>
      apply (rule subsetI, simp add: D_Seq, elim disjE exE conjE)
      by (meson in_mono le_approx1 \<open>P \<sqsubseteq> Q\<close>) (metis D_T le_approx2T \<open>P \<sqsubseteq> Q\<close>)
  next
    show \<open>s \<notin> \<D> (P \<^bold>; S) \<Longrightarrow> \<R>\<^sub>a (P \<^bold>; S) s \<subseteq> \<R>\<^sub>a (Q \<^bold>; S) s\<close> for s
      apply (auto simp add: D_Seq Refusals_after_def F_Seq set_eq_iff append_T_imp_tickFree)[1]
      by (meson le_approx2 \<open>P \<sqsubseteq> Q\<close>)
        (metis F_imp_front_tickFree append_T_imp_tickFree is_processT7 is_processT9 le_approx2T not_Cons_self2 \<open>P \<sqsubseteq> Q\<close>)+
  next
    show \<open>s \<notin> \<D> (P \<^bold>; S) \<Longrightarrow> \<R>\<^sub>a (Q \<^bold>; S) s \<subseteq> \<R>\<^sub>a (P \<^bold>; S) s\<close> for s
      apply (auto simp add: D_Seq Refusals_after_def F_Seq set_eq_iff append_T_imp_tickFree)
          apply (meson le_approx2 \<open>P \<sqsubseteq> Q\<close>)
      by ((metis D_T le_approx2T \<open>P \<sqsubseteq> Q\<close>)+)[2]
        ((meson in_mono le_approx1 \<open>P \<sqsubseteq> Q\<close>)+)[2]
  next
    show \<open>min_elems (\<D> (P \<^bold>; S)) \<subseteq> \<T> (Q \<^bold>; S)\<close>
    proof (rule subset_trans; rule subsetI)
      fix t assume \<open>t \<in> min_elems (\<D> (P \<^bold>; S))\<close>
      hence \<open>t \<in> \<D> (P \<^bold>; S)\<close> by (meson elem_min_elems)
      then consider \<open>t \<in> \<D> P\<close> | u v r where \<open>t = u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>u \<notin> \<D> P\<close> \<open>v \<in> \<D> S\<close>
        by (simp add: D_Seq)
          (metis D_imp_front_tickFree append_T_imp_tickFree is_processT7 not_Cons_self2)
      thus \<open>t \<in> min_elems (\<D> P) \<union> {u @ v |u v r. u @ [\<checkmark>(r)] \<in> \<T> P \<and> u \<notin> \<D> P \<and> v \<in> min_elems (\<D> S)}\<close>
      proof cases
        assume \<open>t \<in> \<D> P\<close>
        with \<open>t \<in> min_elems (\<D> (P \<^bold>; S))\<close> have \<open>t \<in> min_elems (\<D> P)\<close>
          by (auto simp add: D_Seq min_elems_def)
        thus \<open>t \<in> min_elems (\<D> P) \<union> {u @ v |u v r. u @ [\<checkmark>(r)] \<in> \<T> P \<and> u \<notin> \<D> P \<and> v \<in> min_elems (\<D> S)}\<close> ..
      next
        fix u v r assume \<open>t = u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>u \<notin> \<D> P\<close> \<open>v \<in> \<D> S\<close>
        with \<open>t \<in> min_elems (\<D> (P \<^bold>; S))\<close>
        have \<open>t \<in> {u @ v |u v r. u @ [\<checkmark>(r)] \<in> \<T> P \<and> u \<notin> \<D> P \<and> v \<in> min_elems (\<D> S)}\<close>
          by (simp add: D_Seq min_elems_def)
            (metis (mono_tags, lifting) Un_iff less_append mem_Collect_eq)
        thus \<open>t \<in> min_elems (\<D> P) \<union> {u @ v |u v r. u @ [\<checkmark>(r)] \<in> \<T> P \<and> u \<notin> \<D> P \<and> v \<in> min_elems (\<D> S)}\<close> ..
      qed
    next
      show \<open>t \<in> min_elems (\<D> P) \<union> {u @ v |u v r. u @ [\<checkmark>(r)] \<in> \<T> P \<and> u \<notin> \<D> P \<and> v \<in> min_elems (\<D> S)}
            \<Longrightarrow> t \<in> \<T> (Q \<^bold>; S)\<close> for t
        by (simp add: T_Seq, elim disjE exE conjE)
          (metis (no_types, lifting) Prefix_Order.prefixI T_nonTickFree_imp_decomp
            elem_min_elems in_mono is_processT9 le_approx3 min_elems_no
            not_Cons_self2 self_append_conv \<open>P \<sqsubseteq> Q\<close>,
            metis D_T elem_min_elems is_processT9 le_approx2T \<open>P \<sqsubseteq> Q\<close>)
    qed
  qed

  moreover have \<open>S \<^bold>; P \<sqsubseteq> S \<^bold>; Q\<close> if \<open>P \<sqsubseteq> Q\<close> for P Q and S :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  proof (unfold le_approx_def, intro conjI allI impI subset_antisym)
    show \<open>\<D> (S \<^bold>; Q) \<subseteq> \<D> (S \<^bold>; P)\<close>
      by (rule subsetI, simp add: D_Seq) (metis in_mono le_approx1 that)
  next
    show \<open>s \<notin> \<D> (S \<^bold>; P) \<Longrightarrow> \<R>\<^sub>a (S \<^bold>; P) s \<subseteq> \<R>\<^sub>a (S \<^bold>; Q) s\<close> for s
      apply (auto simp add: D_Seq Refusals_after_def F_Seq append_T_imp_tickFree)
      by (metis proc_ord2a that)+
  next
    show \<open>s \<notin> \<D> (S \<^bold>; P) \<Longrightarrow> \<R>\<^sub>a (S \<^bold>; Q) s \<subseteq> \<R>\<^sub>a (S \<^bold>; P) s\<close> for s
      apply (auto simp add: D_Seq Refusals_after_def F_Seq append_T_imp_tickFree)
      by (metis proc_ord2a that)+
  next
    show \<open>min_elems (\<D> (S \<^bold>; P)) \<subseteq> \<T> (S \<^bold>; Q)\<close>
    proof (rule subset_trans; rule subsetI)
      fix t assume \<open>t \<in> min_elems (\<D> (S \<^bold>; P))\<close>
      hence \<open>t \<in> \<D> (S \<^bold>; P)\<close> by (meson elem_min_elems)
      then consider \<open>t \<in> \<D> S\<close> | u v r where \<open>t = u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> S\<close> \<open>u \<notin> \<D> S\<close> \<open>v \<in> \<D> P\<close>
        by (simp add: D_Seq)
          (metis D_imp_front_tickFree append_T_imp_tickFree is_processT7 not_Cons_self2)
      thus \<open>t \<in> min_elems (\<D> S) \<union> {u @ v |u v r. u @ [\<checkmark>(r)] \<in> \<T> S \<and> u \<notin> \<D> S \<and> v \<in> min_elems (\<D> P)}\<close>
      proof cases
        assume \<open>t \<in> \<D> S\<close>
        with \<open>t \<in> min_elems (\<D> (S \<^bold>; P))\<close> have \<open>t \<in> min_elems (\<D> S)\<close>
          by (auto simp add: D_Seq min_elems_def)
        thus \<open>t \<in> min_elems (\<D> S) \<union> {u @ v |u v r. u @ [\<checkmark>(r)] \<in> \<T> S \<and> u \<notin> \<D> S \<and> v \<in> min_elems (\<D> P)}\<close> ..
      next
        fix u v r assume \<open>t = u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> S\<close> \<open>u \<notin> \<D> S\<close> \<open>v \<in> \<D> P\<close>
        with \<open>t \<in> min_elems (\<D> (S \<^bold>; P))\<close>
        have \<open>t \<in> {u @ v |u v r. u @ [\<checkmark>(r)] \<in> \<T> S \<and> u \<notin> \<D> S \<and> v \<in> min_elems (\<D> P)}\<close>
          by (simp add: D_Seq min_elems_def)
            (metis (mono_tags, lifting) Un_iff less_append mem_Collect_eq)
        thus \<open>t \<in> min_elems (\<D> S) \<union> {u @ v |u v r. u @ [\<checkmark>(r)] \<in> \<T> S \<and> u \<notin> \<D> S \<and> v \<in> min_elems (\<D> P)}\<close> ..
      qed
    next
      show \<open>t \<in> min_elems (\<D> S) \<union> {u @ v |u v r. u @ [\<checkmark>(r)] \<in> \<T> S \<and> u \<notin> \<D> S \<and> v \<in> min_elems (\<D> P)}
            \<Longrightarrow> t \<in> \<T> (S \<^bold>; Q)\<close> for t
        by (simp add:  T_Seq, elim disjE exE conjE)
          (use elem_min_elems in blast,
            metis insert_absorb insert_subset le_approx3 \<open>P \<sqsubseteq> Q\<close>)
    qed
  qed

  ultimately show \<open>P \<sqsubseteq> Q \<Longrightarrow> R \<sqsubseteq> S \<Longrightarrow> P \<^bold>; R \<sqsubseteq> Q \<^bold>; S\<close> by (meson below_trans)
qed


context begin

private lemma chain_Seq_left: \<open>chain Y \<Longrightarrow> chain (\<lambda>i. Y i \<^bold>; S)\<close>
  by (simp add: mono_Seq po_class.chain_def)

private lemma chain_Seq_right: \<open>chain Y \<Longrightarrow> chain (\<lambda>i. S \<^bold>; Y i)\<close>
  by (simp add: mono_Seq po_class.chain_def)


private lemma cont_left_prem_Seq :
  \<open>(\<Squnion>i. Y i) \<^bold>; S = (\<Squnion>i. Y i \<^bold>; S)\<close> (is \<open>?lhs = ?rhs\<close>) if \<open>chain Y\<close>
proof (subst Process_eq_spec_optimized, safe)
  show \<open>t \<in> \<D> ?lhs \<Longrightarrow> t \<in> \<D> ?rhs\<close> for t
    by (auto simp add: D_Seq limproc_is_thelub \<open>chain Y\<close> chain_Seq_left LUB_projs)
next
  fix t assume \<open>t \<in> \<D> ?rhs\<close>
  define T where \<open>T i \<equiv> {u \<in> \<D> (Y i). t = u} \<union>
                        {u. \<exists>r v. t = u @ v \<and> u @ [\<checkmark>(r)] \<in> \<T> (Y i) \<and> v \<in> \<D> S}\<close> for i
  from \<open>t \<in> \<D> ?rhs\<close> have \<open>T i \<noteq> {}\<close> for i
    by (auto simp add: T_def D_Seq limproc_is_thelub \<open>chain Y\<close> chain_Seq_left D_LUB)
  moreover have \<open>finite (T 0)\<close> unfolding T_def by (prove_finite_subset_of_prefixes t)
  moreover have \<open>T (Suc i) \<subseteq> T i\<close> for i
    unfolding T_def apply (intro allI Un_mono subsetI, simp_all)
    by (meson \<open>chain Y\<close> in_mono le_approx1 po_class.chainE)
      (metis \<open>chain Y\<close> le_approx_lemma_T po_class.chain_def subset_iff)
  ultimately have \<open>(\<Inter>i. T i) \<noteq> {}\<close> by (rule Inter_nonempty_finite_chained_sets)
  then obtain u where \<open>\<forall>i. u \<in> T i\<close> by fast
  show \<open>t \<in> \<D> ?lhs\<close>
  proof (cases \<open>\<forall>i. t \<in> \<D> (Y i)\<close>)
    show \<open>\<forall>i. t \<in> \<D> (Y i) \<Longrightarrow> t \<in> \<D> ?lhs\<close>
      by (simp add: D_Seq limproc_is_thelub D_LUB \<open>chain Y\<close>)
  next
    assume \<open>\<not> (\<forall>i. t \<in> \<D> (Y i))\<close>
    with \<open>\<forall>i. u \<in> T i\<close> obtain r v j
      where \<open>t = u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> (Y j)\<close> \<open>u \<notin> \<D> (Y j)\<close> \<open>v \<in> \<D> S\<close>
      by (simp add: T_def)
        (metis D_imp_front_tickFree append_T_imp_tickFree is_processT7 not_Cons_self2)
    from \<open>u \<notin> \<D> (Y j)\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> (Y j)\<close> have \<open>\<forall>i\<ge>j. u @ [\<checkmark>(r)] \<in> \<T> (Y i)\<close>
      by (meson ND_F_dir2' \<open>chain Y\<close> \<open>u \<notin> \<D> (Y j)\<close> is_processT9 is_ub_thelub)
    hence \<open>u @ [\<checkmark>(r)] \<in> \<T> (\<Squnion>i. Y i)\<close>
      by (simp add: limproc_is_thelub T_LUB \<open>chain Y\<close>)
        (meson D_T \<open>chain Y\<close> le_approx2T nle_le po_class.chain_mono)
    with \<open>v \<in> \<D> S\<close> show \<open>t \<in> \<D> ?lhs\<close> by (auto simp add: \<open>t = u @ v\<close> D_Seq \<open>chain Y\<close>)
  qed
next
  show \<open>(t, X) \<in> \<F> ?lhs \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> for t X
    by (auto simp add: F_Seq limproc_is_thelub \<open>chain Y\<close> chain_Seq_left LUB_projs)
next
  assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
  fix t X assume \<open>(t, X) \<in> \<F> ?rhs\<close>
  then consider \<open>\<forall>i. t \<in> \<D> (Y i)\<close> 
    | j       where \<open>t \<notin> \<D> (Y j)\<close> \<open>(t, X \<union> range tick) \<in> \<F> (Y j)\<close> \<open>tF t\<close>
    | j u r v where \<open>t \<notin> \<D> (Y j)\<close> \<open>t = u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> (Y j)\<close> \<open>(v, X) \<in> \<F> S\<close>
    by (simp add: limproc_is_thelub \<open>chain Y\<close> chain_Seq_left F_LUB F_Seq) blast
  thus \<open>(t, X) \<in> \<F> ?lhs\<close>
  proof cases
    show \<open>\<forall>i. t \<in> \<D> (Y i) \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close>
      by (simp add: D_LUB_2 D_Seq is_processT8 limproc_is_thelub \<open>chain Y\<close>)
  next
    fix j assume \<open>t \<notin> \<D> (Y j)\<close> \<open>(t, X \<union> range tick) \<in> \<F> (Y j)\<close> \<open>tF t\<close>
    hence \<open>(t, X \<union> range tick) \<in> \<F> (\<Squnion>i. Y i)\<close>
      by (simp add: limproc_is_thelub \<open>chain Y\<close> F_LUB)
        (metis is_processT8 nle_le po_class.chain_mono proc_ord2a \<open>chain Y\<close>)
    with \<open>tF t\<close> show \<open>(t, X) \<in> \<F> ?lhs\<close> by (simp add: F_Seq)
  next
    fix j u r v assume \<open>t \<notin> \<D> (Y j)\<close> \<open>t = u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> (Y j)\<close> \<open>(v, X) \<in> \<F> S\<close>
    hence \<open>u @ [\<checkmark>(r)] \<in> \<T> (\<Squnion>i. Y i)\<close>
      by (simp add: limproc_is_thelub \<open>chain Y\<close> T_LUB)
        (meson F_imp_front_tickFree ND_F_dir2' T_F_spec append_T_imp_tickFree
          is_processT7 is_ub_thelub min_elems2 not_Cons_self2 \<open>chain Y\<close>)
    with \<open>(v, X) \<in> \<F> S\<close> show \<open>(t, X) \<in> \<F> ?lhs\<close> by (auto simp add: F_Seq \<open>t = u @ v\<close>)
  qed
qed


private lemma cont_right_prem_Seq :
  \<open>S \<^bold>; (\<Squnion>i. Y i) = (\<Squnion>i. S \<^bold>; Y i)\<close> (is \<open>?lhs = ?rhs\<close>) if \<open>chain Y\<close> 
proof (subst Process_eq_spec_optimized, safe)
  show \<open>t \<in> \<D> ?lhs \<Longrightarrow> t \<in> \<D> ?rhs\<close> for t
    by (auto simp add: D_Seq limproc_is_thelub \<open>chain Y\<close> chain_Seq_right D_LUB)
next
  show \<open>t \<in> \<D> ?lhs\<close> if \<open>t \<in> \<D> ?rhs\<close> for t
  proof (cases \<open>t \<in> \<D> S\<close>)
    show \<open>t \<in> \<D> S \<Longrightarrow> t \<in> \<D> (S \<^bold>; (\<Squnion>i. Y i))\<close> by (simp add: D_Seq)
  next
    assume \<open>t \<notin> \<D> S\<close>
    define T where \<open>T i \<equiv> {u. \<exists>v r. t = u @ v \<and> u @ [\<checkmark>(r)] \<in> \<T> S \<and> v \<in> \<D> (Y i)}\<close> for i
    from \<open>t \<notin> \<D> S\<close> \<open>t \<in> \<D> ?rhs\<close> have \<open>T i \<noteq> {}\<close> for i
      by (simp add: T_def limproc_is_thelub chain_Seq_right \<open>chain Y\<close> D_LUB D_Seq)
    moreover have \<open>finite (T 0)\<close>
      unfolding T_def by (prove_finite_subset_of_prefixes t)
    moreover have \<open>T (Suc i) \<subseteq> T i\<close> for i
      unfolding T_def apply (intro allI Un_mono subsetI; simp)
      by (metis le_approx1 po_class.chainE subset_iff \<open>chain Y\<close>)
    ultimately have \<open>(\<Inter>i. T i) \<noteq> {}\<close> by (rule Inter_nonempty_finite_chained_sets)
    then obtain u where \<open>\<forall>i. u \<in> T i\<close> by fast
    then obtain v r where \<open>t = u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> S\<close> \<open>\<forall>i. v \<in> \<D> (Y i)\<close>
      by (simp add: T_def) blast
    from \<open>\<forall>i. v \<in> \<D> (Y i)\<close> have \<open>v \<in> \<D> (\<Squnion>i. Y i)\<close>
      by (simp add: D_LUB \<open>chain Y\<close> limproc_is_thelub)
    with \<open>u @ [\<checkmark>(r)] \<in> \<T> S\<close> show \<open>t \<in> \<D> ?lhs\<close> by (auto simp add: \<open>t = u @ v\<close>  D_Seq)
  qed
next
  show \<open>(t, X) \<in> \<F> ?lhs \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> for t X
    by (auto simp add: F_Seq limproc_is_thelub \<open>chain Y\<close> chain_Seq_right F_LUB)
next
  assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
  show \<open>(t, X) \<in> \<F> ?lhs\<close> if \<open>(t, X) \<in> \<F> ?rhs\<close> for t X
  proof (cases \<open>t \<in> \<D> ?rhs\<close>)
    show \<open>t \<in> \<D> ?rhs \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close>
      by (simp add: is_processT8 same_div)
  next
    assume \<open>t \<notin> \<D> ?rhs\<close>
    then obtain j where \<open>t \<notin> \<D> (S \<^bold>; Y j)\<close>
      by (auto simp add: limproc_is_thelub chain_Seq_right \<open>chain Y\<close> D_LUB)
    moreover from \<open>(t, X) \<in> \<F> ?rhs\<close> have \<open>(t, X) \<in> \<F> (S \<^bold>; Y j)\<close>
      by (simp add: limproc_is_thelub chain_Seq_right \<open>chain Y\<close> F_LUB)
    ultimately show \<open>(t, X) \<in> \<F> ?lhs\<close>
      by (fact le_approx2[OF mono_Seq[OF below_refl is_ub_thelub[OF \<open>chain Y\<close>]], THEN iffD2])
  qed
qed


lemma Seq_cont [simp] : \<open>cont (\<lambda>x. f x \<^bold>; g x)\<close> if \<open>cont f\<close> and \<open>cont g\<close>
proof (rule cont_apply[where f = \<open>\<lambda>x y. f x \<^bold>; y\<close>])
  show \<open>cont g\<close> by (fact \<open>cont g\<close>)
next
  show \<open>cont ((\<^bold>;) (f x))\<close> for x
  proof (rule contI2)
    show \<open>monofun ((\<^bold>;) (f x))\<close> by (simp add: mono_Seq monofunI)
  next
    show \<open>chain Y \<Longrightarrow> f x \<^bold>; (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. f x \<^bold>; Y i)\<close> for Y
      by (simp add: cont_right_prem_Seq)
  qed
next
  show \<open>cont (\<lambda>x. f x \<^bold>; y)\<close> for y
  proof (rule contI2)
    show \<open>monofun (\<lambda>x. f x \<^bold>; y)\<close> by (simp add: cont2monofunE mono_Seq monofunI \<open>cont f\<close>)
  next
    show \<open>chain Y \<Longrightarrow> f (\<Squnion>i. Y i) \<^bold>; y \<sqsubseteq> (\<Squnion>i. f (Y i) \<^bold>; y)\<close> for Y
      by (simp add: ch2ch_cont cont2contlubE cont_left_prem_Seq \<open>cont f\<close>)
  qed
qed


end

(*<*)
end
  (*>*)
