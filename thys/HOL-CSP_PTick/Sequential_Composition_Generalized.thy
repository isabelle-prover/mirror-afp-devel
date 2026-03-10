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


chapter \<open>Generalization of the Sequential Composition\<close>


(*<*)
theory Sequential_Composition_Generalized
  imports "HOL-CSP"
begin
  (*>*)


section \<open>Definition\<close>

text \<open>
For the sequential composition, the generalization seems quite straightforward.
In a nutshell, we just replace \<^term>\<open>Q\<close> with \<^term>\<open>Q r\<close> in the definition
of \<^term>\<open>P \<^bold>; Q\<close> since \<^term>\<open>Q\<close> is now of type \<^typ>\<open>'r \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
(instead of \<^typ>\<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>).
\<close>

lift_definition Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ::
  \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (infixl \<open>\<^bold>;\<^sub>\<checkmark>\<close> 74)
  is \<open>\<lambda>P Q. ({(t, X) |t X. (t, X \<union> range tick) \<in> \<F> P \<and> tF t} \<union>
             {(t @ u, X) |t u r X. t @ [\<checkmark>(r)] \<in> \<T> P \<and> (u, X) \<in> \<F> (Q r)} \<union>
             {(t, X). t \<in> \<D> P},
             \<D> P \<union> {t @ u |t u r. t @ [\<checkmark>(r)] \<in> \<T> P \<and> u \<in> \<D> (Q r)})\<close>
  oops


text \<open>
Except that this is not a fully satisfactory definition yet. Indeed, here, the right-hand
side argument must produce processes whose terminations keep the same type.
In other words, \<^term>\<open>Q\<close> is of type \<^typ>\<open>'r \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> while
we would like to have in full generality \<^typ>\<open>'r \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>.
The final definition given below is not immediate, and involves a precise
understanding of the behaviour of the sequential composition.
\<close>

subsection \<open>Preliminaries\<close>

text \<open>
The first key for generalizing the definition is to see that \<^term>\<open>map (ev \<circ> of_ev)\<close>
allows for changing the type of termination in tick-free traces.
\<close>

lemma tickFree_map_ev_of_ev_same_type_is : \<open>tF t \<Longrightarrow> map (ev \<circ> of_ev) t = t\<close>
  \<comment> \<open>In this case the type of termination remains unchanged.\<close>
  by (induct t) simp_all


lemma tickFree_map_ev_of_ev_eq_iff :
  \<open>tF t \<Longrightarrow> map (ev \<circ> of_ev) t = t' \<Longrightarrow> t = map (ev \<circ> of_ev) t'\<close>
  by (induct t arbitrary: t') auto

lemma tickFree_map_ev_of_ev_inj :
  \<open>tF t \<Longrightarrow> tF t' \<Longrightarrow> map (ev \<circ> of_ev) t = map (ev \<circ> of_ev) t' \<longleftrightarrow> t = t'\<close>
  by (induct t arbitrary: t') (use event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.expand in auto)+

lemma map_ev_of_ev_map_ev_of_ev [simp] :
  \<open>map (ev \<circ> of_ev) (map (ev \<circ> of_ev) t) = map (ev \<circ> of_ev) t\<close> by simp

lemma map_ev_of_ev_map_ev_of_ev_simplified [simp] :
  \<open>map (ev \<circ> of_ev \<circ> (ev \<circ> of_ev)) t = map (ev \<circ> of_ev) t\<close> by simp

lemma tickFree_map_ev_of_ev_eq_imp_ev_mem_iff :
  \<open>tF t' \<Longrightarrow> t = map (ev \<circ> of_ev) t' \<Longrightarrow> ev a \<in> set t \<longleftrightarrow> ev a \<in> set t'\<close>
  by (induct t' arbitrary: t) auto



text \<open>
The second key is to understand that \<^term>\<open>X \<union> range tick\<close>
can be rewritten as \<^term>\<open>(ev \<circ> of_ev) ` (X \<inter> range ev) \<union> range tick\<close>,
and that this second expression also allows for changing the type of termination.
\<close>

definition ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :: \<open>('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set \<Rightarrow> ('a, 's) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close>
  where \<open>ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X \<equiv> (ev \<circ> of_ev) ` (X \<inter> range ev) \<union> range tick\<close>

lemma ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_same_type_is : \<open>ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X = X \<union> range tick\<close>
  \<comment> \<open>In this case the type of termination remains unchanged.\<close>
  by (auto simp add: ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def set_eq_iff image_iff)
    (metis Int_iff event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) rangeI)


lemma mono_ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : \<open>X \<subseteq> Y \<Longrightarrow> ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X \<subseteq> ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Y\<close>
  unfolding ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def by fast


lemma ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_idem : \<open>ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) = ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X\<close>
  by (auto simp add: image_iff ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def) 
    (metis Int_iff event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) rangeI,
      metis (lifting) Int_iff Un_iff event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) image_eqI rangeI)


lemma ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comp_ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : \<open>ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<circ> ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k = ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  by (rule ext) (simp add: ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_idem)


lemma ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_iff :
  \<open>ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X = ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Y \<longleftrightarrow> X \<inter> range ev = Y \<inter> range ev\<close>
proof (rule iffI)
  show \<open>X \<inter> range ev = Y \<inter> range ev \<Longrightarrow> ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X = ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Y\<close>
    by (auto simp add: ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
next
  show \<open>X \<inter> range ev = Y \<inter> range ev\<close> if \<open>ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X = ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Y\<close>
  proof (rule set_eqI)
    show \<open>e \<in> X \<inter> range ev \<longleftrightarrow> e \<in> Y \<inter> range ev\<close> for e
      using that[unfolded set_eq_iff, THEN spec, of \<open>(ev \<circ> of_ev) e\<close>]
      by (auto simp add: ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
  qed
qed


lemma ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_image :
  \<open>ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X = map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id g ` (X \<inter> range ev) \<union> range tick\<close>
  \<comment> \<open>Note that \<^term>\<open>g\<close> is free here and does not matter.\<close>
  by (auto simp add: ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def image_iff)
    (metis Int_iff eq_id_iff map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_ev_iff rangeI,
      metis Int_iff event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) rangeI)


lemma ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_union_image_ev :
  \<open>ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (X \<union> ev ` S) = ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X \<union> ev ` S\<close>
  by (auto simp add: ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def image_iff)
    (metis Int_iff Un_iff event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) image_eqI rangeI)

lemma ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_UNIV : \<open>ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k UNIV = UNIV\<close>
  by (simp add: set_eq_iff ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def image_iff)
    (meson event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust)



subsection \<open>Formal Definition\<close>



definition div_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ::
  \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 's) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close>
  where \<open>div_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k P Q \<equiv>
         {map (ev \<circ> of_ev) t @ u |t u. t \<in> \<D> P \<and> tF t \<and> ftF u} \<union>
         {map (ev \<circ> of_ev) t @ u |t u r. t @ [\<checkmark>(r)] \<in> \<T> P \<and> tF t \<and> u \<in> \<D> (Q r)}\<close>

definition fail_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ::
  \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 's) failure\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close>
  where \<open>fail_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k P Q \<equiv>
         {(map (ev \<circ> of_ev) t, X) |t X. (t, ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<in> \<F> P \<and> tF t} \<union>
         {(map (ev \<circ> of_ev) t @ u, X) |t u r X. t @ [\<checkmark>(r)] \<in> \<T> P \<and> tF t \<and> (u, X) \<in> \<F> (Q r)} \<union>
         {(map (ev \<circ> of_ev) t @ u, X) |t u X. t \<in> \<D> P \<and> tF t \<and> ftF u}\<close>
    \<comment> \<open>\<^term>\<open>tF t\<close> is trivial when \<^term>\<open>t @ [\<checkmark>(r)] \<in> \<T> P\<close>, but we add it for proof automation\<close>

lift_definition Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ::
  \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'r \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (infixl \<open>\<^bold>;\<^sub>\<checkmark>\<close> 74)
  is \<open>\<lambda>P Q. (fail_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k P Q, div_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k P Q)\<close>
proof -
  show \<open>?thesis P Q\<close> (is \<open>is_process(?f, ?d)\<close>) for P and Q
  proof (unfold is_process_def FAILURES_def DIVERGENCES_def fst_conv snd_conv, intro conjI allI impI)
    show \<open>([], {}) \<in> ?f\<close>
      by (simp add: fail_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
        (metis append_Nil is_processT1 trace_tick_continuation_or_all_tick_failuresE)
  next
    show \<open>(t, X) \<in> ?f \<Longrightarrow> ftF t\<close> for t X
      by (auto simp add: fail_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def div_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def
          F_imp_front_tickFree D_imp_front_tickFree
          intro: front_tickFree_append)
  next
    show \<open>(t @ u, {}) \<in> ?f \<Longrightarrow> (t, {}) \<in> ?f\<close> for t u
    proof (induct u arbitrary: t)
      show \<open>(t @ [], {}) \<in> ?f \<Longrightarrow> (t, {}) \<in> ?f\<close> for t by simp
    next
      fix t e u assume prem : \<open>(t @ e # u, {}) \<in> ?f\<close>
      assume hyp : \<open>(t @ u, {}) \<in> ?f \<Longrightarrow> (t, {}) \<in> ?f\<close> for t
      from prem have \<open>((t @ [e]) @ u, {}) \<in> ?f\<close> by simp
      with hyp have \<open>(t @ [e], {}) \<in> ?f\<close> by presburger
      then consider (D_P) t' u where \<open>t @ [e] = map (ev \<circ> of_ev) t' @ u\<close> \<open>t' \<in> \<D> P\<close> \<open>tF t'\<close> \<open>ftF u\<close>
        | (F_P) t' where \<open>t @ [e] = map (ev \<circ> of_ev) t'\<close> \<open>(t', range tick) \<in> \<F> P\<close> \<open>tF t'\<close>
        | (F_Q) t' r u where \<open>t @ [e] = map (ev \<circ> of_ev) t' @ u\<close> \<open>t' @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>(u, {}) \<in> \<F> (Q r)\<close>
        by (auto simp add: fail_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def div_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
      thus \<open>(t, {}) \<in> ?f\<close>
      proof cases
        case D_P
        show ?thesis
        proof (cases u rule: rev_cases)
          assume \<open>u = []\<close>
          have \<open>(butlast t', {}) \<in> \<F> P\<close> 
            by (metis D_P(2) D_T prefixI T_F_spec append_butlast_last_id
                butlast.simps(1) is_processT3_TR)
          thus \<open>(t, {}) \<in> ?f\<close>
            by (elim trace_tick_continuation_or_all_tick_failuresE, simp_all add: fail_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
              (metis (no_types, opaque_lifting) D_P(1) \<open>u = []\<close> append.right_neutral
                append_T_imp_tickFree butlast_snoc is_processT1 map_butlast not_Cons_self2,
                metis D_P(1,3) \<open>u = []\<close> append.right_neutral butlast_snoc
                front_tickFree_iff_tickFree_butlast map_butlast tickFree_imp_front_tickFree)
        next
          fix e' u' assume \<open>u = u' @ [e']\<close>
          with D_P have \<open>t = map (ev \<circ> of_ev) t' @ u'\<close> \<open>t' \<in> \<D> P\<close> \<open>tF t'\<close> \<open>ftF u'\<close>  
            by (simp_all add: front_tickFree_append_iff)
          thus \<open>(t, {}) \<in> ?f\<close> by (auto simp add: fail_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
        qed
      next
        case F_P
        have \<open>(butlast t', {}) \<in> \<F> P\<close>
          by (metis F_P(1, 2) is_processT3 is_processT4_empty list.map_disc_iff snoc_eq_iff_butlast)
        with F_P(2) show \<open>(t, {}) \<in> ?f\<close>
          by (elim trace_tick_continuation_or_all_tick_failuresE, simp_all add: fail_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
            (metis (no_types, lifting) F_P(1) T_imp_front_tickFree append.right_neutral butlast_snoc
              front_tickFree_iff_tickFree_butlast is_processT1 map_butlast,
              metis F_P(1) F_imp_front_tickFree butlast_snoc front_tickFree_iff_tickFree_butlast map_butlast)
      next
        case F_Q
        show \<open>(t, {}) \<in> ?f\<close>
        proof (cases u rule: rev_cases)
          assume \<open>u = []\<close>
          have \<open>(butlast t', {}) \<in> \<F> P\<close>
            by (metis F_Q(2) T_F_spec append_butlast_last_id butlast.simps(1) is_processT3_TR_append)
          thus \<open>(t, {}) \<in> ?f\<close>
            by (elim trace_tick_continuation_or_all_tick_failuresE, simp_all add: fail_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
              (metis (no_types, lifting) F_Q(1) \<open>u = []\<close> append_T_imp_tickFree butlast_snoc
                is_processT1 map_butlast not_Cons_self2 self_append_conv,
                metis F_Q(1, 2) T_imp_front_tickFree \<open>u = []\<close> append_self_conv butlast_snoc
                front_tickFree_iff_tickFree_butlast is_processT3_TR_append map_butlast)
        next
          from F_Q show \<open>u = u' @ [e'] \<Longrightarrow> (t, {}) \<in> ?f\<close> for u' e'
            by (simp add: fail_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def) 
              (metis append_T_imp_tickFree is_processT3 list.distinct(1))
        qed
      qed
    qed
  next
    fix t X Y assume \<open>(t, Y) \<in> ?f \<and> X \<subseteq> Y\<close>
    hence \<open>(t, Y)\<in> ?f\<close> \<open>X \<subseteq> Y\<close> by simp_all
    from \<open>(t, Y)\<in> ?f\<close> consider (F_P) t' where \<open>t = map (ev \<circ> of_ev) t'\<close>
      \<open>(t', (ev \<circ> of_ev) ` (Y \<inter> range ev) \<union> range tick) \<in> \<F> P\<close> \<open>tF t'\<close>
    | (F_Q) t' r u where \<open>t = map (ev \<circ> of_ev) t' @ u\<close> \<open>t' @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>tF t'\<close> \<open>(u, Y) \<in> \<F> (Q r)\<close>
    | (D_P) t' u where \<open>t = map (ev \<circ> of_ev) t' @ u\<close> \<open>t' \<in> \<D> P\<close> \<open>tF t'\<close> \<open>ftF u\<close>
      by (auto simp add: fail_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
    thus \<open>(t, X) \<in> ?f\<close>
    proof cases
      case F_P
      from \<open>X \<subseteq> Y\<close> have \<open>(ev \<circ> of_ev) ` (X \<inter> range ev) \<union> range tick \<subseteq>
                         (ev \<circ> of_ev) ` (Y \<inter> range ev) \<union> range tick\<close> by blast
      with F_P(2) have \<open>(t', (ev \<circ> of_ev) ` (X \<inter> range ev) \<union> range tick) \<in> \<F> P\<close>
        by (metis is_processT4)
      with F_P(1, 3) show \<open>(t, X) \<in> ?f\<close>
        by (auto simp add: fail_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
    next
      case F_Q thus \<open>(t, X) \<in> ?f\<close>
        by (simp add: fail_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def) (metis \<open>X \<subseteq> Y\<close> is_processT4)
    next
      case D_P thus \<open>(t, X) \<in> ?f\<close> by (auto simp add: fail_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
    qed
  next
    fix t X Y assume * : \<open>(t, X) \<in> ?f \<and> (\<forall>e. e \<in> Y \<longrightarrow> (t @ [e], {}) \<notin> ?f)\<close>
    from "*" consider \<open>t \<in> ?d\<close>
      | (F_P) t' where \<open>t = map (ev \<circ> of_ev) t'\<close> \<open>(t', (ev \<circ> of_ev) ` (X \<inter> range ev) \<union> range tick) \<in> \<F> P\<close> \<open>tF t'\<close>
      | (F_Q) t' r u where \<open>t = map (ev \<circ> of_ev) t' @ u\<close> \<open>t' @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>tF t'\<close> \<open>(u, X) \<in> \<F> (Q r)\<close>
      unfolding fail_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def div_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def by auto
    thus \<open>(t, X \<union> Y) \<in> ?f\<close>
    proof cases
      show \<open>t \<in> ?d \<Longrightarrow> (t, X \<union> Y) \<in> ?f\<close>
        by (simp add: div_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def fail_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def) (metis is_processT8)
    next
      case F_P
      have \<open>(t', (ev \<circ> of_ev) ` (X \<inter> range ev) \<union> range tick \<union> (ev \<circ> of_ev) ` (Y \<inter> range ev)) \<in> \<F> P\<close>
      proof (intro is_processT5[OF F_P(2)] allI impI)
        fix e :: \<open>('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> assume \<open>e \<in> (ev \<circ> of_ev) ` (Y \<inter> range ev)\<close>
        then obtain a where \<open>e = ev a\<close> \<open>ev a \<in> Y\<close> by auto
        from "*"[THEN conjunct2, rule_format, OF this(2), unfolded fail_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def] F_P(1, 3)
        show \<open>(t' @ [e], {}) \<notin> \<F> P\<close>
          apply (simp add: fail_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def \<open>e = ev a\<close> append_eq_map_conv ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
          by (smt (verit, del_insts) append_Nil2 comp_apply event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) is_processT1
                  list.simps(8, 9) map_append tickFree_append_iff
                  tickFree_map_ev_comp trace_tick_continuation_or_all_tick_failuresE)
      qed
      also have \<open>(ev \<circ> of_ev) ` (X \<inter> range ev) \<union> range tick \<union> (ev \<circ> of_ev) ` (Y \<inter> range ev) =
                 ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (X \<union> Y)\<close> unfolding ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def by blast
      finally show \<open>(t, X \<union> Y) \<in> ?f\<close>
        using F_P(1, 3) by (auto simp add: fail_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
    next
      case F_Q
      from "*" have \<open>\<forall>e. e \<in> Y \<longrightarrow> (u @ [e], {}) \<notin> \<F> (Q r)\<close>
        by (simp add: fail_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def F_Q(1, 2))
          (metis F_Q(2) append_T_imp_tickFree not_Cons_self2)
      with F_Q(3, 4) have \<open>(u, X \<union> Y) \<in> \<F> (Q r)\<close> by (simp add: is_processT5)
      with F_Q(1-3) show \<open>(t, X \<union> Y) \<in> ?f\<close> by (auto simp add: fail_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
    qed
  next
    show \<open>t \<in> ?d \<and> tF t \<and> ftF u \<Longrightarrow> t @ u \<in> ?d\<close> for t u
      by (simp add: div_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def, elim conjE disjE exE)
        (solves \<open>use front_tickFree_append in auto\<close>,
          meson append.assoc is_processT7 tickFree_append_iff)
  next  
    show \<open>t \<in> ?d \<Longrightarrow> (t, X) \<in> ?f\<close> for t X
      by (simp add: div_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def fail_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def) (metis is_processT8)
  next
    show * : \<open>t @ [\<checkmark>(r')] \<in> ?d \<Longrightarrow> t \<in> ?d\<close> for t r'
      by (simp add: div_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def, elim disjE exE conjE)
        (metis butlast_append butlast_snoc front_tickFree_iff_tickFree_butlast non_tickFree_tick
          tickFree_append_iff tickFree_imp_front_tickFree tickFree_map_ev_comp,
          metis D_imp_front_tickFree butlast_append butlast_snoc
          div_butlast_when_non_tickFree_iff non_tickFree_tick
          tickFree_append_iff tickFree_map_ev_comp)

    fix t r' X assume \<open>(t @ [\<checkmark>(r')], {}) \<in> ?f\<close>
    then consider \<open>t @ [\<checkmark>(r')] \<in> ?d\<close>
      | (F_Q) t' r u where \<open>t @ [\<checkmark>(r')] = map (ev \<circ> of_ev) t' @ u\<close>
        \<open>t' @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>tF t'\<close> \<open>(u, X) \<in> \<F> (Q r)\<close>
      by (auto simp add: fail_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def div_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
        (metis non_tickFree_tick tickFree_append_iff tickFree_map_ev_comp,
          metis F_T F_imp_front_tickFree nonTickFree_n_frontTickFree
                non_tickFree_tick tickFree_append_iff tickFree_map_ev_comp tick_T_F)
    thus \<open>(t, X - {\<checkmark>(r')}) \<in> ?f\<close>
    proof cases
      assume \<open>t @ [\<checkmark>(r')] \<in> ?d\<close>
      with "*" have \<open>t \<in> ?d\<close> .
      thus \<open>(t, X - {\<checkmark>(r')}) \<in> ?f\<close>
        by (simp add: fail_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def div_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def) (metis is_processT8)
    next
      case F_Q
      from F_Q(1, 2) obtain u' where \<open>u = u' @ [\<checkmark>(r')]\<close>
        by (cases u rule: rev_cases, simp_all)
          (metis non_tickFree_tick tickFree_append_iff tickFree_map_ev_comp)
      with F_Q(4) have \<open>(u', X - {\<checkmark>(r')}) \<in> \<F> (Q r)\<close> by (simp add: F_T is_processT6_TR)
      with F_Q(1-3) \<open>u = u' @ [\<checkmark>(r')]\<close> show \<open>(t, X - {\<checkmark>(r')}) \<in> ?f\<close>
        by (auto simp add: fail_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
    qed
  qed
qed




section \<open>Projections\<close>

lemma F_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : \<open>\<F> (P \<^bold>;\<^sub>\<checkmark> Q) = fail_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k P Q\<close>
  by (simp add: Failures.rep_eq FAILURES_def Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.rep_eq)


lemma D_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : \<open>\<D> (P \<^bold>;\<^sub>\<checkmark> Q) = div_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k P Q\<close>
  by (simp add: Divergences.rep_eq DIVERGENCES_def Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.rep_eq)


lemma T_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_bis :
  \<open>\<T> (P \<^bold>;\<^sub>\<checkmark> Q) = {map (ev \<circ> of_ev) t |t. (t, range tick) \<in> \<F> P \<and> tF t} \<union>
                {map (ev \<circ> of_ev) t @ u |t u r. t @ [\<checkmark>(r)] \<in> \<T> P \<and> tF t \<and> u \<in> \<T> (Q r)} \<union>
                {map (ev \<circ> of_ev) t @ u |t u. t \<in> \<D> P \<and> tF t \<and> ftF u}\<close>
  by (auto simp add: Traces.rep_eq TRACES_def F_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k fail_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def
      intro: is_processT4 simp flip: Failures.rep_eq)
    (metis, metis (lifting) image_empty inf_bot_left sup_bot_left, blast)


lemma T_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>\<T> (P \<^bold>;\<^sub>\<checkmark> Q) = {map (ev \<circ> of_ev) t |t. t \<in> \<T> P \<and> tF t} \<union>
                {map (ev \<circ> of_ev) t @ u |t u r. t @ [\<checkmark>(r)] \<in> \<T> P \<and> tF t \<and> u \<in> \<T> (Q r)} \<union>
                {map (ev \<circ> of_ev) t @ u |t u. t \<in> \<D> P \<and> tF t \<and> ftF u}\<close>
  \<comment>\<open>Often easier to use\<close>
  by (auto simp add: T_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_bis F_T)
    (metis T_F_spec append.right_neutral is_processT1_TR
      trace_tick_continuation_or_all_tick_failuresE)

lemmas Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs = F_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k D_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k T_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k fail_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def div_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def


lemma mono_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq : \<open>P \<^bold>;\<^sub>\<checkmark> Q = P' \<^bold>;\<^sub>\<checkmark> Q'\<close> if * : \<open>P = P'\<close> \<open>\<And>r. r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<Longrightarrow> Q r = Q' r\<close>
  for P P' :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and Q Q' :: \<open>'r \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof (fold "*"(1), subst Process_eq_spec_optimized, safe)
  { fix t and Q Q' :: \<open>'r \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    assume \<open>t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q)\<close> and * : \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<Longrightarrow> Q r = Q' r\<close> for r
    from \<open>t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q)\<close> consider (D_P) t' u where \<open>t = map (ev \<circ> of_ev) t' @ u\<close> \<open>t' \<in> \<D> P\<close> \<open>tF t'\<close> \<open>ftF u\<close>
      | (D_Q) t' r u where \<open>t = map (ev \<circ> of_ev) t' @ u\<close> \<open>t' @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>tF t'\<close> \<open>u \<in> \<D> (Q r)\<close>
      unfolding Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
    hence \<open>t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q')\<close>
    proof cases
      case D_P thus \<open>t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q')\<close> by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
    next
      case D_Q thus \<open>t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q')\<close>
        by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
          (metis "*" D_imp_front_tickFree is_processT9 strict_ticks_of_memI)
    qed
  } note $ = this
  show \<open>t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q) \<Longrightarrow> t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q')\<close>
    and \<open>t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q') \<Longrightarrow> t \<in> \<D> (P \<^bold>;\<^sub>\<checkmark> Q)\<close> for t
    by (erule "$", simp add: "*"(2))+
next
  { fix t X and Q Q' :: \<open>'r \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    assume \<open>(t, X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q)\<close> and same_div : \<open>\<D> (P \<^bold>;\<^sub>\<checkmark> Q) = \<D> (P \<^bold>;\<^sub>\<checkmark> Q')\<close>
      and * : \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<Longrightarrow> Q r = Q' r\<close> for r
    from \<open>(t, X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q)\<close>
    consider (F_P) t' where \<open>t = map (ev \<circ> of_ev) t'\<close> \<open>(t', ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k X) \<in> \<F> P\<close> \<open>tF t'\<close>
      | (F_Q) t' r u where \<open>t = map (ev \<circ> of_ev) t' @ u\<close> \<open>t' @ [\<checkmark>(r)] \<in> \<T> P\<close>  \<open>tF t'\<close> \<open>(u, X) \<in> \<F> (Q r)\<close>
      | (D_P) t' u where \<open>t = map (ev \<circ> of_ev) t' @ u\<close> \<open>t' \<in> \<D> P\<close> \<open>tF t'\<close> \<open>ftF u\<close>
      unfolding Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs  by blast
    hence \<open>(t, X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q')\<close>
    proof cases
      case F_P thus \<open>(t, X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q')\<close> by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
    next
      case F_Q thus \<open>(t, X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q')\<close>
        by (simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
          (metis "*" F_imp_front_tickFree is_processT9 strict_ticks_of_memI)
    next
      case D_P thus \<open>(t, X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q')\<close> by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
    qed
  } note $ = this
  show \<open>\<D> (P \<^bold>;\<^sub>\<checkmark> Q) = \<D> (P \<^bold>;\<^sub>\<checkmark> Q') \<Longrightarrow> (t, X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q) \<Longrightarrow> (t, X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q')\<close>
    and \<open>\<D> (P \<^bold>;\<^sub>\<checkmark> Q) = \<D> (P \<^bold>;\<^sub>\<checkmark> Q') \<Longrightarrow> (t, X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q') \<Longrightarrow> (t, X) \<in> \<F> (P \<^bold>;\<^sub>\<checkmark> Q)\<close> for t X
    by (erule "$"; simp add: "*"(2))+
qed




text \<open>
Note that this definition allowing for changing the type of termination is actually
a generalization of the first idea that we mentioned at the beginning.
Indeed, when we enforce the type of \<^term>\<open>P\<close> and \<^term>\<open>Q\<close> to be
\<^typ>\<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and \<^typ>\<open>'r \<Rightarrow> ('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> respectively,
the projections can be rewritten as follows.
\<close>



lemma F_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_same_type :
  \<open>\<F> (P \<^bold>;\<^sub>\<checkmark> Q) = {(t, X) |t X. (t, X \<union> range tick) \<in> \<F> P \<and> tF t} \<union>
                {(t @ u, X) |t u r X. t @ [\<checkmark>(r)] \<in> \<T> P \<and> (u, X) \<in> \<F> (Q r)} \<union>
                {(t, X). t \<in> \<D> P}\<close>
  by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs tickFree_map_ev_of_ev_same_type_is ref_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_same_type_is is_processT7)
    (metis tickFree_map_ev_of_ev_same_type_is,
      metis append_T_imp_tickFree not_Cons_self2,
      metis D_T T_imp_front_tickFree T_nonTickFree_imp_decomp append.right_neutral
            front_tickFree_nonempty_append_imp is_processT9 not_Cons_self2
            tickFree_Nil tickFree_imp_front_tickFree)


lemma D_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_same_type : \<open>\<D> (P \<^bold>;\<^sub>\<checkmark> Q) = \<D> P \<union> {t @ u |t u r. t @ [\<checkmark>(r)] \<in> \<T> P \<and> u \<in> \<D> (Q r)}\<close>
  by (auto simp add: Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs tickFree_map_ev_of_ev_same_type_is is_processT7)
    (blast,
      metis D_imp_front_tickFree butlast_snoc div_butlast_when_non_tickFree_iff
            front_tickFree_charn front_tickFree_nonempty_append_imp
            self_append_conv tickFree_Nil tickFree_map_ev_of_ev_same_type_is,
      metis append_T_imp_tickFree not_Cons_self2)


lemma T_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_same_type_bis :
  \<open>\<T> (P \<^bold>;\<^sub>\<checkmark> Q) = {t. (t, range tick) \<in> \<F> P \<and> tF t} \<union>
                {t @ u |t u r. t @ [\<checkmark>(r)] \<in> \<T> P \<and> u \<in> \<T> (Q r)} \<union>
                \<D> P\<close>
  by (auto simp add: Traces.rep_eq TRACES_def F_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_same_type simp flip: Failures.rep_eq)
    (meson is_processT4 sup_ge2, meson is_processT5_S7', blast)


lemma T_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_same_type :
  \<open>\<T> (P \<^bold>;\<^sub>\<checkmark> Q) = {t \<in> \<T> P. tF t} \<union> {t @ u |t u r. t @ [\<checkmark>(r)] \<in> \<T> P \<and> u \<in> \<T> (Q r)} \<union> \<D> P\<close>
  \<comment>\<open>Often easier to use\<close>
  by (auto simp add: T_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_same_type_bis F_T)
    (metis T_F_spec append.right_neutral is_processT1_TR
      trace_tick_continuation_or_all_tick_failuresE)

lemmas Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_same_type_projs = F_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_same_type D_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_same_type T_Seq\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_same_type



(*<*)
end
  (*>*)