(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSPM - Architectural operators for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff.
 *
 * This file       : The Interrupt operator
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

section\<open> The Interrupt Operator \<close>

(*<*)
theory  Interrupt
  imports "HOL-CSP.CSP"
begin
  (*>*)

subsection \<open>Definition\<close>

text \<open>We want to add the binary operator of interruption of \<^term>\<open>P\<close> by \<^term>\<open>Q\<close>: 
      it behaves like \<^term>\<open>P\<close> except that at any time \<^term>\<open>Q\<close> can take over.\<close>

text \<open>The definition provided by Roscoe \<^cite>\<open>\<open>p.239\<close> in "Roscoe2010UnderstandingCS"\<close> does
      not respect the invariant \<^const>\<open>is_process\<close>: it seems like \<^const>\<open>tick\<close> is not handled.\<close>

text \<open>We propose here our corrected version.\<close>

lift_definition Interrupt :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (infixl \<open>\<triangle>\<close> 81)
  is \<open>\<lambda>P Q. 
  ({(t @ [\<checkmark>(r)], X) |t r X. t @ [\<checkmark>(r)] \<in> \<T> P} \<union>
   {(t, X - {\<checkmark>(r)}) |t r X. t @ [\<checkmark>(r)] \<in> \<T> P} \<union>
   {(t, X). (t, X) \<in> \<F> P \<and> tF t \<and> ([], X) \<in> \<F> Q} \<union>
   {(t @ u, X) |t u X. t \<in> \<T> P \<and> tF t \<and> (u, X) \<in> \<F> Q \<and> u \<noteq> []} \<union>
   {(t, X - {\<checkmark>(r)}) |t r X. t \<in> \<T> P \<and> tF t \<and> [\<checkmark>(r)] \<in> \<T> Q} \<union>
   {(t, X). t \<in> \<D> P} \<union>
   {(t @ u, X) |t u X. t \<in> \<T> P \<and> tF t \<and> u \<in> \<D> Q},
   \<D> P \<union> {t @ u |t u. t \<in> \<T> P \<and> tF t \<and> u \<in> \<D> Q})\<close>
proof -
  show \<open>?thesis P Q\<close> 
    (is \<open>is_process (?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7, ?d1 \<union> ?d2)\<close>) for P Q
    unfolding is_process_def FAILURES_def DIVERGENCES_def fst_conv snd_conv
  proof (intro conjI allI impI)
    have \<open>([], {}) \<in> ?f3\<close> by (simp add: is_processT1)
    thus \<open>([], {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by fast
  next
    show \<open>(t, X) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7 \<Longrightarrow> ftF t\<close> for t X
      by (simp add: is_processT2 D_imp_front_tickFree front_tickFree_append)
        (meson front_tickFree_append front_tickFree_dw_closed is_processT2_TR process_charn)
  next
    fix t u
    show \<open>(t @ u, {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7 \<Longrightarrow>
              (t, {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close>
    proof (induct u rule: rev_induct)
      show \<open>(t @ [], {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7 \<Longrightarrow>
                 (t, {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by simp
    next
      fix a u
      assume assm : \<open>(t @ u @ [a], {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close>
        and  hyp : \<open>(t @ u, {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7 \<Longrightarrow>
                         (t, {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close>
      from assm have \<open>(t @ u @ [a], {}) \<in> ?f1 \<or> (t @ u @ [a], {}) \<in> ?f2 \<or>
        (t @ u @ [a], {}) \<in> ?f3 \<or> (t @ u @ [a], {}) \<in> ?f4 \<or> (t @ u @ [a], {}) \<in> ?f5 \<or> 
        (t @ u @ [a], {}) \<in> ?f6 \<or> (t @ u @ [a], {}) \<in> ?f7\<close> by fast
      thus \<open>(t, {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close>
      proof (elim disjE)
        assume \<open>(t @ u @ [a], {}) \<in> ?f1\<close>
        hence \<open>(t, {}) \<in> ?f3\<close>
          by simp (meson T_F append_T_imp_tickFree is_processT snoc_eq_iff_butlast) 
        thus \<open>(t, {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
      next
        assume \<open>(t @ u @ [a], {}) \<in> ?f2\<close>
        hence \<open>(t, {}) \<in> ?f3\<close>
          by simp (metis T_F Nil_is_append_conv append_T_imp_tickFree is_processT list.discI)
        thus \<open>(t, {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
      next
        assume \<open>(t @ u @ [a], {}) \<in> ?f3\<close>
        with is_processT3 have \<open>(t, {}) \<in> ?f3\<close> by simp blast
        thus \<open>(t, {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
      next
        assume \<open>(t @ u @ [a], {}) \<in> ?f4\<close>
        then obtain t' u'
          where * : \<open>t @ u = t' @ u'\<close> \<open>t' \<in> \<T> P\<close> \<open>tF t'\<close> \<open>(u' @ [a], {}) \<in> \<F> Q\<close>
          by simp (metis butlast_append last_appendR snoc_eq_iff_butlast)
        show \<open>(t, {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close>
        proof (cases \<open>u' = []\<close>)
          assume \<open>u' = []\<close>
          with "*"(1, 2, 3) have \<open>(t, {}) \<in> ?f3\<close>
            by simp (metis T_F process_charn tickFree_append_iff)
          thus \<open>(t, {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
        next
          assume \<open>u' \<noteq> []\<close>
          with "*" is_processT3 have \<open>(t @ u, {}) \<in> ?f4\<close> by simp blast
          thus \<open>(t, {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by (intro hyp) blast
        qed
      next
        assume \<open>(t @ u @ [a], {}) \<in> ?f5\<close>
        hence \<open>(t, {}) \<in> ?f3\<close> by simp (metis T_F process_charn)
        thus \<open>(t, {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
      next
        assume \<open>(t @ u @ [a], {}) \<in> ?f6\<close>
        hence \<open>(t, {}) \<in> ?f3\<close>
          by simp (meson D_T append_T_imp_tickFree process_charn snoc_eq_iff_butlast)
        thus \<open>(t, {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
      next
        assume \<open>(t @ u @ [a], {}) \<in> ?f7\<close>
        then obtain t' u'
          where * : \<open>t @ u @ [a] = t' @ u'\<close> \<open>t' \<in> \<T> P\<close> \<open>tF t'\<close> \<open>u' \<in> \<D> Q\<close> by blast
        hence \<open>(t @ u, {}) \<in> (if length u' \<le> 1 then ?f3 else ?f4)\<close>
          apply (cases u' rule: rev_cases; simp)
          by (metis T_F append_assoc process_charn tickFree_append_iff)
            (metis D_T T_F is_processT3)
        thus \<open>(t, {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close>
          by (intro hyp) (meson UnI1 UnI2)
      qed
    qed
  next
    fix t X Y
    assume assm : \<open>(t, Y) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7 \<and> X \<subseteq> Y\<close>
    hence \<open>(t, Y) \<in> ?f1 \<or> (t, Y) \<in> ?f2 \<or> (t, Y) \<in> ?f3 \<or> (t, Y) \<in> ?f4 \<or>
           (t, Y) \<in> ?f5 \<or> (t, Y) \<in> ?f6 \<or> (t, Y) \<in> ?f7\<close> by fast
    thus \<open>(t, X) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close>
    proof (elim disjE)
      assume \<open>(t, Y) \<in> ?f1\<close>
      hence \<open>(t, X) \<in> ?f1\<close> by simp
      thus \<open>(t, X) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    next
      assume \<open>(t, Y) \<in> ?f2\<close>
      with assm[THEN conjunct2] have \<open>(t, X) \<in> ?f2\<close> by simp blast
      thus \<open>(t, X) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    next
      assume \<open>(t, Y) \<in> ?f3\<close>
      with assm[THEN conjunct2] is_processT4 have \<open>(t, X) \<in> ?f3\<close> by simp blast
      thus \<open>(t, X) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    next
      assume \<open>(t, Y) \<in> ?f4\<close>
      with assm[THEN conjunct2] is_processT4 have \<open>(t, X) \<in> ?f4\<close> by simp blast
      thus \<open>(t, X) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    next
      assume \<open>(t, Y) \<in> ?f5\<close>
      with assm[THEN conjunct2] have \<open>(t, X) \<in> ?f5\<close> by simp blast
      thus \<open>(t, X) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    next
      assume \<open>(t, Y) \<in> ?f6\<close>
      hence \<open>(t, X) \<in> ?f6\<close> by simp
      thus \<open>(t, X) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    next
      assume \<open>(t, Y) \<in> ?f7\<close>
      hence \<open>(t, X) \<in> ?f7\<close> by simp
      thus \<open>(t, X) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    qed
  next
    fix t X Y
    assume assm : \<open>(t, X) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7 \<and>
                   (\<forall>c. c \<in> Y \<longrightarrow> (t @ [c], {}) \<notin> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7)\<close>
    have \<open>(t, X) \<in> ?f1 \<or> (t, X) \<in> ?f2 \<or> (t, X) \<in> ?f3 \<or> (t, X) \<in> ?f4 \<or>
          (t, X) \<in> ?f5 \<or> (t, X) \<in> ?f6 \<or> (t, X) \<in> ?f7\<close> using assm[THEN conjunct1] by fast
    thus \<open>(t, X \<union> Y) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close>
    proof (elim disjE)
      assume \<open>(t, X) \<in> ?f1\<close>
      hence \<open>(t, X \<union> Y) \<in> ?f1\<close> by simp
      thus \<open>(t, X \<union> Y) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    next
      assume \<open>(t, X) \<in> ?f2\<close>
      with assm[THEN conjunct2] have \<open>(t, X \<union> Y) \<in> ?f2\<close>
        by simp (metis Diff_insert_absorb Un_Diff)
      thus \<open>(t, X \<union> Y) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    next
      assume \<open>(t, X) \<in> ?f3\<close>
      with assm[THEN conjunct2] have \<open>(t, X \<union> Y) \<in> ?f3\<close>
        by simp (metis F_T T_F T_nonTickFree_imp_decomp append1_eq_conv append_Nil event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.distinct_disc(2)
            is_processT5_S7' list.distinct(1) tickFree_Cons_iff tickFree_append_iff)
      thus \<open>(t, X \<union> Y) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    next
      assume \<open>(t, X) \<in> ?f4\<close>
      with assm[THEN conjunct2] have \<open>(t, X \<union> Y) \<in> ?f4\<close>
        by simp (metis append.assoc append_is_Nil_conv is_processT5)
      thus \<open>(t, X \<union> Y) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    next
      assume \<open>(t, X) \<in> ?f5\<close>
      with assm[THEN conjunct2] have \<open>(t, X \<union> Y) \<in> ?f5\<close>
        by simp (metis Diff_empty Diff_insert0 T_F Un_Diff not_Cons_self)
      thus \<open>(t, X \<union> Y) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    next
      assume \<open>(t, X) \<in> ?f6\<close>
      hence \<open>(t, X \<union> Y) \<in> ?f6\<close> by simp
      thus \<open>(t, X \<union> Y) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    next
      assume \<open>(t, X) \<in> ?f7\<close>
      hence \<open>(t, X \<union> Y) \<in> ?f7\<close> by simp
      thus \<open>(t, X \<union> Y) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    qed
  next
    fix t r X
    have * : \<open>(t @ [\<checkmark>(r)], {}) \<notin> ?f2 \<union> ?f3 \<union> ?f5\<close>
      by simp (metis T_imp_front_tickFree front_tickFree_Cons_iff front_tickFree_append_iff
          non_tickFree_tick tickFree_Cons_iff tickFree_Nil)
    assume \<open>(t @ [\<checkmark>(r)], {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close>
    with "*" have \<open>(t @ [\<checkmark>(r)], {}) \<in> ?f1 \<or> (t @ [\<checkmark>(r)], {}) \<in> ?f4 \<or>
                   (t @ [\<checkmark>(r)], {}) \<in> ?f6 \<or> (t @ [\<checkmark>(r)], {}) \<in> ?f7\<close> by fast
    thus \<open>(t, X - {\<checkmark>(r)}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close>
    proof (elim disjE)
      assume \<open>(t @ [\<checkmark>(r)], {}) \<in> ?f1\<close>
      hence \<open>(t, X - {\<checkmark>(r)}) \<in> ?f2\<close> by blast
      thus \<open>(t, X - {\<checkmark>(r)}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    next
      assume \<open>(t @ [\<checkmark>(r)], {}) \<in> ?f4\<close>
      then obtain t' u'
        where ** : \<open>t = t' @ u'\<close> \<open>t' \<in> \<T> P\<close> \<open>tF t'\<close> \<open>(u' @ [\<checkmark>(r)], {}) \<in> \<F> Q\<close> 
        by simp (metis butlast_append last_appendR snoc_eq_iff_butlast)
      hence \<open>(t, X - {\<checkmark>(r)}) \<in> (if u' = [] then ?f5 else ?f4)\<close>
        by simp (metis F_T process_charn self_append_conv2)
      thus \<open>(t, X - {\<checkmark>(r)}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by (meson UnCI)
    next
      assume \<open>(t @ [\<checkmark>(r)], {}) \<in> ?f6\<close>
      with is_processT9 have \<open>t \<in> \<D> P\<close> by fast
      thus \<open>(t, X - {\<checkmark>(r)}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    next
      assume \<open>(t @ [\<checkmark>(r)], {}) \<in> ?f7\<close>
      then obtain t' u'
        where ** : \<open>t @ [\<checkmark>(r)] = t' @ u'\<close> \<open>t' \<in> \<T> P\<close> \<open>tF t'\<close> \<open>u' \<in> \<D> Q\<close> by blast
      from "**"(1, 3, 4) obtain u'' where \<open>u' = u'' @ [\<checkmark>(r)]\<close> \<open>u'' @ [\<checkmark>(r)] \<in> \<D> Q\<close>
        by (cases u' rule: rev_cases) auto
      with "**"(1) is_processT9 have \<open>t = t' @ u'' \<and> u'' \<in> \<D> Q\<close> by force
      with "**"(2, 3) have \<open>(t, X - {\<checkmark>(r)}) \<in> ?f7\<close> by simp blast
      thus \<open>(t, X - {\<checkmark>(r)}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    qed
  next
    show \<open>t \<in> ?d1 \<union> ?d2 \<and> tF t \<and> ftF u \<Longrightarrow> t @ u \<in> ?d1 \<union> ?d2\<close> for t u
      apply (simp, elim conjE disjE exE)
      by (solves \<open>simp add: is_processT7\<close>)      
        (meson append.assoc is_processT7 tickFree_append_iff)
  next
    show \<open>t \<in> ?d1 \<union> ?d2 \<Longrightarrow> (t, X) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> for t X
      by blast
  next
    fix t r
    assume \<open>t @ [\<checkmark>(r)] \<in> ?d1 \<union> ?d2\<close>
    then consider \<open>t @ [\<checkmark>(r)] \<in> ?d1\<close> | \<open>t @ [\<checkmark>(r)] \<in> ?d2\<close> by blast
    thus \<open>t \<in> ?d1 \<union> ?d2\<close>
    proof cases
      assume \<open>t @ [\<checkmark>(r)] \<in> ?d1\<close>
      hence \<open>t \<in> ?d1\<close> by (fact is_processT9)
      thus \<open>t \<in> ?d1 \<union> ?d2\<close> by blast
    next
      assume \<open>t @ [\<checkmark>(r)] \<in> ?d2\<close>
      then obtain t' u'
        where ** : \<open>t @ [\<checkmark>(r)] = t' @ u'\<close> \<open>t' \<in> \<T> P\<close> \<open>tF t'\<close> \<open>u' \<in> \<D> Q\<close> by blast
      from "**"(1, 3, 4) obtain u'' where \<open>u' = u'' @ [\<checkmark>(r)]\<close> \<open>u'' @ [\<checkmark>(r)] \<in> \<D> Q\<close>
        by (cases u' rule: rev_cases) auto
      with "**"(1) is_processT9 have \<open>t = t' @ u'' \<and> u'' \<in> \<D> Q\<close> by force
      with "**"(2, 3) have \<open>t \<in> ?d2\<close> by simp blast
      thus \<open>t \<in> ?d1 \<union> ?d2\<close> by blast
    qed
  qed
qed



subsection \<open>Projections\<close>

lemma F_Interrupt :
  \<open>\<F> (P \<triangle> Q) = 
   {(t @ [\<checkmark>(r)], X) |t r X. t @ [\<checkmark>(r)] \<in> \<T> P} \<union>
   {(t, X - {\<checkmark>(r)}) |t r X. t @ [\<checkmark>(r)] \<in> \<T> P} \<union>
   {(t, X). (t, X) \<in> \<F> P \<and> tF t \<and> ([], X) \<in> \<F> Q} \<union>
   {(t @ u, X) |t u X. t \<in> \<T> P \<and> tF t \<and> (u, X) \<in> \<F> Q \<and> u \<noteq> []} \<union>
   {(t, X - {\<checkmark>(r)}) |t r X. t \<in> \<T> P \<and> tF t \<and> [\<checkmark>(r)] \<in> \<T> Q} \<union>
   {(t, X). t \<in> \<D> P} \<union>
   {(t @ u, X) |t u X. t \<in> \<T> P \<and> tF t \<and> u \<in> \<D> Q}\<close>
  by (simp add: Failures.rep_eq FAILURES_def Interrupt.rep_eq)

lemma D_Interrupt : 
  \<open>\<D> (P \<triangle> Q) = \<D> P \<union> {t @ u |t u. t \<in> \<T> P \<and> tF t \<and> u \<in> \<D> Q}\<close>
  by (simp add: Divergences.rep_eq DIVERGENCES_def Interrupt.rep_eq)

lemma T_Interrupt : 
  \<open>\<T> (P \<triangle> Q) = \<T> P \<union> {t @ u |t u. t \<in> \<T> P \<and> tF t \<and> u \<in> \<T> Q}\<close>
  apply (simp add: Traces.rep_eq TRACES_def F_Interrupt flip: Failures.rep_eq)
  apply (safe, simp_all add: is_processT8)
       apply (meson is_processT4_empty is_processT6)
      apply auto[2]
    apply (metis is_processT8)
   apply (metis is_processT4_empty nonTickFree_n_frontTickFree process_charn)
  by (metis append.right_neutral is_processT4_empty tickFree_Nil)

lemmas Interrupt_projs = F_Interrupt D_Interrupt T_Interrupt



subsection \<open>Monotony\<close>

lemma mono_Interrupt : \<open>P \<triangle> Q \<sqsubseteq> P' \<triangle> Q'\<close> if \<open>P \<sqsubseteq> P'\<close> and \<open>Q \<sqsubseteq> Q'\<close>
proof (unfold le_approx_def, intro conjI allI impI subsetI)
  show \<open>s \<in> \<D> (P' \<triangle> Q') \<Longrightarrow> s \<in> \<D> (P \<triangle> Q)\<close> for s
    using \<open>P \<sqsubseteq> P'\<close>[THEN le_approx1] \<open>Q \<sqsubseteq> Q'\<close>[THEN le_approx1]
      \<open>P \<sqsubseteq> P'\<close>[THEN le_approx2T] D_T by (simp add: D_Interrupt) blast
next
  show \<open>s \<notin> \<D> (P \<triangle> Q) \<Longrightarrow> \<R>\<^sub>a (P \<triangle> Q) s = \<R>\<^sub>a (P' \<triangle> Q') s\<close> for s
    apply (simp add: D_Interrupt Refusals_after_def F_Interrupt,
        intro subset_antisym subsetI; simp, elim disjE)
                apply (metis le_approx2T \<open>P \<sqsubseteq> P'\<close>)
               apply (metis is_processT9 le_approx2T \<open>P \<sqsubseteq> P'\<close>)
              apply (metis F_T append.right_neutral le_approx2 \<open>P \<sqsubseteq> P'\<close> \<open>Q \<sqsubseteq> Q'\<close>)
             apply (metis is_processT2 is_processT7 le_approx2T proc_ord2a \<open>P \<sqsubseteq> P'\<close> \<open>Q \<sqsubseteq> Q'\<close>)
            apply (metis append_Nil2 is_processT9 le_approx2T self_append_conv2 \<open>P \<sqsubseteq> P'\<close> \<open>Q \<sqsubseteq> Q'\<close>)
           apply metis
          apply (metis le_approx2T \<open>P \<sqsubseteq> P'\<close>)
         apply (metis le_approx_lemma_T subset_eq \<open>P \<sqsubseteq> P'\<close>)
        apply (metis is_processT8 le_approx2 \<open>P \<sqsubseteq> P'\<close> \<open>Q \<sqsubseteq> Q'\<close>)
       apply (metis is_processT2 is_processT7 le_approx2 le_approx2T \<open>P \<sqsubseteq> P'\<close> \<open>Q \<sqsubseteq> Q'\<close>) 
      apply (metis D_T le_approx2T \<open>P \<sqsubseteq> P'\<close> \<open>Q \<sqsubseteq> Q'\<close>)
     apply (metis in_mono le_approx1 \<open>P \<sqsubseteq> P'\<close>)
    by (metis le_approx1 le_approx2T process_charn subsetD \<open>P \<sqsubseteq> P'\<close> \<open>Q \<sqsubseteq> Q'\<close>)
next
  (* from \<open>P \<sqsubseteq> P'\<close>[THEN le_approx3] \<open>Q \<sqsubseteq> Q'\<close>[THEN le_approx3] *)
  show \<open>s \<in> min_elems (\<D> (P \<triangle> Q)) \<Longrightarrow> s \<in> \<T> (P' \<triangle> Q')\<close> for s
    apply (rule set_mp[of \<open>min_elems (\<D> P) \<union> {t1 @ t2| t1 t2. t1 \<in> \<T> P' \<and> tickFree t1 \<and> t2 \<in> min_elems (\<D> Q)}\<close>])
      (* apply (use \<open>P \<sqsubseteq> P'\<close>[THEN le_approx3] \<open>Q \<sqsubseteq> Q'\<close>[THEN le_approx3] in simp) *)
     apply (rule Un_least)
      apply (simp add: T_Interrupt le_approx3 le_supI1 \<open>P \<sqsubseteq> P'\<close>)
     apply (simp add: T_Interrupt subset_iff, metis le_approx_def subset_iff \<open>Q \<sqsubseteq> Q'\<close>)
    apply (simp add: min_elems_def D_Interrupt less_list_def)
      (* TODO: break this smt *)
    by (smt (verit, ccfv_threshold) D_imp_front_tickFree same_prefix_prefix Un_iff is_processT7 le_approx2T mem_Collect_eq same_append_eq that(1))
qed




subsection \<open>Properties\<close>

lemma Interrupt_STOP [simp] : \<open>P \<triangle> STOP = P\<close>
proof (subst Process_eq_spec, safe)
  show \<open>t \<in> \<D> (P \<triangle> STOP) \<Longrightarrow> t \<in> \<D> P\<close> for t
    by (simp add: D_Interrupt D_STOP)
next
  show \<open>t \<in> \<D> P \<Longrightarrow> t \<in> \<D> (P \<triangle> STOP)\<close> for t
    by (simp add: D_Interrupt D_STOP)
next
  show \<open>(t, X) \<in> \<F> (P \<triangle> STOP) \<Longrightarrow> (t, X) \<in> \<F> P\<close> for t X
    by (simp add: F_Interrupt STOP_projs)
      (meson is_processT6_TR is_processT8 tick_T_F)
next
  show \<open>(t, X) \<in> \<F> P \<Longrightarrow> (t, X) \<in> \<F> (P \<triangle> STOP)\<close> for t X
    by (simp add: F_Interrupt STOP_projs)
      (metis F_T T_nonTickFree_imp_decomp)
qed

lemma STOP_Interrupt [simp] : \<open>STOP \<triangle> P = P\<close>
proof (subst Process_eq_spec, safe)
  show \<open>t \<in> \<D> (STOP \<triangle> P) \<Longrightarrow> t \<in> \<D> P\<close> for t
    by (simp add: D_Interrupt STOP_projs)
next
  show \<open>t \<in> \<D> P \<Longrightarrow> t \<in> \<D> (STOP \<triangle> P)\<close> for t
    by (simp add: D_Interrupt STOP_projs)
next
  show \<open>(t, X) \<in> \<F> (STOP \<triangle> P) \<Longrightarrow> (t, X) \<in> \<F> P\<close> for t X
    by (simp add: F_Interrupt STOP_projs)
      (metis is_processT6_TR is_processT8 self_append_conv2)
next
  show \<open>(t, X) \<in> \<F> P \<Longrightarrow> (t, X) \<in> \<F> (STOP \<triangle> P)\<close> for t X
    by (auto simp add: F_Interrupt STOP_projs)
qed

lemma Interrupt_is_STOP_iff : \<open>P \<triangle> Q = STOP \<longleftrightarrow> P = STOP \<and> Q = STOP\<close>
  by (simp add: STOP_iff_T T_Interrupt set_eq_iff)
    (metis append_self_conv2 is_processT1_TR tickFree_Nil)


lemma Interrupt_BOT [simp] : \<open>P \<triangle> \<bottom> = \<bottom>\<close>
  and BOT_Interrupt [simp] : \<open>\<bottom> \<triangle> P = \<bottom>\<close>
  by (simp_all add: BOT_iff_Nil_D D_Interrupt D_BOT)

lemma Interrupt_is_BOT_iff : \<open>P \<triangle> Q = \<bottom> \<longleftrightarrow> P = \<bottom> \<or> Q = \<bottom>\<close>
  by (simp add: BOT_iff_Nil_D D_Interrupt)


lemma SKIP_Interrupt_is_SKIP_Det : \<open>SKIP r \<triangle> P = SKIP r \<box> P\<close>
proof (subst Process_eq_spec, safe)
  show \<open>t \<in> \<D> (SKIP r \<triangle> P) \<Longrightarrow> t \<in> \<D> (SKIP r \<box> P)\<close> for t
    by (auto simp add: D_Interrupt D_Det SKIP_projs)
next
  show \<open>t \<in> \<D> (SKIP r \<box> P) \<Longrightarrow> t \<in> \<D> (SKIP r \<triangle> P)\<close> for t
    by (auto simp add: D_Interrupt D_Det SKIP_projs intro: tickFree_Nil)
next
  show \<open>(t, X) \<in> \<F> (SKIP r \<triangle> P) \<Longrightarrow> (t, X) \<in> \<F> (SKIP r \<box> P)\<close> for t X
    by (cases t) (auto simp add: F_Interrupt SKIP_projs F_Det intro: is_processT8)
next
  show \<open>(t, X) \<in> \<F> (SKIP r \<box> P) \<Longrightarrow> (t, X) \<in> \<F> (SKIP r \<triangle> P)\<close> for t X
    by (cases t) (auto simp add: F_Interrupt SKIP_projs F_Det intro: tickFree_Nil)
qed



lemma Interrupt_assoc: \<open>P \<triangle> (Q \<triangle> R) = P \<triangle> Q \<triangle> R\<close> (is \<open>?lhs = ?rhs\<close>)
proof -
  have \<open>?lhs = ?rhs\<close> if non_BOT : \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close> \<open>R \<noteq> \<bottom>\<close>
  proof (subst Process_eq_spec_optimized, safe)
    fix s
    assume \<open>s \<in> \<D> ?lhs\<close>
    then consider \<open>s \<in> \<D> P\<close>
      | \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<T> P \<and> tickFree t1 \<and> t2 \<in> \<D> (Q \<triangle> R)\<close>
      by (simp add: D_Interrupt) blast
    thus \<open>s \<in> \<D> ?rhs\<close>
    proof cases
      show \<open>s \<in> \<D> P \<Longrightarrow> s \<in> \<D> ?rhs\<close> by (simp add: D_Interrupt)
    next
      assume \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<T> P \<and> tickFree t1 \<and> t2 \<in> \<D> (Q \<triangle> R)\<close>
      then obtain t1 t2 where * : \<open>s = t1 @ t2\<close> \<open>t1 \<in> \<T> P\<close>
        \<open>tickFree t1\<close> \<open>t2 \<in> \<D> (Q \<triangle> R)\<close> by blast
      from "*"(4) consider \<open>t2 \<in> \<D> Q\<close>
        | \<open>\<exists>u1 u2. t2 = u1 @ u2 \<and> u1 \<in> \<T> Q \<and> tickFree u1 \<and> u2 \<in> \<D> R\<close>
        by (simp add: D_Interrupt) blast
      thus \<open>s \<in> \<D> ?rhs\<close>
      proof cases
        from "*"(1, 2, 3) show \<open>t2 \<in> \<D> Q \<Longrightarrow> s \<in> \<D> ?rhs\<close> by (simp add: D_Interrupt) blast
      next
        show \<open>\<exists>u1 u2. t2 = u1 @ u2 \<and> u1 \<in> \<T> Q \<and> tickFree u1 \<and> u2 \<in> \<D> R \<Longrightarrow> s \<in> \<D> ?rhs\<close>
          by (simp add: "*"(1) D_Interrupt T_Interrupt)
            (metis "*"(2, 3) append_assoc tickFree_append_iff)
      qed
    qed
  next
    fix s
    assume \<open>s \<in> \<D> ?rhs\<close>
    then consider \<open>s \<in> \<D> (P \<triangle> Q)\<close>
      | \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<T> (P \<triangle> Q) \<and> tickFree t1 \<and> t2 \<in> \<D> R\<close>
      by (simp add: D_Interrupt) blast
    thus \<open>s \<in> \<D> ?lhs\<close>
    proof cases
      show \<open>s \<in> \<D> (P \<triangle> Q) \<Longrightarrow> s \<in> \<D> ?lhs\<close> by (simp add: D_Interrupt) blast
    next
      assume \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<T> (P \<triangle> Q) \<and> tickFree t1 \<and> t2 \<in> \<D> R\<close>
      then obtain t1 t2 where * : \<open>s = t1 @ t2\<close> \<open>t1 \<in> \<T> (P \<triangle> Q)\<close>
        \<open>tickFree t1\<close> \<open>t2 \<in> \<D> R\<close> by blast
      from "*"(2) consider \<open>t1 \<in> \<T> P\<close>
        | \<open>\<exists>u1 u2. t1 = u1 @ u2 \<and> u1 \<in> \<T> P \<and> tickFree u1 \<and> u2 \<in> \<T> Q\<close>
        by (simp add: T_Interrupt) blast
      thus \<open>s \<in> \<D> ?lhs\<close>
      proof cases
        show \<open>t1 \<in> \<T> P \<Longrightarrow> s \<in> \<D> ?lhs\<close>
          by (simp add: D_Interrupt "*"(1))
            (metis "*"(3, 4) Nil_elem_T append_Nil tickFree_Nil)
      next
        show \<open>\<exists>u1 u2. t1 = u1 @ u2 \<and> u1 \<in> \<T> P \<and> tickFree u1 \<and> u2 \<in> \<T> Q \<Longrightarrow> s \<in> \<D> ?lhs\<close>
          by (simp add: D_Interrupt "*"(1)) 
            (metis "*"(3, 4) append.assoc tickFree_append_iff)
      qed
    qed
  next
    fix s X
    assume same_div: \<open>\<D> ?lhs = \<D> ?rhs\<close>
    assume \<open>(s, X) \<in> \<F> ?lhs\<close>
    then consider \<open>s \<in> \<D> ?lhs\<close>
      | \<open>\<exists>t1 r. s = t1 @ [\<checkmark>(r)] \<and> t1 @ [\<checkmark>(r)] \<in> \<T> P\<close>
      | \<open>\<exists>r. s @ [\<checkmark>(r)] \<in> \<T> P \<and> \<checkmark>(r) \<notin> X\<close>
      | \<open>(s, X) \<in> \<F> P \<and> tickFree s \<and> ([], X) \<in> \<F> (Q \<triangle> R)\<close>
      | \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<T> P \<and> tickFree t1 \<and> (t2, X) \<in> \<F> (Q \<triangle> R) \<and> t2 \<noteq> []\<close>
      | \<open>\<exists>r. s \<in> \<T> P \<and> tickFree s \<and> [\<checkmark>(r)] \<in> \<T> (Q \<triangle> R) \<and> \<checkmark>(r) \<notin> X\<close>
      by (subst (asm) F_Interrupt, simp add: D_Interrupt) blast
    thus \<open>(s, X) \<in> \<F> ?rhs\<close>
    proof cases
      from same_div D_F show \<open>s \<in> \<D> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> by blast
    next
      show \<open>\<exists>t1 r. s = t1 @ [\<checkmark>(r)] \<and> t1 @ [\<checkmark>(r)] \<in> \<T> P \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
        by (auto simp add: F_Interrupt T_Interrupt)
    next
      show \<open>\<exists>r. s @ [\<checkmark>(r)] \<in> \<T> P \<and> \<checkmark>(r) \<notin> X \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
        by (simp add: F_Interrupt T_Interrupt) (metis Diff_insert_absorb)
    next
      assume assm : \<open>(s, X) \<in> \<F> P \<and> tickFree s \<and> ([], X) \<in> \<F> (Q \<triangle> R)\<close>
      with non_BOT(2, 3) consider r where \<open>[\<checkmark>(r)] \<in> \<T> Q \<and> \<checkmark>(r) \<notin> X\<close>
        | \<open>([], X) \<in> \<F> Q \<and> ([], X) \<in> \<F> R\<close>
        | r where \<open>[] \<in> \<T> Q \<and> [\<checkmark>(r)] \<in> \<T> R \<and> \<checkmark>(r) \<notin> X\<close>
        by (simp add: F_Interrupt BOT_iff_Nil_D) blast
      thus \<open>(s, X) \<in> \<F> ?rhs\<close>
      proof cases
        show \<open>[\<checkmark>(r)] \<in> \<T> Q \<and> \<checkmark>(r) \<notin> X \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for r
          by (simp add: F_Interrupt T_Interrupt) (metis Diff_insert_absorb F_T assm)
      next
        show \<open>([], X) \<in> \<F> Q \<and> ([], X) \<in> \<F> R \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
          by (simp add: F_Interrupt assm)
      next
        show \<open>[] \<in> \<T> Q \<and> [\<checkmark>(r)] \<in> \<T> R \<and> \<checkmark>(r) \<notin> X \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for r
          by (simp add: F_Interrupt T_Interrupt) (metis Diff_insert_absorb F_T assm)
      qed
    next
      assume \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<T> P \<and> tickFree t1 \<and>
                      (t2, X) \<in> \<F> (Q \<triangle> R) \<and> t2 \<noteq> []\<close>
      then obtain t1 t2 where * : \<open>s = t1 @ t2\<close> \<open>t1 \<in> \<T> P\<close> \<open>tickFree t1\<close> 
        \<open>(t2, X) \<in> \<F> (Q \<triangle> R)\<close> \<open>t2 \<noteq> []\<close> by blast
      from "*"(4) consider \<open>t2 \<in> \<D> (Q \<triangle> R)\<close>
        | u1 r where \<open>t2 = u1 @ [\<checkmark>(r)]\<close> \<open>u1 @ [\<checkmark>(r)] \<in> \<T> Q\<close>
        | r where \<open>t2 @ [\<checkmark>(r)] \<in> \<T> Q\<close> \<open>\<checkmark>(r) \<notin> X\<close>
        | \<open>(t2, X) \<in> \<F> Q\<close> \<open>tickFree t2\<close> \<open>([], X) \<in> \<F> R\<close>
        | u1 u2 where \<open>t2 = u1 @ u2\<close> \<open>u1 \<in> \<T> Q\<close> \<open>tickFree u1\<close> \<open>(u2, X) \<in> \<F> R\<close> \<open>u2 \<noteq> []\<close>
        | r where \<open>t2 \<in> \<T> Q\<close> \<open>tickFree t2\<close> \<open>[\<checkmark>(r)] \<in> \<T> R\<close> \<open>\<checkmark>(r) \<notin> X\<close>
        by (simp add: F_Interrupt D_Interrupt) blast
      thus \<open>(s, X) \<in> \<F> ?rhs\<close>
      proof cases
        assume \<open>t2 \<in> \<D> (Q \<triangle> R)\<close>
        with "*"(1, 2, 3) have \<open>s \<in> \<D> ?lhs\<close> by (simp add: D_Interrupt) blast
        with same_div D_F show \<open>(s, X) \<in> \<F> ?rhs\<close> by blast
      next
        from "*"(1, 2, 3) show \<open>t2 = u1 @ [\<checkmark>(r)] \<Longrightarrow> u1 @ [\<checkmark>(r)] \<in> \<T> Q \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for u1 r
          by (auto simp add: F_Interrupt T_Interrupt)
      next
        from "*"(1, 2, 3) show \<open>t2 @ [\<checkmark>(r)] \<in> \<T> Q \<Longrightarrow> \<checkmark>(r) \<notin> X \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for r
          by (simp add: F_Interrupt T_Interrupt) (metis Diff_insert_absorb)
      next
        from "*"(1) show \<open>(t2, X) \<in> \<F> Q \<Longrightarrow> tickFree t2 \<Longrightarrow> ([], X) \<in> \<F> R \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
          by (simp add: F_Interrupt T_Interrupt) (metis "*"(2, 3, 5))
      next
        from "*"(1, 2, 3) show \<open>t2 = u1 @ u2 \<Longrightarrow> u1 \<in> \<T> Q \<Longrightarrow> tickFree u1 \<Longrightarrow>
                                (u2, X) \<in> \<F> R \<Longrightarrow> u2 \<noteq> [] \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for u1 u2
          by (simp add: F_Interrupt T_Interrupt)
            (metis (mono_tags, lifting) append_assoc tickFree_append_iff)
      next
        from "*"(1, 2, 3) show \<open>t2 \<in> \<T> Q \<Longrightarrow> tickFree t2 \<Longrightarrow>
          [\<checkmark>(r)] \<in> \<T> R \<Longrightarrow> \<checkmark>(r) \<notin> X \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for r
          by (simp add: F_Interrupt T_Interrupt) (metis Diff_insert_absorb)
      qed
    next
      show \<open>\<exists>r. s \<in> \<T> P \<and> tickFree s \<and> [\<checkmark>(r)] \<in> \<T> (Q \<triangle> R) \<and> \<checkmark>(r) \<notin> X \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
        by (simp add: F_Interrupt T_Interrupt)
          (metis Diff_insert_absorb append_eq_Cons_conv non_tickFree_tick tickFree_append_iff)
    qed
  next
    fix s X
    assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
    assume \<open>(s, X) \<in> \<F> ?rhs\<close>
    then consider \<open>s \<in> \<D> ?rhs\<close>
      | \<open>\<exists>t1 r. s = t1 @ [\<checkmark>(r)] \<and> t1 @ [\<checkmark>(r)] \<in> \<T> (P \<triangle> Q)\<close>
      | r where \<open>s @ [\<checkmark>(r)] \<in> \<T> (P \<triangle> Q)\<close> \<open>\<checkmark>(r) \<notin> X\<close>
      | \<open>(s, X) \<in> \<F> (P \<triangle> Q) \<and> tickFree s \<and> ([], X) \<in> \<F> R\<close>
      | \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<T> (P \<triangle> Q) \<and> tickFree t1 \<and> (t2, X) \<in> \<F> R \<and> t2 \<noteq> []\<close>
      | \<open>\<exists>r. s \<in> \<T> (P \<triangle> Q) \<and> tickFree s \<and> [\<checkmark>(r)] \<in> \<T> R \<and> \<checkmark>(r) \<notin> X\<close>
      by (subst (asm) F_Interrupt, simp add: D_Interrupt) blast 
    thus \<open>(s, X) \<in> \<F> ?lhs\<close>
    proof cases
      from same_div D_F show \<open>s \<in> \<D> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> by blast
    next
      show \<open>\<exists>t1 r. s = t1 @ [\<checkmark>(r)] \<and> t1 @ [\<checkmark>(r)] \<in> \<T> (P \<triangle> Q) \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
        by (simp add: F_Interrupt T_Interrupt)
          (metis last_append self_append_conv snoc_eq_iff_butlast)
    next
      fix r assume \<open>s @ [\<checkmark>(r)] \<in> \<T> (P \<triangle> Q)\<close> \<open>\<checkmark>(r) \<notin> X\<close>
      from this(1) consider \<open>s @ [\<checkmark>(r)] \<in> \<T> P\<close>
        | t1 t2 where \<open>s @ [\<checkmark>(r)] = t1 @ t2\<close> \<open>t1 \<in> \<T> P\<close> \<open>tickFree t1\<close> \<open>t2 \<in> \<T> Q\<close>
        by (simp add: T_Interrupt) blast
      thus \<open>(s, X) \<in> \<F> ?lhs\<close>
      proof cases
        show \<open>s @ [\<checkmark>(r)] \<in> \<T> P \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
          by (simp add: F_Interrupt) (metis Diff_insert_absorb \<open>\<checkmark>(r) \<notin> X\<close>)
      next
        show \<open>s @ [\<checkmark>(r)] = t1 @ t2 \<Longrightarrow> t1 \<in> \<T> P \<Longrightarrow> tickFree t1 \<Longrightarrow> t2 \<in> \<T> Q \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for t1 t2

(* TODO: break the smts *)
          apply (simp add: F_Interrupt T_Interrupt, safe, simp_all)
             apply (smt (z3) Diff_insert_absorb T_nonTickFree_imp_decomp \<open>\<checkmark>(r) \<notin> X\<close> append.assoc append1_eq_conv append_self_conv2 non_tickFree_tick tickFree_append_iff) 
            apply (metis \<open>s @ [\<checkmark>(r)] \<in> \<T> (P \<triangle> Q)\<close> append_T_imp_tickFree list.discI)
           apply (smt (z3) Diff_insert_absorb T_nonTickFree_imp_decomp \<open>\<checkmark>(r) \<notin> X\<close> append1_eq_conv append_assoc is_processT6_TR non_tickFree_tick tickFree_append_iff)
          apply (smt (z3) Diff_insert_absorb T_nonTickFree_imp_decomp \<open>\<checkmark>(r) \<notin> X\<close> append1_eq_conv append_assoc non_tickFree_tick self_append_conv2 tickFree_append_iff)
          done
      qed
    next
      assume assm : \<open>(s, X) \<in> \<F> (P \<triangle> Q) \<and> tickFree s \<and> ([], X) \<in> \<F> R\<close>
      from assm[THEN conjunct1] consider \<open>s \<in> \<D> (P \<triangle> Q)\<close>
        | t1 r where \<open>s = t1 @ [\<checkmark>(r)]\<close> \<open>t1 @ [\<checkmark>(r)] \<in> \<T> P\<close>
        | r where \<open>s @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>\<checkmark>(r) \<notin> X\<close>
        | \<open>(s, X) \<in> \<F> P\<close> \<open>tickFree s\<close> \<open>([], X) \<in> \<F> Q\<close>
        | t1 t2 where \<open>s = t1 @ t2\<close> \<open>t1 \<in> \<T> P\<close> \<open>tickFree t1\<close> \<open>(t2, X) \<in> \<F> Q\<close> \<open>t2 \<noteq> []\<close>
        | r where \<open>s \<in> \<T> P\<close> \<open>tickFree s\<close> \<open>[\<checkmark>(r)] \<in> \<T> Q\<close> \<open>\<checkmark>(r) \<notin> X\<close>
        by (simp add: F_Interrupt D_Interrupt) blast
      thus \<open>(s, X) \<in> \<F> ?lhs\<close>
      proof cases
        assume \<open>s \<in> \<D> (P \<triangle> Q)\<close>
        hence \<open>s \<in> \<D> ?rhs\<close> by (simp add: D_Interrupt)
        with same_div D_F show \<open>(s, X) \<in> \<F> ?lhs\<close> by blast
      next
        show \<open>s = t1 @ [\<checkmark>(r)] \<Longrightarrow> t1 @ [\<checkmark>(r)] \<in> \<T> P \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for t1 r
          by (simp add: F_Interrupt)
      next
        show \<open>s @ [\<checkmark>(r)] \<in> \<T> P \<Longrightarrow> \<checkmark>(r) \<notin> X \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for r
          by (simp add: F_Interrupt) (metis Diff_insert_absorb)
      next
        show \<open>(s, X) \<in> \<F> P \<Longrightarrow> tickFree s \<Longrightarrow> ([], X) \<in> \<F> Q \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
          by (simp add: F_Interrupt assm[THEN conjunct2])
      next
        show \<open>s = t1 @ t2 \<Longrightarrow> t1 \<in> \<T> P \<Longrightarrow> tickFree t1 \<Longrightarrow> (t2, X) \<in> \<F> Q \<Longrightarrow>
              t2 \<noteq> [] \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for t1 t2
          by (simp add: F_Interrupt) (metis assm[THEN conjunct2] tickFree_append_iff)
      next
        show \<open>s \<in> \<T> P \<Longrightarrow> tickFree s \<Longrightarrow> [\<checkmark>(r)] \<in> \<T> Q \<Longrightarrow> \<checkmark>(r) \<notin> X \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for r
          by (simp add: F_Interrupt T_Interrupt) (metis Diff_insert_absorb)
      qed
    next
      assume \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<T> (P \<triangle> Q) \<and> 
                      tickFree t1 \<and> (t2, X) \<in> \<F> R \<and> t2 \<noteq> []\<close>
      then obtain t1 t2 where * : \<open>s = t1 @ t2\<close> \<open>t1 \<in> \<T> (P \<triangle> Q)\<close>
        \<open>tickFree t1\<close> \<open>(t2, X) \<in> \<F> R\<close> \<open>t2 \<noteq> []\<close> by blast
      from "*"(2) consider \<open>t1 \<in> \<T> P\<close>
        | \<open>\<exists>u1 u2. t1 = u1 @ u2 \<and> u1 \<in> \<T> P \<and> tickFree u1 \<and> u2 \<in> \<T> Q\<close>
        by (simp add: T_Interrupt) blast
      thus \<open>(s, X) \<in> \<F> ?lhs\<close>
      proof cases
        from "*"(1, 3, 4, 5) show \<open>t1 \<in> \<T> P \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
          by (simp add: F_Interrupt T_Interrupt)
            (metis Nil_elem_T append_Nil tickFree_Nil)
      next
        from "*"(1, 3, 4, 5) show \<open>\<exists>u1 u2. t1 = u1 @ u2 \<and> u1 \<in> \<T> P \<and>
                                           tickFree u1 \<and> u2 \<in> \<T> Q \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
          by (elim exE, simp add: F_Interrupt) (metis append_is_Nil_conv)
      qed
    next
      show \<open>\<exists>r. s \<in> \<T> (P \<triangle> Q) \<and> tickFree s \<and> [\<checkmark>(r)] \<in> \<T> R \<and> \<checkmark>(r) \<notin> X \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
        by (simp add: F_Interrupt T_Interrupt)
          (metis Diff_insert_absorb Nil_elem_T append.right_neutral
            append_Nil tickFree_append_iff)
    qed
  qed

  thus \<open>?lhs = ?rhs\<close>
    by (cases \<open>P = \<bottom>\<close>; cases \<open>Q = \<bottom>\<close>; cases \<open>R = \<bottom>\<close>) simp_all
qed



subsection \<open>Continuity\<close>

context begin

private lemma chain_Interrupt_left: \<open>chain Y \<Longrightarrow> chain (\<lambda>i. Y i \<triangle> Q)\<close>
  by (simp add: chain_def mono_Interrupt)

private lemma chain_Interrupt_right: \<open>chain Y \<Longrightarrow> chain (\<lambda>i. P \<triangle> Y i)\<close>
  by (simp add: chain_def mono_Interrupt)  


private lemma cont_left_prem_Interrupt : \<open>(\<Squnion> i. Y i) \<triangle> Q = (\<Squnion> i. Y i  \<triangle> Q)\<close>
  (is \<open>?lhs = ?rhs\<close>) if chain : \<open>chain Y\<close>
proof (subst Process_eq_spec_optimized, safe)
  show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close> for s
    by (simp add: limproc_is_thelub chain chain_Interrupt_left
        D_Interrupt T_LUB D_LUB) blast
next
  fix s
  define S
    where \<open>S i \<equiv> {t1. s = t1 \<and> t1 \<in> \<D> (Y i)} \<union>
                  {t1. \<exists>t2. s = t1 @ t2 \<and> t1 \<in> \<T> (Y i) \<and> tickFree t1 \<and> t2 \<in> \<D> Q}\<close> for i
  assume \<open>s \<in> \<D> ?rhs\<close>
  hence \<open>s \<in> \<D> (Y i \<triangle> Q)\<close> for i
    by (simp add: limproc_is_thelub D_LUB chain_Interrupt_left chain)
  hence \<open>S i \<noteq> {}\<close> for i by (simp add: S_def D_Interrupt) blast
  moreover have \<open>finite (S 0)\<close>
    unfolding S_def by (prove_finite_subset_of_prefixes s)
  moreover have \<open>S (Suc i) \<subseteq> S i\<close> for i
    unfolding S_def apply (intro allI Un_mono subsetI; simp)
    by (metis in_mono le_approx1 po_class.chainE chain)
      (metis le_approx_lemma_T po_class.chain_def subset_eq chain)
  ultimately have \<open>(\<Inter>i. S i) \<noteq> {}\<close>
    by (rule Inter_nonempty_finite_chained_sets)
  then obtain t1 where * : \<open>\<forall>i. t1 \<in> S i\<close>
    by (meson INT_iff ex_in_conv iso_tuple_UNIV_I)
  show \<open>s \<in> \<D> ?lhs\<close>
  proof (cases \<open>\<forall>i. s \<in> \<D> (Y i)\<close>)
    case True
    thus \<open>s \<in> \<D> ?lhs\<close> by (simp add: D_Interrupt limproc_is_thelub D_LUB chain)
  next
    case False
    with "*" obtain j t2 where ** : \<open>s = t1 @ t2\<close> \<open>t1 \<in> \<T> (Y j)\<close> \<open> tickFree t1\<close> \<open>t2 \<in> \<D> Q\<close>
      by (simp add: S_def) blast
    from "*" D_T have \<open>\<forall>i. t1 \<in> \<T> (Y i)\<close> by (simp add: S_def) blast
    with "**"(1, 3, 4) show \<open>s \<in> \<D> ?lhs\<close>
      by (simp add: D_Interrupt limproc_is_thelub T_LUB chain) blast
  qed
next
  show \<open>(s, X) \<in> \<F> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for s X
    by (simp add: limproc_is_thelub chain chain_Interrupt_left
        F_Interrupt F_LUB T_LUB D_LUB, safe; simp; metis)
next
  assume same_div : \<open>\<D> ((\<Squnion>i. Y i) \<triangle> Q) = \<D> (\<Squnion>i. Y i \<triangle> Q)\<close>
  fix s X assume \<open>(s, X) \<in> \<F> (\<Squnion>i. Y i \<triangle> Q)\<close>
  show \<open>(s, X) \<in> \<F> ((\<Squnion>i. Y i) \<triangle> Q)\<close>
  proof (cases \<open>s \<in> \<D> (\<Squnion>i. Y i \<triangle> Q)\<close>)
    show \<open>s \<in> \<D> (\<Squnion>i. Y i \<triangle> Q) \<Longrightarrow> (s, X) \<in> \<F> ((\<Squnion>i. Y i) \<triangle> Q)\<close>
      by (simp add: is_processT8 same_div)
  next
    assume \<open>s \<notin> \<D> (\<Squnion>i. Y i \<triangle> Q)\<close>
    then obtain j where \<open>s \<notin> \<D> (Y j \<triangle> Q)\<close>
      by (auto simp add: limproc_is_thelub chain_Interrupt_left \<open>chain Y\<close> D_LUB)
    moreover from \<open>(s, X) \<in> \<F> (\<Squnion>i. Y i \<triangle> Q)\<close> have \<open>(s, X) \<in> \<F> (Y j \<triangle> Q)\<close>
      by (simp add: limproc_is_thelub chain_Interrupt_left \<open>chain Y\<close> F_LUB)
    ultimately show \<open>(s, X) \<in> \<F> ((\<Squnion>i. Y i) \<triangle> Q)\<close>
      by (fact le_approx2[OF mono_Interrupt[OF is_ub_thelub[OF \<open>chain Y\<close>] below_refl], THEN iffD2])
  qed
qed



private lemma cont_right_prem_Interrupt : \<open>S \<triangle> (\<Squnion>i. Y i) = (\<Squnion>i. S \<triangle> Y i)\<close> if \<open>chain Y\<close>
proof (subst Process_eq_spec_optimized, safe)
  show \<open>s \<in> \<D> (S \<triangle> (\<Squnion>i. Y i)) \<Longrightarrow> s \<in> \<D> (\<Squnion>i. S \<triangle> Y i)\<close> for s
    by (auto simp add: D_Interrupt limproc_is_thelub \<open>chain Y\<close> chain_Interrupt_right D_LUB)
next
  fix s assume \<open>s \<in> \<D> (\<Squnion>i. S \<triangle> Y i)\<close>
  show \<open>s \<in> \<D> (S \<triangle> (\<Squnion>i. Y i))\<close>
  proof (cases \<open>s \<in> \<D> S\<close>)
    show \<open>s \<in> \<D> S \<Longrightarrow> s \<in> \<D> (S \<triangle> (\<Squnion>i. Y i))\<close> by (simp add: D_Interrupt)
  next
    assume \<open>s \<notin> \<D> S\<close>
    thm D_Interrupt
    define T where \<open>T i \<equiv> {t1. \<exists>t2 r. s = t1 @ t2 \<and> t1 \<in> \<T> S \<and> tickFree t1 \<and> t2 \<in> \<D> (Y i)}\<close> for i
    from \<open>s \<notin> \<D> S\<close> \<open>s \<in> \<D> (\<Squnion>i. S \<triangle> Y i)\<close> have \<open>T i \<noteq> {}\<close> for i
      by (simp add: T_def limproc_is_thelub chain_Interrupt_right \<open>chain Y\<close> D_LUB D_Interrupt) blast
    moreover have \<open>finite (T 0)\<close>
      unfolding T_def by (prove_finite_subset_of_prefixes s)
    moreover have \<open>T (Suc i) \<subseteq> T i\<close> for i
      unfolding T_def apply (intro allI Un_mono subsetI; simp)
      by (metis le_approx1 po_class.chainE subset_iff \<open>chain Y\<close>)
    ultimately have \<open>(\<Inter>i. T i) \<noteq> {}\<close> by (rule Inter_nonempty_finite_chained_sets)
    then obtain t1 where \<open>\<forall>i. t1 \<in> T i\<close> by auto
    then obtain t2 where * : \<open>s = t1 @ t2\<close> \<open>t1 \<in> \<T> S\<close> \<open>tickFree t1\<close> \<open>\<forall>i. t2 \<in> \<D> (Y i)\<close>
      by (simp add: T_def) blast
    thus \<open>s \<in> \<D> (S \<triangle> (\<Squnion>i. Y i))\<close>
      by (simp add: D_Interrupt limproc_is_thelub \<open>chain Y\<close> D_LUB) blast
  qed
next
  show \<open>(s, X) \<in> \<F> (S \<triangle> (\<Squnion>i. Y i)) \<Longrightarrow> (s, X) \<in> \<F> (\<Squnion>i. S \<triangle> Y i)\<close> for s X
    by (simp add: F_Interrupt limproc_is_thelub \<open>chain Y\<close> chain_Interrupt_right F_LUB T_LUB D_LUB)
      (elim disjE exE conjE; metis)
next
  assume same_div : \<open>\<D> (S \<triangle> (\<Squnion>i. Y i)) = \<D> (\<Squnion>i. S \<triangle> Y i)\<close>
  fix s X assume \<open>(s, X) \<in> \<F> (\<Squnion>i. S \<triangle> Y i)\<close>
  show \<open>(s, X) \<in> \<F> (S \<triangle> (\<Squnion>i. Y i))\<close>
  proof (cases \<open>s \<in> \<D> (\<Squnion>i. S \<triangle> Y i)\<close>)
    show \<open>s \<in> \<D> (\<Squnion>i. S \<triangle> Y i) \<Longrightarrow> (s, X) \<in> \<F> (S \<triangle> (\<Squnion>i. Y i))\<close>
      by (simp add: is_processT8 same_div)
  next
    assume \<open>s \<notin> \<D> (\<Squnion>i. S \<triangle> Y i)\<close>
    then obtain j where \<open>s \<notin> \<D> (S \<triangle> Y j)\<close>
      by (auto simp add: limproc_is_thelub chain_Interrupt_right \<open>chain Y\<close> D_LUB)
    moreover from \<open>(s, X) \<in> \<F> (\<Squnion>i. S \<triangle> Y i)\<close> have \<open>(s, X) \<in> \<F> (S \<triangle> Y j)\<close>
      by (simp add: limproc_is_thelub chain_Interrupt_right \<open>chain Y\<close> F_LUB)
    ultimately show \<open>(s, X) \<in> \<F> (S \<triangle> (\<Squnion>i. Y i))\<close>
      by (fact le_approx2[OF mono_Interrupt[OF below_refl is_ub_thelub[OF \<open>chain Y\<close>]], THEN iffD2])
  qed
qed



lemma Interrupt_cont [simp] :
  \<open>cont (\<lambda>x. f x \<triangle> g x)\<close> if \<open>cont f\<close> and \<open>cont g\<close>
proof (rule cont_apply[where f = \<open>\<lambda>x y. f x \<triangle> y\<close>])
  show \<open>cont g\<close> by (fact \<open>cont g\<close>)
next
  show \<open>cont ((\<triangle>) (f x))\<close> for x
  proof (rule contI2)
    show \<open>monofun ((\<triangle>) (f x))\<close> by (simp add: mono_Interrupt monofunI)
  next
    show \<open>chain Y \<Longrightarrow> f x \<triangle> (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. f x \<triangle> Y i)\<close> for Y
      by (simp add: cont_right_prem_Interrupt)
  qed
next
  show \<open>cont (\<lambda>x. f x \<triangle> y)\<close> for y
  proof (rule contI2)
    show \<open>monofun (\<lambda>x. f x \<triangle> y)\<close> by (simp add: cont2monofunE mono_Interrupt monofunI \<open>cont f\<close>)
  next
    show \<open>chain Y \<Longrightarrow> f (\<Squnion>i. Y i) \<triangle> y \<sqsubseteq> (\<Squnion>i. f (Y i) \<triangle> y)\<close> for Y
      by (simp add: ch2ch_cont cont2contlubE cont_left_prem_Interrupt \<open>cont f\<close>)
  qed
qed


end

(*<*)
end
  (*>*)
