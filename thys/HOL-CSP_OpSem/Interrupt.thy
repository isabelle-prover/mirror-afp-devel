(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : HOL-CSP_OpSem - Operational semantics for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Burkhart Wolff
 *
 * This file       : The Interrupt operator
 *
 * Copyright (c) 2023 Université Paris-Saclay, France
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


theory  Interrupt
  imports "HOL-CSPM.CSPM"
begin


(*<*)
hide_const R
text \<open>We need to hide this because we want to be allowed to use the letter R in our lemmas.
      We can still access this notion via the notation \<^term>\<open>\<R> P\<close>.
      In further versions of \<^theory>\<open>HOL-CSP.Process\<close>, R will be renamed in Refusals 
      and we will remove this paragraph.\<close>
(*>*)

subsection \<open>Definition\<close>

text \<open>We want to add the binary operator of interruption of \<^term>\<open>P\<close> by \<^term>\<open>Q\<close>: 
      it behaves like \<^term>\<open>P\<close> except that at any time \<^term>\<open>Q\<close> can take over.\<close>

text \<open>The definition provided by Roscoe \<^cite>\<open>\<open>p.239\<close> in "Roscoe2010UnderstandingCS"\<close> does
      not respect the invariant \<^const>\<open>is_process\<close>: it seems like \<^const>\<open>tick\<close> is not handled.\<close>

text \<open>We propose here our corrected version.\<close>

lift_definition Interrupt :: \<open>['\<alpha> process, '\<alpha> process] \<Rightarrow> '\<alpha> process\<close> (infixl \<open>\<triangle>\<close> 75)
  is \<open>\<lambda>P Q. 
  ({(t1 @ [tick], X)| t1 X. t1 @ [tick] \<in> \<T> P} \<union>
   {(t1, X - {tick})| t1 X. t1 @ [tick] \<in> \<T> P} \<union>
   {(t1, X) \<in> \<F> P. tickFree t1 \<and> ([], X) \<in> \<F> Q} \<union>
   {(t1 @ t2, X)| t1 t2 X. t1 \<in> \<T> P \<and> tickFree t1 \<and> (t2, X) \<in> \<F> Q \<and> t2 \<noteq> []} \<union>
   {(t1, X - {tick})| t1 X. t1 \<in> \<T> P \<and> tickFree t1 \<and> [tick] \<in> \<T> Q} \<union>
   {(t1, X). t1 \<in> \<D> P} \<union> 
   {(t1 @ t2, X)| t1 t2 X. t1 \<in> \<T> P \<and> tickFree t1 \<and> t2 \<in> \<D> Q},
   \<D> P \<union> {t1 @ t2| t1 t2. t1 \<in> \<T> P \<and> tickFree t1 \<and> t2 \<in> \<D> Q})\<close>
proof -
  show \<open>?thesis P Q\<close> 
  (is \<open>is_process (?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7, ?d1 \<union> ?d2)\<close>) for P Q
    unfolding is_process_def FAILURES_def DIVERGENCES_def fst_conv snd_conv
  proof (intro conjI allI impI)
    have \<open>([], {}) \<in> ?f3\<close> by (simp add: is_processT1)
    thus \<open>([], {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by fast
  next
    show \<open>(s, X) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7 \<Longrightarrow> front_tickFree s\<close> for s X
      by (simp add: is_processT2 D_imp_front_tickFree front_tickFree_append)
         (meson front_tickFree_append front_tickFree_dw_closed is_processT2_TR process_charn)
  next
    fix s t
    show \<open>(s @ t, {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7 \<Longrightarrow>
              (s, {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close>
    proof (induct t rule: rev_induct)
      show \<open>(s @ [], {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7 \<Longrightarrow>
                 (s, {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by simp
    next
      fix a t
      assume assm : \<open>(s @ t @ [a], {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close>
         and  hyp : \<open>(s @ t, {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7 \<Longrightarrow>
                         (s, {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close>
      from assm have \<open>(s @ t @ [a], {}) \<in> ?f1 \<or> (s @ t @ [a], {}) \<in> ?f2 \<or>
        (s @ t @ [a], {}) \<in> ?f3 \<or> (s @ t @ [a], {}) \<in> ?f4 \<or> (s @ t @ [a], {}) \<in> ?f5 \<or> 
        (s @ t @ [a], {}) \<in> ?f6 \<or> (s @ t @ [a], {}) \<in> ?f7\<close> by fast
      thus \<open>(s, {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close>
      proof (elim disjE)
        assume \<open>(s @ t @ [a], {}) \<in> ?f1\<close>
        hence \<open>(s, {}) \<in> ?f3\<close>
          by simp (meson NF_NT append_T_imp_tickFree is_processT snoc_eq_iff_butlast) 
        thus \<open>(s, {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
      next
        assume \<open>(s @ t @ [a], {}) \<in> ?f2\<close>
        hence \<open>(s, {}) \<in> ?f3\<close>
          by simp (metis NF_NT Nil_is_append_conv append_T_imp_tickFree is_processT list.discI)
        thus \<open>(s, {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
      next
        assume \<open>(s @ t @ [a], {}) \<in> ?f3\<close>
        with is_processT3 have \<open>(s, {}) \<in> ?f3\<close> by simp blast
        thus \<open>(s, {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
      next
        assume \<open>(s @ t @ [a], {}) \<in> ?f4\<close>
        then obtain t1 t2 where * : \<open>s @ t = t1 @ t2\<close> \<open>t1 \<in> \<T> P\<close>
                                    \<open>tickFree t1\<close> \<open>(t2 @ [a], {}) \<in> \<F> Q\<close>
          by simp (metis butlast_append last_appendR snoc_eq_iff_butlast)
        show \<open>(s, {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close>
        proof (cases \<open>t2 = []\<close>)
          assume \<open>t2 = []\<close>
          with "*"(1, 2, 3) have \<open>(s, {}) \<in> ?f3\<close>
            by simp (metis T_F process_charn tickFree_append)
          thus \<open>(s, {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
        next
          assume \<open>t2 \<noteq> []\<close>
          with "*" is_processT3 have \<open>(s @ t, {}) \<in> ?f4\<close> by simp blast
          thus \<open>(s, {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by (intro hyp) blast
        qed
      next
        assume \<open>(s @ t @ [a], {}) \<in> ?f5\<close>
        hence \<open>(s, {}) \<in> ?f3\<close> by simp (metis T_F process_charn)
        thus \<open>(s, {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
      next
        assume \<open>(s @ t @ [a], {}) \<in> ?f6\<close>
        hence \<open>(s, {}) \<in> ?f3\<close>
          by simp (meson front_tickFree_mono is_processT snoc_eq_iff_butlast)
        thus \<open>(s, {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
      next
        assume \<open>(s @ t @ [a], {}) \<in> ?f7\<close>
        then obtain t1 t2 where * : \<open>s @ t @ [a] = t1 @ t2\<close> \<open>t1 \<in> \<T> P\<close>
                                    \<open>tickFree t1\<close> \<open>t2 \<in> \<D> Q\<close> by blast
        hence \<open>(s @ t, {}) \<in> (if length t2 \<le> 1 then ?f3 else ?f4)\<close>
          apply (cases t2 rule: rev_cases; simp)
          by (metis T_F append_assoc process_charn tickFree_append)
             (metis D_T T_F is_processT3_ST)
        thus \<open>(s, {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close>
          by (intro hyp) (meson UnI1 UnI2)
      qed
    qed
  next
    fix s X Y
    assume assm : \<open>(s, Y) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7 \<and> X \<subseteq> Y\<close>
    hence \<open>(s, Y) \<in> ?f1 \<or> (s, Y) \<in> ?f2 \<or> (s, Y) \<in> ?f3 \<or> (s, Y) \<in> ?f4 \<or>
           (s, Y) \<in> ?f5 \<or> (s, Y) \<in> ?f6 \<or> (s, Y) \<in> ?f7\<close> by fast
    thus \<open>(s, X) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close>
    proof (elim disjE)
      assume \<open>(s, Y) \<in> ?f1\<close>
      hence \<open>(s, X) \<in> ?f1\<close> by simp
      thus \<open>(s, X) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    next
      assume \<open>(s, Y) \<in> ?f2\<close>
      with assm[THEN conjunct2] have \<open>(s, X) \<in> ?f2\<close> by simp blast
      thus \<open>(s, X) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    next
      assume \<open>(s, Y) \<in> ?f3\<close>
      with assm[THEN conjunct2] is_processT4 have \<open>(s, X) \<in> ?f3\<close> by simp blast
      thus \<open>(s, X) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    next
      assume \<open>(s, Y) \<in> ?f4\<close>
      with assm[THEN conjunct2] is_processT4 have \<open>(s, X) \<in> ?f4\<close> by simp blast
      thus \<open>(s, X) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    next
      assume \<open>(s, Y) \<in> ?f5\<close>
      with assm[THEN conjunct2] have \<open>(s, X) \<in> ?f5\<close> by simp blast
      thus \<open>(s, X) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    next
      assume \<open>(s, Y) \<in> ?f6\<close>
      hence \<open>(s, X) \<in> ?f6\<close> by simp
      thus \<open>(s, X) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    next
      assume \<open>(s, Y) \<in> ?f7\<close>
      hence \<open>(s, X) \<in> ?f7\<close> by simp
      thus \<open>(s, X) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    qed
  next
    fix s X Y
    assume assm : \<open>(s, X) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7 \<and>
                   (\<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7)\<close>
    have \<open>(s, X) \<in> ?f1 \<or> (s, X) \<in> ?f2 \<or> (s, X) \<in> ?f3 \<or> (s, X) \<in> ?f4 \<or>
          (s, X) \<in> ?f5 \<or> (s, X) \<in> ?f6 \<or> (s, X) \<in> ?f7\<close> using assm[THEN conjunct1] by fast
    thus \<open>(s, X \<union> Y) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close>
    proof (elim disjE)
      assume \<open>(s, X) \<in> ?f1\<close>
      hence \<open>(s, X \<union> Y) \<in> ?f1\<close> by simp
      thus \<open>(s, X \<union> Y) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    next
      assume \<open>(s, X) \<in> ?f2\<close>
      with assm[THEN conjunct2] have \<open>(s, X \<union> Y) \<in> ?f2\<close> by simp blast
      thus \<open>(s, X \<union> Y) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    next
      assume \<open>(s, X) \<in> ?f3\<close>
      with assm[THEN conjunct2] have \<open>(s, X \<union> Y) \<in> ?f3\<close>
        by simp (metis F_T T_F append_Nil is_processT5_S7' list.distinct(1))
      thus \<open>(s, X \<union> Y) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    next
      assume \<open>(s, X) \<in> ?f4\<close>
      with assm[THEN conjunct2] have \<open>(s, X \<union> Y) \<in> ?f4\<close>
        by simp (metis append.assoc append_is_Nil_conv is_processT5_S1)
      thus \<open>(s, X \<union> Y) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    next
      assume \<open>(s, X) \<in> ?f5\<close>
      with assm[THEN conjunct2] have \<open>(s, X \<union> Y) \<in> ?f5\<close>
        by simp (metis Diff_empty Diff_insert0 T_F Un_Diff not_Cons_self)
      thus \<open>(s, X \<union> Y) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    next
      assume \<open>(s, X) \<in> ?f6\<close>
      hence \<open>(s, X \<union> Y) \<in> ?f6\<close> by simp
      thus \<open>(s, X \<union> Y) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    next
      assume \<open>(s, X) \<in> ?f7\<close>
      hence \<open>(s, X \<union> Y) \<in> ?f7\<close> by simp
      thus \<open>(s, X \<union> Y) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    qed
  next
    fix s X
    have * : \<open>(s @ [tick], {}) \<notin> ?f2 \<union> ?f3 \<union> ?f5\<close>
      by simp (metis Cons_eq_appendI append_self_conv2 front_tickFree_mono 
                     is_processT2_TR list.distinct(1) non_tickFree_tick)
    assume \<open>(s @ [tick], {}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close>
    with "*" have \<open>(s @ [tick], {}) \<in> ?f1 \<or> (s @ [tick], {}) \<in> ?f4 \<or>
                   (s @ [tick], {}) \<in> ?f6 \<or> (s @ [tick], {}) \<in> ?f7\<close> by fast
    thus \<open>(s, X - {tick}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close>
    proof (elim disjE)
      assume \<open>(s @ [tick], {}) \<in> ?f1\<close>
      hence \<open>(s, X - {tick}) \<in> ?f2\<close> by blast
      thus \<open>(s, X - {tick}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    next
      assume \<open>(s @ [tick], {}) \<in> ?f4\<close>
      then obtain t1 t2
        where ** : \<open>s = t1 @ t2\<close> \<open>t1 \<in> \<T> P\<close> \<open>tickFree t1\<close> \<open>(t2 @ [tick], {}) \<in> \<F> Q\<close> 
        by simp (metis butlast_append last_appendR snoc_eq_iff_butlast)
      hence \<open>(s, X - {tick}) \<in> (if t2 = [] then ?f5 else ?f4)\<close>
        by simp (metis F_T process_charn self_append_conv2)
      thus \<open>(s, X - {tick}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by (meson UnCI)
    next
      assume \<open>(s @ [tick], {}) \<in> ?f6\<close>
      with is_processT9 have \<open>s \<in> \<D> P\<close> by simp blast
      thus \<open>(s, X - {tick}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    next
      assume \<open>(s @ [tick], {}) \<in> ?f7\<close>
      then obtain t1 t2 where ** : \<open>s @ [tick] = t1 @ t2\<close> \<open>t1 \<in> \<T> P\<close>
                                   \<open>tickFree t1\<close> \<open>t2 \<in> \<D> Q\<close> by blast
      from "**"(1, 3, 4) obtain t2' where \<open>t2 = t2' @ [tick]\<close> \<open>t2' @ [tick] \<in> \<D> Q\<close>
        by (cases t2 rule: rev_cases) auto
      with "**"(1) is_processT9 have \<open>s = t1 @ t2' \<and> t2' \<in> \<D> Q\<close> by simp blast
      with "**"(2, 3) have \<open>(s, X - {tick}) \<in> ?f7\<close> by simp blast
      thus \<open>(s, X - {tick}) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> by blast
    qed
  next
    show \<open>s \<in> ?d1 \<union> ?d2 \<and> tickFree s \<and> front_tickFree t \<Longrightarrow> s @ t \<in> ?d1 \<union> ?d2\<close> for s t
      apply (simp, elim conjE disjE exE)
      by (solves \<open>simp add: is_processT7\<close>)      
         (meson append.assoc is_processT7 tickFree_append)
  next
    show \<open>s \<in> ?d1 \<union> ?d2 \<Longrightarrow> (s, X) \<in> ?f1 \<union> ?f2 \<union> ?f3 \<union> ?f4 \<union> ?f5 \<union> ?f6 \<union> ?f7\<close> for s X
      by blast
  next
    fix s
    assume \<open>s @ [tick] \<in> ?d1 \<union> ?d2\<close>
    then consider \<open>s @ [tick] \<in> ?d1\<close> | \<open>s @ [tick] \<in> ?d2\<close> by blast
    thus \<open>s \<in> ?d1 \<union> ?d2\<close>
    proof cases
      assume \<open>s @ [tick] \<in> ?d1\<close>
      with is_processT have \<open>s \<in> ?d1\<close> by blast
      thus \<open>s \<in> ?d1 \<union> ?d2\<close> by blast
    next
      assume \<open>s @ [tick] \<in> ?d2\<close>
      then obtain t1 t2 where ** : \<open>s @ [tick] = t1 @ t2\<close> \<open>t1 \<in> \<T> P\<close>
                                   \<open>tickFree t1\<close> \<open>t2 \<in> \<D> Q\<close> by blast
      from "**"(1, 3, 4) obtain t2' where \<open>t2 = t2' @ [tick]\<close> \<open>t2' @ [tick] \<in> \<D> Q\<close>
        by (cases t2 rule: rev_cases) auto
      with "**"(1) is_processT9 have \<open>s = t1 @ t2' \<and> t2' \<in> \<D> Q\<close> by simp blast
      with "**"(2, 3) have \<open>s \<in> ?d2\<close> by simp blast
      thus \<open>s \<in> ?d1 \<union> ?d2\<close> by blast
    qed
  qed
qed



subsection \<open>Projections\<close>

lemma F_Interrupt :
  \<open>\<F> (P \<triangle> Q) = 
   {(t1 @ [tick], X)| t1 X. t1 @ [tick] \<in> \<T> P} \<union>
   {(t1, X - {tick})| t1 X. t1 @ [tick] \<in> \<T> P} \<union>
   {(t1, X) \<in> \<F> P. tickFree t1 \<and> ([], X) \<in> \<F> Q} \<union>
   {(t1 @ t2, X)| t1 t2 X. t1 \<in> \<T> P \<and> tickFree t1 \<and> (t2, X) \<in> \<F> Q \<and> t2 \<noteq> []} \<union>
   {(t1, X - {tick})| t1 X. t1 \<in> \<T> P \<and> tickFree t1 \<and> [tick] \<in> \<T> Q} \<union>
   {(t1, X). t1 \<in> \<D> P} \<union> 
   {(t1 @ t2, X)| t1 t2 X. t1 \<in> \<T> P \<and> tickFree t1 \<and> t2 \<in> \<D> Q}\<close>
  by (simp add: Failures_def FAILURES_def Interrupt.rep_eq)
  (* by (simp add: Failures.rep_eq FAILURES_def Interrupt.rep_eq) *)

lemma D_Interrupt : 
  \<open>\<D> (P \<triangle> Q) = \<D> P \<union> {t1 @ t2| t1 t2. t1 \<in> \<T> P \<and> tickFree t1 \<and> t2 \<in> \<D> Q}\<close>
  by (simp add: Divergences_def DIVERGENCES_def Interrupt.rep_eq)
  (* by (simp add: Divergences.rep_eq DIVERGENCES_def Interrupt.rep_eq) *)

lemma T_Interrupt : 
  \<open>\<T> (P \<triangle> Q) = \<T> P \<union> {t1 @ t2| t1 t2. t1 \<in> \<T> P \<and> tickFree t1 \<and> t2 \<in> \<T> Q}\<close>
  apply (simp add: Traces_def TRACES_def Failures_def[symmetric] F_Interrupt)
  (* apply (simp add: Traces.rep_eq TRACES_def Failures.rep_eq[symmetric] F_Interrupt) *)
  apply (safe, simp_all add: is_processT8)
  subgoal by (metis is_processT3_SR)
  subgoal by auto
  subgoal by auto
  subgoal by (metis is_processT8_S)
  subgoal by (metis is_processT4_empty nonTickFree_n_frontTickFree process_charn)
  by (metis append.right_neutral is_processT4_empty tickFree_Nil)
  



subsection \<open>Monotony\<close>

lemma mono_Interrupt[simp]: \<open>P \<triangle> Q \<sqsubseteq> P' \<triangle> Q'\<close> if \<open>P \<sqsubseteq> P'\<close> and \<open>Q \<sqsubseteq> Q'\<close>
proof (unfold le_approx_def, intro conjI allI impI subsetI)
  show \<open>s \<in> \<D> (P' \<triangle> Q') \<Longrightarrow> s \<in> \<D> (P \<triangle> Q)\<close> for s
    using that[THEN le_approx1] D_T that(1)[THEN le_approx2T]
    by (simp add: D_Interrupt) blast
next
  show \<open>s \<notin> \<D> (P \<triangle> Q) \<Longrightarrow> \<R>\<^sub>a (P \<triangle> Q) s = \<R>\<^sub>a (P' \<triangle> Q') s\<close> for s
    apply (simp add: D_Interrupt Ra_def F_Interrupt,
           intro subset_antisym subsetI; simp, elim disjE)
    subgoal by (metis le_approx2T that(1))
    subgoal by (metis is_processT9 le_approx2T that(1))
    subgoal by (metis F_T append.right_neutral le_approx2 that)
    subgoal by (metis is_processT2 is_processT7 le_approx2T proc_ord2a that)
    subgoal by (metis (no_types, lifting) append_Nil2 le_approx2T min_elems6
          no_Trace_implies_no_Failure self_append_conv2 that)
    subgoal by metis
    subgoal by (metis le_approx2T that(1))
    subgoal by (metis le_approx_lemma_T subset_eq that(1))
    subgoal by (metis is_processT8_S le_approx2 that)
    subgoal by (metis is_processT2 is_processT7_S le_approx2 le_approx2T that) 
    subgoal by (metis D_T le_approx2T that)
    subgoal by (metis in_mono le_approx1 that(1))
    by (metis le_approx1 le_approx2T process_charn subsetD that)
next
  from that[THEN le_approx3]
  show \<open>s \<in> min_elems (\<D> (P \<triangle> Q)) \<Longrightarrow> s \<in> \<T> (P' \<triangle> Q')\<close> for s
    by (auto simp add: min_elems_def D_Interrupt T_Interrupt subset_iff)
       (metis le_approx2T le_list_def less_append order_le_imp_less_or_eq that(1))
qed


lemma mono_Interrupt_T: \<open>P \<sqsubseteq>\<^sub>T P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>T Q' \<Longrightarrow> P \<triangle> Q \<sqsubseteq>\<^sub>T P' \<triangle> Q'\<close>
  unfolding trace_refine_def by (auto simp add: T_Interrupt)

lemma mono_right_Interrupt_D: \<open>Q \<sqsubseteq>\<^sub>D Q' \<Longrightarrow> P \<triangle> Q \<sqsubseteq>\<^sub>D P \<triangle> Q'\<close>
  unfolding divergence_refine_def by (auto simp add: D_Interrupt) 

\<comment>\<open>We have no monotony, even partial, with \<^term>\<open>(\<sqsubseteq>\<^sub>F)\<close>.\<close>

lemma mono_Interrupt_FD:
  \<open>P \<sqsubseteq>\<^sub>F\<^sub>D P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>F\<^sub>D Q' \<Longrightarrow> P \<triangle> Q \<sqsubseteq>\<^sub>F\<^sub>D P' \<triangle> Q'\<close>
  unfolding failure_divergence_refine_def le_ref_def
  by (simp add: D_Interrupt F_Interrupt, safe;
      metis [[metis_verbose = false]] F_subset_imp_T_subset subsetD)

lemma mono_Interrupt_DT:
  \<open>P \<sqsubseteq>\<^sub>D\<^sub>T P' \<Longrightarrow> Q \<sqsubseteq>\<^sub>D\<^sub>T Q' \<Longrightarrow> P \<triangle> Q \<sqsubseteq>\<^sub>D\<^sub>T P' \<triangle> Q'\<close>
  unfolding trace_divergence_refine_def trace_refine_def divergence_refine_def
  by (auto simp add: T_Interrupt D_Interrupt subset_iff)



subsection \<open>Properties\<close>


lemma Interrupt_STOP_neutral : \<open>P \<triangle> STOP = P\<close> \<open>STOP \<triangle> P = P\<close>
   apply (all \<open>subst Process_eq_spec\<close>, safe)
         apply (simp_all add: Process_eq_spec F_Interrupt D_Interrupt F_STOP T_STOP
      D_STOP T_F is_processT6 is_processT8_S tick_T_F)
  subgoal by (meson process_charn tick_T_F)
  subgoal by (metis F_T T_nonTickFree_imp_decomp)
  subgoal by (meson DiffE insertI1 is_processT6_S2 is_processT8_S)
  by blast

lemma Interrupt_BOT_absorb : \<open>P \<triangle> \<bottom> = \<bottom>\<close> \<open>\<bottom> \<triangle> P = \<bottom>\<close>
  by (simp_all add: BOT_iff_D D_Interrupt D_UU Nil_elem_T)

lemma Interrupt_is_BOT_iff : \<open>P \<triangle> Q = \<bottom> \<longleftrightarrow> P = \<bottom> \<or> Q = \<bottom>\<close>
  by (simp add: BOT_iff_D D_Interrupt Nil_elem_T)


lemma events_Interrupt: \<open>events_of (P \<triangle> Q) = events_of P \<union> events_of Q\<close>
  apply (intro subset_antisym subsetI; simp add: events_of_def T_Interrupt)
  by (metis UnE set_append) (metis Nil_elem_T append_Nil tickFree_Nil)


lemma Interrupt_Ndet_distrib : \<open>P \<triangle> Q1 \<sqinter> Q2 = (P \<triangle> Q1) \<sqinter> (P \<triangle> Q2)\<close>
  (is \<open>?lhs = ?rhs\<close>)
proof (subst Process_eq_spec_optimized, safe)
  show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close> for s
    by (auto simp add: D_Interrupt D_Ndet)
next
  show \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ?lhs\<close> for s
    by (auto simp add: D_Interrupt D_Ndet)
next
  fix s X
  assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
  assume \<open>(s, X) \<in> \<F> ?lhs\<close>
  then consider \<open>s \<in> \<D> (P \<triangle> Q1 \<sqinter> Q2)\<close>
    | \<open>\<exists>t1. s = t1 @ [tick] \<and> t1 @ [tick] \<in> \<T> P\<close>
    | \<open>s @ [tick] \<in> \<T> P \<and> tick \<notin> X\<close>
    | \<open>(s, X) \<in> \<F> P \<and> tickFree s \<and> ([], X) \<in> \<F> (Q1 \<sqinter> Q2)\<close>
    | \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<T> P \<and> tickFree t1 \<and> (t2, X) \<in> \<F> (Q1 \<sqinter> Q2) \<and> t2 \<noteq> []\<close>
    | \<open>s \<in> \<T> P \<and> tickFree s \<and> [tick] \<in> \<T> (Q1 \<sqinter> Q2) \<and> tick \<notin> X\<close>
    by (simp add: F_Interrupt D_Interrupt) blast
  thus \<open>(s, X) \<in> \<F> ?rhs\<close>
  proof cases
    from same_div D_F show \<open>s \<in> \<D> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> by blast
  next
    show \<open>\<exists>t1. s = t1 @ [tick] \<and> t1 @ [tick] \<in> \<T> P \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
      by (simp add: F_Ndet F_Interrupt)
  next
    show \<open>s @ [tick] \<in> \<T> P \<and> tick \<notin> X \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
      by (simp add: F_Ndet F_Interrupt) (metis Diff_insert_absorb)
  next
    show \<open>(s, X) \<in> \<F> P \<and> tickFree s \<and> ([], X) \<in> \<F> (Q1 \<sqinter> Q2) \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
      by (simp add: F_Ndet F_Interrupt) blast
  next
    show \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<T> P \<and> tickFree t1 \<and> 
                  (t2, X) \<in> \<F> (Q1 \<sqinter> Q2) \<and> t2 \<noteq> [] \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
      by (simp add: F_Ndet F_Interrupt) metis
  next
    show \<open>s \<in> \<T> P \<and> tickFree s \<and> [tick] \<in> \<T> (Q1 \<sqinter> Q2) \<and> tick \<notin> X \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
      by (simp add: F_Interrupt F_Ndet T_Ndet) (metis Diff_insert_absorb)
  qed
next
  have \<open>(s, X) \<in> \<F> (P \<triangle> Q1) \<Longrightarrow> (s, X) \<in> \<F> (P \<triangle> Q1 \<sqinter> Q2)\<close> for s X Q1 Q2
    by (simp add: F_Interrupt F_Ndet D_Ndet T_Ndet) blast
  thus \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for s X
    by (simp add: F_Ndet) (metis Ndet_commute)
qed


lemma Ndet_Interrupt_distrib : \<open>P1 \<sqinter> P2 \<triangle> Q = (P1 \<triangle> Q) \<sqinter> (P2 \<triangle> Q)\<close>
  (is \<open>?lhs = ?rhs\<close>) 
proof (subst Process_eq_spec_optimized, safe)
  show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close> for s
    by (auto simp add: D_Ndet T_Ndet D_Interrupt)
next
  show \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ?lhs\<close> for s
    by (auto simp add: D_Ndet T_Ndet D_Interrupt)
next
  fix s X
  assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
  assume \<open>(s, X) \<in> \<F> ?lhs\<close>
  then consider \<open>s \<in> \<D> ?lhs\<close>
    | \<open>\<exists>t1. s = t1 @ [tick] \<and> t1 @ [tick] \<in> \<T> (P1 \<sqinter> P2)\<close>
    | \<open>s @ [tick] \<in> \<T> (P1 \<sqinter> P2) \<and> tick \<notin> X\<close>
    | \<open>(s, X) \<in> \<F> (P1 \<sqinter> P2) \<and> tickFree s \<and> ([], X) \<in> \<F> Q\<close>
    | \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<T> (P1 \<sqinter> P2) \<and> tickFree t1 \<and> (t2, X) \<in> \<F> Q \<and> t2 \<noteq> []\<close>
    | \<open>s \<in> \<T> (P1 \<sqinter> P2) \<and> tickFree s \<and> [tick] \<in> \<T> Q \<and> tick \<notin> X\<close>
    by (simp add: F_Interrupt D_Interrupt) blast
  thus \<open>(s, X) \<in> \<F> ?rhs\<close>
  proof cases
    from same_div D_F show \<open>s \<in> \<D> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> by blast
  next
    show \<open>\<exists>t1. s = t1 @ [tick] \<and> t1 @ [tick] \<in> \<T> (P1 \<sqinter> P2) \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
      by (simp add: T_Ndet F_Ndet F_Interrupt) metis
  next
    show \<open>s @ [tick] \<in> \<T> (P1 \<sqinter> P2) \<and> tick \<notin> X \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
      by (simp add: T_Ndet F_Ndet F_Interrupt) (metis Diff_insert_absorb)
  next
    show \<open>(s, X) \<in> \<F> (P1 \<sqinter> P2) \<and> tickFree s \<and> ([], X) \<in> \<F> Q \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
      by (simp add: F_Ndet F_Interrupt) blast
  next
    show \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<T> (P1 \<sqinter> P2) \<and> tickFree t1 \<and>
                  (t2, X) \<in> \<F> Q \<and> t2 \<noteq> [] \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
      by (simp add: T_Ndet F_Ndet F_Interrupt) metis
  next
    show \<open>s \<in> \<T> (P1 \<sqinter> P2) \<and> tickFree s \<and> [tick] \<in> \<T> Q \<and> tick \<notin> X \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
      by (simp add: T_Ndet F_Ndet F_Interrupt) (metis Diff_insert_absorb)
  qed
next
  have \<open>(s, X) \<in> \<F> (P1 \<triangle> Q) \<Longrightarrow> (s, X) \<in> \<F> (P1 \<sqinter> P2 \<triangle> Q)\<close> for s X P1 P2
    by (simp add: F_Interrupt F_Ndet D_Ndet T_Ndet) blast
  thus \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for s X
    by (simp add: F_Ndet) (metis Ndet_commute)
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
             (metis "*"(2, 3) append_assoc tickFree_append)
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
             (metis "*"(3, 4) append.assoc tickFree_append)
      qed
    qed
  next
    fix s X
    assume same_div: \<open>\<D> ?lhs = \<D> ?rhs\<close>
    assume \<open>(s, X) \<in> \<F> ?lhs\<close>
    then consider \<open>s \<in> \<D> ?lhs\<close>
      | \<open>\<exists>t1. s = t1 @ [tick] \<and> t1 @ [tick] \<in> \<T> P\<close>
      | \<open>s @ [tick] \<in> \<T> P \<and> tick \<notin> X\<close>
      | \<open>(s, X) \<in> \<F> P \<and> tickFree s \<and> ([], X) \<in> \<F> (Q \<triangle> R)\<close>
      | \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<T> P \<and> tickFree t1 \<and> (t2, X) \<in> \<F> (Q \<triangle> R) \<and> t2 \<noteq> []\<close>
      | \<open>s \<in> \<T> P \<and> tickFree s \<and> [tick] \<in> \<T> (Q \<triangle> R) \<and> tick \<notin> X\<close>
      by (subst (asm) F_Interrupt, simp add:  D_Interrupt) blast
    thus \<open>(s, X) \<in> \<F> ?rhs\<close>
    proof cases
      from same_div D_F show \<open>s \<in> \<D> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> by blast
    next
      show \<open>\<exists>t1. s = t1 @ [tick] \<and> t1 @ [tick] \<in> \<T> P \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
        by (auto simp add: F_Interrupt T_Interrupt)
    next
      show \<open>s @ [tick] \<in> \<T> P \<and> tick \<notin> X \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
        by (simp add: F_Interrupt T_Interrupt) (metis Diff_insert_absorb)
    next
      assume assm : \<open>(s, X) \<in> \<F> P \<and> tickFree s \<and> ([], X) \<in> \<F> (Q \<triangle> R)\<close>
      with non_BOT(2, 3) consider \<open>[tick] \<in> \<T> Q \<and> tick \<notin> X\<close>
        | \<open>([], X) \<in> \<F> Q \<and> ([], X) \<in> \<F> R\<close>
        | \<open>[] \<in> \<T> Q \<and> [tick] \<in> \<T> R \<and> tick \<notin> X\<close>
        by (simp add: F_Interrupt Nil_elem_T BOT_iff_D) blast
      thus \<open>(s, X) \<in> \<F> ?rhs\<close>
      proof cases
        show \<open>[tick] \<in> \<T> Q \<and> tick \<notin> X \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
          by (simp add: F_Interrupt T_Interrupt) (metis Diff_insert_absorb F_T assm)
      next
        show \<open>([], X) \<in> \<F> Q \<and> ([], X) \<in> \<F> R \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
          by (simp add: F_Interrupt assm)
      next
        show \<open>[] \<in> \<T> Q \<and> [tick] \<in> \<T> R \<and> tick \<notin> X \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
          by (simp add: F_Interrupt T_Interrupt) (metis Diff_insert_absorb F_T assm)
      qed
    next
      assume \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<T> P \<and> tickFree t1 \<and>
                      (t2, X) \<in> \<F> (Q \<triangle> R) \<and> t2 \<noteq> []\<close>
      then obtain t1 t2 where * : \<open>s = t1 @ t2\<close> \<open>t1 \<in> \<T> P\<close> \<open>tickFree t1\<close> 
                                  \<open>(t2, X) \<in> \<F> (Q \<triangle> R)\<close> \<open>t2 \<noteq> []\<close> by blast
      from "*"(4) consider \<open>t2 \<in> \<D> (Q \<triangle> R)\<close>
        | \<open>\<exists>u1. t2 = u1 @ [tick] \<and> u1 @ [tick] \<in> \<T> Q\<close>
        | \<open>t2 @ [tick] \<in> \<T> Q \<and> tick \<notin> X\<close>
        | \<open>(t2, X) \<in> \<F> Q \<and> tickFree t2 \<and> ([], X) \<in> \<F> R\<close>
        | \<open>\<exists>u1 u2. t2 = u1 @ u2 \<and> u1 \<in> \<T> Q \<and> tickFree u1 \<and> (u2, X) \<in> \<F> R \<and> u2 \<noteq> []\<close>
        | \<open>t2 \<in> \<T> Q \<and> tickFree t2 \<and> [tick] \<in> \<T> R \<and> tick \<notin> X\<close>
        by (simp add: F_Interrupt D_Interrupt) blast
      thus \<open>(s, X) \<in> \<F> ?rhs\<close>
      proof cases
        assume \<open>t2 \<in> \<D> (Q \<triangle> R)\<close>
        with "*"(1, 2, 3) have \<open>s \<in> \<D> ?lhs\<close> by (simp add: D_Interrupt) blast
        with same_div D_F show \<open>(s, X) \<in> \<F> ?rhs\<close> by blast
      next
        from "*"(1, 2, 3) show \<open>\<exists>u1. t2 = u1 @ [tick] \<and> u1 @ [tick] \<in> \<T> Q \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
          by (simp add: F_Interrupt T_Interrupt) (metis append_assoc)
      next
        from "*"(1, 2, 3) show \<open>t2 @ [tick] \<in> \<T> Q \<and> tick \<notin> X \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
          by (simp add: F_Interrupt T_Interrupt) (metis Diff_insert_absorb)
      next
        from "*"(1) show \<open>(t2, X) \<in> \<F> Q \<and> tickFree t2 \<and> ([], X) \<in> \<F> R \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
          by (simp add: F_Interrupt T_Interrupt) (metis "*"(2, 3, 5))
      next
        from "*"(1, 2, 3) show \<open>\<exists>u1 u2. t2 = u1 @ u2 \<and> u1 \<in> \<T> Q \<and> tickFree u1 \<and>
                                        (u2, X) \<in> \<F> R \<and> u2 \<noteq> [] \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
          by (simp add: F_Interrupt T_Interrupt)
             (metis (mono_tags, lifting) append_assoc tickFree_append)
      next
        from "*"(1, 2, 3) show \<open>t2 \<in> \<T> Q \<and> tickFree t2 \<and> [tick] \<in> \<T> R \<and> 
                                tick \<notin> X \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
          by (simp add: F_Interrupt T_Interrupt) (metis Diff_insert_absorb)
      qed
    next
      show \<open>s \<in> \<T> P \<and> tickFree s \<and> [tick] \<in> \<T> (Q \<triangle> R) \<and> tick \<notin> X \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
        by (simp add: F_Interrupt T_Interrupt)
           (metis Diff_insert_absorb append_Nil hd_append2 hd_in_set list.sel(1) tickFree_def)
    qed
  next
    fix s X
    assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
    assume \<open>(s, X) \<in> \<F> ?rhs\<close>
    then consider \<open>s \<in> \<D> ?rhs\<close>
      | \<open>\<exists>t1. s = t1 @ [tick] \<and> t1 @ [tick] \<in> \<T> (P \<triangle> Q)\<close>
      | \<open>s @ [tick] \<in> \<T> (P \<triangle> Q) \<and> tick \<notin> X\<close>
      | \<open>(s, X) \<in> \<F> (P \<triangle> Q) \<and> tickFree s \<and> ([], X) \<in> \<F> R\<close>
      | \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<T> (P \<triangle> Q) \<and> tickFree t1 \<and> (t2, X) \<in> \<F> R \<and> t2 \<noteq> []\<close>
      | \<open>s \<in> \<T> (P \<triangle> Q) \<and> tickFree s \<and> [tick] \<in> \<T> R \<and> tick \<notin> X\<close>
      by (subst (asm) F_Interrupt, simp add: D_Interrupt) blast 
    thus \<open>(s, X) \<in> \<F> ?lhs\<close>
    proof cases
      from same_div D_F show \<open>s \<in> \<D> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> by blast
    next
      show \<open>\<exists>t1. s = t1 @ [tick] \<and> t1 @ [tick] \<in> \<T> (P \<triangle> Q) \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
        by (simp add: F_Interrupt T_Interrupt)
           (metis last_append self_append_conv snoc_eq_iff_butlast)
    next
      assume assm : \<open>s @ [tick] \<in> \<T> (P \<triangle> Q) \<and> tick \<notin> X\<close>
      from assm[THEN conjunct1] consider \<open>s @ [tick] \<in> \<T> P\<close>
        | \<open>\<exists>t1 t2. s @ [tick] = t1 @ t2 \<and> t1 \<in> \<T> P \<and> tickFree t1 \<and> t2 \<in> \<T> Q\<close>
        by (simp add: T_Interrupt) blast
      thus \<open>(s, X) \<in> \<F> ?lhs\<close>
      proof cases
        show \<open>s @ [tick] \<in> \<T> P \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
          by (simp add: F_Interrupt) (metis Diff_insert_absorb assm[THEN conjunct2])
      next
        show \<open>\<exists>t1 t2. s @ [tick] = t1 @ t2 \<and> t1 \<in> \<T> P \<and>
                      tickFree t1 \<and> t2 \<in> \<T> Q \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
          by (simp add: F_Interrupt T_Interrupt)
             (metis Diff_insert_absorb T_nonTickFree_imp_decomp
                    append.right_neutral append_Nil assm[THEN conjunct2]
                    butlast.simps(2) butlast_append non_tickFree_tick tickFree_append)
      qed
    next
      assume assm : \<open>(s, X) \<in> \<F> (P \<triangle> Q) \<and> tickFree s \<and> ([], X) \<in> \<F> R\<close>
      from assm[THEN conjunct1] consider \<open>s \<in> \<D> (P \<triangle> Q)\<close>
        | \<open>\<exists>t1. s = t1 @ [tick] \<and> t1 @ [tick] \<in> \<T> P\<close>
        | \<open>s @ [tick] \<in> \<T> P \<and> tick \<notin> X\<close>
        | \<open>(s, X) \<in> \<F> P \<and> tickFree s \<and> ([], X) \<in> \<F> Q\<close>
        | \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<T> P \<and> tickFree t1 \<and> (t2, X) \<in> \<F> Q \<and> t2 \<noteq> []\<close>
        | \<open>s \<in> \<T> P \<and> tickFree s \<and> [tick] \<in> \<T> Q \<and> tick \<notin> X\<close>
        by (simp add: F_Interrupt D_Interrupt) blast
      thus \<open>(s, X) \<in> \<F> ?lhs\<close>
      proof cases
        assume \<open>s \<in> \<D> (P \<triangle> Q)\<close>
        hence \<open>s \<in> \<D> ?rhs\<close> by (simp add: D_Interrupt)
        with same_div D_F show \<open>(s, X) \<in> \<F> ?lhs\<close> by blast
      next
        show \<open>\<exists>t1. s = t1 @ [tick] \<and> t1 @ [tick] \<in> \<T> P \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
          by (simp add: F_Interrupt)
      next
        show \<open>s @ [tick] \<in> \<T> P \<and> tick \<notin> X \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
          by (simp add: F_Interrupt) (metis Diff_insert_absorb)
      next
        show \<open>(s, X) \<in> \<F> P \<and> tickFree s \<and> ([], X) \<in> \<F> Q \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
          by (simp add: F_Interrupt assm[THEN conjunct2])
      next
        show \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<T> P \<and> tickFree t1 \<and>
                      (t2, X) \<in> \<F> Q \<and> t2 \<noteq> [] \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
          by (simp add: F_Interrupt) (metis assm[THEN conjunct2] tickFree_append)
      next
        show \<open>s \<in> \<T> P \<and> tickFree s \<and> [tick] \<in> \<T> Q \<and> tick \<notin> X \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
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
      show \<open>s \<in> \<T> (P \<triangle> Q) \<and> tickFree s \<and> [tick] \<in> \<T> R \<and> tick \<notin> X \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
        by (simp add: F_Interrupt T_Interrupt)
           (metis Diff_insert_absorb Nil_elem_T append.right_neutral append_Nil tickFree_append)
    qed
  qed

  thus \<open>?lhs = ?rhs\<close>
    apply (cases \<open>P = \<bottom>\<close>, solves \<open>simp add: Interrupt_BOT_absorb\<close>)
    apply (cases \<open>Q = \<bottom>\<close>, solves \<open>simp add: Interrupt_BOT_absorb\<close>)
    apply (cases \<open>R = \<bottom>\<close>, solves \<open>simp add: Interrupt_BOT_absorb\<close>)
    by blast
qed



subsection \<open>Key Property\<close>


lemma Interrupt_Mprefix:
  \<open>(\<box>a \<in> A \<rightarrow> P a) \<triangle> Q = Q \<box> (\<box>a \<in> A \<rightarrow> P a \<triangle> Q)\<close> (is \<open>?lhs = ?rhs\<close>)
proof (subst Process_eq_spec_optimized, safe)
  fix s
  assume \<open>s \<in> \<D> ?lhs\<close>
  then consider \<open>s \<in> \<D> (\<box>a \<in> A \<rightarrow> P a)\<close>
    | \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<T> (\<box>a \<in> A \<rightarrow> P a) \<and> tickFree t1 \<and> t2 \<in> \<D> Q\<close>
    by (simp add: D_Interrupt) blast
  thus \<open>s \<in> \<D> ?rhs\<close>
  proof cases
    show \<open>s \<in> \<D> (\<box>a \<in> A \<rightarrow> P a) \<Longrightarrow> s \<in> \<D> ?rhs\<close>
      by (simp add: D_Det D_Mprefix D_Interrupt) blast
  next
    assume \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<T> (\<box>a \<in> A \<rightarrow> P a) \<and> tickFree t1 \<and> t2 \<in> \<D> Q\<close>
    then obtain t1 t2 where \<open>s = t1 @ t2\<close> \<open>t1 \<in> \<T> (\<box>a \<in> A \<rightarrow> P a)\<close>
                            \<open>tickFree t1\<close> \<open>t2 \<in> \<D> Q\<close> by blast
    thus \<open>s \<in> \<D> ?rhs\<close>
      by (simp add: D_Det D_Mprefix T_Mprefix D_Interrupt)
         (metis (no_types, opaque_lifting) hd_append2 imageI
                self_append_conv2 tickFree_tl tl_append2)
  qed
next
  fix s
  assume \<open>s \<in> \<D> ?rhs\<close>
  then consider \<open>s \<in> \<D> Q\<close> | \<open>\<exists>a s'. s = ev a # s' \<and> a \<in> A \<and> s' \<in> \<D> (P a \<triangle> Q)\<close>
    by (simp add: D_Det D_Mprefix image_iff) (metis event.inject list.exhaust_sel)
  thus \<open>s \<in> \<D> ?lhs\<close>
  proof cases
    show \<open>s \<in> \<D> Q \<Longrightarrow> s \<in> \<D> ?lhs\<close>
      apply (simp add: D_Interrupt)
      using Nil_elem_T tickFree_Nil by blast
  next
    assume \<open>\<exists>a s'. s = ev a # s' \<and> a \<in> A \<and> s' \<in> \<D> (P a \<triangle> Q)\<close>
    then obtain a s'
      where * : \<open>s = ev a # s'\<close> \<open>a \<in> A\<close>
                \<open>s' \<in> \<D> (P a) \<or> (\<exists>t1 t2. s' = t1 @ t2 \<and> t1 \<in> \<T> (P a) \<and> 
                                          tickFree t1 \<and> t2 \<in> \<D> Q)\<close>
      by (simp add: D_Interrupt) blast
    from "*"(3) show \<open>s \<in> \<D> ?lhs\<close>
      apply (elim disjE exE)
      subgoal by (solves \<open>simp add: "*"(1, 2) D_Interrupt D_Mprefix image_iff\<close>)
      by (simp add: "*"(1) D_Interrupt T_Mprefix)
         (metis "*"(2) Cons_eq_appendI event.distinct(1) list.sel(1, 3) tickFree_Cons)
  qed
next
  fix s X
  assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
  assume \<open>(s, X) \<in> \<F> ?lhs\<close>
  then consider \<open>s \<in> \<D> ?lhs\<close> 
    | \<open>\<exists>t1. s = t1 @ [tick] \<and> t1 @ [tick] \<in> \<T> (Mprefix A P)\<close>
    | \<open>s @ [tick] \<in> \<T> (Mprefix A P) \<and> tick \<notin> X\<close>
    | \<open>(s, X) \<in> \<F> (Mprefix A P) \<and> tickFree s \<and> ([], X) \<in> \<F> Q\<close>
    | \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<T> (Mprefix A P) \<and> tickFree t1 \<and> (t2, X) \<in> \<F> Q \<and> t2 \<noteq> []\<close>
    | \<open>s \<in> \<T> (Mprefix A P) \<and> tickFree s \<and> [tick] \<in> \<T> Q \<and> tick \<notin> X\<close>
    by (simp add: F_Interrupt D_Interrupt) blast
  thus \<open>(s, X) \<in> \<F> ?rhs\<close>
  proof cases
    from D_F same_div show \<open>s \<in> \<D> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> by blast
  next
    show \<open>\<exists>t1. s = t1 @ [tick] \<and> t1 @ [tick] \<in> \<T> (Mprefix A P) \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> 
      by (elim exE, simp add: F_Det T_Mprefix F_Mprefix F_Interrupt image_iff)
         (metis event.distinct(1) hd_append list.sel(1) tl_append2)
  next
    show \<open>s @ [tick] \<in> \<T> (Mprefix A P) \<and> tick \<notin> X \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
      by (simp add: F_Det T_Mprefix F_Mprefix F_Interrupt image_iff)
         (metis Diff_insert_absorb event.simps(3) hd_append list.sel(1) tl_append_if)
  next
    show \<open>(s, X) \<in> \<F> (Mprefix A P) \<and> tickFree s \<and> ([], X) \<in> \<F> Q \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
      by (simp add: F_Det F_Mprefix F_Interrupt image_iff) (metis tickFree_tl)
  next
    show \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<T> (Mprefix A P) \<and>
                  tickFree t1 \<and> (t2, X) \<in> \<F> Q \<and> t2 \<noteq> [] \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
      by (elim exE, simp add: F_Det T_Mprefix F_Mprefix F_Interrupt image_iff)
         (metis hd_append2 self_append_conv2 tickFree_tl tl_append2)
  next
    show \<open>s \<in> \<T> (Mprefix A P) \<and> tickFree s \<and> [tick] \<in> \<T> Q \<and> tick \<notin> X \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
      by (simp add: F_Det T_Mprefix F_Mprefix F_Interrupt image_iff)
         (metis Diff_insert_absorb tickFree_tl)
  qed
next
  fix s X
  assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
  assume assm : \<open>(s, X) \<in> \<F> ?rhs\<close>
  show \<open>(s, X) \<in> \<F> ?lhs\<close>
  proof (cases \<open>s = []\<close>)
    from assm show \<open>s = [] \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
      by (simp add: F_Det F_Mprefix F_Interrupt Nil_elem_T) blast
  next 
    assume \<open>s \<noteq> []\<close>
    with assm consider \<open>(s, X) \<in> \<F> Q\<close>
      | \<open>\<exists>a s'. s = ev a # s' \<and> a \<in> A \<and> (s', X) \<in> \<F> (P a \<triangle> Q)\<close>
      by (simp add: F_Det F_Mprefix image_iff) (metis event.inject list.exhaust_sel)
    thus \<open>(s, X) \<in> \<F> ?lhs\<close>
    proof cases
      show \<open>(s, X) \<in> \<F> Q \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
        by (simp add: F_Interrupt)
           (metis Nil_elem_T \<open>s \<noteq> []\<close> append_Nil tickFree_Nil)
    next
      assume \<open>\<exists>a s'. s = ev a # s' \<and> a \<in> A \<and> (s', X) \<in> \<F> (P a \<triangle> Q)\<close>
      then obtain a s'
        where * : \<open>s = ev a # s'\<close> \<open>a \<in> A\<close> \<open>(s', X) \<in> \<F> (P a \<triangle> Q)\<close> by blast
      from "*"(3) consider \<open>s' \<in> \<D> (P a \<triangle> Q)\<close>
        | \<open>\<exists>t1. s' = t1 @ [tick] \<and> t1 @ [tick] \<in> \<T> (P a)\<close>
        | \<open>s' @ [tick] \<in> \<T> (P a) \<and> tick \<notin> X\<close>
        | \<open>(s', X) \<in> \<F> (P a) \<and> tickFree s' \<and> ([], X) \<in> \<F> Q\<close>
        | \<open>\<exists>t1 t2. s' = t1 @ t2 \<and> t1 \<in> \<T> (P a) \<and> tickFree t1 \<and> (t2, X) \<in> \<F> Q \<and> t2 \<noteq> []\<close>
        | \<open>s' \<in> \<T> (P a) \<and> tickFree s' \<and> [tick] \<in> \<T> Q \<and> tick \<notin> X\<close>
        by (simp add: F_Interrupt D_Interrupt) blast
      thus \<open>(s, X) \<in> \<F> ?lhs\<close>
      proof cases
        assume \<open>s' \<in> \<D> (P a \<triangle> Q)\<close>
        hence \<open>s \<in> \<D> ?lhs\<close>
          by (simp add: D_Interrupt D_Mprefix T_Mprefix "*"(1, 2) image_iff)
             (metis "*"(2) append_Cons event.distinct(1) list.sel(1, 3) tickFree_Cons)
        with D_F same_div show \<open>(s, X) \<in> \<F> ?lhs\<close> by blast 
      next
        show \<open>\<exists>t1. s' = t1 @ [tick] \<and> t1 @ [tick] \<in> \<T> (P a) \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
          by (elim exE, simp add: "*"(1, 2) F_Interrupt T_Mprefix)
      next
        show \<open>s' @ [tick] \<in> \<T> (P a) \<and> tick \<notin> X \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
          by (simp add: "*"(1, 2) F_Interrupt T_Mprefix) blast
      next
        show \<open>(s', X) \<in> \<F> (P a) \<and> tickFree s' \<and> ([], X) \<in> \<F> Q \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
          by (simp add: "*"(1, 2) F_Interrupt F_Mprefix)
      next
        show \<open>\<exists>t1 t2. s' = t1 @ t2 \<and> t1 \<in> \<T> (P a) \<and> tickFree t1 \<and>
                      (t2, X) \<in> \<F> Q \<and> t2 \<noteq> [] \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
          by (elim exE, simp add: F_Interrupt T_Mprefix "*"(1))
             (metis "*"(2) Cons_eq_appendI event.distinct(1) list.sel(1, 3) tickFree_Cons)
      next
        show \<open>s' \<in> \<T> (P a) \<and> tickFree s' \<and> [tick] \<in> \<T> Q \<and> tick \<notin> X \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
          by (simp add: F_Interrupt T_Mprefix "*"(1, 2) image_iff) blast
      qed
    qed
  qed
qed


corollary \<open>(\<box>a \<in> A \<rightarrow> P a) \<triangle> (\<box>b \<in> B \<rightarrow> Q b) = 
   \<box>x \<in> A \<union> B \<rightarrow> (     if x \<in> A \<inter> B then (P x \<triangle> (\<box>b \<in> B \<rightarrow> Q b)) \<sqinter> Q x
                   else if   x \<in> A   then  P x \<triangle> (\<box>b \<in> B \<rightarrow> Q b)
                   else                     Q x)\<close>
  apply (subst Interrupt_Mprefix, subst Mprefix_Det_distr)
  by (metis Det_commute Mprefix_Det_distr)


subsection \<open>Continuity\<close>

lemma chain_left_Interrupt: \<open>chain Y \<Longrightarrow> chain (\<lambda>i. Y i \<triangle> Q)\<close>
  by (simp add: chain_def)

lemma chain_right_Interrupt: \<open>chain Y \<Longrightarrow> chain (\<lambda>i. P \<triangle> Y i)\<close>
  by(simp add: chain_def)  


lemma cont_left_prem_Interrupt : \<open>(\<Squnion> i. Y i) \<triangle> Q = (\<Squnion> i. Y i  \<triangle> Q)\<close>
  (is \<open>?lhs = ?rhs\<close>) if chain : \<open>chain Y\<close>
proof (subst Process_eq_spec, safe)
 show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close> for s
   by (simp add: limproc_is_thelub chain chain_left_Interrupt
                 D_Interrupt T_LUB D_LUB) blast
next
  fix s
  define S
    where \<open>S i \<equiv> {t1. s = t1 \<and> t1 \<in> \<D> (Y i)} \<union>
                  {t1. \<exists>t2. s = t1 @ t2 \<and> t1 \<in> \<T> (Y i) \<and> tickFree t1 \<and> t2 \<in> \<D> Q}\<close> for i
  assume \<open>s \<in> \<D> ?rhs\<close>
  hence \<open>s \<in> \<D> (Y i \<triangle> Q)\<close> for i
    by (simp add: limproc_is_thelub D_LUB chain_left_Interrupt chain)
  hence \<open>\<forall>i. S i \<noteq> {}\<close> by (simp add: S_def D_Interrupt) blast
  moreover have \<open>finite (S 0)\<close>
    unfolding S_def
    apply (rule finite_subset[of _ \<open>{t1. \<exists>t2. s = t1 @ t2}\<close>], blast)
    by (metis prefixes_fin)
  moreover have \<open>\<forall>i. S (Suc i) \<subseteq> S i\<close>
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
    by (simp add: limproc_is_thelub chain chain_left_Interrupt
                  F_Interrupt F_LUB T_LUB D_LUB) blast
next
  fix s X
  define S
    where \<open>S i \<equiv> {t1. s = t1 @ [tick] \<and> t1 @ [tick] \<in> \<T> (Y i)} \<union>
                 {t1. s = t1 \<and> t1 @ [tick] \<in> \<T> (Y i) \<and> tick \<notin> X} \<union>
                 {t1. s = t1 \<and> (t1, X) \<in> \<F> (Y i) \<and> tickFree t1 \<and> ([], X) \<in> \<F> Q} \<union>
                 {t1. \<exists>t2. s = t1 @ t2 \<and> t1 \<in> \<T> (Y i) \<and> tickFree t1 \<and> (t2, X) \<in> \<F> Q \<and> t2 \<noteq> []} \<union>
                 {t1. s = t1 \<and> t1 \<in> \<T> (Y i) \<and> tickFree t1 \<and> [tick] \<in> \<T> Q \<and> tick \<notin> X} \<union>
                 {t1. s = t1 \<and> t1 \<in> \<D> (Y i)} \<union>
                 {t1. \<exists>t2. s = t1 @ t2 \<and> t1 \<in> \<T> (Y i) \<and> tickFree t1 \<and> t2 \<in> \<D> Q}\<close> for i
  assume \<open>(s, X) \<in> \<F> ?rhs\<close>
  hence \<open>(s, X) \<in> \<F> (Y i \<triangle> Q)\<close> for i
    by (simp add: limproc_is_thelub F_LUB chain_left_Interrupt chain)
  hence \<open>\<forall>i. S i \<noteq> {}\<close> by (simp add: S_def F_Interrupt, safe; simp, blast)
  moreover have \<open>finite (S 0)\<close>
    unfolding S_def
    apply (intro finite_UnI)
    apply (all \<open>rule finite_subset[of _ \<open>{t1. \<exists>t2. s = t1 @ t2}\<close>], blast\<close>)
    by (metis prefixes_fin)+
  moreover have \<open>\<forall>i. S (Suc i) \<subseteq> S i\<close> (* Try to improve this. *)
    unfolding S_def apply (intro allI Un_mono subsetI; simp)
    subgoal using D_T le_approx2T po_class.chain_def chain by blast
    subgoal using D_T le_approx2T po_class.chain_def chain by blast
    subgoal using is_processT8_S le_approx2 po_class.chainE chain by blast
    subgoal by (metis NT_ND le_approx2T po_class.chainE chain) 
    subgoal using D_T le_approx2T po_class.chain_def chain by blast 
    subgoal by (meson in_mono le_approx1 po_class.chainE chain)
    by (metis NT_ND le_approx2T po_class.chainE chain)
  ultimately have \<open>(\<Inter>i. S i) \<noteq> {}\<close>
    by (rule Inter_nonempty_finite_chained_sets)
  then obtain t1 where * : \<open>\<forall>i. t1 \<in> S i\<close> 
    by (meson INT_iff ex_in_conv iso_tuple_UNIV_I)
  show \<open>(s, X) \<in> \<F> ?lhs\<close>
  proof (cases \<open>\<exists>j t2. s = t1 @ t2 \<and> t1 \<in> \<T> (Y j) \<and> tickFree t1 \<and> t2 \<in> \<D> Q\<close>)
    case True1 : True
    then obtain j t2 where ** : \<open>s = t1 @ t2\<close> \<open>t1 \<in> \<T> (Y j)\<close>
                                \<open>tickFree t1\<close> \<open>t2 \<in> \<D> Q\<close> by blast
    from "*" F_T NT_ND is_processT3_ST have \<open>\<forall>i. t1 \<in> \<T> (Y i)\<close>
      by (simp add: S_def) blast
    with "**"(1, 3, 4) show \<open>(s, X) \<in> \<F> ?lhs\<close>
      by (simp add: F_Interrupt limproc_is_thelub chain T_LUB) blast
  next
    case False1 : False
    show \<open>(s, X) \<in> \<F> ?lhs\<close>
    proof (cases \<open>\<exists>j t2. s = t1 @ t2 \<and> t1 \<in> \<T> (Y j) \<and> tickFree t1 \<and>
                         (t2, X) \<in> \<F> Q \<and> t2 \<noteq> []\<close>)
      case True2 : True
      then obtain j t2 where ** : \<open>s = t1 @ t2\<close> \<open>t1 \<in> \<T> (Y j)\<close> \<open>tickFree t1\<close>
                                  \<open>(t2, X) \<in> \<F> Q\<close> \<open>t2 \<noteq> []\<close> by blast
      from "*" F_T NT_ND is_processT3_ST have \<open>\<forall>i. t1 \<in> \<T> (Y i)\<close>
        by (simp add: S_def) blast
      with "**"(1, 3, 4, 5) False1 show \<open>(s, X) \<in> \<F> ?lhs\<close>
        by (simp add: F_Interrupt limproc_is_thelub chain T_LUB) blast
    next
      case False2: False
      show \<open>(s, X) \<in> \<F> ?lhs\<close>
      proof (cases \<open>\<exists>j. s = t1 \<and> t1 \<in> \<T> (Y j) \<and> tickFree t1 \<and> [tick] \<in> \<T> Q \<and> tick \<notin> X\<close>)
        case True3 : True
        then obtain j where ** : \<open>s = t1\<close> \<open>t1 \<in> \<T> (Y j)\<close> \<open>tickFree t1\<close>
                                 \<open>[tick] \<in> \<T> Q\<close> \<open>tick \<notin> X\<close> by blast
        from "*" F_T NT_ND is_processT3_ST have \<open>\<forall>i. t1 \<in> \<T> (Y i)\<close>
          by (simp add: S_def) blast
        with "**"(1, 3, 4, 5) False1 show \<open>(s, X) \<in> \<F> ?lhs\<close>
          by (simp add: F_Interrupt limproc_is_thelub chain T_LUB) blast
      next
        case False3: False
        show \<open>(s, X) \<in> \<F> ?lhs\<close>
        proof (cases \<open>\<exists>j. s = t1 \<and> (t1, X) \<in> \<F> (Y j) \<and> tickFree t1 \<and> ([], X) \<in> \<F> Q\<close>)
          case True4 : True
          then obtain j where ** : \<open>s = t1\<close> \<open>(t1, X) \<in> \<F> (Y j)\<close> \<open>tickFree t1\<close> \<open>([], X) \<in> \<F> Q\<close> by blast
          have \<open>(t1, X) \<in> \<F> (Y i)\<close> for i
            using "*"[rule_format, of i] apply (simp add: S_def "**"(1), elim disjE)
            subgoal by (solves \<open>simp add: T_F_spec is_processT6_S1\<close>)
            subgoal by (solves \<open>simp add: T_F_spec is_processT6_S1\<close>)
            subgoal using "**"(1) False3 by blast
            subgoal by (solves \<open>simp add: is_processT8\<close>)
            using "**"(1) False1 by blast
          with "**"(1, 3, 4) show \<open>(s, X) \<in> \<F> ?lhs\<close>
            by (simp add: F_Interrupt limproc_is_thelub chain F_LUB)
        next
          case False4: False
          show \<open>(s, X) \<in> \<F> ?lhs\<close>
          proof (cases \<open>\<exists>j. s = t1 @ [tick] \<and> t1 @ [tick] \<in> \<T> (Y j)\<close>)
            case True5 : True
            then obtain j where ** : \<open>s = t1 @ [tick]\<close> \<open>t1 @ [tick] \<in> \<T> (Y j)\<close> by blast
            from "*" False1 False2 have \<open>\<forall>i. t1 @ [tick] \<in> \<T> (Y i)\<close>
              by (auto simp add: S_def "**"(1))
            with "**"(1) show \<open>(s, X) \<in> \<F> ?lhs\<close>
              by (simp add: F_Interrupt limproc_is_thelub chain T_LUB)
          next
            case False5 : False
            show \<open>(s, X) \<in> \<F> ?lhs\<close>
            proof (cases \<open>\<exists>j. s = t1 \<and> t1 @ [tick] \<in> \<T> (Y j) \<and> tick \<notin> X\<close>)
              case True6 : True
              then obtain j where ** : \<open>s = t1\<close> \<open>t1 @ [tick] \<in> \<T> (Y j)\<close> \<open>tick \<notin> X\<close> by blast
              have \<open>t1 @ [tick] \<in> \<T> (Y i)\<close> for i
                using "*"[rule_format, of i] apply (simp add: S_def "**"(1), elim disjE)
                subgoal by (solves simp)
                subgoal using "**"(1) False4 by blast
                subgoal using "**"(1) False3 by blast
                subgoal using "**"(2) D_T front_tickFree_mono is_processT2_TR is_processT7 by blast
                subgoal using "**"(1) False1 by blast
                done
              with "**"(1, 3) show \<open>(s, X) \<in> \<F> ?lhs\<close>
                by (simp add: F_Interrupt limproc_is_thelub chain T_LUB)
                   (metis Diff_insert_absorb)
            next
              case False6: False
              have \<open>s = t1 \<and> t1 \<in> \<D> (Y i)\<close> for i
                using "*"[rule_format, of i] apply (simp add: S_def, elim disjE)
                subgoal using False5 by blast
                subgoal using False6 by blast
                subgoal using False4 by blast
                subgoal using False2 by blast
                subgoal using False3 by blast
                subgoal by (solves simp)
                subgoal using False1 by blast
                done
              thus \<open>(s, X) \<in> \<F> ?lhs\<close>
                by (simp add: F_Interrupt limproc_is_thelub chain D_LUB)
            qed
          qed
        qed
      qed
    qed
  qed
qed


lemma cont_right_prem_Interrupt : \<open>P \<triangle> (\<Squnion> i. Y i) = (\<Squnion> i. P \<triangle> Y i)\<close>
  (is \<open>?lhs = ?rhs\<close>) if chain : \<open>chain Y\<close>
proof (subst Process_eq_spec, safe)
  show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close> for s
    by (simp add: limproc_is_thelub chain chain_right_Interrupt
                  D_Interrupt D_LUB) blast
next
  fix s
  define S where \<open>S i \<equiv> {t1. \<exists>t2. s = t1 @ t2 \<and> t1 \<in> \<T> P \<and> 
                                  tickFree t1 \<and> t2 \<in> \<D> (Y i)}\<close> for i
  assume assm : \<open>s \<in> \<D> ?rhs\<close>
  show \<open>s \<in> \<D> ?lhs\<close>
  proof (cases \<open>s \<in> \<D> P\<close>)
    show \<open>s \<in> \<D> P \<Longrightarrow> s \<in> \<D> ?lhs\<close> by (simp add: D_Interrupt)
  next
    assume \<open>s \<notin> \<D> P\<close>
    with assm have \<open>\<forall>i. S i \<noteq> {}\<close>
      by (simp add: limproc_is_thelub chain chain_right_Interrupt
                    S_def D_Interrupt D_LUB) blast
    moreover have \<open>finite (S 0)\<close>
      unfolding S_def
      apply (rule finite_subset[of _ \<open>{t1. \<exists>t2. s = t1 @ t2}\<close>], blast)
      by (metis prefixes_fin)
    moreover have \<open>\<forall>i. S (Suc i) \<subseteq> S i\<close>
      unfolding S_def apply (intro allI Un_mono subsetI; simp)
      by (metis in_mono le_approx1 po_class.chainE chain)
    ultimately have \<open>(\<Inter>i. S i) \<noteq> {}\<close>
      by (rule Inter_nonempty_finite_chained_sets)
    then obtain t1 where * : \<open>\<forall>i. t1 \<in> S i\<close>
      by (meson INT_iff ex_in_conv iso_tuple_UNIV_I)
    thus \<open>s \<in> \<D> ?lhs\<close>
      by (simp add: D_Interrupt limproc_is_thelub chain D_LUB S_def) blast
  qed
next
  show \<open>(s, X) \<in> \<F> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for s X
    by (simp add: limproc_is_thelub chain chain_right_Interrupt
                  F_Interrupt F_LUB T_LUB D_LUB) blast
next
  fix s X
  define S
    where \<open>S i \<equiv> {t1. s = t1 \<and> (t1, X) \<in> \<F> P \<and> tickFree t1 \<and> ([], X) \<in> \<F> (Y i)} \<union>
                 {t1. \<exists>t2. s = t1 @ t2 \<and> t1 \<in> \<T> P \<and> tickFree t1 \<and> (t2, X) \<in> \<F> (Y i) \<and> t2 \<noteq> []} \<union>
                 {t1. s = t1 \<and> t1 \<in> \<T> P \<and> tickFree t1 \<and> [tick] \<in> \<T> (Y i) \<and> tick \<notin> X} \<union>
                 {t1. \<exists>t2. s = t1 @ t2 \<and> t1 \<in> \<T> P \<and> tickFree t1 \<and> t2 \<in> \<D> (Y i)}\<close> for i
  assume assm : \<open>(s, X) \<in> \<F> ?rhs\<close>
  show \<open>(s, X) \<in> \<F> ?lhs\<close>
  proof (cases \<open>\<exists>t1. s = t1 @ [tick] \<and> t1 @ [tick] \<in> \<T> P \<or>
                     s = t1 \<and> t1 @ [tick] \<in> \<T> P \<and> tick \<notin> X \<or>
                     s = t1 \<and> t1 \<in> \<D> P\<close>)
    case True
    thus \<open>(s, X) \<in> \<F> ?lhs\<close>
      by (simp add: F_Interrupt) (metis Diff_insert_absorb)
  next
    case False
    with assm have \<open>\<forall>i. S i \<noteq> {}\<close>
      by (simp add: limproc_is_thelub chain chain_right_Interrupt
                    S_def F_Interrupt F_LUB) blast
    moreover have \<open>finite (S 0)\<close>
      unfolding S_def
      apply (rule finite_subset[of _ \<open>{t1. \<exists>t2. s = t1 @ t2}\<close>], blast)
      by (metis prefixes_fin)
    moreover have \<open>\<forall>i. S (Suc i) \<subseteq> S i\<close>
      unfolding S_def apply (intro allI Un_mono subsetI; simp)
      subgoal by (meson le_approx2 po_class.chainE process_charn chain)
      subgoal by (metis le_approx2 po_class.chainE process_charn chain)
      subgoal by (metis insert_absorb insert_subset le_approx_lemma_T po_class.chainE chain)
      by (metis in_mono le_approx1 po_class.chainE chain)
    ultimately have \<open>(\<Inter>i. S i) \<noteq> {}\<close>
      by (rule Inter_nonempty_finite_chained_sets)
    then obtain t1 where * : \<open>\<forall>i. t1 \<in> S i\<close>
      by (meson INT_iff ex_in_conv iso_tuple_UNIV_I)
    
    show \<open>(s, X) \<in> \<F> ?lhs\<close>
    proof (cases \<open>\<exists>j t2. s = t1 @ t2 \<and> t1 \<in> \<T> P \<and> tickFree t1 \<and>
                         (t2, X) \<in> \<F> (Y j) \<and> t2 \<noteq> []\<close>)
      case True1 : True
      then obtain j t2
        where ** : \<open>s = t1 @ t2\<close> \<open>t1 \<in> \<T> P\<close> \<open>tickFree t1\<close> 
                   \<open>(t2, X) \<in> \<F> (Y j)\<close> \<open>t2 \<noteq> []\<close> by blast
      from "*" "**"(1, 5) D_F have \<open>\<forall>i. (t2, X) \<in> \<F> (Y i)\<close> by (simp add: S_def) blast
      with "**"(1, 2, 3, 5) show \<open>(s, X) \<in> \<F> ?lhs\<close>
        by (simp add: F_Interrupt limproc_is_thelub chain F_LUB) blast
    next
      case False1: False
      show \<open>(s, X) \<in> \<F> ?lhs\<close>
      proof (cases \<open>\<exists>j. s = t1 \<and> (t1, X) \<in> \<F> P \<and> tickFree t1 \<and> ([], X) \<in> \<F> (Y j)\<close>)
        case True2 : True
        then obtain j where ** : \<open>s = t1\<close> \<open>(t1, X) \<in> \<F> P\<close> 
                                 \<open>tickFree t1\<close> \<open>([], X) \<in> \<F> (Y j)\<close> by blast
        from "*" "**"(1) D_F is_processT6_S2 have \<open>\<forall>i. ([], X) \<in> \<F> (Y i)\<close>
          by (simp add: S_def) blast
        with "**"(1, 2, 3) show \<open>(s, X) \<in> \<F> ?lhs\<close>
          by (simp add: F_Interrupt limproc_is_thelub chain F_LUB)
      next
        case False2: False
        show \<open>(s, X) \<in> \<F> ?lhs\<close> 
        proof (cases \<open>\<exists>j. s = t1 \<and> t1 \<in> \<T> P \<and> tickFree t1 \<and>
                          [tick] \<in> \<T> (Y j) \<and> tick \<notin> X\<close>)
          case True3 : True
          then obtain j where ** : \<open>s = t1\<close> \<open>t1 \<in> \<T> P\<close> \<open>tickFree t1\<close>
                                   \<open>[tick] \<in> \<T> (Y j)\<close> \<open>tick \<notin> X\<close> by blast
          from "*" "**"(1) False2 have \<open>\<forall>i. [tick] \<in> \<T> (Y i)\<close>
            by (simp add: S_def)
               (metis BOT_iff_D CollectI D_Bot NT_ND 
                      front_tickFree_Nil front_tickFree_single)
          with "**"(1, 2, 3, 5) show \<open>(s, X) \<in> \<F> ?lhs\<close>
            by (simp add: F_Interrupt limproc_is_thelub chain T_LUB) blast
        next
          case False3 : False
          have \<open>\<exists>t2. s = t1 @ t2 \<and> t1 \<in> \<T> P \<and> tickFree t1 \<and> t2 \<in> \<D> (Y i)\<close> for i
            using "*"[rule_format, of i] apply (simp add: S_def, elim disjE)
            using False1 False2 False3 by blast+
           
          thus \<open>(s, X) \<in> \<F> ?lhs\<close>
            by (simp add: F_Interrupt limproc_is_thelub chain D_LUB)
               (metis same_append_eq)
        qed
      qed
    qed
  qed
qed
  

lemma Interrupt_cont[simp] : 
  assumes cont_f : \<open>cont f\<close> and cont_g : \<open>cont g\<close>
  shows \<open>cont (\<lambda>x. f x \<triangle> g x)\<close>
proof -
  have * : \<open>cont (\<lambda>y. y \<triangle> g x)\<close> for x
    by (rule contI2, rule monofunI, solves simp, simp add: cont_left_prem_Interrupt)
  have \<open>\<And>y. cont (Interrupt y)\<close>
    by (simp add: contI2 cont_right_prem_Interrupt fun_belowD lub_fun monofunI)
  hence ** : \<open>cont (\<lambda>x. y \<triangle> g x)\<close> for y
    by (rule cont_compose) (simp add: cont_g)
  show ?thesis by (fact cont_apply[OF cont_f "*" "**"])
qed


end