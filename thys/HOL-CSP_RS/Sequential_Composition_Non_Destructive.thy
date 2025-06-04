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


section \<open>Non Destructiveness of Sequential Composition\<close>

(*<*)
theory Sequential_Composition_Non_Destructive
  imports Process_Restriction_Space "HOL-CSPM.CSPM"
begin
  (*>*)

subsection \<open>Refinement\<close>

lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq_FD :
  \<open>P \<^bold>; Q \<down> n \<sqsubseteq>\<^sub>F\<^sub>D (P \<down> n) \<^bold>; (Q \<down> n)\<close> (is \<open>?lhs \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close>)
proof -
  have * : \<open>t \<in> \<D> (P \<down> n) \<Longrightarrow> t \<in> \<D> ?lhs\<close> for t
    by (elim D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
      (auto simp add: Seq_projs D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  { fix t u v r w x
    assume \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>length u < n\<close> \<open>v = w @ x\<close> \<open>w \<in> \<T> Q\<close>
      \<open>length w = n\<close> \<open>tF w\<close> \<open>ftF x\<close> \<open>t = u @ v\<close>
    hence \<open>t = (u @ take (n - length u) w) @ drop (n - length u) w @ x \<and>
           u @ take (n - length u) w \<in> \<T> (P \<^bold>; Q) \<and>
           length (u @ take (n - length u) w) = n \<and>
           tF (u @ take (n - length u) w) \<and> ftF (drop (n - length u) w @ x)\<close>
      by (simp add: \<open>t = u @ v\<close> T_Seq)
        (metis append_T_imp_tickFree append_take_drop_id front_tickFree_append
          is_processT3_TR_append list.distinct(1) tickFree_append_iff)
    with D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k have \<open>t \<in> \<D> ?lhs\<close> by blast
  } note ** = this

  show \<open>?lhs \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close>
  proof (unfold refine_defs, safe)
    show div : \<open>t \<in> \<D> ?lhs\<close> if \<open>t \<in> \<D> ?rhs\<close> for t
    proof -
      from \<open>t \<in> \<D> ?rhs\<close> consider \<open>t \<in> \<D> (P \<down> n)\<close>
        | u v r where \<open>t = u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> (P \<down> n)\<close> \<open>v \<in> \<D> (Q \<down> n)\<close>
        unfolding D_Seq by blast
      thus \<open>t \<in> \<D> ?lhs\<close>
      proof cases
        show \<open>t \<in> \<D> (P \<down> n) \<Longrightarrow> t \<in> \<D> ?lhs\<close> by (fact "*")
      next
        fix u v r assume \<open>t = u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> (P \<down> n)\<close> \<open>v \<in> \<D> (Q \<down> n)\<close>
        from \<open>u @ [\<checkmark>(r)] \<in> \<T> (P \<down> n)\<close> consider \<open>u @ [\<checkmark>(r)] \<in> \<D> (P \<down> n)\<close> | \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>length u < n\<close>
          by (elim T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE) (auto simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        thus \<open>t \<in> \<D> ?lhs\<close>
        proof cases
          show \<open>u @ [\<checkmark>(r)] \<in> \<D> (P \<down> n) \<Longrightarrow> t \<in> \<D> ?lhs\<close>
            by (metis "*" D_imp_front_tickFree \<open>t = u @ v\<close> \<open>v \<in> \<D> (Q \<down> n)\<close>
                front_tickFree_append_iff is_processT7 is_processT9 not_Cons_self)
        next
          from \<open>v \<in> \<D> (Q \<down> n)\<close> show \<open>u @ [\<checkmark>(r)] \<in> \<T> P \<Longrightarrow> length u < n \<Longrightarrow> t \<in> \<D> ?lhs\<close>
          proof (elim D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE exE conjE)
            show \<open>u @ [\<checkmark>(r)] \<in> \<T> P \<Longrightarrow> v \<in> \<D> Q \<Longrightarrow> t \<in> \<D> ?lhs\<close>
              by (simp add: \<open>t = u @ v\<close> D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k D_Seq) blast
          next
            show \<open>\<lbrakk>u @ [\<checkmark>(r)] \<in> \<T> P; length u < n; v = w @ x; w \<in> \<T> Q;
                   length w = n; tF w; ftF x\<rbrakk> \<Longrightarrow> t \<in> \<D> ?lhs\<close> for w x
              using "**" \<open>t = u @ v\<close> by blast
          qed
        qed
      qed
    qed

    have mono : \<open>(P \<down> n) \<^bold>; (Q \<down> n) \<sqsubseteq> P \<^bold>; Q\<close>
      by (simp add: fun_below_iff mono_Seq restriction_fun_def
          restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_approx_self)

    show \<open>(t, X) \<in> \<F> ?lhs\<close> if \<open>(t, X) \<in> \<F> ?rhs\<close> for t X
      by (meson F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI div is_processT8 mono proc_ord2a that)
  qed
qed


corollary restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_MultiSeq_FD :
  \<open>(SEQ l \<in>@ L. P l) \<down> n \<sqsubseteq>\<^sub>F\<^sub>D SEQ l \<in>@ L. (P l \<down> n)\<close>
proof (induct L rule: rev_induct)
  show \<open>(SEQ l \<in>@ []. P l) \<down> n \<sqsubseteq>\<^sub>F\<^sub>D SEQ l \<in>@ []. (P l \<down> n)\<close> by simp
next
  fix a L
  assume hyp: \<open>(SEQ l \<in>@ L. P l) \<down> n \<sqsubseteq>\<^sub>F\<^sub>D SEQ l \<in>@ L. (P l \<down> n)\<close>
  have \<open>(SEQ l \<in>@ (L @ [a]). P l) \<down> n = (SEQ l \<in>@ L. P l \<^bold>; P a) \<down> n\<close> by simp
  also have \<open>\<dots> \<sqsubseteq>\<^sub>F\<^sub>D SEQ l \<in>@ L. (P l \<down> n) \<^bold>; (P a \<down> n)\<close>
    by (fact trans_FD[OF restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Seq_FD mono_Seq_FD[OF hyp idem_FD]])
  also have \<open>\<dots> = SEQ l\<in>@(L @ [a]). (P l \<down> n)\<close> by simp
  finally show \<open>(SEQ l \<in>@ (L @ [a]). P l) \<down> n \<sqsubseteq>\<^sub>F\<^sub>D \<dots>\<close> .
qed



subsection \<open>Non Destructiveness\<close>

lemma Seq_non_destructive :
  \<open>non_destructive (\<lambda>(P :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, Q). P \<^bold>; Q)\<close>
proof (rule order_non_destructiveI, clarify)
  fix P P' Q Q' :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and n
  assume \<open>(P, Q) \<down> n = (P', Q') \<down> n\<close> \<open>0 < n\<close>
  hence \<open>P \<down> n = P' \<down> n\<close> \<open>Q \<down> n = Q' \<down> n\<close>
    by (simp_all add: restriction_prod_def)
  show \<open>P \<^bold>; Q \<down> n \<sqsubseteq>\<^sub>F\<^sub>D P' \<^bold>; Q' \<down> n\<close>
  proof (rule leFD_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
    show div : \<open>t \<in> \<D> (P' \<^bold>; Q') \<Longrightarrow> t \<in> \<D> (P \<^bold>; Q \<down> n)\<close> if \<open>length t \<le> n\<close> for t
    proof (unfold D_Seq, safe)
      show \<open>t \<in> \<D> P' \<Longrightarrow> t \<in> \<D> (P \<^bold>; Q \<down> n)\<close>
        by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Seq_projs)
          (metis (no_types, opaque_lifting) D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE
            D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI \<open>P \<down> n = P' \<down> n\<close>)
    next
      fix u r v assume \<open>t = u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> P'\<close> \<open>v \<in> \<D> Q'\<close>
      from \<open>t = u @ v\<close> \<open>length t \<le> n\<close> consider \<open>v = []\<close> \<open>length u = n\<close>
        | \<open>u = []\<close> \<open>length v = n\<close> | \<open>length u < n\<close> \<open>length v < n\<close>
        using nless_le by (cases u; cases v, auto)
      thus \<open>u @ v \<in> \<D> (P \<^bold>; Q \<down> n)\<close>
      proof cases
        assume \<open>v = []\<close> \<open>length u = n\<close>
        from \<open>u @ [\<checkmark>(r)] \<in> \<T> P'\<close> append_T_imp_tickFree is_processT3_TR_append
        have \<open>tF u\<close> \<open>u \<in> \<T> P'\<close> by auto
        from \<open>u \<in> \<T> P'\<close> \<open>length u = n\<close> \<open>P \<down> n = P' \<down> n\<close> have \<open>u \<in> \<T> P\<close>
          by (metis T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI less_or_eq_imp_le
              length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        with \<open>tF u\<close> have \<open>u \<in> \<T> (P \<^bold>; Q)\<close> by (simp add: T_Seq)
        with \<open>length u = n\<close> show \<open>u @ v \<in> \<D> (P \<^bold>; Q \<down> n)\<close>
          by (simp add: \<open>v = []\<close> \<open>tF u\<close> D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
      next
        assume \<open>u = []\<close> \<open>length v = n\<close>
        from \<open>0 < n\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> P'\<close> \<open>u = []\<close> \<open>P \<down> n = P' \<down> n\<close>
        have \<open>[\<checkmark>(r)] \<in> \<T> P\<close>
          by (cases n, simp_all)
            (metis Suc_leI T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI length_Cons
              length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k list.size(3) zero_less_Suc)
        show \<open>u @ v \<in> \<D> (P \<^bold>; Q \<down> n)\<close>
        proof (cases \<open>tF v\<close>)
          assume \<open>tF v\<close>
          have \<open>v \<in> \<T> Q'\<close> by (simp add: D_T \<open>v \<in> \<D> Q'\<close>)
          with \<open>length v = n\<close> \<open>Q \<down> n = Q' \<down> n\<close> have \<open>v \<in> \<T> Q\<close>
            unfolding restriction_fun_def
            by (metis T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI less_or_eq_imp_le
                length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
          with \<open>[\<checkmark>(r)] \<in> \<T> P\<close> have \<open>v \<in> \<T> (P \<^bold>; Q)\<close>
            by (simp add: T_Seq) (metis append_Nil)
          with \<open>length v = n\<close> show \<open>u @ v \<in> \<D> (P \<^bold>; Q \<down> n)\<close>
            by (simp add: \<open>u = []\<close> \<open>tF v\<close> D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
        next
          assume \<open>\<not> tF v\<close>
          with \<open>u = []\<close> \<open>Q \<down> n = Q' \<down> n\<close> \<open>\<not> tF v\<close> \<open>length t \<le> n\<close>
            \<open>t = u @ v\<close> \<open>v \<in> \<D> Q'\<close> have \<open>v \<in> \<D> Q\<close>
            by (metis append_self_conv2 not_tickFree_in_D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
          with \<open>[\<checkmark>(r)] \<in> \<T> P\<close> have \<open>v \<in> \<D> (P \<^bold>; Q)\<close>
            by (simp add: D_Seq) (metis append_Nil)
          thus \<open>u @ v \<in> \<D> (P \<^bold>; Q \<down> n)\<close>
            by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI \<open>u = []\<close>)
        qed
      next
        assume \<open>length u < n\<close> \<open>length v < n\<close>
        from \<open>u @ [\<checkmark>(r)] \<in> \<T> P'\<close> \<open>length u < n\<close> \<open>P \<down> n = P' \<down> n\<close>
        have \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close>
          by (metis length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Suc_le_eq 
              length_append_singleton T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
        moreover from \<open>v \<in> \<D> Q'\<close> \<open>length v < n\<close> \<open>Q \<down> n = Q' \<down> n\<close>
        have \<open>v \<in> \<D> Q\<close>
          by (metis D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI length_less_in_D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        ultimately show \<open>u @ v \<in> \<D> (P \<^bold>; Q \<down> n)\<close>
          by (auto simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k D_Seq)
      qed
    qed

    fix t X assume \<open>(t, X) \<in> \<F> (P' \<^bold>; Q')\<close> \<open>length t \<le> n\<close>
    consider \<open>t \<in> \<D> (P' \<^bold>; Q')\<close> | \<open>(t, X \<union> range tick) \<in> \<F> P'\<close> \<open>tF t\<close>
      | u r v where \<open>t = u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> P'\<close> \<open>(v, X) \<in> \<F> Q'\<close>
      using \<open>(t, X) \<in> \<F> (P' \<^bold>; Q')\<close> by (auto simp add: Seq_projs)
    thus \<open>(t, X) \<in> \<F> (P \<^bold>; Q \<down> n)\<close>
    proof cases
      from div \<open>length t \<le> n\<close> D_F
      show \<open>t \<in> \<D> (P' \<^bold>; Q') \<Longrightarrow> (t, X) \<in> \<F> (P \<^bold>; Q \<down> n)\<close> by blast
    next
      show \<open>(t, X) \<in> \<F> (P \<^bold>; Q \<down> n)\<close> if \<open>(t, X \<union> range tick) \<in> \<F> P'\<close> \<open>tF t\<close>
      proof (cases \<open>length t = n\<close>)
        assume \<open>length t = n\<close>
        from \<open>(t, X \<union> range tick) \<in> \<F> P'\<close> have \<open>t \<in> \<T> P'\<close> by (simp add: F_T)
        with \<open>P \<down> n = P' \<down> n\<close> \<open>length t \<le> n\<close> have \<open>t \<in> \<T> P\<close>
          by (metis T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        with \<open>tF t\<close> have \<open>t \<in> \<T> (P \<^bold>; Q)\<close> by (simp add: T_Seq)
        with \<open>length t = n\<close> \<open>tF t\<close> show \<open>(t, X) \<in> \<F> (P \<^bold>; Q \<down> n)\<close>
          by (simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
      next
        assume \<open>length t \<noteq> n\<close>
        with \<open>length t \<le> n\<close> have \<open>length t < n\<close> by linarith
        with \<open>P \<down> n = P' \<down> n\<close> \<open>(t, X \<union> range tick) \<in> \<F> P'\<close>
        have \<open>(t, X \<union> range tick) \<in> \<F> P\<close>
          by (metis F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI length_less_in_F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        with \<open>tF t\<close> show \<open>(t, X) \<in> \<F> (P \<^bold>; Q \<down> n)\<close>
          by (simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI F_Seq)
      qed
    next
      fix u r v assume \<open>t = u @ v\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> P'\<close> \<open>(v, X) \<in> \<F> Q'\<close>
      from \<open>t = u @ v\<close> \<open>length t \<le> n\<close> consider \<open>v = []\<close> \<open>length u = n\<close>
        | \<open>u = []\<close> \<open>length v = n\<close> | \<open>length u < n\<close> \<open>length v < n\<close>
        using nless_le by (cases u; cases v, auto)
      thus \<open>(t, X) \<in> \<F> (P \<^bold>; Q \<down> n)\<close>
      proof cases
        assume \<open>v = []\<close> \<open>length u = n\<close>
        from \<open>u @ [\<checkmark>(r)] \<in> \<T> P'\<close> append_T_imp_tickFree is_processT3_TR_append
        have \<open>tF u\<close> \<open>u \<in> \<T> P'\<close> by auto
        from \<open>u \<in> \<T> P'\<close> \<open>length u = n\<close> \<open>P \<down> n = P' \<down> n\<close> have \<open>u \<in> \<T> P\<close>
          by (metis T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI less_or_eq_imp_le
              length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        with \<open>tF u\<close> have \<open>u \<in> \<T> (P \<^bold>; Q)\<close> by (simp add: T_Seq)
        with \<open>length u = n\<close> show \<open>(t, X) \<in> \<F> (P \<^bold>; Q \<down> n)\<close>
          by (simp add: \<open>v = []\<close> \<open>tF u\<close> F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
            (use \<open>t = u @ v\<close> \<open>tF u\<close> \<open>v = []\<close> front_tickFree_Nil in blast)
      next
        assume \<open>u = []\<close> \<open>length v = n\<close>
        from \<open>0 < n\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> P'\<close> \<open>u = []\<close> \<open>P \<down> n = P' \<down> n\<close>
        have \<open>[\<checkmark>(r)] \<in> \<T> P\<close>
          by (cases n, simp_all)
            (metis Suc_leI T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI length_Cons
              length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k list.size(3) zero_less_Suc)
        show \<open>(t, X) \<in> \<F> (P \<^bold>; Q \<down> n)\<close>
        proof (cases \<open>tF v\<close>)
          assume \<open>tF v\<close>
          from F_T \<open>(v, X) \<in> \<F> Q'\<close> have \<open>v \<in> \<T> Q'\<close> by blast
          with \<open>length v = n\<close> \<open>Q \<down> n = Q' \<down> n\<close> have \<open>v \<in> \<T> Q\<close>
            unfolding restriction_fun_def
            by (metis T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI less_or_eq_imp_le
                length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
          with \<open>[\<checkmark>(r)] \<in> \<T> P\<close> have \<open>v \<in> \<T> (P \<^bold>; Q)\<close>
            by (simp add: T_Seq) (metis append_Nil)
          with \<open>length v = n\<close> have \<open>t \<in> \<D> (P \<^bold>; Q \<down> n)\<close>
            by (simp add: \<open>u = []\<close> \<open>tF v\<close> \<open>t = u @ v\<close> D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
          with D_F show \<open>(t, X) \<in> \<F> (P \<^bold>; Q \<down> n)\<close> by blast
        next
          assume \<open>\<not> tF v\<close>
          with \<open>u = []\<close> \<open>Q \<down> n = Q' \<down> n\<close> \<open>\<not> tF v\<close> \<open>length t \<le> n\<close>
            \<open>t = u @ v\<close> \<open>(v, X) \<in> \<F> Q'\<close> have \<open>(v, X) \<in> \<F> Q\<close>
            by (metis append_self_conv2 not_tickFree_in_F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
          with \<open>[\<checkmark>(r)] \<in> \<T> P\<close> have \<open>(t, X) \<in> \<F> (P \<^bold>; Q)\<close>
            by (simp add: \<open>t = u @ v\<close> \<open>u = []\<close> F_Seq) (metis append_Nil)
          thus \<open>(t, X) \<in> \<F> (P \<^bold>; Q \<down> n)\<close>
            by (simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
        qed
      next
        assume \<open>length u < n\<close> \<open>length v < n\<close>
        from \<open>u @ [\<checkmark>(r)] \<in> \<T> P'\<close> \<open>length u < n\<close> \<open>P \<down> n = P' \<down> n\<close>
        have \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close>
          by (metis length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Suc_le_eq 
              length_append_singleton T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
        moreover from \<open>(v, X) \<in> \<F> Q'\<close> \<open>length v < n\<close> \<open>Q \<down> n = Q' \<down> n\<close>
        have \<open>(v, X) \<in> \<F> Q\<close>
          by (metis F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI length_less_in_F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        ultimately show \<open>(t, X) \<in> \<F> (P \<^bold>; Q \<down> n)\<close>
          by (auto simp add: \<open>t = u @ v\<close> F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k F_Seq)
      qed
    qed
  qed
qed



(*<*)
end
  (*>*)