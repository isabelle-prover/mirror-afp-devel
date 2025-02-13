(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : HOL-CSP_OpSem - Operational semantics for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Burkhart Wolff.
 *
 * This file       : New laws
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

chapter\<open> Bonus: powerful new Laws \<close>

(*<*)
theory  CSP_New_Laws
  imports Initials
begin
(*>*)

section \<open>Powerful Results about \<^const>\<open>Sync\<close>\<close>

lemma add_complementary_events_of_in_failure:
  \<open>(t, X) \<in> \<F> P \<Longrightarrow> (t, X \<union> ev ` (- \<alpha>(P))) \<in> \<F> P\<close>
  by (erule is_processT5) (auto simp add: events_of_def, metis F_T in_set_conv_decomp)

lemma add_complementary_initials_in_refusal: \<open>X \<in> \<R> P \<Longrightarrow> X \<union> - P\<^sup>0 \<in> \<R> P\<close>
  unfolding Refusals_iff by (erule is_processT5) (auto simp add: initials_def F_T)

lemma TickRightSync: 
  \<open>\<checkmark>(r) \<in> S \<Longrightarrow> ftF u \<Longrightarrow> t setinterleaves ((u, [\<checkmark>(r)]), S) \<Longrightarrow> t = u \<and> last u = \<checkmark>(r)\<close>
  by (simp add: TickLeftSync setinterleaving_sym)

  

theorem Sync_is_Sync_restricted_superset_events:
  fixes S A :: \<open>'a set\<close> and P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  assumes superset : \<open>\<alpha>(P) \<union> \<alpha>(Q) \<subseteq> A\<close>
  defines \<open>S' \<equiv> S \<inter> A\<close>
  shows \<open>P \<lbrakk>S\<rbrakk> Q = P \<lbrakk>S'\<rbrakk> Q\<close>
proof (subst Process_eq_spec_optimized, safe)
  show \<open>s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q) \<Longrightarrow> s \<in> \<D> (P \<lbrakk>S'\<rbrakk> Q)\<close> for s
    by (simp add: D_Sync S'_def)
       (metis Un_UNIV_left Un_commute equals0D events_of_is_strict_events_of_or_UNIV
              inf_top.right_neutral sup.orderE superset)
next
  show \<open>s \<in> \<D> (P \<lbrakk>S'\<rbrakk> Q) \<Longrightarrow> s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close> for s
    by (simp add: D_Sync S'_def)
       (metis Un_UNIV_left Un_commute equals0D events_of_is_strict_events_of_or_UNIV
              inf_top.right_neutral sup.orderE superset)
next
  let ?S  = \<open>range tick \<union> ev ` S  :: ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close>
  and ?S' = \<open>range tick \<union> ev ` S' :: ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close>
  fix s X
  assume same_div : \<open>\<D> (P \<lbrakk>S\<rbrakk> Q) = \<D> (P \<lbrakk>S'\<rbrakk> Q)\<close>
  assume \<open>(s, X) \<in> \<F> (P \<lbrakk>S'\<rbrakk> Q)\<close>
  then consider \<open>s \<in> \<D> (P \<lbrakk>S'\<rbrakk> Q)\<close>
    | s_P X_P s_Q X_Q where \<open>(rev s_P, X_P) \<in> \<F> P\<close> \<open>(rev s_Q, X_Q) \<in> \<F> Q\<close>
                            \<open>s setinterleaves ((rev s_P, rev s_Q), ?S')\<close>
                            \<open>X = (X_P \<union> X_Q) \<inter> ?S' \<union> X_P \<inter> X_Q\<close>
    by (simp add: F_Sync D_Sync) (metis rev_rev_ident)
  thus \<open>(s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close>
  proof cases
    from same_div D_F show \<open>s \<in> \<D> (P \<lbrakk>S'\<rbrakk> Q) \<Longrightarrow> (s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close> by blast
  next
    fix s_P s_Q and X_P X_Q :: \<open>('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close>
    let ?X_P' = \<open>X_P \<union> ev ` (- \<alpha>(P))\<close> and ?X_Q' = \<open>X_Q \<union> ev ` (- \<alpha>(Q))\<close>
    assume assms : \<open>(rev s_P, X_P) \<in> \<F> P\<close> \<open>(rev s_Q, X_Q) \<in> \<F> Q\<close>
                   \<open>s setinterleaves ((rev s_P, rev s_Q), ?S')\<close>
                   \<open>X = (X_P \<union> X_Q) \<inter> ?S' \<union> X_P \<inter> X_Q\<close>
    
    from assms(1, 2)[THEN F_T] and assms(3)
    have assms_3_bis : \<open>s setinterleaves ((rev s_P, rev s_Q), ?S)\<close>
    proof (induct \<open>(s_P, ?S, s_Q)\<close> arbitrary: s_P s_Q s rule: setinterleaving.induct)
      case 1
      thus \<open>s setinterleaves ((rev [], rev []), ?S)\<close> by simp
    next
      case (2 y s_Q)
      from "2.prems"(3)[THEN doubleReverse] obtain s' b 
        where * : \<open>y = ev b\<close> \<open>b \<notin> S'\<close> \<open>s = rev (y # s')\<close>
                  \<open>s' setinterleaves (([], s_Q), ?S')\<close>
        by (simp add: image_iff split: if_split_asm) (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust)
      from "2.prems"(2)[unfolded \<open>y = ev b\<close>]
      have \<open>b \<in> \<alpha>(Q)\<close> by (force simp add: events_of_def)
      with \<open>b \<notin> S'\<close> superset have \<open>b \<notin> S\<close> by (simp add: S'_def subset_iff)
      from "2.prems"(2)[simplified, THEN is_processT3_TR] have \<open>rev s_Q \<in> \<T> Q\<close> by auto
      have \<open>y \<notin> ?S\<close> by (simp add: "*"(1) \<open>b \<notin> S\<close> image_iff)
      have \<open>rev s' setinterleaves ((rev [], rev s_Q), ?S)\<close>
        by (fact "2.hyps"[OF \<open>y \<notin> ?S\<close> "2.prems"(1) \<open>rev s_Q \<in> \<T> Q\<close> "*"(4)[THEN doubleReverse]])
      from this[THEN addNonSync, OF \<open>y \<notin> ?S\<close>]
      show \<open>s setinterleaves ((rev [], rev (y # s_Q)), ?S)\<close>
        by (simp add: \<open>s = rev (y # s')\<close>)
    next
      case (3 x s_P)
      from "3.prems"(3)[THEN doubleReverse] obtain s' a 
        where * : \<open>x = ev a\<close> \<open>a \<notin> S'\<close> \<open>s = rev (x # s')\<close>
                  \<open>s' setinterleaves ((s_P, []), ?S')\<close>
        by (simp add: image_iff split: if_split_asm) (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust)
      from "3.prems"(1)[unfolded \<open>x = ev a\<close>]
      have \<open>a \<in> \<alpha>(P)\<close> by (force simp add: events_of_def)
      with \<open>a \<notin> S'\<close> superset have \<open>a \<notin> S\<close> by (simp add: S'_def subset_iff)
      from "3.prems"(1)[simplified, THEN is_processT3_TR] have \<open>rev s_P \<in> \<T> P\<close> by auto
      have \<open>x \<notin> ?S\<close> by (simp add: "*"(1) \<open>a \<notin> S\<close> image_iff)
      have \<open>rev s' setinterleaves ((rev s_P, rev []), ?S)\<close>
        by (fact "3.hyps"[OF \<open>x \<notin> ?S\<close> \<open>rev s_P \<in> \<T> P\<close> "3.prems"(2) "*"(4)[THEN doubleReverse]])
      from this[THEN addNonSync, OF \<open>x \<notin> ?S\<close>]
      show \<open>s setinterleaves ((rev (x # s_P), rev []), ?S)\<close>
        by (simp add: \<open>s = rev (x # s')\<close>)
    next
      case (4 x s_P y s_Q)
      from "4.prems"(1)[simplified, THEN is_processT3_TR] have \<open>rev s_P \<in> \<T> P\<close> by auto
      from "4.prems"(2)[simplified, THEN is_processT3_TR] have \<open>rev s_Q \<in> \<T> Q\<close> by auto
      from "4.prems"(1) have \<open>x \<in> range tick \<union> ev ` \<alpha>(P)\<close>
        by (cases x; force simp add: events_of_def image_iff split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
      from "4.prems"(2) have \<open>y \<in> range tick \<union> ev ` \<alpha>(Q)\<close>
        by (cases y; force simp add: events_of_def image_iff split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
      consider \<open>x \<in> ?S\<close> and \<open>y \<in> ?S\<close> | \<open>x \<in> ?S\<close> and \<open>y \<notin> ?S\<close>
        | \<open>x \<notin> ?S\<close> and \<open>y \<in> ?S\<close> | \<open>x \<notin> ?S\<close> and \<open>y \<notin> ?S\<close> by blast
      thus \<open>s setinterleaves ((rev (x # s_P), rev (y # s_Q)), ?S)\<close>
      proof cases
        assume \<open>x \<in> ?S\<close> and \<open>y \<in> ?S\<close>
        with \<open>x \<in> range tick \<union> ev ` \<alpha>(P)\<close> \<open>y \<in> range tick \<union> ev ` \<alpha>(Q)\<close> superset
        have \<open>x \<in> ?S'\<close> and \<open>y \<in> ?S'\<close> by (auto simp add: S'_def)
        with "4.prems"(3)[THEN doubleReverse] obtain s'
        where * : \<open>x = y\<close> \<open>s = rev (x # s')\<close> \<open>s' setinterleaves ((s_P, s_Q), ?S')\<close>
          by (simp split: if_split_asm) blast

        from "4.hyps"(1)[OF \<open>x \<in> ?S\<close> \<open>y \<in> ?S\<close> \<open>x = y\<close> \<open>rev s_P \<in> \<T> P\<close> \<open>rev s_Q \<in> \<T> Q\<close>
                            \<open>s' setinterleaves ((s_P, s_Q), ?S')\<close>[THEN doubleReverse]]
        have \<open>rev s' setinterleaves ((rev s_P, rev s_Q), ?S)\<close> .
        from this[THEN doubleReverse] \<open>x \<in> ?S\<close>
        have \<open>(x # s') setinterleaves ((x # s_P, x # s_Q), ?S)\<close> by simp
        from this[THEN doubleReverse] show ?case by (simp add: "*"(1, 2))
      next
        assume \<open>x \<in> ?S\<close> and \<open>y \<notin> ?S\<close>
        with \<open>x \<in> range tick \<union> ev ` \<alpha>(P)\<close> \<open>y \<in> range tick \<union> ev ` \<alpha>(Q)\<close> superset
        have \<open>x \<in> ?S'\<close> and \<open>y \<notin> ?S'\<close> by (auto simp add: S'_def)
        with "4.prems"(3)[THEN doubleReverse, simplified] obtain s'
        where * : \<open>s = rev (y # s')\<close> \<open>s' setinterleaves ((x # s_P, s_Q), ?S')\<close>
          by (simp split: if_split_asm) blast
        from "4.hyps"(2)[OF \<open>x \<in> ?S\<close> \<open>y \<notin> ?S\<close> \<open>rev (x # s_P) \<in> \<T> P\<close> \<open>rev s_Q \<in> \<T> Q\<close>
                            \<open>s' setinterleaves ((x # s_P, s_Q), ?S')\<close>[THEN doubleReverse]]
        have \<open>rev s' setinterleaves ((rev (x # s_P), rev s_Q), ?S)\<close> .
        from this[THEN doubleReverse] \<open>x \<in> ?S\<close> \<open>y \<notin> ?S\<close>
        have \<open>(y # s') setinterleaves ((x # s_P, y # s_Q), ?S)\<close> by simp
        from this[THEN doubleReverse] show ?case by (simp add: \<open>s = rev (y # s')\<close>)
      next
        assume \<open>x \<notin> ?S\<close> and \<open>y \<in> ?S\<close>
        with \<open>x \<in> range tick \<union> ev ` \<alpha>(P)\<close> \<open>y \<in> range tick \<union> ev ` \<alpha>(Q)\<close> superset
        have \<open>x \<notin> ?S'\<close> and \<open>y \<in> ?S'\<close> by (auto simp add: S'_def)
        with "4.prems"(3)[THEN doubleReverse] obtain s'
        where * : \<open>s = rev (x # s')\<close> \<open>s' setinterleaves ((s_P, y # s_Q), ?S')\<close>
          by (simp split: if_split_asm) blast
        from "4.hyps"(5)[OF \<open>x \<notin> ?S\<close> _ \<open>rev s_P \<in> \<T> P\<close> \<open>rev (y # s_Q) \<in> \<T> Q\<close>
                            \<open>s' setinterleaves ((s_P, y # s_Q), ?S')\<close>[THEN doubleReverse]] \<open>y \<in> ?S\<close>
        have \<open>rev s' setinterleaves ((rev s_P, rev (y # s_Q)), ?S)\<close> by simp
        from this[THEN doubleReverse] \<open>x \<notin> ?S\<close> \<open>y \<in> ?S\<close>
        have \<open>(x # s') setinterleaves ((x # s_P, y # s_Q), ?S)\<close> by simp
        from this[THEN doubleReverse] show ?case by (simp add: \<open>s = rev (x # s')\<close>)
      next
        assume \<open>x \<notin> ?S\<close> and \<open>y \<notin> ?S\<close>
        with \<open>x \<in> range tick \<union> ev ` \<alpha>(P)\<close> \<open>y \<in> range tick \<union> ev ` \<alpha>(Q)\<close>
        have \<open>x \<notin> ?S'\<close> and \<open>y \<notin> ?S'\<close> by (auto simp add: S'_def)
        with "4.prems"(3)[THEN doubleReverse, simplified] consider
          s' where \<open>s = rev (x # s')\<close> \<open>s' setinterleaves ((s_P, y # s_Q), ?S')\<close>
        | s' where \<open>s = rev (y # s')\<close> \<open>s' setinterleaves ((x # s_P, s_Q), ?S')\<close>
          by (simp split: if_split_asm) blast
        thus ?case
        proof cases
          fix s' assume \<open>s = rev (x # s')\<close> \<open>s' setinterleaves ((s_P, y # s_Q), ?S')\<close>
          from "4.hyps"(3)[OF \<open>x \<notin> ?S\<close> \<open>y \<notin> ?S\<close> \<open>rev s_P \<in> \<T> P\<close> \<open>rev (y # s_Q) \<in> \<T> Q\<close>
                              \<open>s' setinterleaves ((s_P, y # s_Q), ?S')\<close>[THEN doubleReverse]]
          have \<open>rev s' setinterleaves ((rev s_P, rev (y # s_Q)), ?S)\<close> .
          from this[THEN doubleReverse] \<open>x \<notin> ?S\<close> \<open>y \<notin> ?S\<close>
          have \<open>(x # s') setinterleaves ((x # s_P, y # s_Q), ?S)\<close> by simp
          from this[THEN doubleReverse] show ?case by (simp add: \<open>s = rev (x # s')\<close>)
        next
          fix s' assume \<open>s = rev (y # s')\<close> \<open>s' setinterleaves ((x # s_P, s_Q), ?S')\<close>
          from "4.hyps"(4)[OF \<open>x \<notin> ?S\<close> \<open>y \<notin> ?S\<close> \<open>rev (x # s_P) \<in> \<T> P\<close> \<open>rev s_Q \<in> \<T> Q\<close>
                              \<open>s' setinterleaves ((x # s_P, s_Q), ?S')\<close>[THEN doubleReverse]]
          have \<open>rev s' setinterleaves ((rev (x # s_P), rev s_Q), ?S)\<close> .
          from this[THEN doubleReverse] \<open>x \<notin> ?S\<close> \<open>y \<notin> ?S\<close>
          have \<open>(y # s') setinterleaves ((x # s_P, y # s_Q), ?S)\<close> by simp
          from this[THEN doubleReverse] show ?case by (simp add: \<open>s = rev (y # s')\<close>)
        qed
      qed
    qed
  
    from add_complementary_events_of_in_failure[OF assms(1)]
    have \<open>(rev s_P, ?X_P') \<in> \<F> P\<close> .
    moreover from add_complementary_events_of_in_failure[OF assms(2)]
    have \<open>(rev s_Q, ?X_Q') \<in> \<F> Q\<close> .
    ultimately have \<open>(s, (?X_P' \<union> ?X_Q') \<inter> ?S \<union> ?X_P' \<inter> ?X_Q') \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close>
      using assms_3_bis by (simp add: F_Sync) blast
    moreover have \<open>X \<subseteq> (?X_P' \<union> ?X_Q') \<inter> ?S \<union> ?X_P' \<inter> ?X_Q'\<close>
      by (auto simp add: assms(4) S'_def image_iff)
    ultimately show \<open>(s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close> by (rule is_processT4)
  qed
next
  let ?S  = \<open>range tick \<union> ev ` S  :: ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close>
  and ?S' = \<open>range tick \<union> ev ` S' :: ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close>
  fix s X
  assume same_div : \<open>\<D> (P \<lbrakk>S\<rbrakk> Q) = \<D> (P \<lbrakk>S'\<rbrakk> Q)\<close>
  assume \<open>(s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close>
  then consider \<open>s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
    | s_P X_P s_Q X_Q where \<open>(rev s_P, X_P) \<in> \<F> P\<close> \<open>(rev s_Q, X_Q) \<in> \<F> Q\<close>
                            \<open>s setinterleaves ((rev s_P, rev s_Q), ?S)\<close>
                            \<open>X = (X_P \<union> X_Q) \<inter> ?S \<union> X_P \<inter> X_Q\<close>
    by (simp add: F_Sync D_Sync) (metis rev_rev_ident)
  thus \<open>(s, X) \<in> \<F> (P \<lbrakk>S'\<rbrakk> Q)\<close>
  proof cases
    from same_div D_F show \<open>s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q) \<Longrightarrow> (s, X) \<in> \<F> (P \<lbrakk>S'\<rbrakk> Q)\<close> by blast
  next
    fix s_P s_Q and X_P X_Q :: \<open>('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set\<close>
    let ?X_P' = \<open>X_P \<union> ev ` (- \<alpha>(P))\<close> and ?X_Q' = \<open>X_Q \<union> ev ` (- \<alpha>(Q))\<close>
    assume assms : \<open>(rev s_P, X_P) \<in> \<F> P\<close> \<open>(rev s_Q, X_Q) \<in> \<F> Q\<close>
                   \<open>s setinterleaves ((rev s_P, rev s_Q), ?S)\<close>
                   \<open>X = (X_P \<union> X_Q) \<inter> ?S \<union> X_P \<inter> X_Q\<close>
    
    from assms(1, 2)[THEN F_T] and assms(3)
    have assms_3_bis : \<open>s setinterleaves ((rev s_P, rev s_Q), ?S')\<close>
    proof (induct \<open>(s_P, ?S', s_Q)\<close> arbitrary: s_P s_Q s rule: setinterleaving.induct)
      case 1
      thus \<open>s setinterleaves ((rev [], rev []), ?S')\<close> by simp
    next
      case (2 y s_Q)
      from "2.prems"(3)[THEN doubleReverse] obtain s' b 
        where * : \<open>y = ev b\<close> \<open>b \<notin> S\<close> \<open>s = rev (y # s')\<close>
                  \<open>s' setinterleaves (([], s_Q), ?S)\<close>
        by (simp add: image_iff split: if_split_asm) (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust)
      from "2.prems"(2)[unfolded \<open>y = ev b\<close>]
      have \<open>b \<in> \<alpha>(Q)\<close> by (force simp add: events_of_def)
      with \<open>b \<notin> S\<close> have \<open>b \<notin> S'\<close> by (simp add: S'_def)
      from "2.prems"(2)[simplified, THEN is_processT3_TR] have \<open>rev s_Q \<in> \<T> Q\<close> by auto
      have \<open>y \<notin> ?S'\<close> by (simp add: "*"(1) \<open>b \<notin> S'\<close> image_iff)
      have \<open>rev s' setinterleaves ((rev [], rev s_Q), ?S')\<close>
        by (fact "2.hyps"[OF \<open>y \<notin> ?S'\<close> "2.prems"(1) \<open>rev s_Q \<in> \<T> Q\<close> "*"(4)[THEN doubleReverse]])
      from this[THEN addNonSync, OF \<open>y \<notin> ?S'\<close>]
      show \<open>s setinterleaves ((rev [], rev (y # s_Q)), ?S')\<close>
        by (simp add: \<open>s = rev (y # s')\<close>)
    next
      case (3 x s_P)
      from "3.prems"(3)[THEN doubleReverse] obtain s' a 
        where * : \<open>x = ev a\<close> \<open>a \<notin> S\<close> \<open>s = rev (x # s')\<close>
                  \<open>s' setinterleaves ((s_P, []), ?S)\<close>
        by (simp add: image_iff split: if_split_asm) (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust)
      from "3.prems"(1)[unfolded \<open>x = ev a\<close>]
      have \<open>a \<in> \<alpha>(P)\<close> by (force simp add: events_of_def)
      with \<open>a \<notin> S\<close> have \<open>a \<notin> S'\<close> by (simp add: S'_def)
      from "3.prems"(1)[simplified, THEN is_processT3_TR] have \<open>rev s_P \<in> \<T> P\<close> by auto
      have \<open>x \<notin> ?S'\<close> by (simp add: "*"(1) \<open>a \<notin> S'\<close> image_iff)
      have \<open>rev s' setinterleaves ((rev s_P, rev []), ?S')\<close>
        by (fact "3.hyps"[OF \<open>x \<notin> ?S'\<close> \<open>rev s_P \<in> \<T> P\<close> "3.prems"(2) "*"(4)[THEN doubleReverse]])
      from this[THEN addNonSync, OF \<open>x \<notin> ?S'\<close>]
      show \<open>s setinterleaves ((rev (x # s_P), rev []), ?S')\<close>
        by (simp add: \<open>s = rev (x # s')\<close>)
    next
      case (4 x s_P y s_Q)
      from "4.prems"(1)[simplified, THEN is_processT3_TR] have \<open>rev s_P \<in> \<T> P\<close> by auto
      from "4.prems"(2)[simplified, THEN is_processT3_TR] have \<open>rev s_Q \<in> \<T> Q\<close> by auto
      from "4.prems"(1) have \<open>x \<in> range tick \<union> ev ` \<alpha>(P)\<close>
        by (cases x; force simp add: events_of_def image_iff split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
      from "4.prems"(2) have \<open>y \<in> range tick \<union> ev ` \<alpha>(Q)\<close>
        by (cases y; force simp add: events_of_def image_iff split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
      consider \<open>x \<in> ?S'\<close> and \<open>y \<in> ?S'\<close> | \<open>x \<in> ?S'\<close> and \<open>y \<notin> ?S'\<close>
        | \<open>x \<notin> ?S'\<close> and \<open>y \<in> ?S'\<close> | \<open>x \<notin> ?S'\<close> and \<open>y \<notin> ?S'\<close> by blast
      thus \<open>s setinterleaves ((rev (x # s_P), rev (y # s_Q)), ?S')\<close>
      proof cases
        assume \<open>x \<in> ?S'\<close> and \<open>y \<in> ?S'\<close>
        with \<open>x \<in> range tick \<union> ev ` \<alpha>(P)\<close> \<open>y \<in> range tick \<union> ev ` \<alpha>(Q)\<close>
        have \<open>x \<in> ?S\<close> and \<open>y \<in> ?S\<close> by (auto simp add: S'_def)
        with "4.prems"(3)[THEN doubleReverse] obtain s'
        where * : \<open>x = y\<close> \<open>s = rev (x # s')\<close> \<open>s' setinterleaves ((s_P, s_Q), ?S)\<close>
          by (simp split: if_split_asm) blast

        from "4.hyps"(1)[OF \<open>x \<in> ?S'\<close> \<open>y \<in> ?S'\<close> \<open>x = y\<close> \<open>rev s_P \<in> \<T> P\<close> \<open>rev s_Q \<in> \<T> Q\<close>
                            \<open>s' setinterleaves ((s_P, s_Q), ?S)\<close>[THEN doubleReverse]]
        have \<open>rev s' setinterleaves ((rev s_P, rev s_Q), ?S')\<close> .
        from this[THEN doubleReverse] \<open>x \<in> ?S'\<close>
        have \<open>(x # s') setinterleaves ((x # s_P, x # s_Q), ?S')\<close> by simp
        from this[THEN doubleReverse] show ?case by (simp add: "*"(1, 2))
      next
        assume \<open>x \<in> ?S'\<close> and \<open>y \<notin> ?S'\<close>
        with \<open>x \<in> range tick \<union> ev ` \<alpha>(P)\<close> \<open>y \<in> range tick \<union> ev ` \<alpha>(Q)\<close> superset
        have \<open>x \<in> ?S\<close> and \<open>y \<notin> ?S\<close> by (auto simp add: S'_def)
        with "4.prems"(3)[THEN doubleReverse, simplified] obtain s'
        where * : \<open>s = rev (y # s')\<close> \<open>s' setinterleaves ((x # s_P, s_Q), ?S)\<close>
          by (simp split: if_split_asm) blast
        from "4.hyps"(2)[OF \<open>x \<in> ?S'\<close> \<open>y \<notin> ?S'\<close> \<open>rev (x # s_P) \<in> \<T> P\<close> \<open>rev s_Q \<in> \<T> Q\<close>
                            \<open>s' setinterleaves ((x # s_P, s_Q), ?S)\<close>[THEN doubleReverse]]
        have \<open>rev s' setinterleaves ((rev (x # s_P), rev s_Q), ?S')\<close> .
        from this[THEN doubleReverse] \<open>x \<in> ?S'\<close> \<open>y \<notin> ?S'\<close>
        have \<open>(y # s') setinterleaves ((x # s_P, y # s_Q), ?S')\<close> by simp
        from this[THEN doubleReverse] show ?case by (simp add: \<open>s = rev (y # s')\<close>)
      next
        assume \<open>x \<notin> ?S'\<close> and \<open>y \<in> ?S'\<close>
        with \<open>x \<in> range tick \<union> ev ` \<alpha>(P)\<close> \<open>y \<in> range tick \<union> ev ` \<alpha>(Q)\<close> superset
        have \<open>x \<notin> ?S\<close> and \<open>y \<in> ?S\<close> by (auto simp add: S'_def)
        with "4.prems"(3)[THEN doubleReverse] obtain s'
        where * : \<open>s = rev (x # s')\<close> \<open>s' setinterleaves ((s_P, y # s_Q), ?S)\<close>
          by (simp split: if_split_asm) blast
        from "4.hyps"(5)[OF \<open>x \<notin> ?S'\<close> _ \<open>rev s_P \<in> \<T> P\<close> \<open>rev (y # s_Q) \<in> \<T> Q\<close>
                            \<open>s' setinterleaves ((s_P, y # s_Q), ?S)\<close>[THEN doubleReverse]] \<open>y \<in> ?S'\<close>
        have \<open>rev s' setinterleaves ((rev s_P, rev (y # s_Q)), ?S')\<close> by simp
        from this[THEN doubleReverse] \<open>x \<notin> ?S'\<close> \<open>y \<in> ?S'\<close>
        have \<open>(x # s') setinterleaves ((x # s_P, y # s_Q), ?S')\<close> by simp
        from this[THEN doubleReverse] show ?case by (simp add: \<open>s = rev (x # s')\<close>)
      next
        assume \<open>x \<notin> ?S'\<close> and \<open>y \<notin> ?S'\<close>
        with \<open>x \<in> range tick \<union> ev ` \<alpha>(P)\<close> \<open>y \<in> range tick \<union> ev ` \<alpha>(Q)\<close> superset
        have \<open>x \<notin> ?S\<close> and \<open>y \<notin> ?S\<close> by (auto simp add: S'_def)
        with "4.prems"(3)[THEN doubleReverse, simplified] consider
          s' where \<open>s = rev (x # s')\<close> \<open>s' setinterleaves ((s_P, y # s_Q), ?S)\<close>
        | s' where \<open>s = rev (y # s')\<close> \<open>s' setinterleaves ((x # s_P, s_Q), ?S)\<close>
          by (simp split: if_split_asm) blast
        thus ?case
        proof cases
          fix s' assume \<open>s = rev (x # s')\<close> \<open>s' setinterleaves ((s_P, y # s_Q), ?S)\<close>
          from "4.hyps"(3)[OF \<open>x \<notin> ?S'\<close> \<open>y \<notin> ?S'\<close> \<open>rev s_P \<in> \<T> P\<close> \<open>rev (y # s_Q) \<in> \<T> Q\<close>
                              \<open>s' setinterleaves ((s_P, y # s_Q), ?S)\<close>[THEN doubleReverse]]
          have \<open>rev s' setinterleaves ((rev s_P, rev (y # s_Q)), ?S')\<close> .
          from this[THEN doubleReverse] \<open>x \<notin> ?S'\<close> \<open>y \<notin> ?S'\<close>
          have \<open>(x # s') setinterleaves ((x # s_P, y # s_Q), ?S')\<close> by simp
          from this[THEN doubleReverse] show ?case by (simp add: \<open>s = rev (x # s')\<close>)
        next
          fix s' assume \<open>s = rev (y # s')\<close> \<open>s' setinterleaves ((x # s_P, s_Q), ?S)\<close>
          from "4.hyps"(4)[OF \<open>x \<notin> ?S'\<close> \<open>y \<notin> ?S'\<close> \<open>rev (x # s_P) \<in> \<T> P\<close> \<open>rev s_Q \<in> \<T> Q\<close>
                              \<open>s' setinterleaves ((x # s_P, s_Q), ?S)\<close>[THEN doubleReverse]]
          have \<open>rev s' setinterleaves ((rev (x # s_P), rev s_Q), ?S')\<close> .
          from this[THEN doubleReverse] \<open>x \<notin> ?S'\<close> \<open>y \<notin> ?S'\<close>
          have \<open>(y # s') setinterleaves ((x # s_P, y # s_Q), ?S')\<close> by simp
          from this[THEN doubleReverse] show ?case by (simp add: \<open>s = rev (y # s')\<close>)
        qed
      qed
    qed
  
    from add_complementary_events_of_in_failure[OF assms(1)]
    have \<open>(rev s_P, ?X_P') \<in> \<F> P\<close> .
    moreover from add_complementary_events_of_in_failure[OF assms(2)]
    have \<open>(rev s_Q, ?X_Q') \<in> \<F> Q\<close> .
    ultimately have \<open>(s, (?X_P' \<union> ?X_Q') \<inter> ?S' \<union> ?X_P' \<inter> ?X_Q') \<in> \<F> (P \<lbrakk>S'\<rbrakk> Q)\<close>
      using assms_3_bis by (simp add: F_Sync) blast
    moreover from superset have \<open>X \<subseteq> (?X_P' \<union> ?X_Q') \<inter> ?S' \<union> ?X_P' \<inter> ?X_Q'\<close>
      by (auto simp add: assms(4) S'_def image_iff)
    ultimately show \<open>(s, X) \<in> \<F> (P \<lbrakk>S'\<rbrakk> Q)\<close> by (rule is_processT4)
  qed
qed

corollary Sync_is_Sync_restricted_events : \<open>P \<lbrakk>S\<rbrakk> Q = P \<lbrakk>S \<inter> (\<alpha>(P) \<union> \<alpha>(Q))\<rbrakk> Q\<close>
  by (simp add: Sync_is_Sync_restricted_superset_events)

text \<open>This version is closer to the intuition that we may have, but the first one would be more
useful if we don't want to compute the events of a process but know a superset approximation.\<close>


(* lemma Sync_with_SKIP_eq_itself_if_disjoint_events:
  \<open>\<alpha>(P) \<inter> S = {} \<Longrightarrow> P \<lbrakk>S\<rbrakk> SKIP r = P\<close>
  oops
  by (metis Int_commute Inter_SKIP Sync_is_Sync_restricted_events events_Inter)

lemma Sync_with_STOP_eq_itself_Seq_STOP_if_disjoint_events:
  \<open>\<alpha>(P) \<inter> S = {} \<Longrightarrow> P \<lbrakk>S\<rbrakk> STOP = P \<^bold>; (\<lambda>r. STOP)\<close>
  oops
  by (metis Int_Un_eq(3) Int_commute Inter_STOP_Seq_STOP Sync_is_Sync_restricted_events events_STOP) *)


corollary \<open>deadlock_free P \<Longrightarrow> deadlock_free Q \<Longrightarrow>
           S \<inter> (\<alpha>(P) \<union> \<alpha>(Q)) = {} \<Longrightarrow> deadlock_free (P \<lbrakk>S\<rbrakk> Q)\<close>
  by (subst Sync_is_Sync_restricted_events) (simp add: Inter_deadlock_free)
    (* but we already had this with data_independence_deadlock_free_Sync *)






section \<open>Powerful Results about \<^const>\<open>Renaming\<close>\<close>

text \<open>In this section we will provide laws about the \<^const>\<open>Renaming\<close> operator.
      In the first subsection we will give slight generalizations of previous results,
      but in the other we prove some very powerful theorems.\<close>

subsection \<open>Some Generalizations\<close>

text \<open>For \<^const>\<open>Renaming\<close>, we can obtain generalizations of the following results:

      @{thm Renaming_Mprefix[no_vars] Renaming_Mndetprefix[no_vars]}\<close>



lemma Renaming_Mprefix_Sliding:
  \<open>Renaming ((\<box>a \<in> A \<rightarrow> P a) \<rhd> Q) f g = 
   (\<box>y \<in> f ` A \<rightarrow> \<sqinter>a \<in> {x \<in> A. y = f x}. Renaming (P a) f g) \<rhd> Renaming Q f g\<close>
  unfolding Sliding_def
  by (simp add: Renaming_Det Renaming_distrib_Ndet Renaming_Mprefix)





subsection \<open>\<^const>\<open>Renaming\<close> and \<^const>\<open>Hiding\<close>\<close>

text \<open>When \<^term>\<open>f\<close> is one to one, \<^term>\<open>Renaming (P \ S) f\<close> will behave like we expect it to do.\<close>

lemma strict_mono_map: \<open>strict_mono g \<Longrightarrow> strict_mono (\<lambda>i. map f (g i))\<close>
  unfolding strict_mono_def less_eq_list_def less_list_def prefix_def by fastforce



lemma trace_hide_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>inj_on (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (set s \<union> ev ` S) \<Longrightarrow>
   trace_hide (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s) (ev ` f ` S) = 
   map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (trace_hide s (ev ` S))\<close>
proof (induct s)
  case Nil
  show ?case by simp
next
  case (Cons e s)
  hence * : \<open>trace_hide (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s) (ev ` f ` S) = 
             map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (trace_hide s (ev ` S))\<close> by fastforce
  from Cons.prems[unfolded inj_on_def, rule_format, of e, simplified] show ?case
    by (simp add: "*", simp add: image_iff split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
       (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(9))
qed
  


theorem bij_Renaming_Hiding: \<open>Renaming (P \ S) f g = Renaming P f g \ f ` S\<close>
  (is \<open>?lhs = ?rhs\<close>) if bij_f: \<open>bij f\<close> and bij_g : \<open>bij g\<close>
proof -
  have inj_on_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : \<open>inj_on (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) X\<close> for X
    by (metis bij_betw_imp_inj_on bij_f bij_g event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inj_map inj_eq inj_onI)
  have inj_on_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inv : \<open>inj_on (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (inv f) (inv g)) X\<close> for X
    by (metis bij_betw_def bij_f bij_g event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inj_map inj_on_inverseI inv_f_eq surj_imp_inj_inv)
  show \<open>?lhs = ?rhs\<close>
  proof (subst Process_eq_spec_optimized, safe)
    fix s
    assume \<open>s \<in> \<D> ?lhs\<close>
    then obtain s1 s2 where * : \<open>tF s1\<close> \<open>ftF s2\<close>
                                \<open>s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1 @ s2\<close> \<open>s1 \<in> \<D> (P \ S)\<close>
      by (simp add: D_Renaming) blast
    from "*"(4) obtain t u
      where ** : \<open>ftF u\<close> \<open>tF t\<close> \<open>s1 = trace_hide t (ev ` S) @ u\<close>
                 \<open>t \<in> \<D> P \<or> (\<exists>g. isInfHiddenRun g P S \<and> t \<in> range g)\<close>
      by (simp add: D_Hiding) blast
    from "**"(4) show \<open>s \<in> \<D> ?rhs\<close>
    proof (elim disjE)
      assume \<open>t \<in> \<D> P\<close>
      hence \<open>ftF (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u @ s2) \<and> tF (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t) \<and>
             s = trace_hide (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t) (ev ` f ` S) @ map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u @ s2 \<and>
             map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t \<in> \<D> (Renaming P f g)\<close>
        apply (simp add: "*"(3) "**"(2, 3) map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree, intro conjI)
          apply (metis "*"(1, 2) "**"(1) "**"(3) front_tickFree_append_iff
                       map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_front_tickFree map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree tickFree_append_iff)
         apply (rule trace_hide_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[symmetric])
         apply (meson inj_def inj_onCI inj_on_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        apply (simp add: D_Renaming)
        using "**"(2) front_tickFree_Nil by blast
      thus \<open>s \<in> \<D> ?rhs\<close> by (simp add: D_Hiding) blast
    next
      assume \<open>\<exists>h. isInfHiddenRun h P S \<and> t \<in> range h\<close>
      then obtain h where \<open>isInfHiddenRun h P S\<close> \<open>t \<in> range h\<close> by blast
      hence \<open>ftF (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u @ s2) \<and>
             tF (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t) \<and>
             s = trace_hide (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t) (ev ` f ` S) @ map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u @ s2 \<and>
             isInfHiddenRun (\<lambda>i. map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (h i)) (Renaming P f g) (f ` S) \<and> 
             map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t \<in> range (\<lambda>i. map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (h i))\<close>
        apply (simp add: "*"(3) "**"(2, 3) map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree, intro conjI)
             apply (metis "*"(1, 2) "**"(3) front_tickFree_append map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree tickFree_append_iff)
            apply (rule trace_hide_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF inj_on_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, symmetric])
           apply (solves \<open>rule strict_mono_map, simp\<close>)
          apply (solves \<open>auto simp add: T_Renaming\<close>)
         apply (subst (1 2) trace_hide_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF inj_on_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k])
        by metis blast
      thus \<open>s \<in> \<D> ?rhs\<close> by (simp add: D_Hiding) blast
    qed
  next
    fix s
    assume \<open>s \<in> \<D> ?rhs\<close>
    then obtain t u
      where * : \<open>ftF u\<close> \<open>tF t\<close> \<open>s = trace_hide t (ev ` f ` S) @ u\<close>
                \<open>t \<in> \<D> (Renaming P f g) \<or> 
                 (\<exists>h. isInfHiddenRun h (Renaming P f g) (f ` S) \<and> t \<in> range h)\<close>
      by (simp add: D_Hiding) blast
    from "*"(4) show \<open>s \<in> \<D> ?lhs\<close>
    proof (elim disjE)
      assume \<open>t \<in> \<D> (Renaming P f g)\<close>
      then obtain t1 t2 where ** : \<open>tF t1\<close> \<open>ftF t2\<close> 
                                   \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1 @ t2\<close> \<open>t1 \<in> \<D> P\<close>
        by (simp add: D_Renaming) blast
      have \<open>tF (trace_hide t1 (ev ` S)) \<and> 
            ftF (trace_hide t2 (ev ` f ` S) @ u) \<and>
            trace_hide (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1) (ev ` f ` S) @ trace_hide t2 (ev ` f ` S) @ u =
            map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (trace_hide t1 (ev ` S)) @ trace_hide t2 (ev ` f ` S) @ u \<and>
            trace_hide t1 (ev ` S) \<in> \<D> (P \ S)\<close>
        apply (simp, intro conjI)
        using "**"(1) Hiding_tickFree apply blast
        using "*"(1, 2) "**"(3) Hiding_tickFree front_tickFree_append tickFree_append_iff apply blast
         apply (rule trace_hide_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF inj_on_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k])
        using "**"(4) mem_D_imp_mem_D_Hiding by blast
      thus \<open>s \<in> \<D> ?lhs\<close> by (simp add: D_Renaming "*"(3) "**"(3)) blast
    next
      have inv_S: \<open>S = inv f ` f ` S\<close> by (simp add: bij_is_inj bij_f)
      have inj_inv_f: \<open>inj (inv f)\<close> 
        by (simp add: bij_imp_bij_inv bij_is_inj bij_f)
      have ** : \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (inv f) (inv g) \<circ> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) v = v\<close> for v
        by (induct v, simp_all)
           (metis UNIV_I bij_betw_inv_into_left bij_f bij_g event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.map(2) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(9))
      assume \<open>\<exists>h. isInfHiddenRun h (Renaming P f g) (f ` S) \<and> t \<in> range h\<close>
      then obtain h
        where *** : \<open>isInfHiddenRun h (Renaming P f g) (f ` S)\<close> \<open>t \<in> range h\<close> by blast
      then consider t1 where \<open>t1 \<in> \<T> P\<close> \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1\<close>
        | t1 t2 where \<open>tF t1\<close> \<open>ftF t2\<close> 
                      \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1 @ t2\<close> \<open>t1 \<in> \<D> P\<close>
        by (simp add: T_Renaming) blast
      thus \<open>s \<in> \<D> ?lhs\<close>
      proof cases
        fix t1 assume **** : \<open>t1 \<in> \<T> P\<close> \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1\<close>
        have ***** : \<open>t1 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (inv f) (inv g)) t\<close> by (simp add: "****"(2) "**")
        have ****** : \<open>trace_hide t1 (ev ` S) = trace_hide t1 (ev ` S) \<and>
                       isInfHiddenRun (\<lambda>i. map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (inv f) (inv g)) (h i)) P S \<and> 
                       t1 \<in> range (\<lambda>i. map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (inv f) (inv g)) (h i))\<close>
          apply (simp add: "***"(1) strict_mono_map, intro conjI)
            apply (subst Renaming_inv[where f = f and g = g, symmetric])
              apply (solves \<open>simp add: bij_is_inj bij_f\<close>)
             apply (solves \<open>simp add: bij_is_inj bij_g\<close>)

          using "***"(1) apply (subst T_Renaming, blast)
           apply (subst (1 2) inv_S, subst (1 2) trace_hide_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF inj_on_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inv])
           apply (metis "***"(1))
          using "***"(2) "*****" by blast
        have \<open>tF (trace_hide t1 (ev ` S)) \<and> ftF t1 \<and>
              trace_hide (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1) (ev ` f ` S) @ u = 
              map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (trace_hide t1 (ev ` S)) @ u \<and> 
              trace_hide t1 (ev ` S) \<in> \<D> (P \ S)\<close>
          apply (simp, intro conjI)
          using "*"(2) "****"(2) map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree Hiding_tickFree apply blast
          using "****"(1) is_processT2_TR apply blast
          apply (rule trace_hide_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF inj_on_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k])
          apply (simp add: D_Renaming D_Hiding)
          using "*"(2) "*****" "******" map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree front_tickFree_Nil by blast
        with "*"(1) show \<open>s \<in> \<D> ?lhs\<close> by (simp add: D_Renaming "*"(3) "****"(2)) blast
      next
        fix t1 t2 assume **** : \<open>tF t1\<close> \<open>ftF t2\<close>
                                \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1 @ t2\<close> \<open>t1 \<in> \<D> P\<close>
        have \<open>tF (trace_hide t1 (ev ` S)) \<and>
              ftF (trace_hide t2 (ev ` f ` S) @ u) \<and>
              trace_hide (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1) (ev ` f ` S) @ trace_hide t2 (ev ` f ` S) @ u =
              map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (trace_hide t1 (ev ` S)) @ trace_hide t2 (ev ` f ` S) @ u \<and>
              trace_hide t1 (ev ` S) \<in> \<D> (P \ S)\<close>
          apply (simp, intro conjI)
          using "****"(1) Hiding_tickFree apply blast
          using "*"(1, 2) "****"(3) Hiding_tickFree front_tickFree_append tickFree_append_iff apply blast
           apply (rule trace_hide_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF inj_on_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k])
          using "****"(4) mem_D_imp_mem_D_Hiding by blast
        thus \<open>s \<in> \<D> ?lhs\<close> by (simp add: D_Renaming "*"(3) "****"(3)) blast
      qed
    qed
  next
    fix s X
    assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
    assume \<open>(s, X) \<in> \<F> ?lhs\<close>
    then consider \<open>s \<in> \<D> ?lhs\<close>
      | s1 where \<open>(s1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (P \ S)\<close> \<open>s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1\<close>
      by (simp add: F_Renaming D_Renaming) blast
    thus \<open>(s, X) \<in> \<F> ?rhs\<close>
    proof cases
      from D_F same_div show \<open>s \<in> \<D> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> by blast
    next
      fix s1 assume * : \<open>(s1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (P \ S)\<close>
                        \<open>s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1\<close>
      from this(1) consider \<open>s1 \<in> \<D> (P \ S)\<close>
        | t where \<open>s1 = trace_hide t (ev ` S)\<close> \<open>(t, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X \<union> ev ` S) \<in> \<F> P\<close>
        by (simp add: F_Hiding D_Hiding) blast
      thus \<open>(s, X) \<in> \<F> ?rhs\<close>
      proof cases
        assume \<open>s1 \<in> \<D> (P \ S)\<close>
        then obtain t u
          where ** : \<open>ftF u\<close> \<open>tF t\<close> \<open>s1 = trace_hide t (ev ` S) @ u\<close>
                     \<open>t \<in> \<D> P \<or> (\<exists>g. isInfHiddenRun g P S \<and> t \<in> range g)\<close>
          by (simp add: D_Hiding) blast
        have *** : \<open>ftF (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u) \<and> tF (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t) \<and>
                    map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (trace_hide t (ev ` S)) @ map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u = 
                    trace_hide (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t) (ev ` f ` S) @ (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u)\<close>
          by (simp add: map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_front_tickFree map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree "**"(1, 2))
             (rule trace_hide_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF inj_on_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, symmetric])
        from "**"(4) show \<open>(s, X) \<in> \<F> ?rhs\<close>
        proof (elim disjE exE)
          assume \<open>t \<in> \<D> P\<close>
          hence $ : \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t \<in> \<D> (Renaming P f g)\<close>
            apply (simp add: D_Renaming)
            using "**"(2) front_tickFree_Nil by blast
          show \<open>(s, X) \<in> \<F> ?rhs\<close>
            by (simp add: F_Hiding) (metis "$" "*"(2) "**"(3) "***" map_append)
        next
          fix h assume \<open>isInfHiddenRun h P S \<and> t \<in> range h\<close>
          hence $ : \<open>isInfHiddenRun (\<lambda>i. map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (h i)) (Renaming P f g) (f ` S) \<and> 
                     map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t \<in> range (\<lambda>i. map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (h i))\<close>
            apply (subst (1 2) trace_hide_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF inj_on_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k])
            by (simp add: strict_mono_map T_Renaming image_iff) (metis (mono_tags, lifting))
          show \<open>(s, X) \<in> \<F> ?rhs\<close>
            apply (simp add: F_Hiding)
            (* TODO: break this smt *)
            by (smt (verit, del_insts) "$" "*"(2) "**"(3) "***" map_append)
        qed
      next
        fix t assume ** : \<open>s1 = trace_hide t (ev ` S)\<close> 
                          \<open>(t, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X \<union> ev ` S) \<in> \<F> P\<close>
        have *** : \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X \<union> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` ev ` f ` S = map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X \<union> ev ` S\<close>
          by (simp add: set_eq_iff map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_ev_iff image_iff) (metis bij_f bij_pointE)
        have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (trace_hide t (ev ` S)) = 
              trace_hide (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t) (ev ` f ` S) \<and>
              (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t, X \<union> ev ` f ` S) \<in> \<F> (Renaming P f g)\<close>
          apply (intro conjI)
           apply (rule trace_hide_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF inj_on_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, symmetric])
          apply (simp add: F_Renaming)
          using "**"(2) "***" by auto
        show \<open>(s, X) \<in> \<F> ?rhs\<close>
          apply (simp add: F_Hiding "*"(2) "**"(1))
          using \<open>?this\<close> by blast
      qed
    qed
  next
    fix s X
    assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
    assume \<open>(s, X) \<in> \<F> ?rhs\<close>
    then consider \<open>s \<in> \<D> ?rhs\<close>
      | t where \<open>s = trace_hide t (ev ` f ` S)\<close> \<open>(t, X \<union> ev ` f ` S) \<in> \<F> (Renaming P f g)\<close>
      by (simp add: F_Hiding D_Hiding) blast
    thus \<open>(s, X) \<in> \<F> ?lhs\<close>
    proof cases
      from D_F same_div show \<open>s \<in> \<D> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> by blast
    next
      fix t assume \<open>s = trace_hide t (ev ` f ` S)\<close> \<open>(t, X \<union> ev ` f ` S) \<in> \<F> (Renaming P f g)\<close>
      then obtain t
        where * : \<open>s = trace_hide t (ev ` f ` S)\<close>
                  \<open>(t, X \<union> ev ` f ` S) \<in> \<F> (Renaming P f g)\<close> by blast
      have ** : \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X \<union> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` ev ` f ` S = map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X \<union> ev ` S\<close>
          by (simp add: set_eq_iff map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_ev_iff image_iff) (metis bij_f bij_pointE)
      have \<open>(\<exists>s1. (s1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X \<union> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` ev ` f ` S) \<in> \<F> P \<and> t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1) \<or> 
            (\<exists>s1 s2. tF s1 \<and> ftF s2 \<and> t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1 @ s2 \<and> s1 \<in> \<D> P)\<close>
        using "*"(2) by (auto simp add: F_Renaming)
      thus \<open>(s, X) \<in> \<F> ?lhs\<close>
      proof (elim disjE exE conjE)
        fix s1
        assume \<open>(s1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X \<union> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` ev ` f ` S) \<in> \<F> P\<close> \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1\<close>
        hence \<open>(trace_hide s1 (ev ` S), map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (P \ S) \<and>
               s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (trace_hide s1 (ev ` S))\<close>
          apply (simp add: "*"(1) F_Hiding "**", intro conjI)
          by blast (rule trace_hide_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF inj_on_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k])
        show \<open>(s, X) \<in> \<F> ?lhs\<close>
          apply (simp add: F_Renaming)
          using \<open>?this\<close> by blast
      next
        fix s1 s2
        assume \<open>tF s1\<close> \<open>ftF s2\<close> \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1 @ s2\<close> \<open>s1 \<in> \<D> P\<close>
        hence \<open>tF (trace_hide s1 (ev ` S)) \<and> 
               ftF (trace_hide s2 (ev ` f ` S)) \<and> 
               s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (trace_hide s1 (ev ` S)) @ trace_hide s2 (ev ` f ` S) \<and> 
               trace_hide s1 (ev ` S) \<in> \<D> (P \ S)\<close>
          apply (simp add: F_Renaming "*"(1), intro conjI)
          using Hiding_tickFree apply blast
          using Hiding_front_tickFree apply blast
           apply (rule trace_hide_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF inj_on_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k])
          using mem_D_imp_mem_D_Hiding by blast
        show \<open>(s, X) \<in> \<F> ?lhs\<close>
          apply (simp add: F_Renaming)
          using \<open>?this\<close> by blast
      qed
    qed
  qed
qed



subsection \<open>\<^const>\<open>Renaming\<close> and \<^const>\<open>Sync\<close>\<close>

text \<open>Idem for the synchronization: when \<^term>\<open>f\<close> is one to one, 
      \<^term>\<open>Renaming (P \<lbrakk>S\<rbrakk> Q)\<close> will behave as expected.\<close>

lemma map_antecedent_if_subset_rangeE :
  assumes \<open>set u \<subseteq> range f\<close>
  obtains t where \<open>u = map f t\<close>
  \<comment> \<open>In particular, when \<^term>\<open>f\<close> is surjective or bijective.\<close>
proof -
  from \<open>set u \<subseteq> range f\<close> have \<open>\<exists>t. u = map f t\<close>
  proof (induct u)
    show \<open>\<exists>t. [] = map f t\<close> by simp
  next
    fix a u
    assume prem : \<open>set (a # u) \<subseteq> range f\<close>
       and  hyp : \<open>set u \<subseteq> range f \<Longrightarrow> \<exists>t. u = map f t\<close>
    then obtain t where * : \<open>u = map f t\<close> 
      by (meson set_subset_Cons subset_trans)
    from prem obtain x where ** : \<open>f x = a\<close> by auto
    show \<open>\<exists>t. a # u = map f t\<close>
    proof (intro exI)
      show \<open>a # u = map f (x # t)\<close> by (simp add: "*" "**")
    qed
  qed
  with that show thesis by blast
qed


lemma bij_map_setinterleaving_iff_setinterleaving :
  \<open>map f r setinterleaves ((map f t, map f u), f ` S) \<longleftrightarrow>
   r setinterleaves ((t, u), S)\<close> if bij_f : \<open>bij f\<close>
proof (induct \<open>(t, S, u)\<close> arbitrary: t u r rule: setinterleaving.induct)
  case 1
  thus ?case by simp
next
  case (2 y u)
  show ?case
  proof (cases \<open>y \<in> S\<close>)
    show \<open>y \<in> S \<Longrightarrow> ?case\<close> by simp
  next
    assume \<open>y \<notin> S\<close>
    hence \<open>f y \<notin> f ` S\<close> by (metis bij_betw_imp_inj_on inj_image_mem_iff bij_f)
    with "2.hyps"[OF \<open>y \<notin> S\<close>, of \<open>tl r\<close>] show ?case
      by (cases r; simp add: \<open>y \<notin> S\<close>) (metis bij_pointE bij_f)
  qed
next
  case (3 x t)
  show ?case
  proof (cases \<open>x \<in> S\<close>)
    show \<open>x \<in> S \<Longrightarrow> ?case\<close> by simp
  next
    assume \<open>x \<notin> S\<close>
    hence \<open>f x \<notin> f ` S\<close> by (metis bij_betw_imp_inj_on inj_image_mem_iff bij_f)
    with "3.hyps"[OF \<open>x \<notin> S\<close>, of \<open>tl r\<close>] show ?case
      by (cases r; simp add: \<open>x \<notin> S\<close>) (metis bij_pointE bij_f)
  qed
next
  case (4 x t y u)
  have  * : \<open>x \<noteq> y \<Longrightarrow> f x \<noteq> f y\<close> by (metis bij_pointE bij_f)
  have ** : \<open>f z \<in> f ` S \<longleftrightarrow> z \<in> S\<close> for z
    by (meson bij_betw_def inj_image_mem_iff bij_f)
  show ?case
  proof (cases \<open>x \<in> S\<close>; cases \<open>y \<in> S\<close>)
    from "4.hyps"(1)[of \<open>tl r\<close>] show \<open>x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> ?case\<close>
      by (cases r; simp add: "*") (metis bij_pointE bij_f)
  next
    from "4.hyps"(2)[of \<open>tl r\<close>] show \<open>x \<in> S \<Longrightarrow> y \<notin> S \<Longrightarrow> ?case\<close>
      by (cases r; simp add: "**") (metis bij_pointE bij_f)
  next
    from "4.hyps"(5)[of \<open>tl r\<close>] show \<open>x \<notin> S \<Longrightarrow> y \<in> S \<Longrightarrow> ?case\<close>
      by (cases r; simp add: "**") (metis bij_pointE bij_f)
  next
    from "4.hyps"(3, 4)[of \<open>tl r\<close>] show \<open>x \<notin> S \<Longrightarrow> y \<notin> S \<Longrightarrow> ?case\<close>
      by (cases r; simp add: "**") (metis bij_pointE bij_f)
  qed
qed


theorem bij_Renaming_Sync:
  \<open>Renaming (P \<lbrakk>S\<rbrakk> Q) f g = Renaming P f g \<lbrakk>f ` S\<rbrakk> Renaming Q f g\<close>
  (is \<open>?lhs P Q = ?rhs P Q\<close>) if bij_f: \<open>bij f\<close> and bij_g : \<open>bij g\<close>
proof -
  \<comment> \<open>Some intermediate results.\<close>
  have map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inv_comp_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (inv f) (inv g) \<circ> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g = id\<close>
  proof (rule ext)
    show map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inv_comp_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
      \<open>(map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (inv f) (inv g) \<circ> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t = id t\<close> for t
      by (induct t, simp_all) (metis bij_f bij_inv_eq_iff, metis bij_g bij_inv_eq_iff)
  qed
  have map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comp_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inv : \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g \<circ> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (inv f) (inv g) = id\<close>
    proof (rule ext)
    show map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inv_comp_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
      \<open>(map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g \<circ> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (inv f) (inv g)) t = id t\<close> for t
      by (induct t, simp_all) (metis bij_f bij_inv_eq_iff, metis bij_g bij_inv_eq_iff)
  qed
  from map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inv_comp_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comp_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inv o_bij
  have bij_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : \<open>bij (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)\<close> by blast
  have inv_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inv : \<open>inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) = map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (inv f) (inv g)\<close>
    by (simp add: inv_equality map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comp_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inv map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inv_comp_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k pointfree_idE)
  have sets_S_eq : \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g ` (range tick \<union> ev ` S) = range tick \<union> ev ` f ` S\<close>
    by (auto simp add: set_eq_iff image_iff tick_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff ev_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
       (metis UNIV_I Un_iff bij_betw_def bij_g image_iff, blast)
  have inj_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : \<open>inj (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)\<close>
   and inj_inv_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : \<open>inj (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g))\<close>
    by (use bij_betw_imp_inj_on bij_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k in blast)
       (meson bij_betw_imp_inj_on bij_betw_inv_into bij_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  show \<open>?lhs P Q = ?rhs P Q\<close>
  proof (subst Process_eq_spec_optimized, safe)
    fix s
    assume \<open>s \<in> \<D> (?lhs P Q)\<close>
    then obtain s1 s2
      where * : \<open>tF s1\<close> \<open>ftF s2\<close> \<open>s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1 @ s2\<close> \<open>s1 \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
      by (simp add: D_Renaming) blast
    from "*"(4) obtain t u r v 
      where ** : \<open>ftF v\<close> \<open>tF r \<or> v = []\<close> 
                 \<open>s1 = r @ v\<close> \<open>r setinterleaves ((t, u), range tick \<union> ev ` S)\<close>
                 \<open>t \<in> \<D> P \<and> u \<in> \<T> Q \<or> t \<in> \<D> Q \<and> u \<in> \<T> P\<close> 
      by (simp add: D_Sync) blast
    { fix t u P Q
      assume assms : \<open>r setinterleaves ((t, u), range tick \<union> ev ` S)\<close> 
                     \<open>t \<in> \<D> P\<close> \<open>u \<in> \<T> Q\<close>
      have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) r setinterleaves 
            ((map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t, map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u), range tick \<union> ev ` f ` S)\<close>
        by (metis assms(1) bij_map_setinterleaving_iff_setinterleaving bij_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k sets_S_eq)
      moreover have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t \<in> \<D> (Renaming P f g)\<close>
        apply (cases \<open>tF t\<close>; simp add: D_Renaming)
        using assms(2) front_tickFree_Nil apply blast
        by (metis D_T D_imp_front_tickFree append_T_imp_tickFree assms(2) front_tickFree_Cons_iff
            is_processT9 list.simps(3) map_append nonTickFree_n_frontTickFree map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_front_tickFree)
      moreover have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u \<in> \<T> (Renaming Q f g)\<close>
        using assms(3) by (simp add: T_Renaming) blast
      ultimately have \<open>s \<in> \<D> (?rhs P Q)\<close>
        by (simp add: D_Sync "*"(3) "**"(3))
           (metis "*"(1, 2) "**"(3) map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree front_tickFree_append tickFree_append_iff)
    } note *** = this

    from "**"(4, 5) "***" show \<open>s \<in> \<D> (?rhs P Q)\<close>
      apply (elim disjE)
      using "**"(4) "***" apply blast
      using "**"(4) "***" by (subst Sync_commute) blast
  next
    fix s
    assume \<open>s \<in> \<D> (?rhs P Q)\<close>
    then obtain t u r v
      where * : \<open>ftF v\<close> \<open>tF r \<or> v = []\<close> \<open>s = r @ v\<close> 
                \<open>r setinterleaves ((t, u), range tick \<union> ev ` f ` S)\<close>
                \<open>t \<in> \<D> (Renaming P f g) \<and> u \<in> \<T> (Renaming Q f g) \<or>
                 t \<in> \<D> (Renaming Q f g) \<and> u \<in> \<T> (Renaming P f g)\<close>
      by (simp add: D_Sync) blast

    { fix t u P Q
      assume assms : \<open>r setinterleaves ((t, u), range tick \<union> ev ` f ` S)\<close>
                     \<open>t \<in> \<D> (Renaming P f g)\<close> \<open>u \<in> \<T> (Renaming Q f g)\<close>
      have \<open>inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) ` (range tick \<union> ev ` f ` S) =
            inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) ` map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g ` (range tick \<union> ev ` S)\<close>
        using sets_S_eq by presburger
      from bij_map_setinterleaving_iff_setinterleaving
           [THEN iffD2, OF _ assms(1), of \<open>inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)\<close>,
            simplified this image_inv_f_f[OF inj_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k]]
      have ** : \<open>(map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) r) setinterleaves
                 ((map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) t, map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) u), range tick \<union> ev ` S)\<close>
        using bij_betw_inv_into bij_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
      from assms(2) obtain s1 s2
        where \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1 @ s2\<close> \<open>tF s1\<close> \<open>ftF s2\<close> \<open>s1 \<in> \<D> P\<close>
        by (auto simp add: D_Renaming)
      hence \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (inv f) (inv g)) t \<in> \<D> (Renaming (Renaming P f g) (inv f) (inv g))\<close>
        apply (simp add: D_Renaming)
        apply (rule_tac x = \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1\<close> in exI)
        apply (rule_tac x = \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (inv f) (inv g)) s2\<close> in exI)
        by simp (metis append_Nil2 front_tickFree_Nil map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_front_tickFree map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree)
      hence *** : \<open>map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) t \<in> \<D> P\<close>
        by (metis Renaming_inv bij_def bij_f bij_g inv_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inv)
      have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (inv f) (inv g)) u \<in> \<T> (Renaming (Renaming Q f g) (inv f) (inv g))\<close>
        using assms(3) by (subst T_Renaming, simp) blast
      hence **** : \<open>map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) u \<in> \<T> Q\<close>
        by (simp add: Renaming_inv bij_f bij_g bij_is_inj inv_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inv)
      have ***** : \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g \<circ> inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) r = r\<close>
        by (metis (no_types, lifting) bij_betw_imp_inj_on bij_betw_inv_into bij_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k inj_iff list.map_comp list.map_id)
      have \<open>s \<in> \<D> (?lhs P Q)\<close>
      proof (cases \<open>tF r\<close>)
        assume \<open>tF r\<close>
        have $ : \<open>r @ v = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) r) @ v\<close>
          by (simp add: "*****")
        show \<open>s \<in> \<D> (?lhs P Q)\<close>
          apply (simp add: D_Renaming D_Sync "*"(3))
          by (metis "$" "*"(1) "**" "***" "****" map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree \<open>tF r\<close> 
                    append.right_neutral append_same_eq front_tickFree_Nil)
      next
        assume \<open>\<not> tF r\<close>
        then obtain r' res where $ : \<open>r = r' @ [\<checkmark>(res)]\<close> \<open>tF r'\<close>
          by (metis D_imp_front_tickFree assms butlast_snoc front_tickFree_charn
                    front_tickFree_single ftf_Sync is_processT2_TR list.distinct(1)
                    nonTickFree_n_frontTickFree self_append_conv2)
        then obtain t' u'
          where $$ : \<open>t = t' @ [\<checkmark>(res)]\<close> \<open>u = u' @ [\<checkmark>(res)]\<close>
          by (metis D_imp_front_tickFree SyncWithTick_imp_NTF T_imp_front_tickFree assms)
        hence $$$ : \<open>(map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) r') setinterleaves
                     ((map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) t', map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) u'),
                      range tick \<union> ev ` S)\<close>
          by (metis (no_types) "$"(1) append_same_eq assms(1) bij_betw_imp_surj_on
                    bij_map_setinterleaving_iff_setinterleaving bij_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
                    ftf_Sync32 inj_imp_bij_betw_inv inj_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k sets_S_eq)
        from "***" $$(1) have *** : \<open>map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) t' \<in> \<D> P\<close> 
          by simp (use inv_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inv is_processT9 in force)
        from "****" $$(2) have **** : \<open>map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) u' \<in> \<T> Q\<close>
          using is_processT3_TR prefixI by simp blast
        have $$$$ : \<open>r = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) r') @ [\<checkmark>(res)]\<close>
          using "$" "*****" by auto
        show \<open>s \<in> \<D> (?lhs P Q)\<close>
          by (simp add: D_Renaming D_Sync "*"(3) "$$$")
             (metis "$"(1) "$"(2) "$$$" "$$$$" "*"(2) "***" "****" map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree \<open>\<not> tF r\<close>
                    append.right_neutral append_same_eq front_tickFree_Nil front_tickFree_single)
      qed
    } note ** = this
    show \<open>s \<in> \<D> (?lhs P Q)\<close> by (metis "*"(4, 5) "**" Sync_commute)
  next
    fix s X
    assume same_div : \<open>\<D> (?lhs P Q) = \<D> (?rhs P Q)\<close>
    assume \<open>(s, X) \<in> \<F> (?lhs P Q)\<close>
    then consider \<open>s \<in> \<D> (?lhs P Q)\<close>
      | s1 where \<open>(s1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close> \<open>s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1\<close>
      by (simp add: F_Renaming D_Renaming) blast
    thus \<open>(s, X) \<in> \<F> (?rhs P Q)\<close>
    proof cases
      from same_div D_F show \<open>s \<in> \<D> (?lhs P Q) \<Longrightarrow> (s, X) \<in> \<F> (?rhs P Q)\<close> by blast
    next
      fix s1 assume * : \<open>(s1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close> 
                        \<open>s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1\<close>
      from "*"(1) consider \<open>s1 \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
        | t_P t_Q X_P X_Q 
        where \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close> 
              \<open>s1 setinterleaves ((t_P, t_Q), range tick \<union> ev ` S)\<close>
              \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` S) \<union> X_P \<inter> X_Q\<close>
        by (auto simp add: F_Sync D_Sync)
      thus \<open>(s, X) \<in> \<F> (?rhs P Q)\<close>
      proof cases
        assume \<open>s1 \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
        hence \<open>s \<in> \<D> (?lhs P Q)\<close>
          apply (cases \<open>tF s1\<close>; simp add: D_Renaming "*"(2)) 
          using front_tickFree_Nil apply blast
          by (metis (no_types, lifting) map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_front_tickFree butlast_snoc front_tickFree_iff_tickFree_butlast
                    front_tickFree_single map_butlast nonTickFree_n_frontTickFree process_charn)
        with same_div D_F show \<open>(s, X) \<in> \<F> (?rhs P Q)\<close> by blast
      next
        fix t_P t_Q X_P X_Q
        assume ** : \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
                    \<open>s1 setinterleaves ((t_P, t_Q), range tick \<union> ev ` S)\<close>
                    \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` S) \<union> X_P \<inter> X_Q\<close>
        have \<open>(map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t_P, (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) ` X_P) \<in> \<F> (Renaming P f g)\<close>
          by (simp add: F_Renaming)
             (metis "**"(1) bij_betw_def bij_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k inj_vimage_image_eq)  
        moreover have \<open>(map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t_Q, (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) ` X_Q) \<in> \<F> (Renaming Q f g)\<close>
          by (simp add: F_Renaming)
             (metis "**"(2) bij_betw_imp_inj_on bij_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k inj_vimage_image_eq)
        moreover have \<open>s setinterleaves ((map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t_P, map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t_Q),
                                         range tick \<union> ev ` f ` S)\<close>
          by (metis "*"(2) "**"(3) bij_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k sets_S_eq
                    bij_map_setinterleaving_iff_setinterleaving)
        moreover have \<open>X = ((map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) ` X_P \<union> (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) ` X_Q) \<inter> (range tick \<union> ev ` f ` S) \<union>
                  (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) ` X_P \<inter> (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) ` X_Q\<close>
          apply (rule inj_image_eq_iff[THEN iffD1, OF inj_inv_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k])
          apply (subst bij_vimage_eq_inv_image[OF bij_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, symmetric])
          apply (subst "**"(4), fold image_Un sets_S_eq)
          apply (subst (1 2) image_Int[OF inj_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, symmetric])
          apply (fold image_Un)
          apply (subst image_inv_f_f[OF inj_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k])
          by simp
        ultimately show \<open>(s, X) \<in> \<F> (?rhs P Q)\<close>
          by (simp add: F_Sync) blast
      qed
    qed
  next
    fix s X
    assume same_div : \<open>\<D> (?lhs P Q) = \<D> (?rhs P Q)\<close>
    assume \<open>(s, X) \<in> \<F> (?rhs P Q)\<close>
    then consider \<open>s \<in> \<D> (?rhs P Q)\<close>
      | t_P t_Q X_P X_Q where
        \<open>(t_P, X_P) \<in> \<F> (Renaming P f g)\<close> \<open>(t_Q, X_Q) \<in> \<F> (Renaming Q f g)\<close>
        \<open>s setinterleaves ((t_P, t_Q), range tick \<union> ev ` f ` S)\<close>
        \<open>X = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` f ` S) \<union> X_P \<inter> X_Q\<close>
      by (simp add: F_Sync D_Sync) blast
    thus \<open>(s, X) \<in> \<F> (?lhs P Q)\<close>
    proof cases
      from same_div D_F show \<open>s \<in> \<D> (?rhs P Q) \<Longrightarrow> (s, X) \<in> \<F> (?lhs P Q)\<close> by blast
    next
      fix t_P t_Q X_P X_Q
      assume * : \<open>(t_P, X_P) \<in> \<F> (Renaming P f g)\<close> \<open>(t_Q, X_Q) \<in> \<F> (Renaming Q f g)\<close>
                 \<open>s setinterleaves ((t_P, t_Q), range tick \<union> ev ` f ` S)\<close>
                 \<open>X = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` f ` S) \<union> X_P \<inter> X_Q\<close>
      from "*"(1, 2) consider \<open>t_P \<in> \<D> (Renaming P f g) \<or> t_Q \<in> \<D> (Renaming Q f g)\<close>
        | t_P1 t_Q1 where \<open>(t_P1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X_P) \<in> \<F> P\<close> \<open>t_P = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t_P1\<close>
                          \<open>(t_Q1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X_Q) \<in> \<F> Q\<close> \<open>t_Q = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t_Q1\<close>
        by (simp add: F_Renaming D_Renaming) blast
      thus \<open>(s, X) \<in> \<F> (?lhs P Q)\<close>
      proof cases
        assume \<open>t_P \<in> \<D> (Renaming P f g) \<or> t_Q \<in> \<D> (Renaming Q f g)\<close>
        hence \<open>s \<in> \<D> (?rhs P Q)\<close>
          apply (simp add: D_Sync)
          using "*"(1, 2, 3) F_T setinterleaving_sym front_tickFree_Nil by blast
        with same_div D_F show \<open>(s, X) \<in> \<F> (?lhs P Q)\<close> by blast
      next
        fix t_P1 t_Q1
        assume ** : \<open>(t_P1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X_P) \<in> \<F> P\<close> \<open>t_P = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t_P1\<close>
                    \<open>(t_Q1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X_Q) \<in> \<F> Q\<close> \<open>t_Q = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t_Q1\<close>
        from "**"(2, 4) have *** : \<open>t_P1 = map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) t_P\<close>
                                   \<open>t_Q1 = map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) t_Q\<close>
          by (simp_all add: inj_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        have **** : \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) s) = s\<close>
          by (metis bij_betw_imp_surj bij_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k list.map_comp list.map_id surj_iff)
        from bij_map_setinterleaving_iff_setinterleaving
             [of \<open>inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)\<close> s t_P \<open>range tick \<union> ev ` f ` S\<close> t_Q, simplified "*"(3)]
        have \<open>map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) s setinterleaves ((t_P1, t_Q1), range tick \<union> ev ` S)\<close>
          by (metis "***" bij_betw_def bij_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k inj_imp_bij_betw_inv sets_S_eq)
        moreover have \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X = (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X_P \<union> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X_Q) \<inter> (range tick \<union> ev ` S) \<union> 
                      map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X_P \<inter> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X_Q\<close>
          by (metis (no_types, lifting) "*"(4) inj_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k inj_vimage_image_eq sets_S_eq vimage_Int vimage_Un)
        ultimately show \<open>(s, X) \<in> \<F> (?lhs P Q)\<close>
          by (simp add: F_Renaming F_Sync)
             (metis "**"(1, 3) "****")
      qed
    qed
  qed
qed


section \<open>\<^const>\<open>Hiding\<close> and \<^const>\<open>Mprefix\<close>\<close>

text \<open>We already have a way to distribute the \<^const>\<open>Hiding\<close> operator on the
      \<^const>\<open>Mprefix\<close> operator with @{thm Hiding_Mprefix_disjoint[of S A]}.
      But this is only usable when \<^term>\<open>A \<inter> S = {}\<close>. With the \<^const>\<open>Sliding\<close>
      operator, we can now handle the case \<^term>\<open>A \<inter> S \<noteq> {}\<close>.\<close>

subsection \<open>\<^const>\<open>Hiding\<close> and \<^const>\<open>Mprefix\<close> for disjoint Sets\<close>

text \<open>This is a result similar to @{thm Hiding_Mprefix_disjoint}
      when we add a \<^const>\<open>Sliding\<close> in the expression.\<close>

theorem Hiding_Mprefix_Sliding_disjoint:
  \<open>((\<box>a \<in> A \<rightarrow> P a) \<rhd> Q) \ S = (\<box>a \<in> A \<rightarrow> (P a \ S)) \<rhd> (Q \ S)\<close>
  if disjoint: \<open>A \<inter> S = {}\<close>
proof (subst Hiding_Mprefix_disjoint[OF disjoint, symmetric])
  show \<open>((\<box>a \<in> A \<rightarrow> P a) \<rhd> Q) \ S = (\<box>a \<in> A \<rightarrow> P a \ S) \<rhd> (Q \ S)\<close>
   (is \<open>?lhs = ?rhs\<close>)
  proof (subst Process_eq_spec_optimized, safe)
    fix s
    assume \<open>s \<in> \<D> ?lhs\<close>
    hence \<open>s \<in> \<D> (Mprefix A P \<sqinter> Q \ S)\<close>
      by (simp add: D_Hiding D_Sliding D_Ndet T_Sliding T_Ndet)
    thus \<open>s \<in> \<D> ?rhs\<close>
      by (rule set_rev_mp) (simp add: D_Ndet D_Sliding Hiding_distrib_Ndet)
  next
    fix s
    assume \<open>s \<in> \<D> ?rhs\<close>
    hence \<open>s \<in> \<D> (Q \ S) \<or> s \<in> \<D> (\<box>a \<in> A \<rightarrow> P a \ S)\<close>
      by (simp add: Hiding_Mprefix_disjoint[OF disjoint]
                    D_Ndet D_Sliding) blast
    thus \<open>s \<in> \<D> ?lhs\<close>
      by (auto simp add: D_Hiding D_Sliding T_Sliding)
  next
    fix s X
    assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
    assume \<open>(s, X) \<in> \<F> ?lhs\<close>
    then consider \<open>s \<in> \<D> ?lhs\<close>
      |\<open>\<exists>t. s = trace_hide t (ev ` S) \<and> (t, X \<union> ev ` S) \<in> \<F> (Mprefix A P \<rhd> Q)\<close>
      by (simp add: F_Hiding D_Hiding) blast
    thus \<open>(s, X) \<in> \<F> ?rhs\<close>
    proof cases
      from same_div D_F show \<open>s \<in> \<D> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> by blast
    next
      assume \<open>\<exists>t. s = trace_hide t (ev ` S) \<and>
                  (t, X \<union> ev ` S) \<in> \<F> (Mprefix A P \<rhd> Q)\<close>
      then obtain t
        where * : \<open>s = trace_hide t (ev ` S)\<close>
                  \<open>(t, X \<union> ev ` S) \<in> \<F> (Mprefix A P \<rhd> Q)\<close> by blast
      from "*"(2) consider \<open>(t, X \<union> ev ` S) \<in> \<F> Q\<close>
        | \<open>t \<noteq> []\<close> \<open>(t, X \<union> ev ` S) \<in> \<F> (Mprefix A P)\<close>
        by (simp add: F_Sliding D_Mprefix) blast
      thus \<open>(s, X) \<in> \<F> ?rhs\<close>
      proof cases
        have \<open>(t, X \<union> ev ` S) \<in> \<F> Q \<Longrightarrow> (s, X) \<in> \<F> (Q \ S)\<close>
          by (auto simp add: F_Hiding "*"(1))
        thus \<open>(t, X \<union> ev ` S) \<in> \<F> Q \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
          by (simp add: F_Ndet F_Sliding "*"(1))
      next
        assume assms : \<open>t \<noteq> []\<close> \<open>(t, X \<union> ev ` S) \<in> \<F> (Mprefix A P)\<close>
        with disjoint have \<open>trace_hide t (ev ` S) \<noteq> []\<close>
          by (cases t, auto simp add: F_Mprefix)
        also have \<open>(s, X) \<in> \<F> (Mprefix A P \ S)\<close>
          using assms by (auto simp: F_Hiding "*"(1))
        ultimately show \<open>(s, X) \<in> \<F> ?rhs\<close>
          by (simp add: F_Sliding "*"(1))
      qed
    qed
  next
    have * : \<open>t \<in> \<T> (Mprefix A P) \<Longrightarrow> trace_hide t (ev ` S) = [] \<longleftrightarrow> t = []\<close> for t
      using disjoint by (cases t, auto simp add: T_Mprefix)
    have ** : \<open>[] \<notin> \<D> (Mprefix A P \ S)\<close>
      apply (rule ccontr, simp add: D_Hiding, elim exE conjE disjE)
      by (use "*" D_T Nil_notin_D_Mprefix in blast)
         (metis (no_types, lifting) "*" UNIV_I f_inv_into_f old.nat.distinct(2) strict_mono_on_eqD)
    fix s X
    assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
    assume \<open>(s, X) \<in> \<F> ?rhs\<close>
    with ** consider \<open>(s, X) \<in> \<F> (Q \ S)\<close>
      | \<open>s \<noteq> []\<close> \<open>(s, X) \<in> \<F> (Mprefix A P \ S)\<close>
      by (simp add: Hiding_Mprefix_disjoint[OF disjoint] F_Sliding D_Mprefix) blast
    thus \<open>(s, X) \<in> \<F> ?lhs\<close>
    proof cases
      assume \<open>(s, X) \<in> \<F> (Q \ S)\<close>
      then consider \<open>s \<in> \<D> (Q \ S)\<close>
        | \<open>\<exists>t. s = trace_hide t (ev ` S) \<and> (t, X \<union> ev ` S) \<in> \<F> Q\<close>
        by (simp add: F_Hiding D_Hiding) blast
      thus \<open>(s, X) \<in> \<F> ?lhs\<close>
      proof cases
        assume \<open>s \<in> \<D> (Q \ S)\<close>
        hence \<open>s \<in> \<D> ?rhs\<close> by (simp add: D_Ndet D_Sliding)
        with same_div D_F show \<open>(s, X) \<in> \<F> ?lhs\<close> by blast
      next
        assume \<open>\<exists>t. s = trace_hide t (ev ` S) \<and> (t, X \<union> ev ` S) \<in> \<F> Q\<close>
        thus \<open>(s, X) \<in> \<F> ?lhs\<close>
          by (simp add: F_Hiding F_Sliding) blast
      qed
    next
      assume assms : \<open>s \<noteq> []\<close> \<open>(s, X) \<in> \<F> (Mprefix A P \ S)\<close>
      then consider \<open>s \<in> \<D> (Mprefix A P \ S)\<close>
        | \<open>\<exists>t. t \<noteq> [] \<and> s = trace_hide t (ev ` S) \<and> (t, X \<union> ev ` S) \<in> \<F> (Mprefix A P)\<close>
        by (simp add: F_Hiding D_Hiding) (metis filter.simps(1))
      thus \<open>(s, X) \<in> \<F> ?lhs\<close>
      proof cases
        assume \<open>s \<in> \<D> (Mprefix A P \ S)\<close>
        hence \<open>s \<in> \<D> ?rhs\<close> by (simp add: D_Ndet D_Sliding)
        with same_div D_F show \<open>(s, X) \<in> \<F> ?lhs\<close> by blast
      next
        show \<open>\<exists>t. t \<noteq> [] \<and> s = trace_hide t (ev ` S) \<and>
                  (t, X \<union> ev ` S) \<in> \<F> (Mprefix A P) \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
          by (auto simp add: F_Sliding F_Hiding)
      qed
    qed
  qed
qed




subsection \<open>\<^const>\<open>Hiding\<close> and \<^const>\<open>Mprefix\<close> for non-disjoint Sets\<close>

text \<open>Finally the new version, when \<^term>\<open>A \<inter> S \<noteq> {}\<close>.\<close>

\<comment> \<open>Just a small lemma to understand why the nonempty hypothesis is necessary.\<close>
lemma \<open>\<exists>A :: nat set. \<exists>P S.
       A \<inter> S = {} \<and> \<box>a \<in> A \<rightarrow> P a \ S \<noteq> 
       (\<box>a \<in> (A - S) \<rightarrow> (P a \ S)) \<rhd> (\<sqinter>a \<in> (A \<inter> S). (P a \ S))\<close>
proof (intro exI)
  show \<open>{0} \<inter> {Suc 0} = {} \<and> 
        \<box>a \<in> {0} \<rightarrow> SKIP undefined \ {Suc 0} \<noteq> 
        (\<box>a \<in> ({0} - {Suc 0}) \<rightarrow> (SKIP undefined \ {Suc 0})) \<rhd> (\<sqinter>a \<in> ({0} \<inter> {Suc 0}). (SKIP undefined \ {Suc 0}))\<close>
    apply (simp add: write0_def[symmetric] Hiding_write0_disjoint)
    using UNIV_I list.discI by (auto simp add: Process_eq_spec write0_def F_Ndet
                                               F_Mprefix F_Sliding F_STOP set_eq_iff)
qed


text \<open>This is a result similar to @{thm Hiding_Mprefix_non_disjoint}
      when we add a \<^const>\<open>Sliding\<close> in the expression.\<close>

lemma Hiding_Mprefix_Sliding_non_disjoint:
  \<open>(\<box>a \<in> A \<rightarrow> P a) \<rhd> Q \ S = (\<box>a \<in> (A - S) \<rightarrow> (P a \ S)) \<rhd> 
                              (Q \ S) \<sqinter> (\<sqinter>a \<in> (A \<inter> S). (P a \ S))\<close>
  if non_disjoint: \<open>A \<inter> S \<noteq> {}\<close>
proof (subst Sliding_distrib_Ndet_left,
       subst Hiding_Mprefix_non_disjoint[OF non_disjoint, symmetric])
  show \<open>Mprefix A P \<rhd> Q \ S =
        ((\<box>a \<in> (A - S) \<rightarrow> (P a \ S)) \<rhd> (Q \ S)) \<sqinter> (\<box>a \<in> A \<rightarrow> P a \ S)\<close>
   (is \<open>?lhs = ?rhs\<close>)
  proof (subst Process_eq_spec_optimized, safe)
    fix s
    assume \<open>s \<in> \<D> ?lhs\<close>
    hence \<open>s \<in> \<D> (Mprefix A P \<sqinter> Q \ S)\<close>
      by (simp add: D_Hiding D_Sliding D_Ndet T_Sliding T_Ndet)
    thus \<open>s \<in> \<D> ?rhs\<close>
      by (rule set_rev_mp)
         (simp add: D_Ndet D_Sliding Hiding_distrib_Ndet subsetI)
  next
    fix s
    assume \<open>s \<in> \<D> ?rhs\<close>
    hence \<open>s \<in> \<D> (Q \ S) \<or> s \<in> \<D> (\<box>a \<in> A \<rightarrow> P a \ S)\<close>
      by (simp add: Hiding_Mprefix_non_disjoint[OF non_disjoint]
                    D_Ndet D_Sliding) blast
    thus \<open>s \<in> \<D> ?lhs\<close>
      by (auto simp add: D_Hiding D_Sliding T_Sliding)
  next
    fix s X
    assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
    assume \<open>(s, X) \<in> \<F> ?lhs\<close>
    then consider \<open>s \<in> \<D> ?lhs\<close>
      |\<open>\<exists>t. s = trace_hide t (ev ` S) \<and> (t, X \<union> ev ` S) \<in> \<F> (Mprefix A P \<rhd> Q)\<close>
      by (simp add: F_Hiding D_Hiding) blast
    thus \<open>(s, X) \<in> \<F> ?rhs\<close>
    proof cases
      from same_div D_F show \<open>s \<in> \<D> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> by blast
    next
      assume \<open>\<exists>t. s = trace_hide t (ev ` S) \<and>
                  (t, X \<union> ev ` S) \<in> \<F> (Mprefix A P \<rhd> Q)\<close>
      then obtain t
        where * : \<open>s = trace_hide t (ev ` S)\<close>
                  \<open>(t, X \<union> ev ` S) \<in> \<F> (Mprefix A P \<rhd> Q)\<close> by blast
      from "*"(2) consider \<open>(t, X \<union> ev ` S) \<in> \<F> Q\<close>
        | \<open>(t, X \<union> ev ` S) \<in> \<F> (Mprefix A P)\<close>
        by (simp add: F_Sliding D_Mprefix) blast
      thus \<open>(s, X) \<in> \<F> ?rhs\<close>
      proof cases
        have \<open>(t, X \<union> ev ` S) \<in> \<F> Q \<Longrightarrow> (s, X) \<in> \<F> (Q \ S)\<close>
          by (auto simp add: F_Hiding "*"(1))
        thus \<open>(t, X \<union> ev ` S) \<in> \<F> Q \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
          by (simp add: F_Ndet F_Sliding "*"(1))
      next
        assume \<open>(t, X \<union> ev ` S) \<in> \<F> (Mprefix A P)\<close>
        hence \<open>(s, X) \<in> \<F> (Mprefix A P \ S)\<close> by (auto simp: F_Hiding "*"(1))
        thus \<open>(s, X) \<in> \<F> ?rhs\<close> by (simp add: F_Ndet "*"(1))
      qed
    qed
  next
    fix s X
    have * : \<open>s \<noteq> [] \<Longrightarrow> (s, X) \<in> \<F> (\<box>a \<in> (A - S) \<rightarrow> (P a \ S)) \<Longrightarrow> 
                          (s, X) \<in> \<F> (\<box>a \<in> A \<rightarrow> P a \ S)\<close>
      by (simp add: Hiding_Mprefix_non_disjoint[OF non_disjoint] F_Sliding)
    assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
    assume \<open>(s, X) \<in> \<F> ?rhs\<close>
    with "*" consider \<open>(s, X) \<in> \<F> (Q \ S)\<close> | \<open>(s, X) \<in> \<F> (Mprefix A P \ S)\<close>
      by (auto simp add: F_Ndet F_Sliding)
    thus \<open>(s, X) \<in> \<F> ?lhs\<close>
    proof cases
      assume \<open>(s, X) \<in> \<F> (Q \ S)\<close>
      then consider \<open>s \<in> \<D> (Q \ S)\<close>
        | \<open>\<exists>t. s = trace_hide t (ev ` S) \<and> (t, X \<union> ev ` S) \<in> \<F> Q\<close>
        by (simp add: F_Hiding D_Hiding) blast
      thus \<open>(s, X) \<in> \<F> ?lhs\<close>
      proof cases
        assume \<open>s \<in> \<D> (Q \ S)\<close>
        hence \<open>s \<in> \<D> ?rhs\<close> by (simp add: D_Ndet D_Sliding)
        with same_div D_F show \<open>(s, X) \<in> \<F> ?lhs\<close> by blast
      next
        assume \<open>\<exists>t. s = trace_hide t (ev ` S) \<and> (t, X \<union> ev ` S) \<in> \<F> Q\<close>
        thus \<open>(s, X) \<in> \<F> ?lhs\<close>
          by (simp add: F_Hiding F_Sliding) blast
      qed
    next
      assume \<open>(s, X) \<in> \<F> (Mprefix A P \ S)\<close>
      then consider \<open>s \<in> \<D> (Mprefix A P \ S)\<close>
        | \<open>\<exists>t. s = trace_hide t (ev ` S) \<and> (t, X \<union> ev ` S) \<in> \<F> (Mprefix A P)\<close>
        by (simp add: F_Hiding D_Hiding) blast
      thus \<open>(s, X) \<in> \<F> ?lhs\<close>
      proof cases
        assume \<open>s \<in> \<D> (Mprefix A P \ S)\<close>
        hence \<open>s \<in> \<D> ?rhs\<close> by (simp add: D_Ndet D_Sliding)
        with same_div D_F show \<open>(s, X) \<in> \<F> ?lhs\<close> by blast
      next
        assume \<open>\<exists>t. s = trace_hide t (ev ` S) \<and> (t, X \<union> ev ` S) \<in> \<F> (Mprefix A P)\<close>
        then obtain t where * : \<open>s = trace_hide t (ev ` S)\<close>
                                \<open>(t, X \<union> ev ` S) \<in> \<F> (Mprefix A P)\<close> by blast
        from "*"(2) non_disjoint have \<open>t \<noteq> []\<close> by (simp add: F_Mprefix) blast
        with "*" show \<open>(s, X) \<in> \<F> ?lhs\<close>
          by (simp add: F_Hiding F_Sliding) blast
      qed
    qed
  qed
qed
       


section \<open>\<^const>\<open>Sliding\<close> behaviour\<close>

text \<open>We already proved several laws for the \<^const>\<open>Sliding\<close> operator.
      Here we give other results in the same spirit as
      @{thm [source] Hiding_Mprefix_Sliding_disjoint} and
      @{thm [source] Hiding_Mprefix_Sliding_non_disjoint}.\<close>

lemma Mprefix_Sliding_Mprefix_Sliding:
  \<open>(\<box>a \<in> A \<rightarrow> P a) \<rhd> (\<box>b \<in> B \<rightarrow> Q b) \<rhd> R =
   (\<box> x \<in> (A \<union> B) \<rightarrow> (if x \<in> A \<inter> B then P x \<sqinter> Q x else if x \<in> A then P x else Q x)) \<rhd> R\<close>
  (is \<open>(\<box>a \<in> A \<rightarrow> P a) \<rhd> (\<box>b \<in> B \<rightarrow> Q b) \<rhd> R = ?term \<rhd> R\<close>)
proof (subst Sliding_def, subst Mprefix_Det_Mprefix)
  have \<open>Mprefix B Q \<sqinter> (Mprefix A P \<box> Mprefix B Q) \<rhd> R = Mprefix A P \<box> Mprefix B Q \<rhd> R\<close>
    by (metis (no_types, opaque_lifting) Det_assoc Det_commute Ndet_commute
              Ndet_distrib_Det_left Ndet_id Sliding_Det Sliding_assoc Sliding_def)
  thus \<open>?term \<sqinter> Mprefix B Q \<rhd> R = ?term \<rhd> R\<close>
    by (simp add: Mprefix_Det_Mprefix Ndet_commute)
qed


lemma Mprefix_Sliding_Seq: 
  \<open>(\<box>a \<in> A \<rightarrow> P a) \<rhd> P' \<^bold>; Q = (\<box>a \<in> A \<rightarrow> (P a \<^bold>; Q)) \<rhd> (P' \<^bold>; Q)\<close>
proof (subst Mprefix_Seq[symmetric])
  show \<open>((\<box>a \<in> A \<rightarrow> P a) \<rhd> P') \<^bold>; Q = 
        ((\<box>a \<in> A \<rightarrow> P a) \<^bold>; Q) \<rhd> (P' \<^bold>; Q)\<close> (is \<open>?lhs = ?rhs\<close>)
  proof (subst Process_eq_spec, safe)
    show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close> for s
      by (simp add: D_Sliding D_Seq T_Sliding) blast
  next
    show \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ?lhs\<close> for s
      by (auto simp add: D_Sliding D_Seq T_Sliding)
  next
    show \<open>(s, X) \<in> \<F> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for s X
      by (cases s; simp add: F_Sliding D_Sliding T_Sliding F_Seq) metis
  next
    show \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for s X
      by (cases s; simp add: F_Sliding D_Sliding T_Sliding
                             F_Seq D_Seq T_Seq D_Mprefix T_Mprefix)
         (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(4) hd_append list.sel(1), blast)
  qed
qed



lemma Throw_Sliding :
  \<open>(\<box>a \<in> A \<rightarrow> P a) \<rhd> P' \<Theta> b \<in> B. Q b = 
   (\<box>a \<in> A \<rightarrow> (if a \<in> B then Q a else P a \<Theta> b \<in> B. Q b)) \<rhd> (P' \<Theta> b \<in> B. Q b)\<close>
  (is \<open>?lhs = ?rhs\<close>)
proof (subst Process_eq_spec_optimized, safe)
  fix s
  assume \<open>s \<in> \<D> ?lhs\<close>
  then consider t1 t2 where \<open>s = t1 @ t2\<close> \<open>t1 \<in> \<D> (Mprefix A P \<rhd> P')\<close>
                            \<open>tF t1\<close> \<open>set t1 \<inter> ev ` B = {}\<close> \<open>ftF t2\<close>
    | t1 b t2 where \<open>s = t1 @ ev b # t2\<close> \<open>t1 @ [ev b] \<in> \<T> (Mprefix A P \<rhd> P')\<close>
                    \<open>set t1 \<inter> ev ` B = {}\<close> \<open>b \<in> B\<close> \<open>t2 \<in> \<D> (Q b)\<close>
    by (simp add: D_Throw) blast
  thus \<open>s \<in> \<D> ?rhs\<close>
  proof cases
    fix t1 t2 assume * : \<open>s = t1 @ t2\<close> \<open>t1 \<in> \<D> (Mprefix A P \<rhd> P')\<close> \<open>tF t1\<close>
                         \<open>set t1 \<inter> ev ` B = {}\<close> \<open>ftF t2\<close>
    from "*"(2) consider \<open>t1 \<in> \<D> (Mprefix A P)\<close> | \<open>t1 \<in> \<D> P'\<close>
      by (simp add: D_Sliding) blast
    thus \<open>s \<in> \<D> ?rhs\<close>
    proof cases
      assume \<open>t1 \<in> \<D> (Mprefix A P)\<close>
      then obtain a t1' where \<open>t1 = ev a # t1'\<close> \<open>a \<in> A\<close> \<open>t1' \<in> \<D> (P a)\<close>
        by (auto simp add: D_Mprefix image_iff)
      with "*"(1, 3, 4, 5) show \<open>s \<in> \<D> ?rhs\<close>
        by (simp add: D_Sliding D_Mprefix D_Throw) (metis image_eqI)
    next
      from "*"(1, 3, 4, 5)  show \<open>t1 \<in> \<D> P' \<Longrightarrow> s \<in> \<D> ?rhs\<close>
        by (simp add: D_Sliding D_Throw) blast
    qed
  next
    fix t1 b t2 assume * : \<open>s = t1 @ ev b # t2\<close> \<open>t1 @ [ev b] \<in> \<T> (Mprefix A P \<rhd> P')\<close>
                           \<open>set t1 \<inter> ev ` B = {}\<close> \<open>b \<in> B\<close> \<open>t2 \<in> \<D> (Q b)\<close>
    from "*"(2) consider \<open>t1 @ [ev b] \<in> \<T> (Mprefix A P)\<close> | \<open>t1 @ [ev b] \<in> \<T> P'\<close>
      by (simp add: T_Sliding) blast
    thus \<open>s \<in> \<D> ?rhs\<close>
    proof cases
      assume \<open>t1 @ [ev b] \<in> \<T> (Mprefix A P)\<close>
      then obtain a t1'
        where \<open>t1 @ [ev b] = ev a # t1'\<close> \<open>a \<in> A\<close> \<open>t1' \<in> \<T> (P a)\<close>
        by (auto simp add: T_Mprefix)
      with "*"(1, 3, 4, 5) show \<open>s \<in> \<D> ?rhs\<close>
        by (cases t1; simp add: "*"(1) D_Sliding D_Mprefix D_Throw)
           (metis image_eqI)
    next
      from "*"(1, 3, 4, 5) show \<open>t1 @ [ev b] \<in> \<T> P' \<Longrightarrow> s \<in> \<D> ?rhs\<close>
        by (simp add: D_Sliding D_Mprefix D_Throw) blast
    qed
  qed
next
  fix s
  assume \<open>s \<in> \<D> ?rhs\<close>
  then consider \<open>s \<in> \<D> (Throw P' B Q)\<close>
    | \<open>s \<in> \<D> (\<box>a\<in>A \<rightarrow> (if a \<in> B then Q a else Throw (P a) B Q))\<close>
    by (simp add: D_Sliding) blast
  thus \<open>s \<in> \<D> ?lhs\<close>
  proof cases
    show \<open>s \<in> \<D> (Throw P' B Q) \<Longrightarrow> s \<in> \<D> ?lhs\<close>
      by (simp add: D_Throw D_Sliding T_Sliding) blast
  next
    assume \<open>s \<in> \<D> (\<box>a\<in>A \<rightarrow> (if a \<in> B then Q a else Throw (P a) B Q))\<close>
    then obtain a s' 
      where * : \<open>s = ev a # s'\<close> \<open>a \<in> A\<close>
                \<open>s' \<in> \<D> (if a \<in> B then Q a else Throw (P a) B Q)\<close>
      by (cases s; simp add: D_Mprefix) blast
    show \<open>s \<in> \<D> ?lhs\<close>
    proof (cases \<open>a \<in> B\<close>)
      from "*" show \<open>a \<in> B \<Longrightarrow> s \<in> \<D> ?lhs\<close>
        by (simp add: D_Throw T_Sliding T_Mprefix disjoint_iff)
           (metis Nil_elem_T emptyE empty_set self_append_conv2)
    next
      assume \<open>a \<notin> B\<close>
      with "*"(3) consider 
        t1 t2 where \<open>s' = t1 @ t2\<close> \<open>t1 \<in> \<D> (P a)\<close> \<open>tF t1\<close>
                    \<open>set t1 \<inter> ev ` B = {}\<close> \<open>ftF t2\<close>
        | t1 b t2 where \<open>s' = t1 @ ev b # t2\<close> \<open>t1 @ [ev b] \<in> \<T> (P a)\<close>
                        \<open>set t1 \<inter> ev ` B = {}\<close> \<open>b \<in> B\<close> \<open>t2 \<in> \<D> (Q b)\<close>
        by (simp add: D_Throw) blast
      thus \<open>s \<in> \<D> ?lhs\<close>
      proof cases
        fix t1 t2 assume ** : \<open>s' = t1 @ t2\<close> \<open>t1 \<in> \<D> (P a)\<close> \<open>tF t1\<close>
                              \<open>set t1 \<inter> ev ` B = {}\<close> \<open>ftF t2\<close>
        have *** : \<open>s = (ev a # t1) @ t2 \<and> set (ev a # t1) \<inter> ev ` B = {}\<close>
          by (simp add: "*"(1) "**"(1, 4) image_iff \<open>a \<notin> B\<close>)
        from "*" "**"(1, 2, 3, 5) show \<open>s \<in> \<D> ?lhs\<close>
          by (simp add: D_Throw D_Sliding D_Mprefix image_iff)
             (metis "***" event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) tickFree_Cons_iff)
      next
        fix t1 b t2 assume ** : \<open>s' = t1 @ ev b # t2\<close> \<open>t1 @ [ev b] \<in> \<T> (P a)\<close>
                                \<open>set t1 \<inter> ev ` B = {}\<close> \<open>b \<in> B\<close> \<open>t2 \<in> \<D> (Q b)\<close>
        have *** : \<open>s = (ev a # t1 @ [ev b]) @ t2 \<and> set (ev a # t1) \<inter> ev ` B = {}\<close>
          by (simp add: "*"(1) "**"(1, 3) image_iff \<open>a \<notin> B\<close>)
        from "*" "**"(1, 2, 4, 5) show \<open>s \<in> \<D> ?lhs\<close>
          by (simp add: D_Throw T_Sliding T_Mprefix) (metis "***" Cons_eq_appendI)
      qed
    qed
  qed
next
  fix s X
  assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
  assume \<open>(s, X) \<in> \<F> ?lhs\<close>
  then consider \<open>s \<in> \<D> ?lhs\<close>
    | \<open>(s, X) \<in> \<F> (Mprefix A P \<rhd> P')\<close> \<open>set s \<inter> ev ` B = {}\<close>
    | t1 b t2 where \<open>s = t1 @ ev b # t2\<close> \<open>t1 @ [ev b] \<in> \<T> (Mprefix A P \<rhd> P')\<close>
                    \<open>set t1 \<inter> ev ` B = {}\<close> \<open>b \<in> B\<close> \<open>(t2, X) \<in> \<F> (Q b)\<close>
    by (auto simp add: F_Throw D_Throw)
  thus \<open>(s, X) \<in> \<F> ?rhs\<close>
  proof cases
    from same_div D_F show \<open>s \<in> \<D> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> by blast
  next
    show \<open>(s, X) \<in> \<F> (Mprefix A P \<rhd> P') \<Longrightarrow> set s \<inter> ev ` B = {} \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
      by (cases s; simp add: F_Sliding F_Mprefix F_Throw) blast
  next
    fix t1 b t2 assume * : \<open>s = t1 @ ev b # t2\<close> \<open>t1 @ [ev b] \<in> \<T> (Mprefix A P \<rhd> P')\<close>
                           \<open>set t1 \<inter> ev ` B = {}\<close> \<open>b \<in> B\<close> \<open>(t2, X) \<in> \<F> (Q b)\<close>
    from "*"(2) consider \<open>t1 @ [ev b] \<in> \<T> (Mprefix A P)\<close> | \<open>t1 @ [ev b] \<in> \<T> P'\<close>
      by (simp add: T_Sliding) blast
    thus \<open>(s, X) \<in> \<F> ?rhs\<close>
    proof cases
      assume \<open>t1 @ [ev b] \<in> \<T> (Mprefix A P)\<close>
      then obtain a t1'
        where \<open>t1 @ [ev b] = ev a # t1'\<close> \<open>a \<in> A\<close> \<open>t1' \<in> \<T> (P a)\<close>
        by (auto simp add: T_Mprefix)
      with "*"(1, 3, 4, 5) show \<open>(s, X) \<in> \<F> ?rhs\<close>
        by (cases t1; simp add: "*"(1) F_Sliding F_Mprefix F_Throw) blast
    next
      from "*"(1, 3, 4, 5) show \<open>t1 @ [ev b] \<in> \<T> P' \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
        by (simp add: F_Sliding F_Mprefix F_Throw) blast
    qed
  qed
next
  fix s X
  assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
  assume \<open>(s, X) \<in> \<F> ?rhs\<close>
  then consider \<open>s \<in> \<D> ?rhs\<close> | \<open>(s, X) \<in> \<F> (Throw P' B Q)\<close>
    | \<open>s \<noteq> []\<close> \<open>(s, X) \<in> \<F> (\<box>a \<in> A \<rightarrow> (if a \<in> B then Q a else Throw (P a) B Q))\<close>
    by (simp add: F_Sliding D_Sliding) blast
  thus \<open>(s, X) \<in> \<F> ?lhs\<close>
  proof cases
    from same_div D_F show \<open>s \<in> \<D> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> by blast
  next
    show \<open>(s, X) \<in> \<F> (Throw P' B Q) \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
      by (simp add: F_Throw F_Sliding D_Sliding T_Sliding) blast
  next
    assume \<open>s \<noteq> []\<close> \<open>(s, X) \<in> \<F> (\<box>a \<in> A \<rightarrow> (if a \<in> B then Q a else Throw (P a) B Q))\<close>
    then obtain a s'
      where * : \<open>s = ev a # s'\<close> \<open>a \<in> A\<close> 
                \<open>(s', X) \<in> \<F> (if a \<in> B then Q a else Throw (P a) B Q)\<close>
      by (auto simp add: F_Mprefix image_iff)
    show \<open>(s, X) \<in> \<F> ?lhs\<close>
    proof (cases \<open>a \<in> B\<close>)
      assume \<open>a \<in> B\<close>
      have \<open>[ev a] \<in> \<T> (Mprefix A P \<rhd> P')\<close>
        by (simp add: T_Sliding T_Mprefix "*"(2))
      with "*"(1, 3) \<open>a \<in> B\<close> show \<open>(s, X) \<in> \<F> ?lhs\<close>
        by (simp add: F_Throw) (metis append_Nil empty_set inf_bot_left)
    next
      assume \<open>a \<notin> B\<close>
      with "*"(3) consider \<open>s' \<in> \<D> (Throw (P a) B Q)\<close>
        | \<open>(s', X) \<in> \<F> (P a)\<close> \<open>set s' \<inter> ev ` B = {}\<close>
        | t1 b t2 where \<open>s' = t1 @ ev b # t2\<close> \<open>t1 @ [ev b] \<in> \<T> (P a)\<close>
                        \<open>set t1 \<inter> ev ` B = {}\<close> \<open>b \<in> B\<close> \<open>(t2, X) \<in> \<F> (Q b)\<close>
        by (auto simp add: F_Throw D_Throw)
      thus \<open>(s, X) \<in> \<F> ?lhs\<close>
      proof cases
        assume \<open>s' \<in> \<D> (Throw (P a) B Q)\<close>
        hence \<open>s \<in> \<D> ?rhs\<close> by (simp add: "*"(1, 2) D_Sliding D_Mprefix \<open>a \<notin> B\<close>)
        with same_div D_F show \<open>(s, X) \<in> \<F> ?lhs\<close> by blast
      next
        show \<open>(s', X) \<in> \<F> (P a) \<Longrightarrow> set s' \<inter> ev ` B = {} \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
          using "*"(1, 2) \<open>a \<notin> B\<close> by (simp add: F_Throw F_Sliding F_Mprefix) blast
      next
        fix t1 b t2 assume ** : \<open>s' = t1 @ ev b # t2\<close> \<open>t1 @ [ev b] \<in> \<T> (P a)\<close>
                                \<open>set t1 \<inter> ev ` B = {}\<close> \<open>b \<in> B\<close> \<open>(t2, X) \<in> \<F> (Q b)\<close>
        from "**" have *** : \<open>(ev a # t1) @ [ev b] \<in> \<T> (Mprefix A P) \<and> 
                              set (ev a # t1) \<inter> ev ` B = {}\<close>
          by (simp add: T_Mprefix "*"(2) image_iff \<open>a \<notin> B\<close>)
        from "*"(1) "**"(1, 4, 5) "**"(5) show \<open>(s, X) \<in> \<F> ?lhs\<close>
          by (simp add: F_Throw T_Sliding) (metis "***" Cons_eq_appendI)
      qed
    qed
  qed
qed



section \<open>Dealing with \<^const>\<open>SKIP\<close>\<close>

lemma Renaming_Mprefix_Det_SKIP:
  \<open>Renaming ((\<box> a \<in> A \<rightarrow> P a) \<box> SKIP r) f g =
   (\<box>y\<in>f ` A \<rightarrow> \<sqinter> a \<in> {x \<in> A. y = f x}. Renaming (P a) f g) \<box> SKIP (g r)\<close>
  (* TODO: remove Renaming_Mprefix from CSP_Laws, or change the name *)
  by (simp add: Renaming_Det Renaming_Mprefix)


lemma Mprefix_Sliding_SKIP_Seq: \<open>((\<box> a \<in> A \<rightarrow> P a) \<rhd> SKIP r) \<^bold>; Q = (\<box> a \<in> A \<rightarrow> (P a \<^bold>; Q)) \<rhd> Q\<close>
  (* TODO: see if we leave Sliding_SKIP in simp *)
  by (simp del: Sliding_SKIP add: Mprefix_Sliding_Seq)

lemma Mprefix_Det_SKIP_Seq: \<open>((\<box> a \<in> A \<rightarrow> P a) \<box> SKIP r) \<^bold>; Q = (\<box> a \<in> A \<rightarrow> (P a \<^bold>; Q)) \<rhd> Q\<close>
  by (fold Sliding_SKIP) (fact Mprefix_Sliding_SKIP_Seq)


lemma Sliding_Ndet_pseudo_assoc : \<open>(P \<rhd> Q) \<sqinter> R = P \<rhd> Q \<sqinter> R\<close>
  by (metis Ndet_assoc Ndet_distrib_Det_right Ndet_id Sliding_def)

lemma Hiding_Mprefix_Det_SKIP:
  \<open>(\<box> a \<in> A \<rightarrow> P a) \<box> SKIP r \ S =
   (if A \<inter> S = {} then (\<box> a \<in> A \<rightarrow> (P a \ S)) \<box> SKIP r
    else ((\<box> a \<in> (A - S) \<rightarrow> (P a \ S)) \<box> SKIP r) \<sqinter> (\<sqinter> a \<in> (A \<inter> S). (P a \ S)))\<close>
  by (fold Sliding_SKIP)
     (simp del: Sliding_SKIP add: Hiding_Mprefix_Sliding_disjoint
           Hiding_Mprefix_Sliding_non_disjoint Sliding_Ndet_pseudo_assoc)


lemma \<open>s \<noteq> [] \<Longrightarrow> (s, X) \<in> \<F> (P \<box> Q) \<longleftrightarrow> (s, X) \<in> \<F> (P \<sqinter> Q)\<close>
  by (simp add: F_Det F_Ndet)



lemma Mprefix_Det_SKIP_Sync_SKIP :
  \<open>((\<box> a \<in> A \<rightarrow> P a) \<box> SKIP res) \<lbrakk>S\<rbrakk> SKIP res' = 
   (if res = res' then (\<box> a \<in> (A - S) \<rightarrow> (P a \<lbrakk>S\<rbrakk> SKIP res')) \<box> SKIP res'
    else (\<box> a \<in> (A - S) \<rightarrow> (P a \<lbrakk>S\<rbrakk> SKIP res')) \<sqinter> STOP)\<close>
  (is \<open>?lhs = (if res = res' then ?rhs1 else ?rhs2)\<close>)
proof (subst Process_eq_spec_optimized, safe)
  fix s
  assume \<open>s \<in> \<D> ?lhs\<close>
  then obtain a t u r v
    where * : \<open>ftF v\<close> \<open>tF r \<or> v = []\<close> \<open>s = r @ v\<close>
              \<open>r setinterleaves ((ev a # t, u), range tick \<union> ev ` S)\<close>
              \<open>a \<in> A\<close> \<open>t \<in> \<D> (P a)\<close> \<open>u \<in> \<T> (SKIP res')\<close>
    by (simp add: D_Sync D_SKIP D_Det D_Mprefix T_SKIP image_iff) blast
  from "*"(3, 4, 5, 7) have ** : \<open>a \<in> A - S\<close> \<open>s = ev a # tl r @ v\<close>
                                 \<open>tl r setinterleaves ((t, u), range tick \<union> ev ` S)\<close>
    by (auto simp add: image_iff T_SKIP split: if_split_asm)
  have \<open>tl s \<in> \<D> (P a \<lbrakk>S\<rbrakk> SKIP res')\<close>
    by (simp add: D_Sync)
       (metis "*"(1, 2, 6, 7) "**"(2, 3) list.sel(3) tickFree_tl)
  with "**"(1) show \<open>s \<in> \<D> (if res = res' then ?rhs1 else ?rhs2)\<close>
    by (simp add: D_Det D_Ndet D_Mprefix "**"(2))
next
  fix s
  assume \<open>s \<in> \<D> (if res = res' then ?rhs1 else ?rhs2)\<close>
  then obtain a s' where * : \<open>s = ev a # s'\<close> \<open>a \<in> A - S\<close> \<open>s' \<in> \<D> (P a \<lbrakk>S\<rbrakk> SKIP res')\<close>
    by (auto simp add: D_Det D_Ndet D_SKIP D_STOP D_Mprefix image_iff split: if_split_asm)
  then obtain t u r v
    where ** : \<open>ftF v\<close> \<open>tF r \<or> v = []\<close> \<open>s' = r @ v\<close>
               \<open>r setinterleaves ((t, u), range tick \<union> ev ` S)\<close>
               \<open>t \<in> \<D> (P a)\<close> \<open>u \<in> \<T> (SKIP res')\<close>
    by (simp add: D_Sync D_SKIP) blast
  have \<open>(ev a # r) setinterleaves ((ev a # t, u), range tick \<union> ev ` S)\<close>
    using "*"(2) "**"(4, 6) by (auto simp add: T_SKIP)
  with "*"(2) "**"(1, 2, 3, 5, 6) show \<open>s \<in> \<D> ?lhs\<close>
    by (simp add: D_Sync D_SKIP D_Det D_Mprefix T_SKIP image_iff)
       (metis (no_types, opaque_lifting) "*"(1) Cons_eq_appendI event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) tickFree_Cons_iff)
next
  fix s Z
  assume same_div : \<open>\<D> ?lhs = \<D> (if res = res' then ?rhs1 else ?rhs2)\<close>
  assume \<open>(s, Z) \<in> \<F> ?lhs\<close>
  then consider \<open>s \<in> \<D> ?lhs\<close>
    | t u X Y where \<open>(t, X) \<in> \<F> (Mprefix A P \<box> SKIP res)\<close> \<open>(u, Y) \<in> \<F> (SKIP res')\<close>
                    \<open>s setinterleaves ((t, u), range tick \<union> ev ` S)\<close>
                    \<open>Z = (X \<union> Y) \<inter> (range tick \<union> ev ` S) \<union> X \<inter> Y\<close>
    by (simp add: F_Sync D_Sync) blast
  thus \<open>(s, Z) \<in> \<F> (if res = res' then ?rhs1 else ?rhs2)\<close>
  proof cases
    from same_div D_F show \<open>s \<in> \<D> ?lhs \<Longrightarrow> (s, Z) \<in> \<F> (if res = res' then ?rhs1 else ?rhs2)\<close> by blast
  next
    fix t u X Y
    assume * : \<open>(t, X) \<in> \<F> (Mprefix A P \<box> SKIP res)\<close> \<open>(u, Y) \<in> \<F> (SKIP res')\<close>
               \<open>s setinterleaves ((t, u), range tick \<union> ev ` S)\<close>
               \<open>Z = (X \<union> Y) \<inter> (range tick \<union> ev ` S) \<union> X \<inter> Y\<close>    
    from "*"(1) consider \<open>t = []\<close> | \<open>t = [\<checkmark>(res)]\<close> | a t' where \<open>t = ev a # t'\<close>
      by (auto simp add: F_Det F_SKIP F_Mprefix)
    thus \<open>(s, Z) \<in> \<F> (if res = res' then ?rhs1 else ?rhs2)\<close>
    proof cases
      assume \<open>t = []\<close>
      with "*"(2, 3) have \<open>s = []\<close> by (auto simp add: F_SKIP)
      with \<open>t = []\<close> "*"(3)[simplified \<open>t = []\<close>, THEN emptyLeftProperty] "*"(1, 2, 3, 4)
      show \<open>(s, Z) \<in> \<F> (if res = res' then ?rhs1 else ?rhs2)\<close>
        by (auto simp add: F_Det F_Ndet F_Mprefix F_STOP F_SKIP D_SKIP T_SKIP)
    next
      assume \<open>t = [\<checkmark>(res)]\<close>
      with "*"(2, 3) have \<open>res' = res \<and> s = [\<checkmark>(res)]\<close>
        by (cases u; auto simp add: F_SKIP split: if_split_asm)
      with \<open>t = [\<checkmark>(res)]\<close> show \<open>(s, Z) \<in> \<F> (if res = res' then ?rhs1 else ?rhs2)\<close>
        by (simp add: F_Det F_Ndet F_STOP F_SKIP)      
    next
      fix a t' assume \<open>t = ev a # t'\<close>
      with "*"(1, 2, 3) empty_setinterleaving obtain s'
        where ** : \<open>s' setinterleaves ((t', u), range tick \<union> ev ` S)\<close>
                   \<open>s = ev a # s'\<close> \<open>(t', X) \<in> \<F> (P a)\<close> \<open>a \<in> A - S\<close>
        by (auto simp add: F_SKIP F_Det F_Mprefix image_iff split: if_split_asm)
      from "*"(2, 4) "**"(1, 3) have \<open>(s', Z) \<in> \<F> (P a \<lbrakk>S\<rbrakk> SKIP res')\<close>
        by (simp add: F_Sync) blast  
      with "**"(4) show \<open>(s, Z) \<in> \<F> (if res = res' then ?rhs1 else ?rhs2)\<close>
        by (simp add: F_Det F_Ndet \<open>s = ev a # s'\<close> F_SKIP F_Mprefix)
    qed
  qed
next
  fix s Z
  assume same_div : \<open>\<D> ?lhs = \<D> (if res = res' then ?rhs1 else ?rhs2)\<close>
  assume \<open>(s, Z) \<in> \<F> (if res = res' then ?rhs1 else ?rhs2)\<close>
  then consider \<open>res = res'\<close> \<open>(s, Z) \<in> \<F> ?rhs1\<close>
    | \<open>res \<noteq> res'\<close> \<open>(s, Z) \<in> \<F> ?rhs2\<close> by presburger
  thus \<open>(s, Z) \<in> \<F> ?lhs\<close>
  proof cases
    assume \<open>res = res'\<close> \<open>(s, Z) \<in> \<F> ?rhs1\<close>
    then consider \<open>s = []\<close> | \<open>s = [\<checkmark>(res')]\<close> | a s' where \<open>s = ev a # s'\<close>
      by (auto simp add: F_Det F_SKIP F_Mprefix)
    thus \<open>(s, Z) \<in> \<F> ?lhs\<close>
    proof cases
      assume \<open>s = []\<close>
      with \<open>(s, Z) \<in> \<F> ?rhs1\<close> have \<open>tick res' \<notin> Z\<close>
        by (auto simp add: F_Det F_Mprefix F_SKIP D_SKIP T_SKIP)
      with \<open>s = []\<close> show \<open>(s, Z) \<in> \<F> ?lhs\<close>
        by (simp add: F_Sync F_Det T_SKIP F_SKIP \<open>res = res'\<close>)
           (metis Int_Un_eq(3) si_empty1 Un_Int_eq(4) Un_commute insertI1)
    next
      assume \<open>s = [\<checkmark>(res')]\<close>
      hence * : \<open>([\<checkmark>(res')], Z) \<in> \<F> (Mprefix A P \<box> SKIP res') \<and> 
                 s setinterleaves (([\<checkmark>(res')], [\<checkmark>(res')]), range tick \<union> ev ` S) \<and> 
                 ([\<checkmark>(res')], Z) \<in> \<F> (SKIP res') \<and> Z = (Z \<union> Z) \<inter> (range tick \<union> ev ` S) \<union> Z \<inter> Z\<close>
        by (simp add: F_Det F_SKIP)
      show \<open>(s, Z) \<in> \<F> ?lhs\<close> by (simp add: F_Sync \<open>res = res'\<close>) (meson "*")
    next
      fix a s' assume \<open>s = ev a # s'\<close>
      with \<open>(s, Z) \<in> \<F> ?rhs1\<close> have * : \<open>a \<in> A\<close> \<open>a \<notin> S\<close> \<open>(s', Z) \<in> \<F> (P a \<lbrakk>S\<rbrakk> SKIP res')\<close>
        by (simp_all add: F_Det F_SKIP F_Mprefix image_iff)
      from "*"(3) consider \<open>s' \<in> \<D> (P a \<lbrakk>S\<rbrakk> SKIP res')\<close>
        | t u X Y where \<open>(t, X) \<in> \<F> (P a)\<close> \<open>(u, Y) \<in> \<F> (SKIP res')\<close>
                        \<open>s' setinterleaves ((t, u), range tick \<union> ev ` S)\<close>
                        \<open>Z = (X \<union> Y) \<inter> (range tick \<union> ev ` S) \<union> X \<inter> Y\<close>
        by (simp add: F_Sync D_Sync) blast
      thus \<open>(s, Z) \<in> \<F> ?lhs\<close>
      proof cases
        assume \<open>s' \<in> \<D> (P a \<lbrakk>S\<rbrakk> SKIP res')\<close>
        hence \<open>s \<in> \<D> ?rhs1\<close>
          by (simp add: D_Det D_Mprefix image_iff "*"(1, 2) \<open>s = ev a # s'\<close>)
        with same_div show \<open>(s, Z) \<in> \<F> ?lhs\<close> by (simp add: \<open>res = res'\<close> is_processT8)
      next
        fix t u X Y assume ** : \<open>(t, X) \<in> \<F> (P a)\<close> \<open>(u, Y) \<in> \<F> (SKIP res')\<close>
                                \<open>s' setinterleaves ((t, u), range tick \<union> ev ` S)\<close>
                                \<open>Z = (X \<union> Y) \<inter> (range tick \<union> ev ` S) \<union> X \<inter> Y\<close>
        from "**"(2, 3) have \<open>(ev a # s') setinterleaves ((ev a # t, u), range tick \<union> ev ` S)\<close>
          by (auto simp add: "*"(1, 2) F_SKIP image_iff)
        thus \<open>(s, Z) \<in> \<F> ?lhs\<close>
          by (simp add: F_Sync F_Det F_Mprefix image_iff)
             (metis "*"(1) "**"(1, 2, 4) \<open>s = ev a # s'\<close> list.distinct(1))
      qed
    qed
  next
    assume \<open>res \<noteq> res'\<close> \<open>(s, Z) \<in> \<F> ?rhs2\<close>
    then consider \<open>s = []\<close>
      | a s' where \<open>a \<in> A\<close> \<open>a \<notin> S\<close> \<open>s = ev a # s'\<close> \<open>(s', Z) \<in> \<F> (P a \<lbrakk>S\<rbrakk> SKIP res')\<close>
      by (auto simp add: F_Ndet F_STOP F_Mprefix)
    thus \<open>(s, Z) \<in> \<F> ?lhs\<close>
    proof cases
      have \<open>([], UNIV) \<in> \<F> ?lhs\<close>
        apply (simp add: F_Sync, rule disjI1)
        apply (rule_tac x = \<open>[]\<close> in exI, simp add: F_Det F_Mprefix F_SKIP T_SKIP D_SKIP)
        apply (rule_tac x = \<open>[]\<close> in exI, rule_tac x = \<open>UNIV - {\<checkmark>(res)}\<close> in exI)
        apply (simp, rule_tac x = \<open>UNIV - {\<checkmark>(res')}\<close> in exI)
        using \<open>res \<noteq> res'\<close> by auto
      thus \<open>s = [] \<Longrightarrow> (s, Z) \<in> \<F> ?lhs\<close> by (auto intro: is_processT4)
    next
      fix a s' assume * : \<open>a \<in> A\<close> \<open>a \<notin> S\<close> \<open>s = ev a # s'\<close> \<open>(s', Z) \<in> \<F> (P a \<lbrakk>S\<rbrakk> SKIP res')\<close>
      from "*"(4) consider \<open>s' \<in> \<D> (P a \<lbrakk>S\<rbrakk> SKIP res')\<close>
        | t u X Y where \<open>(t, X) \<in> \<F> (P a)\<close> \<open>(u, Y) \<in> \<F> (SKIP res')\<close>
                        \<open>s' setinterleaves ((t, u), range tick \<union> ev ` S)\<close>
                        \<open>Z = (X \<union> Y) \<inter> (range tick \<union> ev ` S) \<union> X \<inter> Y\<close>
        by (auto simp add: F_Sync D_Sync)
      thus \<open>(s, Z) \<in> \<F> ?lhs\<close>
      proof cases
        assume \<open>s' \<in> \<D> (P a \<lbrakk>S\<rbrakk> SKIP res')\<close>
        hence \<open>s \<in> \<D> ?rhs2\<close> by (simp add: "*"(1, 2, 3) D_Ndet D_Mprefix)
        with same_div show \<open>(s, Z) \<in> \<F> ?lhs\<close> by (simp add: \<open>res \<noteq> res'\<close> is_processT8)
      next
        fix t u X Y assume ** : \<open>(t, X) \<in> \<F> (P a)\<close> \<open>(u, Y) \<in> \<F> (SKIP res')\<close>
                                \<open>s' setinterleaves ((t, u), range tick \<union> ev ` S)\<close>
                                \<open>Z = (X \<union> Y) \<inter> (range tick \<union> ev ` S) \<union> X \<inter> Y\<close>
        show \<open>(s, Z) \<in> \<F> ?lhs\<close>
          apply (simp add: F_Sync, rule disjI1)
          apply (rule_tac x = \<open>ev a # t\<close> in exI)
          apply (rule_tac x = u in exI)
          apply (rule_tac x = X in exI)
          apply (rule conjI, solves \<open>simp add: F_Det F_Mprefix "*"(1) "**"(1)\<close>)
          apply (rule_tac x = Y in exI)
          apply (simp add: "**"(2, 4))
          using "**"(2, 3) by (auto simp add: "*"(1, 2, 3) F_SKIP)
      qed
    qed
  qed
qed


lemma Sliding_def_bis : \<open>P \<rhd> Q = (P \<sqinter> Q) \<box> Q\<close>
  by (simp add: Det_distrib_Ndet_right Sliding_def)





  
(* 
lemma Sliding_Sync : \<open>P \<rhd> Q \<lbrakk>S\<rbrakk> R = (P \<lbrakk>S\<rbrakk> R) \<rhd> (Q \<lbrakk>S\<rbrakk> R) \<sqinter> (P \<rhd> Q \<lbrakk>S\<rbrakk> R)\<close>
  
  sorry

lemma Sync_Sliding : \<open>P \<lbrakk>S\<rbrakk> Q \<rhd> R = (P \<lbrakk>S\<rbrakk> Q) \<rhd> (P \<lbrakk>S\<rbrakk> R) \<sqinter> (P \<lbrakk>S\<rbrakk> Q \<rhd> R)\<close>
  by (metis Sliding_Sync Sync_commute) *)


(* lemma Sliding_Sync_Sliding :
  \<open>P \<rhd> Q \<lbrakk>B\<rbrakk> R \<rhd> S = (P \<lbrakk>B\<rbrakk> R) \<rhd> ((Q \<lbrakk>B\<rbrakk> R \<rhd> S) \<sqinter> (P \<rhd> Q \<lbrakk>B\<rbrakk> S))\<close>
  (is \<open>?lhs = ?rhs\<close>)
proof (subst Process_eq_spec_optimized, safe)
  show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close> for s
    by (simp add: D_Sync, elim exE conjE disjE)
       (simp add: D_Sync D_Sliding D_Ndet T_Sliding, use front_tickFree_Nil in blast)+
next
  show \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ?lhs\<close> for s
    by (simp add: D_Sliding D_Ndet, elim disjE)
       (simp add: D_Sync D_Sliding T_Sliding, blast)+
next
  fix s Z
  assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
  assume \<open>(s, Z) \<in> \<F> ?lhs\<close>
  with F_T setinterleaving_sym front_tickFree_Nil consider \<open>s \<in> \<D> ?lhs\<close>
    | \<open>\<exists>t u X Y. (t, X) \<in> \<F> (P \<rhd> Q) \<and> t \<notin> \<D> P \<and> (u, Y) \<in> \<F> (R \<rhd> S) \<and> u \<notin> \<D> R \<and>
                 s setinterleaves ((t, u), insert tick (ev ` B)) \<and>
                 Z = (X \<union> Y) \<inter> insert tick (ev ` B) \<union> X \<inter> Y\<close>
    by (simp add: F_Sync D_Sync D_Sliding, blast)
  thus \<open>(s, Z) \<in> \<F> ?rhs\<close>
  proof cases
    from same_div D_F show \<open>s \<in> \<D> ?lhs \<Longrightarrow> (s, Z) \<in> \<F> ?rhs\<close> by blast
  next
    assume \<open>\<exists>t u X Y. (t, X) \<in> \<F> (P \<rhd> Q) \<and> t \<notin> \<D> P \<and> (u, Y) \<in> \<F> (R \<rhd> S) \<and> u \<notin> \<D> R \<and>
                      s setinterleaves ((t, u), insert tick (ev ` B)) \<and>
                      Z = (X \<union> Y) \<inter> insert tick (ev ` B) \<union> X \<inter> Y\<close>
    then obtain t u X Y
      where * : \<open>(t, X) \<in> \<F> (P \<rhd> Q)\<close> \<open>t \<notin> \<D> P\<close> \<open>(u, Y) \<in> \<F> (R \<rhd> S)\<close> \<open>u \<notin> \<D> R\<close>
                \<open>s setinterleaves ((t, u), insert tick (ev ` B))\<close>
                \<open>Z = (X \<union> Y) \<inter> insert tick (ev ` B) \<union> X \<inter> Y\<close> by blast
    from "*"(1, 2, 3, 4)
    have \<open>(t, X) \<in> \<F> Q \<or> t \<noteq> [] \<and> (t, X) \<in> \<F> P \<or> t = [] \<and> tick \<notin> X \<and> [tick] \<in> \<T> P\<close>
     and \<open>(u, Y) \<in> \<F> S \<or> u \<noteq> [] \<and> (u, Y) \<in> \<F> R \<or> u = [] \<and> tick \<notin> Y \<and> [tick] \<in> \<T> R\<close>
      by (auto simp add: F_Sliding)
    with "*"(5, 6) show \<open>(s, Z) \<in> \<F> ?rhs\<close>
      apply (elim disjE; simp add: F_Sliding F_Ndet F_Sync )
              apply (metis+)[5]
         apply (metis empty_setinterleaving)
        apply (metis empty_setinterleaving is_processT6_S2)
      apply (metis emptyLeftProperty is_processT6_S2)
      by (simp add: T_Sync) (metis "*"(5) addSync insertCI self_append_conv2)
  qed
next
  fix s Z
  assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
  assume \<open>(s, Z) \<in> \<F> ?rhs\<close> 
  then consider \<open>s \<in> \<D> ?rhs\<close> | \<open>(s, Z) \<in> \<F> ?rhs\<close> \<open>s \<notin> \<D> ?rhs\<close> by fast
  thus \<open>(s, Z) \<in> \<F> ?lhs\<close>
  proof cases
    oops *)
  
  
  (* 
  
  oops


  show \<open>(s, Z) \<in> \<F> ?rhs \<Longrightarrow> (s, Z) \<in> \<F> ?lhs\<close>
    apply (rule ccontr)
    apply (auto simp add: F_Sync F_Sliding F_Ndet D_Sliding D_Ndet T_Sliding)
                        apply metis+
                        apply (metis append.right_neutral front_tickFree_Nil)+
     defer apply 
    apply (metis append.right_neutral front_tickFree_Nil)+ 
    apply (metis BOT_iff_D Nil_elem_T Sync.si_empty1 Sync_is_BOT_iff insertCI)+

    apply (auto simp add: T_Sync)

    sledgehammer defer sledgehammer defer sledgehammer
    apply (metis T_Sliding Un_iff) defer sledgehammer defer sledgehammer
  then consider \<open>(s, Z) \<in> \<F> (Q \<lbrakk>B\<rbrakk> R \<rhd> S)\<close> | \<open>(s, Z) \<in> \<F> (P \<rhd> Q \<lbrakk>B\<rbrakk> S)\<close>
    | \<open>s \<noteq> []\<close> \<open>(s, Z) \<in> \<F> (P \<lbrakk>B\<rbrakk> R)\<close> \<open>(s, Z) \<notin> \<F> (Q \<lbrakk>B\<rbrakk> R \<rhd> S)\<close> \<open>(s, Z) \<notin> \<F> (P \<rhd> Q \<lbrakk>B\<rbrakk> S)\<close>
    | \<open>s = []\<close> \<open>(s \<in> \<D> (P \<lbrakk>B\<rbrakk> R) \<or> tick \<notin> Z \<and> [tick] \<in> \<T> (P \<lbrakk>B\<rbrakk> R))\<close>
    by (simp add: F_Sliding F_Ndet) blast
  thus \<open>(s, Z) \<in> \<F> ?lhs\<close>
  proof cases
    show \<open>(s, Z) \<in> \<F> (Q \<lbrakk>B\<rbrakk> R \<rhd> S) \<Longrightarrow> (s, Z) \<in> \<F> ?lhs\<close>
      by (simp add: F_Sync F_Sliding T_Sliding D_Sliding; elim disjE; metis)
  next
    show \<open>(s, Z) \<in> \<F> (P \<rhd> Q \<lbrakk>B\<rbrakk> S) \<Longrightarrow> (s, Z) \<in> \<F> ?lhs\<close>
      by (simp add: F_Sync F_Sliding T_Sliding D_Sliding; elim disjE; metis)
  next
    assume assms : \<open>s \<noteq> []\<close> \<open>(s, Z) \<in> \<F> (P \<lbrakk>B\<rbrakk> R)\<close>
      \<open>(s, Z) \<notin> \<F> (Q \<lbrakk>B\<rbrakk> R \<rhd> S)\<close> \<open>(s, Z) \<notin> \<F> (P \<rhd> Q \<lbrakk>B\<rbrakk> S)\<close>
    from assms(2) consider \<open>s \<in> \<D> (P \<lbrakk>B\<rbrakk> R)\<close>
      | \<open>\<exists>t u X Y. (t, X) \<in> \<F> P \<and> (u, Y) \<in> \<F> R \<and>
                   s setinterleaves ((t, u), insert tick (ev ` B)) \<and>
                   Z = (X \<union> Y) \<inter> insert tick (ev ` B) \<union> X \<inter> Y\<close>
      by (simp add: F_Sync D_Sync) blast
    thus \<open>(s, Z) \<in> \<F> ?lhs\<close>
    proof cases
      assume \<open>s \<in> \<D> (P \<lbrakk>B\<rbrakk> R)\<close>
      hence \<open>s \<in> \<D> ?rhs\<close> by (simp add: D_Sliding)
      with same_div D_F show \<open>(s, Z) \<in> \<F> ?lhs\<close> by blast
    next
      assume \<open>\<exists>t u X Y. (t, X) \<in> \<F> P \<and> (u, Y) \<in> \<F> R \<and>
                        s setinterleaves ((t, u), insert tick (ev ` B)) \<and>
                        Z = (X \<union> Y) \<inter> insert tick (ev ` B) \<union> X \<inter> Y\<close>
      then obtain t u X Y
        where * : \<open>(t, X) \<in> \<F> P\<close> \<open>(u, Y) \<in> \<F> R\<close>
                  \<open>s setinterleaves ((t, u), insert tick (ev ` B))\<close>
                  \<open>Z = (X \<union> Y) \<inter> insert tick (ev ` B) \<union> X \<inter> Y\<close> by blast
    (*   from "*"(1, 2) have \<open>(t, X) \<in> \<F> (P \<rhd> Q)\<close> and \<open>(u, Y) \<in> \<F> (R \<rhd> S)\<close>
        apply (auto simp add: F_Sliding) *)
      
      from "*"(3) \<open>s \<noteq> []\<close>
      consider \<open>t \<noteq> []\<close> \<open>u \<noteq> []\<close> | \<open>t = []\<close> \<open>u = s\<close> | \<open>t = s\<close> \<open>u = []\<close>
        by (metis setinterleaving_sym emptyLeftProperty)
      thus \<open>(s, Z) \<in> \<F> ?lhs\<close>
      proof cases
        assume \<open>t \<noteq> []\<close> and \<open>u \<noteq> []\<close>
        with "*"(1, 2) have \<open>(t, X) \<in> \<F> (P \<rhd> Q)\<close> and \<open>(u, Y) \<in> \<F> (R \<rhd> S)\<close> 
          by (simp_all add: F_Sliding)
        with "*"(3, 4) show \<open>(s, Z) \<in> \<F> ?lhs\<close> by (simp add: F_Sync) blast
      next
        assume \<open>t = []\<close> and \<open>u = s\<close>
        with "*"(2) \<open>s \<noteq> []\<close> have \<open>(u, Y) \<in> \<F> (R \<rhd> S)\<close> by (simp add: F_Sliding)
        have \<open>(t, X) \<notin> \<F> Q\<close>
        proof (rule ccontr)
          assume \<open>\<not> (t, X) \<notin> \<F> Q\<close>
          with "*"(3, 4) \<open>(u, Y) \<in> \<F> (R \<rhd> S)\<close> have \<open>(s, Z) \<in> \<F> (Q \<lbrakk>B\<rbrakk> R \<rhd> S)\<close>
            by (simp add: F_Sync) blast
          with assms(3) show False by simp
        qed
        from assms(4) "*"(3, 4) consider \<open>(t, X) \<notin> \<F> (P \<rhd> Q)\<close> | \<open>(u, Y) \<notin> \<F> S\<close>
          by (simp add: F_Sync) blast
        thus \<open>(s, Z) \<in> \<F> ?lhs\<close>
        proof cases
          assume \<open>(t, X) \<notin> \<F> (P \<rhd> Q)\<close>
          hence ** : \<open>([], X) \<notin> \<F> Q\<close> \<open>[] \<notin> \<D> P\<close> \<open>tick \<in> X \<or> [tick] \<notin> \<T> P\<close>
            by (simp_all add: F_Sliding \<open>(t, X) \<notin> \<F> Q\<close> \<open>t = []\<close>)
          thus \<open>(s, Z) \<in> \<F> ?lhs\<close>
            apply (simp add: F_Sync)
            apply (rule disjI1)
            apply (auto simp add: F_Sliding) sledgehammer
            sorry
        next
          show \<open>(u, Y) \<notin> \<F> S \<Longrightarrow> (s, Z) \<in> \<F> (P \<rhd> Q \<lbrakk>B\<rbrakk> R \<rhd> S)\<close>
            apply (simp add: F_Sync)
          thm this[simplified F_Sliding, simplified, simplified ]

          oops
          apply (simp add: F_Sync)
          apply (rule disjI1)
          apply (rule_tac x = \<open>[]\<close> in exI, rule_tac x = u in exI, rule_tac x = \<open>{}\<close> in exI)
          apply (simp add: is_processT1)
          apply (rule_tac x = \<open>Z \<union> insert tick (ev ` B)\<close> in exI, intro conjI)
            apply (intro conjI)
          sledgehammer
          apply (meson \<open>(u, Y) \<in> \<F> (R \<rhd> S)\<close> inf_sup_ord(1) is_processT4)
            apply (meson \<open>(u, Y) \<in> \<F> (R \<rhd> S)\<close> inf_sup_ord(1) is_processT4)
defer sledgehammer defer 
          sledgehammer
          using "*"(3) \<open>t = []\<close> apply blast
          using is_processT1 apply blast


          thm F_Sliding


        oops
          using  by blast
      from "*"(3) \<open>s \<noteq> []\<close> have \<open>t \<noteq> [] \<and> u \<noteq> []\<close>
        apply (cases t; cases u; simp split: if_split_asm) sledgehammer
      thus \<open>(s, Z) \<in> \<F> ?lhs\<close>
        
        apply (simp add: F_Sync)
        apply (rule disjI1)
    thm this[simplified F_Sync, simplified]


     apply (simp add: F_Sync F_Sliding, elim conjE disjE, rule disjI1) sledgehammer


    oops
    apply (simp add: F_Sync D_Sliding T_Sliding F_Sliding, elim conjE disjE exE) sledgehammer
    sorry
qed


      oops

  then consider \<open>s \<in> \<D> (P \<lbrakk>B\<rbrakk> R)\<close> | \<open>s \<in> \<D> (Q \<lbrakk>B\<rbrakk> R \<rhd> S)\<close> | \<open>s \<in> \<D> (P \<rhd> Q \<lbrakk>B\<rbrakk> S)\<close>
    by (simp add: D_Sliding D_Ndet) blast
  thus \<open>s \<in> \<D> (?lhs P Q R S)\<close>
  proof cases
    show \<open>s \<in> \<D> (P \<lbrakk>B\<rbrakk> R) \<Longrightarrow> s \<in> \<D> (P \<rhd> Q \<lbrakk>B\<rbrakk> R \<rhd> S)\<close>
      by (simp add: D_Sync D_Sliding T_Sliding) blast
  next
    show \<open>s \<in> \<D> (Q \<lbrakk>B\<rbrakk> R \<rhd> S) \<Longrightarrow> s \<in> \<D> (P \<rhd> Q \<lbrakk>B\<rbrakk> R \<rhd> S)\<close>
      by (simp add: D_Sync D_Sliding T_Sliding) blast
  next
    
  thm this[simplified D_Sliding, simplified]
  

    thm "**"[of u t]

    oops
    sledgehammer
    sorry
 *)
 

(* 
lemma Sliding_Sync_Mprefix :
  \<open>P \<rhd> Q \<lbrakk>S\<rbrakk> (\<box>a \<in> A \<rightarrow> R a) =
   \<box> a \<in> A - S \<rightarrow> ((P \<rhd> Q) \<lbrakk>S\<rbrakk> R a) \<box> ((P \<lbrakk>S\<rbrakk> (\<box>a \<in> A \<rightarrow> R a)) \<rhd> (Q \<lbrakk>S\<rbrakk> (\<box>a \<in> A \<rightarrow> R a)))\<close>
  (is \<open>?lhs = ?rhs\<close>)
  oops
   

 *)

(* 

section \<open>Global Non-Deterministic Choice\<close>

lemma GlobalNdet_Mprefix_distr:
  \<open>A \<noteq> {} \<Longrightarrow> (\<sqinter> a \<in> A. \<box> b \<in> B \<rightarrow> P a b) = \<box> b \<in> B \<rightarrow> (\<sqinter> a \<in> A. P a b)\<close>
  by (auto simp add: Process_eq_spec F_GlobalNdet D_GlobalNdet F_Mprefix D_Mprefix)

lemma GlobalNdet_Mprefix :
  \<open>(\<sqinter> a\<in>A. \<box> b \<in> B a \<rightarrow> P a b) = (if A = {} then STOP else
   (\<sqinter> a\<in>A. \<box> b \<in> B a - (\<Union>a'\<in>{a'\<in>A. a' \<noteq> a}. B a') \<rightarrow> P a b)
   \<box> (\<box> b \<in> (\<Inter>a\<in>A. B a) \<rightarrow> \<sqinter>a\<in>A. P a b))\<close>
  (is \<open>?lhs = (if A = {} then STOP else ?rhs)\<close>)
proof (split if_split, intro conjI impI)
  show \<open>A = {} \<Longrightarrow> ?lhs = STOP\<close> by (simp add: GlobalNdet.abs_eq STOP.abs_eq)
next
  show \<open>?lhs = ?rhs\<close> if \<open>A \<noteq> {}\<close>
  proof (subst Process_eq_spec, safe)
    show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close> for s
      apply (auto simp add: \<open>A \<noteq> {}\<close> D_Det D_GlobalNdet D_Mprefix)
      sledgehammer

  apply (auto simp add: Process_eq_spec F_GlobalNdet F_Det)
 *)

(*<*)
end 
(*>*)
