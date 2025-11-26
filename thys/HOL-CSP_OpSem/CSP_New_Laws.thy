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






text \<open>This is a result similar to @{thm [source] Hiding_Mprefix_disjoint}
      when we add a @{const [source] Sliding} in the expression.\<close>

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



subsection \<open>Non-disjoint Sets\<close>

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


text \<open>This is a result similar to @{thm [source] Hiding_Mprefix_non_disjoint}
      when we add a @{const [source] Sliding} in the expression.\<close>

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
      with "*"(1, 3-5) show \<open>s \<in> \<D> ?rhs\<close>
        by (cases t1; simp add: "*"(1) D_Sliding D_Mprefix D_Throw)
           (metis image_eqI)
    next
      from "*"(1, 3-5) show \<open>t1 @ [ev b] \<in> \<T> P' \<Longrightarrow> s \<in> \<D> ?rhs\<close>
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





section \<open>Powerful Results about \<^const>\<open>Hiding\<close>\<close>

theorem Hiding_is_Hiding_restricted_superset_events:
  fixes S :: \<open>'a set\<close> and P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  assumes superset : \<open>\<alpha>(P) \<subseteq> A\<close>
  defines \<open>S' \<equiv> S \<inter> A\<close>
  shows \<open>P \ S = P \ S'\<close>
proof -
  have set_trace_subset : \<open>t \<in> \<T> P \<Longrightarrow> set t \<subseteq> range tick \<union> ev ` \<alpha>(P)\<close> for t
    by (simp add: events_of_def subset_iff image_iff) (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust)
  moreover from superset
  have \<open>set t \<subseteq> range tick \<union> ev ` \<alpha>(P) \<Longrightarrow>
        trace_hide t (ev ` S) = trace_hide t (ev ` S')\<close> for t :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (induct t) (auto simp add: S'_def image_iff subset_iff)
  ultimately have same_trace_hide :
    \<open>t \<in> \<T> P \<Longrightarrow> trace_hide t (ev ` S) = trace_hide t (ev ` S')\<close> for t by blast

  have \<open>isInfHidden_seqRun_strong x P S t \<Longrightarrow> seqRun t x i \<in> \<T> P\<close> for x t S i by simp
  from this[THEN set_trace_subset]
  have \<open>isInfHidden_seqRun_strong x P S t \<Longrightarrow> x i \<in> ev ` \<alpha>(P)\<close> for x t S i
    by (simp add: seqRun_def subset_iff image_iff)
      (metis atLeastLessThan_iff event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(4) le0 lessI)
  moreover have \<open>isInfHidden_seqRun_strong x P S t \<Longrightarrow>
                 trace_hide t (ev ` S) = trace_hide t (ev ` S')\<close> for x t
    by (metis same_trace_hide seqRun_0)
  ultimately have IH_strong_iff :
    \<open>isInfHidden_seqRun_strong x P S t \<longleftrightarrow> isInfHidden_seqRun_strong x P S' t\<close> for x t
    by (safe, auto simp add: S'_def)
      (metis (no_types, lifting) ext S'_def lessI same_trace_hide trace_hide_seqRun_eq_iff)

  show \<open>P \ S = P \ S'\<close>
  proof (subst Process_eq_spec_optimized, safe)
    show \<open>t \<in> \<D> (P \ S) \<Longrightarrow> t \<in> \<D> (P \ S')\<close> for t
    proof (elim D_Hiding_seqRunE disjE exE)
      fix u v assume \<open>ftF v\<close> \<open>tF u\<close> \<open>t = trace_hide u (ev ` S) @ v\<close> \<open>u \<in> \<D> P\<close>
      from \<open>u \<in> \<D> P\<close> D_T same_trace_hide
      have \<open>trace_hide u (ev ` S) = trace_hide u (ev ` S')\<close> by blast
      with \<open>ftF v\<close> \<open>tF u\<close> \<open>u \<in> \<D> P\<close> \<open>t = trace_hide u (ev ` S) @ v\<close>
      show \<open>t \<in> \<D> (P \ S')\<close> unfolding D_Hiding by blast
    next
      fix u v x assume \<open>ftF v\<close> \<open>tF u\<close> \<open>t = trace_hide u (ev ` S) @ v\<close>
        and IH_strong : \<open>isInfHidden_seqRun_strong x P S u\<close>
      have \<open>trace_hide u (ev ` S) = trace_hide u (ev ` S')\<close>
        by (metis IH_strong same_trace_hide seqRun_0)
      moreover from IH_strong have \<open>isInfHidden_seqRun_strong x P S' u\<close>
        by (simp add: IH_strong_iff)
      ultimately show \<open>t \<in> \<D> (P \ S')\<close>
        using \<open>ftF v\<close> \<open>tF u\<close> \<open>t = trace_hide u (ev ` S) @ v\<close>
        by (blast intro: D_Hiding_seqRunI)
    qed
  next
    show \<open>t \<in> \<D> (P \ S') \<Longrightarrow> t \<in> \<D> (P \ S)\<close> for t
    proof (elim D_Hiding_seqRunE disjE exE)
      fix u v assume \<open>ftF v\<close> \<open>tF u\<close> \<open>t = trace_hide u (ev ` S') @ v\<close> \<open>u \<in> \<D> P\<close>
      from \<open>u \<in> \<D> P\<close> D_T same_trace_hide
      have \<open>trace_hide u (ev ` S') = trace_hide u (ev ` S)\<close> by metis
      with \<open>ftF v\<close> \<open>tF u\<close> \<open>u \<in> \<D> P\<close> \<open>t = trace_hide u (ev ` S') @ v\<close>
      show \<open>t \<in> \<D> (P \ S)\<close> unfolding D_Hiding by blast
    next
      fix u v x assume \<open>ftF v\<close> \<open>tF u\<close> \<open>t = trace_hide u (ev ` S') @ v\<close>
        and IH_strong : \<open>isInfHidden_seqRun_strong x P S' u\<close>
      have \<open>trace_hide u (ev ` S') = trace_hide u (ev ` S)\<close>
        by (metis IH_strong same_trace_hide seqRun_0)
      moreover from IH_strong have \<open>isInfHidden_seqRun_strong x P S u\<close>
        by (simp flip: IH_strong_iff)
      ultimately show \<open>t \<in> \<D> (P \ S)\<close>
        using \<open>ftF v\<close> \<open>tF u\<close> \<open>t = trace_hide u (ev ` S') @ v\<close>
        by (blast intro: D_Hiding_seqRunI)
    qed
  next
    fix t X assume same_div : \<open>\<D> (P \ S) = \<D> (P \ S')\<close>
    assume \<open>(t, X) \<in> \<F> (P \ S)\<close>
    then consider \<open>t \<in> \<D> (P \ S)\<close>
      | u where \<open>t = trace_hide u (ev ` S)\<close> \<open>(u, X \<union> ev ` S) \<in> \<F> P\<close>
      unfolding F_Hiding D_Hiding by blast
    thus \<open>(t, X) \<in> \<F> (P \ S')\<close>
    proof cases
      from same_div D_F show \<open>t \<in> \<D> (P \ S) \<Longrightarrow> (t, X) \<in> \<F> (P \ S')\<close> by blast
    next
      fix u assume \<open>t = trace_hide u (ev ` S)\<close> \<open>(u, X \<union> ev ` S) \<in> \<F> P\<close>
      with F_T same_trace_hide have \<open>t = trace_hide u (ev ` S')\<close> by blast
      moreover have \<open>(u, X \<union> ev ` S') \<in> \<F> P\<close>
      proof (rule is_processT4)
        show \<open>(u, X \<union> ev ` S) \<in> \<F> P\<close> by (fact \<open>(u, X \<union> ev ` S) \<in> \<F> P\<close>)
      next
        show \<open>X \<union> ev ` S' \<subseteq> X \<union> ev ` S\<close> unfolding S'_def by blast
      qed
      ultimately show \<open>(t, X) \<in> \<F> (P \ S')\<close> unfolding F_Hiding by blast
    qed
  next
    fix t X assume same_div : \<open>\<D> (P \ S) = \<D> (P \ S')\<close>
    assume \<open>(t, X) \<in> \<F> (P \ S')\<close>
    then consider \<open>t \<in> \<D> (P \ S')\<close>
      | u where \<open>t = trace_hide u (ev ` S')\<close> \<open>(u, X \<union> ev ` S') \<in> \<F> P\<close>
      unfolding F_Hiding D_Hiding by blast
    thus \<open>(t, X) \<in> \<F> (P \ S)\<close>
    proof cases
      from same_div D_F show \<open>t \<in> \<D> (P \ S') \<Longrightarrow> (t, X) \<in> \<F> (P \ S)\<close> by blast
    next
      fix u assume \<open>t = trace_hide u (ev ` S')\<close> \<open>(u, X \<union> ev ` S') \<in> \<F> P\<close>
      with F_T same_trace_hide have \<open>t = trace_hide u (ev ` S)\<close> by metis
      moreover have \<open>(u, X \<union> ev ` S) \<in> \<F> P\<close>
      proof (rule is_processT4[OF add_complementary_events_of_in_failure])
        show \<open>(u, X \<union> ev ` S') \<in> \<F> P\<close> by (fact \<open>(u, X \<union> ev ` S') \<in> \<F> P\<close>)
      next
        from superset show \<open>X \<union> ev ` S \<subseteq> X \<union> ev ` S' \<union> ev ` (- \<alpha>(P))\<close>
          unfolding S'_def by blast
      qed
      ultimately show \<open>(t, X) \<in> \<F> (P \ S)\<close> unfolding F_Hiding by blast
    qed
  qed
qed




corollary Hiding_is_Hiding_restricted_events : \<open>P \ S = P \ S \<inter> \<alpha>(P)\<close>
  by (simp add: Hiding_is_Hiding_restricted_superset_events)

text \<open>This version is closer to the intuition that we may have, but the first one would be more
useful if we don't want to compute the events of a process but know a superset approximation.\<close>



(*<*)
end 
(*>*)
