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

section \<open>Depth Operator\<close>

(*<*)
theory Process_Restriction_Space
  imports "Restriction_Spaces-HOLCF" "HOL-CSP.Basic_CSP_Laws"
begin
  (*>*)

subsection \<open>Definition\<close>

instantiation process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :: (type, type) order_restriction_space
begin

lift_definition restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ::
  \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, nat] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  is \<open>\<lambda>P n. (\<F> P \<union> {(t @ u, X) |t u X. t \<in> \<T> P \<and> length t = n \<and> tF t \<and> ftF u},
             \<D> P \<union> { t @ u     |t u.   t \<in> \<T> P \<and> length t = n \<and> tF t \<and> ftF u})\<close>
proof -
  show \<open>?thesis P n\<close> (is \<open>is_process (?f, ?d)\<close>) for P and n
  proof (unfold is_process_def FAILURES_def fst_conv DIVERGENCES_def snd_conv, intro conjI impI allI)
    show \<open>([], {}) \<in> ?f\<close> by (simp add: process_charn)
  next
    show \<open>(t, X) \<in> ?f \<Longrightarrow> ftF t\<close> for t X
      by simp (meson front_tickFree_append is_processT)
  next
    fix t u
    assume \<open>(t @ u, {}) \<in> ?f\<close>
    then consider \<open>(t @ u, {}) \<in> \<F> P\<close>
      | t' u' where \<open>t @ u = t' @ u'\<close> \<open>t' \<in> \<T> P\<close> \<open>length t' = n\<close> \<open>tF t'\<close> \<open>ftF u'\<close> by blast
    thus \<open>(t, {}) \<in> ?f\<close>
    proof cases
      assume \<open>(t @ u, {}) \<in> \<F> P\<close>
      with is_processT3 have \<open>(t, {}) \<in> \<F> P\<close> by auto
      thus \<open>(t, {}) \<in> ?f\<close> by fast
    next
      fix t' u' assume * : \<open>t @ u = t' @ u'\<close> \<open>t' \<in> \<T> P\<close> \<open>length t' = n\<close> \<open>tF t'\<close> \<open>ftF u'\<close>
      show \<open>(t, {}) \<in> ?f\<close>
      proof (cases \<open>t \<le> t'\<close>)
        assume \<open>t \<le> t'\<close>
        with "*"(2) is_processT3_TR have \<open>t \<in> \<T> P\<close> by auto
        thus \<open>(t, {}) \<in> ?f\<close> by (simp add: T_F)
      next
        assume \<open>\<not> t \<le> t'\<close>
        with "*"(1) have \<open>t = t' @ take (length t - length t') u'\<close>
          by (metis (no_types, lifting) Prefix_Order.prefixI append_Nil2
              diff_is_0_eq nle_le take_all take_append take_eq_Nil)
        with "*"(2, 3, 4, 5) show \<open>(t, {}) \<in> ?f\<close>
          by simp (metis append_take_drop_id front_tickFree_dw_closed)
      qed
    qed
  next
    show \<open>(t, Y) \<in> ?f \<and> X \<subseteq> Y \<Longrightarrow> (t, X) \<in> ?f\<close> for t X Y
      by simp (meson is_processT4)
  next
    show \<open>(t, X) \<in> ?f \<and> (\<forall>c. c \<in> Y \<longrightarrow> (t @ [c], {}) \<notin> ?f) \<Longrightarrow> (t, X \<union> Y) \<in> ?f\<close> for t X Y
      by (auto simp add: is_processT5)
  next
    show \<open>(t @ [\<checkmark>(r)], {}) \<in> ?f \<Longrightarrow> (t, X - {\<checkmark>(r)}) \<in> ?f\<close> for t r X
      by (simp, elim disjE exE, solves \<open>simp add: is_processT6\<close>)
        (metis append_assoc butlast_snoc front_tickFree_dw_closed
          nonTickFree_n_frontTickFree non_tickFree_tick tickFree_append_iff)
  next
    from front_tickFree_append is_processT7 tickFree_append_iff
    show \<open>t \<in> ?d \<and> tF t \<and> ftF u \<Longrightarrow> t @ u \<in> ?d\<close> for t u by fastforce
  next
    from D_F show \<open>t \<in> ?d \<Longrightarrow> (t, X) \<in> ?f\<close> for t X by blast
  next
    show \<open>t @ [\<checkmark>(r)] \<in> ?d \<Longrightarrow> t \<in> ?d\<close> for t r
      by simp (metis butlast_append butlast_snoc front_tickFree_iff_tickFree_butlast is_processT9
          non_tickFree_tick tickFree_Nil tickFree_append_iff tickFree_imp_front_tickFree)
  qed
qed



subsection \<open>Projections\<close>

context fixes P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> begin

lemma F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>\<F> (P \<down> n) = \<F> P \<union> {(t @ u, X) |t u X. t \<in> \<T> P \<and> length t = n \<and> tF t \<and> ftF u}\<close>
  by (simp add: Failures_def FAILURES_def restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.rep_eq)     

lemma D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>\<D> (P \<down> n) = \<D> P \<union> {t @ u |t u. t \<in> \<T> P \<and> length t = n \<and> tF t \<and> ftF u}\<close>
  by (simp add: Divergences_def DIVERGENCES_def restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.rep_eq)

lemma T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>\<T> (P \<down> n) = \<T> P \<union> {t @ u |t u. t \<in> \<T> P \<and> length t = n \<and> tF t \<and> ftF u}\<close>
  using F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by (auto simp add: Failures_def Traces_def TRACES_def)

lemmas restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs = F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k


lemma D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE:
  assumes \<open>t \<in> \<D> (P \<down> n)\<close>
  obtains \<open>t \<in> \<D> P\<close> and \<open>length t \<le> n\<close>
  | u v where \<open>t = u @ v\<close> \<open>u \<in> \<T> P\<close> \<open>length u = n\<close> \<open>tF u\<close> \<open>ftF v\<close>
proof -
  note assms = that
  from \<open>t \<in> \<D> (P \<down> n)\<close> have \<open>ftF t\<close> by (simp add: D_imp_front_tickFree)
  from \<open>t \<in> \<D> (P \<down> n)\<close> consider \<open>t \<in> \<D> P\<close>
    | u v where \<open>t = u @ v\<close> \<open>u \<in> \<T> P\<close> \<open>length u = n\<close> \<open>tF u\<close> \<open>ftF v\<close>
    by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) blast
  thus thesis
  proof cases
    show \<open>t = u @ v \<Longrightarrow> u \<in> \<T> P \<Longrightarrow> length u = n \<Longrightarrow> tF u \<Longrightarrow> ftF v \<Longrightarrow> thesis\<close> for u v
      by (fact assms(2))
  next
    show thesis if \<open>t \<in> \<D> P\<close>
    proof (cases \<open>length t \<le> n\<close>)
      from \<open>t \<in> \<D> P\<close> show \<open>length t \<le> n \<Longrightarrow> thesis\<close> by (rule assms(1))
    next
      show thesis if \<open>\<not> length t \<le> n\<close>
      proof (intro assms(2) exI)
        show \<open>t = take n t @ drop n t\<close> by simp
      next
        show \<open>take n t \<in> \<T> P\<close> by (metis D_T \<open>t \<in> \<D> P\<close> append_take_drop_id is_processT3_TR_append)
      next
        show \<open>length (take n t) = n\<close> by (simp add: min_def \<open>\<not> length t \<le> n\<close>)
      next
        show \<open>tF (take n t)\<close> by (metis \<open>ftF t\<close> append_take_drop_id drop_eq_Nil2
              front_tickFree_append_iff \<open>\<not> length t \<le> n\<close>)
      next
        show \<open>ftF (drop n t)\<close> by (metis \<open>ftF t\<close> append_take_drop_id drop_eq_Nil
              front_tickFree_append_iff that)
      qed
    qed
  qed
qed


lemma F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE :
  assumes \<open>(t, X) \<in> \<F> (P \<down> n)\<close>
  obtains \<open>(t, X) \<in> \<F> P\<close> and \<open>length t \<le> n\<close>
  | u v where \<open>t = u @ v\<close> \<open>u \<in> \<T> P\<close> \<open>length u = n\<close> \<open>tF u\<close> \<open>ftF v\<close>
proof -
  from \<open>(t, X) \<in> \<F> (P \<down> n)\<close> consider \<open>(t, X) \<in> \<F> P\<close> | \<open>t \<in> \<D> (P \<down> n)\<close>
    unfolding restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
  thus thesis
  proof cases
    show \<open>(t, X) \<in> \<F> P \<Longrightarrow> thesis\<close>
      by (metis F_T F_imp_front_tickFree append_take_drop_id
          drop_eq_Nil front_tickFree_nonempty_append_imp
          is_processT3_TR_append length_take min_def that)
  next
    show \<open>t \<in> \<D> (P \<down> n) \<Longrightarrow> thesis\<close> by (meson D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE is_processT8 that)
  qed
qed


lemma T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE :
  \<open>\<lbrakk>t \<in> \<T> (P \<down> n); t \<in> \<T> P \<Longrightarrow> length t \<le> n \<Longrightarrow> thesis;
    \<And>u v. t = u @ v \<Longrightarrow> u \<in> \<T> P \<Longrightarrow> length u = n \<Longrightarrow> tF u \<Longrightarrow> ftF v \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis\<close>
  by (fold T_F_spec, elim F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE) (simp_all add: T_F)


lemmas restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_elims =
  F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE


lemma D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI :
  \<open>t \<in> \<D> P \<or> t \<in> \<T> P \<and> (length t = n \<and> tF t \<or> n < length t) \<Longrightarrow> t \<in> \<D> (P \<down> n)\<close>
  by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, elim disjE conjE)
    (solves simp, use front_tickFree_Nil in blast, 
      metis (no_types) T_imp_front_tickFree append_self_conv front_tickFree_nonempty_append_imp
      id_take_nth_drop is_processT3_TR_append leD length_take min.absorb4 take_all_iff)

lemma F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI :
  \<open>(t, X) \<in> \<F> P \<or> t \<in> \<T> P \<and> (length t = n \<and> tF t \<or> n < length t) \<Longrightarrow> (t, X) \<in> \<F> (P \<down> n)\<close>
  by (metis (mono_tags, lifting) D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Un_iff is_processT8)

lemma T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI :
  \<open>t \<in> \<T> P \<or> t \<in> \<T> P \<and> (length t = n \<and> tF t \<or> n < length t) \<Longrightarrow> t \<in> \<T> (P \<down> n)\<close>
  using F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI T_F_spec by blast



lemma F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Suc_length_iff_F :
  \<open>(t, X) \<in> \<F> (P \<down> Suc (length t)) \<longleftrightarrow> (t, X) \<in> \<F> P\<close>
  and D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Suc_length_iff_D :
  \<open>t \<in> \<D> (P \<down> Suc (length t)) \<longleftrightarrow> t \<in> \<D> P\<close>
  and T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Suc_length_iff_T :
  \<open>t \<in> \<T> (P \<down> Suc (length t)) \<longleftrightarrow> t \<in> \<T> P\<close>
  by (auto simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)


lemma length_less_in_F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>length t < n \<Longrightarrow> (t, X) \<in> \<F> (P \<down> n) \<Longrightarrow> (t, X) \<in> \<F> P\<close>
  by (auto elim: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)

lemma length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>length t \<le> n \<Longrightarrow> t \<in> \<T> (P \<down> n) \<Longrightarrow> t \<in> \<T> P\<close>
  by (auto elim: T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)

lemma length_less_in_D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>length t < n \<Longrightarrow> t \<in> \<D> (P \<down> n) \<Longrightarrow> t \<in> \<D> P\<close>
  by (auto elim: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)

lemma not_tickFree_in_F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff :
  \<open>length t \<le> n \<Longrightarrow> \<not> tF t \<Longrightarrow> (t, X) \<in> \<F> (P \<down> n) \<longleftrightarrow> (t, X) \<in> \<F> P\<close>
  by (auto simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)

lemma not_tickFree_in_D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff :
  \<open>length t \<le> n \<Longrightarrow> \<not> tF t \<Longrightarrow> t \<in> \<D> (P \<down> n) \<longleftrightarrow> t \<in> \<D> P\<close>
  by (auto simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)

end


(* TODO: move this in HOL-CSP ? *)
lemma front_tickFreeE :
  \<open>\<lbrakk>ftF t; tF t \<Longrightarrow> thesis; \<And>t' r. t = t' @ [\<checkmark>(r)] \<Longrightarrow> tF t' \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis\<close>
  by (metis front_tickFree_append_iff nonTickFree_n_frontTickFree not_Cons_self2)


subsection \<open>Proof obligation\<close>

instance
proof intro_classes
  fix P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  have \<open>P \<down> 0 = \<bottom>\<close> by (simp add: BOT_iff_Nil_D D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  thus \<open>P \<down> 0 \<sqsubseteq>\<^sub>F\<^sub>D Q \<down> 0\<close> by simp
next
  show \<open>P \<down> n \<down> m = P \<down> min n m\<close> for P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and n m
  proof (rule Process_eq_optimizedI)
    show \<open>t \<in> \<D> (P \<down> n \<down> m) \<Longrightarrow> t \<in> \<D> (P \<down> min n m)\<close> for t
      by (elim restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_elims)
        (auto simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k intro: front_tickFree_append)
  next
    show \<open>t \<in> \<D> (P \<down> min n m) \<Longrightarrow> t \<in> \<D> (P \<down> n \<down> m)\<close> for t
      by (elim restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_elims)
        (auto simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs min_def split: if_split_asm)
  next
    fix t X assume \<open>(t, X) \<in> \<F> (P \<down> n \<down> m)\<close> \<open>t \<notin> \<D> (P \<down> n \<down> m)\<close>
    hence \<open>(t, X) \<in> \<F> P \<and> length t \<le> min n m\<close>
      by (elim F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE) (auto simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
    thus \<open>(t, X) \<in> \<F> (P \<down> min n m)\<close> unfolding F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
  next
    fix t X assume \<open>(t, X) \<in> \<F> (P \<down> min n m)\<close> \<open>t \<notin> \<D> (P \<down> min n m)\<close>
    hence \<open>(t, X) \<in> \<F> P \<and> length t \<le> min n m\<close>
      by (elim F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE) (auto simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
    thus \<open>(t, X) \<in> \<F> (P \<down> n \<down> m)\<close> unfolding F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
  qed
next
  show \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> P \<down> n \<sqsubseteq>\<^sub>F\<^sub>D Q \<down> n\<close> for P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and n
    by (simp add: refine_defs restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs
        flip: T_F_spec) blast
next  
  fix P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> assume \<open>\<not> P \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>
  then consider t where \<open>t \<in> \<D> Q\<close> \<open>t \<notin> \<D> P\<close>
    | t X where \<open>(t, X) \<in> \<F> Q\<close> \<open>(t, X) \<notin> \<F> P\<close>
    unfolding refine_defs by auto
  thus \<open>\<exists>n. \<not> P \<down> n \<sqsubseteq>\<^sub>F\<^sub>D Q \<down> n\<close>
  proof cases
    fix t assume \<open>t \<in> \<D> Q\<close> \<open>t \<notin> \<D> P\<close>
    with D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Suc_length_iff_D
    have \<open>t \<in> \<D> (Q \<down> Suc (length t)) \<and> t \<notin> \<D> (P \<down> Suc (length t))\<close> by blast
    hence \<open>\<not> P \<down> Suc (length t) \<sqsubseteq>\<^sub>F\<^sub>D Q \<down> Suc (length t)\<close> unfolding refine_defs by blast
    thus \<open>\<exists>n. \<not> P \<down> n \<sqsubseteq>\<^sub>F\<^sub>D Q \<down> n\<close> ..
  next
    fix t X assume \<open>(t, X) \<in> \<F> Q\<close> \<open>(t, X) \<notin> \<F> P\<close>
    with F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Suc_length_iff_F
    have \<open>(t, X) \<in> \<F> (Q \<down> Suc (length t)) \<and> (t, X) \<notin> \<F> (P \<down> Suc (length t))\<close> by blast
    hence \<open>\<not> P \<down> Suc (length t) \<sqsubseteq>\<^sub>F\<^sub>D Q \<down> Suc (length t)\<close> unfolding refine_defs by blast
    thus \<open>\<exists>n. \<not> P \<down> n \<sqsubseteq>\<^sub>F\<^sub>D Q \<down> n\<close> ..
  qed
qed


\<comment>\<open>Of course, we immediately recover the structure of \<^class>\<open>restriction_space\<close>.\<close>

corollary \<open>OFCLASS(('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, restriction_space_class)\<close>
  by intro_classes

end

instance process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :: (type, type) pcpo_restriction_space
proof intro_classes
  show \<open>P \<down> 0 \<sqsubseteq> Q \<down> 0\<close> for P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (metis below_refl restriction_0_related)
next
  show \<open>P \<down> n \<sqsubseteq> Q \<down> n\<close> if \<open>P \<sqsubseteq> Q\<close> for P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and n
  proof (unfold le_approx_def Refusals_after_def, safe)
    from \<open>P \<sqsubseteq> Q\<close>[THEN le_approx1] \<open>P \<sqsubseteq> Q\<close>[THEN le_approx2T]
    show \<open>t \<in> \<D> (Q \<down> n) \<Longrightarrow> t \<in> \<D> (P \<down> n)\<close> for t
      by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k subset_iff) (metis D_T)
  next
    from \<open>P \<sqsubseteq> Q\<close>[THEN le_approx2] \<open>P \<sqsubseteq> Q\<close>[THEN le_approx_lemma_T]
    show \<open>t \<notin> \<D> (P \<down> n) \<Longrightarrow> (t, X) \<in> \<F> (P \<down> n) \<Longrightarrow> (t, X) \<in> \<F> (Q \<down> n)\<close>
      and \<open>t \<notin> \<D> (P \<down> n) \<Longrightarrow> (t, X) \<in> \<F> (Q \<down> n) \<Longrightarrow> (t, X) \<in> \<F> (P \<down> n)\<close> for t X
      by (auto simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
  next
    from \<open>P \<sqsubseteq> Q\<close>[THEN le_approx3] \<open>P \<sqsubseteq> Q\<close>[THEN le_approx2T]
    show \<open>t \<in> min_elems (\<D> (P \<down> n)) \<Longrightarrow> t \<in> \<T> (Q \<down> n)\<close> for t
      by (simp add: min_elems_def restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs ball_Un subset_iff)
        (metis is_processT7)
  qed
next
  fix P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  assume \<open>\<not> P \<sqsubseteq> Q\<close>
  then consider t where \<open>t \<in> \<D> Q\<close> \<open>t \<notin> \<D> P\<close>
    | t X where \<open>t \<notin> \<D> P\<close> \<open>(t, X) \<in> \<F> P \<longleftrightarrow> (t, X) \<notin> \<F> Q\<close>
    | t where \<open>t \<in> min_elems (\<D> P)\<close> \<open>t \<notin> \<T> Q\<close>
    unfolding le_approx_def Refusals_after_def by blast
  thus \<open>\<exists>n. \<not> P \<down> n \<sqsubseteq> Q \<down> n\<close>
  proof cases
    fix t assume \<open>t \<in> \<D> Q\<close> \<open>t \<notin> \<D> P\<close>
    hence \<open>t \<in> \<D> (Q \<down> Suc (length t))\<close> \<open>t \<notin> \<D> (P \<down> Suc (length t))\<close>
      by (simp_all add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Suc_length_iff_D)
    hence \<open>\<not> P \<down> Suc (length t) \<sqsubseteq> Q \<down> Suc (length t)\<close>
      unfolding le_approx_def by blast
    thus \<open>\<exists>n. \<not> P \<down> n \<sqsubseteq> Q \<down> n\<close> ..
  next
    fix t X assume \<open>t \<notin> \<D> P\<close> \<open>(t, X) \<in> \<F> P \<longleftrightarrow> (t, X) \<notin> \<F> Q\<close>
    hence \<open>t \<notin> \<D> (P \<down> Suc (length t))\<close>
      \<open>(t, X) \<in> \<F> (P \<down> Suc (length t)) \<longleftrightarrow> (t, X) \<notin> \<F> (Q \<down> Suc (length t))\<close>
      by (simp_all add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Suc_length_iff_D
          F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Suc_length_iff_F)
    hence \<open>\<not> P \<down> Suc (length t) \<sqsubseteq> Q \<down> Suc (length t)\<close>
      unfolding le_approx_def Refusals_after_def by blast
    thus \<open>\<exists>n. \<not> P \<down> n \<sqsubseteq> Q \<down> n\<close> ..
  next
    fix t assume \<open>t \<in> min_elems (\<D> P)\<close> \<open>t \<notin> \<T> Q\<close>
    hence \<open>t \<in> min_elems (\<D> (P \<down> Suc (length t)))\<close> \<open>t \<notin> \<T> (Q \<down> Suc (length t))\<close>
      by (simp_all add: min_elems_def D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Suc_length_iff_D
          T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Suc_length_iff_T)
        (meson length_less_in_D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k less_SucI less_length_mono)
    hence \<open>\<not> P \<down> Suc (length t) \<sqsubseteq> Q \<down> Suc (length t)\<close>
      unfolding le_approx_def by blast
    thus \<open>\<exists>n. \<not> P \<down> n \<sqsubseteq> Q \<down> n\<close> ..
  qed
next
  show \<open>chain S \<Longrightarrow> \<exists>P. range S <<| P\<close> for S :: \<open>nat \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (simp add: cpo_class.cpo)
next
  show \<open>\<exists>P :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k. \<forall>Q. P \<sqsubseteq> Q\<close> by blast
qed


setup \<open>Sign.add_const_constraint (\<^const_name>\<open>restriction\<close>, SOME \<^typ>\<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> nat \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>)\<close>
  \<comment> \<open>Only allow \<^const>\<open>restriction\<close> for \<^typ>\<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
     (otherwise we would often have to specify).\<close>



subsection \<open>Compatibility with Refinements\<close>

lemma leF_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI: \<open>P \<down> n \<sqsubseteq>\<^sub>F Q \<down> n\<close>
  if \<open>\<And>s X. (s, X) \<in> \<F> Q \<Longrightarrow> length s \<le> n \<Longrightarrow> (s, X) \<in> \<F> (P \<down> n)\<close>
proof (unfold failure_refine_def, safe)
  show \<open>(s, X) \<in> \<F> (Q \<down> n) \<Longrightarrow> (s, X) \<in> \<F> (P \<down> n)\<close> for s X
  proof (elim F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE exE conjE)
    show \<open>(s, X) \<in> \<F> Q \<Longrightarrow> length s \<le> n \<Longrightarrow> (s, X) \<in> \<F> (P \<down> n)\<close>
      by (simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) (meson F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE that)
  next
    fix s' t'
    assume \<open>s = s' @ t'\<close> \<open>s' \<in> \<T> Q\<close> \<open>length s' = n\<close> \<open>tickFree s'\<close> \<open>front_tickFree t'\<close>
    from \<open>s' \<in> \<T> Q\<close> \<open>length s' = n\<close> have \<open>s' \<in> \<T> P\<close>
      by (metis F_T T_F dual_order.refl length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k that)
    with \<open>s = s' @ t'\<close> \<open>length s' = n\<close> \<open>tickFree s'\<close> \<open>front_tickFree t'\<close>
    show \<open>(s, X) \<in> \<F> (P \<down> n)\<close> by (simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) blast
  qed
qed


lemma leT_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI: \<open>P \<down> n \<sqsubseteq>\<^sub>T Q \<down> n\<close>
  if \<open>\<And>s. s \<in> \<T> Q \<Longrightarrow> length s \<le> n \<Longrightarrow> s \<in> \<T> (P \<down> n)\<close>
proof (unfold trace_refine_def, safe)
  show \<open>s \<in> \<T> (Q \<down> n) \<Longrightarrow> s \<in> \<T> (P \<down> n)\<close> for s
  proof (elim T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE exE conjE)
    show \<open>s \<in> \<T> Q \<Longrightarrow> length s \<le> n \<Longrightarrow> s \<in> \<T> (P \<down> n)\<close>
      by (simp add: T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) (meson T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE that)
  next
    fix s' t'
    assume \<open>s = s' @ t'\<close> \<open>s' \<in> \<T> Q\<close> \<open>length s' = n\<close> \<open>tickFree s'\<close> \<open>front_tickFree t'\<close>
    from \<open>s' \<in> \<T> Q\<close> \<open>length s' = n\<close> have \<open>s' \<in> \<T> P\<close>
      using length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k that by blast
    with \<open>s = s' @ t'\<close> \<open>length s' = n\<close> \<open>tickFree s'\<close> \<open>front_tickFree t'\<close>
    show \<open>s \<in> \<T> (P \<down> n)\<close> by (simp add: T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) blast
  qed
qed


lemma leDT_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI: \<open>P \<down> n \<sqsubseteq>\<^sub>D\<^sub>T Q \<down> n\<close>
  if \<open>\<And>s. s \<in> \<T> Q \<Longrightarrow> length s \<le> n \<Longrightarrow> s \<in> \<T> (P \<down> n)\<close>
    and \<open>\<And>s. length s \<le> n \<Longrightarrow> s \<in> \<D> Q \<Longrightarrow> s \<in> \<D> (P \<down> n)\<close>
proof (rule leD_leT_imp_leDT)
  show \<open>P \<down> n \<sqsubseteq>\<^sub>T Q \<down> n\<close> by (simp add: leT_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI that(1))
next
  show \<open>P \<down> n \<sqsubseteq>\<^sub>D Q \<down> n\<close>
  proof (unfold divergence_refine_def, rule subsetI)
    show \<open>s \<in> \<D> (Q \<down> n) \<Longrightarrow> s \<in> \<D> (P \<down> n)\<close> for s
    proof (elim D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE exE conjE)
      show \<open>s \<in> \<D> Q \<Longrightarrow> length s \<le> n \<Longrightarrow> s \<in> \<D> (P \<down> n)\<close>
        by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) (meson D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE that(2))
    next
      fix s' t'
      assume \<open>s = s' @ t'\<close> \<open>s' \<in> \<T> Q\<close> \<open>length s' = n\<close> \<open>tickFree s'\<close> \<open>front_tickFree t'\<close>
      from \<open>s' \<in> \<T> Q\<close> \<open>length s' = n\<close> have \<open>s' \<in> \<T> P\<close>
        using length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k that(1) by blast
      with \<open>s = s' @ t'\<close> \<open>length s' = n\<close> \<open>tickFree s'\<close> \<open>front_tickFree t'\<close>
      show \<open>s \<in> \<D> (P \<down> n)\<close> by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) blast
    qed
  qed
qed


lemma leFD_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI: \<open>P \<down> n \<sqsubseteq>\<^sub>F\<^sub>D Q \<down> n\<close>
  if \<open>\<And>s X. (s, X) \<in> \<F> Q \<Longrightarrow> length s \<le> n \<Longrightarrow> (s, X) \<in> \<F> (P \<down> n)\<close>
    and \<open>\<And>s. s \<in> \<D> Q \<Longrightarrow> length s \<le> n \<Longrightarrow> s \<in> \<D> (P \<down> n)\<close>
proof (rule leF_leD_imp_leFD)
  show \<open>P \<down> n \<sqsubseteq>\<^sub>F Q \<down> n\<close> by (simp add: leF_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI that(1))
next
  show \<open>P \<down> n \<sqsubseteq>\<^sub>D Q \<down> n\<close>  by (meson T_F_spec leDT_imp_leD leDT_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI that)
qed



subsection \<open>First Laws\<close>

lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_0 [simp] : \<open>P \<down> 0 = \<bottom>\<close>
  by (simp add: BOT_iff_Nil_D D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)

lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_BOT [simp] : \<open>(\<bottom> :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<down> n = \<bottom>\<close>
  by (simp add: BOT_iff_Nil_D D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k D_BOT)

lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_BOT_iff :
  \<open>P \<down> n = \<bottom> \<longleftrightarrow> n = 0 \<or> P = \<bottom>\<close>
  by (auto simp add: BOT_iff_Nil_D D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)


lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_STOP [simp] : \<open>STOP \<down> n = (if n = 0 then \<bottom> else STOP)\<close>
  by (simp add: STOP_iff_T T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k T_STOP)

lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_STOP_iff : \<open>P \<down> n = STOP \<longleftrightarrow> n \<noteq> 0 \<and> P = STOP\<close>
  by (simp add: STOP_iff_T T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set_eq_iff)
    (metis (no_types, lifting) append_self_conv2 front_tickFree_single gr0I
      less_numeral_extra(3) list.discI list.size(3) tickFree_Nil)


lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIP [simp] : \<open>SKIP r \<down> n = (if n = 0 then \<bottom> else SKIP r)\<close>
  by simp (auto simp add: Process_eq_spec restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs SKIP_projs)

lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_SKIP_iff : \<open>P \<down> n = SKIP r \<longleftrightarrow> n \<noteq> 0 \<and> P = SKIP r\<close>
proof (intro iffI conjI)
  show \<open>n \<noteq> 0 \<and> P = SKIP r \<Longrightarrow> P \<down> n = SKIP r\<close> by simp
next
  show \<open>P \<down> n = SKIP r \<Longrightarrow> n \<noteq> 0\<close> by (metis restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_0 SKIP_neq_BOT)
next
  show \<open>P \<down> n = SKIP r \<Longrightarrow> P = SKIP r\<close>
    by (simp add: Process_eq_spec set_eq_iff SKIP_projs
        restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs, safe; metis)
qed


lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_SKIPS [simp] : \<open>SKIPS R \<down> n = (if n = 0 then \<bottom> else SKIPS R)\<close>
  by simp (auto simp add: Process_eq_spec restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs SKIPS_projs)

lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_SKIPS_iff : \<open>P \<down> n = SKIPS R \<longleftrightarrow> n \<noteq> 0 \<and> P = SKIPS R\<close>
proof (cases \<open>R = {}\<close>)
  show \<open>R = {} \<Longrightarrow> P \<down> n = SKIPS R \<longleftrightarrow> n \<noteq> 0 \<and> P = SKIPS R\<close>
    by (simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_STOP_iff)
next
  show \<open>P \<down> n = SKIPS R \<longleftrightarrow> n \<noteq> 0 \<and> P = SKIPS R\<close> if \<open>R \<noteq> {}\<close>
  proof (intro iffI conjI)
    show \<open>n \<noteq> 0 \<and> P = SKIPS R \<Longrightarrow> P \<down> n = SKIPS R\<close> by simp
  next
    show \<open>P \<down> n = SKIPS R \<Longrightarrow> n \<noteq> 0\<close> 
      by (metis BOT_iff_Nil_D D_SKIPS empty_iff restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_0)
  next
    show \<open>P \<down> n = SKIPS R \<Longrightarrow> P = SKIPS R\<close>
      by (simp add: Process_eq_spec \<open>R \<noteq> {}\<close> SKIPS_projs
          restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs, safe; blast)
  qed
qed



subsection \<open>Monotony\<close>

subsubsection \<open>\<^term>\<open>P \<down> n\<close> is an Approximation of the \<^term>\<open>P\<close>\<close>

lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_approx_self : \<open>P \<down> n \<sqsubseteq> P\<close>
proof (unfold le_approx_def Refusals_after_def, safe)
  show \<open>t \<in> \<D> P \<Longrightarrow> t \<in> \<D> (P \<down> n)\<close> for t by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
next
  show \<open>t \<notin> \<D> (P \<down> n) \<Longrightarrow> (t, X) \<in> \<F> (P \<down> n) \<Longrightarrow> (t, X) \<in> \<F> P\<close> for t X
    by (auto simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k elim: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
next
  show \<open>t \<notin> \<D> (P \<down> n) \<Longrightarrow> (t, X) \<in> \<F> P \<Longrightarrow> (t, X) \<in> \<F> (P \<down> n)\<close> for t X
    by (auto simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
next
  show \<open>t \<in> min_elems (\<D> (P \<down> n)) \<Longrightarrow> t \<in> \<T> P\<close> for t
    by (auto simp add: min_elems_def D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ball_Un D_T)
      (metis append.right_neutral front_tickFree_charn less_append nil_less2)
qed

lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD_self : \<open>P \<down> n \<sqsubseteq>\<^sub>F\<^sub>D P\<close>
  by (simp add: le_approx_imp_le_ref restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_approx_self)

lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_F_self : \<open>P \<down> n \<sqsubseteq>\<^sub>F P\<close>
  by (simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD_self leFD_imp_leF)

lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_D_self : \<open>P \<down> n \<sqsubseteq>\<^sub>D P\<close>
  by (simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD_self leFD_imp_leD)

lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_T_self : \<open>P \<down> n \<sqsubseteq>\<^sub>T P\<close>
  by (simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_F_self leF_imp_leT) 

lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DT_self : \<open>P \<down> n \<sqsubseteq>\<^sub>D\<^sub>T P\<close>
  by (simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_D_self restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_T_self leD_leT_imp_leDT)



subsubsection \<open>Monotony of \<^term>\<open>(\<down>)\<close>\<close>

lemma Suc_right_mono_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : \<open>P \<down> n \<sqsubseteq> P \<down> Suc n\<close>
  by (metis restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_approx_self restriction_chainD
      restriction_chain_restrictions)

lemma Suc_right_mono_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD : \<open>P \<down> n \<sqsubseteq>\<^sub>F\<^sub>D P \<down> Suc n\<close>
  by (simp add: Suc_right_mono_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k le_approx_imp_le_ref)

lemma Suc_right_mono_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_F  : \<open>P \<down> n \<sqsubseteq>\<^sub>F P \<down> Suc n\<close>
  by (simp add: Suc_right_mono_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD leFD_imp_leF)

lemma Suc_right_mono_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_D  : \<open>P \<down> n \<sqsubseteq>\<^sub>D P \<down> Suc n\<close>
  by (simp add: Suc_right_mono_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD leFD_imp_leD)

lemma Suc_right_mono_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_T  : \<open>P \<down> n \<sqsubseteq>\<^sub>T P \<down> Suc n\<close>
  by (simp add: Suc_right_mono_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD leFD_imp_leF leF_imp_leT)

lemma Suc_right_mono_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_DT : \<open>P \<down> n \<sqsubseteq>\<^sub>D\<^sub>T P \<down> Suc n\<close>
  by (simp add: Suc_right_mono_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_D
      Suc_right_mono_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_T leD_leT_imp_leDT)


lemma le_right_mono_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : \<open>n \<le> m \<Longrightarrow> P \<down> n \<sqsubseteq> P \<down> m\<close>
  by (metis restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_approx_self restriction_chain_def_ter
      restriction_chain_restrictions)


lemma le_right_mono_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD : \<open>n \<le> m \<Longrightarrow> P \<down> n \<sqsubseteq>\<^sub>F\<^sub>D P \<down> m\<close>
  by (simp add: le_approx_imp_le_ref le_right_mono_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)

lemma le_right_mono_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_F : \<open>n \<le> m \<Longrightarrow> P \<down> n \<sqsubseteq>\<^sub>F P \<down> m\<close>
  by (simp add: leFD_imp_leF le_right_mono_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD)

lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_le_right_mono_D : \<open>n \<le> m \<Longrightarrow> P \<down> n \<sqsubseteq>\<^sub>D P \<down> m\<close>
  by (simp add: leFD_imp_leD le_right_mono_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD)

lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_le_right_mono_T : \<open>n \<le> m \<Longrightarrow> P \<down> n \<sqsubseteq>\<^sub>T P \<down> m\<close>
  by (simp add: leF_imp_leT le_right_mono_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_F)

lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_le_right_mono_DT : \<open>n \<le> m \<Longrightarrow> P \<down> n \<sqsubseteq>\<^sub>D\<^sub>T P \<down> m\<close>
  by (simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_le_right_mono_D
      restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_le_right_mono_T leD_leT_imp_leDT)



subsubsection \<open>Interpretations of Refinements\<close>

lemma ex_not_restriction_leD : \<open>\<exists>n. \<not> P \<down> n \<sqsubseteq>\<^sub>D Q \<down> n\<close> if \<open>\<not> P \<sqsubseteq>\<^sub>D Q\<close>
proof -
  from \<open>\<not> P \<sqsubseteq>\<^sub>D Q\<close> obtain t where \<open>t \<in> \<D> Q\<close> \<open>t \<notin> \<D> P\<close>
    unfolding divergence_refine_def by blast
  hence \<open>t \<in> \<D> (Q \<down> Suc (length t))\<close> \<open>t \<notin> \<D> (P \<down> Suc (length t))\<close>
    by (simp_all add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Suc_length_iff_D)
  hence \<open>\<not> P \<down> Suc (length t) \<sqsubseteq>\<^sub>D Q \<down> Suc (length t)\<close>
    unfolding divergence_refine_def by blast
  thus \<open>\<exists>n. \<not> P \<down> n \<sqsubseteq>\<^sub>D Q \<down> n\<close> ..
qed

interpretation PRS_leF : PreorderRestrictionSpace \<open>(\<down>)\<close> \<open>(\<sqsubseteq>\<^sub>F)\<close>
proof unfold_locales
  show \<open>P \<down> 0 \<sqsubseteq>\<^sub>F Q \<down> 0\<close> for P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> by simp
next
  show \<open>P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> P \<down> n \<sqsubseteq>\<^sub>F Q \<down> n\<close> for P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and n
    by (simp add: failure_refine_def F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
        flip: T_F_spec) blast
next
  fix P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> assume \<open>\<not> P \<sqsubseteq>\<^sub>F Q\<close>
  then obtain t X where \<open>(t, X) \<in> \<F> Q\<close> \<open>(t, X) \<notin> \<F> P\<close>
    unfolding failure_refine_def by auto
  with F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Suc_length_iff_F
  have \<open>(t, X) \<in> \<F> (Q \<down> Suc (length t)) \<and> (t, X) \<notin> \<F> (P \<down> Suc (length t))\<close> by blast
  hence \<open>\<not> P \<down> Suc (length t) \<sqsubseteq>\<^sub>F Q \<down> Suc (length t)\<close> unfolding failure_refine_def by blast
  thus \<open>\<exists>n. \<not> P \<down> n \<sqsubseteq>\<^sub>F Q \<down> n\<close> ..
next
  show \<open>P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> Q \<sqsubseteq>\<^sub>F R \<Longrightarrow> P \<sqsubseteq>\<^sub>F R\<close> for P Q R :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (fact trans_F)
qed


interpretation PRS_leT : PreorderRestrictionSpace \<open>(\<down>)\<close> \<open>(\<sqsubseteq>\<^sub>T)\<close>
proof unfold_locales
  show \<open>P \<down> 0 \<sqsubseteq>\<^sub>T Q \<down> 0\<close> for P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> by simp
next
  show \<open>P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> P \<down> n \<sqsubseteq>\<^sub>T Q \<down> n\<close> for P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and n
    by (auto simp add: trace_refine_def T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
next
  fix P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> assume \<open>\<not> P \<sqsubseteq>\<^sub>T Q\<close>
  then obtain t where \<open>t \<in> \<T> Q\<close> \<open>t \<notin> \<T> P\<close>
    unfolding trace_refine_def by auto
  with T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Suc_length_iff_T
  have \<open>t \<in> \<T> (Q \<down> Suc (length t)) \<and> t \<notin> \<T> (P \<down> Suc (length t))\<close> by blast
  hence \<open>\<not> P \<down> Suc (length t) \<sqsubseteq>\<^sub>T Q \<down> Suc (length t)\<close> unfolding trace_refine_def by blast
  thus \<open>\<exists>n. \<not> P \<down> n \<sqsubseteq>\<^sub>T Q \<down> n\<close> ..
next
  show \<open>P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> Q \<sqsubseteq>\<^sub>T R \<Longrightarrow> P \<sqsubseteq>\<^sub>T R\<close> for P Q R :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (fact trans_T)
qed


interpretation PRS_leDT : PreorderRestrictionSpace \<open>(\<down>)\<close> \<open>(\<sqsubseteq>\<^sub>D\<^sub>T)\<close>
proof unfold_locales
  show \<open>P \<down> 0 \<sqsubseteq>\<^sub>D\<^sub>T Q \<down> 0\<close> for P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> by simp
next
  show \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> P \<down> n \<sqsubseteq>\<^sub>D\<^sub>T Q \<down> n\<close> for P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and n
    by (auto simp add: refine_defs restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
next
  fix P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> assume \<open>\<not> P \<sqsubseteq>\<^sub>D\<^sub>T Q\<close>
  hence \<open>\<not> P \<sqsubseteq>\<^sub>D Q \<or> \<not> P \<sqsubseteq>\<^sub>T Q\<close> unfolding trace_divergence_refine_def by blast
  with ex_not_restriction_leD PRS_leT.ex_not_restriction_related
  have \<open>(\<exists>n. \<not> P \<down> n \<sqsubseteq>\<^sub>D Q \<down> n) \<or> (\<exists>n. \<not> P \<down> n \<sqsubseteq>\<^sub>T Q \<down> n)\<close> by blast
  thus \<open>\<exists>n. \<not> P \<down> n \<sqsubseteq>\<^sub>D\<^sub>T Q \<down> n\<close>
    unfolding trace_divergence_refine_def by blast
next
  show \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> Q \<sqsubseteq>\<^sub>D\<^sub>T R \<Longrightarrow> P \<sqsubseteq>\<^sub>D\<^sub>T R\<close> for P Q R :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    by (fact trans_DT)
qed



subsection \<open>Continuity\<close>

context begin

private lemma chain_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : \<open>chain Y \<Longrightarrow> chain (\<lambda>i. Y i \<down> n)\<close>
  by (simp add: mono_restriction_below po_class.chain_def)


private lemma cont_prem_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>(\<Squnion> i. Y i) \<down> n = (\<Squnion> i. Y i \<down> n)\<close> (is \<open>?lhs = ?rhs\<close>) if \<open>chain Y\<close>
proof (rule Process_eq_optimizedI)
  show \<open>t \<in> \<D> ?lhs \<Longrightarrow> t \<in> \<D> ?rhs\<close> for t
    by (auto simp add: limproc_is_thelub chain_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
        D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k LUB_projs \<open>chain Y\<close>)
next
  show \<open>t \<in> \<D> ?rhs \<Longrightarrow> t \<in> \<D> ?lhs\<close> for t
    by (simp add: limproc_is_thelub chain_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
        D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k LUB_projs \<open>chain Y\<close>)
      (metis D_T append_eq_append_conv is_processT3_TR_append)
next
  show \<open>(t, X) \<in> \<F> ?lhs \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> for t X
    by (auto simp add: limproc_is_thelub chain_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
        F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k LUB_projs \<open>chain Y\<close>)
next
  show \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for s X
    by (simp add: limproc_is_thelub chain_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
        F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k LUB_projs \<open>chain Y\<close>)
      (metis F_T append_eq_append_conv is_processT3_TR_append)
qed


lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_cont [simp] : \<open>cont (\<lambda>x. f x \<down> n)\<close> if \<open>cont f\<close>
proof (rule contI2)
  show \<open>monofun (\<lambda>x. f x \<down> n)\<close>
    by (simp add: cont2monofunE mono_restriction_below monofunI \<open>cont f\<close>)
next
  show \<open>chain Y \<Longrightarrow> f (\<Squnion>i. Y i) \<down> n \<sqsubseteq> (\<Squnion>i. f (Y i) \<down> n)\<close> for Y
    by (simp add: ch2ch_cont cont2contlubE cont_prem_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<open>cont f\<close>)
qed

end



subsection \<open>Completeness\<close>

text \<open>Processes are actually an instance of \<^class>\<open>complete_restriction_space\<close>.\<close>

lemma chain_restriction_chain :
  \<open>restriction_chain \<sigma> \<Longrightarrow> chain \<sigma>\<close> for \<sigma> :: \<open>nat \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  by (metis po_class.chainI restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_approx_self restriction_chainD)


lemma restricted_LUB_restriction_chain_is :
  \<open>(\<lambda>n. (\<Squnion>n. \<sigma> n) \<down> n) = \<sigma>\<close> if \<open>restriction_chain \<sigma>\<close>
proof (rule ext)
  have \<open>chain \<sigma>\<close> by (simp add: chain_restriction_chain \<open>restriction_chain \<sigma>\<close>)
  moreover have \<open>\<sigma> = (\<lambda>n. \<sigma> n \<down> n)\<close>
    by (simp add: restricted_restriction_chain_is \<open>restriction_chain \<sigma>\<close>)
  ultimately have \<open>chain (\<lambda>n. \<sigma> n \<down> n)\<close> by simp

  have \<open>length t < n \<Longrightarrow> t \<in> \<D> (\<sigma> n) \<longleftrightarrow> (\<forall>i. t \<in> \<D> (\<sigma> i))\<close> for t n
  proof safe
    show \<open>t \<in> \<D> (\<sigma> i)\<close> if \<open>length t < n\<close> \<open>t \<in> \<D> (\<sigma> n)\<close> for i
    proof (cases \<open>i \<le> n\<close>)
      from \<open>t \<in> \<D> (\<sigma> n)\<close> \<open>chain \<sigma>\<close> le_approx_def po_class.chain_mono
      show \<open>i \<le> n \<Longrightarrow> t \<in> \<D> (\<sigma> i)\<close> by blast
    next
      from \<open>length t < n\<close> \<open>t \<in> \<D> (\<sigma> n)\<close> show \<open>\<not> i \<le> n \<Longrightarrow> t \<in> \<D> (\<sigma> i)\<close>
        by (induct n, simp_all)
          (metis \<open>restriction_chain \<sigma>\<close> length_less_in_D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
            nat_le_linear restriction_chain_def_ter)
    qed
  next
    show \<open>\<forall>i. t \<in> \<D> (\<sigma> i) \<Longrightarrow> t \<in> \<D> (\<sigma> n)\<close> by simp
  qed
  hence * : \<open>length t < n \<Longrightarrow> t \<in> \<D> (\<sigma> n) \<longleftrightarrow> t \<in> \<D> (\<Squnion>i. \<sigma> i)\<close> for t n
    by (simp add: D_LUB \<open>chain \<sigma>\<close> limproc_is_thelub)

  show \<open>(\<Squnion>n. \<sigma> n) \<down> n = \<sigma> n\<close> for n
  proof (subst (3) \<open>\<sigma> = (\<lambda>n. \<sigma> n \<down> n)\<close>, rule Process_eq_optimizedI)
    show \<open>t \<in> \<D> ((\<Squnion>n. \<sigma> n) \<down> n) \<Longrightarrow> t \<in> \<D> (\<sigma> n \<down> n)\<close> for t
    proof (elim D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
      show \<open>t \<in> \<D> (\<Squnion>n. \<sigma> n) \<Longrightarrow> length t \<le> n \<Longrightarrow> t \<in> \<D> (\<sigma> n \<down> n)\<close>
        by (simp add: \<open>chain \<sigma>\<close> limproc_is_thelub D_LUB D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    next
      show \<open>\<lbrakk>t = u @ v; u \<in> \<T> (\<Squnion>n. \<sigma> n); length u = n; tF u; ftF v\<rbrakk> \<Longrightarrow> t \<in> \<D> (\<sigma> n \<down> n)\<close> for u v
        by (auto simp add: \<open>chain \<sigma>\<close> limproc_is_thelub LUB_projs restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs)
    qed
  next
    fix t assume \<open>t \<in> \<D> (\<sigma> n \<down> n)\<close>
    hence \<open>ftF t\<close> by (simp add: D_imp_front_tickFree)
    with \<open>t \<in> \<D> (\<sigma> n \<down> n)\<close> consider \<open>length t < n\<close> \<open>t \<in> \<D> (\<sigma> n)\<close>
      | t' r where \<open>t = t' @ [\<checkmark>(r)]\<close> \<open>tF t'\<close> \<open>length t' < n\<close> \<open>t' \<in> \<D> (\<sigma> n)\<close>
      | u v  where \<open>t = u @ v\<close> \<open>u \<in> \<T> (\<sigma> n)\<close> \<open>length u = n\<close> \<open>tF u\<close> \<open>ftF v\<close>
      by (auto elim!: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
        (metis D_T Suc_le_lessD antisym_conv2 append.right_neutral
          front_tickFree_Nil front_tickFree_nonempty_append_imp
          is_processT9 length_append_singleton nonTickFree_n_frontTickFree)
    thus \<open>t \<in> \<D> ((\<Squnion>n. \<sigma> n) \<down> n)\<close>
    proof cases
      show \<open>length t < n \<Longrightarrow> t \<in> \<D> (\<sigma> n) \<Longrightarrow> t \<in> \<D> ((\<Squnion>n. \<sigma> n) \<down> n)\<close>
        by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k "*")
    next
      fix t' r assume \<open>t = t' @ [\<checkmark>(r)]\<close> \<open>tF t'\<close> \<open>length t' < n\<close> \<open>t' \<in> \<D> (\<sigma> n)\<close>
      from \<open>length t' < n\<close> \<open>t' \<in> \<D> (\<sigma> n)\<close> have \<open>t' \<in> \<D> ((\<Squnion>n. \<sigma> n) \<down> n)\<close>
        by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k "*")
      thus \<open>t \<in> \<D> ((\<Squnion>n. \<sigma> n) \<down> n)\<close>
        by (simp add: \<open>t = t' @ [\<checkmark>(r)]\<close> \<open>tF t'\<close> is_processT7)
    next
      fix u v assume \<open>t = u @ v\<close> \<open>u \<in> \<T> (\<sigma> n)\<close> \<open>length u = n\<close> \<open>tF u\<close> \<open>ftF v\<close>
      from \<open>length u = n\<close> \<open>u \<in> \<T> (\<sigma> n)\<close> have \<open>u \<in> \<T> (\<sigma> (Suc n))\<close>
        by (metis length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k nat_le_linear
            restriction_chainD \<open>restriction_chain \<sigma>\<close>)
      from \<open>chain \<sigma>\<close> \<open>u \<in> \<T> (\<sigma> (Suc n))\<close> D_T le_approx2T po_class.chain_mono
      have \<open>i \<le> Suc n \<Longrightarrow> u \<in> \<T> (\<sigma> i)\<close> for i by blast
      moreover have \<open>Suc n < i \<Longrightarrow> u \<in> \<T> (\<sigma> i)\<close> for i
        by (subst T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Suc_length_iff_T[symmetric])
          (metis \<open>length u = n\<close> \<open>u \<in> \<T> (\<sigma> (Suc n))\<close>
            restriction_chain_def_bis \<open>restriction_chain \<sigma>\<close>)
      ultimately have \<open>u \<in> \<T> (\<Squnion>i. \<sigma> i)\<close>
        by (metis T_LUB_2 \<open>chain \<sigma>\<close> limproc_is_thelub linorder_not_le)
      with \<open>ftF v\<close> \<open>length u = n\<close> \<open>tF u\<close> show \<open>t \<in> \<D> ((\<Squnion>n. \<sigma> n) \<down> n)\<close>
        by (auto simp add: \<open>t = u @ v\<close> D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    qed
  next
    show \<open>(t, X) \<in> \<F> ((\<Squnion>n. \<sigma> n) \<down> n) \<Longrightarrow> t \<notin> \<D> ((\<Squnion>n. \<sigma> n) \<down> n) \<Longrightarrow> (t, X) \<in> \<F> (\<sigma> n \<down> n)\<close> for t X
      by (meson \<open>chain \<sigma>\<close> is_processT8 is_ub_thelub proc_ord2a restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_approx_self)
  next
    fix t X assume \<open>(t, X) \<in> \<F> (\<sigma> n \<down> n)\<close> \<open>t \<notin> \<D> (\<sigma> n \<down> n)\<close>
    hence \<open>length t \<le> n\<close> \<open>(t, X) \<in> \<F> (\<sigma> n)\<close> \<open>t \<notin> \<D> (\<sigma> n)\<close>
      by (auto elim!: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    thus \<open>(t, X) \<in> \<F> ((\<Squnion>i. \<sigma> i) \<down> n)\<close>
      by (simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        (meson \<open>chain \<sigma>\<close> is_ub_thelub le_approx2)
  qed
qed


instance process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :: (type, type) complete_restriction_space
proof (intro_classes, rule restriction_convergentI)
  show \<open>\<sigma> \<midarrow>\<down>\<rightarrow> (\<Squnion>i. \<sigma> i)\<close> if \<open>restriction_chain \<sigma>\<close> for \<sigma> :: \<open>nat \<Rightarrow> ('a, 'b) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  proof (subst restricted_LUB_restriction_chain_is[symmetric])
    from \<open>restriction_chain \<sigma>\<close> show \<open>restriction_chain \<sigma>\<close> .
  next
    from restriction_tendsto_restrictions
    show \<open>(\<lambda>n. (\<Squnion>i. \<sigma> i) \<down> n) \<midarrow>\<down>\<rightarrow> (\<Squnion>i. \<sigma> i)\<close> .
  qed
qed


text \<open>This is a very powerful result. Now we can write fixed-point equations for processes
      like \<^term>\<open>\<upsilon> X. f X\<close>, providing the fact that \<^term>\<open>f\<close> is \<^const>\<open>constructive\<close>.\<close>



setup \<open>Sign.add_const_constraint (\<^const_name>\<open>restriction\<close>, NONE)\<close>
  \<comment> \<open>Back to normal.\<close>

(*<*)
end
  (*>*)
