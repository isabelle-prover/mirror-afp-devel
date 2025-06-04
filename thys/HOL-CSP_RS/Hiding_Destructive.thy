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


section \<open>Destructiveness of Hiding\<close>

(*>*)
theory Hiding_Destructive
  imports "HOL-CSPM.CSPM_Laws" Prefixes_Constructive
begin
  (*>*)


subsection \<open>Refinement\<close>

lemma Hiding_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD : \<open>(P \<down> n) \ S \<sqsubseteq>\<^sub>F\<^sub>D P \ S \<down> n\<close>
proof (unfold refine_defs, safe)
  show * : \<open>t \<in> \<D> (P \ S \<down> n) \<Longrightarrow> t \<in> \<D> ((P \<down> n) \ S)\<close> for t
  proof (elim D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
    show \<open>t \<in> \<D> (P \ S) \<Longrightarrow> t \<in> \<D> ((P \<down> n) \ S)\<close>
      by (simp add: D_Hiding restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs) blast
  next
    fix u v
    assume \<open>t = u @ v\<close> \<open>u \<in> \<T> (P \ S)\<close> \<open>length u = n\<close> \<open>tF u\<close> \<open>ftF v\<close>
    from \<open>u \<in> \<T> (P \ S)\<close>[simplified T_Hiding, simplified]
    consider \<open>u \<in> \<D> (P \ S)\<close> | u' where \<open>u = trace_hide u' (ev ` S)\<close> \<open>(u', ev ` S) \<in> \<F> P\<close>
      by (simp add: F_Hiding D_Hiding) blast
    thus \<open>t \<in> \<D> ((P \<down> n) \ S)\<close>
    proof cases
      assume \<open>u \<in> \<D> (P \ S)\<close>
      hence \<open>t \<in> \<D> (P \ S)\<close> by (simp add: \<open>ftF v\<close> \<open>t = u @ v\<close> \<open>tF u\<close> is_processT7)
      with restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_approx_self le_approx1 mono_Hiding
      show \<open>t \<in> \<D> ((P \<down> n) \ S)\<close> by blast
    next
      fix u' assume \<open>u = trace_hide u' (ev ` S)\<close> \<open>(u', ev ` S) \<in> \<F> P\<close>
      with \<open>length u = n\<close> \<open>tF u\<close> Hiding_tickFree length_filter_le F_T
      have \<open>n \<le> length u'\<close> \<open>tickFree u'\<close> \<open>u' \<in> \<T> P\<close> by blast+
      with \<open>u = trace_hide u' (ev ` S)\<close>
      have \<open>u' = (take n u') @ (drop n u') \<and> take n u' \<in> \<T> P \<and>
            length (take n u') = n \<and> tF (take n u') \<and> ftF (drop n u')\<close>
        by (simp add: min_def) (metis append_take_drop_id is_processT3_TR_append
            tickFree_append_iff tickFree_imp_front_tickFree)
      with D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k have \<open>u' \<in> \<D> (P \<down> n)\<close> by blast
      with Hiding_tickFree \<open>ftF v\<close> \<open>t = u @ v\<close> \<open>u = trace_hide u' (ev ` S)\<close> \<open>tF u\<close>
      show \<open>t \<in> \<D> ((P \<down> n) \ S)\<close> by (simp add: D_Hiding) blast
    qed
  qed

  fix s X
  assume \<open>(s, X) \<in> \<F> ((P \ S) \<down> n)\<close>
  then consider \<open>s \<in> \<D> ((P \ S) \<down> n)\<close> | \<open>(s, X) \<in> \<F> (P \ S)\<close>
    unfolding restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
  thus \<open>(s, X) \<in> \<F> ((P \<down> n) \ S)\<close>
  proof cases
    from "*" D_F show \<open>s \<in> \<D> ((P \ S) \<down> n) \<Longrightarrow> (s, X) \<in> \<F> ((P \<down> n) \ S)\<close> by blast
  next
    show \<open>(s, X) \<in> \<F> (P \ S) \<Longrightarrow> (s, X) \<in> \<F> ((P \<down> n) \ S)\<close>
      using restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_approx_self D_F mono_Hiding proc_ord2a by blast
  qed
qed


subsection \<open>Destructiveness\<close>

lemma Hiding_destructive :
  \<open>\<exists>P Q :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k. P \<down> n = Q \<down> n \<and> (P \ S) \<down> Suc 0 \<noteq> (Q \ S) \<down> Suc 0\<close> if \<open>S \<noteq> {}\<close>
proof -
  from \<open>S \<noteq> {}\<close> obtain e where \<open>e \<in> S\<close> by blast
  define P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> where \<open>P \<equiv> iterate (Suc n)\<cdot>(\<Lambda> X. write0 e X)\<cdot>(SKIP undefined)\<close>
  define Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> where \<open>Q \<equiv> iterate (Suc n)\<cdot>(\<Lambda> X. write0 e X)\<cdot>STOP\<close>
  have \<open>P \<down> n = Q \<down> n\<close>
    unfolding P_def Q_def by (induct n) (simp_all add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_write0) 
  have \<open>P \ S = SKIP undefined\<close>
    unfolding P_def by (induct n) (simp_all add: Hiding_write0_non_disjoint \<open>e \<in> S\<close>)
  hence \<open>(P \ S) \<down> Suc 0 = SKIP undefined\<close> by simp
  have \<open>Q \ S = STOP\<close>
    unfolding Q_def by (induct n) (simp_all add: Hiding_write0_non_disjoint \<open>e \<in> S\<close>)
  hence \<open>(Q \ S) \<down> Suc 0 = STOP\<close> by simp

  have \<open>P \<down> n = Q \<down> n \<and> (P \ S) \<down> Suc 0 \<noteq> (Q \ S) \<down> Suc 0\<close>
    by (simp add: \<open>P \<down> n = Q \<down> n\<close> \<open>(P \ S) \<down> Suc 0 = SKIP undefined\<close>
        \<open>(Q \ S) \<down> Suc 0 = STOP\<close> SKIP_Neq_STOP)
  thus ?thesis by blast
qed



(*<*)
end
  (*>*)