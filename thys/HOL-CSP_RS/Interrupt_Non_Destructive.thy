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


section \<open>Non Destructiveness of Interrupt\<close>

(*<*)
theory Interrupt_Non_Destructive
  imports Process_Restriction_Space "HOL-CSPM"
begin
  (*>*)

subsection \<open>Refinement\<close>

lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Interrupt_FD :
  \<open>P \<triangle> Q \<down> n \<sqsubseteq>\<^sub>F\<^sub>D (P \<down> n) \<triangle> (Q \<down> n)\<close> (is \<open>?lhs \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close>)
proof (unfold refine_defs, safe)  
  show * : \<open>t \<in> \<D> ?lhs\<close> if \<open>t \<in> \<D> ?rhs\<close> for t
  proof -
    from \<open>t \<in> \<D> ?rhs\<close> consider \<open>t \<in> \<D> (P \<down> n)\<close>
      | u v where \<open>t = u @ v\<close> \<open>u \<in> \<T> (P \<down> n)\<close> \<open>tF u\<close> \<open>v \<in> \<D> (Q \<down> n)\<close>
      by (simp add: D_Interrupt) blast
    thus \<open>t \<in> \<D> ?lhs\<close>
    proof cases
      show \<open>t \<in> \<D> (P \<down> n) \<Longrightarrow> t \<in> \<D> ?lhs\<close>
        by (elim D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE) (auto simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Interrupt_projs)
    next
      fix u v assume \<open>t = u @ v\<close> \<open>u \<in> \<T> (P \<down> n)\<close> \<open>tF u\<close> \<open>v \<in> \<D> (Q \<down> n)\<close>
      from \<open>v \<in> \<D> (Q \<down> n)\<close> show \<open>t \<in> \<D> ?lhs\<close>
      proof (elim D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
        from \<open>t = u @ v\<close> \<open>u \<in> \<T> (P \<down> n)\<close> \<open>tF u\<close> show \<open>v \<in> \<D> Q \<Longrightarrow> t \<in> \<D> ?lhs\<close>
          by (auto simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs Interrupt_projs
              D_imp_front_tickFree front_tickFree_append)
      next
        fix w x assume \<open>v = w @ x\<close> \<open>w \<in> \<T> Q\<close> \<open>length w = n\<close> \<open>tF w\<close> \<open>ftF x\<close>
        from \<open>u \<in> \<T> (P \<down> n)\<close> consider \<open>u \<in> \<D> (P \<down> n)\<close> | \<open>u \<in> \<T> P\<close> \<open>length u \<le> n\<close>
          by (elim T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE) (auto simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        thus \<open>t \<in> \<D> ?lhs\<close>
        proof cases
          assume \<open>u \<in> \<D> (P \<down> n)\<close>
          with D_imp_front_tickFree \<open>t = u @ v\<close> \<open>tF u\<close> \<open>v \<in> \<D> (Q \<down> n)\<close> is_processT7
          have \<open>t \<in> \<D> (P \<down> n)\<close> by blast
          thus \<open>t \<in> \<D> ?lhs\<close> by (elim D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
              (auto simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Interrupt_projs)
        next
          assume \<open>u \<in> \<T> P\<close> \<open>length u \<le> n\<close>
          hence \<open>t = take n (u @ w) @ drop (n - length u) w @ x \<and>
                 take n (u @ w) \<in> \<T> (P \<triangle> Q) \<and> length (take n (u @ w)) = n \<and>
                 tF (take n (u @ w)) \<and> ftF (drop (n - length u) w @ x)\<close>
            by (simp add: \<open>t = u @ v\<close> \<open>v = w @ x\<close> \<open>length w = n\<close> \<open>tF u\<close> T_Interrupt)
              (metis \<open>ftF x\<close> \<open>tF u\<close> \<open>tF w\<close> \<open>w \<in> \<T> Q\<close> append_take_drop_id
                front_tickFree_append is_processT3_TR_append tickFree_append_iff)
          with D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k show \<open>t \<in> \<D> ?lhs\<close> by blast
        qed
      qed
    qed
  qed

  show \<open>(t, X) \<in> \<F> ?rhs \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for t X
    by (meson "*" is_processT8 mono_Interrupt proc_ord2a restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_approx_self)
qed



subsection \<open>Non Destructiveness\<close>

lemma Interrupt_non_destructive :
  \<open>non_destructive (\<lambda>(P :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, Q). P \<triangle> Q)\<close>
proof (rule order_non_destructiveI, clarify)
  fix P P' Q Q' :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and n
  assume \<open>(P, Q) \<down> n = (P', Q') \<down> n\<close> \<open>0 < n\<close>
  hence \<open>P \<down> n = P' \<down> n\<close> \<open>Q \<down> n = Q' \<down> n\<close>
    by (simp_all add: restriction_prod_def)
  show \<open>P \<triangle> Q \<down> n \<sqsubseteq>\<^sub>F\<^sub>D P' \<triangle> Q' \<down> n\<close>
  proof (rule leFD_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
    show \<open>t \<in> \<D> (P' \<triangle> Q') \<Longrightarrow> t \<in> \<D> (P \<triangle> Q \<down> n)\<close> for t
      by (metis (mono_tags, opaque_lifting) \<open>P \<down> n = P' \<down> n\<close> \<open>Q \<down> n = Q' \<down> n\<close>
                in_mono le_ref1 mono_Interrupt_FD restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD_self
                restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Interrupt_FD)
  next
    show \<open>(s, X) \<in> \<F> (P' \<triangle> Q') \<Longrightarrow> (s, X) \<in> \<F> (P \<triangle> Q \<down> n)\<close> for s X
      by (metis (mono_tags, opaque_lifting) \<open>P \<down> n = P' \<down> n\<close> \<open>Q \<down> n = Q' \<down> n\<close>
                failure_refine_def leFD_imp_leF mono_Interrupt_FD
                restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD_self
                restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Interrupt_FD subset_iff)
  qed
qed



(*<*)
end
  (*>*)
