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
  imports Process_Restriction_Space "HOL-CSPM.CSPM_Laws"
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

  { let ?lhs = \<open>P \<triangle> Q \<down> n\<close>
    fix t u v assume \<open>t = u @ v\<close> \<open>u \<in> \<T> (P' \<triangle> Q')\<close> \<open>length u = n\<close> \<open>tF u\<close> \<open>ftF v\<close>
    from this(2) \<open>tF u\<close> obtain u1 u2
      where \<open>u = u1 @ u2\<close> \<open>u1 \<in> \<T> P'\<close> \<open>tF u1\<close> \<open>u2 \<in> \<T> Q'\<close> \<open>tF u2\<close>
      by (simp add: T_Interrupt)
        (metis append_Nil2 is_processT1_TR tickFree_append_iff)

    from \<open>length u = n\<close> \<open>u = u1 @ u2\<close>
    have \<open>length u1 \<le> n\<close> \<open>length u2 \<le> n\<close> by simp_all
    with \<open>u1 \<in> \<T> P'\<close> \<open>P \<down> n = P' \<down> n\<close> \<open>u2 \<in> \<T> Q'\<close> \<open>Q \<down> n = Q' \<down> n\<close>
    have \<open>u1 \<in> \<T> P\<close> \<open>u2 \<in> \<T> Q\<close>
      by (metis T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI
          length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)+
    with \<open>tF u1\<close> have \<open>u \<in> \<T> (P \<triangle> Q)\<close>
      by (auto simp add: \<open>u = u1 @ u2\<close> T_Interrupt)
    with \<open>length u = n\<close> \<open>tF u\<close> have \<open>u \<in> \<D> ?lhs\<close>
      by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
    hence \<open>t \<in> \<D> ?lhs\<close> by (simp add: \<open>ftF v\<close> \<open>t = u @ v\<close> \<open>tF u\<close> is_processT7)
  } note * = this

  show \<open>P \<triangle> Q \<down> n \<sqsubseteq>\<^sub>F\<^sub>D P' \<triangle> Q' \<down> n\<close> (is \<open>?lhs \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close>)
  proof (unfold refine_defs, safe)
    show div : \<open>t \<in> \<D> ?rhs \<Longrightarrow> t \<in> \<D> ?lhs\<close> for t
    proof (elim D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
      assume \<open>t \<in> \<D> (P' \<triangle> Q')\<close> \<open>length t \<le> n\<close>
      from this(1) consider \<open>t \<in> \<D> P'\<close>
        | (divR) t1 t2 where \<open>t = t1 @ t2\<close> \<open>t1 \<in> \<T> P'\<close> \<open>tF t1\<close> \<open>t2 \<in> \<D> Q'\<close>
        unfolding D_Interrupt by blast
      thus \<open>t \<in> \<D> ?lhs\<close>
      proof cases
        assume \<open>t \<in> \<D> P'\<close>
        hence \<open>ftF t\<close> by (simp add: D_imp_front_tickFree)
        thus \<open>t \<in> \<D> ?lhs\<close>
        proof (elim front_tickFreeE)
          show \<open>t \<in> \<D> ?lhs\<close> if \<open>tF t\<close>
          proof (cases \<open>length t = n\<close>)
            assume \<open>length t = n\<close>
            from \<open>P \<down> n = P' \<down> n\<close> \<open>t \<in> \<D> P'\<close> \<open>length t \<le> n\<close> have \<open>t \<in> \<T> P\<close>
              by (metis D_T T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI
                  length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
            with \<open>tF t\<close> \<open>length t = n\<close> front_tickFree_Nil show \<open>t \<in> \<D> ?lhs\<close>
              by (simp (no_asm) add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k T_Interrupt) blast
          next
            assume \<open>length t \<noteq> n\<close>
            with \<open>length t \<le> n\<close> have \<open>length t < n\<close> by simp
            with \<open>P \<down> n = P' \<down> n\<close> \<open>t \<in> \<D> P'\<close> have \<open>t \<in> \<D> P\<close>
              by (metis D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI
                  length_less_in_D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
            thus \<open>t \<in> \<D> ?lhs\<close> by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI D_Interrupt)
          qed
        next
          fix t' r assume \<open>t = t' @ [\<checkmark>(r)]\<close> \<open>tF t'\<close>
          with \<open>t \<in> \<D> P'\<close> \<open>length t \<le> n\<close>
          have \<open>t' \<in> \<D> P'\<close> \<open>length t' < n\<close> by (auto intro: is_processT9)
          with \<open>P \<down> n = P' \<down> n\<close> have \<open>t' \<in> \<D> P\<close>
            by (metis D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI
                length_less_in_D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
          with \<open>t = t' @ [\<checkmark>(r)]\<close> \<open>tF t'\<close> have \<open>t \<in> \<D> P\<close> by (simp add: is_processT7)
          thus \<open>t \<in> \<D> ?lhs\<close> by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI D_Interrupt)
        qed
      next
        fix u v assume \<open>t = u @ v\<close> \<open>u \<in> \<T> P'\<close> \<open>tF u\<close> \<open>v \<in> \<D> Q'\<close>
        from \<open>t = u @ v\<close> \<open>length t \<le> n\<close> have \<open>length u \<le> n\<close> by simp
        with \<open>P \<down> n = P' \<down> n\<close> \<open>u \<in> \<T> P'\<close> have \<open>u \<in> \<T> P\<close>
          by (metis T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        show \<open>t \<in> \<D> ?lhs\<close>
        proof (cases \<open>length v = n\<close>)
          assume \<open>length v = n\<close>
          with \<open>t = u @ v\<close> \<open>length t \<le> n\<close> have \<open>u = []\<close> by simp
          from D_imp_front_tickFree \<open>v \<in> \<D> Q'\<close> have \<open>ftF v\<close> by blast
          thus \<open>t \<in> \<D> ?lhs\<close>
          proof (elim front_tickFreeE)
            assume \<open>tF v\<close>
            from \<open>length v = n\<close> \<open>Q \<down> n = Q' \<down> n\<close> \<open>v \<in> \<D> Q'\<close> have \<open>v \<in> \<T> Q\<close>
              by (metis D_T D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI dual_order.refl
                  length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
            with \<open>tF u\<close> \<open>u \<in> \<T> P\<close> have \<open>t \<in> \<T> (P \<triangle> Q)\<close>
              by (auto simp add: \<open>t = u @ v\<close> T_Interrupt)
            with \<open>length v = n\<close> \<open>t = u @ v\<close> \<open>tF v\<close> \<open>u = []\<close> show \<open>t \<in> \<D> ?lhs\<close>
              by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
          next
            fix v' r assume \<open>v = v' @ [\<checkmark>(r)]\<close> \<open>tF v'\<close>
            with \<open>v \<in> \<D> Q'\<close> \<open>length t \<le> n\<close> \<open>t = u @ v\<close>
            have \<open>v' \<in> \<D> Q'\<close> \<open>length v' < n\<close> by (auto intro: is_processT9)
            with \<open>Q \<down> n = Q' \<down> n\<close> have \<open>v' \<in> \<D> Q\<close>
              by (metis D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI
                  length_less_in_D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
            with \<open>v = v' @ [\<checkmark>(r)]\<close> \<open>tF v'\<close> have \<open>v \<in> \<D> Q\<close> by (simp add: is_processT7)
            with \<open>tF u\<close> \<open>u \<in> \<T> P\<close> have \<open>t \<in> \<D> (P \<triangle> Q)\<close>
              by (auto simp add: \<open>t = u @ v\<close> D_Interrupt)
            thus \<open>t \<in> \<D> ?lhs\<close> by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
          qed
        next
          assume \<open>length v \<noteq> n\<close>
          with \<open>length t \<le> n\<close> \<open>t = u @ v\<close> have \<open>length v < n\<close> by simp
          with \<open>Q \<down> n = Q' \<down> n\<close> \<open>v \<in> \<D> Q'\<close> have \<open>v \<in> \<D> Q\<close>
            by (metis D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI
                length_less_in_D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
          with \<open>t = u @ v\<close> \<open>tF u\<close> \<open>u \<in> \<T> P\<close> have \<open>t \<in> \<D> (P \<triangle> Q)\<close>
            by (auto simp add: D_Interrupt)
          thus \<open>t \<in> \<D> ?lhs\<close> by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
        qed
      qed
    next
      show \<open>t = u @ v \<Longrightarrow> u \<in> \<T> (P' \<triangle> Q') \<Longrightarrow> length u = n \<Longrightarrow>
            tF u \<Longrightarrow> ftF v \<Longrightarrow> t \<in> \<D> ?lhs\<close> for u v by (fact "*")
    qed

    show \<open>(t, X) \<in> \<F> ?rhs \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for t X
    proof (elim F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
      assume \<open>(t, X) \<in> \<F> (P' \<triangle> Q')\<close> \<open>length t \<le> n\<close>
      from this(1) consider \<open>t \<in> \<D> (P' \<triangle> Q')\<close>
        | u r where \<open>t = u @ [\<checkmark>(r)]\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> P'\<close>
        | r where \<open>\<checkmark>(r) \<notin> X\<close> \<open>t @ [\<checkmark>(r)] \<in> \<T> P'\<close>
        | \<open>(t, X) \<in> \<F> P'\<close> \<open>tF t\<close> \<open>([], X) \<in> \<F> Q'\<close>
        | u v where \<open>t = u @ v\<close> \<open>u \<in> \<T> P'\<close> \<open>tF u\<close> \<open>(v, X) \<in> \<F> Q'\<close> \<open>v \<noteq> []\<close>
        | r where \<open>\<checkmark>(r) \<notin> X\<close> \<open>t \<in> \<T> P'\<close> \<open>tF t\<close> \<open>[\<checkmark>(r)] \<in> \<T> Q'\<close>
        unfolding Interrupt_projs by blast
      thus \<open>(t, X) \<in> \<F> ?lhs\<close>
      proof cases
        assume \<open>t \<in> \<D> (P' \<triangle> Q')\<close>
        hence \<open>t \<in> \<D> ?rhs\<close> by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
        with div D_F show \<open>t \<in> \<D> (P' \<triangle> Q') \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> by blast
      next
        fix u r assume \<open>t = u @ [\<checkmark>(r)]\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> P'\<close>
        with \<open>P \<down> n = P' \<down> n\<close> \<open>length t \<le> n\<close> have \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close>
          by (metis T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        hence \<open>(t, X) \<in> \<F> (P \<triangle> Q)\<close> by (auto simp add: \<open>t = u @ [\<checkmark>(r)]\<close> F_Interrupt)
        thus \<open>(t, X) \<in> \<F> ?lhs\<close> by (simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
      next
        fix r assume \<open>\<checkmark>(r) \<notin> X\<close> \<open>t @ [\<checkmark>(r)] \<in> \<T> P'\<close>
        show \<open>(t, X) \<in> \<F> ?lhs\<close>
        proof (cases \<open>length t = n\<close>)
          assume \<open>length t = n\<close>
          with \<open>P \<down> n = P' \<down> n\<close> \<open>length t \<le> n\<close> \<open>t @ [\<checkmark>(r)] \<in> \<T> P'\<close> have \<open>t \<in> \<T> P\<close>
            by (metis T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI is_processT3_TR_append
                length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
          moreover from \<open>t @ [\<checkmark>(r)] \<in> \<T> P'\<close> append_T_imp_tickFree have \<open>tF t\<close> by blast
          ultimately have \<open>t \<in> \<T> (P \<triangle> Q)\<close> by (simp add: T_Interrupt)
          with \<open>length t = n\<close> \<open>tF t\<close> show \<open>(t, X) \<in> \<F> ?lhs\<close>
            by (simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
        next
          assume \<open>length t \<noteq> n\<close>
          with \<open>length t \<le> n\<close> have \<open>length (t @ [\<checkmark>(r)]) \<le> n\<close> by simp
          with \<open>P \<down> n = P' \<down> n\<close> \<open>t @ [\<checkmark>(r)] \<in> \<T> P'\<close> have \<open>t @ [\<checkmark>(r)] \<in> \<T> P\<close>
            by (metis T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
          with \<open>\<checkmark>(r) \<notin> X\<close> have \<open>(t, X) \<in> \<F> (P \<triangle> Q)\<close>
            by (simp add: F_Interrupt) (metis Diff_insert_absorb)
          thus \<open>(t, X) \<in> \<F> ?lhs\<close> by (simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
        qed
      next
        assume \<open>(t, X) \<in> \<F> P'\<close> \<open>tF t\<close> \<open>([], X) \<in> \<F> Q'\<close>
        show \<open>(t, X) \<in> \<F> ?lhs\<close>
        proof (cases \<open>length t = n\<close>)
          assume \<open>length t = n\<close>
          from \<open>(t, X) \<in> \<F> P'\<close> \<open>P \<down> n = P' \<down> n\<close> \<open>length t \<le> n\<close> have \<open>t \<in> \<T> P\<close>
            by (simp add: F_T T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
                length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
          hence \<open>t \<in> \<T> (P \<triangle> Q)\<close> by (simp add: T_Interrupt)
          with \<open>length t = n\<close> \<open>tF t\<close> show \<open>(t, X) \<in> \<F> ?lhs\<close>
            by (simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
        next
          assume \<open>length t \<noteq> n\<close>
          with \<open>length t \<le> n\<close> have \<open>length t < n\<close> by simp
          with \<open>(t, X) \<in> \<F> P'\<close> \<open>P \<down> n = P' \<down> n\<close> \<open>length t \<noteq> n\<close> have \<open>(t, X) \<in> \<F> P\<close>
            by (metis F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI length_less_in_F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
          moreover from \<open>([], X) \<in> \<F> Q'\<close> have \<open>([], X) \<in> \<F> Q\<close>
            by (metis F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI \<open>0 < n\<close> \<open>Q \<down> n = Q' \<down> n\<close>
                length_less_in_F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k list.size(3))
          ultimately have \<open>(t, X) \<in> \<F> (P \<triangle> Q)\<close>
            using \<open>tF t\<close> by (simp add: F_Interrupt)
          thus \<open>(t, X) \<in> \<F> ?lhs\<close> by (simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
        qed
      next
        fix u v assume \<open>t = u @ v\<close> \<open>u \<in> \<T> P'\<close> \<open>tF u\<close> \<open>(v, X) \<in> \<F> Q'\<close> \<open>v \<noteq> []\<close>
        from \<open>t = u @ v\<close> \<open>length t \<le> n\<close> have \<open>length u \<le> n\<close> by simp
        with \<open>P \<down> n = P' \<down> n\<close> \<open>u \<in> \<T> P'\<close> have \<open>u \<in> \<T> P\<close> 
          by (simp add: T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        show \<open>(t, X) \<in> \<F> ?lhs\<close>
        proof (cases \<open>length v = n\<close>)
          assume \<open>length v = n\<close>
          with \<open>t = u @ v\<close> \<open>length t \<le> n\<close> have \<open>u = []\<close> by simp
          from F_imp_front_tickFree \<open>(v, X) \<in> \<F> Q'\<close> have \<open>ftF v\<close> by blast
          thus \<open>(t, X) \<in> \<F> ?lhs\<close>
          proof (elim front_tickFreeE)
            assume \<open>tF v\<close>
            from \<open>length v = n\<close> \<open>Q \<down> n = Q' \<down> n\<close> \<open>(v, X) \<in> \<F> Q'\<close> have \<open>v \<in> \<T> Q\<close>
              by (metis F_T F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI dual_order.refl
                  length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
            with \<open>tF u\<close> \<open>u \<in> \<T> P\<close> have \<open>t \<in> \<T> (P \<triangle> Q)\<close>
              by (auto simp add: \<open>t = u @ v\<close> T_Interrupt)
            with \<open>length v = n\<close> \<open>t = u @ v\<close> \<open>tF v\<close> \<open>u = []\<close> show \<open>(t, X) \<in> \<F> ?lhs\<close>
              by (simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
          next
            fix v' r assume \<open>v = v' @ [\<checkmark>(r)]\<close> \<open>tF v'\<close>
            with \<open>(v, X) \<in> \<F> Q'\<close> \<open>length t \<le> n\<close> \<open>t = u @ v\<close>
              \<open>Q \<down> n = Q' \<down> n\<close> \<open>u = []\<close> have \<open>v' @ [\<checkmark>(r)] \<in> \<T> Q\<close>
              by (metis F_T T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI append_self_conv2
                  length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
            with \<open>t = u @ v\<close> \<open>tF u\<close> \<open>u \<in> \<T> P\<close> \<open>v = v' @ [\<checkmark>(r)]\<close> have \<open>t \<in> \<T> (P \<triangle> Q)\<close>
              by (auto simp add: T_Interrupt)
            thus \<open>(t, X) \<in> \<F> ?lhs\<close>
              by (simp add: \<open>t = u @ v\<close> \<open>u = []\<close> \<open>v = v' @ [\<checkmark>(r)]\<close>
                  restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs(3) tick_T_F)
          qed
        next
          assume \<open>length v \<noteq> n\<close>
          with \<open>length t \<le> n\<close> \<open>t = u @ v\<close> have \<open>length v < n\<close> by simp
          with \<open>Q \<down> n = Q' \<down> n\<close> \<open>(v, X) \<in> \<F> Q'\<close> have \<open>(v, X) \<in> \<F> Q\<close>
            by (metis F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI
                length_less_in_F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
          with \<open>t = u @ v\<close> \<open>tF u\<close> \<open>u \<in> \<T> P\<close> \<open>v \<noteq> []\<close> have \<open>(t, X) \<in> \<F> (P \<triangle> Q)\<close>
            by (simp add: F_Interrupt) blast
          thus \<open>(t, X) \<in> \<F> ?lhs\<close> by (simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
        qed
      next
        fix r assume \<open>\<checkmark>(r) \<notin> X\<close> \<open>t \<in> \<T> P'\<close> \<open>tF t\<close> \<open>[\<checkmark>(r)] \<in> \<T> Q'\<close>
        have \<open>t \<in> \<T> P\<close>
          by (metis T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI \<open>P \<down> n = P' \<down> n\<close> \<open>length t \<le> n\<close>
              \<open>t \<in> \<T> P'\<close> length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        moreover have \<open>[\<checkmark>(r)] \<in> \<T> Q\<close>
          by (metis (no_types, lifting) Suc_leI T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
              Un_iff \<open>0 < n\<close> \<open>Q \<down> n = Q' \<down> n\<close> \<open>[\<checkmark>(r)] \<in> \<T> Q'\<close> length_Cons
              length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k list.size(3))
        ultimately have \<open>(t, X) \<in> \<F> (P \<triangle> Q)\<close>
          using \<open>\<checkmark>(r) \<notin> X\<close> \<open>tF t\<close> by (simp add: F_Interrupt) blast
        thus \<open>(t, X) \<in> \<F> ?lhs\<close> by (simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
      qed
    next
      show \<open>t = u @ v \<Longrightarrow> u \<in> \<T> (P' \<triangle> Q') \<Longrightarrow> length u = n \<Longrightarrow>
            tF u \<Longrightarrow> ftF v \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for u v
        by (simp add: "*" is_processT8)
    qed
  qed
qed


(*<*)
end
  (*>*)