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


section \<open>Non Destructiveness of Throw\<close>


(*<*)
theory Throw_Non_Destructive
  imports Process_Restriction_Space "HOL-CSP_OpSem.Initials"
begin
  (*>*)


subsection \<open>Equality\<close>

lemma Depth_Throw_1_is_constant: \<open>P \<Theta> a \<in> A. Q1 a \<down> 1 = P \<Theta> a \<in> A. Q2 a \<down> 1\<close>
proof (rule FD_antisym)
  show \<open>P \<Theta> a \<in> A. Q2 a \<down> 1 \<sqsubseteq>\<^sub>F\<^sub>D P \<Theta> a \<in> A. Q1 a \<down> 1\<close> for Q1 Q2
  proof (unfold refine_defs, safe)
    show div :  \<open>t \<in> \<D> (Throw P A Q1 \<down> 1) \<Longrightarrow> t \<in> \<D> (Throw P A Q2 \<down> 1)\<close> for t
    proof (elim D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE) 
      assume \<open>t \<in> \<D> (P \<Theta> a \<in> A. Q1 a)\<close> and \<open>length t \<le> 1\<close>
      from \<open>length t \<le> 1\<close> consider \<open>t = []\<close> | e where \<open>t = [e]\<close> by (cases t) simp_all
      thus \<open>t \<in> \<D> (P \<Theta> a \<in> A. Q2 a \<down> 1)\<close>
      proof cases
        from \<open>t \<in> \<D> (P \<Theta> a \<in> A. Q1 a)\<close> show \<open>t = [] \<Longrightarrow> t \<in> \<D> (P \<Theta> a \<in> A. Q2 a \<down> 1)\<close>
          by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k D_Throw)
      next
        fix e assume \<open>t = [e]\<close>
        with \<open>t \<in> \<D> (P \<Theta> a \<in> A. Q1 a)\<close>
        consider \<open>[] \<in> \<D> P\<close> | a where \<open>t = [ev a]\<close> \<open>[ev a] \<in> \<D> P\<close> \<open>a \<notin> A\<close>
          | a where \<open>t = [ev a]\<close> \<open>[ev a] \<in> \<T> P\<close> \<open>a \<in> A\<close>
          by (auto simp add: D_Throw disjoint_iff image_iff)
            (metis D_T append_Nil event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust process_charn,
              metis append_Nil empty_iff empty_set hd_append2 hd_in_set in_set_conv_decomp set_ConsD)
        thus \<open>t \<in> \<D> (P \<Theta> a \<in> A. Q2 a \<down> 1)\<close>
        proof cases
          show \<open>t = [ev a] \<Longrightarrow> [ev a] \<in> \<T> P \<Longrightarrow> a \<in> A \<Longrightarrow> t \<in> \<D> (P \<Theta> a \<in> A. Q2 a \<down> 1)\<close> for a
            by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k T_Throw)
              (metis append_Nil append_self_conv front_tickFree_charn inf_bot_left
                is_ev_def is_processT1_TR length_0_conv length_Cons list.set(1)
                tickFree_Cons_iff tickFree_Nil)
        next
          show \<open>[] \<in> \<D> P \<Longrightarrow> t \<in> \<D> (P \<Theta> a \<in> A. Q2 a \<down> 1)\<close>
            by (simp flip: BOT_iff_Nil_D add: D_BOT)
              (use \<open>t = [e]\<close> front_tickFree_single in blast)
        next
          show \<open>t = [ev a] \<Longrightarrow> [ev a] \<in> \<D> P \<Longrightarrow> a \<notin> A \<Longrightarrow> t \<in> \<D> (P \<Theta> a \<in> A. Q2 a \<down> 1)\<close> for a  
            by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k D_Throw disjoint_iff image_iff)
              (metis append.right_neutral empty_set event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1)
                front_tickFree_Nil list.simps(15) singletonD tickFree_Cons_iff tickFree_Nil)
        qed
      qed
    next
      fix u v assume * : \<open>t = u @ v\<close> \<open>u \<in> \<T> (Throw P A Q1)\<close> \<open>length u = 1\<close> \<open>tF u\<close> \<open>ftF v\<close>
      from \<open>length u = 1\<close> \<open>tF u\<close> obtain a where \<open>u = [ev a]\<close>
        by (cases u) (auto simp add: is_ev_def)
      with "*"(2) show \<open>t \<in> \<D> (Throw P A Q2 \<down> 1)\<close>
        by (simp add: \<open>t = u @ v\<close> D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Throw_projs Cons_eq_append_conv)
          (metis (no_types) "*"(3-5) One_nat_def append_Nil empty_set inf_bot_left
            insert_disjoint(2) is_processT1_TR list.simps(15))
    qed

    show \<open>(t, X) \<in> \<F> (Throw P A Q1 \<down> 1) \<Longrightarrow> (t, X) \<in> \<F> (Throw P A Q2 \<down> 1)\<close> for t X
    proof (elim F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
      assume \<open>(t, X) \<in> \<F> (P \<Theta> a \<in> A. Q1 a)\<close> \<open>length t \<le> 1\<close>
      then consider \<open>t \<in> \<D> (P \<Theta> a \<in> A. Q1 a)\<close> | \<open>(t, X) \<in> \<F> P\<close> \<open>set t \<inter> ev ` A = {}\<close>
        | a where \<open>t = [ev a]\<close> \<open>[ev a] \<in> \<T> P\<close> \<open>a \<in> A\<close>
        by (auto simp add: F_Throw D_Throw)
      thus \<open>(t, X) \<in> \<F> (P \<Theta> a \<in> A. Q2 a \<down> 1)\<close>
      proof cases
        from D_F div \<open>length t \<le> 1\<close>
        show \<open>t \<in> \<D> (P \<Theta> a \<in> A. Q1 a) \<Longrightarrow> (t, X) \<in> \<F> (P \<Theta> a \<in> A. Q2 a \<down> 1)\<close>
          using D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI by blast
      next
        show \<open>(t, X) \<in> \<F> P \<Longrightarrow> set t \<inter> ev ` A = {} \<Longrightarrow> (t, X) \<in> \<F> (Throw P A Q2 \<down> 1)\<close>
          by (simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k F_Throw)
      next
        show \<open>\<lbrakk>t = [ev a]; [ev a] \<in> \<T> P; a \<in> A\<rbrakk> \<Longrightarrow> (t, X) \<in> \<F> (Throw P A Q2 \<down> 1)\<close> for a
          by (simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k T_Throw)
            (metis append.right_neutral append_Nil empty_set event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1)
              front_tickFree_Nil inf_bot_left is_processT1_TR length_Cons
              list.size(3) tickFree_Cons_iff tickFree_Nil)
      qed
    next
      fix u v assume * : \<open>t = u @ v\<close> \<open>u \<in> \<T> (Throw P A Q1)\<close> \<open>length u = 1\<close> \<open>tF u\<close> \<open>ftF v\<close>
      from \<open>length u = 1\<close> \<open>tF u\<close> obtain a where \<open>u = [ev a]\<close>
        by (cases u) (auto simp add: is_ev_def)
      with "*"(2) show \<open>(t, X) \<in> \<F> (Throw P A Q2 \<down> 1)\<close>
        by (simp add: \<open>t = u @ v\<close> F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Throw_projs Cons_eq_append_conv)
          (metis (no_types) "*"(3-5) One_nat_def append_Nil empty_set inf_bot_left
            insert_disjoint(2) is_processT1_TR list.simps(15))
    qed
  qed

  thus \<open>P \<Theta> a \<in> A. Q2 a \<down> 1 \<sqsubseteq>\<^sub>F\<^sub>D P \<Theta> a \<in> A. Q1 a \<down> 1\<close> by simp
qed



subsection \<open>Refinement\<close>

lemma restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Throw_FD :
  \<open>(P \<Theta> a \<in> A. Q a) \<down> n \<sqsubseteq>\<^sub>F\<^sub>D (P \<down> n) \<Theta> a \<in> A. (Q a \<down> n)\<close> (is \<open>?lhs \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close>)
proof (unfold refine_defs, safe)
  show \<open>t \<in> \<D> ?lhs\<close> if \<open>t \<in> \<D> ?rhs\<close> for t
  proof -
    from \<open>t \<in> \<D> ?rhs\<close>
    consider t1 t2 where \<open>t = t1 @ t2\<close> \<open>t1 \<in> \<D> (P \<down> n)\<close> \<open>tF t1\<close> \<open>set t1 \<inter> ev ` A = {}\<close> \<open>ftF t2\<close>
      | t1 a t2 where \<open>t = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> (P \<down> n)\<close>
        \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>t2 \<in> \<D> (Q a \<down> n)\<close>
      unfolding D_Throw by blast
    thus \<open>t \<in> \<D> ?lhs\<close>
    proof cases
      show \<open>\<lbrakk>t = t1 @ t2; t1 \<in> \<D> (P \<down> n); tF t1; set t1 \<inter> ev ` A = {}; ftF t2\<rbrakk> \<Longrightarrow> t \<in> \<D> ?lhs\<close> for t1 t2
        by (elim D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE, simp_all add: Throw_projs D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
          (blast, metis (no_types, lifting) front_tickFree_append inf_sup_aci(8) inf_sup_distrib2 sup_bot_right)
    next
      fix t1 a t2
      assume \<open>t = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> (P \<down> n)\<close>
        \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>t2 \<in> \<D> (Q a \<down> n)\<close>
      from \<open>t2 \<in> \<D> (Q a \<down> n)\<close> show \<open>t \<in> \<D> ?lhs\<close>
      proof (elim D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
        from \<open>t1 @ [ev a] \<in> \<T> (P \<down> n)\<close> show \<open>t2 \<in> \<D> (Q a) \<Longrightarrow> length t2 \<le> n \<Longrightarrow> t \<in> \<D> ?lhs\<close>
        proof (elim T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
          from \<open>a \<in> A\<close> \<open>set t1 \<inter> ev ` A = {}\<close> \<open>t = t1 @ ev a # t2\<close>
          show \<open>t2 \<in> \<D> (Q a) \<Longrightarrow> t1 @ [ev a] \<in> \<T> P \<Longrightarrow> t \<in> \<D> ?lhs\<close>
            by (auto simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k D_Throw)
        next
          fix u v assume \<open>t2 \<in> \<D> (Q a)\<close> \<open>length t2 \<le> n\<close> \<open>t1 @ [ev a] = u @ v\<close>
            \<open>u \<in> \<T> P\<close> \<open>length u = n\<close> \<open>tF u\<close> \<open>ftF v\<close>
          from \<open>t1 @ [ev a] = u @ v\<close> \<open>ftF v\<close> consider \<open>t1 @ [ev a] = u\<close>
            | v' where \<open>t1 = u @ v'\<close> \<open>v = v' @ [ev a]\<close> \<open>ftF v'\<close>
            by (cases v rule: rev_cases) (simp_all add: front_tickFree_append_iff)
          thus \<open>t \<in> \<D> ?lhs\<close>
          proof cases
            from \<open>a \<in> A\<close> \<open>length u = n\<close> \<open>set t1 \<inter> ev ` A = {}\<close> \<open>t2 \<in> \<D> (Q a)\<close> \<open>tF u\<close> \<open>u \<in> \<T> P\<close>
            show \<open>t1 @ [ev a] = u \<Longrightarrow> t \<in> \<D> ?lhs\<close>
              by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k T_Throw \<open>t = t1 @ ev a # t2\<close>)
                (metis Cons_eq_appendI D_imp_front_tickFree append_Nil append_assoc is_processT1_TR)
          next
            from \<open>ftF v\<close> \<open>length u = n\<close> \<open>set t1 \<inter> ev ` A = {}\<close> \<open>t = t1 @ ev a # t2\<close> \<open>u \<in> \<T> P\<close>
            show \<open>t1 = u @ v' \<Longrightarrow> v = v' @ [ev a] \<Longrightarrow> ftF v' \<Longrightarrow> t \<in> \<D> ?lhs\<close> for v'
              by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k T_Throw)
                (metis D_imp_front_tickFree Int_assoc Un_Int_eq(3) append_assoc
                  front_tickFree_append front_tickFree_nonempty_append_imp
                  inf_bot_right list.distinct(1) same_append_eq set_append \<open>t \<in> \<D> ?rhs\<close>)
          qed
        qed
      next
        from \<open>t1 @ [ev a] \<in> \<T> (P \<down> n)\<close>
        show \<open>\<lbrakk>t2 = u @ v; u \<in> \<T> (Q a); length u = n; tF u; ftF v\<rbrakk> \<Longrightarrow> t \<in> \<D> ?lhs\<close> for u v
        proof (elim T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
          assume \<open>t2 = u @ v\<close> \<open>u \<in> \<T> (Q a)\<close> \<open>length u = n\<close> \<open>tF u\<close>
            \<open>ftF v\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close> \<open>length (t1 @ [ev a]) \<le> n\<close>
          from \<open>a \<in> A\<close> \<open>set t1 \<inter> ev ` A = {}\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close> \<open>u \<in> \<T> (Q a)\<close>
          have \<open>t1 @ ev a # u \<in> \<T> (P \<Theta> a\<in>A. Q a)\<close> by (auto simp add: T_Throw)
          moreover have \<open>n < length (t1 @ ev a # u)\<close> by (simp add: \<open>length u = n\<close>)
          ultimately have \<open>t1 @ ev a # u \<in> \<D> ?lhs\<close> by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
          moreover have \<open>t = (t1 @ ev a # u) @ v\<close> by (simp add: \<open>t = t1 @ ev a # t2\<close> \<open>t2 = u @ v\<close>)
          moreover from \<open>t1 @ [ev a] \<in> \<T> P\<close> \<open>tF u\<close> append_T_imp_tickFree
          have \<open>tF (t1 @ ev a # u)\<close> by auto
          ultimately show \<open>t \<in> \<D> ?lhs\<close> using \<open>ftF v\<close> is_processT7 by blast
        next
          fix w x assume \<open>t2 = u @ v\<close> \<open>u \<in> \<T> (Q a)\<close> \<open>length u = n\<close> \<open>tF u\<close> \<open>ftF v\<close>
            \<open>t1 @ [ev a] = w @ x\<close> \<open>w \<in> \<T> P\<close> \<open>length w = n\<close> \<open>tF w\<close> \<open>ftF x\<close>
          from \<open>t1 @ [ev a] = w @ x\<close> consider \<open>t1 @ [ev a] = w\<close>
            | x' where \<open>t1 = w @ x'\<close> \<open>x = x' @ [ev a]\<close>
            by (cases x rule: rev_cases) simp_all
          thus \<open>t \<in> \<D> ?lhs\<close>
          proof cases
            assume \<open>t1 @ [ev a] = w\<close>
            with \<open>a \<in> A\<close> \<open>set t1 \<inter> ev ` A = {}\<close> \<open>u \<in> \<T> (Q a)\<close> \<open>w \<in> \<T> P\<close>
            have \<open>t1 @ ev a # u \<in> \<T> (P \<Theta> a\<in>A. Q a)\<close> by (auto simp add: T_Throw)
            moreover have \<open>n < length (t1 @ ev a # u)\<close> by (simp add: \<open>length u = n\<close>)
            ultimately have \<open>t1 @ ev a # u \<in> \<D> ?lhs\<close> by (blast intro: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
            moreover have \<open>t = (t1 @ ev a # u) @ v\<close>
              by (simp add: \<open>t = t1 @ ev a # t2\<close> \<open>t2 = u @ v\<close>)
            moreover from \<open>t1 @ [ev a] = w\<close> \<open>tF u\<close> \<open>tF w\<close> have \<open>tF (t1 @ ev a # u)\<close> by auto
            ultimately show \<open>t \<in> \<D> ?lhs\<close> using \<open>ftF v\<close> is_processT7 by blast
          next
            fix x' assume \<open>t1 = w @ x'\<close> \<open>x = x' @ [ev a]\<close>
            from \<open>set t1 \<inter> ev ` A = {}\<close> \<open>t1 = w @ x'\<close> \<open>w \<in> \<T> P\<close>
            have \<open>w \<in> \<T> P \<and> set w \<inter> ev ` A = {}\<close> by auto
            hence \<open>w \<in> \<T> (P \<Theta> a\<in>A. Q a)\<close> by (simp add: T_Throw)
            with \<open>length w = n\<close> \<open>tF w\<close> have \<open>w \<in> \<D> ?lhs\<close>
              by (blast intro: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
            moreover have \<open>t = w @ x @ t2\<close>
              by (simp add: \<open>t = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] = w @ x\<close>)
            moreover from D_imp_front_tickFree[OF \<open>t \<in> \<D> ?rhs\<close>] \<open>t = t1 @ ev a # t2\<close> \<open>t1 = w @ x'\<close>
              front_tickFree_nonempty_append_imp that tickFree_append_iff
            have \<open>ftF (x @ t2)\<close> by (simp add: \<open>t = w @ x @ t2\<close> front_tickFree_append_iff)
            ultimately show \<open>t \<in> \<D> ?lhs\<close> by (simp add: \<open>tF w\<close> is_processT7)
          qed
        qed
      qed
    qed
  qed

  thus \<open>(t, X) \<in> \<F> ?rhs \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for t X
    by (meson is_processT8 le_approx2 mono_Throw restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_approx_self)
qed



subsection \<open>Non Destructiveness\<close>

lemma Throw_non_destructive :
  \<open>non_destructive (\<lambda>(P :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, Q). P \<Theta> a \<in> A. Q a)\<close>
proof (rule order_non_destructiveI, clarify)
  fix P P' :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and Q Q' :: \<open>'a \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and n
  assume \<open>(P, Q) \<down> n = (P', Q') \<down> n\<close> \<open>0 < n\<close>
  hence \<open>P \<down> n = P' \<down> n\<close> \<open>Q \<down> n = Q' \<down> n\<close>
    by (simp_all add: restriction_prod_def)

  { let ?lhs = \<open>P \<Theta> a \<in> A. Q a \<down> n\<close>
    fix t u v assume \<open>t = u @ v\<close> \<open>u \<in> \<T> (Throw P' A Q')\<close> \<open>length u = n\<close> \<open>tF u\<close> \<open>ftF v\<close>
    from this(2) consider \<open>u \<in> \<T> P'\<close> \<open>set u \<inter> ev ` A = {}\<close>
      | (divL) t1 t2 where \<open>u = t1 @ t2\<close> \<open>t1 \<in> \<D> P'\<close> \<open>tF t1\<close>
        \<open>set t1 \<inter> ev ` A = {}\<close> \<open>ftF t2\<close>
      | (traces) t1 a t2 where \<open>u = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P'\<close>
        \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>t2 \<in> \<T> (Q' a)\<close>
      unfolding T_Throw by blast
    hence \<open>t \<in> \<D> ?lhs\<close>
    proof cases
      assume \<open>u \<in> \<T> P'\<close> \<open>set u \<inter> ev ` A = {}\<close>
      from \<open>u \<in> \<T> P'\<close> \<open>length u = n\<close> \<open>P \<down> n = P' \<down> n\<close> have \<open>u \<in> \<T> P\<close>
        by (metis T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI dual_order.refl
            length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      with \<open>set u \<inter> ev ` A = {}\<close> have \<open>u \<in> \<T> (Throw P A Q)\<close>
        by (simp add: T_Throw)
      with \<open>ftF v\<close> \<open>t = u @ v\<close> \<open>tF u\<close> \<open>length u = n\<close> show \<open>t \<in> \<D> ?lhs\<close>
        by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI is_processT7)
    next
      case divL
      show \<open>t \<in> \<D> ?lhs\<close>
      proof (cases \<open>length t1 = n\<close>)
        assume \<open>length t1 = n\<close>
        with \<open>P \<down> n = P' \<down> n\<close> divL(2,4) have \<open>t1 \<in> \<T> (Throw P A Q)\<close>
          by (simp add: T_Throw)
            (metis D_T T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI dual_order.refl
              length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        with \<open>ftF v\<close> \<open>length t1 = n\<close> \<open>t = u @ v\<close> \<open>tF u\<close>
          divL(1,3,5) \<open>length u = n\<close> show \<open>t \<in> \<D> ?lhs\<close>
          by (auto simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k is_processT7)
      next
        assume \<open>length t1 \<noteq> n\<close>
        with \<open>length u = n\<close> divL(1) have \<open>length t1 < n\<close> by simp
        with \<open>P \<down> n = P' \<down> n\<close> divL(2,3,4) have \<open>t1 \<in> \<D> P\<close>
          by (simp add: D_Throw)
            (metis D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI length_less_in_D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        with \<open>ftF v\<close> \<open>t = u @ v\<close> divL(1,3,4) show \<open>t \<in> \<D> ?lhs\<close>
          by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k T_Throw)
            (metis \<open>length u = n\<close> \<open>tF u\<close> append.assoc divL(5))
      qed
    next
      case traces
      from \<open>length u = n\<close> traces(1)
      have \<open>length (t1 @ [ev a]) \<le> n\<close> \<open>length t2 \<le> n\<close> by simp_all
      from \<open>P \<down> n = P' \<down> n\<close> \<open>t1 @ [ev a] \<in> \<T> P'\<close> \<open>length (t1 @ [ev a]) \<le> n\<close>
      have \<open>t1 @ [ev a] \<in> \<T> P\<close>
        by (metis T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      moreover from \<open>length t2 \<le> n\<close> \<open>t2 \<in> \<T> (Q' a)\<close> \<open>Q \<down> n = Q' \<down> n\<close>
      have \<open>t2 \<in> \<T> (Q a)\<close>
        by (metis T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI restriction_fun_def
            length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      ultimately have \<open>u \<in> \<T> (P \<Theta> a \<in> A. Q a)\<close>
        using traces(1,3,4) unfolding T_Throw by blast
      with \<open>ftF v\<close> \<open>length u = n\<close> \<open>t = u @ v\<close> \<open>tF u\<close>
      show \<open>t \<in> \<D> ?lhs\<close> by (auto simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    qed
  } note * = this

  show \<open>P \<Theta> a \<in> A. Q a \<down> n \<sqsubseteq>\<^sub>F\<^sub>D P' \<Theta> a \<in> A. Q' a \<down> n\<close> (is \<open>?lhs \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close>)
  proof (unfold refine_defs, safe)
    show div : \<open>t \<in> \<D> ?rhs \<Longrightarrow> t \<in> \<D> ?lhs\<close> for t
    proof (elim D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
      assume \<open>t \<in> \<D> (P' \<Theta> a \<in> A. Q' a)\<close> \<open>length t \<le> n\<close>
      from this(1) consider (divL) t1 t2 where \<open>t = t1 @ t2\<close> \<open>t1 \<in> \<D> P'\<close>
        \<open>tF t1\<close> \<open>set t1 \<inter> ev ` A = {}\<close> \<open>ftF t2\<close>
      | (divR) t1 a t2 where \<open>t = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P'\<close>
        \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>t2 \<in> \<D> (Q' a)\<close>
        unfolding D_Throw by blast
      thus \<open>t \<in> \<D> ?lhs\<close>
      proof cases
        case divL
        show \<open>t \<in> \<D> ?lhs\<close>
        proof (cases \<open>length t1 = n\<close>)
          assume \<open>length t1 = n\<close>
          have \<open>t1 \<in> \<T> P'\<close> by (simp add: D_T divL(2))
          with \<open>P \<down> n = P' \<down> n\<close> \<open>length t1 = n\<close> have \<open>t1 \<in> \<T> P\<close>
            by (metis T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI dual_order.eq_iff
                length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
          with divL(4) have \<open>t1 \<in> \<T> (Throw P A Q)\<close> by (simp add: T_Throw)
          with \<open>length t1 = n\<close> divL(1,3,5) show \<open>t \<in> \<D> ?lhs\<close>
            by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI is_processT7)
        next
          assume \<open>length t1 \<noteq> n\<close>
          with \<open>length t \<le> n\<close> divL(1) have \<open>length t1 < n\<close> by simp
          with \<open>t1 \<in> \<D> P'\<close> \<open>P \<down> n = P' \<down> n\<close> have \<open>t1 \<in> \<D> P\<close>
            by (metis D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI length_less_in_D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
          with divL(3, 4) front_tickFree_Nil have \<open>t1 \<in> \<D> (Throw P A Q)\<close>
            by (simp (no_asm) add: D_Throw) blast
          with divL(1,3,5) show \<open>t \<in> \<D> ?lhs\<close>
            by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI is_processT7)
        qed
      next
        case divR
        from \<open>length t \<le> n\<close> divR(1)
        have \<open>length (t1 @ [ev a]) \<le> n\<close> \<open>length t2 < n\<close> by simp_all
        from \<open>P \<down> n = P' \<down> n\<close> \<open>t1 @ [ev a] \<in> \<T> P'\<close> \<open>length (t1 @ [ev a]) \<le> n\<close>
        have \<open>t1 @ [ev a] \<in> \<T> P\<close>
          by (metis T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        moreover from \<open>length t2 < n\<close> \<open>t2 \<in> \<D> (Q' a)\<close> \<open>Q \<down> n = Q' \<down> n\<close>
        have \<open>t2 \<in> \<D> (Q a)\<close>
          by (metis D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI restriction_fun_def
              length_less_in_D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        ultimately have \<open>t \<in> \<D> (P \<Theta> a \<in> A. Q a)\<close>
          using divR(1,3,4) unfolding D_Throw by blast
        thus \<open>t \<in> \<D> ?lhs\<close> by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
      qed
    next
      show \<open>t = u @ v \<Longrightarrow> u \<in> \<T> (Throw P' A Q') \<Longrightarrow> length u = n \<Longrightarrow>
            tF u \<Longrightarrow> ftF v \<Longrightarrow> t \<in> \<D> ?lhs\<close> for u v by (fact "*")
    qed

    show \<open>(t, X) \<in> \<F> ?rhs \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for t X
    proof (elim F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
      assume \<open>(t, X) \<in> \<F> (Throw P' A Q')\<close> \<open>length t \<le> n\<close>
      from this(1) consider \<open>t \<in> \<D> (Throw P' A Q')\<close> | \<open>(t, X) \<in> \<F> P'\<close> \<open>set t \<inter> ev ` A = {}\<close>
        | (failR) t1 a t2 where \<open>t = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P'\<close>
          \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>(t2, X) \<in> \<F> (Q' a)\<close>
        unfolding Throw_projs by auto
      thus \<open>(t, X) \<in> \<F> ?lhs\<close>
      proof cases
        assume \<open>t \<in> \<D> (Throw P' A Q')\<close>
        hence \<open>t \<in> \<D> ?rhs\<close> by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
        with D_F div show \<open>(t, X) \<in> \<F> ?lhs\<close> by blast
      next
        assume \<open>(t, X) \<in> \<F> P'\<close> \<open>set t \<inter> ev ` A = {}\<close>
        from \<open>(t, X) \<in> \<F> P'\<close> \<open>P \<down> n = P' \<down> n\<close> \<open>length t \<le> n\<close> have \<open>t \<in> \<T> P\<close>
          by (metis F_T T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        with \<open>set t \<inter> ev ` A = {}\<close> have \<open>t \<in> \<T> (Throw P A Q)\<close> by (simp add: T_Throw)
        from F_imp_front_tickFree \<open>(t, X) \<in> \<F> P'\<close> have \<open>ftF t\<close> by blast
        thus \<open>(t, X) \<in> \<F> ?lhs\<close>
        proof (elim front_tickFreeE)
          show \<open>(t, X) \<in> \<F> ?lhs\<close> if \<open>tF t\<close>
          proof (cases \<open>length t = n\<close>)
            assume \<open>length t = n\<close>
            with \<open>t \<in> \<T> (Throw P A Q)\<close> \<open>tF t\<close> front_tickFree_charn show \<open>(t, X) \<in> \<F> ?lhs\<close>
              by (simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) blast
          next
            assume \<open>length t \<noteq> n\<close>
            with \<open>length t \<le> n\<close> have \<open>length t < n\<close> by simp
            with \<open>(t, X) \<in> \<F> P'\<close> \<open>P \<down> n = P' \<down> n\<close> have \<open>(t, X) \<in> \<F> P\<close>
              by (simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k length_less_in_F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
            with \<open>set t \<inter> ev ` A = {}\<close> have \<open>(t, X) \<in> \<F> (Throw P A Q)\<close> by (simp add: F_Throw)
            thus \<open>(t, X) \<in> \<F> ?lhs\<close> by (simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
          qed
        next
          fix t' r assume \<open>t = t' @ [\<checkmark>(r)]\<close>
          with \<open>t \<in> \<T> (Throw P A Q)\<close> have \<open>(t, X) \<in> \<F> (Throw P A Q)\<close>
            by (simp add: tick_T_F)
          thus \<open>(t, X) \<in> \<F> ?lhs\<close> by (simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
        qed
      next
        case failR
        from \<open>length t \<le> n\<close> failR(1)
        have \<open>length (t1 @ [ev a]) \<le> n\<close> \<open>length t2 < n\<close> by simp_all
        from \<open>P \<down> n = P' \<down> n\<close> \<open>t1 @ [ev a] \<in> \<T> P'\<close> \<open>length (t1 @ [ev a]) \<le> n\<close>
        have \<open>t1 @ [ev a] \<in> \<T> P\<close>
          by (metis T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        moreover from \<open>length t2 < n\<close> \<open>(t2, X) \<in> \<F> (Q' a)\<close> \<open>Q \<down> n = Q' \<down> n\<close>
        have \<open>(t2, X) \<in> \<F> (Q a)\<close>
          by (metis F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI restriction_fun_def
              length_less_in_F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        ultimately have \<open>(t, X) \<in> \<F> (P \<Theta> a \<in> A. Q a)\<close>
          using failR(1,3,4) unfolding F_Throw by blast
        thus \<open>(t, X) \<in> \<F> ?lhs\<close> by (simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
      qed
    next
      show \<open>t = u @ v \<Longrightarrow> u \<in> \<T> (Throw P' A Q') \<Longrightarrow> length u = n \<Longrightarrow>
            tF u \<Longrightarrow> ftF v \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for u v
        by (simp add: "*" is_processT8)
    qed
  qed
qed



lemma ThrowR_constructive_if_disjoint_initials :
  \<open>constructive (\<lambda>Q :: 'a \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k. P \<Theta> a \<in> A. Q a)\<close>
  if \<open>A \<inter> {e. ev e \<in> P\<^sup>0} = {}\<close>
proof (rule order_constructiveI)
  fix Q Q' :: \<open>'a \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and n assume \<open>Q \<down> n = Q' \<down> n\<close>

  { let ?lhs = \<open>Throw P A Q \<down> Suc n\<close>
    fix t u v
    assume \<open>t = u @ v\<close> \<open>u \<in> \<T> (Throw P A Q')\<close> \<open>length u = Suc n\<close> \<open>tF u\<close> \<open>ftF v\<close>
    from \<open>u \<in> \<T> (Throw P A Q')\<close> consider \<open>u \<in> \<T> P\<close> \<open>set u \<inter> ev ` A = {}\<close>
      | (divL) t1 t2 where \<open>u = t1 @ t2\<close> \<open>t1 \<in> \<D> P\<close> \<open>tF t1\<close>
        \<open>set t1 \<inter> ev ` A = {}\<close> \<open>ftF t2\<close>
      | (traces) t1 a t2 where \<open>u = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close>
        \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>t2 \<in> \<T> (Q' a)\<close>
      unfolding T_Throw by blast
    hence \<open>u \<in> \<D> ?lhs\<close>
    proof cases
      assume \<open>u \<in> \<T> P\<close> \<open>set u \<inter> ev ` A = {}\<close>
      hence \<open>u \<in> \<T> (Throw P A Q)\<close> by (simp add: T_Throw)
      with \<open>length u = Suc n\<close> \<open>tF u\<close> show \<open>u \<in> \<D> ?lhs\<close>
        by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
    next
      case divL
      hence \<open>u \<in> \<D> (Throw P A Q)\<close> by (auto simp add: D_Throw)
      thus \<open>u \<in> \<D> ?lhs\<close> by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
    next
      case traces
      from \<open>length u = Suc n\<close> traces(1) have \<open>length t2 \<le> n\<close> by simp
      with \<open>t2 \<in> \<T> (Q' a)\<close> \<open>Q \<down> n = Q' \<down> n\<close> have \<open>t2 \<in> \<T> (Q a)\<close>
        by (metis T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI restriction_fun_def
            length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      with traces(1-4) have \<open>u \<in> \<T> (Throw P A Q)\<close> by (auto simp add: T_Throw)
      thus \<open>u \<in> \<D> ?lhs\<close>
        by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI \<open>length u = Suc n\<close> \<open>tF u\<close>)
    qed
    hence \<open>t \<in> \<D> ?lhs\<close> by (simp add: \<open>ftF v\<close> \<open>t = u @ v\<close> \<open>tF u\<close> is_processT7)
  } note * = this

  show \<open>(P \<Theta> a \<in> A. Q a) \<down> Suc n \<sqsubseteq>\<^sub>F\<^sub>D P \<Theta> a \<in> A. Q' a \<down> Suc n\<close> (is \<open>?lhs \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close>)
  proof (unfold refine_defs, safe)
    show div : \<open>t \<in> \<D> ?rhs \<Longrightarrow> t \<in> \<D> ?lhs\<close> for t
    proof (elim D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
      assume \<open>t \<in> \<D> (P \<Theta> a \<in> A. Q' a)\<close> \<open>length t \<le> Suc n\<close>
      from this(1) consider (divL) t1 t2 where \<open>t = t1 @ t2\<close> \<open>t1 \<in> \<D> P\<close>
        \<open>tF t1\<close> \<open>set t1 \<inter> ev ` A = {}\<close> \<open>ftF t2\<close>
      | (divR) t1 a t2 where \<open>t = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close>
        \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>t2 \<in> \<D> (Q' a)\<close>
        unfolding D_Throw by blast
      thus \<open>t \<in> \<D> ?lhs\<close>
      proof cases
        case divL
        hence \<open>t \<in> \<D> (P \<Theta> a \<in> A. Q a)\<close> by (auto simp add: D_Throw)
        thus \<open>t \<in> \<D> ?lhs\<close> by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
      next
        case divR
        from divR(2,4) that have \<open>t1 \<noteq> []\<close>
          by (cases t1) (auto intro: initials_memI)
        with divR(1) \<open>length t \<le> Suc n\<close> nat_less_le have \<open>length t2 < n\<close> by force
        with \<open>t2 \<in> \<D> (Q' a)\<close> \<open>Q \<down> n = Q' \<down> n\<close> have \<open>t2 \<in> \<D> (Q a)\<close>
          by (metis D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI restriction_fun_def
              length_less_in_D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        with divR(1-4) have \<open>t \<in> \<D> (Throw P A Q)\<close> by (auto simp add: D_Throw)
        thus \<open>t \<in> \<D> ?lhs\<close> by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
      qed
    next
      show \<open>t = u @ v \<Longrightarrow> u \<in> \<T> (Throw P A Q') \<Longrightarrow> length u = Suc n \<Longrightarrow>
            tF u \<Longrightarrow> ftF v \<Longrightarrow> t \<in> \<D> ?lhs\<close> for u v by (fact "*")
    qed

    show \<open>(t, X) \<in> \<F> ?rhs \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for t X
    proof (elim F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
      assume \<open>(t, X) \<in> \<F> (Throw P A Q')\<close> \<open>length t \<le> Suc n\<close>
      from this(1) consider \<open>t \<in> \<D> (Throw P A Q')\<close> | \<open>(t, X) \<in> \<F> P\<close> \<open>set t \<inter> ev ` A = {}\<close>
        | (failR) t1 a t2 where \<open>t = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close>
          \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>(t2, X) \<in> \<F> (Q' a)\<close>
        unfolding Throw_projs by auto
      thus \<open>(t, X) \<in> \<F> ?lhs\<close>
      proof cases
        assume \<open>t \<in> \<D> (Throw P A Q')\<close>
        hence \<open>t \<in> \<D> ?rhs\<close> by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
        with D_F div show \<open>(t, X) \<in> \<F> ?lhs\<close> by blast
      next
        assume \<open>(t, X) \<in> \<F> P\<close> \<open>set t \<inter> ev ` A = {}\<close>
        hence \<open>(t, X) \<in> \<F> (Throw P A Q)\<close> by (simp add: F_Throw)
        thus \<open>(t, X) \<in> \<F> ?lhs\<close> by (simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
      next
        case failR
        from failR(2, 4) that have \<open>t1 \<noteq> []\<close>
          by (cases t1) (auto intro: initials_memI)
        with failR(1) \<open>length t \<le> Suc n\<close> nat_less_le have \<open>length t2 < n\<close> by force
        with \<open>(t2, X) \<in> \<F> (Q' a)\<close> \<open>Q \<down> n = Q' \<down> n\<close> have \<open>(t2, X) \<in> \<F> (Q a)\<close>
          by (metis F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI restriction_fun_def
              length_less_in_F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        with failR(1-4) have \<open>(t, X) \<in> \<F> (Throw P A Q)\<close> by (auto simp add: F_Throw)
        thus \<open>(t, X) \<in> \<F> ?lhs\<close> by (simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
      qed
    next
      show \<open>t = u @ v \<Longrightarrow> u \<in> \<T> (Throw P A Q') \<Longrightarrow> length u = Suc n \<Longrightarrow>
            tF u \<Longrightarrow> ftF v \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for u v
        by (simp add: "*" is_processT8)
    qed
  qed
qed


(*<*)
end
  (*>*)