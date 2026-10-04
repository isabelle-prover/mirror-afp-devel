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
              (metis append_Nil append_self_conv ftF_charn inf_bot_left
                is_ev_def is_processT1_TR length_0_conv length_Cons list.set(1)
                tF_Cons_iff tF_Nil)
        next
          show \<open>[] \<in> \<D> P \<Longrightarrow> t \<in> \<D> (P \<Theta> a \<in> A. Q2 a \<down> 1)\<close>
            by (simp flip: BOT_iff_Nil_D add: D_BOT)
              (use \<open>t = [e]\<close> ftF_single in blast)
        next
          show \<open>t = [ev a] \<Longrightarrow> [ev a] \<in> \<D> P \<Longrightarrow> a \<notin> A \<Longrightarrow> t \<in> \<D> (P \<Theta> a \<in> A. Q2 a \<down> 1)\<close> for a  
            by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k D_Throw disjoint_iff image_iff)
              (metis append.right_neutral empty_set event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1)
                ftF_Nil list.simps(15) singletonD tF_Cons_iff tF_Nil)
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
              ftF_Nil inf_bot_left is_processT1_TR length_Cons
              list.size(3) tF_Cons_iff tF_Nil)
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
          (blast, metis (no_types, lifting) ftF_append inf_sup_aci(8) inf_sup_distrib2 sup_bot_right)
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
            by (cases v rule: rev_cases) (simp_all add: ftF_append_iff)
          thus \<open>t \<in> \<D> ?lhs\<close>
          proof cases
            from \<open>a \<in> A\<close> \<open>length u = n\<close> \<open>set t1 \<inter> ev ` A = {}\<close> \<open>t2 \<in> \<D> (Q a)\<close> \<open>tF u\<close> \<open>u \<in> \<T> P\<close>
            show \<open>t1 @ [ev a] = u \<Longrightarrow> t \<in> \<D> ?lhs\<close>
              by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k T_Throw \<open>t = t1 @ ev a # t2\<close>)
                (metis Cons_eq_appendI D_imp_ftF append_Nil append_assoc is_processT1_TR)
          next
            from \<open>ftF v\<close> \<open>length u = n\<close> \<open>set t1 \<inter> ev ` A = {}\<close> \<open>t = t1 @ ev a # t2\<close> \<open>u \<in> \<T> P\<close>
            show \<open>t1 = u @ v' \<Longrightarrow> v = v' @ [ev a] \<Longrightarrow> ftF v' \<Longrightarrow> t \<in> \<D> ?lhs\<close> for v'
              by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k T_Throw)
                (metis D_imp_ftF Int_assoc Un_Int_eq(3) append_assoc
                  ftF_append ftF_nonempty_append_imp
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
          moreover from \<open>t1 @ [ev a] \<in> \<T> P\<close> \<open>tF u\<close> append_T_imp_tF
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
            moreover from D_imp_ftF[OF \<open>t \<in> \<D> ?rhs\<close>] \<open>t = t1 @ ev a # t2\<close> \<open>t1 = w @ x'\<close>
              ftF_nonempty_append_imp that tF_append_iff
            have \<open>ftF (x @ t2)\<close> by (simp add: \<open>t = w @ x @ t2\<close> ftF_append_iff)
            ultimately show \<open>t \<in> \<D> ?lhs\<close> by (simp add: \<open>tF w\<close> is_processT7)
          qed
        qed
      qed
    qed
  qed

  thus \<open>(t, X) \<in> \<F> ?rhs \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for t X
    by (meson is_processT8 le_approxD(2) mono_Throw restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_approx_self)
qed



subsection \<open>Non Destructiveness\<close>

lemma Throw_non_destructive :
  \<open>non_destructive (\<lambda>(P :: ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, Q). P \<Theta> a \<in> A. Q a)\<close>
proof (rule order_non_destructiveI, clarify)
  fix P P' :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and Q Q' :: \<open>'a \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and n
  assume \<open>(P, Q) \<down> n = (P', Q') \<down> n\<close> \<open>0 < n\<close>
  hence \<open>P \<down> n = P' \<down> n\<close> \<open>Q \<down> n = Q' \<down> n\<close>
    by (simp_all add: restriction_prod_def)
  show \<open>P \<Theta> a \<in> A. Q a \<down> n \<sqsubseteq>\<^sub>F\<^sub>D P' \<Theta> a \<in> A. Q' a \<down> n\<close>
  proof (rule leFD_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
    show \<open>t \<in> \<D> (P' \<Theta> a \<in> A. Q' a) \<Longrightarrow> t \<in> \<D> (P \<Theta> a \<in> A. Q a \<down> n)\<close> for t
      by (metis (no_types, lifting) ext \<open>P \<down> n = P' \<down> n\<close> \<open>Q \<down> n = Q' \<down> n\<close>[unfolded restriction_fun_def]
          in_mono le_FD_D(1) mono_Throw_FD restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD_self
          restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Throw_FD)
  next
    show \<open>(s, X) \<in> \<F> (P' \<Theta> a \<in> A. Q' a) \<Longrightarrow> (s, X) \<in> \<F> (P \<Theta> a \<in> A. Q a \<down> n)\<close> for s X
      by (metis (no_types, lifting) ext \<open>P \<down> n = P' \<down> n\<close>
          \<open>Q \<down> n = Q' \<down> n\<close>[unfolded restriction_fun_def]
          in_mono le_FD_D(2) mono_Throw_FD restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_FD_self
          restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Throw_FD)
  qed
qed




text \<open>Stronger version in Isabelle26, initially suggested
to Burkhart by Claude and polished by Benoît.\<close>

lemma ThrowR_constructive :
  \<open>constructive (\<lambda>Q :: 'a \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k. P \<Theta> a \<in> A. Q a)\<close>
proof (rule order_constructiveI)
  fix Q Q' :: \<open>'a \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and n assume \<open>Q \<down> n = Q' \<down> n\<close>
  show \<open>(P \<Theta> a \<in> A. Q a) \<down> Suc n \<sqsubseteq>\<^sub>F\<^sub>D P \<Theta> a \<in> A. Q' a \<down> Suc n\<close> (is \<open>?lhs \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close>)
  proof (rule failure_divergence_refineI_D\<^sub>m\<^sub>i\<^sub>n_version)
    fix t assume \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n ?rhs\<close>
    hence \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n (P \<Theta> a \<in> A. Q' a) \<and> length t \<le> Suc n \<or>
      t \<in> \<T> (P \<Theta> a \<in> A. Q' a) - \<D> (P \<Theta> a \<in> A. Q' a) \<and> length t = Suc n \<and> tF t\<close>
      by (simp add: D\<^sub>m\<^sub>i\<^sub>n_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    thus \<open>t \<in> \<D> ?lhs\<close>
    proof (elim disjE conjE)
      assume \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n (P \<Theta> a \<in> A. Q' a)\<close> \<open>length t \<le> Suc n\<close>
      from this(1) consider (D_P) \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n P\<close> \<open>tF t\<close> \<open>set t \<inter> ev ` A = {}\<close>
        | (D_Q) t1 a t2 where \<open>t = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close>
          \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>t2 \<in> \<D>\<^sub>m\<^sub>i\<^sub>n (Q' a)\<close>
        by (blast dest: D\<^sub>m\<^sub>i\<^sub>n_Throw_subset[THEN set_mp])
      thus \<open>t \<in> \<D> ?lhs\<close>
      proof cases
        case D_P thus \<open>t \<in> \<D> ?lhs\<close>
          by (intro D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI, simp add: D_Throw)
            (metis (mono_tags, lifting) D\<^sub>m\<^sub>i\<^sub>n_D append.right_neutral ftF_Nil)
      next
        case D_Q
        from D_Q(1) \<open>length t \<le> Suc n\<close> have \<open>length t2 \<le> n\<close> by simp
        hence \<open>length t2 < n \<or> length t2 = n\<close> by presburger
        thus \<open>t \<in> \<D> ?lhs\<close>
        proof (elim disjE)
          assume \<open>length t2 < n\<close>
          with D_Q(5) \<open>Q \<down> n = Q' \<down> n\<close> have \<open>t2 \<in> \<D> (Q a)\<close>
            by (metis D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI Divergences\<^sub>m\<^sub>i\<^sub>n_def elem_min_elems
                length_less_in_D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k restriction_fun_def)
          with D_Q(1-4) show \<open>t \<in> \<D> ?lhs\<close>
            by (auto intro: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI simp add: D_Throw)
        next
          from \<open>t \<in> \<D>\<^sub>m\<^sub>i\<^sub>n (P \<Theta> a \<in> A. Q' a)\<close> have \<open>tF t\<close> by (fact tF_mem_D\<^sub>m\<^sub>i\<^sub>n)
          assume \<open>length t2 = n\<close>
          with D_Q(5) \<open>Q \<down> n = Q' \<down> n\<close> have \<open>t2 \<in> \<T> (Q a)\<close>
            by (metis D\<^sub>m\<^sub>i\<^sub>n_D D_T D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI Orderings.order_eq_iff
                length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k restriction_fun_def)
          with D_Q(1-4) \<open>length t2 = n\<close> have \<open>t \<in> \<T> (P \<Theta> a \<in> A. Q a)\<close> \<open>Suc n \<le> length t\<close>
            by (auto simp add: T_Throw)
          with \<open>tF t\<close> show \<open>t \<in> \<D> ?lhs\<close>
            by (metis D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI antisym_conv1)
        qed
      qed
    next
      assume \<open>t \<in> \<T> (P \<Theta> a \<in> A. Q' a) - \<D> (P \<Theta> a \<in> A. Q' a)\<close> \<open>length t = Suc n\<close> \<open>tF t\<close>
      from this(1) consider (T_P) \<open>t \<in> \<T> P\<close> \<open>set t \<inter> ev ` A = {}\<close>
        | (T_Q) t1 a t2 where \<open>t = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close>
          \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>t2 \<in> \<T> (Q' a)\<close>
        unfolding Throw_projs by fast
      thus \<open>t \<in> \<D> ?lhs\<close>
      proof cases
        case T_P with \<open>length t = Suc n\<close> \<open>tF t\<close> show \<open>t \<in> \<D> ?lhs\<close>
          by (auto intro: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI simp add: Throw_projs)
      next
        case T_Q
        from T_Q(1) \<open>length t = Suc n\<close> have \<open>length t2 \<le> n\<close> by simp
        with T_Q(5) \<open>Q \<down> n = Q' \<down> n\<close> have \<open>t2 \<in> \<T> (Q a)\<close>
          by (metis T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI
              length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k restriction_fun_def)
        with T_Q(1-4) have \<open>t \<in> \<T> (P \<Theta> a \<in> A. Q a)\<close>
          by (auto simp add: T_Throw)
        with \<open>tF t\<close> \<open>length t = Suc n\<close> show \<open>t \<in> \<D> ?lhs\<close>
          by (blast intro: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
      qed
    qed
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?rhs\<close> \<open>t \<notin> \<D> ?rhs\<close>
    with le_approxD(2) restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_approx_self
    have \<open>(t, X) \<in> \<F> (P \<Theta> a \<in> A. Q' a) \<and> t \<notin> \<D> (P \<Theta> a \<in> A. Q' a)\<close>
      by (blast intro: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
    then consider (F_P) \<open>(t, X) \<in> \<F> P\<close> \<open>set t \<inter> ev ` A = {}\<close>
      | (F_Q) t1 a t2 where \<open>t = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close>
        \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>(t2, X) \<in> \<F> (Q' a)\<close>
      unfolding Throw_projs by blast
    thus \<open>(t, X) \<in> \<F> ?lhs\<close>
    proof cases
      case F_P thus \<open>(t, X) \<in> \<F> ?lhs\<close>
        by (auto intro: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI simp add: F_Throw)
    next
      case F_Q
      with \<open>(t, X) \<in> \<F> (P \<Theta> a \<in> A. Q' a) \<and> t \<notin> \<D> (P \<Theta> a \<in> A. Q' a)\<close>
        \<open>(t, X) \<in> \<F> ?rhs\<close> \<open>t \<notin> \<D> ?rhs\<close> have \<open>length t2 \<le> n\<close>
        by (metis D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI F_T add_leE length_Cons
            length_append linorder_not_le not_less_eq_eq)
      with F_Q(5) consider \<open>length t2 < n\<close> | \<open>tF t2\<close> \<open>length t2 = n\<close>
        | t2' r where \<open>t2 = t2' @ [\<checkmark>(r)]\<close> \<open>length t2 = n\<close>
        by (metis is_processT2 not_tF_and_ftF order_neq_le_trans)
      thus \<open>(t, X) \<in> \<F> ?lhs\<close>
      proof cases
        assume \<open>length t2 < n\<close>
        with F_Q(5) \<open>Q \<down> n = Q' \<down> n\<close> have \<open>(t2, X) \<in> \<F> (Q a)\<close>
          by (metis F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI
              length_less_in_F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k restriction_fun_def)
        with F_Q(1-4) show \<open>(t, X) \<in> \<F> ?lhs\<close>
          by (auto intro: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI simp add: F_Throw)
      next
        assume \<open>tF t2\<close> \<open>length t2 = n\<close>
        from this(2) F_Q(5) \<open>Q \<down> n = Q' \<down> n\<close> have \<open>t2 \<in> \<T> (Q a)\<close>
          by (metis F_T T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI dual_order.refl
              length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k restriction_fun_def)
        with F_Q(1-4) \<open>tF t2\<close> \<open>length t2 = n\<close> show \<open>(t, X) \<in> \<F> ?lhs\<close>
          by (auto intro!: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI simp add: T_Throw)
      next
        fix t2' r assume \<open>t2 = t2' @ [\<checkmark>(r)]\<close> \<open>length t2 = n\<close>
        from this(2) F_Q(5) \<open>Q \<down> n = Q' \<down> n\<close> have \<open>t2 \<in> \<T> (Q a)\<close>
          by (metis F_T T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI dual_order.refl
              length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k restriction_fun_def)
        with F_Q(1-4) have \<open>t \<in> \<T> ?lhs\<close>
          by (auto intro!: T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI simp add: T_Throw)
        with F_Q(1) \<open>t2 = t2' @ [\<checkmark>(r)]\<close> show \<open>(t, X) \<in> \<F> ?lhs\<close>
          by (metis Cons_eq_appendI append_assoc tick_T_F)
      qed
    qed
  qed
qed


(*<*)
end
  (*>*)