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



subsection \<open>Constructiveness in the Continuation\<close>

text \<open>Constructiveness in the continuation of \<^const>\<open>Throw\<close> (FDR's exception operator
\<open>P [| A |> Q\<close>): the continuation only starts after an event of \<open>A\<close>. In contrast to
@{thm [source] ThrowR_constructive_if_disjoint_initials}, no condition on the initials of \<open>P\<close>
is needed.

Context: these rules arose from the crash handling of the Dali model (\<^verbatim>\<open>HOL-CSPM/Dali.thy\<close>),
where e.g. \<open>DaliCrashR = (DaliRecovery ||| (crash \<rightarrow> Skip)) \<Theta> a \<in> alphaCrash. DaliCrashR\<close>
recurses only through the continuation. There, the exception event \<open>crash\<close> is an initial of the
left operand, so the disjointness condition fails and Dali was only accepted via the HOLCF
fallback. Since the continuation is entered only \<^emph>\<open>after\<close> an event of \<open>A\<close>, recursion through it
is guarded regardless of the initials of \<open>P\<close>, and with the rules below the \<^verbatim>\<open>Fixrec\<close> package accepts Dali in
restriction spaces. The proofs use the explicit introduction rules \<open>T_ThrowI_exc\<close> and
\<open>D_ThrowI_exc\<close>, since \<open>metis\<close>/\<open>blast\<close>/\<open>auto\<close> loop on the set descriptions of
@{thm [source] T_Throw} and @{thm [source] D_Throw}. A minimal test of the pattern is
\<open>cr\<close>/\<open>cr'\<close> in \<^verbatim>\<open>HOL-CSP_RS/Fixrec_RS.thy\<close>.\<close>

lemmas T_ThrowI_exc = T_ThrowI2  \<comment> \<open>the trace version is a general fact of \<^session>\<open>HOL-CSPM\<close>\<close>

lemma D_ThrowI_exc : \<open>t1 @ [ev a] \<in> \<T> P \<Longrightarrow> set t1 \<inter> ev ` A = {} \<Longrightarrow> a \<in> A \<Longrightarrow> t2 \<in> \<D> (Q a)
                        \<Longrightarrow> t1 @ ev a # t2 \<in> \<D> (P \<Theta> a \<in> A. Q a)\<close>
  unfolding D_Throw by blast

lemma ThrowR_constructive :
  \<open>constructive (\<lambda>Q :: 'a \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k. P \<Theta> a \<in> A. Q a)\<close>
proof (rule order_constructiveI)
  fix Q Q' :: \<open>'a \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and n assume eq : \<open>Q \<down> n = Q' \<down> n\<close>
  let ?lhs = \<open>Throw P A Q \<down> Suc n\<close>

  have T_agree : \<open>length s \<le> n \<Longrightarrow> s \<in> \<T> (Q' a) \<Longrightarrow> s \<in> \<T> (Q a)\<close> for s a
    by (metis T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI eq restriction_fun_def
              length_le_in_T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  have D_agree : \<open>length s < n \<Longrightarrow> s \<in> \<D> (Q' a) \<Longrightarrow> s \<in> \<D> (Q a)\<close> for s a
    by (metis D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI eq restriction_fun_def
              length_less_in_D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  have F_agree : \<open>length s < n \<Longrightarrow> (s, X) \<in> \<F> (Q' a) \<Longrightarrow> (s, X) \<in> \<F> (Q a)\<close> for s X a
    by (metis F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI eq restriction_fun_def
              length_less_in_F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)

  \<comment> \<open>traces of maximal length (the depth of the restriction) diverge in \<open>?lhs\<close>\<close>
  have maxlen : \<open>t1 @ ev a # t2 \<in> \<D> ?lhs\<close>
    if \<open>t1 @ [ev a] \<in> \<T> P\<close> \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>t2 \<in> \<T> (Q' a)\<close>
       \<open>length (t1 @ ev a # t2) = Suc n\<close> \<open>tF (t1 @ ev a # t2)\<close> for t1 a t2
  proof -
    from that(5) have \<open>length t2 \<le> n\<close> by simp
    with that(4) T_agree have \<open>t2 \<in> \<T> (Q a)\<close> by blast
    with that(1-3) have \<open>t1 @ ev a # t2 \<in> \<T> (Throw P A Q)\<close> by (auto simp add: T_Throw)
    with that(5,6) show ?thesis by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
  qed

  { fix t u v
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
      with maxlen \<open>length u = Suc n\<close> \<open>tF u\<close> show \<open>u \<in> \<D> ?lhs\<close> by blast
    qed
    hence \<open>t \<in> \<D> ?lhs\<close> by (simp add: \<open>ftF v\<close> \<open>t = u @ v\<close> \<open>tF u\<close> is_processT7)
  } note * = this

  \<comment> \<open>continuation diverging on a trace of length \<open>n\<close> right after the initial event\<close>
  have divR_long : \<open>ev a # t2 \<in> \<D> ?lhs\<close>
    if prem: \<open>[ev a] \<in> \<T> P\<close> \<open>a \<in> A\<close> \<open>t2 \<in> \<D> (Q' a)\<close> \<open>length t2 = n\<close> for a t2
  proof (cases \<open>tF t2\<close>)
    case True
    have t2T : \<open>t2 \<in> \<T> (Q' a)\<close> using prem(3) by (rule D_T)
    have \<open>[] @ ev a # t2 \<in> \<D> ?lhs\<close>
      by (rule maxlen) (use prem(1,2,4) True t2T in simp_all)
    thus ?thesis by simp
  next
    case False
    obtain t2' r where eq2 : \<open>t2 = t2' @ [\<checkmark>(r)]\<close>
      using False D_imp_ftF[OF prem(3)] not_tF_and_ftF by blast
    from prem(3) have \<open>t2' @ [\<checkmark>(r)] \<in> \<D> (Q' a)\<close> by (simp add: eq2)
    hence \<open>t2' \<in> \<D> (Q' a)\<close> by (rule is_processT9)
    moreover have \<open>length t2' < n\<close> using eq2 prem(4) by simp
    ultimately have t2'D : \<open>t2' \<in> \<D> (Q a)\<close> by (rule_tac D_agree)
    have \<open>[] @ ev a # t2' \<in> \<D> (Throw P A Q)\<close>
      by (rule D_ThrowI_exc) (use prem(1,2) t2'D in simp_all)
    moreover have \<open>tF t2'\<close>
      using D_imp_ftF[OF prem(3)] eq2 by (simp add: ftF_append_iff)
    ultimately have \<open>(ev a # t2') @ [\<checkmark>(r)] \<in> \<D> (Throw P A Q)\<close>
      by (intro is_processT7) simp_all
    thus ?thesis by (simp add: eq2 D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
  qed

  show \<open>(P \<Theta> a \<in> A. Q a) \<down> Suc n \<sqsubseteq>\<^sub>F\<^sub>D P \<Theta> a \<in> A. Q' a \<down> Suc n\<close> (is \<open>_ \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close>)
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
        show \<open>t \<in> \<D> ?lhs\<close>
        proof (cases \<open>length t2 < n\<close>)
          case True
          with \<open>t2 \<in> \<D> (Q' a)\<close> have \<open>t2 \<in> \<D> (Q a)\<close> by (simp add: D_agree)
          with divR(1-4) have \<open>t \<in> \<D> (Throw P A Q)\<close> by (auto simp add: D_Throw)
          thus \<open>t \<in> \<D> ?lhs\<close> by (simp add: D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
        next
          case False
          with divR(1) \<open>length t \<le> Suc n\<close> have \<open>t1 = []\<close> \<open>length t2 = n\<close> by (cases t1, simp_all)+
          with divR divR_long show \<open>t \<in> \<D> ?lhs\<close> by simp
        qed
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
        show \<open>(t, X) \<in> \<F> ?lhs\<close>
        proof (cases \<open>length t2 < n\<close>)
          case True
          with \<open>(t2, X) \<in> \<F> (Q' a)\<close> have \<open>(t2, X) \<in> \<F> (Q a)\<close> by (simp add: F_agree)
          with failR(1-4) have \<open>(t, X) \<in> \<F> (Throw P A Q)\<close> by (auto simp add: F_Throw)
          thus \<open>(t, X) \<in> \<F> ?lhs\<close> by (simp add: F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
        next
          case False
          with failR(1) \<open>length t \<le> Suc n\<close> have \<open>t1 = []\<close> \<open>length t2 = n\<close> by (cases t1, simp_all)+
          from failR(5) have t2T: \<open>t2 \<in> \<T> (Q' a)\<close> by (simp add: F_T)
          show \<open>(t, X) \<in> \<F> ?lhs\<close>
          proof (cases \<open>tF t2\<close>)
            case True
            with maxlen[of \<open>[]\<close> a t2] failR(2-4) t2T \<open>t1 = []\<close> \<open>length t2 = n\<close> failR(1)
            have \<open>t \<in> \<D> ?lhs\<close> by simp
            thus \<open>(t, X) \<in> \<F> ?lhs\<close> using D_F by blast
          next
            case False
            with F_imp_ftF[OF failR(5)] obtain t2' r where eq2 : \<open>t2 = t2' @ [\<checkmark>(r)]\<close>
              using not_tF_and_ftF by blast
            have \<open>t2 \<in> \<T> (Q a)\<close> by (rule T_agree) (simp_all add: \<open>length t2 = n\<close> t2T)
            hence \<open>[] @ ev a # t2 \<in> \<T> (Throw P A Q)\<close>
              by (intro T_ThrowI_exc) (use failR(2-4) \<open>t1 = []\<close> in simp_all)
            hence \<open>(ev a # t2') @ [\<checkmark>(r)] \<in> \<T> (Throw P A Q)\<close> by (simp add: eq2)
            hence \<open>((ev a # t2') @ [\<checkmark>(r)], X) \<in> \<F> (Throw P A Q)\<close> by (rule tick_T_F)
            thus \<open>(t, X) \<in> \<F> ?lhs\<close>
              by (simp add: failR(1) \<open>t1 = []\<close> eq2 F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kI)
          qed
        qed
      qed
    next
      show \<open>t = u @ v \<Longrightarrow> u \<in> \<T> (Throw P A Q') \<Longrightarrow> length u = Suc n \<Longrightarrow>
            tF u \<Longrightarrow> ftF v \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for u v
        by (simp add: "*" is_processT8)
    qed
  qed
qed

text \<open>More generally, the whole \<^const>\<open>Throw\<close> is constructive if the left operand is
constructive and the continuation non-destructive: restricted to depth \<open>Suc n\<close>, \<open>P \<Theta> a \<in> A. Q a\<close>
depends only on \<open>P\<close> up to depth \<open>Suc n\<close> (@{thm [source] Throw_non_destructive}) and on \<open>Q\<close> up to
depth \<open>n\<close> (@{thm [source] ThrowR_constructive}). Constructiveness of the left operand cannot be
weakened: for \<open>A = {}\<close>, \<open>P \<Theta> a \<in> A. Q a = P\<close>.\<close>

lemma Throw_constructive_continuation :
  \<open>constructive f \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> non_destructive (g a)) \<Longrightarrow> constructive (\<lambda>x. f x \<Theta> a \<in> A. g a x)\<close>
proof -
  assume cf : \<open>constructive f\<close> and nd : \<open>\<And>a. a \<in> A \<Longrightarrow> non_destructive (g a)\<close>
  let ?g = \<open>\<lambda>x a. if a \<in> A then g a x else STOP\<close>
  have * : \<open>f x \<Theta> a \<in> A. g a x = f x \<Theta> a \<in> A. ?g x a\<close> for x
    by (auto intro: mono_Throw_eq)
  have ndg : \<open>non_destructive ?g\<close> by (auto intro: nd)
  show \<open>constructive (\<lambda>x. f x \<Theta> a \<in> A. g a x)\<close>
  proof (subst "*", rule constructiveI)
    fix n and x y :: 'a assume eq : \<open>x \<down> n = y \<down> n\<close>
    have \<open>(f x \<Theta> a \<in> A. ?g x a) \<down> Suc n = (f y \<Theta> a \<in> A. ?g x a) \<down> Suc n\<close>
      using non_destructiveD[OF Throw_non_destructive, of \<open>(f x, ?g x)\<close> \<open>Suc n\<close> \<open>(f y, ?g x)\<close>]
            constructiveD[OF cf eq]
      by (simp add: restriction_prod_def)
    also have \<open>\<dots> = (f y \<Theta> a \<in> A. ?g y a) \<down> Suc n\<close>
      by (rule constructiveD[OF ThrowR_constructive non_destructiveD[OF ndg eq]])
    finally show \<open>(f x \<Theta> a \<in> A. ?g x a) \<down> Suc n = (f y \<Theta> a \<in> A. ?g y a) \<down> Suc n\<close> .
  qed
qed



(*<*)
end
  (*>*)