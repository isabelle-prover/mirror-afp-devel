(***********************************************************************************
 * Copyright (c) 2025 Université Paris-Saclay
 *
 * Author: Benoît Ballenghien, Université Paris-Saclay,
 *         CNRS, ENS Paris-Saclay, LMF
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


section \<open>Associativity\<close>

(*<*)
theory Synchronization_Product_Generalized_Associativity
  imports CSP_PTick_Renaming
begin
  (*>*)



subsection \<open>Motivation\<close>

text \<open>
The classical synchronization product is associative: @{thm Sync_assoc[of P A Q R]}
but in our generalization such a law cannot be obtained in all generality.
We already encountered a similar issue for the commutativity:
we have to find a setup in which the different combinations of the ticks
that we need make sense, and prove the quasi-associativity.
\<close>



subsection \<open>Formalization\<close>

locale Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_locale =
  Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>1 : Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale \<open>(\<otimes>\<checkmark>1)\<close> +
  Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>2 : Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale \<open>(\<otimes>\<checkmark>2)\<close> +
  Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>3 : Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale \<open>(\<otimes>\<checkmark>3)\<close> +
  Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>4 : Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale \<open>(\<otimes>\<checkmark>4)\<close>
  for tick_join1 :: \<open>'r \<Rightarrow> 's \<Rightarrow> 't option\<close> (infixl \<open>\<otimes>\<checkmark>1\<close> 100)
    and tick_join2 :: \<open>'t \<Rightarrow> 'u \<Rightarrow> 'v option\<close> (infixl \<open>\<otimes>\<checkmark>2\<close> 100)
    and tick_join3 :: \<open>'r \<Rightarrow> 'w \<Rightarrow> 'x option\<close> (infixl \<open>\<otimes>\<checkmark>3\<close> 100)
    and tick_join4 :: \<open>'s \<Rightarrow> 'u \<Rightarrow> 'w option\<close> (infixl \<open>\<otimes>\<checkmark>4\<close> 100) +
  fixes tick_assoc_ren      :: \<open>'v \<Rightarrow> 'x\<close> (\<open>\<otimes>\<checkmark>2\<Rightarrow>\<otimes>\<checkmark>3\<close>)
    and tick_assoc_ren_conv :: \<open>'x \<Rightarrow> 'v\<close> (\<open>\<otimes>\<checkmark>3\<Rightarrow>\<otimes>\<checkmark>2\<close>)
  assumes None_assms_tick_join :
    \<open>r \<otimes>\<checkmark>1 s = \<diamond> \<Longrightarrow> s \<otimes>\<checkmark>4 u = \<diamond> \<or> r \<otimes>\<checkmark>3 \<lceil>s \<otimes>\<checkmark>4 u\<rceil> = \<diamond>\<close>
    \<open>r \<otimes>\<checkmark>1 s \<noteq> \<diamond> \<Longrightarrow> \<lceil>r \<otimes>\<checkmark>1 s\<rceil> \<otimes>\<checkmark>2 u = \<diamond> \<Longrightarrow> s \<otimes>\<checkmark>4 u = \<diamond> \<or> r \<otimes>\<checkmark>3 \<lceil>s \<otimes>\<checkmark>4 u\<rceil> = \<diamond>\<close>
    \<open>s \<otimes>\<checkmark>4 u = \<diamond> \<Longrightarrow> r \<otimes>\<checkmark>1 s = \<diamond> \<or> \<lceil>r \<otimes>\<checkmark>1 s\<rceil> \<otimes>\<checkmark>2 u = \<diamond>\<close>
    \<open>s \<otimes>\<checkmark>4 u \<noteq> \<diamond> \<Longrightarrow> r \<otimes>\<checkmark>3 \<lceil>s \<otimes>\<checkmark>4 u\<rceil> = \<diamond> \<Longrightarrow> r \<otimes>\<checkmark>1 s = \<diamond> \<or> \<lceil>r \<otimes>\<checkmark>1 s\<rceil> \<otimes>\<checkmark>2 u = \<diamond>\<close>
    and tick_assoc_ren_hyp :
    \<open>r \<otimes>\<checkmark>1 s = \<lfloor>t\<rfloor> \<Longrightarrow> t \<otimes>\<checkmark>2 u = \<lfloor>v\<rfloor> \<Longrightarrow> \<lceil>r \<otimes>\<checkmark>3 \<lceil>s \<otimes>\<checkmark>4 u\<rceil>\<rceil> = \<otimes>\<checkmark>2\<Rightarrow>\<otimes>\<checkmark>3 v\<close>
    and tick_assoc_ren_conv_hyp :
    \<open>s \<otimes>\<checkmark>4 u = \<lfloor>w\<rfloor> \<Longrightarrow> r \<otimes>\<checkmark>3 w = \<lfloor>x\<rfloor> \<Longrightarrow> \<lceil>\<lceil>r \<otimes>\<checkmark>1 s\<rceil> \<otimes>\<checkmark>2 u\<rceil> = \<otimes>\<checkmark>3\<Rightarrow>\<otimes>\<checkmark>2 x\<close>
begin


text \<open>There is a symmetry over the variables.\<close>

sublocale Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_locale_sym :
  Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_locale \<open>\<lambda>u s. s \<otimes>\<checkmark>4 u\<close> \<open>\<lambda>w r. r \<otimes>\<checkmark>3 w\<close> \<open>\<lambda>u t. t \<otimes>\<checkmark>2 u\<close>
  \<open>\<lambda>s r. r \<otimes>\<checkmark>1 s\<close> \<open>\<otimes>\<checkmark>3\<Rightarrow>\<otimes>\<checkmark>2\<close> \<open>\<otimes>\<checkmark>2\<Rightarrow>\<otimes>\<checkmark>3\<close>
  by unfold_locales
    (fact None_assms_tick_join tick_assoc_ren_hyp tick_assoc_ren_conv_hyp)+

end


subsection \<open>First Properties\<close>

lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_locale) tick_assoc_ren_tick_assoc_ren_conv :
  \<open>\<exists>r s u w. s \<otimes>\<checkmark>4 u = \<lfloor>w\<rfloor> \<and> r \<otimes>\<checkmark>3 w = \<lfloor>x\<rfloor> \<Longrightarrow>
   \<otimes>\<checkmark>2\<Rightarrow>\<otimes>\<checkmark>3 (\<otimes>\<checkmark>3\<Rightarrow>\<otimes>\<checkmark>2 x) = x\<close>
  by (metis None_assms_tick_join(1,2) option.collapse option.distinct(1)
      option.sel tick_assoc_ren_hyp tick_assoc_ren_conv_hyp)

lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_locale) tick_assoc_ren_conv_tick_assoc_ren :
  \<open>\<exists>r s t u. r \<otimes>\<checkmark>1 s = \<lfloor>t\<rfloor> \<and> t \<otimes>\<checkmark>2 u = \<lfloor>v\<rfloor> \<Longrightarrow> \<otimes>\<checkmark>3\<Rightarrow>\<otimes>\<checkmark>2 (\<otimes>\<checkmark>2\<Rightarrow>\<otimes>\<checkmark>3 v) = v\<close>
  by (metis Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_locale_sym.tick_assoc_ren_tick_assoc_ren_conv)

lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_locale) inj_on_tick_assoc_ren :
  \<open>inj_on \<otimes>\<checkmark>2\<Rightarrow>\<otimes>\<checkmark>3 {v. \<exists>r s t u. r \<otimes>\<checkmark>1 s = \<lfloor>t\<rfloor> \<and> t \<otimes>\<checkmark>2 u = \<lfloor>v\<rfloor>}\<close>
  by (rule inj_onI, simp) (metis tick_assoc_ren_conv_tick_assoc_ren)

lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_locale) inj_on_tick_assoc_ren_conv :
  \<open>inj_on \<otimes>\<checkmark>3\<Rightarrow>\<otimes>\<checkmark>2 {x. \<exists>r s u w. s \<otimes>\<checkmark>4 u = \<lfloor>w\<rfloor> \<and> r \<otimes>\<checkmark>3 w = \<lfloor>x\<rfloor>}\<close>
  by (rule inj_onI, simp) (metis tick_assoc_ren_tick_assoc_ren_conv)



subsection \<open>Associativity for the Traces\<close>

lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_locale) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_left : 
  \<open>\<lbrakk>t\<^sub>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>1)\<^esub> ((t\<^sub>r, t\<^sub>s), A);
    t\<^sub>v setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>2)\<^esub> ((t\<^sub>t, t\<^sub>u), A)\<rbrakk> \<Longrightarrow>
    \<exists>t\<^sub>w. map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id \<otimes>\<checkmark>2\<Rightarrow>\<otimes>\<checkmark>3) t\<^sub>v setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t\<^sub>r, t\<^sub>w), A) \<and>
         t\<^sub>w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t\<^sub>s, t\<^sub>u), A)\<close>
proof -
  let ?map = \<open>\<lambda>t. map ev (map of_ev t)\<close>
  let ?map_event = \<open>\<lambda>t. map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id \<otimes>\<checkmark>2\<Rightarrow>\<otimes>\<checkmark>3) t\<close>
  show \<open>\<lbrakk>t\<^sub>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>1)\<^esub> ((t\<^sub>r, t\<^sub>s), A);
         t\<^sub>v setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>2)\<^esub> ((t\<^sub>t, t\<^sub>u), A)\<rbrakk> \<Longrightarrow> ?thesis\<close>
  proof (induct \<open>((\<otimes>\<checkmark>2), t\<^sub>t, A, t\<^sub>u)\<close> arbitrary: t\<^sub>r t\<^sub>s t\<^sub>t t\<^sub>u t\<^sub>v)
    case Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil
    thus ?case
      by (cases t\<^sub>r; cases t\<^sub>s)
        (auto intro: Nil_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k simp add: setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps
          split: if_split_asm event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split_asm option.split_asm)
  next
    case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil a t\<^sub>t)
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil.prems(2)
    have \<open>a \<notin> A\<close> \<open>tF t\<^sub>t\<close> \<open>set t\<^sub>t \<inter> ev ` A = {}\<close> \<open>t\<^sub>v = ?map (ev a # t\<^sub>t)\<close>
      and $ : \<open>?map t\<^sub>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>2)\<^esub> ((t\<^sub>t, []), A)\<close>
      by (auto simp add: setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_NilR_iff split: if_split_asm)
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil.prems(1)
    consider (mv_left) t\<^sub>r' where \<open>t\<^sub>r = ev a # t\<^sub>r'\<close> \<open>t\<^sub>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>1)\<^esub> ((t\<^sub>r', t\<^sub>s), A)\<close>
      | (mv_right) t\<^sub>s' where \<open>t\<^sub>s = ev a # t\<^sub>s'\<close> \<open>t\<^sub>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>1)\<^esub> ((t\<^sub>r, t\<^sub>s'), A)\<close>
      by (auto simp add: \<open>a \<notin> A\<close> elim: Cons_ev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
    thus ?case
    proof cases
      case mv_left
      from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil.hyps[OF \<open>a \<notin> A\<close> mv_left(2) "$"]
      obtain t\<^sub>w where * : \<open>?map_event (?map t\<^sub>t) setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub>((t\<^sub>r', t\<^sub>w), A)\<close>
        \<open>t\<^sub>w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t\<^sub>s, []), A)\<close> by blast
      from "*"(1) have \<open>?map_event t\<^sub>v setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t\<^sub>r, t\<^sub>w), A)\<close>
        by (cases t\<^sub>w, auto simp add: mv_left(1) \<open>a \<notin> A\<close> \<open>t\<^sub>v = ?map (ev a # t\<^sub>t)\<close>
            setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
      with "*"(2) show ?thesis by blast
    next
      case mv_right
      from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil.hyps[OF \<open>a \<notin> A\<close> mv_right(2) "$"]
      obtain t\<^sub>w where * : \<open>?map_event (?map t\<^sub>t) setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t\<^sub>r, t\<^sub>w), A)\<close>
        \<open>t\<^sub>w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t\<^sub>s', []), A)\<close> by blast
      from "*"(2) have \<open>ev a # t\<^sub>w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t\<^sub>s, []), A)\<close>
        by (simp add: \<open>a \<notin> A\<close> \<open>t\<^sub>v = ?map (ev a # t\<^sub>t)\<close> mv_right(1))
      moreover from "*"(1) 
      have \<open>?map_event t\<^sub>v setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t\<^sub>r, ev a # t\<^sub>w), A)\<close>
        by (cases t\<^sub>r, auto simp add: \<open>a \<notin> A\<close> \<open>t\<^sub>v = ?map (ev a # t\<^sub>t)\<close> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps
            split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
      ultimately show ?thesis by blast
    qed
  next
    case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil r t\<^sub>t)
    from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_Nil.prems(2) have False by simp
    thus ?case ..
  next
    case (Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev b t\<^sub>u)
    from Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(1)[THEN setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_imp_lengthLR_le]
    have \<open>t\<^sub>r = []\<close> \<open>t\<^sub>s = []\<close> by simp_all
    from Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(2)
    have \<open>b \<notin> A\<close> \<open>tF t\<^sub>u\<close> \<open>set t\<^sub>u \<inter> ev ` A = {}\<close> \<open>t\<^sub>v = ?map (ev b # t\<^sub>u)\<close>
      and $ : \<open>?map t\<^sub>u setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>2)\<^esub> (([], t\<^sub>u), A)\<close>
      by (auto simp add: setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_NilL_iff split: if_split_asm)
    from Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps[OF \<open>b \<notin> A\<close> Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(1) "$"]
    obtain t\<^sub>w where \<open>?map_event (?map t\<^sub>u) setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t\<^sub>r, t\<^sub>w), A)\<close>
      \<open>t\<^sub>w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t\<^sub>s, t\<^sub>u), A)\<close> by blast
    hence \<open>?map_event t\<^sub>v setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t\<^sub>r, ev b # t\<^sub>w), A) \<and>
          ev b # t\<^sub>w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t\<^sub>s, ev b # t\<^sub>u), A)\<close>
      by (simp add: \<open>t\<^sub>v = ?map (ev b # t\<^sub>u)\<close> \<open>t\<^sub>r = []\<close> \<open>t\<^sub>s = []\<close> \<open>b \<notin> A\<close>)
    thus ?case ..
  next
    case (Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick r\<^sub>u t\<^sub>u)
    from Nil_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems(2) have False by simp
    thus ?case ..
  next
    case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev a t\<^sub>t b t\<^sub>u)
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(2)
    consider (mv_both) t\<^sub>v' where \<open>a \<in> A\<close> \<open>b \<in> A\<close> \<open>a = b\<close> \<open>t\<^sub>v = ev b # t\<^sub>v'\<close> \<open>t\<^sub>v' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>2)\<^esub> ((t\<^sub>t, t\<^sub>u), A)\<close>
      |      (mvR_inL) t\<^sub>v' where \<open>a \<in> A\<close> \<open>b \<notin> A\<close> \<open>t\<^sub>v = ev b # t\<^sub>v'\<close> \<open>t\<^sub>v' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>2)\<^esub> ((ev a # t\<^sub>t, t\<^sub>u), A)\<close>
      |      (mvL_inR) t\<^sub>v' where \<open>a \<notin> A\<close> \<open>b \<in> A\<close> \<open>t\<^sub>v = ev a # t\<^sub>v'\<close> \<open>t\<^sub>v' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>2)\<^esub> ((t\<^sub>t, ev b # t\<^sub>u), A)\<close>
      |      (mvR_notin) t\<^sub>v' where \<open>a \<notin> A\<close> \<open>b \<notin> A\<close> \<open>t\<^sub>v = ev b # t\<^sub>v'\<close> \<open>t\<^sub>v' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>2)\<^esub> ((ev a # t\<^sub>t, t\<^sub>u), A)\<close>
      |      (mvL_notin) t\<^sub>v' where \<open>a \<notin> A\<close> \<open>b \<notin> A\<close> \<open>t\<^sub>v = ev a # t\<^sub>v'\<close> \<open>t\<^sub>v' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>2)\<^esub> ((t\<^sub>t, ev b # t\<^sub>u), A)\<close>
      by (auto split: if_split_asm)
    thus ?case
    proof cases
      case mv_both
      from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(1)
      obtain t\<^sub>r' t\<^sub>s' where \<open>t\<^sub>r = ev a # t\<^sub>r'\<close> \<open>t\<^sub>s = ev a # t\<^sub>s'\<close>
        \<open>t\<^sub>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>1)\<^esub> ((t\<^sub>r', t\<^sub>s'), A)\<close>
        by (auto simp add: \<open>a \<in> A\<close> elim: Cons_ev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
      from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(1)[OF mv_both(1-3) \<open>t\<^sub>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>1)\<^esub> ((t\<^sub>r', t\<^sub>s'), A)\<close> mv_both(5)]
      obtain t\<^sub>w where \<open>?map_event t\<^sub>v' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t\<^sub>r', t\<^sub>w), A)\<close>
        \<open>t\<^sub>w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t\<^sub>s', t\<^sub>u), A)\<close> by blast
      hence \<open>?map_event t\<^sub>v setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t\<^sub>r, ev a # t\<^sub>w), A) \<and>
           ev a # t\<^sub>w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t\<^sub>s, ev b # t\<^sub>u), A)\<close>
        by (simp add: mv_both(2-4) \<open>t\<^sub>s = ev a # t\<^sub>s'\<close> \<open>t\<^sub>r = ev a # t\<^sub>r'\<close>)
      thus ?thesis ..
    next
      case mvR_inL
      from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(1)
      obtain t\<^sub>r' t\<^sub>s' where \<open>t\<^sub>r = ev a # t\<^sub>r'\<close> \<open>t\<^sub>s = ev a # t\<^sub>s'\<close>
        \<open>t\<^sub>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>1)\<^esub> ((t\<^sub>r', t\<^sub>s'), A)\<close>
        by (auto simp add: \<open>a \<in> A\<close> elim: Cons_ev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
      from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(2)[OF mvR_inL(1, 2) ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(1) mvR_inL(4)]
      obtain t\<^sub>w where \<open>?map_event t\<^sub>v' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t\<^sub>r, t\<^sub>w), A)\<close>
        \<open>t\<^sub>w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t\<^sub>s, t\<^sub>u), A)\<close> by blast
      hence \<open>?map_event t\<^sub>v setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t\<^sub>r, ev b # t\<^sub>w), A) \<and>
           ev b # t\<^sub>w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t\<^sub>s, ev b # t\<^sub>u), A)\<close>
        by (simp add: \<open>t\<^sub>r = ev a # t\<^sub>r'\<close> \<open>t\<^sub>s = ev a # t\<^sub>s'\<close> mvR_inL(1-3))
      thus ?thesis ..
    next
      case mvL_inR
      from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(1)
      consider (mv_left) t\<^sub>r' where \<open>t\<^sub>r = ev a # t\<^sub>r'\<close> \<open>t\<^sub>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>1)\<^esub> ((t\<^sub>r', t\<^sub>s), A)\<close>
        | (mv_right) t\<^sub>s' where \<open>t\<^sub>s = ev a # t\<^sub>s'\<close> \<open>t\<^sub>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>1)\<^esub> ((t\<^sub>r, t\<^sub>s'), A)\<close>
        by (auto simp add: \<open>a \<notin> A\<close> elim: Cons_ev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
      thus ?thesis
      proof cases
        case mv_left
        from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(3)[OF mvL_inR(1, 2) mv_left(2) mvL_inR(4)]
        obtain t\<^sub>w where \<open>?map_event t\<^sub>v' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t\<^sub>r', t\<^sub>w), A)\<close>
          \<open>t\<^sub>w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t\<^sub>s, ev b # t\<^sub>u), A)\<close> by blast
        hence \<open>?map_event t\<^sub>v setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t\<^sub>r, t\<^sub>w), A) \<and>
             t\<^sub>w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t\<^sub>s, ev b # t\<^sub>u), A)\<close>
          by (cases t\<^sub>w) (auto simp add: mvL_inR(1-3) mv_left(1)
              setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
        thus ?thesis ..
      next
        case mv_right
        from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(3)[OF mvL_inR(1, 2) mv_right(2) mvL_inR(4)]
        obtain t\<^sub>w where \<open>?map_event t\<^sub>v' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t\<^sub>r, t\<^sub>w), A)\<close>
          \<open>t\<^sub>w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t\<^sub>s', ev b # t\<^sub>u), A)\<close> by blast
        hence \<open>?map_event t\<^sub>v setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t\<^sub>r, ev a # t\<^sub>w), A) \<and>
             ev a # t\<^sub>w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t\<^sub>s, ev b # t\<^sub>u), A)\<close>
          by (cases t\<^sub>r) (auto simp add: mvL_inR(1-3) mv_right(1)
              setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
        thus ?thesis ..
      qed
    next
      case mvR_notin
      from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(1)
      consider (mv_left) t\<^sub>r' where \<open>t\<^sub>r = ev a # t\<^sub>r'\<close> \<open>t\<^sub>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>1)\<^esub> ((t\<^sub>r', t\<^sub>s), A)\<close>
        | (mv_right) t\<^sub>s' where \<open>t\<^sub>s = ev a # t\<^sub>s'\<close> \<open>t\<^sub>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>1)\<^esub> ((t\<^sub>r, t\<^sub>s'), A)\<close>
        by (auto simp add: \<open>a \<notin> A\<close> elim: Cons_ev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
      thus ?thesis
      proof cases
        case mv_left
        from mv_left(2) have \<open>ev a # t\<^sub>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>1)\<^esub> ((t\<^sub>r, t\<^sub>s), A)\<close>
          by (cases t\<^sub>s) (auto simp add: mv_left(1) mvR_notin(1)
              setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
        from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(5)[OF mvR_notin(1, 2) this mvR_notin(4)]
        obtain t\<^sub>w where \<open>?map_event t\<^sub>v' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t\<^sub>r, t\<^sub>w), A)\<close>
          \<open>t\<^sub>w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t\<^sub>s, t\<^sub>u), A)\<close> by blast
        hence \<open>?map_event t\<^sub>v setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t\<^sub>r, ev b # t\<^sub>w), A) \<and>
             ev b # t\<^sub>w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t\<^sub>s, ev b # t\<^sub>u), A)\<close>
          by (cases t\<^sub>s) (auto simp add: mvR_notin(1-3) mv_left(1)
              setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
        thus ?thesis ..
      next
        case mv_right
        from mv_right(2) have \<open>ev a # t\<^sub>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>1)\<^esub> ((t\<^sub>r, t\<^sub>s), A)\<close>
          by (cases t\<^sub>r) (auto simp add: mv_right(1) mvR_notin(1)
              setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
        from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(5)[OF mvR_notin(1, 2) this mvR_notin(4)]
        obtain t\<^sub>w where \<open>?map_event t\<^sub>v' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t\<^sub>r, t\<^sub>w), A)\<close>
          \<open>t\<^sub>w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t\<^sub>s, t\<^sub>u), A)\<close> by blast
        hence \<open>?map_event t\<^sub>v setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t\<^sub>r, ev b # t\<^sub>w), A) \<and>
             ev b # t\<^sub>w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t\<^sub>s, ev b # t\<^sub>u), A)\<close>
          by (cases t\<^sub>r) (auto simp add: mvR_notin(1-3) mv_right(1)
              setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
        thus ?thesis ..
      qed
    next
      case mvL_notin
      from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(1)
      consider (mv_left) t\<^sub>r' where \<open>t\<^sub>r = ev a # t\<^sub>r'\<close> \<open>t\<^sub>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>1)\<^esub> ((t\<^sub>r', t\<^sub>s), A)\<close>
        | (mv_right) t\<^sub>s' where \<open>t\<^sub>s = ev a # t\<^sub>s'\<close> \<open>t\<^sub>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>1)\<^esub> ((t\<^sub>r, t\<^sub>s'), A)\<close>
        by (auto simp add: \<open>a \<notin> A\<close> elim: Cons_ev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
      thus ?thesis
      proof cases
        case mv_left
        from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(4)[OF mvL_notin(1, 2) mv_left(2) mvL_notin(4)]
        obtain t\<^sub>w where \<open>?map_event t\<^sub>v' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t\<^sub>r', t\<^sub>w), A)\<close>
          \<open>t\<^sub>w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t\<^sub>s, ev b # t\<^sub>u), A)\<close> by blast
        hence \<open>?map_event t\<^sub>v setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t\<^sub>r, t\<^sub>w), A) \<and>
             t\<^sub>w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t\<^sub>s, ev b # t\<^sub>u), A)\<close>
          by (cases t\<^sub>w) (auto simp add: mv_left(1) mvL_notin(1, 3)
              setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
        thus ?thesis ..
      next
        case mv_right
        from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps(4)[OF mvL_notin(1, 2) mv_right(2) mvL_notin(4)]
        obtain t\<^sub>w where \<open>?map_event t\<^sub>v' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t\<^sub>r, t\<^sub>w), A)\<close>
          \<open>t\<^sub>w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t\<^sub>s', ev b # t\<^sub>u), A)\<close> by blast
        hence \<open>?map_event t\<^sub>v setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t\<^sub>r, ev a # t\<^sub>w), A) \<and>
             ev a # t\<^sub>w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t\<^sub>s, ev b # t\<^sub>u), A)\<close>
          by (cases t\<^sub>r) (auto simp add: mv_right(1) mvL_notin(1, 3)
              setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
        thus ?thesis ..
      qed
    qed
  next
    case (ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick a t\<^sub>t s t\<^sub>u)
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems(2) obtain t\<^sub>v'
      where \<open>a \<notin> A\<close> \<open>t\<^sub>v = ev a # t\<^sub>v'\<close>
        and $ : \<open>t\<^sub>v' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>2)\<^esub> ((t\<^sub>t, \<checkmark>(s) # t\<^sub>u), A)\<close>
      by (auto split: if_split_asm)
    from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems(1)
    have \<open>t\<^sub>r \<noteq> [] \<and> hd t\<^sub>r = ev a \<and> t\<^sub>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>1)\<^esub> ((tl t\<^sub>r, t\<^sub>s), A) \<or>
        t\<^sub>s \<noteq> [] \<and> hd t\<^sub>s = ev a \<and> t\<^sub>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>1)\<^esub> ((t\<^sub>r, tl t\<^sub>s), A)\<close>
      by (auto simp add: \<open>a \<notin> A\<close> elim: Cons_ev_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
    thus ?case
    proof (elim disjE conjE)
      assume \<open>t\<^sub>r \<noteq> []\<close> \<open>hd t\<^sub>r = ev a\<close> \<open>t\<^sub>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>1)\<^esub> ((tl t\<^sub>r, t\<^sub>s), A)\<close>
      from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.hyps[OF \<open>a \<notin> A\<close> this(3) "$"]
      obtain t\<^sub>w where * : \<open>?map_event t\<^sub>v' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub>((tl t\<^sub>r, t\<^sub>w), A)\<close>
        \<open>t\<^sub>w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t\<^sub>s, \<checkmark>(s) # t\<^sub>u), A)\<close> by blast
      from "*"(1) have \<open>?map_event t\<^sub>v setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t\<^sub>r, t\<^sub>w), A)\<close>
        by (subst list.collapse[OF \<open>t\<^sub>r \<noteq> []\<close>, symmetric])
          (cases t\<^sub>w, auto simp add: \<open>a \<notin> A\<close> \<open>hd t\<^sub>r = ev a\<close> \<open>t\<^sub>v = ev a # t\<^sub>v'\<close>
            setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
      with "*"(2) show ?case by blast
    next
      assume \<open>t\<^sub>s \<noteq> []\<close> \<open>hd t\<^sub>s = ev a\<close> \<open>t\<^sub>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>1)\<^esub> ((t\<^sub>r, tl t\<^sub>s), A)\<close>
      from ev_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.hyps[OF \<open>a \<notin> A\<close> this(3) "$"]
      obtain t\<^sub>w where * : \<open>?map_event t\<^sub>v' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t\<^sub>r, t\<^sub>w), A)\<close>
        \<open>t\<^sub>w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((tl t\<^sub>s, \<checkmark>(s) # t\<^sub>u), A)\<close> by blast
      from "*"(2) have \<open>ev a # t\<^sub>w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t\<^sub>s, \<checkmark>(s) # t\<^sub>u), A)\<close>
        by (subst list.collapse[OF \<open>t\<^sub>s \<noteq> []\<close>, symmetric])
          (simp add: \<open>a \<notin> A\<close> \<open>t\<^sub>v = ev a # t\<^sub>v'\<close> \<open>hd t\<^sub>s = ev a\<close>)
      moreover from "*"(1)
      have \<open>?map_event t\<^sub>v setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t\<^sub>r, ev a # t\<^sub>w), A)\<close>
        by (cases t\<^sub>r, auto simp add: \<open>a \<notin> A\<close> \<open>t\<^sub>v = ev a # t\<^sub>v'\<close> setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_simps
            split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split)
      ultimately show ?case by blast
    qed
  next
    case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev r\<^sub>t t\<^sub>t b t\<^sub>u)
    from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(1)
    obtain r\<^sub>r r\<^sub>s t\<^sub>r' t\<^sub>s' where \<open>(r\<^sub>r \<otimes>\<checkmark>1 r\<^sub>s) = \<lfloor>r\<^sub>t\<rfloor>\<close> \<open>t\<^sub>r = \<checkmark>(r\<^sub>r) # t\<^sub>r'\<close> \<open>t\<^sub>s = \<checkmark>(r\<^sub>s) # t\<^sub>s'\<close>
      by (auto elim: Cons_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
    from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(2) obtain t\<^sub>v'
      where \<open>b \<notin> A\<close> \<open>t\<^sub>v = ev b # t\<^sub>v'\<close>
        and $ : \<open>t\<^sub>v' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>2)\<^esub> ((\<checkmark>(r\<^sub>t) # t\<^sub>t, t\<^sub>u), A)\<close>
      by (auto split: if_split_asm)
    from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.hyps[OF \<open>b \<notin> A\<close> tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_ev.prems(1) "$"]
    obtain t\<^sub>w where \<open>?map_event t\<^sub>v' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t\<^sub>r, t\<^sub>w), A)\<close>
      \<open>t\<^sub>w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t\<^sub>s, t\<^sub>u), A)\<close> by blast
    hence \<open>?map_event t\<^sub>v setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t\<^sub>r, ev b # t\<^sub>w), A) \<and>
         ev b # t\<^sub>w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t\<^sub>s, ev b # t\<^sub>u), A)\<close>
      by (simp add: \<open>b \<notin> A\<close> \<open>t\<^sub>v = ev b # t\<^sub>v'\<close> \<open>t\<^sub>r = \<checkmark>(r\<^sub>r) # t\<^sub>r'\<close> \<open>t\<^sub>s = \<checkmark>(r\<^sub>s) # t\<^sub>s'\<close>)
    thus ?case ..
  next
    case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick r\<^sub>t t\<^sub>t r\<^sub>u t\<^sub>u)
    from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems(1)
    obtain r\<^sub>r r\<^sub>s t\<^sub>r' t\<^sub>s' where \<open>r\<^sub>r \<otimes>\<checkmark>1 r\<^sub>s = \<lfloor>r\<^sub>t\<rfloor>\<close> \<open>t\<^sub>r = \<checkmark>(r\<^sub>r) # t\<^sub>r'\<close> \<open>t\<^sub>s = \<checkmark>(r\<^sub>s) # t\<^sub>s'\<close>
      \<open>t\<^sub>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>1)\<^esub> ((t\<^sub>r', t\<^sub>s'), A)\<close>
      by (auto elim: Cons_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
    from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems(2)
    obtain r\<^sub>v t\<^sub>v' where \<open>r\<^sub>t \<otimes>\<checkmark>2 r\<^sub>u = \<lfloor>r\<^sub>v\<rfloor>\<close> \<open>t\<^sub>v = \<checkmark>(r\<^sub>v) # t\<^sub>v'\<close>
      \<open>t\<^sub>v' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>2)\<^esub> ((t\<^sub>t, t\<^sub>u), A)\<close>
      by (auto split: option.split_asm)
    from \<open>r\<^sub>r \<otimes>\<checkmark>1 r\<^sub>s = \<lfloor>r\<^sub>t\<rfloor>\<close> \<open>r\<^sub>t \<otimes>\<checkmark>2 r\<^sub>u = \<lfloor>r\<^sub>v\<rfloor>\<close> obtain r\<^sub>w where \<open>r\<^sub>s \<otimes>\<checkmark>4 r\<^sub>u = \<lfloor>r\<^sub>w\<rfloor>\<close>
      by (metis None_assms_tick_join(3) not_None_eq option.sel)
    from \<open>r\<^sub>s \<otimes>\<checkmark>4 r\<^sub>u = \<lfloor>r\<^sub>w\<rfloor>\<close> \<open>r\<^sub>r \<otimes>\<checkmark>1 r\<^sub>s = \<lfloor>r\<^sub>t\<rfloor>\<close> \<open>r\<^sub>t \<otimes>\<checkmark>2 r\<^sub>u = \<lfloor>r\<^sub>v\<rfloor>\<close>
    obtain r\<^sub>x where \<open>r\<^sub>r \<otimes>\<checkmark>3 r\<^sub>w = \<lfloor>r\<^sub>x\<rfloor>\<close>
      by (metis None_assms_tick_join(4) option.distinct(1) option.exhaust_sel option.sel)
    have \<open>\<otimes>\<checkmark>2\<Rightarrow>\<otimes>\<checkmark>3 r\<^sub>v = r\<^sub>x\<close>
      by (metis \<open>r\<^sub>r \<otimes>\<checkmark>1 r\<^sub>s = \<lfloor>r\<^sub>t\<rfloor>\<close> \<open>r\<^sub>r \<otimes>\<checkmark>3 r\<^sub>w = \<lfloor>r\<^sub>x\<rfloor>\<close> \<open>r\<^sub>s \<otimes>\<checkmark>4 r\<^sub>u = \<lfloor>r\<^sub>w\<rfloor>\<close>
          \<open>r\<^sub>t \<otimes>\<checkmark>2 r\<^sub>u = \<lfloor>r\<^sub>v\<rfloor>\<close> tick_assoc_ren_hyp option.sel)
    from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.hyps
      [OF \<open>r\<^sub>t \<otimes>\<checkmark>2 r\<^sub>u = \<lfloor>r\<^sub>v\<rfloor>\<close> \<open>t\<^sub>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>1)\<^esub> ((t\<^sub>r', t\<^sub>s'), A)\<close>
        \<open>t\<^sub>v' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>2)\<^esub> ((t\<^sub>t, t\<^sub>u), A)\<close>]
    obtain t\<^sub>w where \<open>?map_event t\<^sub>v' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t\<^sub>r', t\<^sub>w), A)\<close>
      \<open>t\<^sub>w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t\<^sub>s', t\<^sub>u), A)\<close> by blast
    hence \<open>?map_event t\<^sub>v setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t\<^sub>r, \<checkmark>(r\<^sub>w) # t\<^sub>w), A) \<and>
          \<checkmark>(r\<^sub>w) # t\<^sub>w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t\<^sub>s, \<checkmark>(r\<^sub>u) # t\<^sub>u), A)\<close>
      by (simp add: \<open>t\<^sub>r = \<checkmark>(r\<^sub>r) # t\<^sub>r'\<close> \<open>t\<^sub>s = \<checkmark>(r\<^sub>s) # t\<^sub>s'\<close> \<open>t\<^sub>v = \<checkmark>(r\<^sub>v) # t\<^sub>v'\<close>
          \<open>r\<^sub>s \<otimes>\<checkmark>4 r\<^sub>u = \<lfloor>r\<^sub>w\<rfloor>\<close> \<open>r\<^sub>r \<otimes>\<checkmark>3 r\<^sub>w = \<lfloor>r\<^sub>x\<rfloor>\<close> \<open>\<otimes>\<checkmark>2\<Rightarrow>\<otimes>\<checkmark>3 r\<^sub>v = r\<^sub>x\<close>)
    thus ?case ..
  qed
qed



lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_locale) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_right :
  \<open>t\<^sub>w setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t\<^sub>s, t\<^sub>u), A) \<Longrightarrow>
   t\<^sub>x setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t\<^sub>r, t\<^sub>w), A) \<Longrightarrow>
   \<exists>t\<^sub>t. map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id \<otimes>\<checkmark>3\<Rightarrow>\<otimes>\<checkmark>2) t\<^sub>x setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>2)\<^esub> ((t\<^sub>t, t\<^sub>u), A) \<and>
        t\<^sub>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>1)\<^esub> ((t\<^sub>r, t\<^sub>s), A)\<close>
  by (subst (1 2) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym, subst (asm) (1 2) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym)
    (fact Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_locale_sym.setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_left)



subsection \<open>Associativity\<close>

context Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_locale
begin

notation Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>1.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<open>(_ \<lbrakk>_\<rbrakk>\<^sub>\<checkmark>\<^sub>1 _)\<close> [70, 0, 71] 70)
notation Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>2.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<open>(_ \<lbrakk>_\<rbrakk>\<^sub>\<checkmark>\<^sub>2 _)\<close> [70, 0, 71] 70)
notation Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>3.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<open>(_ \<lbrakk>_\<rbrakk>\<^sub>\<checkmark>\<^sub>3 _)\<close> [70, 0, 71] 70)
notation Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>4.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<open>(_ \<lbrakk>_\<rbrakk>\<^sub>\<checkmark>\<^sub>4 _)\<close> [70, 0, 71] 70)


lemma Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_oneside :
  \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>3 (Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>4 R) \<sqsubseteq>\<^sub>F\<^sub>D RenamingTick (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>1 Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>2 R) \<otimes>\<checkmark>2\<Rightarrow>\<otimes>\<checkmark>3\<close> (is \<open>?lhs \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close>)
proof -
  let ?map_event = \<open>\<lambda>t. map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id \<otimes>\<checkmark>2\<Rightarrow>\<otimes>\<checkmark>3) t\<close>
  let ?map_event_conv = \<open>\<lambda>t. map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id \<otimes>\<checkmark>3\<Rightarrow>\<otimes>\<checkmark>2) t\<close>
  show \<open>?lhs \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close>
  proof (rule failure_divergence_refine_optimizedI)
    fix t assume \<open>t \<in> \<D> ?rhs\<close>
    then obtain t\<^sub>1 t\<^sub>2 where \<open>t = ?map_event t\<^sub>1 @ t\<^sub>2\<close>
      \<open>tF t\<^sub>1\<close> \<open>ftF t\<^sub>2\<close> \<open>t\<^sub>1 \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>1 Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>2 R)\<close>
      unfolding D_Renaming by blast
    from \<open>t\<^sub>1 \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>1 Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>2 R)\<close> obtain t\<^sub>1\<^sub>1 t\<^sub>1\<^sub>2 t_P_Q t_R
      where * : \<open>t\<^sub>1 = t\<^sub>1\<^sub>1 @ t\<^sub>1\<^sub>2\<close> \<open>tF t\<^sub>1\<^sub>1\<close> \<open>ftF t\<^sub>1\<^sub>2\<close>
        \<open>t\<^sub>1\<^sub>1 setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>2)\<^esub> ((t_P_Q, t_R), S)\<close>
        \<open>t_P_Q \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>1 Q) \<and> t_R \<in> \<T> R \<or>
         t_P_Q \<in> \<T> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>1 Q) \<and> t_P_Q \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>1 Q) \<and> t_R \<in> \<D> R\<close>
      unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>2.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k using D_T by blast
    from "*"(5) show \<open>t \<in> \<D> ?lhs\<close>
    proof (elim disjE conjE)
      assume \<open>t_P_Q \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>1 Q)\<close> \<open>t_R \<in> \<T> R\<close>
      from \<open>t_P_Q \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>1 Q)\<close> obtain t_P_Q\<^sub>1 t_P_Q\<^sub>2 t_P t_Q
        where ** : \<open>t_P_Q = t_P_Q\<^sub>1 @ t_P_Q\<^sub>2\<close> \<open>tF t_P_Q\<^sub>1\<close> \<open>ftF t_P_Q\<^sub>2\<close>
          \<open>t_P_Q\<^sub>1 setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>1)\<^esub> ((t_P, t_Q), S)\<close>
          \<open>t_P \<in> \<D> P \<and> t_Q \<in> \<T> Q \<or> t_P \<in> \<T> P \<and> t_Q \<in> \<D> Q\<close>
        unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>1.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
      from "*"(4)[unfolded "**"(1), THEN setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_appendL]
      obtain t\<^sub>1\<^sub>1\<^sub>1 t\<^sub>1\<^sub>1\<^sub>2 t_R\<^sub>1 t_R\<^sub>2
        where *** : \<open>t\<^sub>1\<^sub>1 = t\<^sub>1\<^sub>1\<^sub>1 @ t\<^sub>1\<^sub>1\<^sub>2\<close> \<open>t_R = t_R\<^sub>1 @ t_R\<^sub>2\<close>
          \<open>t\<^sub>1\<^sub>1\<^sub>1 setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>2)\<^esub> ((t_P_Q\<^sub>1, t_R\<^sub>1), S)\<close>
          \<open>t\<^sub>1\<^sub>1\<^sub>2 setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>2)\<^esub> ((t_P_Q\<^sub>2, t_R\<^sub>2), S)\<close> by blast
      from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_left[OF "**"(4) "***"(3)]
      obtain t_Q_R where **** : \<open>?map_event t\<^sub>1\<^sub>1\<^sub>1 setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t_P, t_Q_R), S)\<close>
        \<open>t_Q_R setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t_Q, t_R\<^sub>1), S)\<close> by blast
      have \<open>tF (?map_event t\<^sub>1)\<close>
        by (simp add: \<open>tF t\<^sub>1\<close> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree)
      moreover have \<open>ftF (?map_event (t\<^sub>1\<^sub>1\<^sub>2 @ t\<^sub>1\<^sub>2) @ t\<^sub>2)\<close>
        by (metis "*"(1) "***"(1) \<open>ftF t\<^sub>2\<close> \<open>tF t\<^sub>1\<close> front_tickFree_append
            map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree tickFree_append_iff)
      moreover from "**"(5)
      have \<open>t_P \<in> \<D> P \<and> t_Q_R \<in> \<T> (Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>4 R) \<or> t_P \<in> \<T> P \<and> t_Q_R \<in> \<D> (Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>4 R)\<close>
      proof (elim disjE conjE)
        assume \<open>t_P \<in> \<D> P\<close> \<open>t_Q \<in> \<T> Q\<close>
        hence \<open>t_P \<in> \<D> P \<and> t_Q_R \<in> \<T> (Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>4 R)\<close> 
          by (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>4.T_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
            (metis "****"(2) "***"(2) \<open>t_R \<in> \<T> R\<close> is_processT3_TR_append)
        thus ?thesis ..
      next
        assume \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<D> Q\<close>
        from "**"(2, 4) have \<open>tF t_Q\<close> by (simp add: tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
        with "****"(2) setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree_imp have \<open>tF t_Q_R\<close> by blast
        moreover from "***"(2) \<open>t_R \<in> \<T> R\<close> is_processT3_TR_append have \<open>t_R\<^sub>1 \<in> \<T> R\<close> by blast
        ultimately have \<open>t_P \<in> \<T> P \<and> t_Q_R \<in> \<D> (Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>4 R)\<close>
          unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>4.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
          using "****"(2) \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<D> Q\<close> front_tickFree_Nil by blast
        thus ?thesis ..
      qed
      ultimately show \<open>t \<in> \<D> ?lhs\<close>
        using "****"(1) by (auto simp add: \<open>t = ?map_event t\<^sub>1 @ t\<^sub>2\<close>
            "*"(1) "***"(1) Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>3.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
    next
      assume \<open>t_P_Q \<in> \<T> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>1 Q)\<close> \<open>t_P_Q \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>1 Q)\<close> \<open>t_R \<in> \<D> R\<close>
      from this(1, 2) obtain t_P t_Q
        where ** : \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close> \<open>t_P_Q setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>1)\<^esub> ((t_P, t_Q), S)\<close>
        unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>1.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
      from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_left[OF "**"(3) "*"(4)] obtain t_Q'
        where *** : \<open>?map_event t\<^sub>1\<^sub>1 setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t_P, t_Q'), S)\<close>
          \<open>t_Q' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t_Q, t_R), S)\<close> by blast
      from "*"(2) "**"(2) "***" \<open>t_R \<in> \<D> R\<close> have \<open>t_Q' \<in> \<D> (Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>4 R)\<close>
        by (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>4.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
          (metis append.right_neutral front_tickFree_Nil
            map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
      moreover have \<open>t = ?map_event t\<^sub>1\<^sub>1 @ (?map_event t\<^sub>1\<^sub>2 @ t\<^sub>2)\<close>
        by (simp add: "*"(1) \<open>t = ?map_event t\<^sub>1 @ t\<^sub>2\<close>)
      moreover have \<open>tF (?map_event t\<^sub>1\<^sub>1)\<close>
        by (simp add: "*"(2) map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree)
      moreover from "*"(1) \<open>ftF t\<^sub>2\<close> \<open>tF t\<^sub>1\<close> have \<open>ftF (?map_event t\<^sub>1\<^sub>2 @ t\<^sub>2)\<close>
        using front_tickFree_append map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree tickFree_append_iff by blast
      ultimately show \<open>t \<in> \<D> ?lhs\<close>
        unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>3.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k using "**"(1) "***"(1) by blast
    qed
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?rhs\<close> \<open>\<D> ?rhs \<subseteq> \<D> ?lhs\<close>
    then consider \<open>t \<in> \<D> ?rhs\<close>
      | t\<^sub>1 where \<open>t = ?map_event t\<^sub>1\<close> \<open>t \<notin> \<D> ?rhs\<close>
        \<open>(t\<^sub>1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id \<otimes>\<checkmark>2\<Rightarrow>\<otimes>\<checkmark>3 -` X) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>1 Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>2 R)\<close>
      unfolding Renaming_projs by blast
    thus \<open>(t, X) \<in> \<F> ?lhs\<close>
    proof cases
      assume \<open>t \<in> \<D> ?rhs\<close>
      with \<open>\<D> ?rhs \<subseteq> \<D> ?lhs\<close> have \<open>t \<in> \<D> ?lhs\<close> by blast
      thus \<open>(t, X) \<in> \<F> ?lhs\<close> by (fact is_processT8)
    next
      fix t\<^sub>1 assume * : \<open>t = ?map_event t\<^sub>1\<close> \<open>t \<notin> \<D> ?rhs\<close>
        \<open>(t\<^sub>1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id \<otimes>\<checkmark>2\<Rightarrow>\<otimes>\<checkmark>3 -` X) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>1 Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>2 R)\<close>
      from "*"(1) \<open>t \<notin> \<D> ?rhs\<close> have \<open>t\<^sub>1 \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>1 Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>2 R)\<close>
        by (cases \<open>tF t\<^sub>1\<close>, simp_all add: D_Renaming)
          (use front_tickFree_Nil in blast,
            metis D_imp_front_tickFree front_tickFree_append_iff is_processT9
            map_append map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_front_tickFree
            nonTickFree_n_frontTickFree non_tickFree_tick tickFree_Nil)
      with "*"(3) obtain t_P_Q X_P_Q t_R X_R
        where ** : \<open>(t_P_Q, X_P_Q) \<in> \<F> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>1 Q)\<close> \<open>(t_R, X_R) \<in> \<F> R\<close>
          \<open>t\<^sub>1 setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>2)\<^esub> ((t_P_Q, t_R), S)\<close>
          \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id \<otimes>\<checkmark>2\<Rightarrow>\<otimes>\<checkmark>3 -` X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>2) X_P_Q S X_R\<close>
        unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>2.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
      from "**"(1) consider \<open>t_P_Q \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>1 Q)\<close>
        | (fail) t_P X_P t_Q X_Q where \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
          \<open>t_P_Q setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>1)\<^esub> ((t_P, t_Q), S)\<close>
          \<open>X_P_Q \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>1) X_P S X_Q\<close>
        unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>1.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
      thus \<open>(t, X) \<in> \<F> ?lhs\<close>
      proof cases
        assume \<open>t_P_Q \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>1 Q)\<close>
        have \<open>t\<^sub>1 \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>1 Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>2 R)\<close>
        proof (cases \<open>tF t_P_Q\<close>)
          assume \<open>tF t_P_Q\<close>
          with "**"(3)[THEN setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree_imp[rotated]] have \<open>tF t\<^sub>1\<close> by simp
          with "**"(3) "**"(2)[THEN F_T] \<open>t_P_Q \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>1 Q)\<close>
          show \<open>t\<^sub>1 \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>1 Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>2 R)\<close>
            by (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>2.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
              (meson front_tickFree_Nil self_append_conv)
        next
          assume \<open>\<not> tF t_P_Q\<close>
          then obtain t_P_Q' r where \<open>tF t_P_Q'\<close> \<open>t_P_Q = t_P_Q' @ [\<checkmark>(r)]\<close>
            by (metis D_imp_front_tickFree \<open>t_P_Q \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>1 Q)\<close> butlast_snoc
                front_tickFree_iff_tickFree_butlast nonTickFree_n_frontTickFree)
          moreover from "**"(2,3) \<open>\<not> tF t_P_Q\<close> obtain t_R' s
            where \<open>tF t_R'\<close> \<open>t_R = t_R' @ [\<checkmark>(s)]\<close>
            by (metis  F_imp_front_tickFree butlast_snoc front_tickFree_iff_tickFree_butlast
                nonTickFree_n_frontTickFree setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree_imp)
          ultimately obtain r_s t\<^sub>1' where \<open>t\<^sub>1 = t\<^sub>1' @ [\<checkmark>(r_s)]\<close>
            \<open>t\<^sub>1' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>2)\<^esub> ((t_P_Q', t_R'), S)\<close>
            using "**"(3) by (auto elim!: setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_snoc_tick_snoc_tickE)
          moreover have \<open>t_P_Q' \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>1 Q)\<close>
            by (metis D_imp_front_tickFree \<open>\<not> tF t_P_Q\<close> \<open>t_P_Q = t_P_Q' @ [\<checkmark>(r)]\<close>
                \<open>t_P_Q \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>1 Q)\<close> butlast_snoc div_butlast_when_non_tickFree_iff)
          moreover have \<open>t_R' \<in> \<T> R\<close>
            using "**"(2) F_T \<open>t_R = t_R' @ [\<checkmark>(s)]\<close> is_processT3_TR_append by blast
          ultimately have \<open>t\<^sub>1' \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>1 Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>2 R)\<close>
            by (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>2.D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
              (metis "**"(3) D_imp_front_tickFree \<open>tF t_R'\<close> \<open>t_P_Q \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>1 Q)\<close>
                \<open>t_R = t_R' @ [\<checkmark>(s)]\<close> append.right_neutral butlast_snoc front_tickFree_charn
                front_tickFree_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff tickFree_Nil tickFree_append_iff)
          thus \<open>t\<^sub>1 \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>1 Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>2 R)\<close>
            by (simp add: \<open>t\<^sub>1 = t\<^sub>1' @ [\<checkmark>(r_s)]\<close>)
              (metis "*"(3) F_imp_front_tickFree \<open>t\<^sub>1 = t\<^sub>1' @ [\<checkmark>(r_s)]\<close> butlast_snoc
                div_butlast_when_non_tickFree_iff non_tickFree_tick tickFree_append_iff)
        qed
        with \<open>t\<^sub>1 \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>1 Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>2 R)\<close> show \<open>(t, X) \<in> \<F> ?lhs\<close> ..
      next
        case fail
        from setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_left[OF fail(3) "**"(3)] obtain t_Q'
          where *** : \<open>?map_event t\<^sub>1 setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t_P, t_Q'), S)\<close>
            \<open>t_Q' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>4)\<^esub> ((t_Q, t_R), S)\<close> by blast
        from "**"(2) "***"(2) fail(2)
        have \<open>(t_Q', super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>4) X_Q S X_R) \<in> \<F> (Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>4 R)\<close>
          by (auto simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>4.F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        moreover have \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>3)\<^esub> ((t_P, t_Q'), S)\<close>
          by (simp add: "*"(1) "***"(1))
        have \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>3) X_P S (super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>4) X_Q S X_R)\<close>
        proof (rule subsetI)
          fix e assume \<open>e \<in> X\<close>
          show \<open>e \<in> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>3) X_P S (super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>4) X_Q S X_R)\<close>
          proof (cases e)
            fix a assume \<open>e = ev a\<close>
            obtain a' where \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id \<otimes>\<checkmark>2\<Rightarrow>\<otimes>\<checkmark>3 (ev a') = ev a\<close> by simp
            with \<open>e \<in> X\<close> have \<open>ev a' \<in> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id \<otimes>\<checkmark>2\<Rightarrow>\<otimes>\<checkmark>3 -` X\<close>
              by (simp add: \<open>e = ev a\<close>)
            with **(4)[THEN set_mp, OF this] fail(4)
              \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id \<otimes>\<checkmark>2\<Rightarrow>\<otimes>\<checkmark>3 (ev a') = ev a\<close>
            show \<open>e \<in> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>3) X_P S (super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>4) X_Q S X_R)\<close>
              by (auto simp add: \<open>e = ev a\<close> subset_iff super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
          next
            fix r_s_t assume \<open>e = \<checkmark>(r_s_t)\<close>
            show \<open>e \<in> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>3) X_P S (super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>4) X_Q S X_R)\<close>
            proof (cases \<open>\<exists>r s t s_t. s \<otimes>\<checkmark>4 t = \<lfloor>s_t\<rfloor> \<and> r \<otimes>\<checkmark>3 s_t = \<lfloor>r_s_t\<rfloor>\<close>)
              assume \<open>\<exists>r s t s_t. s \<otimes>\<checkmark>4 t = \<lfloor>s_t\<rfloor> \<and> r \<otimes>\<checkmark>3 s_t = \<lfloor>r_s_t\<rfloor>\<close>
              then obtain r s t s_t
                where $ : \<open>s \<otimes>\<checkmark>4 t = \<lfloor>s_t\<rfloor>\<close> \<open>r \<otimes>\<checkmark>3 s_t = \<lfloor>r_s_t\<rfloor>\<close> by blast
              then obtain r' s' t' r_s'
                where $$ : \<open>r' \<otimes>\<checkmark>1 s' = \<lfloor>r_s'\<rfloor>\<close> \<open>r_s' \<otimes>\<checkmark>2 t' = \<lfloor>\<otimes>\<checkmark>3\<Rightarrow>\<otimes>\<checkmark>2 r_s_t\<rfloor>\<close>
                by (metis None_assms_tick_join(1,2) option.collapse option.discI
                    option.sel tick_assoc_ren_conv_hyp)
              have \<open>\<checkmark>(\<otimes>\<checkmark>3\<Rightarrow>\<otimes>\<checkmark>2 r_s_t) \<in> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id \<otimes>\<checkmark>2\<Rightarrow>\<otimes>\<checkmark>3 -` X\<close>
                by (metis \<open>e = \<checkmark>(r_s_t)\<close> \<open>e \<in> X\<close> "$" event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(10)
                    tick_assoc_ren_tick_assoc_ren_conv vimage_eq)
              from **(4)[THEN set_mp, OF this] fail(4)[THEN set_mp, of \<open>\<checkmark>(r_s')\<close>]
              show \<open>e \<in> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>3) X_P S (super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>4) X_Q S X_R)\<close>
                by (simp add: \<open>e = \<checkmark>(r_s_t)\<close> subset_iff super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def)
                  (metis (no_types, lifting) "$$" None_assms_tick_join(3,4)
                    Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>2.inj_tick_join option.collapse option.discI
                    option.sel tick_assoc_ren_hyp tick_assoc_ren_tick_assoc_ren_conv)
            next
              assume \<open>\<nexists>r s t s_t. s \<otimes>\<checkmark>4 t = \<lfloor>s_t\<rfloor> \<and> r \<otimes>\<checkmark>3 s_t = \<lfloor>r_s_t\<rfloor>\<close>
              thus \<open>e \<in> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>3) X_P S (super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>4) X_Q S X_R)\<close>
                by (simp add: \<open>e = \<checkmark>(r_s_t)\<close> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def) blast
            qed
          qed
        qed
        ultimately show \<open>(t, X) \<in> \<F> ?lhs\<close>
          using "*"(1) "***"(1) fail(1) by (auto simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>3.F_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      qed
    qed
  qed
qed

end



lemma (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) strict_ticks_of_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset :
  \<open>\<^bold>\<checkmark>\<^bold>s(P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q) \<subseteq> {r_s |r_s r s. r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor> \<and>
                                 r \<in> \<^bold>\<checkmark>\<^bold>s(P) \<and> s \<in> \<^bold>\<checkmark>\<^bold>s(Q)}\<close> (is \<open>_ \<subseteq> ?S\<close>)
proof (rule subsetI, elim strict_ticks_of_memE)
  fix t r_s assume \<open>t @ [\<checkmark>(r_s)] \<in> \<T> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> \<open>t \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
  from \<open>t \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> have \<open>t @ [\<checkmark>(r_s)] \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> by (meson is_processT9)
  with \<open>t @ [\<checkmark>(r_s)] \<in> \<T> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> obtain t_P t_Q
    where \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close> \<open>t @ [\<checkmark>(r_s)] setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P, t_Q), S)\<close>
    unfolding Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_projs by blast
  from this(3) show \<open>r_s \<in> ?S\<close>
  proof (elim snoc_tick_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
    fix t_P' t_Q' r s
    assume * : \<open>r \<otimes>\<checkmark> s = Some r_s\<close> \<open>t_P = t_P' @ [\<checkmark>(r)]\<close> \<open>t_Q = t_Q' @ [\<checkmark>(s)]\<close>
      \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((t_P', t_Q'), S)\<close>
    have \<open>t_P' \<notin> \<D> P \<and> t_Q' \<notin> \<D> Q\<close>
    proof (rule ccontr)
      assume \<open>\<not> (t_P' \<notin> \<D> P \<and> t_Q' \<notin> \<D> Q)\<close>
      with \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close> have \<open>t \<in> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close>
        by (simp add: D_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k "*"(2,3,4))
          (metis "*"(4) append.right_neutral append_T_imp_tickFree front_tickFree_Nil
            is_processT3_TR_append not_Cons_self2 setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree_imp)
      with \<open>t \<notin> \<D> (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark> Q)\<close> show False ..
    qed
    with "*"(2, 3) \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close> have \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P)\<close> \<open>s \<in> \<^bold>\<checkmark>\<^bold>s(Q)\<close>
      by (metis is_processT9 strict_ticks_of_memI)+
    with "*"(1) show \<open>r_s \<in> ?S\<close> by blast
  qed
qed


theorem (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_locale) Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc :
  \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>3 (Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>4 R) = RenamingTick (P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>1 Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>2 R) \<otimes>\<checkmark>2\<Rightarrow>\<otimes>\<checkmark>3\<close> (is \<open>?lhs = ?rhs\<close>)
proof (rule FD_antisym)
  show \<open>?lhs \<sqsubseteq>\<^sub>F\<^sub>D ?rhs\<close> by (fact Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_oneside)
next
  from Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_assoc_oneside[of R S Q P]
  have \<open>Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>2.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k R S
        (Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>1.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Q S P) \<sqsubseteq>\<^sub>F\<^sub>D
        RenamingTick (Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>3.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
        (Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>4.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k R S Q) S P) \<otimes>\<checkmark>3\<Rightarrow>\<otimes>\<checkmark>2\<close> .
  also have \<open>Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>1.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Q S P = P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>1 Q\<close>
    by (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>1.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym)
  also have \<open>Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>2.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k R S P_Q = P_Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>2 R\<close> for P_Q
    by (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>2.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym)
  also have \<open>Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>4.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k R S Q = Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>4 R\<close>
    by (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>4.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym)
  also have \<open>Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>3.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k Q_R S P = P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>3 Q_R\<close> for Q_R
    by (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>3.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym)
  finally have \<open>P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>1 Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>2 R \<sqsubseteq>\<^sub>F\<^sub>D RenamingTick ?lhs \<otimes>\<checkmark>3\<Rightarrow>\<otimes>\<checkmark>2\<close> .
  hence \<open>?rhs \<sqsubseteq>\<^sub>F\<^sub>D RenamingTick (RenamingTick ?lhs \<otimes>\<checkmark>3\<Rightarrow>\<otimes>\<checkmark>2) \<otimes>\<checkmark>2\<Rightarrow>\<otimes>\<checkmark>3\<close>
    by (fact mono_Renaming_FD)
  also have \<open>\<dots> = RenamingTick ?lhs (\<otimes>\<checkmark>2\<Rightarrow>\<otimes>\<checkmark>3 \<circ> \<otimes>\<checkmark>3\<Rightarrow>\<otimes>\<checkmark>2)\<close>
    by (simp add: RenamingTick_comp)
  also have \<open>\<dots> = RenamingTick ?lhs id\<close>
  proof (rule RenamingTick_is_restrictable_on_strict_ticks_of)
    fix r_s_t assume \<open>r_s_t \<in> \<^bold>\<checkmark>\<^bold>s(P \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>3 (Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>4 R))\<close>
    with Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>3.strict_ticks_of_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset obtain r s_t
      where \<open>r \<otimes>\<checkmark>3 s_t = \<lfloor>r_s_t\<rfloor>\<close> \<open>r \<in> \<^bold>\<checkmark>\<^bold>s(P)\<close> \<open>s_t \<in> \<^bold>\<checkmark>\<^bold>s(Q \<lbrakk>S\<rbrakk>\<^sub>\<checkmark>\<^sub>4 R)\<close> by blast
    from this(3) Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<^sub>4.strict_ticks_of_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset obtain s t
      where \<open>s \<otimes>\<checkmark>4 t = \<lfloor>s_t\<rfloor>\<close> \<open>s \<in> \<^bold>\<checkmark>\<^bold>s(Q)\<close> \<open>t \<in> \<^bold>\<checkmark>\<^bold>s(R)\<close> by blast
    from \<open>r \<otimes>\<checkmark>3 s_t = \<lfloor>r_s_t\<rfloor>\<close> \<open>s \<otimes>\<checkmark>4 t = \<lfloor>s_t\<rfloor>\<close>
    show \<open>(\<otimes>\<checkmark>2\<Rightarrow>\<otimes>\<checkmark>3 \<circ> \<otimes>\<checkmark>3\<Rightarrow>\<otimes>\<checkmark>2) r_s_t = id r_s_t\<close>
      by (auto intro!: tick_assoc_ren_tick_assoc_ren_conv)
  qed
  also have \<open>\<dots> = ?lhs\<close> by simp
  finally show \<open>?rhs \<sqsubseteq>\<^sub>F\<^sub>D ?lhs\<close> .
qed


(*<*)
end
  (*>*)
