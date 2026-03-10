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


chapter \<open>Commutativity and Associativity of Synchronization\<close>

section \<open>Commutativity\<close>

(*<*)
theory Synchronization_Product_Generalized_Commutativity
  imports CSP_PTick_Renaming
begin
  (*>*)

subsection \<open>Motivation\<close>

text (in Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale) \<open>
The classical synchronization product is commutative: @{thm Sync_commute[of P A Q]}
but in our generalization such a law cannot be obtained in all generality.
Imagine for example that the \<^term>\<open>tick_join\<close> parameter is actually \<^term>\<open>\<lambda>r s. \<lfloor>(r, s)\<rfloor>\<close>:
we easily figure out that in this case the corresponding law should
be something like \<open>P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r Q = TickSwap (Q \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>P\<^sub>a\<^sub>i\<^sub>r P)\<close>.
More generally, in the \<^theory_text>\<open>locale\<close>, when writing \<^term>\<open>P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q\<close>,
\<^term>\<open>P\<close> is of type \<^typ>\<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> while \<^term>\<open>Q\<close> is of type \<^typ>\<open>('a, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
so we want to find an abstract setup in which we can establish a quasi-commutativity.
This is done in the next subsection.
\<close>


subsection \<open>Formalization\<close>

locale Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale =
  Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale \<open>(\<otimes>\<checkmark>)\<close> for tick_join :: \<open>'r \<Rightarrow> 's \<Rightarrow> 't option\<close> (infixl \<open>\<otimes>\<checkmark>\<close> 100) +
fixes tick_join_rev      :: \<open>'s \<Rightarrow> 'r \<Rightarrow> 'u option\<close> (infixl \<open>\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v\<close> 100)
  and tick_join_conv     :: \<open>'t \<Rightarrow> 'u\<close> (\<open>\<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v\<close>)
  and tick_join_rev_conv :: \<open>'u \<Rightarrow> 't\<close> (\<open>\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v\<Rightarrow>\<otimes>\<checkmark>\<close>)
assumes tick_join_None_iff :
  \<open>r \<otimes>\<checkmark> s = \<diamond> \<longleftrightarrow> s \<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v r = \<diamond>\<close>
  and tick_join_Some_imp :
  \<open>r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor> \<Longrightarrow> s \<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v r = \<lfloor>\<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v r_s\<rfloor>\<close>
  and tick_join_rev_Some_imp :
  \<open>s \<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v r = \<lfloor>s_r\<rfloor> \<Longrightarrow> r \<otimes>\<checkmark> s = \<lfloor>\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v\<Rightarrow>\<otimes>\<checkmark> s_r\<rfloor>\<close>
begin


text \<open>There is an obvious symmetry over the variables.\<close>

sublocale Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym :
  Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale \<open>(\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v)\<close> \<open>(\<otimes>\<checkmark>)\<close> \<open>\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v\<Rightarrow>\<otimes>\<checkmark>\<close> \<open>\<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v\<close>
proof unfold_locales
  show \<open>s \<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v r = \<lfloor>s_r\<rfloor> \<Longrightarrow> s' \<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v r' = \<lfloor>s_r\<rfloor>
        \<Longrightarrow> s' = s \<and> r' = r\<close> for s r s_r s' r'
    using inj_tick_join tick_join_rev_Some_imp by blast
next
  show \<open>s \<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v r = \<diamond> \<longleftrightarrow> r \<otimes>\<checkmark> s = \<diamond>\<close> for s r
    by (simp add: tick_join_None_iff)
next
  show \<open>s \<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v r = \<lfloor>s_r\<rfloor> \<Longrightarrow> r \<otimes>\<checkmark> s = \<lfloor>\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v\<Rightarrow>\<otimes>\<checkmark> s_r\<rfloor>\<close> for s r s_r
    by (simp add: tick_join_rev_Some_imp)
next
  show \<open>r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor> \<Longrightarrow> s \<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v r = \<lfloor>\<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v r_s\<rfloor>\<close> for r s r_s
    by (simp add: tick_join_Some_imp)
qed


notation Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<open>(_ \<lbrakk>_\<rbrakk>\<^sub>\<checkmark>\<^sub>r\<^sub>e\<^sub>v _)\<close> [70, 0, 71] 70)
notation Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym.Inter\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<open>(_ |||\<^sub>\<checkmark>\<^sub>r\<^sub>e\<^sub>v _)\<close> [72, 73] 72)
notation Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym.Par\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<open>(_ ||\<^sub>\<checkmark>\<^sub>r\<^sub>e\<^sub>v _)\<close> [74, 75] 74)



subsection \<open>First Properties\<close>

lemma tick_join_conv_image_range_tick_join :
  \<open>\<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v ` range_tick_join = Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym.range_tick_join\<close>
  by (simp add: set_eq_iff flip: setcompr_eq_image)
    (metis option.inject tick_join_Some_imp tick_join_rev_Some_imp)

lemma tick_join_rev_conv_comp_tick_join_conv [simp] :
  \<open>r_s \<in> range_tick_join \<Longrightarrow> \<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v\<Rightarrow>\<otimes>\<checkmark> (\<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v r_s) = r_s\<close>
  using tick_join_Some_imp tick_join_rev_Some_imp by fastforce

lemma inj_on_tick_join_conv : \<open>inj_on \<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v range_tick_join\<close>
  by (rule inj_onI, simp)
    (metis option.inject tick_join_Some_imp tick_join_rev_Some_imp)

lemma bij_betw_tick_join_conv :
  \<open>bij_betw \<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v range_tick_join Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym.range_tick_join\<close>
proof (rule bij_betw_imageI)
  show \<open>inj_on \<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v range_tick_join\<close>
    by (fact inj_on_tick_join_conv)
next
  show \<open>\<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v ` range_tick_join = Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym.range_tick_join\<close>
    using tick_join_conv_image_range_tick_join by blast
qed



lemma map_tick_join_rev_conv_map_tick_join_conv :
  \<open>{r_s. \<checkmark>(r_s) \<in> set t} \<subseteq> range_tick_join \<Longrightarrow>
   map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id \<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v\<Rightarrow>\<otimes>\<checkmark>) (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id \<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v) t) = t\<close>
proof (induct t)
  case Nil show ?case by simp
next
  let ?f1 = \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id \<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v\<close>
  let ?f2 = \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id \<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v\<Rightarrow>\<otimes>\<checkmark>\<close>
  case (Cons e t)
  have \<open>map ?f2 (map ?f1 (e # t)) = ?f2 (?f1 e) # map ?f2 (map ?f1 t)\<close> by simp
  also have \<open>?f2 (?f1 e) = e\<close>
  proof (cases e)
    show \<open>e = ev a \<Longrightarrow> ?f2 (?f1 e) = e\<close> for a by simp
  next
    fix r_s assume \<open>e = \<checkmark>(r_s)\<close>
    with Cons.prems have \<open>r_s \<in> range_tick_join\<close> by auto
    with \<open>e = \<checkmark>(r_s)\<close> inj_on_tick_join_conv
    show \<open>?f2 (?f1 e) = e\<close> by simp
  qed
  also have \<open>map ?f2 (map ?f1 t) = t\<close>
    by (rule Cons.hyps) (use Cons.prems in auto)
  finally show \<open>map ?f2 (map ?f1 (e # t)) = e # t\<close> .
qed

end



subsection \<open>Commutativity\<close>

context Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale begin

lemma setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_imp_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_rev :
  \<open>t setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((u, v), A) \<Longrightarrow>
   map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id \<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v) t
   setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v)\<^esub> ((v, u), A)\<close>
  \<comment> \<open>Finally not used, and probably obtainable as a corollary of
      @{thm inj_on_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_setinterleaves\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF inj_on_tick_join_conv, of t u A v]}\<close>
proof (induct \<open>((\<otimes>\<checkmark>), u, A, v)\<close> arbitrary: t u v)
  case (tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick r u s v)
  from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.prems
  obtain r_s t'
    where * : \<open>r \<otimes>\<checkmark> s = \<lfloor>r_s\<rfloor>\<close> \<open>t = \<checkmark>(r_s) # t'\<close>
      \<open>t' setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>)\<^esub> ((u, v), A)\<close>
    by (auto split: option.split_asm)
  from tick_setinterleaving\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tick.hyps[OF "*"(1), OF "*"(3)]
  have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id \<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v) t'
        setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v)\<^esub> ((v, u), A)\<close> .
  moreover from tick_join_Some_imp[OF "*"(1)]
  have \<open>s \<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v r = \<lfloor>\<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v r_s\<rfloor>\<close> .
  ultimately show \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id \<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v) t
                   setinterleaves\<^sub>\<checkmark>\<^bsub>(\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v)\<^esub> ((\<checkmark>(s) # v, \<checkmark>(r) # u), A)\<close>
    by (simp add: "*"(1, 2))
qed auto

lemma vimage_tick_join_rev_conv_subset_super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff :
  \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k id \<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v\<Rightarrow>\<otimes>\<checkmark> -` X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v) X_Q A X_P
   \<longleftrightarrow> X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P A X_Q\<close>
  (is \<open>?lhs1 \<subseteq> ?lhs2 \<longleftrightarrow> X \<subseteq> ?rhs\<close>)
  \<comment> \<open>Same: finally not used, and probably obtainable as a corollary of
      @{thm Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym.vimage_inj_on_subset_super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff
            [OF Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym.inj_on_tick_join_conv]}.\<close>
proof -
  have * : \<open>(\<lambda>r s. case r \<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v s of \<diamond> \<Rightarrow> \<diamond> | \<lfloor>r_s\<rfloor> \<Rightarrow> \<lfloor>\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v\<Rightarrow>\<otimes>\<checkmark> r_s\<rfloor>) =
            (\<lambda>s r. r \<otimes>\<checkmark> s)\<close>
    by (intro ext, simp split: option.split)
      (metis tick_join_None_iff tick_join_rev_Some_imp)
  show ?thesis
  proof (subst Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym.vimage_inj_on_subset_super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
    show \<open>inj_on \<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v\<Rightarrow>\<otimes>\<checkmark> Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym.range_tick_join\<close>
      by (fact Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym.inj_on_tick_join_conv)
  next
    show \<open>X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
               (\<lambda>r s. case r \<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v s of \<diamond> \<Rightarrow> \<diamond> | \<lfloor>r_s\<rfloor> \<Rightarrow> \<lfloor>\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v\<Rightarrow>\<otimes>\<checkmark> r_s\<rfloor>) X_Q A X_P
          \<longleftrightarrow> X \<subseteq> super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (\<otimes>\<checkmark>) X_P A X_Q\<close>
      using super_ref_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym by (simp add: "*") blast
  qed
qed



text \<open>
In the end, the proof is quite simple: mainly a corollary
of @{thm inj_on_RenamingTick_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[no_vars]}.
\<close>

theorem Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_commute :
  \<open>RenamingTick (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q) \<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v = Q \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>r\<^sub>e\<^sub>v P\<close>
proof -
  from inj_on_RenamingTick_Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF inj_on_tick_join_conv]
  have \<open>RenamingTick (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q) \<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v =
        Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
        (\<lambda>r s. case r \<otimes>\<checkmark> s of \<diamond> \<Rightarrow> \<diamond> | \<lfloor>r_s\<rfloor> \<Rightarrow> \<lfloor>\<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v r_s\<rfloor>) P A Q\<close>
    (is \<open>_ = Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_locale.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ?tick_join' P A Q\<close>) .
  also have \<open>?tick_join' = (\<lambda>r s. s \<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v r)\<close>
    by (intro ext)
      (simp add: Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym.tick_join_rev_Some_imp
        tick_join_None_iff split: option.split)
  finally show \<open>RenamingTick (P \<lbrakk>A\<rbrakk>\<^sub>\<checkmark> Q) \<otimes>\<checkmark>\<Rightarrow>\<otimes>\<checkmark>\<^sub>r\<^sub>e\<^sub>v = Q \<lbrakk>A\<rbrakk>\<^sub>\<checkmark>\<^sub>r\<^sub>e\<^sub>v P\<close>
    by (metis Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comm_locale_sym.Sync\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_sym)
qed


end


(*<*)
end
  (*>*)