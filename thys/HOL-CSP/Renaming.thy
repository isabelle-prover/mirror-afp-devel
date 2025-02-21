(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff, Lina Ye.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : Renaming operator
 *
 * Copyright (c) 2009 Université Paris-Sud, France
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

chapter\<open> The Renaming Operator \<close>

(*<*)
theory  Renaming
  imports Process
begin
  (*>*)

section\<open>Some preliminaries\<close>

term \<open>f -` B\<close> (* instead of defining our own antecedent function *)

definition finitary :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> bool\<close> 
  where \<open>finitary f \<equiv> \<forall>x. finite(f -` {x})\<close>

(* 
definition finitaryExt :: \<open>('a \<Rightarrow> ('b, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<Rightarrow> bool\<close> 
  where \<open>finitaryExt f \<equiv> \<forall>x. finite(f -` {ev x})\<close>

 *)

text \<open>We start with some simple results.\<close>

lemma \<open>f -` {} = {}\<close> by simp

lemma \<open>X \<subseteq> Y \<Longrightarrow> f -` X \<subseteq> f -` Y\<close> by (rule vimage_mono)

lemma \<open>f -`(X \<union> Y) = f -` X \<union> f -` Y\<close> by (rule vimage_Un)


lemma map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_ev_iff   : \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g e = ev b \<longleftrightarrow> (\<exists>a. e = ev a   \<and> b = f a)\<close>
  and map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_tick_iff : \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g e = \<checkmark>(s) \<longleftrightarrow> (\<exists>r. e = \<checkmark>(r) \<and> s = g r)\<close>
  and ev_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff   : \<open>ev b = map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g e \<longleftrightarrow> (\<exists>a. e = ev a   \<and> b = f a)\<close>
  and tick_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff : \<open>\<checkmark>(s) = map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g e \<longleftrightarrow> (\<exists>r. e = \<checkmark>(r) \<and> s = g r)\<close>
  by (cases e; auto)+


lemma inj_left_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k: \<open>inj (\<lambda>f. map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)\<close>
proof (intro injI ext)
  show \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f1 g = map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f2 g \<Longrightarrow> f1 a = f2 a\<close> for f1 f2 :: \<open>'a \<Rightarrow> 'b\<close> and a :: 'a
    by (drule fun_cong[where x = \<open>ev a\<close>]) simp
qed

lemma inj_right_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k: \<open>inj (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f)\<close>
proof (intro injI ext)
  show \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g1 = map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g2 \<Longrightarrow> g1 r = g2 r\<close> for g1 g2 :: \<open>'r \<Rightarrow> 's\<close> and r :: 'r
    by (drule fun_cong[where x = \<open>\<checkmark>(r)\<close>]) simp
qed


lemma map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree : \<open>tickFree (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s) \<longleftrightarrow> tickFree s\<close>
  by (induct s) (simp_all add: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.case_eq_if)

lemma map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_front_tickFree : \<open>front_tickFree (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s) \<longleftrightarrow> front_tickFree s\<close>
  by (simp add: front_tickFree_iff_tickFree_butlast map_butlast[symmetric] map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree)


lemma map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_tick_iff :
  \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t = [\<checkmark>(s)] \<longleftrightarrow> (\<exists>r. s = g r \<and> t = [\<checkmark>(r)])\<close>
  and tick_eq_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff :
  \<open>[\<checkmark>(s)] = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t \<longleftrightarrow> (\<exists>r. s = g r \<and> t = [\<checkmark>(r)])\<close> 
  by (auto simp add: map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_tick_iff tick_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)


section\<open>The Renaming Operator Definition\<close>

text \<open>Our new renaming operator does not only deal with events but also with termination.\<close>

lift_definition Renaming :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a \<Rightarrow> 'b, 'r \<Rightarrow> 's] \<Rightarrow> ('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  is \<open>\<lambda>P f g. ({( map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1, X)| s1 X. (s1, (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) -` X) \<in> \<F> P} \<union>
               {((map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1) @ s2, X)| s1 s2 X. tickFree s1 \<and> front_tickFree s2 \<and> s1 \<in> \<D> P},
               {( map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1) @ s2| s1 s2. tickFree s1 \<and> front_tickFree s2 \<and> s1 \<in> \<D> P})\<close>
proof -
  show \<open>?thesis P f g\<close> (is \<open>is_process(?f, ?d)\<close>) for P f g
  proof (unfold is_process_def FAILURES_def DIVERGENCES_def fst_conv snd_conv, intro conjI allI impI)
    show \<open>([], {}) \<in> ?f\<close>
      by (simp add: process_charn)
  next
    show \<open>(s, X) \<in> ?f \<Longrightarrow> front_tickFree s\<close> for s X
      by (auto simp add: F_imp_front_tickFree map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_front_tickFree
          map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree front_tickFree_append)
  next
    show \<open>(s @ t, {}) \<in> ?f \<Longrightarrow> (s, {}) \<in> ?f\<close> for s t
    proof (induct t rule: rev_induct)
      case Nil thus \<open>(s, {}) \<in> ?f\<close> by simp
    next
      case (snoc e t)
      from snoc.prems is_processT8 
      consider (fail) s1 where \<open>s @ t @ [e] = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1\<close> \<open>(s1, {}) \<in> \<F> P\<close>
        | (div) s1 s2 where \<open>s @ t @ [e] = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1 @ s2\<close> \<open>s2 \<noteq> []\<close>
          \<open>tickFree s1\<close> \<open>front_tickFree s2\<close> \<open>s1 \<in> \<D> P\<close> by auto blast
      thus \<open>(s, {}) \<in> ?f\<close>
      proof cases
        case fail
        from fail(1) obtain s1' e' where \<open>s1 = s1' @ [e']\<close> \<open>s @ t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1'\<close>
          by (metis Nil_is_append_conv butlast_append list.map_disc_iff map_butlast snoc_eq_iff_butlast)
        from this(1) fail(2) is_processT3 have \<open>(s1', {}) \<in> \<F> P\<close> by blast
        with \<open>s @ t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1'\<close> have \<open>(s @ t, {}) \<in> ?f\<close> by auto
        with snoc.hyps show \<open>(s, {}) \<in> ?f\<close> by presburger
      next
        case div
        from div(2) obtain s2' e' where \<open>s2 = s2' @ [e']\<close> by (meson rev_exhaust)
        with div(1, 3, 4, 5) \<open>s2 = s2' @ [e']\<close> front_tickFree_dw_closed 
        have \<open>(s @ t, {}) \<in> ?f\<close> by simp blast
        with snoc.hyps show \<open>(s, {}) \<in> ?f\<close> by presburger
      qed
    qed
  next
    show \<open>(s, Y) \<in> ?f \<and> X \<subseteq> Y \<Longrightarrow> (s, X) \<in> ?f\<close> for s X Y
      by (induct s rule: rev_induct, simp_all)
        (meson is_processT4 vimage_mono)+
  next
    show \<open>(s, X) \<in> ?f \<and> (\<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> ?f) \<Longrightarrow> (s, X \<union> Y) \<in> ?f\<close> for s X Y
      by auto (metis (no_types, lifting) is_processT5 list.simps(8, 9) map_append vimageE)
  next
    fix s r X assume \<open>(s @ [\<checkmark>(r)], {}) \<in> ?f\<close>
    then consider (fail) s1 where \<open>s @ [\<checkmark>(r)] = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1\<close> \<open>(s1, {}) \<in> \<F> P\<close>
      | (div) s1 s2 where \<open>s @ [\<checkmark>(r)] = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1 @ s2\<close> \<open>s2 \<noteq> []\<close>
        \<open>tickFree s1\<close> \<open>front_tickFree s2\<close> \<open>s1 \<in> \<D> P\<close>
      using is_processT8 by auto blast
    thus \<open>(s, X - {\<checkmark>(r)}) \<in> ?f\<close>
    proof cases
      case fail
      from fail(1) obtain s1' r' where * : \<open>s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1'\<close> \<open>s1 = s1' @ [\<checkmark>(r')]\<close> \<open>r = g r'\<close>
        by (simp add: append_eq_map_conv) (metis (mono_tags, opaque_lifting) map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_tick_iff)
      from this(2) fail(2) have \<open>(s1', map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X - {\<checkmark>(r')}) \<in> \<F> P\<close> 
        by (simp add: is_processT6)
      hence  \<open>(s1', map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` (X - {\<checkmark>(r)})) \<in> \<F> P\<close>
        by (rule is_processT4) (auto simp add: \<open>r = g r'\<close>)
      thus \<open>(s, X - {\<checkmark>(r)}) \<in> ?f\<close> by (unfold "*"(1)) blast
    next
      case div
      from div(2, 4) front_tickFree_charn tickFree_imp_front_tickFree
      obtain s2' e' where \<open>s2 = s2' @ [e']\<close> \<open>front_tickFree s2'\<close> by blast
      from \<open>s2 = s2' @ [e']\<close> div(1) have \<open>s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1 @ s2'\<close> by simp
      with div(3, 5) \<open>front_tickFree s2'\<close> show \<open>(s, X - {\<checkmark>(r)}) \<in> ?f\<close> by blast
    qed
  next
    show \<open>s \<in> ?d \<and> tickFree s \<and> front_tickFree t \<Longrightarrow> s @ t \<in> ?d\<close> for s t
      using front_tickFree_append by safe auto
  next
    show \<open>s \<in> ?d \<Longrightarrow> (s, X) \<in> ?f\<close> for s X by blast

  next
    fix s r assume \<open>s @ [\<checkmark>(r)] \<in> ?d\<close>
    then obtain s1 s2 where * : \<open>s @ [\<checkmark>(r)] = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1 @ s2\<close>
      \<open>tickFree s1\<close> \<open>front_tickFree s2\<close> \<open>s1 \<in> \<D> P\<close> by blast
    from "*"(1, 2, 3) obtain s2' e where \<open>s2 = s2' @ [e]\<close> \<open>front_tickFree s2'\<close>
      by (metis append_self_conv front_tickFree_charn front_tickFree_dw_closed
          non_tickFree_tick map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree tickFree_append_iff)
    from this(1) "*"(1) have \<open>s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1 @ s2'\<close> by simp
    with "*"(2, 4) \<open>front_tickFree s2'\<close> show \<open>s \<in> ?d\<close> by blast
  qed
qed



text \<open>Some syntactic sugar.\<close>

syntax
  "_Renaming"  :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> updbinds \<Rightarrow> updbinds \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (\<open>_ \<lbrakk>_\<rbrakk> \<lbrakk>_\<rbrakk>\<close> [100, 100, 100]) (*see the values we need, at least 51*)
  "_Renaming_left"   :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> updbinds \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (\<open>_ \<lbrakk>_\<rbrakk> \<lbrakk>\<rbrakk>\<close> [100, 100])
  "_Renaming_right"  :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> updbinds \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (\<open>_ \<lbrakk>\<rbrakk> \<lbrakk>_\<rbrakk>\<close> [100, 100])
syntax_consts "_Renaming" \<rightleftharpoons> Renaming
  and         "_Renaming_left" \<rightleftharpoons> Renaming
  and         "_Renaming_right" \<rightleftharpoons> Renaming
translations
  "_Renaming P f_updates g_updates" \<rightleftharpoons> "CONST Renaming P (_Update (CONST id) f_updates) (_Update (CONST id) g_updates)"
  "_Renaming_left  P f_updates" \<rightleftharpoons> "CONST Renaming P (_Update (CONST id) f_updates) (CONST id)"
  "_Renaming_right P g_updates" \<rightleftharpoons> "CONST Renaming P (CONST id) (_Update (CONST id) g_updates)"

text \<open>Now we can write \<^term>\<open>P \<lbrakk>a := b\<rbrakk> \<lbrakk>c := d\<rbrakk>\<close>.
      If we only want to rename events, or results, we use respectively
      \<^term>\<open>P \<lbrakk>a := b\<rbrakk> \<lbrakk>\<rbrakk>\<close> and  \<^term>\<open>P \<lbrakk>\<rbrakk> \<lbrakk>c := d\<rbrakk>\<close>. 
      Like in \<^theory>\<open>HOL.Fun\<close>, we can write this kind of expression with as many
      updates we want: \<^term>\<open>P\<lbrakk>a := b, c := d, e := f, g := h\<rbrakk> \<lbrakk>r1 := r2, r3 := r4\<rbrakk>\<close>.
      By construction we also inherit all the results about \<^const>\<open>fun_upd\<close>, for example
      @{thm fun_upd_other fun_upd_upd fun_upd_twist}.\<close>

lemma \<open>P \<lbrakk>x := y, x := z\<rbrakk> \<lbrakk>\<rbrakk> = P\<lbrakk>x := z\<rbrakk> \<lbrakk>\<rbrakk>\<close> by simp

lemma \<open>a \<noteq> c \<Longrightarrow> P \<lbrakk>a := b, c := d\<rbrakk> \<lbrakk>r1 := r2\<rbrakk> = P \<lbrakk>c := d, a := b\<rbrakk> \<lbrakk>r1 := r2\<rbrakk>\<close> by (simp add: fun_upd_twist)




section\<open>The Projections\<close>

lemma F_Renaming: \<open>\<F> (Renaming P f g) = 
  {( map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1, X)| s1 X. (s1, (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) -` X) \<in> \<F> P} \<union>
  {((map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1) @ s2, X)| s1 s2 X. tickFree s1 \<and> front_tickFree s2 \<and> s1 \<in> \<D> P}\<close>
  by (simp add: Failures.rep_eq FAILURES_def Renaming.rep_eq)

lemma D_Renaming: \<open>\<D> (Renaming P f g) =
  {(map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1) @ s2| s1 s2. tickFree s1 \<and> front_tickFree s2 \<and> s1 \<in> \<D> P}\<close>
  by (simp add: Divergences.rep_eq DIVERGENCES_def Renaming.rep_eq)

lemma T_Renaming: \<open>\<T> (Renaming P f g) = 
  { map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1| s1. s1 \<in> \<T> P} \<union>
  {(map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1) @ s2| s1 s2. tickFree s1 \<and> front_tickFree s2 \<and> s1 \<in> \<D> P}\<close>
  by (subst set_eq_iff, fold T_F_spec, simp add: F_Renaming)

lemmas Renaming_projs = F_Renaming D_Renaming T_Renaming



section\<open>Continuity Rule\<close>

subsection \<open>Monotonicity of \<^const>\<open>Renaming\<close>.\<close>

lemma mono_Renaming : \<open>Renaming P f g \<sqsubseteq> Renaming Q f g\<close> if \<open>P \<sqsubseteq> Q\<close>
proof (subst le_approx_def, intro conjI subset_antisym allI impI subsetI)
  show \<open>s \<in> \<D> (Renaming Q f g) \<Longrightarrow> s \<in> \<D> (Renaming P f g)\<close> for s
    unfolding D_Renaming using le_approx1 \<open>P \<sqsubseteq> Q\<close> by blast
next
  show \<open>s \<notin> \<D> (Renaming P f g) \<Longrightarrow> X \<in> \<R>\<^sub>a (Renaming P f g) s \<Longrightarrow> X \<in> \<R>\<^sub>a (Renaming Q f g) s\<close> for s X
    by (simp add: D_Renaming Refusals_after_def F_Renaming)
      (metis (no_types, opaque_lifting) F_imp_front_tickFree append.right_neutral front_tickFree_Nil
        front_tickFree_append_iff front_tickFree_single is_processT9 map_append tickFree_Nil
        map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_tick_iff nonTickFree_n_frontTickFree non_tickFree_tick proc_ord2a \<open>P \<sqsubseteq> Q\<close>)
next
  show \<open>s \<notin> \<D> (Renaming P f g) \<Longrightarrow> X \<in> \<R>\<^sub>a (Renaming Q f g) s \<Longrightarrow> X \<in> \<R>\<^sub>a (Renaming P f g) s\<close> for s X
    by (simp add: D_Renaming Refusals_after_def F_Renaming)
      (metis (no_types, lifting) is_processT8 le_approx1 proc_ord2a subset_eq \<open>P \<sqsubseteq> Q\<close>) 
next
  show \<open>s \<in> min_elems (\<D> (Renaming P f g)) \<Longrightarrow> s \<in> \<T> (Renaming Q f g)\<close> for s
    apply (rule set_mp[of \<open>{map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1 |s1. s1 \<in> min_elems (\<D> P)}\<close>])
     apply (simp add: T_Renaming, use le_approx3 \<open>P \<sqsubseteq> Q\<close> in blast)
    apply (drule set_rev_mp[of _ _ \<open>min_elems {map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1 |s1. tickFree s1 \<and> s1 \<in> \<D> P}\<close>])
     apply (simp_all add: D_Renaming min_elems_def subset_iff)
    by (metis prefixI antisym_conv2 append.right_neutral front_tickFree_Nil)
      (metis (no_types, lifting) antisym_conv2 append_butlast_last_id 
        front_tickFree_iff_tickFree_butlast less_self list.map_disc_iff map_butlast
        min_elems1 min_elems_no nil_less order_less_imp_le tickFree_imp_front_tickFree)
qed


lemma \<open>{ev c |c. f c = a} = ev`{c . f c = a}\<close> by (rule setcompr_eq_image)


lemma vimage_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_subset_vimage: \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` (ev ` A) \<subseteq> range tick \<union> (ev ` (f -` A))\<close>
  and vimage_subset_vimage_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k: \<open>(ev ` (f -` A)) \<subseteq> (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` (ev ` A)) - range tick\<close>
  by (auto simp add: image_def vimage_def)
    (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust_sel event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(1) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(9))




subsection \<open>Some useful results about \<^const>\<open>finitary\<close>, and preliminaries lemmas for continuity.\<close>

lemma inj_imp_finitary[simp] : \<open>inj f \<Longrightarrow> finitary f\<close> by (simp add: finitary_def finite_vimageI)

lemma finitary_comp_iff : \<open>finitary g \<Longrightarrow> finitary (g o f) \<longleftrightarrow> finitary f\<close>
proof (unfold finitary_def, intro iffI allI;
    (subst vimage_comp[symmetric] | subst (asm) vimage_comp[symmetric]))
  have f1: \<open>f -` g -` {x} = (\<Union>y \<in> g -` {x}. f -` {y})\<close> for x by blast
  show \<open>finite (f -` g -` {x})\<close> if  \<open>\<forall>x. finite (f -` {x})\<close> and \<open>\<forall>x. finite (g -` {x})\<close> for x
    apply (subst f1, subst finite_UN)
    by (rule that(2)[unfolded finitary_def, rule_format])
      (intro ballI that(1)[rule_format])
qed (metis finite_Un insert_absorb vimage_insert vimage_singleton_eq)



lemma finitary_updated_iff[simp] : \<open>finitary (f (a := b)) \<longleftrightarrow> finitary f\<close>
proof (unfold fun_upd_def finitary_def vimage_def, intro iffI allI)
  show \<open>finite {x. (if x = a then b else f x) \<in> {y}}\<close> if \<open>\<forall>y. finite {x. f x \<in> {y}}\<close> for y
    apply (rule finite_subset[of _ \<open>{x. x = a} \<union> {x. f x \<in> {y}}\<close>], (auto)[1])
    apply (rule finite_UnI)
    by simp (fact that[rule_format]) 
next
  show \<open>finite {x. f x \<in> {y}}\<close> if \<open>\<forall>y. finite {x. (if x = a then b else f x) \<in> {y}}\<close> for y
    apply (rule finite_subset[of _ \<open>{x. x = a \<and> f x \<in> {y}} \<union> {x. x \<noteq> a \<and> f x \<in> {y}}\<close>], (auto)[1])
    apply (rule finite_UnI)
    using that[rule_format, of y] by (simp_all add: Collect_mono rev_finite_subset)
qed

text \<open>By declaring this simp, we automatically obtain this kind of result.\<close>

lemma \<open>finitary f \<longleftrightarrow> finitary (f (a := b, c := d, e:= g, h := i))\<close> by simp


lemma Cont_RenH2:
  \<open>finitary ((map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) :: ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('b, 's) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<longleftrightarrow> finitary f \<and> finitary g\<close>
proof (intro iffI conjI)
  show \<open>finitary f\<close> if \<open>finitary (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)\<close>
  proof (unfold finitary_def, rule allI)
    fix b :: 'b
    have \<open>finite ((map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) -` {ev b})\<close>
      by (fact \<open>finitary (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)\<close>[unfolded finitary_def, rule_format])
    also have \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` {ev b} = ev ` (f -` {b})\<close>
      by (unfold vimage_def image_def) (auto simp add: map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_ev_iff)
    finally show \<open>finite (f -` {b})\<close> by (simp add: inj_on_def finite_image_iff)
  qed
next
  show \<open>finitary g\<close> if \<open>finitary (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)\<close>
  proof (unfold finitary_def, rule allI)
    fix s :: 's
    have \<open>finite ((map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) -` {tick s})\<close>
      by (fact \<open>finitary (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)\<close>[unfolded finitary_def, rule_format])
    also have \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` {tick s} = tick ` (g -` {s})\<close>
      by (unfold vimage_def image_def) (auto simp add: map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_tick_iff)
    finally show \<open>finite (g -` {s})\<close> by (simp add: inj_on_def finite_image_iff)
  qed
next
  show \<open>finitary (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)\<close> if \<open>finitary f \<and> finitary g\<close>
  proof (unfold finitary_def, rule allI)
    fix e :: \<open>('b, 's) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
    show \<open>finite (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` {e})\<close>
    proof (cases e)
      fix b assume \<open>e = ev b\<close>
      have \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` {ev b} = ev ` (f -` {b})\<close>
        by (unfold vimage_def image_def) (auto simp add: map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_ev_iff)
      thus \<open>finite (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` {e})\<close>
        by (simp add: \<open>e = ev b\<close>) (meson finitary_def finite_imageI that)
    next
      fix s assume \<open>e = tick s\<close>
      have \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` {tick s} = tick ` (g -` {s})\<close>
        by (unfold vimage_def image_def) (auto simp add: map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_tick_iff)
      thus \<open>finite (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` {e})\<close>
        by (simp add: \<open>e = tick s\<close>) (meson finitary_def finite_imageI that)
    qed
  qed
qed



lemma Cont_RenH3:
  \<open>{s1 @ t1 |s1 t1. (\<exists> b. s1 = [b] & f b = a) \<and> list = map f t1} = 
   (\<Union> b \<in> f -`{a}. (\<lambda>t. b # t) ` {t. list = map f t})\<close>
  by auto (metis append_Cons append_Nil)


lemma Cont_RenH4: \<open>finitary f \<longleftrightarrow> (\<forall>s. finite {t. s = map f t})\<close>
proof (unfold finitary_def, intro iffI allI)
  show \<open>finite {t. s = map f t}\<close> if \<open>\<forall>x. finite (f -` {x})\<close> for s
  proof (induct s)
    show \<open>finite {t. [] = map f t}\<close> by simp
  next
    case (Cons a s)
    have \<open>{t. a # s = map f t} = (\<Union>b \<in> f -` {a}. {b # t |t. s = map f t})\<close>
      by (subst Cons_eq_map_conv) blast
    thus ?case by (simp add: finite_UN[OF that[rule_format]] local.Cons)
  qed
next
  have map1: \<open>[a] = map f s = (\<exists>b. s = [b] \<and> f b = a)\<close> for a s by fastforce
  show \<open>finite (f -` {x}) \<close> if \<open>\<forall>s. finite {t. s = map f t}\<close> for x
    by (simp add: vimage_def)
      (fact finite_vimageI[OF that[rule_format, of \<open>[x]\<close>, simplified map1], 
          of \<open>\<lambda>x. [x]\<close>, unfolded inj_on_def, simplified])
qed



lemma Cont_RenH5: \<open>finitary f \<Longrightarrow> finitary g \<Longrightarrow> finite (\<Union>t \<in> {t. t \<le> s}. {s. t=map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s})\<close>
  apply (rule finite_UN_I)
  unfolding less_eq_list_def prefix_def
   apply (induct s rule: rev_induct, simp)
   apply (subgoal_tac \<open>{t. \<exists>r. t @ r = xs @ [x]} = insert (xs @ [x]) {t. \<exists>r. t @ r = xs}\<close>, auto)
    (* TODO: break this smt *)
  apply (smt (verit, ccfv_SIG) Collect_cong finite_insert)
  apply (metis Sublist.prefix_snoc prefix_def)
  using Cont_RenH2 Cont_RenH4 apply blast
  done



lemma Cont_RenH6: \<open>{t. \<exists>t2. tickFree t \<and> front_tickFree t2 \<and> x = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t @ t2}
                   \<subseteq> {y. \<exists>xa. xa \<in> {t. t \<le> x} \<and> y \<in> {s. xa = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s}}\<close>
  by auto


lemma Cont_RenH7: \<open>finite {t. \<exists>t2. tickFree t \<and> front_tickFree t2 \<and> s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t @ t2}\<close>
  if \<open>finitary f\<close> and \<open>finitary g\<close>
proof -
  have f1: \<open>{y. map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) y \<le> s} = (\<Union>z \<in> {z. z \<le> s}. {y. z = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) y})\<close> by fast
  show ?thesis
    apply (rule finite_subset[OF Cont_RenH6])
    apply (simp add: f1)
    apply (rule finite_UN_I)
    apply (induct s rule: rev_induct, simp)
    apply (subgoal_tac \<open>{z. z \<le> xs @ [x]} = insert (xs @ [x]) {z. z \<le> xs}\<close>, auto)
    using Cont_RenH2 Cont_RenH4 that by blast
qed


lemma chain_Renaming: \<open>chain Y \<Longrightarrow> chain (\<lambda>i. Renaming (Y i) f g)\<close>
  by (simp add: mono_Renaming chain_def)





subsection \<open>Finally, continuity !\<close>

lemma Cont_Renaming_prem:
  \<open>(\<Squnion> i. Renaming (Y i) f g) = Renaming (\<Squnion> i. Y i) f g\<close>
  if finitary: \<open>finitary f\<close> \<open>finitary g\<close> and chain: \<open>chain Y\<close>
proof (subst Process_eq_spec_optimized, safe)
  fix s
  assume \<open>s \<in> \<D> (\<Squnion>i. Renaming (Y i) f g)\<close>
  define S where \<open>S i \<equiv> {s1. \<exists>t2.   tickFree s1 \<and> front_tickFree t2 
                                    \<and> s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1 @ t2 \<and> s1 \<in> \<D> (Y i)}\<close> for i
  have \<open>(\<Inter>i. S i) \<noteq> {}\<close> 
    apply (rule Inter_nonempty_finite_chained_sets, unfold S_def)
    apply (use \<open>s \<in> \<D> (\<Squnion>i. Renaming (Y i) f g)\<close> in
        \<open>simp add: limproc_is_thelub chain chain_Renaming D_Renaming D_LUB, blast\<close>)
    apply (rule finite_subset[OF _ Cont_RenH7[OF finitary, of s]], blast)
    using chain unfolding chain_def le_approx_def by blast
  then obtain s1 where f5: \<open>s1 \<in> (\<Inter>i. S i)\<close> by blast
  thus \<open>s \<in> \<D> (Renaming (Lub Y) f g)\<close>
    by (simp add: limproc_is_thelub chain chain_Renaming D_Renaming D_LUB S_def) blast
next
  show \<open>s \<in> \<D> (Renaming (Lub Y) f g) \<Longrightarrow> s \<in> \<D> (\<Squnion>i. Renaming (Y i) f g)\<close> for s
    by (auto simp add: limproc_is_thelub chain chain_Renaming D_Renaming D_LUB)
next
next
  assume same_div : \<open>\<D> (\<Squnion>i. Renaming (Y i) f g) = \<D> (Renaming (\<Squnion>i. Y i) f g)\<close>
  fix s X assume \<open>(s, X) \<in> \<F> (\<Squnion>i. Renaming (Y i) f g)\<close>
  show \<open>(s, X) \<in> \<F> (Renaming (\<Squnion>i. Y i) f g)\<close>
  proof (cases \<open>s \<in> \<D> (\<Squnion>i. Renaming (Y i) f g)\<close>)
    show \<open>s \<in> \<D> (\<Squnion>i. Renaming (Y i) f g) \<Longrightarrow> (s, X) \<in> \<F> (Renaming (\<Squnion>i. Y i) f g)\<close>
      by (simp add: is_processT8 same_div)
  next
    assume \<open>s \<notin> \<D> (\<Squnion>i. Renaming (Y i) f g)\<close>
    then obtain j where \<open>s \<notin> \<D> (Renaming (Y j) f g)\<close>
      by (auto simp add: limproc_is_thelub chain_Renaming \<open>chain Y\<close> D_LUB)
    moreover from \<open>(s, X) \<in> \<F> (\<Squnion>i. Renaming (Y i) f g)\<close> have \<open>(s, X) \<in> \<F> (Renaming (Y j) f g)\<close>
      by (simp add: limproc_is_thelub chain_Renaming \<open>chain Y\<close> F_LUB)
    ultimately show \<open>(s, X) \<in> \<F> (Renaming (\<Squnion>i. Y i) f g)\<close>
      by (fact le_approx2[OF mono_Renaming[OF is_ub_thelub[OF \<open>chain Y\<close>]], THEN iffD2])
  qed
next
  show \<open>(s, X) \<in> \<F> (Renaming (Lub Y) f g) \<Longrightarrow> (s, X) \<in> \<F> (\<Squnion>i. Renaming (Y i) f g)\<close> for s X
    by (auto simp add: limproc_is_thelub chain chain_Renaming F_Renaming D_LUB F_LUB)  
qed


lemma Renaming_cont[simp] : \<open>cont P \<Longrightarrow> finitary f \<Longrightarrow> finitary g \<Longrightarrow> cont (\<lambda>x. (Renaming (P x) f g))\<close>
  by (rule contI2)
    (simp add: cont2monofunE mono_Renaming monofun_def,
      simp add: Cont_Renaming_prem ch2ch_cont cont2contlubE)



lemma RenamingF_cont : \<open>cont P \<Longrightarrow> cont (\<lambda>x. (P x) \<lbrakk>a := b\<rbrakk> \<lbrakk>c := d\<rbrakk>)\<close>
  (* by simp *)
  by (simp only: Renaming_cont finitary_updated_iff inj_imp_finitary inj_on_id)


lemma \<open>cont P \<Longrightarrow> cont (\<lambda>x. (P x)\<lbrakk>a := b, c := d, e := f, g := a\<rbrakk> \<lbrakk>r1 := r2, r3:= r4, r5:= r6\<rbrakk>)\<close>
  by simp



section \<open>Some nice properties\<close>

lemma map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comp: \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (f2 \<circ> f1) (g2 \<circ> g1) = map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f2 g2 \<circ> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f1 g1\<close>
  by (rule ext) (simp add: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.map_comp)


lemma Renaming_comp : \<open>Renaming P (f2 \<circ> f1) (g2 \<circ> g1) = Renaming (Renaming P f1 g1) f2 g2\<close>
proof (subst Process_eq_spec, intro conjI subset_antisym)
  show \<open>\<F> (Renaming P (f2 \<circ> f1) (g2 \<circ> g1)) \<subseteq> \<F> (Renaming (Renaming P f1 g1) f2 g2)\<close>
    apply (simp add: F_Renaming D_Renaming subset_iff, safe)
    by (metis (no_types, opaque_lifting) map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comp list.map_comp set.compositionality)
      (metis (no_types, opaque_lifting) map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comp map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree append.right_neutral 
        front_tickFree_Nil list.map_comp)
next
  show \<open>\<F> (Renaming (Renaming P f1 g1) f2 g2) \<subseteq> \<F> (Renaming P (f2 \<circ> f1) (g2 \<circ> g1))\<close>
    apply (simp add: F_Renaming D_Renaming map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comp, safe)
    subgoal by simp (metis (no_types, lifting) vimage_comp)
    subgoal using map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_front_tickFree by simp blast
    subgoal by simp (metis front_tickFree_append map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree) .
next
  show \<open>\<D> (Renaming P (f2 \<circ> f1) (g2 \<circ> g1)) \<subseteq> \<D> (Renaming (Renaming P f1 g1) f2 g2)\<close>
    by (simp add: D_Renaming subset_iff, safe)
      (metis (no_types, opaque_lifting) map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comp map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree append.right_neutral 
        front_tickFree_Nil list.map_comp)
next
  show \<open>\<D> (Renaming (Renaming P f1 g1) f2 g2) \<subseteq> \<D> (Renaming P (f2 \<circ> f1) (g2 \<circ> g1))\<close>
    by (auto simp add: D_Renaming subset_iff)
      (metis map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_comp map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree front_tickFree_append)
qed




lemma Renaming_id: \<open>Renaming P id id = P\<close>
  by (subst Process_eq_spec, auto simp add: F_Renaming D_Renaming event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.map_id0
      is_processT7 is_processT8)
    (metis append.right_neutral front_tickFree_append_iff
      nonTickFree_n_frontTickFree not_Cons_self2 process_charn)


lemma Renaming_inv: \<open>Renaming (Renaming P f g) (inv f) (inv g) = P\<close> if \<open>inj f\<close> and \<open>inj g\<close>
proof -
  have \<open>  Renaming (Renaming P f g) (inv f) (inv g)
        = Renaming P (inv f \<circ> f) (inv g \<circ> g)\<close> by (simp add: Renaming_comp)
  also have \<open>\<dots> = Renaming P id id\<close> by (simp add: \<open>inj f\<close> \<open>inj g\<close>)
  also have \<open>\<dots> = P\<close> by (fact Renaming_id)
  finally show \<open>Renaming (Renaming P f g) (inv f) (inv g) = P\<close> .
qed


lemma inv_Renaming: \<open>Renaming (Renaming P (inv f) (inv g)) f g = P\<close>
  if \<open>bij f\<close> and \<open>bij g\<close>
proof -
  have \<open>  Renaming (Renaming P (inv f) (inv g)) f g
        = Renaming P (f \<circ> inv f) (g \<circ>  inv g)\<close> by (simp add: Renaming_comp)
  also have \<open>\<dots> = Renaming P id id\<close>
    by (metis bij_betw_def surj_iff \<open>bij f\<close> \<open>bij g\<close>)
  also have \<open>\<dots> = P\<close> by (fact Renaming_id)
  finally show \<open>Renaming (Renaming P (inv f) (inv g)) f g = P\<close> .
qed


(*<*)
end
  (*>*)
