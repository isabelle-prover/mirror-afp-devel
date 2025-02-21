(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSPM - Architectural operators for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff.
 *
 * This file       : Laws for architectural operators
 *
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

section \<open>Results for Throw\<close>
(*<*)
theory CSPM_Laws
  imports Global_Deterministic_Choice Multi_Synchronization_Product
    Multi_Sequential_Composition Interrupt Throw
begin
(*>*)


subsection \<open>Laws for Throw\<close>

lemma Throw_GlobalDet :
  \<open>(\<box> a \<in> A. P a) \<Theta> b \<in> B. Q b = \<box> a \<in> A. P a \<Theta> b \<in> B. Q b\<close> (is \<open>?lhs = ?rhs\<close>)
proof (rule Process_eq_optimizedI)
  show \<open>t \<in> \<D> ?lhs \<Longrightarrow> t \<in> \<D> ?rhs\<close> for t
    by (simp add: D_Throw GlobalDet_projs split: if_split_asm) blast
next
  show \<open>t \<in> \<D> ?rhs \<Longrightarrow> t \<in> \<D> ?lhs\<close> for t
    by (simp add: D_Throw GlobalDet_projs) (meson empty_iff)
next
  fix t X assume \<open>(t, X) \<in> \<F> ?lhs\<close> \<open>t \<notin> \<D> ?lhs\<close>
  then consider \<open>(t, X) \<in> \<F> (\<box>a \<in> A. P a)\<close> \<open>set t \<inter> ev ` B = {}\<close>
    | (failR) t1 b t2 where \<open>t = t1 @ ev b # t2\<close> \<open>t1 @ [ev b] \<in> \<T> (\<box>a \<in> A. P a)\<close>
      \<open>set t1 \<inter> ev ` B = {}\<close> \<open>b \<in> B\<close> \<open>(t2, X) \<in> \<F> (Q b)\<close>
    unfolding Throw_projs by blast
  thus \<open>(t, X) \<in> \<F> ?rhs\<close>
  proof cases
    show \<open>(t, X) \<in> \<F> (\<box>a \<in> A. P a) \<Longrightarrow> set t \<inter> ev ` B = {} \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close>
      by (cases t) (auto simp add: F_GlobalDet Throw_projs)
  next
    case failR
    from failR(2) obtain a where \<open>a \<in> A\<close> \<open>t1 @ [ev b] \<in> \<T> (P a)\<close>
      by (auto simp add: T_GlobalDet split: if_split_asm)
    with failR(3-5) show \<open>(t, X) \<in> \<F> ?rhs\<close>
      by (simp add: F_GlobalDet F_Throw failR(1)) blast
  qed
next
  fix t X assume \<open>(t, X) \<in> \<F> ?rhs\<close> \<open>t \<notin> \<D> ?rhs\<close>
  then consider \<open>t = []\<close> \<open>\<forall>a\<in>A. (t, X) \<in> \<F> (P a \<Theta> b \<in> B. Q b)\<close>
    | a where \<open>a \<in> A\<close> \<open>t \<noteq> []\<close> \<open>(t, X) \<in> \<F> (P a \<Theta> b \<in> B. Q b)\<close>
    | a r where \<open>a \<in> A\<close> \<open>t = []\<close> \<open>\<checkmark>(r) \<notin> X\<close> \<open>[\<checkmark>(r)] \<in> \<T> (P a \<Theta> b \<in> B. Q b)\<close>
    by (auto simp add: GlobalDet_projs)
  thus \<open>(t, X) \<in> \<F> ?lhs\<close>
  proof cases
    show \<open>t = [] \<Longrightarrow> \<forall>a\<in>A. (t, X) \<in> \<F> (P a \<Theta> b \<in> B. Q b) \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close>
      by (auto simp add: F_Throw F_GlobalDet)
  next
    show \<open>a \<in> A \<Longrightarrow> t \<noteq> [] \<Longrightarrow> (t, X) \<in> \<F> (P a \<Theta> b \<in> B. Q b) \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for a
      by (simp add: F_Throw GlobalDet_projs) (metis empty_iff)
  next
    show \<open>\<lbrakk>a \<in> A; t = []; \<checkmark>(r) \<notin> X; [\<checkmark>(r)] \<in> \<T> (P a \<Theta> b \<in> B. Q b)\<rbrakk> \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for a r
      by (simp add: Throw_projs F_GlobalDet Cons_eq_append_conv) (metis is_processT9_tick)
  qed
qed


lemma Throw_GlobalNdetR :
  \<open>P \<Theta> a \<in> A. \<sqinter>b \<in> B. Q a b =
   (if B = {} then P \<Theta> a \<in> A. STOP else \<box>b \<in> B. P \<Theta> a \<in> A. Q a b)\<close>
  (is \<open>?lhs = (if _ then _ else ?rhs)\<close>)
proof (split if_split, intro conjI impI)
  show \<open>B = {} \<Longrightarrow> ?lhs = P \<Theta> a \<in> A. STOP\<close> by simp
next
  show \<open>?lhs = ?rhs\<close> if \<open>B \<noteq> {}\<close>
  proof (subst Process_eq_spec, safe)
    show \<open>t \<in> \<D> ?lhs \<Longrightarrow> t \<in> \<D> ?rhs\<close> for t
      by (auto simp add: \<open>B \<noteq> {}\<close> D_Throw D_GlobalNdet D_GlobalDet)
  next
    show \<open>t \<in> \<D> ?rhs \<Longrightarrow> t \<in> \<D> ?lhs\<close> for t
      by (auto simp add: \<open>B \<noteq> {}\<close> D_Throw D_GlobalNdet D_GlobalDet)
  next
    show \<open>(t, X) \<in> \<F> ?lhs \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> for t X
      by (cases t) (auto simp add: \<open>B \<noteq> {}\<close> F_Throw F_GlobalNdet F_GlobalDet)
  next
    show \<open>(t, X) \<in> \<F> ?rhs \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for t X
      by (auto simp add: \<open>B \<noteq> {}\<close> Throw_projs F_GlobalNdet F_GlobalDet D_T
          is_processT7 Cons_eq_append_conv intro!: is_processT6_TR_notin)
  qed
qed


corollary Throw_Det : \<open>P \<box> P' \<Theta> a \<in> A. Q a = (P \<Theta> a \<in> A. Q a) \<box> (P' \<Theta> a \<in> A. Q a)\<close>
proof -
  have \<open>P \<box> P' \<Theta> a \<in> A. Q a = (\<box>a\<in>{0 :: nat, 1}. (if a = 0 then P else P')) \<Theta> a \<in> A. Q a\<close>
    by (simp add: GlobalDet_distrib_unit)
  also have \<open>\<dots> = \<box>a\<in>{0 :: nat, 1}. (if a = 0 then P else P') \<Theta> a \<in> A. Q a\<close>
    by (fact Throw_GlobalDet)
  also have \<open>\<dots> = (P \<Theta> a \<in> A. Q a) \<box> (P' \<Theta> a \<in> A. Q a)\<close>
    by (simp add: GlobalDet_distrib_unit)
  finally show ?thesis .
qed

corollary Throw_NdetR : \<open>P \<Theta> a \<in> A. Q a \<sqinter> Q' a = (P \<Theta> a \<in> A. Q a) \<box> (P \<Theta> a \<in> A. Q' a)\<close>
proof -
  have \<open>P \<Theta> a \<in> A. Q a \<sqinter> Q' a = P \<Theta> a \<in> A. \<sqinter>b \<in> {0 :: nat, 1}. (if b = 0 then Q a else Q' a)\<close>
    by (simp add: GlobalNdet_distrib_unit)
  also have \<open>\<dots> = \<box>b \<in> {0 :: nat, 1}. P \<Theta> a \<in> A. (if b = 0 then Q a else Q' a)\<close>
    by (simp add: Throw_GlobalNdetR)
  also have \<open>\<dots> = (P \<Theta> a \<in> A. Q a) \<box> (P \<Theta> a \<in> A. Q' a)\<close>
    by (simp add: GlobalDet_distrib_unit)
  finally show ?thesis .
qed



subsection \<open>Laws for Sync\<close>

lemma Sync_GlobalNdet_cartprod:
  \<open>(\<sqinter> (a, b) \<in> A \<times> B. (P a \<lbrakk>S\<rbrakk> Q b)) = 
   (if A = {} \<or> B = {} then STOP else (\<sqinter>a \<in> A. P a) \<lbrakk>S\<rbrakk> (\<sqinter>b \<in> B. Q b))\<close>  
  by (simp add: GlobalNdet_cartprod Sync_distrib_GlobalNdet_left
      Sync_distrib_GlobalNdet_right GlobalNdet_sets_commute[of A])


lemmas Inter_GlobalNdet_cartprod = Sync_GlobalNdet_cartprod[where S = \<open>{}\<close>]
  and   Par_GlobalNdet_cartprod = Sync_GlobalNdet_cartprod[where S = UNIV]



lemma MultiSync_Hiding_pseudo_distrib:
  \<open>finite A \<Longrightarrow> A \<inter> S = {} \<Longrightarrow> (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> p \<in># M. (P p \ A)) = (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> p \<in># M. P p) \ A\<close>
  by (induct M, simp) (metis MultiSync_add MultiSync_rec1 Hiding_Sync)


lemma MultiSync_prefix_pseudo_distrib:
  \<open>M \<noteq> {#} \<Longrightarrow> a \<in> S \<Longrightarrow> (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> p \<in># M. (a \<rightarrow> P p)) = (a \<rightarrow> (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> p \<in># M. P p))\<close>
  by (induct M rule: mset_induct_nonempty) 
    (simp_all add: write0_Sync_write0_subset)

lemmas MultiInter_Hiding_pseudo_distrib =
  MultiSync_Hiding_pseudo_distrib[where S = \<open>{}\<close>, simplified]
  and MultiPar_prefix_pseudo_distrib =
  MultiSync_prefix_pseudo_distrib[where S = \<open>UNIV\<close>, simplified]


text \<open>A result on Mndetprefix and Sync.\<close>

lemma Mndetprefix_Sync_distr: \<open>A \<noteq> {} \<Longrightarrow> B \<noteq> {} \<Longrightarrow> 
       (\<sqinter> a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk> (\<sqinter> b \<in> B \<rightarrow> Q b) =
        \<sqinter> a\<in>A. \<sqinter> b\<in>B. (\<box>c \<in> ({a} - S) \<rightarrow> (P a \<lbrakk>S\<rbrakk> (b \<rightarrow> Q b))) \<box> 
                       (\<box>d \<in> ({b} - S) \<rightarrow> ((a \<rightarrow> P a) \<lbrakk>S\<rbrakk> Q b)) \<box>
                       (\<box>c\<in>({a} \<inter> {b} \<inter> S) \<rightarrow> (P a \<lbrakk>S\<rbrakk> Q b))\<close>
  apply (subst (1 2) Mndetprefix_GlobalNdet) 
  apply (subst Sync_distrib_GlobalNdet_right, simp)
  apply (subst Sync_commute)
  apply (subst Sync_distrib_GlobalNdet_right, simp)
  apply (subst Sync_commute)
  apply (unfold write0_def)
  apply (subst Mprefix_Sync_Mprefix)
  by (fold write0_def, rule refl)

lemma \<open>A \<noteq> {} \<Longrightarrow> B \<noteq> {} \<Longrightarrow> (\<sqinter> a \<in> A \<rightarrow> P a) \<lbrakk>S\<rbrakk> (\<sqinter> b \<in> B \<rightarrow> Q b) =
        \<sqinter> a\<in>A. \<sqinter> b\<in>B. (if a \<in> S then STOP else (a \<rightarrow> (P a \<lbrakk>S\<rbrakk> (b \<rightarrow> Q b)))) \<box> 
                       (if b \<in> S then STOP else (b \<rightarrow> ((a \<rightarrow> P a) \<lbrakk>S\<rbrakk> Q b))) \<box>
                       (if a = b \<and> a \<in> S then (a \<rightarrow> (P a \<lbrakk>S\<rbrakk> Q a)) else STOP)\<close>
  apply (subst Mndetprefix_Sync_distr, assumption+)
  apply (intro mono_GlobalNdet_eq)
  apply (intro arg_cong2[where f = \<open>(\<box>)\<close>])
  by (simp_all add: Mprefix_singl insert_Diff_if Int_insert_left)





subsection \<open>GlobalDet, GlobalNdet and write0\<close>

lemma GlobalDet_write0_is_GlobalNdet_write0:
  \<open>(\<box> p \<in> A. (a \<rightarrow> P p)) = \<sqinter> p \<in> A. (a \<rightarrow> P p)\<close> (is \<open>?lhs = ?rhs\<close>)
proof (subst Process_eq_spec, safe)
  show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close>
    and \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ?lhs\<close> for s
    by (simp_all add: D_GlobalDet write0_def D_Mprefix D_GlobalNdet)
next
  show \<open>(s, X) \<in> \<F> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
    and \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for s X
    by (auto simp add: F_GlobalDet write0_def F_Mprefix F_GlobalNdet split: if_split_asm)
qed    

lemma write0_GlobalNdet_bis:
  \<open>A \<noteq> {} \<Longrightarrow> (a \<rightarrow> (\<sqinter> p \<in> A. P p) = \<box> p \<in> A. (a \<rightarrow> P p))\<close>
  by (simp add: GlobalDet_write0_is_GlobalNdet_write0 write0_GlobalNdet)






section \<open>Some Results on Renaming\<close>

(* TODO: useful ? and rename *)
lemma Renaming_GlobalNdet:
  \<open>Renaming (\<sqinter> a \<in> A. P (f a)) f g = \<sqinter> b \<in> f ` A. Renaming (P b) f g\<close>
  by (metis Renaming_distrib_GlobalNdet mono_GlobalNdet_eq2)

lemma Renaming_GlobalNdet_inj_on:
  \<open>Renaming (\<sqinter> a \<in> A. P a) f g =
   \<sqinter> b \<in> f ` A. Renaming (P (THE a. a \<in> A \<and> f a = b)) f g\<close>
  if inj_on_f: \<open>inj_on f A\<close>
  by (smt (verit, ccfv_SIG) Renaming_distrib_GlobalNdet inj_on_def mono_GlobalNdet_eq2 that the_equality)

corollary Renaming_GlobalNdet_inj:
  \<open>Renaming (\<sqinter> a \<in> A. P a) f g =
   \<sqinter> b \<in> f ` A. Renaming (P (THE a. f a = b)) f g\<close> if inj_f: \<open>inj f\<close>
  apply (subst Renaming_GlobalNdet_inj_on, metis inj_eq inj_onI inj_f)
  apply (rule mono_GlobalNdet_eq[rule_format])
  by (metis imageE inj_eq[OF inj_f])


lemma Renaming_distrib_GlobalDet :
  \<open>Renaming (\<box>a \<in> A. P a) f g = \<box>a \<in> A. Renaming (P a) f g\<close> (is \<open>?lhs = ?rhs\<close>)
proof (subst Process_eq_spec_optimized, safe)
  show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close>
    and \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ?lhs\<close> for s
    by (auto simp add: D_Renaming D_GlobalDet)
next
  assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
  fix s X assume \<open>(s, X) \<in> \<F> ?lhs\<close>
  then consider \<open>s \<in> \<D> ?lhs\<close>
    | t where \<open>s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t\<close> \<open>(t, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (\<box>a \<in> A. P a)\<close>
    unfolding Renaming_projs by blast
  thus \<open>(s, X) \<in> \<F> ?rhs\<close>
  proof cases
    from same_div D_F show \<open>s \<in> \<D> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> by blast
  next
    show \<open>s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t \<Longrightarrow> (t, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (\<box>a \<in> A. P a)
          \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for t
      by (cases t; simp add: F_GlobalDet Renaming_projs)
        (force, metis list.simps(9))
  qed
next
  assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
  fix s X assume \<open>(s, X) \<in> \<F> ?rhs\<close>
  then consider \<open>s = []\<close> \<open>\<forall>a\<in>A. (s, X) \<in> \<F> (Renaming (P a) f g)\<close>
    | a where \<open>a \<in> A\<close> \<open>s \<noteq> []\<close> \<open>(s, X) \<in> \<F> (Renaming (P a) f g)\<close>
    | a where \<open>a \<in> A\<close> \<open>s = []\<close> \<open>s \<in> \<D> (Renaming (P a) f g)\<close>
    | a r where \<open>a \<in> A\<close> \<open>s = []\<close> \<open>\<checkmark>(r) \<notin> X\<close> \<open>[\<checkmark>(r)] \<in> \<T> (Renaming (P a) f g)\<close>
    unfolding F_GlobalDet by blast
  thus \<open>(s, X) \<in> \<F> ?lhs\<close>
  proof cases
    show \<open>s = [] \<Longrightarrow> \<forall>a\<in>A. (s, X) \<in> \<F> (Renaming (P a) f g) \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
      by (auto simp add: F_Renaming F_GlobalDet)
  next
    show \<open>a \<in> A \<Longrightarrow> s \<noteq> [] \<Longrightarrow> (s, X) \<in> \<F> (Renaming (P a) f g) \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for a
      by (simp add: F_Renaming GlobalDet_projs) (metis list.simps(8))
  next
    show \<open>a \<in> A \<Longrightarrow> s = [] \<Longrightarrow> s \<in> \<D> (Renaming (P a) f g) \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for a
      by (auto simp add: Renaming_projs D_GlobalDet)
  next
    fix a r assume * : \<open>a \<in> A\<close> \<open>s = []\<close> \<open>\<checkmark>(r) \<notin> X\<close> \<open>[\<checkmark>(r)] \<in> \<T> (Renaming (P a) f g)\<close>
    from "*"(4) consider s1 where \<open>[\<checkmark>(r)] = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1\<close> \<open>s1 \<in> \<T> (P a)\<close>
      | s1 s2 where \<open>[\<checkmark>(r)] = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1 @ s2\<close>
        \<open>tickFree s1\<close> \<open>front_tickFree s2\<close> \<open>s1 \<in> \<D> (P a)\<close>
      by (simp add: T_Renaming) meson
    thus \<open>(s, X) \<in> \<F> ?lhs\<close>
    proof cases
      fix s1 assume \<open>[\<checkmark>(r)] = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1\<close> \<open>s1 \<in> \<T> (P a)\<close>
      from \<open>[\<checkmark>(r)] = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1\<close> obtain r' where \<open>r = g r'\<close> \<open>s1 = [\<checkmark>(r')]\<close>
        by (metis map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_tick_iff)
      with "*"(1, 2, 3) \<open>s1 \<in> \<T> (P a)\<close>
      show \<open>(s, X) \<in> \<F> ?lhs\<close> by (auto simp add: F_Renaming F_GlobalDet)
    next
      fix s1 s2 assume \<open>[\<checkmark>(r)] = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1 @ s2\<close>
        \<open>tickFree s1\<close> \<open>front_tickFree s2\<close> \<open>s1 \<in> \<D> (P a)\<close>
      from \<open>[\<checkmark>(r)] = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1 @ s2\<close> \<open>tickFree s1\<close>
      have \<open>s1 = [] \<and> s2 = [\<checkmark>(r)]\<close>
        by (cases s1; simp) (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(2) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.map_disc_iff(1))
      with "*"(1, 2) \<open>s1 \<in> \<D> (P a)\<close> show \<open>(s, X) \<in> \<F> ?lhs\<close>
        by (auto simp add: F_Renaming F_GlobalDet)
    qed
  qed
qed

lemma Renaming_Mprefix_bis :
  \<open>Renaming (\<box>a \<in> A \<rightarrow> P a) f g = \<box>a \<in> A. (f a \<rightarrow> Renaming (P a) f g)\<close>
  by (simp add: Mprefix_GlobalDet Renaming_distrib_GlobalDet Renaming_write0)


(* TODO : useful ? *)
lemma Renaming_GlobalDet_alt:
  \<open>Renaming (\<box> a \<in> A. P (f a)) f g = \<box> b \<in> f ` A. Renaming (P b) f g\<close>
  (is \<open>?lhs = ?rhs\<close>)
  by (simp add: Renaming_distrib_GlobalDet mono_GlobalDet_eq2)


lemma Renaming_GlobalDet_inj_on:
  \<open>inj_on f A \<Longrightarrow> Renaming (\<box> a \<in> A. P a) f g =
   \<box> b \<in> f ` A. Renaming (P (THE a. a \<in> A \<and> f a = b)) f g\<close>
  by (simp add: Renaming_distrib_GlobalDet inj_on_def mono_GlobalDet_eq2 the_equality)


corollary Renaming_GlobalDet_inj:
  \<open>inj f \<Longrightarrow> Renaming (\<box> a \<in> A. P a) f g = \<box> b \<in> f ` A. Renaming (P (THE a. f a = b)) f g\<close>
  by (subst Renaming_GlobalDet_inj_on, metis inj_eq inj_onI)
    (rule mono_GlobalDet_eq, metis imageE inj_eq)


lemma Renaming_Interrupt :
  \<open>Renaming (P \<triangle> Q) f g = Renaming P f g \<triangle> Renaming Q f g\<close> (is \<open>?lhs = ?rhs\<close>)
proof (subst Process_eq_spec_optimized, safe)
  fix t assume \<open>t \<in> \<D> ?lhs\<close>
  then obtain t1 t2
    where * : \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1 @ t2\<close> \<open>tF t1\<close> \<open>ftF t2\<close> \<open>t1 \<in> \<D> (P \<triangle> Q)\<close>
    unfolding D_Renaming by blast
  from "*"(4) consider \<open>t1 \<in> \<D> P\<close>
    | u1 u2 where \<open>t1 = u1 @ u2\<close> \<open>u1 \<in> \<T> P\<close> \<open>tF u1\<close> \<open>u2 \<in> \<D> Q\<close>
    unfolding D_Interrupt by blast
  thus \<open>t \<in> \<D> ?rhs\<close>
  proof cases
    from "*"(1-3) show \<open>t1 \<in> \<D> P \<Longrightarrow> t \<in> \<D> ?rhs\<close>
      by (auto simp add: D_Interrupt D_Renaming)
  next
    show \<open>t1 = u1 @ u2 \<Longrightarrow> u1 \<in> \<T> P \<Longrightarrow> tF u1 \<Longrightarrow> u2 \<in> \<D> Q \<Longrightarrow> t \<in> \<D> ?rhs\<close> for u1 u2
      by (simp add: D_Interrupt Renaming_projs "*"(1))
        (metis "*"(2, 3) map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree tickFree_append_iff)
  qed
next
  fix t assume \<open>t \<in> \<D> ?rhs\<close>
  then consider \<open>t \<in> \<D> (Renaming P f g)\<close>
    | t1 t2 where \<open>t = t1 @ t2\<close> \<open>t1 \<in> \<T> (Renaming P f g)\<close> \<open>tF t1\<close> \<open>t2 \<in> \<D> (Renaming Q f g)\<close>
    unfolding D_Interrupt by blast
  thus \<open>t \<in> \<D> ?lhs\<close>
  proof cases
    show \<open>t \<in> \<D> (Renaming P f g) \<Longrightarrow> t \<in> \<D> ?lhs\<close>
      by (auto simp add: D_Renaming D_Interrupt)
  next
    show \<open>t = t1 @ t2 \<Longrightarrow> t1 \<in> \<T> (Renaming P f g) \<Longrightarrow> tF t1 \<Longrightarrow> t2 \<in> \<D> (Renaming Q f g) \<Longrightarrow> t \<in> \<D> ?lhs\<close> for t1 t2
      by (auto simp add: Renaming_projs D_Interrupt append.assoc map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree)
        (metis (no_types, opaque_lifting) append.assoc map_append tickFree_append_iff,
          metis front_tickFree_append map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree)
  qed
next
  fix t X assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
  assume \<open>(t, X) \<in> \<F> ?lhs\<close>
  then consider \<open>t \<in> \<D> ?lhs\<close>
    | u where \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u\<close> \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (P \<triangle> Q)\<close>
    unfolding Renaming_projs by blast
  thus \<open>(t, X) \<in> \<F> ?rhs\<close>
  proof cases
    from same_div D_F show \<open>t \<in> \<D> ?lhs \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> by blast
  next
    fix u assume * : \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u\<close> \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (P \<triangle> Q)\<close>
    from "*"(2) consider \<open>u \<in> \<D> (P \<triangle> Q)\<close>
      | u' r  where \<open>u = u' @ [\<checkmark>(r)]\<close> \<open>u' @ [\<checkmark>(r)] \<in> \<T> P\<close>
      | X' r  where \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X = X' - {\<checkmark>(r)}\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close>
      | \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> P\<close> \<open>tF u\<close> \<open>([], map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> Q\<close>
      | u1 u2 where \<open>u = u1 @ u2\<close> \<open>u1 \<in> \<T> P\<close> \<open>tF u1\<close> \<open>(u2, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> Q\<close> \<open>u2 \<noteq> []\<close>
      | X' r  where \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X = X' - {\<checkmark>(r)}\<close> \<open>u \<in> \<T> P\<close> \<open>tF u\<close> \<open>[\<checkmark>(r)] \<in> \<T> Q\<close>
      unfolding Interrupt_projs by safe auto
    thus \<open>(t, X) \<in> \<F> ?rhs\<close>
    proof cases
      assume \<open>u \<in> \<D> (P \<triangle> Q)\<close>
      hence \<open>t \<in> \<D> ?lhs\<close>
        by (simp add: "*"(1) D_Renaming)
          (metis (no_types, opaque_lifting) D_imp_front_tickFree append_Nil2 snoc_eq_iff_butlast
            butlast.simps(1) div_butlast_when_non_tickFree_iff front_tickFree_Nil
            front_tickFree_iff_tickFree_butlast front_tickFree_single map_butlast)
      with same_div D_F show \<open>(t, X) \<in> \<F> ?rhs\<close> by blast
    next
      show \<open>u = u' @ [\<checkmark>(r)] \<Longrightarrow> u' @ [\<checkmark>(r)] \<in> \<T> P \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> for u' r
        by (auto simp add: "*"(1) F_Interrupt T_Renaming)
    next
      fix X' r assume ** : \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X = X' - {\<checkmark>(r)}\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close>
      from "**" obtain X'' where \<open>X = X'' - {\<checkmark>(g r)}\<close>
        by (metis DiffD2 Diff_insert_absorb event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(10) insertI1 vimage_eq)
      moreover from "**"(2) have \<open>t @ [\<checkmark>(g r)] \<in> \<T> (Renaming P f g)\<close>
        by (auto simp add: "*"(1) T_Renaming)
      ultimately show \<open>(t, X) \<in> \<F> ?rhs\<close> by (auto simp add: F_Interrupt)
    next
      show \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> P \<Longrightarrow> tF u \<Longrightarrow>
            ([], map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> Q \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close>
        using map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree by (auto simp add: "*"(1) F_Interrupt F_Renaming)
    next
      fix u1 u2 assume \<open>u = u1 @ u2\<close> \<open>u1 \<in> \<T> P\<close> \<open>tF u1\<close>
        \<open>(u2, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> Q\<close> \<open>u2 \<noteq> []\<close>
      hence \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1 @ map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u2\<close>
        \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1 \<in> \<T> (Renaming P f g)\<close>
        \<open>tF (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1)\<close>
        \<open>(map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u2, X) \<in> \<F> (Renaming Q f g)\<close>
        \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u2 \<noteq> []\<close>
        by (auto simp add: "*"(1) Renaming_projs map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree)
      thus \<open>(t, X) \<in> \<F> ?rhs\<close> by (simp add: F_Interrupt) blast
    next
      fix X' r assume ** : \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X = X' - {\<checkmark>(r)}\<close> \<open>u \<in> \<T> P\<close> \<open>tF u\<close> \<open>[\<checkmark>(r)] \<in> \<T> Q\<close>
      from "**"(1, 2) obtain X'' where \<open>X = X'' - {\<checkmark>(g r)}\<close>
        by (metis DiffD2 Diff_insert_absorb event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(10) insertI1 vimage_eq)
      moreover from "**"(2-4) have \<open>t \<in> \<T> (Renaming P f g)\<close> \<open>tF t\<close>
        \<open>[\<checkmark>(g r)] \<in> \<T> (Renaming Q f g)\<close>
        by (auto simp add: "*"(1) T_Renaming map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree)
      ultimately show \<open>(t, X) \<in> \<F> ?rhs\<close> by (simp add: F_Interrupt) blast
    qed
  qed
next
  fix t X assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
  assume \<open>(t, X) \<in> \<F> ?rhs\<close>
  then consider \<open>t \<in> \<D> ?rhs\<close>
    | t' s  where \<open>t = t' @ [\<checkmark>(s)]\<close> \<open>t' @ [\<checkmark>(s)] \<in> \<T> (Renaming P f g)\<close>
    | X' s  where \<open>X = X' - {\<checkmark>(s)}\<close> \<open>t  @ [\<checkmark>(s)] \<in> \<T> (Renaming P f g)\<close>
    | \<open>(t, X) \<in> \<F> (Renaming P f g)\<close> \<open>tF t\<close> \<open>([], X) \<in> \<F> (Renaming Q f g)\<close>
    | t1 t2 where \<open>t = t1 @ t2\<close> \<open>t1 \<in> \<T> (Renaming P f g)\<close> \<open>tF t1\<close>
      \<open>(t2, X) \<in> \<F> (Renaming Q f g)\<close> \<open>t2 \<noteq> []\<close>
    | X' s where \<open>X = X' - {\<checkmark>(s)}\<close> \<open>t \<in> \<T> (Renaming P f g)\<close> \<open>tF t\<close> \<open>[\<checkmark>(s)] \<in> \<T> (Renaming Q f g)\<close>
    by (simp add: Interrupt_projs) blast
  thus \<open>(t, X) \<in> \<F> ?lhs\<close>
  proof cases
    from same_div D_F show \<open>t \<in> \<D> ?rhs \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> by blast
  next
    show \<open>\<lbrakk>t = t' @ [\<checkmark>(s)]; t' @ [\<checkmark>(s)] \<in> \<T> (Renaming P f g)\<rbrakk> \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for t' s
      by (simp add: Renaming_projs Interrupt_projs)
        (metis T_nonTickFree_imp_decomp map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree non_tickFree_tick tickFree_append_iff)
  next
    fix X' s assume * : \<open>X = X' - {\<checkmark>(s)}\<close> \<open>t @ [\<checkmark>(s)] \<in> \<T> (Renaming P f g)\<close>
    from "*"(2) consider u1 u2 where
      \<open>t @ [\<checkmark>(s)] = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1 @ u2\<close> \<open>tF u1\<close> \<open>ftF u2\<close> \<open>u1 \<in> \<D> P\<close>
    | u r where \<open>s = g r\<close> \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close>
      by (simp add: T_Renaming)
        (metis (no_types, opaque_lifting) T_nonTickFree_imp_decomp event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(4)
          event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.map_sel(2) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.sel(2) last_map map_butlast map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree
          non_tickFree_tick snoc_eq_iff_butlast tickFree_append_iff)
    thus \<open>(t, X) \<in> \<F> ?lhs\<close>
    proof cases
      fix u1 u2 assume \<open>t @ [\<checkmark>(s)] = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1 @ u2\<close> \<open>tF u1\<close> \<open>ftF u2\<close> \<open>u1 \<in> \<D> P\<close>
      hence \<open>t \<in> \<D> ?lhs\<close>
        by (cases u2 rule: rev_cases)
          (auto simp add: D_Interrupt D_Renaming intro: front_tickFree_dw_closed,
            metis map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree non_tickFree_tick tickFree_append_iff)
      with D_F show \<open>(t, X) \<in> \<F> ?lhs\<close> by blast
    next
      fix u r assume \<open>s = g r\<close> \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u\<close> \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close>
      moreover from "*"(1) \<open>s = g r\<close> obtain X'' where \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X = X'' - {\<checkmark>(r)}\<close>
        by (metis Diff_iff Diff_insert_absorb event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(10) vimage_eq vimage_singleton_eq)
      ultimately show \<open>(t, X) \<in> \<F> ?lhs\<close> by (simp add: F_Renaming F_Interrupt) metis
    qed
  next
    show \<open>\<lbrakk>(t, X) \<in> \<F> (Renaming P f g); tF t; ([], X) \<in> \<F> (Renaming Q f g)\<rbrakk> \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close>
      by (simp add: Renaming_projs Interrupt_projs)
        (metis is_processT8 map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree)
  next
    fix t1 t2 assume * : \<open>t = t1 @ t2\<close> \<open>t1 \<in> \<T> (Renaming P f g)\<close> \<open>tF t1\<close>
      \<open>(t2, X) \<in> \<F> (Renaming Q f g)\<close> \<open>t2 \<noteq> []\<close>
    from "*"(2) consider u1 u2 where
      \<open>t1 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1 @ u2\<close> \<open>tF u1\<close> \<open>ftF u2\<close> \<open>u1 \<in> \<D> P\<close>
    | u1 where \<open>t1 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1\<close> \<open>u1 \<in> \<T> P\<close>
      unfolding T_Renaming by blast
    thus \<open>(t, X) \<in> \<F> ?lhs\<close>
    proof cases
      fix u1 u2 assume \<open>t1 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1 @ u2\<close> \<open>tF u1\<close> \<open>ftF u2\<close> \<open>u1 \<in> \<D> P\<close>
      hence \<open>t1 \<in> \<D> ?lhs\<close> by (auto simp add: D_Interrupt D_Renaming)
      with "*"(1, 3, 4) F_imp_front_tickFree is_processT7 have \<open>t \<in> \<D> ?lhs\<close> by blast
      with D_F show \<open>(t, X) \<in> \<F> ?lhs\<close> by blast
    next
      fix u1 assume ** : \<open>t1 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1\<close> \<open>u1 \<in> \<T> P\<close>
      from "*"(4) consider u2 u3 where
        \<open>t2 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u2 @ u3\<close> \<open>tF u2\<close> \<open>ftF u3\<close> \<open>u2 \<in> \<D> Q\<close>
      | u2 where \<open>t2 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u2\<close> \<open>(u2, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> Q\<close>
        unfolding F_Renaming by blast
      thus \<open>(t, X) \<in> \<F> ?lhs\<close>
      proof cases
        fix u2 u3 assume \<open>t2 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u2 @ u3\<close> \<open>tF u2\<close> \<open>ftF u3\<close> \<open>u2 \<in> \<D> Q\<close>
        hence \<open>t \<in> \<D> ?lhs\<close>
          by (simp add: "*"(1) "**"(1) D_Renaming D_Interrupt flip: map_append append.assoc)
            (metis "*"(3) "**"(1, 2) map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree tickFree_append_iff)
        with D_F show \<open>(t, X) \<in> \<F> ?lhs\<close> by blast
      next
        show \<open>t2 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u2 \<Longrightarrow> (u2, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> Q
              \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for u2
          by (simp add: F_Renaming F_Interrupt "*"(1) "**"(1) flip: map_append)
            (metis "*"(3, 5) "**"(1, 2) list.map_disc_iff map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree)
      qed
    qed
  next
    fix X' s assume * : \<open>X = X' - {\<checkmark>(s)}\<close> \<open>t \<in> \<T> (Renaming P f g)\<close>
      \<open>tF t\<close> \<open>[\<checkmark>(s)] \<in> \<T> (Renaming Q f g)\<close>
    from "*"(2) consider u1 u2 where
      \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1 @ u2\<close> \<open>tF u1\<close> \<open>ftF u2\<close> \<open>u1 \<in> \<D> P\<close>
    | u where \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u\<close> \<open>u \<in> \<T> P\<close>
      by (auto simp add: T_Renaming)
    thus \<open>(t, X) \<in> \<F> ?lhs\<close>
    proof cases
      fix u1 u2 assume \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1 @ u2\<close> \<open>tF u1\<close> \<open>ftF u2\<close> \<open>u1 \<in> \<D> P\<close>
      hence \<open>t \<in> \<D> ?lhs\<close> by (auto simp add: D_Interrupt D_Renaming)
      with D_F show \<open>(t, X) \<in> \<F> ?lhs\<close> by blast
    next
      fix u assume ** : \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u\<close> \<open>u \<in> \<T> P\<close>
      from "*"(4) consider \<open>Renaming Q f g = \<bottom>\<close> | r where \<open>s = g r\<close> \<open>[\<checkmark>(r)] \<in> \<T> Q\<close>
        by (simp add: Renaming_projs BOT_iff_tick_D)
          (metis map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_tick_iff)
      thus \<open>(t, X) \<in> \<F> ?lhs\<close>
      proof cases
        assume \<open>Renaming Q f g = \<bottom>\<close>
        hence \<open>Q = \<bottom>\<close> by (simp add: Renaming_is_BOT_iff)
        hence \<open>Renaming (P \<triangle> Q) f g = \<bottom>\<close> by simp
        thus \<open>(t, X) \<in> \<F> ?lhs\<close> by (simp add: F_BOT "*"(3))
      next
        fix r assume \<open>s = g r\<close> \<open>[\<checkmark>(r)] \<in> \<T> Q\<close>
        moreover from "*"(1) \<open>s = g r\<close> obtain X''
          where \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X = X'' - {\<checkmark>(r)}\<close>
          by (metis DiffD2 Diff_empty Diff_insert0 event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(10) insertI1 vimage_eq)
        ultimately show \<open>(t, X) \<in> \<F> ?lhs\<close>
          by (simp add: "**"(1) F_Renaming F_Interrupt)
            (metis "*"(3) "**"(1, 2) map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree)
      qed
    qed
  qed
qed


lemma inj_on_Renaming_Throw :
  \<open>Renaming (P \<Theta> a \<in> A. Q a) f g =
   Renaming P f g \<Theta> b \<in> f ` A. Renaming (Q (inv_into A f b)) f g\<close>
  (is \<open>?lhs = ?rhs\<close>) if inj_on_f : \<open>inj_on f (events_of P \<union> A)\<close>
proof -
  have $ : \<open>set (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t) \<inter> ev ` f ` A = {}
            \<longleftrightarrow> set t \<inter> ev ` A = {}\<close> if \<open>t \<in> \<T> P\<close> for t
  proof -
    from \<open>t \<in> \<T> P\<close> inj_on_f have \<open>inj_on f ({a. ev a \<in> set t} \<union> A)\<close>
      by (auto simp add: inj_on_def events_of_memI)
    thus \<open>set (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t) \<inter> ev ` f ` A = {}
          \<longleftrightarrow> set t \<inter> ev ` A = {}\<close>
      by (auto simp add: disjoint_iff image_iff inj_on_def map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_ev_iff)
        (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(9), blast)
  qed
  show \<open>?lhs = ?rhs\<close>
  proof (subst Process_eq_spec_optimized, safe)
    fix t assume \<open>t \<in> \<D> ?lhs\<close>
    then obtain t1 t2 where * : \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1 @ t2\<close> \<open>tF t1\<close>
      \<open>ftF t2\<close> \<open>t1 \<in> \<D> (P \<Theta> a \<in> A. Q a)\<close>
      unfolding D_Renaming by blast
    from "*"(4) consider u1 u2 where \<open>t1 = u1 @ u2\<close> \<open>u1 \<in> \<D> P\<close> \<open>tF u1\<close>
      \<open>set u1 \<inter> ev ` A = {}\<close> \<open>ftF u2\<close>
    | u1 a u2 where \<open>t1 = u1 @ ev a # u2\<close> \<open>u1 @ [ev a] \<in> \<T> P\<close>
      \<open>set u1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>u2 \<in> \<D> (Q a)\<close>
      unfolding D_Throw by blast
    thus \<open>t \<in> \<D> ?rhs\<close>
    proof cases
      fix u1 u2 assume ** : \<open>t1 = u1 @ u2\<close> \<open>u1 \<in> \<D> P\<close> \<open>tF u1\<close>
        \<open>set u1 \<inter> ev ` A = {}\<close> \<open>ftF u2\<close>
      from "$" "**"(2) "**"(4) D_T
      have *** : \<open>set (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1) \<inter> ev ` f ` A = {}\<close> by blast
      have \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1 @ (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u2 @ t2)\<close>
        by (simp add: "*"(1) "**"(1))
      moreover from "*"(2, 3) "**"(1) have \<open>ftF (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u2 @ t2)\<close>
        by (simp add: front_tickFree_append map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree)
      moreover have \<open>tF (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1)\<close>
        by (simp add: "**"(3) map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree)
      ultimately show \<open>t \<in> \<D> ?rhs\<close>
        by (simp add: D_Throw D_Renaming)
          (use "**"(2) "**"(3) "***" front_tickFree_Nil in blast)
    next
      fix u1 a u2 assume ** : \<open>t1 = u1 @ ev a # u2\<close> \<open>u1 @ [ev a] \<in> \<T> P\<close>
        \<open>set u1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>u2 \<in> \<D> (Q a)\<close>
      have *** : \<open>set (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1) \<inter> ev ` f ` A = {}\<close>
        by (meson "$" "**"(2) "**"(3) T_F_spec is_processT3)
      have \<open>tF u2\<close> using "*"(2) "**"(1) by auto
      moreover have \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1 @ ev (f a) # map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u2 @ t2\<close>
        by (simp add: "*"(1) "**"(1))
      moreover from "**"(2) have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1 @ [ev (f a)] \<in> \<T> (Renaming P f g)\<close>
        by (auto simp add: T_Renaming )
      moreover have \<open>inv_into A f (f a) = a\<close>
        by (meson "**"(4) inj_on_Un inv_into_f_eq inj_on_f)
      ultimately show \<open>t \<in> \<D> ?rhs\<close>
        by (simp add: D_Throw D_Renaming)
          (metis "*"(3) "**"(4) "**"(5) "***" imageI)
    qed
  next
    fix t assume \<open>t \<in> \<D> ?rhs\<close>
    then consider t1 t2 where \<open>t = t1 @ t2\<close> \<open>t1 \<in> \<D> (Renaming P f g)\<close>
      \<open>tF t1\<close> \<open>set t1 \<inter> ev ` f ` A = {}\<close> \<open>ftF t2\<close>
    | t1 b t2 where \<open>t = t1 @ ev b # t2\<close> \<open>t1 @ [ev b] \<in> \<T> (Renaming P f g)\<close>
      \<open>set t1 \<inter> ev ` f ` A = {}\<close> \<open>b \<in> f ` A\<close>
      \<open>t2 \<in> \<D> (Renaming (Q (inv_into A f b)) f g)\<close>
      unfolding D_Throw by blast
    thus \<open>t \<in> \<D> ?lhs\<close>
    proof cases
      fix t1 t2 assume * : \<open>t = t1 @ t2\<close> \<open>t1 \<in> \<D> (Renaming P f g)\<close>
        \<open>tF t1\<close> \<open>set t1 \<inter> ev ` f ` A = {}\<close> \<open>ftF t2\<close>
      from "*"(2) obtain u1 u2
        where ** : \<open>t1 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1 @ u2\<close> \<open>tF u1\<close> \<open>ftF u2\<close> \<open>u1 \<in> \<D> P\<close>
        unfolding D_Renaming by blast
      from "*"(4) "**"(1) have \<open>set u1 \<inter> ev ` A = {}\<close> by auto
      moreover have \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1 @ (u2 @ t2)\<close>
        by (simp add: "*"(1) "**"(1))
      moreover from "*"(3, 5) "**"(1) front_tickFree_append tickFree_append_iff
      have \<open>ftF (u2 @ t2)\<close> by blast
      ultimately show \<open>t \<in> \<D> ?lhs\<close>
        by (simp add: D_Renaming D_Throw)
          (use "**"(2, 4) front_tickFree_Nil in blast)
    next
      fix t1 b t2 assume * : \<open>t = t1 @ ev b # t2\<close> \<open>t1 @ [ev b] \<in> \<T> (Renaming P f g)\<close>
        \<open>set t1 \<inter> ev ` f ` A = {}\<close> \<open>b \<in> f ` A\<close>
        \<open>t2 \<in> \<D> (Renaming (Q (inv_into A f b)) f g)\<close>
      from \<open>b \<in> f ` A\<close> obtain a where \<open>a \<in> A\<close> \<open>b = f a\<close> by blast
      hence \<open>inv_into A f b = a\<close> by (meson inj_on_Un inv_into_f_f inj_on_f)
      from "*"(2) consider u1 u2 where
        \<open>t1 @ [ev b] = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1 @ u2\<close> \<open>u2 \<noteq> []\<close> \<open>tF u1\<close> \<open>ftF u2\<close> \<open>u1 \<in> \<D> P\<close>
      | u1 where \<open>t1 @ [ev b] = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1\<close> \<open>u1 \<in> \<T> P\<close>
        by (simp add: D_T T_Renaming)
          (metis (no_types, opaque_lifting) D_T append.right_neutral)
      thus \<open>t \<in> \<D> ?lhs\<close>
      proof cases
        fix u1 u2
        assume ** : \<open>t1 @ [ev b] = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1 @ u2\<close> \<open>u2 \<noteq> []\<close> \<open>tF u1\<close> \<open>ftF u2\<close> \<open>u1 \<in> \<D> P\<close>
        from "**"(1, 2) obtain u2' where *** : \<open>t1 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1 @ u2'\<close>
          by (metis butlast_append butlast_snoc)
        from "*"(3) "***" have **** : \<open>set u1 \<inter> ev ` A = {}\<close> by auto
        have ***** : \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1 @ (u2' @ ev b # t2)\<close> \<open>ftF (u2' @ ev b # t2)\<close>
          by (simp_all add: "*"(1) "***" "****" front_tickFree_append_iff)
            (metis "*"(2, 5) "***" D_imp_front_tickFree append_T_imp_tickFree
              event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) front_tickFree_Cons_iff not_Cons_self tickFree_append_iff)
        show \<open>t \<in> \<D> ?lhs\<close>
          by (simp add: D_Renaming D_Throw)
            (metis "**"(3) "**"(5) "****" "*****" append_Nil2 front_tickFree_Nil)
      next
        fix u1 assume \<open>t1 @ [ev b] = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1\<close> \<open>u1 \<in> \<T> P\<close>
        then obtain u1' where ** : \<open>t1 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1'\<close> \<open>u1' @ [ev a] \<in> \<T> P\<close>
          by (cases u1 rule: rev_cases, simp_all add: \<open>b = f a\<close> ev_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
            (metis Nil_is_append_conv Un_iff \<open>a \<in> A\<close> events_of_memI inj_onD
              inj_on_f last_in_set last_snoc list.distinct(1))
        from "*"(3) "**"(1) have *** : \<open>set u1' \<inter> ev ` A = {}\<close> by auto
        from "*"(5) \<open>inv_into A f b = a\<close> obtain u2 u3 where
          **** : \<open>t2 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u2 @ u3\<close> \<open>tF u2\<close> \<open>ftF u3\<close> \<open>u2 \<in> \<D> (Q a)\<close>
          unfolding Renaming_projs by blast
        have ***** : \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (u1' @ ev a # u2) @ u3\<close> \<open>tF (u1' @ ev a # u2)\<close>
          by (simp_all add: "*"(1) "**"(1) \<open>b = f a\<close> "****"(1))
            (metis "**"(2) "****"(2) T_imp_front_tickFree butlast_snoc
              front_tickFree_iff_tickFree_butlast)
        show \<open>t \<in> \<D> ?lhs\<close>
          by (simp add: D_Renaming D_Throw)
            (metis "**"(2) "***" "****"(3, 4) "*****"(1, 2) \<open>a \<in> A\<close>)
      qed
    qed
  next
    fix t X assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
    assume \<open>(t, X) \<in> \<F> ?lhs\<close>
    then consider \<open>t \<in> \<D> ?lhs\<close>
      | u where \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u\<close> \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (P \<Theta> a \<in> A. Q a)\<close>
      unfolding Renaming_projs by blast
    thus \<open>(t, X) \<in> \<F> ?rhs\<close>
    proof cases
      from same_div D_F show \<open>t \<in> \<D> ?lhs \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> by blast
    next
      fix u assume * : \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u\<close>
        \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (P \<Theta> a \<in> A. Q a)\<close>
      then consider \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> P\<close> \<open>set u \<inter> ev ` A = {}\<close>
        | u1 u2   where \<open>u = u1 @ u2\<close> \<open>u1 \<in> \<D> P\<close> \<open>tF u1\<close> \<open>set u1 \<inter> ev ` A = {}\<close> \<open>ftF u2\<close>
        | u1 a u2 where \<open>u = u1 @ ev a # u2\<close> \<open>u1 @ [ev a] \<in> \<T> P\<close> \<open>set u1 \<inter> ev ` A = {}\<close>
          \<open>a \<in> A\<close> \<open>(u2, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (Q a)\<close>
        unfolding F_Throw by blast
      thus \<open>(t, X) \<in> \<F> ?rhs\<close>
      proof cases
        show \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> P \<Longrightarrow> set u \<inter> ev ` A = {} \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close>
          by (simp add: F_Throw F_Renaming) (metis "$" "*"(1) F_T)
      next
        fix u1 u2 assume \<open>u = u1 @ u2\<close> \<open>u1 \<in> \<D> P\<close> \<open>tF u1\<close> \<open>set u1 \<inter> ev ` A = {}\<close> \<open>ftF u2\<close>
        hence \<open>t \<in> \<D> ?lhs\<close>
          by (simp add: "*"(1) D_Renaming D_Throw)
            (metis append_Nil2 front_tickFree_Nil map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_front_tickFree)
        with same_div D_F show \<open>(t, X) \<in> \<F> ?rhs\<close> by blast
      next
        fix u1 a u2
        assume ** : \<open>u = u1 @ ev a # u2\<close> \<open>u1 @ [ev a] \<in> \<T> P\<close> \<open>set u1 \<inter> ev ` A = {}\<close>
          \<open>a \<in> A\<close> \<open>(u2, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (Q a)\<close>
        have *** : \<open>set (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1) \<inter> ev ` f ` A = {}\<close>
          by (meson "$" "**"(2, 3) T_F_spec is_processT3)
        have \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1 @ ev (f a) # map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u2\<close>
          by (simp add: "*"(1) "**"(1))
        moreover from "**"(2) have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1 @ [ev (f a)] \<in> \<T> (Renaming P f g)\<close>
          by (auto simp add: T_Renaming)
        moreover have \<open>inv_into A f (f a) = a\<close>
          by (meson "**"(4) inj_on_Un inv_into_f_f inj_on_f)
        moreover from "**"(5) have \<open>(map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u2, X) \<in> \<F> (Renaming (Q a) f g)\<close>
          by (auto simp add: F_Renaming)
        ultimately show \<open>(t, X) \<in> \<F> ?rhs\<close>
          by (simp add: F_Throw) (metis "**"(4) "***" image_eqI)
      qed
    qed
  next
    fix t X assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
    assume \<open>(t, X) \<in> \<F> ?rhs\<close>
    then consider \<open>t \<in> \<D> ?rhs\<close>
      | \<open>(t, X) \<in> \<F> (Renaming P f g)\<close> \<open>set t \<inter> ev ` f ` A = {}\<close>
      | t1 b t2 where \<open>t = t1 @ ev b # t2\<close> \<open>t1 @ [ev b] \<in> \<T> (Renaming P f g)\<close>
        \<open>set t1 \<inter> ev ` f ` A = {}\<close> \<open>b \<in> f ` A\<close>
        \<open>(t2, X) \<in> \<F> (Renaming (Q (inv_into A f b)) f g)\<close>
      unfolding Throw_projs by auto
    thus \<open>(t, X) \<in> \<F> ?lhs\<close>
    proof cases
      from same_div D_F show \<open>t \<in> \<D> ?rhs \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> by blast
    next
      assume * : \<open>(t, X) \<in> \<F> (Renaming P f g)\<close> \<open>set t \<inter> ev ` f ` A = {}\<close>
      from "*"(1) consider \<open>t \<in> \<D> (Renaming P f g)\<close>
        | u where \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u\<close> \<open>(u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> P\<close>
        unfolding Renaming_projs by blast
      thus \<open>(t, X) \<in> \<F> ?lhs\<close>
      proof cases
        assume \<open>t \<in> \<D> (Renaming P f g)\<close>
        hence \<open>t \<in> \<D> ?lhs\<close>
          by (simp add: D_Renaming D_Throw)
            (metis (no_types, lifting) "$" "*"(2) D_T Un_Int_eq(3) append_Nil2
              front_tickFree_Nil inf_bot_right inf_sup_aci(2) set_append)
        with D_F show \<open>(t, X) \<in> \<F> ?lhs\<close> by blast
      next
        show \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u \<Longrightarrow> (u, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> P
              \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for u
          by (simp add: F_Renaming F_Throw) (metis "$" "*"(2) F_T)
      qed
    next
      fix t1 b t2
      assume * : \<open>t = t1 @ ev b # t2\<close> \<open>t1 @ [ev b] \<in> \<T> (Renaming P f g)\<close>
        \<open>set t1 \<inter> ev ` f ` A = {}\<close> \<open>b \<in> f ` A\<close>
        \<open>(t2, X) \<in> \<F> (Renaming (Q (inv_into A f b)) f g)\<close>
      from "*"(4) obtain a where \<open>a \<in> A\<close> \<open>b = f a\<close> by blast
      hence \<open>inv_into A f b = a\<close> by (meson inj_on_Un inv_into_f_f inj_on_f)
      from "*"(2) consider u1 u2 where
        \<open>t1 @ [ev b] = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1 @ u2\<close> \<open>u2 \<noteq> []\<close> \<open>tF u1\<close> \<open>ftF u2\<close> \<open>u1 \<in> \<D> P\<close>
      | u1 where \<open>t1 @ [ev b] = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1\<close> \<open>u1 \<in> \<T> P\<close>
        by (simp add: D_T T_Renaming)
          (metis (no_types, opaque_lifting) D_T append.right_neutral)
      thus \<open>(t, X) \<in> \<F> ?lhs\<close>
      proof cases
        fix u1 u2
        assume ** : \<open>t1 @ [ev b] = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1 @ u2\<close> \<open>u2 \<noteq> []\<close> \<open>tF u1\<close> \<open>ftF u2\<close> \<open>u1 \<in> \<D> P\<close>
        from "**"(1, 2) obtain u2' where *** : \<open>t1 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1 @ u2'\<close>
          by (metis butlast_append butlast_snoc)
        from "*"(3) "***" have \<open>set u1 \<inter> ev ` A = {}\<close> by auto
        with "**"(3-5) "***" have \<open>t \<in> \<D> ?rhs\<close>
          by (simp add: D_Renaming D_Throw)
            (metis "*"(1, 3) F_imp_front_tickFree \<open>(t, X) \<in> \<F> ?rhs\<close> front_tickFree_Nil
              front_tickFree_append_iff front_tickFree_dw_closed list.discI)
        with same_div D_F show \<open>(t, X) \<in> \<F> ?lhs\<close> by blast
      next
        fix u1 assume \<open>t1 @ [ev b] = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1\<close> \<open>u1 \<in> \<T> P\<close>
        then obtain u1' where ** : \<open>t1 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u1'\<close> \<open>u1' @ [ev a] \<in> \<T> P\<close>
          by (cases u1 rule: rev_cases, simp_all add: \<open>b = f a\<close> ev_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
            (metis Nil_is_append_conv Un_iff \<open>a \<in> A\<close> events_of_memI inj_onD
              inj_on_f last_in_set last_snoc list.distinct(1))
        from "*"(3) "**"(1) have *** : \<open>set u1' \<inter> ev ` A = {}\<close> by auto
        from "*"(5) \<open>inv_into A f b = a\<close> consider \<open>t2 \<in> \<D> (Renaming (Q a) f g)\<close>
          | u2 where \<open>t2 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u2\<close> \<open>(u2, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (Q a)\<close>
          unfolding Renaming_projs by blast
        thus \<open>(t, X) \<in> \<F> ?lhs\<close>
        proof cases
          assume \<open>t2 \<in> \<D> (Renaming (Q a) f g)\<close>
          with "*"(1-4) \<open>inv_into A f b = a\<close> have \<open>t \<in> \<D> ?rhs\<close>
            by (auto simp add: D_Throw)
          with same_div D_F show \<open>(t, X) \<in> \<F> ?lhs\<close> by blast
        next
          fix u2 assume **** : \<open>t2 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u2\<close>
            \<open>(u2, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (Q a)\<close>
          from "****"(1) have ***** : \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (u1' @ ev a # u2)\<close>  
            by (simp add: "*"(1) "**"(1) "****" \<open>b = f a\<close>)
          show \<open>(t, X) \<in> \<F> ?lhs\<close>
            by (simp add: F_Renaming F_Throw)
              (use "**"(2) "***" "****"(2) "*****" \<open>a \<in> A\<close> in blast)
        qed
      qed
    qed
  qed
qed



subsection \<open>\<^const>\<open>Renaming\<close> and \<^const>\<open>Hiding\<close>\<close>

text \<open>When \<^term>\<open>f\<close> is one to one, \<^term>\<open>Renaming (P \ S) f\<close> will behave like we expect it to do.\<close>

lemma strict_mono_map: \<open>strict_mono g \<Longrightarrow> strict_mono (\<lambda>i. map f (g i))\<close>
  unfolding strict_mono_def less_eq_list_def less_list_def prefix_def by fastforce



lemma trace_hide_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>inj_on (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (set s \<union> ev ` S) \<Longrightarrow>
   trace_hide (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s) (ev ` f ` S) = 
   map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (trace_hide s (ev ` S))\<close>
proof (induct s)
  case Nil
  show ?case by simp
next
  case (Cons e s)
  hence * : \<open>trace_hide (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s) (ev ` f ` S) = 
             map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (trace_hide s (ev ` S))\<close> by fastforce
  from Cons.prems[unfolded inj_on_def, rule_format, of e, simplified] show ?case
    apply (simp add: "*")
    apply (simp add: image_iff)
    by (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(9))
qed


lemma inj_on_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_set_T:
  \<open>inj_on (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (set s)\<close> if \<open>inj_on f (events_of P)\<close> \<open>s \<in> \<T> P\<close>
proof (rule inj_onI)
  show \<open>e \<in> set s \<Longrightarrow> e' \<in> set s \<Longrightarrow> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g e = map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g e' \<Longrightarrow> e = e'\<close> for e e'
    by (cases e; cases e'; simp)
      (meson events_of_memI inj_onD that(1, 2),
        metis T_imp_front_tickFree event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(2) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(2) front_tickFree_Cons_iff that(2)
        front_tickFree_nonempty_append_imp list.distinct(1) snoc_eq_iff_butlast split_list_last)
qed


theorem bij_Renaming_Hiding: \<open>Renaming (P \ S) f g = Renaming P f g \ f ` S\<close>
  (is \<open>?lhs = ?rhs\<close>) if bij_f: \<open>bij f\<close> and bij_g : \<open>bij g\<close>
proof -
  have inj_on_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : \<open>inj_on (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) X\<close> for X
  proof (rule inj_onI)
    show \<open>e \<in> X \<Longrightarrow> e' \<in> X \<Longrightarrow> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g e = map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g e' \<Longrightarrow> e = e'\<close> for e e'
      by (cases e; cases e'; simp)
        (metis bij_f bij_pointE, metis bij_g bij_pointE)
  qed
  have inj_on_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inv : \<open>inj_on (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (inv f) (inv g)) X\<close> for X
  proof (rule inj_onI)
    show \<open>e \<in> X \<Longrightarrow> e' \<in> X \<Longrightarrow> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (inv f) (inv g) e = map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (inv f) (inv g) e'
          \<Longrightarrow> e = e'\<close> for e e'
      by (cases e; cases e', simp_all)
        (metis bij_f bij_inv_eq_iff, metis bij_g bij_inv_eq_iff)
  qed
  show \<open>?lhs = ?rhs\<close>
  proof (subst Process_eq_spec_optimized, safe)
    fix s
    assume \<open>s \<in> \<D> ?lhs\<close>
    then obtain s1 s2 where * : \<open>tickFree s1\<close> \<open>front_tickFree s2\<close>
      \<open>s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1 @ s2\<close> \<open>s1 \<in> \<D> (P \ S)\<close>
      by (simp add: D_Renaming) blast
    from "*"(4) obtain t u
      where ** : \<open>front_tickFree u\<close> \<open>tickFree t\<close> \<open>s1 = trace_hide t (ev ` S) @ u\<close>
        \<open>t \<in> \<D> P \<or> (\<exists>h. isInfHiddenRun h P S \<and> t \<in> range h)\<close>
      by (simp add: D_Hiding) blast
    from "**"(4) show \<open>s \<in> \<D> ?rhs\<close>
    proof (elim disjE)
      assume \<open>t \<in> \<D> P\<close>
      hence \<open>front_tickFree (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u @ s2) \<and> tickFree (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t) \<and>
             s = trace_hide (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t) (ev ` f ` S) @ map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u @ s2 \<and>
             map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t \<in> \<D> (Renaming P f g)\<close>
        apply (simp add: "*"(3) "**"(2, 3) map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree, intro conjI)
        apply (metis "*"(1, 2) "**"(1) "**"(3) front_tickFree_append_iff
            map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_front_tickFree map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree tickFree_append_iff)
        apply (simp add: trace_hide_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k inj_on_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        by (metis (mono_tags, lifting) "**"(2) CollectI D_Renaming append.right_neutral front_tickFree_Nil)
      thus \<open>s \<in> \<D> ?rhs\<close> by (simp add: D_Hiding) blast
    next
      assume \<open>\<exists>h. isInfHiddenRun h P S \<and> t \<in> range h\<close>
      then obtain h where \<open>isInfHiddenRun h P S\<close> \<open>t \<in> range h\<close> by blast
      hence \<open>front_tickFree (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u @ s2) \<and>
             tickFree (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t) \<and>
             s = trace_hide (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t) (ev ` f ` S) @ map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u @ s2 \<and>
             isInfHiddenRun (\<lambda>i. map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (h i)) (Renaming P f g) (f ` S) \<and> 
             map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t \<in> range (\<lambda>i. map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (h i))\<close>
        apply (simp add: "*"(3) "**"(2, 3) map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree, intro conjI)
        apply (metis "*"(1, 2) "**"(3) front_tickFree_append map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree tickFree_append_iff)
        apply (rule trace_hide_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF inj_on_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, symmetric])
        apply (solves \<open>rule strict_mono_map, simp\<close>)
        apply (solves \<open>auto simp add: T_Renaming\<close>)
        apply (subst (1 2) trace_hide_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF inj_on_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k])
        by metis blast
      thus \<open>s \<in> \<D> ?rhs\<close> by (simp add: D_Hiding) blast
    qed
  next
    fix s
    assume \<open>s \<in> \<D> ?rhs\<close>
    then obtain t u
      where * : \<open>front_tickFree u\<close> \<open>tickFree t\<close> \<open>s = trace_hide t (ev ` f ` S) @ u\<close>
        \<open>t \<in> \<D> (Renaming P f g) \<or> 
                 (\<exists>h. isInfHiddenRun h (Renaming P f g) (f ` S) \<and> t \<in> range h)\<close>
      by (simp add: D_Hiding) blast
    from "*"(4) show \<open>s \<in> \<D> ?lhs\<close>
    proof (elim disjE)
      assume \<open>t \<in> \<D> (Renaming P f g)\<close>
      then obtain t1 t2 where ** : \<open>tickFree t1\<close> \<open>front_tickFree t2\<close> 
        \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1 @ t2\<close> \<open>t1 \<in> \<D> P\<close>
        by (simp add: D_Renaming) blast
      have \<open>tickFree (trace_hide t1 (ev ` S)) \<and> 
            front_tickFree (trace_hide t2 (ev ` f ` S) @ u) \<and>
            trace_hide (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1) (ev ` f ` S) @ trace_hide t2 (ev ` f ` S) @ u =
            map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (trace_hide t1 (ev ` S)) @ trace_hide t2 (ev ` f ` S) @ u \<and>
            trace_hide t1 (ev ` S) \<in> \<D> (P \ S)\<close>
        apply (simp, intro conjI)
        using "**"(1) Hiding_tickFree apply blast
        using "*"(1, 2) "**"(3) Hiding_tickFree front_tickFree_append tickFree_append_iff apply blast
        apply (rule trace_hide_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF inj_on_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k])
        using "**"(4) mem_D_imp_mem_D_Hiding by blast
      thus \<open>s \<in> \<D> ?lhs\<close> by (simp add: D_Renaming "*"(3) "**"(3)) blast
    next
      have inv_S: \<open>S = inv f ` f ` S\<close> by (simp add: bij_is_inj bij_f)
      have inj_inv_f: \<open>inj (inv f)\<close> 
        by (simp add: bij_imp_bij_inv bij_is_inj bij_f)
      have ** : \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (inv f) (inv g) \<circ> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) v = v\<close> for v
        by (induct v, simp_all)
          (metis bij_f bij_g bij_inv_eq_iff event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(9) map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_tick_iff)
      assume \<open>\<exists>h. isInfHiddenRun h (Renaming P f g) (f ` S) \<and> t \<in> range h\<close>
      then obtain h
        where *** : \<open>isInfHiddenRun h (Renaming P f g) (f ` S)\<close> \<open>t \<in> range h\<close> by blast
      then consider t1 where \<open>t1 \<in> \<T> P\<close> \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1\<close>
        | t1 t2 where \<open>tickFree t1\<close> \<open>front_tickFree t2\<close> 
          \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1 @ t2\<close> \<open>t1 \<in> \<D> P\<close>
        by (simp add: T_Renaming) blast
      thus \<open>s \<in> \<D> ?lhs\<close>
      proof cases
        fix t1 assume **** : \<open>t1 \<in> \<T> P\<close> \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1\<close>
        have ***** : \<open>t1 = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (inv f) (inv g)) t\<close> by (simp add: "****"(2) "**")
        have ****** : \<open>trace_hide t1 (ev ` S) = trace_hide t1 (ev ` S) \<and>
                       isInfHiddenRun (\<lambda>i. map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (inv f) (inv g)) (h i)) P S \<and> 
                       t1 \<in> range (\<lambda>i. map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (inv f) (inv g)) (h i))\<close>
          apply (simp add: "***"(1) strict_mono_map, intro conjI)
          apply (subst Renaming_inv[where f = f and g = g, symmetric])
          apply (solves \<open>simp add: bij_is_inj bij_f\<close>)
          apply (solves \<open>simp add: bij_is_inj bij_g\<close>)

          using "***"(1) apply (subst T_Renaming, blast)
          apply (subst (1 2) inv_S, subst (1 2) trace_hide_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF inj_on_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inv])
          apply (metis "***"(1))
          using "***"(2) "*****" by blast
        have \<open>tickFree (trace_hide t1 (ev ` S)) \<and> front_tickFree t1 \<and>
              trace_hide (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1) (ev ` f ` S) @ u = 
              map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (trace_hide t1 (ev ` S)) @ u \<and> 
              trace_hide t1 (ev ` S) \<in> \<D> (P \ S)\<close>
          apply (simp, intro conjI)
          using "*"(2) "****"(2) map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree Hiding_tickFree apply blast
          using "****"(1) is_processT2_TR apply blast
          apply (rule trace_hide_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF inj_on_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k])
          apply (simp add: D_Renaming D_Hiding)
          using "*"(2) "*****" "******" map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree front_tickFree_Nil by blast
        with "*"(1) show \<open>s \<in> \<D> ?lhs\<close> by (simp add: D_Renaming "*"(3) "****"(2)) blast
      next
        fix t1 t2 assume **** : \<open>tickFree t1\<close> \<open>front_tickFree t2\<close>
          \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1 @ t2\<close> \<open>t1 \<in> \<D> P\<close>
        have \<open>tickFree (trace_hide t1 (ev ` S)) \<and>
              front_tickFree (trace_hide t2 (ev ` f ` S) @ u) \<and>
              trace_hide (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t1) (ev ` f ` S) @ trace_hide t2 (ev ` f ` S) @ u =
              map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (trace_hide t1 (ev ` S)) @ trace_hide t2 (ev ` f ` S) @ u \<and>
              trace_hide t1 (ev ` S) \<in> \<D> (P \ S)\<close>
          apply (simp, intro conjI)
          using "****"(1) Hiding_tickFree apply blast
          using "*"(1, 2) "****"(3) Hiding_tickFree front_tickFree_append tickFree_append_iff apply blast
          apply (rule trace_hide_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF inj_on_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k])
          using "****"(4) mem_D_imp_mem_D_Hiding by blast
        thus \<open>s \<in> \<D> ?lhs\<close> by (simp add: D_Renaming "*"(3) "****"(3)) blast
      qed
    qed
  next
    fix s X
    assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
    assume \<open>(s, X) \<in> \<F> ?lhs\<close>
    then consider \<open>s \<in> \<D> ?lhs\<close>
      | s1 where \<open>(s1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (P \ S)\<close> \<open>s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1\<close>
      by (simp add: F_Renaming D_Renaming) blast
    thus \<open>(s, X) \<in> \<F> ?rhs\<close>
    proof cases
      from D_F same_div show \<open>s \<in> \<D> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> by blast
    next
      fix s1 assume * : \<open>(s1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (P \ S)\<close>
        \<open>s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1\<close>
      from this(1) consider \<open>s1 \<in> \<D> (P \ S)\<close>
        | t where \<open>s1 = trace_hide t (ev ` S)\<close> \<open>(t, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X \<union> ev ` S) \<in> \<F> P\<close>
        by (simp add: F_Hiding D_Hiding) blast
      thus \<open>(s, X) \<in> \<F> ?rhs\<close>
      proof cases
        assume \<open>s1 \<in> \<D> (P \ S)\<close>
        then obtain t u
          where ** : \<open>front_tickFree u\<close> \<open>tickFree t\<close> \<open>s1 = trace_hide t (ev ` S) @ u\<close>
            \<open>t \<in> \<D> P \<or> (\<exists>g. isInfHiddenRun g P S \<and> t \<in> range g)\<close>
          by (simp add: D_Hiding) blast
        have *** : \<open>front_tickFree (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u) \<and> tickFree (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t) \<and>
                    map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (trace_hide t (ev ` S)) @ map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u = 
                    trace_hide (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t) (ev ` f ` S) @ (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u)\<close>
          by (simp add: map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_front_tickFree map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree "**"(1, 2))
            (rule trace_hide_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF inj_on_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, symmetric])
        from "**"(4) show \<open>(s, X) \<in> \<F> ?rhs\<close>
        proof (elim disjE exE)
          assume \<open>t \<in> \<D> P\<close>
          hence $ : \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t \<in> \<D> (Renaming P f g)\<close>
            apply (simp add: D_Renaming)
            using "**"(2) front_tickFree_Nil by blast
          show \<open>(s, X) \<in> \<F> ?rhs\<close>
            by (simp add: F_Hiding) (metis "$" "*"(2) "**"(3) "***" map_append)
        next
          fix h assume \<open>isInfHiddenRun h P S \<and> t \<in> range h\<close>
          hence $ : \<open>isInfHiddenRun (\<lambda>i. map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (h i)) (Renaming P f g) (f ` S) \<and> 
                     map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t \<in> range (\<lambda>i. map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (h i))\<close>
            apply (subst (1 2) trace_hide_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF inj_on_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k])
            by (simp add: strict_mono_map T_Renaming image_iff) (metis (mono_tags, lifting))
          show \<open>(s, X) \<in> \<F> ?rhs\<close>
            apply (simp add: F_Hiding)
              (* TODO: break this smt *)
            by (smt (verit, del_insts) "$" "*"(2) "**"(3) "***" map_append)
        qed
      next
        fix t assume ** : \<open>s1 = trace_hide t (ev ` S)\<close> 
          \<open>(t, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X \<union> ev ` S) \<in> \<F> P\<close>
        have *** : \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X \<union> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` ev ` f ` S = map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X \<union> ev ` S\<close>
          by (auto simp add: image_iff map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_ev_iff) (metis bij_f bij_pointE)
        have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (trace_hide t (ev ` S)) = 
              trace_hide (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t) (ev ` f ` S) \<and>
              (map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t, X \<union> ev ` f ` S) \<in> \<F> (Renaming P f g)\<close>
          apply (intro conjI)
          apply (rule trace_hide_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF inj_on_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, symmetric])
          apply (simp add: F_Renaming)
          using "**"(2) "***" by auto
        show \<open>(s, X) \<in> \<F> ?rhs\<close>
          apply (simp add: F_Hiding "*"(2) "**"(1))
          using \<open>?this\<close> by blast
      qed
    qed
  next
    fix s X
    assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
    assume \<open>(s, X) \<in> \<F> ?rhs\<close>
    then consider \<open>s \<in> \<D> ?rhs\<close>
      | t where \<open>s = trace_hide t (ev ` f ` S)\<close> \<open>(t, X \<union> ev ` f ` S) \<in> \<F> (Renaming P f g)\<close>
      by (simp add: F_Hiding D_Hiding) blast
    thus \<open>(s, X) \<in> \<F> ?lhs\<close>
    proof cases
      from D_F same_div show \<open>s \<in> \<D> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> by blast
    next
      fix t assume \<open>s = trace_hide t (ev ` f ` S)\<close> \<open>(t, X \<union> ev ` f ` S) \<in> \<F> (Renaming P f g)\<close>
      then obtain t
        where * : \<open>s = trace_hide t (ev ` f ` S)\<close>
          \<open>(t, X \<union> ev ` f ` S) \<in> \<F> (Renaming P f g)\<close> by blast
      have ** : \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X \<union> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` ev ` f ` S = map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X \<union> ev ` S\<close>
        by (auto simp add: image_iff map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_eq_ev_iff) (metis bij_f bij_pointE)
      have \<open>(\<exists>s1. (s1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X \<union> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` ev ` f ` S) \<in> \<F> P \<and> t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1) \<or> 
            (\<exists>s1 s2. tickFree s1 \<and> front_tickFree s2 \<and> t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1 @ s2 \<and> s1 \<in> \<D> P)\<close>
        using "*"(2) by (auto simp add: F_Renaming)
      thus \<open>(s, X) \<in> \<F> ?lhs\<close>
      proof (elim disjE exE conjE)
        fix s1
        assume \<open>(s1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X \<union> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` ev ` f ` S) \<in> \<F> P\<close> \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1\<close>
        hence \<open>(trace_hide s1 (ev ` S), map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (P \ S) \<and>
               s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (trace_hide s1 (ev ` S))\<close>
          apply (simp add: "*"(1) F_Hiding "**", intro conjI)
          by blast (rule trace_hide_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF inj_on_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k])
        show \<open>(s, X) \<in> \<F> ?lhs\<close>
          apply (simp add: F_Renaming)
          using \<open>?this\<close> by blast
      next
        fix s1 s2
        assume \<open>tickFree s1\<close> \<open>front_tickFree s2\<close> \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1 @ s2\<close> \<open>s1 \<in> \<D> P\<close>
        hence \<open>tickFree (trace_hide s1 (ev ` S)) \<and> 
               front_tickFree (trace_hide s2 (ev ` f ` S)) \<and> 
               s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (trace_hide s1 (ev ` S)) @ trace_hide s2 (ev ` f ` S) \<and> 
               trace_hide s1 (ev ` S) \<in> \<D> (P \ S)\<close>
          apply (simp add: F_Renaming "*"(1), intro conjI)
          using Hiding_tickFree apply blast
          using Hiding_front_tickFree apply blast
          apply (rule trace_hide_map_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k[OF inj_on_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k])
          using mem_D_imp_mem_D_Hiding by blast
        show \<open>(s, X) \<in> \<F> ?lhs\<close>
          apply (simp add: F_Renaming)
          using \<open>?this\<close> by blast
      qed
    qed
  qed
qed



subsection \<open>\<^const>\<open>Renaming\<close> and \<^const>\<open>Sync\<close>\<close>

text \<open>Idem for the synchronization: when \<^term>\<open>f\<close> is one to one, 
      \<^term>\<open>Renaming (P \<lbrakk>S\<rbrakk> Q)\<close> will behave as expected.\<close>

lemma bij_map_setinterleaving_iff_setinterleaving :
  \<open>map f r setinterleaves ((map f t, map f u), f ` S) \<longleftrightarrow>
   r setinterleaves ((t, u), S)\<close> if bij_f : \<open>bij f\<close>
proof (induct \<open>(t, S, u)\<close> arbitrary: t u r rule: setinterleaving.induct)
  case 1
  thus ?case by simp
next
  case (2 y u)
  show ?case
  proof (cases \<open>y \<in> S\<close>)
    show \<open>y \<in> S \<Longrightarrow> ?case\<close> by simp
  next
    assume \<open>y \<notin> S\<close>
    hence \<open>f y \<notin> f ` S\<close> by (metis bij_betw_imp_inj_on inj_image_mem_iff bij_f)
    with "2.hyps"[OF \<open>y \<notin> S\<close>, of \<open>tl r\<close>] show ?case
      by (cases r; simp add: \<open>y \<notin> S\<close>) (metis bij_pointE bij_f)
  qed
next
  case (3 x t)
  show ?case
  proof (cases \<open>x \<in> S\<close>)
    show \<open>x \<in> S \<Longrightarrow> ?case\<close> by simp
  next
    assume \<open>x \<notin> S\<close>
    hence \<open>f x \<notin> f ` S\<close> by (metis bij_betw_imp_inj_on inj_image_mem_iff bij_f)
    with "3.hyps"[OF \<open>x \<notin> S\<close>, of \<open>tl r\<close>] show ?case
      by (cases r; simp add: \<open>x \<notin> S\<close>) (metis bij_pointE bij_f)
  qed
next
  case (4 x t y u)
  have  * : \<open>x \<noteq> y \<Longrightarrow> f x \<noteq> f y\<close> by (metis bij_pointE bij_f)
  have ** : \<open>f z \<in> f ` S \<longleftrightarrow> z \<in> S\<close> for z
    by (meson bij_betw_def inj_image_mem_iff bij_f)
  show ?case
  proof (cases \<open>x \<in> S\<close>; cases \<open>y \<in> S\<close>)
    from "4.hyps"(1)[of \<open>tl r\<close>] show \<open>x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> ?case\<close>
      by (cases r; simp add: "*") (metis bij_pointE bij_f)
  next
    from "4.hyps"(2)[of \<open>tl r\<close>] show \<open>x \<in> S \<Longrightarrow> y \<notin> S \<Longrightarrow> ?case\<close>
      by (cases r; simp add: "**") (metis bij_pointE bij_f)
  next
    from "4.hyps"(5)[of \<open>tl r\<close>] show \<open>x \<notin> S \<Longrightarrow> y \<in> S \<Longrightarrow> ?case\<close>
      by (cases r; simp add: "**") (metis bij_pointE bij_f)
  next
    from "4.hyps"(3, 4)[of \<open>tl r\<close>] show \<open>x \<notin> S \<Longrightarrow> y \<notin> S \<Longrightarrow> ?case\<close>
      by (cases r; simp add: "**") (metis bij_pointE bij_f)
  qed
qed


theorem bij_Renaming_Sync:
  \<open>Renaming (P \<lbrakk>S\<rbrakk> Q) f g = Renaming P f g \<lbrakk>f ` S\<rbrakk> Renaming Q f g\<close>
  (is \<open>?lhs P Q = ?rhs P Q\<close>) if bij_f: \<open>bij f\<close> and bij_g : \<open>bij g\<close>
proof -
  \<comment> \<open>Four intermediate results.\<close>
  have bij_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : \<open>bij (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)\<close>
  proof (rule bijI)
    show \<open>inj (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)\<close>
    proof (rule injI)
      show \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g e = map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g e' \<Longrightarrow> e = e'\<close> for e e'
        by (cases e; cases e'; simp)
          (metis bij_f bij_pointE, metis bij_g bij_pointE)
    qed
  next
    show \<open>surj (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)\<close>
    proof (rule surjI)
      show \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (inv f) (inv g) e) = e\<close> for e
        by (cases e, simp_all)
          (meson bij_f bij_inv_eq_iff, meson bij_g bij_inv_eq_iff)
    qed
  qed
  moreover have \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (inv f) (inv g) \<circ> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g = id\<close>
  proof (rule ext)
    show \<open>(map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (inv f) (inv g) \<circ> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) e = id e\<close> for e
      by (cases e, simp_all)
        (meson bij_betw_def bij_f inv_f_eq, meson bij_betw_def bij_g inv_f_eq)
  qed
  ultimately have inv_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inv :
    \<open>inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) = map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (inv f) (inv g)\<close>
    by (metis bij_betw_imp_inj_on bij_betw_imp_surj_on inv_o_cancel surj_fun_eq)
  have sets_S_eq : \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g ` (range tick \<union> ev ` S) = range tick \<union> ev ` f ` S\<close>
    by (auto simp add: image_iff)
      (metis Un_iff bij_g bij_pointE event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(10) rangeI,
        metis Un_iff event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(9) imageI)
  have inj_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : \<open>inj (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)\<close>
    and inj_inv_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k : \<open>inj (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g))\<close>
    by (use bij_betw_imp_inj_on bij_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k in blast)
      (meson bij_betw_imp_inj_on bij_betw_inv_into bij_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  show \<open>?lhs P Q = ?rhs P Q\<close>
  proof (subst Process_eq_spec_optimized, safe)
    fix s
    assume \<open>s \<in> \<D> (?lhs P Q)\<close>
    then obtain s1 s2 where * : \<open>tickFree s1\<close> \<open>front_tickFree s2\<close>
      \<open>s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1 @ s2\<close> \<open>s1 \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
      by (simp add: D_Renaming) blast
    from "*"(4) obtain t u r v 
      where ** : \<open>front_tickFree v\<close> \<open>tickFree r \<or> v = []\<close> 
        \<open>s1 = r @ v\<close> \<open>r setinterleaves ((t, u), range tick \<union> ev ` S)\<close>
        \<open>t \<in> \<D> P \<and> u \<in> \<T> Q \<or> t \<in> \<D> Q \<and> u \<in> \<T> P\<close> 
      by (simp add: D_Sync) blast
    { fix t u P Q
      assume assms : \<open>r setinterleaves ((t, u), range tick \<union> ev ` S)\<close> 
        \<open>t \<in> \<D> P\<close> \<open>u \<in> \<T> Q\<close>
      have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) r setinterleaves 
            ((map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t, map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u), range tick \<union> ev ` f ` S)\<close>
        by (metis assms(1) bij_map_setinterleaving_iff_setinterleaving bij_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k sets_S_eq)
      moreover have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t \<in> \<D> (Renaming P f g)\<close>
        apply (cases \<open>tickFree t\<close>; simp add: D_Renaming)
        using assms(2) front_tickFree_Nil apply blast
        by (metis D_T D_imp_front_tickFree append_T_imp_tickFree assms(2) front_tickFree_Cons_iff
            is_processT9 list.simps(3) map_append nonTickFree_n_frontTickFree map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_front_tickFree)
      moreover have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u \<in> \<T> (Renaming Q f g)\<close>
        using assms(3) by (simp add: T_Renaming) blast
      ultimately have \<open>s \<in> \<D> (?rhs P Q)\<close>
        by (simp add: D_Sync "*"(3) "**"(3))
          (metis "*"(1, 2) "**"(3) map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree front_tickFree_append tickFree_append_iff)
    } note *** = this

    from "**"(4, 5) "***" show \<open>s \<in> \<D> (?rhs P Q)\<close>
      apply (elim disjE)
      using "**"(4) "***" apply blast
      using "**"(4) "***" by (subst Sync_commute) blast
  next
    fix s
    assume \<open>s \<in> \<D> (?rhs P Q)\<close>
    then obtain t u r v
      where * : \<open>front_tickFree v\<close> \<open>tickFree r \<or> v = []\<close> \<open>s = r @ v\<close> 
        \<open>r setinterleaves ((t, u), range tick \<union> ev ` f ` S)\<close>
        \<open>t \<in> \<D> (Renaming P f g) \<and> u \<in> \<T> (Renaming Q f g) \<or>
                 t \<in> \<D> (Renaming Q f g) \<and> u \<in> \<T> (Renaming P f g)\<close>
      by (simp add: D_Sync) blast

    { fix t u P Q
      assume assms : \<open>r setinterleaves ((t, u), range tick \<union> ev ` f ` S)\<close>
        \<open>t \<in> \<D> (Renaming P f g)\<close> \<open>u \<in> \<T> (Renaming Q f g)\<close>
      have \<open>inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) ` (range tick \<union> ev ` f ` S) =
            inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) ` map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g ` (range tick \<union> ev ` S)\<close>
        using sets_S_eq by presburger
      from bij_map_setinterleaving_iff_setinterleaving
        [THEN iffD2, OF _ assms(1), of \<open>inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)\<close>,
          simplified this image_inv_f_f[OF inj_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k]]
      have ** : \<open>(map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) r) setinterleaves
                 ((map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) t, map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) u), range tick \<union> ev ` S)\<close>
        using bij_betw_inv_into bij_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k by blast
      from assms(2) obtain s1 s2
        where \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1 @ s2\<close> \<open>tickFree s1\<close> \<open>front_tickFree s2\<close> \<open>s1 \<in> \<D> P\<close>
        by (auto simp add: D_Renaming)
      hence \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (inv f) (inv g)) t \<in> \<D> (Renaming (Renaming P f g) (inv f) (inv g))\<close>
        apply (simp add: D_Renaming)
        apply (rule_tac x = \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1\<close> in exI)
        apply (rule_tac x = \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (inv f) (inv g)) s2\<close> in exI)
        by simp (metis append_Nil2 front_tickFree_Nil map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_front_tickFree map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree)
      hence *** : \<open>map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) t \<in> \<D> P\<close>
        by (metis Renaming_inv bij_def bij_f bij_g inv_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inv)
      have \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k (inv f) (inv g)) u \<in> \<T> (Renaming (Renaming Q f g) (inv f) (inv g))\<close>
        using assms(3) by (subst T_Renaming, simp) blast
      hence **** : \<open>map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) u \<in> \<T> Q\<close>
        by (simp add: Renaming_inv bij_f bij_g bij_is_inj inv_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inv)
      have ***** : \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g \<circ> inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) r = r\<close>
        by (metis (no_types, lifting) bij_betw_imp_inj_on bij_betw_inv_into bij_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k inj_iff list.map_comp list.map_id)
      have \<open>s \<in> \<D> (?lhs P Q)\<close>
      proof (cases \<open>tickFree r\<close>)
        assume \<open>tickFree r\<close>
        have $ : \<open>r @ v = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) r) @ v\<close>
          by (simp add: "*****")
        show \<open>s \<in> \<D> (?lhs P Q)\<close>
          apply (simp add: D_Renaming D_Sync "*"(3))
          by (metis "$" "*"(1) "**" "***" "****" map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree \<open>tickFree r\<close> 
              append.right_neutral append_same_eq front_tickFree_Nil)
      next
        assume \<open>\<not> tickFree r\<close>
        then obtain r' res where $ : \<open>r = r' @ [\<checkmark>(res)]\<close> \<open>tickFree r'\<close>
          by (metis D_imp_front_tickFree assms butlast_snoc front_tickFree_charn
              front_tickFree_single ftf_Sync is_processT2_TR list.distinct(1)
              nonTickFree_n_frontTickFree self_append_conv2)
        then obtain t' u'
          where $$ : \<open>t = t' @ [\<checkmark>(res)]\<close> \<open>u = u' @ [\<checkmark>(res)]\<close>
          by (metis D_imp_front_tickFree SyncWithTick_imp_NTF T_imp_front_tickFree assms)
        hence $$$ : \<open>(map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) r') setinterleaves
                     ((map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) t', map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) u'),
                      range tick \<union> ev ` S)\<close>
          by (metis "$"(1) append_same_eq assms(1) bij_betw_imp_surj_on
              bij_map_setinterleaving_iff_setinterleaving bij_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k
              ftf_Sync32 inj_imp_bij_betw_inv inj_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k sets_S_eq)
        from "***" $$(1) have *** : \<open>map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) t' \<in> \<D> P\<close> 
          by simp (use inv_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_is_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_inv is_processT9 in force)
        from "****" $$(2) have **** : \<open>map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) u' \<in> \<T> Q\<close>
          using is_processT3_TR prefixI by simp blast
        have $$$$ : \<open>r = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) r') @ [\<checkmark>(res)]\<close>
          using "$" "*****" by auto
        show \<open>s \<in> \<D> (?lhs P Q)\<close>
          by (simp add: D_Renaming D_Sync "*"(3) "$$$")
            (metis "$"(1) "$"(2) "$$$" "$$$$" "*"(2) "***" "****" map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree \<open>\<not> tickFree r\<close>
              append.right_neutral append_same_eq front_tickFree_Nil front_tickFree_single)
      qed
    } note ** = this
    show \<open>s \<in> \<D> (?lhs P Q)\<close> by (metis "*"(4, 5) "**" Sync_commute)
  next
    fix s X
    assume same_div : \<open>\<D> (?lhs P Q) = \<D> (?rhs P Q)\<close>
    assume \<open>(s, X) \<in> \<F> (?lhs P Q)\<close>
    then consider \<open>s \<in> \<D> (?lhs P Q)\<close>
      | s1 where \<open>(s1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close> \<open>s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1\<close>
      by (simp add: F_Renaming D_Renaming) blast
    thus \<open>(s, X) \<in> \<F> (?rhs P Q)\<close>
    proof cases
      from same_div D_F show \<open>s \<in> \<D> (?lhs P Q) \<Longrightarrow> (s, X) \<in> \<F> (?rhs P Q)\<close> by blast
    next
      fix s1 assume * : \<open>(s1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close> 
        \<open>s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1\<close>
      from "*"(1) consider \<open>s1 \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
        | t_P t_Q X_P X_Q 
        where \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close> 
          \<open>s1 setinterleaves ((t_P, t_Q), range tick \<union> ev ` S)\<close>
          \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` S) \<union> X_P \<inter> X_Q\<close>
        by (auto simp add: F_Sync D_Sync)
      thus \<open>(s, X) \<in> \<F> (?rhs P Q)\<close>
      proof cases
        assume \<open>s1 \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
        hence \<open>s \<in> \<D> (?lhs P Q)\<close>
          apply (cases \<open>tickFree s1\<close>; simp add: D_Renaming "*"(2)) 
          using front_tickFree_Nil apply blast
          by (metis (no_types, lifting) map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_front_tickFree butlast_snoc front_tickFree_iff_tickFree_butlast
              front_tickFree_single map_butlast nonTickFree_n_frontTickFree process_charn)
        with same_div D_F show \<open>(s, X) \<in> \<F> (?rhs P Q)\<close> by blast
      next
        fix t_P t_Q X_P X_Q
        assume ** : \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
          \<open>s1 setinterleaves ((t_P, t_Q), range tick \<union> ev ` S)\<close>
          \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` S) \<union> X_P \<inter> X_Q\<close>
        have \<open>(map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t_P, (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) ` X_P) \<in> \<F> (Renaming P f g)\<close>
          by (simp add: F_Renaming)
            (metis "**"(1) bij_betw_def bij_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k inj_vimage_image_eq)  
        moreover have \<open>(map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t_Q, (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) ` X_Q) \<in> \<F> (Renaming Q f g)\<close>
          by (simp add: F_Renaming)
            (metis "**"(2) bij_betw_imp_inj_on bij_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k inj_vimage_image_eq)
        moreover have \<open>s setinterleaves ((map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t_P, map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t_Q),
                                         range tick \<union> ev ` f ` S)\<close>
          by (metis "*"(2) "**"(3) bij_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k sets_S_eq
              bij_map_setinterleaving_iff_setinterleaving)
        moreover have \<open>X = ((map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) ` X_P \<union> (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) ` X_Q) \<inter> (range tick \<union> ev ` f ` S) \<union>
                  (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) ` X_P \<inter> (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) ` X_Q\<close>
          apply (rule inj_image_eq_iff[THEN iffD1, OF inj_inv_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k])
          apply (subst bij_vimage_eq_inv_image[OF bij_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, symmetric])
          apply (subst "**"(4), fold image_Un sets_S_eq)
          apply (subst (1 2) image_Int[OF inj_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, symmetric])
          apply (fold image_Un)
          apply (subst image_inv_f_f[OF inj_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k])
          by simp
        ultimately show \<open>(s, X) \<in> \<F> (?rhs P Q)\<close>
          by (simp add: F_Sync) blast
      qed
    qed
  next
    fix s X
    assume same_div : \<open>\<D> (?lhs P Q) = \<D> (?rhs P Q)\<close>
    assume \<open>(s, X) \<in> \<F> (?rhs P Q)\<close>
    then consider \<open>s \<in> \<D> (?rhs P Q)\<close>
      | t_P t_Q X_P X_Q where
        \<open>(t_P, X_P) \<in> \<F> (Renaming P f g)\<close> \<open>(t_Q, X_Q) \<in> \<F> (Renaming Q f g)\<close>
        \<open>s setinterleaves ((t_P, t_Q), range tick \<union> ev ` f ` S)\<close>
        \<open>X = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` f ` S) \<union> X_P \<inter> X_Q\<close>
      by (simp add: F_Sync D_Sync) blast
    thus \<open>(s, X) \<in> \<F> (?lhs P Q)\<close>
    proof cases
      from same_div D_F show \<open>s \<in> \<D> (?rhs P Q) \<Longrightarrow> (s, X) \<in> \<F> (?lhs P Q)\<close> by blast
    next
      fix t_P t_Q X_P X_Q
      assume * : \<open>(t_P, X_P) \<in> \<F> (Renaming P f g)\<close> \<open>(t_Q, X_Q) \<in> \<F> (Renaming Q f g)\<close>
        \<open>s setinterleaves ((t_P, t_Q), range tick \<union> ev ` f ` S)\<close>
        \<open>X = (X_P \<union> X_Q) \<inter> (range tick \<union> ev ` f ` S) \<union> X_P \<inter> X_Q\<close>
      from "*"(1, 2) consider \<open>t_P \<in> \<D> (Renaming P f g) \<or> t_Q \<in> \<D> (Renaming Q f g)\<close>
        | t_P1 t_Q1 where \<open>(t_P1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X_P) \<in> \<F> P\<close> \<open>t_P = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t_P1\<close>
          \<open>(t_Q1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X_Q) \<in> \<F> Q\<close> \<open>t_Q = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t_Q1\<close>
        by (simp add: F_Renaming D_Renaming) blast
      thus \<open>(s, X) \<in> \<F> (?lhs P Q)\<close>
      proof cases
        assume \<open>t_P \<in> \<D> (Renaming P f g) \<or> t_Q \<in> \<D> (Renaming Q f g)\<close>
        hence \<open>s \<in> \<D> (?rhs P Q)\<close>
          apply (simp add: D_Sync)
          using "*"(1, 2, 3) F_T setinterleaving_sym front_tickFree_Nil by blast
        with same_div D_F show \<open>(s, X) \<in> \<F> (?lhs P Q)\<close> by blast
      next
        fix t_P1 t_Q1
        assume ** : \<open>(t_P1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X_P) \<in> \<F> P\<close> \<open>t_P = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t_P1\<close>
          \<open>(t_Q1, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X_Q) \<in> \<F> Q\<close> \<open>t_Q = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t_Q1\<close>
        from "**"(2, 4) have *** : \<open>t_P1 = map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) t_P\<close>
          \<open>t_Q1 = map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) t_Q\<close>
          by (simp_all add: inj_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
        have **** : \<open>map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) s) = s\<close>
          by (metis bij_betw_imp_surj bij_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k list.map_comp list.map_id surj_iff)
        from bij_map_setinterleaving_iff_setinterleaving
          [of \<open>inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)\<close> s t_P \<open>range tick \<union> ev ` f ` S\<close> t_Q, simplified "*"(3)]
        have \<open>map (inv (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)) s setinterleaves ((t_P1, t_Q1), range tick \<union> ev ` S)\<close>
          by (metis "***" bij_betw_def bij_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k inj_imp_bij_betw_inv sets_S_eq)
        moreover have \<open>map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X = (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X_P \<union> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X_Q) \<inter> (range tick \<union> ev ` S) \<union> 
                      map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X_P \<inter> map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X_Q\<close>
          by (metis (no_types, lifting) "*"(4) inj_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k inj_vimage_image_eq sets_S_eq vimage_Int vimage_Un)
        ultimately show \<open>(s, X) \<in> \<F> (?lhs P Q)\<close>
          by (simp add: F_Renaming F_Sync) (metis "**"(1, 3) "****")
      qed
    qed
  qed
qed

(*>*)
end 
(*>*)