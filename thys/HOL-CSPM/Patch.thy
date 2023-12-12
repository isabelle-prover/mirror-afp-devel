(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSPM - Architectural operators for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff
 *
 * This file       : Patch
 *
 * Copyright (c) 2023 Université Paris-Saclay, France
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

chapter \<open>Patch for Compatibility\<close>
theory Patch
  imports "HOL-CSP.Assertions"
begin


text \<open>\<^session>\<open>HOL-CSP\<close> significantly changed during the past months, but not all
      the modifications appear in the current version on the AFP.
      This theory fixes the incompatibilities and will be removed in the next release.\<close>


section \<open>Results\<close>

\<comment>\<open>This one is very easy\<close>
lemma Mprefix_Det_distr:
  \<open>(\<box> a \<in> A \<rightarrow> P a) \<box> (\<box> b \<in> B \<rightarrow> Q b) = 
   \<box> x \<in> A \<union> B \<rightarrow> (  if x \<in> A \<inter> B then P x \<sqinter> Q x 
                    else if x \<in> A then P x else Q x)\<close>
  (is \<open>?lhs = ?rhs\<close>)
proof (subst Process_eq_spec, safe)
  show \<open>(s, X) \<in> \<F> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for s X
    by (simp add: F_Det F_Mprefix F_Ndet disjoint_iff, safe, auto)
next
  show \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for s X
    by (auto simp add: F_Mprefix F_Ndet F_Det split: if_split_asm)
next
  show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close> for s
    by (simp add: D_Det D_Mprefix D_Ndet, safe, auto)
next
  show \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ?lhs\<close> for s
    by (auto simp add: D_Mprefix D_Ndet D_Det split: if_split_asm)
qed 



lemma F_Mndetprefix:
  \<open>\<F> (Mndetprefix A P) =
   (if A = {} then {(s, X). s = []} else \<Union>x\<in>A. \<F> (x \<rightarrow> P x))\<close>
  by (simp add: F_Mndetprefix F_STOP)

lemma D_Mndetprefix:
  \<open>\<D> (Mndetprefix A P) = (if A = {} then {} else \<Union>x\<in>A. \<D> (x \<rightarrow> P x))\<close>
  by (simp add: D_Mndetprefix D_STOP)

lemma T_Mndetprefix:
  \<open>\<T> (Mndetprefix A P) = (if A = {} then {[]} else \<Union>x\<in>A. \<T> (x \<rightarrow> P x))\<close>
  by (simp add: T_Mndetprefix T_STOP)

lemma D_expand : 
  \<open>\<D> P = {t1 @ t2| t1 t2. t1 \<in> \<D> P \<and> tickFree t1 \<and> front_tickFree t2}\<close>
  (is \<open>\<D> P = ?rhs\<close>)
proof (intro subset_antisym subsetI)
  show \<open>s \<in> \<D> P \<Longrightarrow> s \<in> ?rhs\<close> for s
    apply (simp, cases \<open>tickFree s\<close>)
     apply (rule_tac x = s in exI, rule_tac x = \<open>[]\<close> in exI, simp)
    apply (rule_tac x = \<open>butlast s\<close> in exI, rule_tac x = \<open>[tick]\<close> in exI, simp)
    by (metis front_tickFree_implies_tickFree nonTickFree_n_frontTickFree
              process_charn snoc_eq_iff_butlast)
next
  show \<open>s \<in> ?rhs \<Longrightarrow> s \<in> \<D> P\<close> for s
    using is_processT7 by blast
qed


lemma F_Seq: \<open>\<F> (P \<^bold>; Q) = {(t, X). (t, X \<union> {tick}) \<in> \<F> P \<and> tickFree t} \<union>
                          {(t1 @ t2, X) |t1 t2 X. t1 @ [tick] \<in> \<T> P \<and> (t2, X) \<in> \<F> Q} \<union>
                          {(t1, X) |t1 X. t1 \<in> \<D> P}\<close>
proof -
  have * : \<open>{(t, X). \<exists>t1 t2. t = t1 @ t2 \<and> t1 @ [tick] \<in> \<T> P \<and> t2 \<in> \<D> Q} \<subseteq>
            {(t1 @ t2, X) |t1 t2 X. t1 @ [tick] \<in> \<T> P \<and> (t2, X) \<in> \<F> Q}\<close>
    using is_processT8 by blast
  have ** : \<open>{(t1, X) |t1 X. t1 \<in> \<D> P} =
             {(t, X). \<exists>t1 t2. t = t1 @ t2 \<and> t1 \<in> \<D> P \<and> tickFree t1 \<and> front_tickFree t2}\<close>
    by (subst D_expand) blast
  show ?thesis
    apply (subst Un_absorb1[OF "*", symmetric], subst "**")
    by (simp add:  F_Seq) blast
qed
   

 
lemma D_Seq:
  \<open>\<D> (P \<^bold>; Q) = \<D> P \<union> {t1 @ t2 |t1 t2. t1 @ [tick] \<in> \<T> P \<and> t2 \<in> \<D> Q}\<close>
  by (subst (2) D_expand) (auto simp add: D_Seq)


lemma T_Seq: \<open>\<T> (P \<^bold>; Q) = {t. \<exists>X. (t, X \<union> {tick}) \<in> \<F> P \<and> tickFree t} \<union> 
                          {t1 @ t2 |t1 t2. t1 @ [tick] \<in> \<T> P \<and> t2 \<in> \<T> Q} \<union>
                          \<D> P\<close>
  by (auto simp add: Traces_def TRACES_def Failures_def[symmetric] F_Seq)



lemma tickFree_butlast:
  \<open>tickFree s \<longleftrightarrow> tickFree (butlast s) \<and> (s \<noteq> [] \<longrightarrow> last s \<noteq> tick)\<close>
  by (induct s) simp_all

lemma front_tickFree_butlast: \<open>front_tickFree s \<longleftrightarrow> tickFree (butlast s)\<close>
  by (induct s) (auto simp add: front_tickFree_def)


lemma STOP_iff_T: \<open>P = STOP \<longleftrightarrow> \<T> P = {[]}\<close>
  apply (intro iffI, simp add: T_STOP)
  apply (subst Process_eq_spec, safe, simp_all add: F_STOP D_STOP)
  by (use F_T in force, use is_processT5_S7 in fastforce)
     (metis D_T append_Nil front_tickFree_single is_processT7_S
            list.distinct(1) singletonD tickFree_Nil)

lemma BOT_iff_D: \<open>P = \<bottom> \<longleftrightarrow> [] \<in> \<D> P\<close>
  apply (intro iffI, simp add: D_UU)
  apply (subst Process_eq_spec, safe)
  by (simp_all add: F_UU D_UU is_processT2 D_imp_front_tickFree)
     (metis append_Nil is_processT tickFree_Nil)+


lemma Ndet_is_STOP_iff: \<open>P \<sqinter> Q = STOP \<longleftrightarrow> P = STOP \<and> Q = STOP\<close>
  using Nil_subset_T by (simp add: STOP_iff_T T_Ndet, blast)

lemma Det_is_STOP_iff: \<open>P \<box> Q = STOP \<longleftrightarrow> P = STOP \<and> Q = STOP\<close>
  using Nil_subset_T by (simp add: STOP_iff_T T_Det, blast)


lemma Det_is_BOT_iff: \<open>P \<box> Q = \<bottom> \<longleftrightarrow> P = \<bottom> \<or> Q = \<bottom>\<close>
  by (simp add: BOT_iff_D D_Det)

lemma Ndet_is_BOT_iff: \<open>P \<sqinter> Q = \<bottom> \<longleftrightarrow> P = \<bottom> \<or> Q = \<bottom>\<close>
  by (simp add: BOT_iff_D D_Ndet)

lemma Sync_is_BOT_iff: \<open>P \<lbrakk>S\<rbrakk> Q = \<bottom> \<longleftrightarrow> P = \<bottom> \<or> Q = \<bottom>\<close>
  by (rule HOL.sym, intro iffI, metis Sync_BOT Sync_commute)
     (use empty_setinterleaving in \<open>auto simp add: BOT_iff_D D_Sync\<close>)


lemma STOP_neq_BOT: \<open>STOP \<noteq> \<bottom>\<close>
  by (simp add: D_STOP BOT_iff_D)

lemma SKIP_neq_BOT: \<open>SKIP \<noteq> \<bottom>\<close>
  by (simp add: D_SKIP BOT_iff_D)


lemma Mprefix_neq_BOT: \<open>Mprefix A P \<noteq> \<bottom>\<close>
  by (simp add: BOT_iff_D)

lemma Mndetprefix_neq_BOT: \<open>Mndetprefix A P \<noteq> \<bottom>\<close>
  by (cases \<open>A = {}\<close>) (simp_all add: D_STOP BOT_iff_D D_Mndetprefix write0_def)


lemma STOP_T_iff: \<open>STOP \<sqsubseteq>\<^sub>T P \<longleftrightarrow> P = STOP\<close>
  by auto (metis Nil_elem_T STOP_iff_T empty_iff subset_singletonD trace_refine_def)

lemma STOP_F_iff: \<open>STOP \<sqsubseteq>\<^sub>F P \<longleftrightarrow> P = STOP\<close>
  by auto (metis Nil_elem_T STOP_iff_T empty_iff leF_imp_leT
                 subset_singletonD trace_refine_def)

lemma STOP_FD_iff: \<open>STOP \<sqsubseteq>\<^sub>F\<^sub>D P \<longleftrightarrow> P = STOP\<close>
  using STOP_F_iff idem_FD leFD_imp_leF by blast

lemma SKIP_FD_iff: \<open>SKIP \<sqsubseteq>\<^sub>F\<^sub>D P \<longleftrightarrow> P = SKIP\<close>
  apply (subst Process_eq_spec,
         auto simp: failure_divergence_refine_def le_ref_def F_SKIP D_SKIP subset_iff)
  by (metis F_T insertI1 is_processT5_S6 is_processT6_S2)
     (metis F_T append.left_neutral insertI1 is_processT5_S6 tick_T_F)

lemma SKIP_F_iff: \<open>SKIP \<sqsubseteq>\<^sub>F P \<longleftrightarrow> P = SKIP\<close>
  apply (subst Process_eq_spec,
         auto simp: Process_eq_spec failure_refine_def le_ref_def F_SKIP D_SKIP subset_iff)
    apply (metis F_T insertI1 is_processT5_S6 is_processT6_S2)
   apply (metis F_T append.left_neutral insertI1 is_processT5_S6 tick_T_F)
  by (metis append_Nil insertI1 neq_Nil_conv process_charn)


lemma Seq_is_SKIP_iff: \<open>P \<^bold>; Q = SKIP \<longleftrightarrow> P = SKIP \<and> Q = SKIP\<close>
proof (intro iffI)
  show \<open>P = SKIP \<and> Q = SKIP \<Longrightarrow> P \<^bold>; Q = SKIP\<close>
    by (simp add: Seq_SKIP)
next
  have \<open>P \<^bold>; Q = SKIP \<Longrightarrow> (Q = SKIP \<longrightarrow> P = SKIP) \<and> Q = SKIP\<close>
  proof (intro conjI impI)
    show \<open>P \<^bold>; Q = SKIP \<Longrightarrow> Q = SKIP \<Longrightarrow> P = SKIP\<close>
      by (simp add: Seq_SKIP)
  next
    show \<open>P \<^bold>; Q = SKIP \<Longrightarrow> Q = SKIP\<close>
      apply (subst (asm) SKIP_F_iff[symmetric], subst SKIP_F_iff[symmetric])
      unfolding failure_refine_def
      apply (subst (asm) subset_iff, subst subset_iff)
      by (auto simp add:F_Seq F_SKIP)
         (metis (no_types, opaque_lifting) F_T append_Nil insert_absorb insert_iff
                                           is_processT5_S6 tickFree_Nil)+
  qed
  thus \<open>P \<^bold>; Q = SKIP \<Longrightarrow> P = SKIP \<and> Q = SKIP\<close> by blast
qed



section \<open>The Renaming Operator\<close>

subsection\<open>Some Preliminaries\<close>


setup_lifting type_definition_process


definition EvExt where \<open>EvExt f x \<equiv> case_event (ev o f) tick x\<close>


definition finitary :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> bool\<close> 
  where \<open>finitary f \<equiv> \<forall>x. finite (f -` {x})\<close>



text \<open>We start with some simple results.\<close>

lemma \<open>f -` {} = {}\<close> by simp

lemma \<open>X \<subseteq> Y \<Longrightarrow> f -` X \<subseteq> f -` Y\<close> by (rule vimage_mono)

lemma \<open>f -`(X \<union> Y) = f -` X \<union> f -` Y\<close> by (rule vimage_Un)


lemma EvExt_id: \<open>EvExt id = id\<close>
  unfolding id_def EvExt_def by (metis comp_apply event.exhaust event.simps(4, 5))

lemma EvExt_eq_tick: \<open>EvExt f a = tick \<longleftrightarrow> a = tick\<close>
  by (metis EvExt_def comp_apply event.exhaust event.simps(3, 4, 5))

lemma tick_eq_EvExt: \<open>tick = EvExt f a \<longleftrightarrow> a = tick\<close>
  by (metis EvExt_eq_tick)

lemma EvExt_ev1:
  \<open>EvExt f b = ev a \<longleftrightarrow> (\<exists>c. b = ev c \<and> EvExt f (ev c) = ev a)\<close>
  by (metis event.exhaust event.simps(3) tick_eq_EvExt)

lemma EvExt_tF: \<open>tickFree (map (EvExt f) s) \<longleftrightarrow> tickFree s\<close> 
  unfolding tickFree_def by (auto simp add: tick_eq_EvExt image_iff)

lemma inj_EvExt: \<open>inj EvExt\<close>
  unfolding inj_on_def EvExt_def
  by auto (metis comp_eq_dest_lhs event.simps(4, 5) ext)




lemma EvExt_ftF: \<open>front_tickFree (map (EvExt f) s) \<longleftrightarrow> front_tickFree s\<close> 
  unfolding front_tickFree_def
  by safe (metis (no_types, opaque_lifting) EvExt_tF map_tl rev_map)+
 

lemma map_EvExt_tick: \<open>[tick] = map (EvExt f) t \<longleftrightarrow> t = [tick]\<close>
  using tick_eq_EvExt by fastforce


lemma anteced_EvExt_diff_tick:
  \<open>EvExt f -` (X - {tick}) = EvExt f -` X - {tick}\<close>
  by (rule subset_antisym)
     (simp_all add: EvExt_eq_tick subset_Diff_insert subset_vimage_iff)
  


lemma   ev_elem_anteced1: \<open>ev a \<in> EvExt f -` A \<longleftrightarrow> ev (f a) \<in> A\<close>
  and tick_elem_anteced1: \<open>tick \<in> EvExt f -` A \<longleftrightarrow> tick \<in> A\<close>
  unfolding EvExt_def by simp_all
  

lemma hd_map_EvExt:
  \<open>t \<noteq> [] \<Longrightarrow> hd t = ev a \<Longrightarrow> hd (map (EvExt f) t) = ev (f a)\<close>
  and tl_map_EvExt: \<open>t \<noteq> [] \<Longrightarrow> tl (map (EvExt f) t) = map (EvExt f) (tl t)\<close>
  by (simp_all add: EvExt_def list.map_sel(1) map_tl)



subsection\<open>The Renaming Operator Definition\<close>

lift_definition Renaming :: \<open>['a process, 'a \<Rightarrow> 'b] \<Rightarrow> 'b process\<close>
  is \<open>\<lambda>P f. ({(s, R). \<exists>s1. (s1, (EvExt f) -` R) \<in> \<F> P \<and>
                           s = map (EvExt f) s1} \<union>
             {(s ,R). \<exists>s1 s2. tickFree s1 \<and> front_tickFree s2 \<and> 
                              s = (map (EvExt f) s1) @ s2 \<and> s1 \<in> \<D> P},
             {t. \<exists> s1 s2. tickFree s1 \<and> front_tickFree s2 \<and>
                          t = (map (EvExt f) s1) @ s2 \<and> s1 \<in> \<D> P})\<close>
proof -
  show \<open>?thesis P f\<close> (is "is_process(?f, ?d)") for P f
    unfolding is_process_def FAILURES_def DIVERGENCES_def fst_conv snd_conv
  proof (intro conjI allI impI)
    show \<open>([], {}) \<in> ?f\<close>
      by (simp add: process_charn)
  next
    show \<open>(s, X) \<in> ?f \<Longrightarrow> front_tickFree s\<close> for s X
      by (auto simp add: EvExt_ftF is_processT2 EvExt_tF front_tickFree_append)
  next
    show \<open>(s @ t, {}) \<in> ?f \<Longrightarrow> (s, {}) \<in> ?f\<close> for s t
    proof (induct t rule: rev_induct)
      show \<open>(s @ [], {}) \<in> ?f \<Longrightarrow> (s, {}) \<in> ?f\<close> by simp
    next
      fix t x
      assume  hyp : \<open>(s @ t, {}) \<in> ?f \<Longrightarrow> (s, {}) \<in> ?f\<close>
         and prem : \<open>(s @ t @ [x], {}) \<in> ?f\<close>
      from prem consider \<open>\<exists>s1. (s1, {}) \<in> \<F> P \<and> s @ t @ [x] = map (EvExt f) s1\<close>
        | \<open>\<exists>s1. tickFree s1 \<and> (\<exists>s2. front_tickFree s2 \<and> 
                s @ t @ [x] = map (EvExt f) s1 @ s2 \<and> s1 \<in> \<D> P)\<close> by fast
      thus \<open>(s, {}) \<in> ?f\<close>
      proof cases
        assume \<open>\<exists>s1. (s1, {}) \<in> \<F> P \<and> s @ t @ [x] = map (EvExt f) s1\<close>
        then obtain s1 where * : \<open>(s1, {}) \<in> \<F> P\<close> \<open>s @ t @ [x] = map (EvExt f) s1\<close> by blast
        hence \<open>(butlast s1, {}) \<in> \<F> P\<close> \<open>s @ t = map (EvExt f) (butlast s1)\<close>
          by (metis append_butlast_last_id butlast.simps(1) is_processT3_SR)
             (metis "*"(2) append.assoc butlast_snoc map_butlast)
        with hyp show \<open>(s, {}) \<in> ?f\<close> by auto
      next
        assume \<open>\<exists>s1. tickFree s1 \<and> (\<exists>s2. front_tickFree s2 \<and>
                     s @ t @ [x] = map (EvExt f) s1 @ s2 \<and> s1 \<in> \<D> P)\<close>
        then obtain s1 s2
          where * : \<open>tickFree s1\<close> \<open>front_tickFree s2\<close>
                    \<open>s @ t @ [x] = map (EvExt f) s1 @ s2\<close> \<open>s1 \<in> \<D> P\<close> by blast
        show \<open>(s, {}) \<in> ?f\<close>
        proof (cases s2 rule: rev_cases)
          from "*"(3, 4) show \<open>s2 = [] \<Longrightarrow> (s, {}) \<in> ?f\<close>
            by (simp add: append_eq_map_conv)
               (metis NT_ND T_F is_processT3_ST)
        next
          fix y s2'
          assume \<open>s2 = s2' @ [y]\<close>
          with "*" front_tickFree_dw_closed have \<open>(s @ t, {}) \<in> ?f\<close> by simp blast
          thus \<open>(s, {}) \<in> ?f\<close> by (rule hyp)
        qed
      qed
    qed
  next
    show \<open>(s, Y) \<in> ?f \<and> X \<subseteq> Y \<Longrightarrow> (s, X) \<in> ?f\<close> for s X Y
      apply (induct s rule: rev_induct, simp_all)
      by (meson is_processT4 vimage_mono)
         (metis process_charn vimage_mono)
  next
    show \<open>(s, X) \<in> ?f \<and> (\<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> ?f) \<Longrightarrow> (s, X \<union> Y) \<in> ?f\<close> for s X Y
      by auto (metis (no_types, lifting) is_processT5 list.simps(8, 9) map_append vimageE)
  next
    show \<open>(s @ [tick], {}) \<in> ?f \<Longrightarrow> (s, X - {tick}) \<in> ?f\<close> for s X
      apply (simp, elim disjE)
      by (metis (no_types, lifting) anteced_EvExt_diff_tick is_processT6 map_EvExt_tick 
                                    map_eq_append_conv)
         (metis EvExt_tF append.assoc butlast_snoc front_tickFree_charn non_tickFree_tick
                tickFree_Nil tickFree_append tickFree_implies_front_tickFree)
  next
    show \<open>s \<in> ?d \<and> tickFree s \<and> front_tickFree t \<Longrightarrow> s @ t \<in> ?d\<close> for s t
      using front_tickFree_append by safe auto
  next
    show \<open>s \<in> ?d \<Longrightarrow> (s, X) \<in> ?f\<close> for s X by blast
      
  next
    fix s
    assume \<open>s @ [tick] \<in> ?d\<close>
    then obtain t1 t2 
      where \<open>tickFree t1\<close> \<open>front_tickFree t2\<close> 
            \<open>s @ [tick] = map (EvExt f) t1 @ t2\<close> \<open>t1 \<in> \<D> P\<close> by blast
    thus \<open>s \<in> ?d\<close>
      apply simp
      apply (rule_tac x = t1 in exI, simp)
      apply (rule_tac x = \<open>butlast t2\<close> in exI)
      by (metis EvExt_tF butlast_append butlast_snoc front_tickFree_butlast
                non_tickFree_tick tickFree_append tickFree_butlast)
  qed
qed


text \<open>Some syntaxic sugar\<close>

syntax
  "_Renaming"  :: \<open>'a process \<Rightarrow> updbinds \<Rightarrow> 'a process\<close> (\<open>_\<lbrakk>_\<rbrakk>\<close> [100, 100]) (*see the values we need, at least 51*)
translations
  "_Renaming P updates" \<rightleftharpoons> "CONST Renaming P (_Update (CONST id) updates)"


text \<open>Now we can write \<^term>\<open>P\<lbrakk>a := b\<rbrakk>\<close>. But like in \<^theory>\<open>HOL.Fun\<close>, we can write this kind of
      expression with as many updates we want: \<^term>\<open>P\<lbrakk>a := b, c := d, e := f, g := h\<rbrakk>\<close>.
      By construction we also inherit all the results about \<^const>\<open>fun_upd\<close>, for example:

      @{thm fun_upd_other[no_vars] fun_upd_upd[no_vars] fun_upd_twist[no_vars]}.\<close>

lemma \<open>P\<lbrakk>x := y, x := z\<rbrakk> = P\<lbrakk>x := z\<rbrakk>\<close> by simp

lemma \<open>a \<noteq> c \<Longrightarrow> P\<lbrakk>a := b, c := d\<rbrakk> = P\<lbrakk>c := d, a := b\<rbrakk>\<close>
  by (simp add: fun_upd_twist)




subsection\<open>The Projections\<close>

lemma F_Renaming: \<open>\<F> (Renaming P f) = 
  {(s, R). \<exists>s1. (s1, EvExt f -` R) \<in> \<F> P \<and> s = map (EvExt f) s1} \<union>
  {(s, R). \<exists>s1 s2. tickFree s1 \<and> front_tickFree s2 \<and> 
                   s = map (EvExt f) s1 @ s2 \<and> s1 \<in> \<D> P}\<close>
  by (simp add: Failures_def FAILURES_def Renaming.rep_eq)

lemma D_Renaming:
  \<open>\<D> (Renaming P f) = {t. \<exists>s1 s2. tickFree s1 \<and> front_tickFree s2 \<and> 
                                   t = map (EvExt f) s1 @ s2 \<and> s1 \<in> \<D> P}\<close>
  by (simp add: Divergences_def DIVERGENCES_def Renaming.rep_eq)

lemma T_Renaming: \<open>\<T> (Renaming P f) = 
  {t. \<exists>t1. t1 \<in> \<T> P \<and> t = map (EvExt f) t1} \<union> 
  {t. \<exists>t1 t2. tickFree t1 \<and> front_tickFree t2 \<and> 
              t = map (EvExt f) t1 @ t2 \<and> t1 \<in> \<D> P}\<close>
  by (auto simp add: Traces_def TRACES_def Failures_def[symmetric] F_Renaming)
     (metis F_T T_F vimage_empty)



subsection\<open>Continuity Rule\<close>

subsubsection \<open>Monotonicity of \<^const>\<open>Renaming\<close>.\<close>

lemma mono_Renaming[simp] : \<open>(Renaming P f) \<sqsubseteq> (Renaming Q f)\<close> if \<open>P \<sqsubseteq> Q\<close>
proof (unfold le_approx_def, intro conjI subset_antisym subsetI allI impI)
  show \<open>s \<in> \<D> (Renaming Q f) \<Longrightarrow> s \<in> \<D> (Renaming P f)\<close> for s
    using that[THEN le_approx1] by (auto simp add: D_Renaming)
next
  show \<open>s \<notin> \<D> (Renaming P f) \<Longrightarrow> 
        X \<in> \<R>\<^sub>a (Renaming P f) s \<Longrightarrow> X \<in> \<R>\<^sub>a (Renaming Q f) s\<close> for s X
    using that[THEN le_approx2] apply (simp add: Ra_def D_Renaming F_Renaming)
    by (metis (no_types, opaque_lifting)  append.right_neutral butlast.simps(2) 
              front_tickFree_butlast front_tickFree_mono list.distinct(1) 
              map_EvExt_tick map_append nonTickFree_n_frontTickFree process_charn)
next
  show \<open>s \<notin> \<D> (Renaming P f) \<Longrightarrow>
        X \<in> \<R>\<^sub>a (Renaming Q f) s \<Longrightarrow> X \<in> \<R>\<^sub>a (Renaming P f) s\<close> for s X
    using that[THEN le_approx2] that[THEN le_approx1]
    by (simp add: Ra_def D_Renaming F_Renaming subset_iff)
       (metis is_processT8_S)
next
  fix s
  assume * : \<open>s \<in> min_elems (\<D> (Renaming P f))\<close>
  from elem_min_elems[OF "*"] obtain s1 s2
    where ** : \<open>tickFree s1\<close> \<open>front_tickFree s2\<close>
               \<open>s = map (EvExt f) s1 @ s2\<close> \<open>s1 \<in> \<D> P\<close>
               \<open>front_tickFree s\<close>
    using D_imp_front_tickFree D_Renaming by blast
  with min_elems_no[OF "*", of \<open>butlast s\<close>] have \<open>s2 = []\<close>
    by (cases s rule: rev_cases; simp add: D_Renaming)
       (metis butlast_append butlast_snoc front_tickFree_butlast less_self 
              nless_le tickFree_implies_front_tickFree)
  with "**" min_elems_no[OF "*", of \<open>butlast s\<close>] have \<open>s1 \<in> min_elems (\<D> P)\<close>
    apply (cases s; simp add: D_Renaming Nil_min_elems)
    by (metis (no_types, lifting) D_imp_front_tickFree append.right_neutral butlast_snoc
                                  front_tickFree_charn less_self list.discI
                                  list.map_disc_iff map_butlast min_elems1 nless_le)
  hence \<open>s1 \<in> \<T> Q\<close> using that[THEN le_approx3] by blast
  show \<open>s \<in> \<T> (Renaming Q f)\<close>
    apply (simp add: "**"(3) \<open>s2 = []\<close> T_Renaming)
    using \<open>s1 \<in> \<T> Q\<close> by blast
qed

 

lemma \<open>{ev c |c. f c = a} = ev ` {c . f c = a}\<close> by (rule setcompr_eq_image)


lemma vimage_EvExt_subset_vimage: \<open>EvExt f -` (ev ` A) \<subseteq> insert tick (ev ` (f -` A))\<close>
  and vimage_subset_vimage_EvExt: \<open>(ev ` (f -` A)) \<subseteq> (EvExt f -` (ev ` A)) - {tick}\<close>
  unfolding EvExt_def by auto (metis comp_apply event.exhaust event.simps(4) image_iff vimage_eq)



subsubsection \<open>Useful Results about \<^const>\<open>finitary\<close>, and Preliminaries Lemmas for Continuity.\<close>

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
  show \<open>finite {x. (if x = a then b else f x) \<in> {y}}\<close>
    if \<open>\<forall>y. finite {x. f x \<in> {y}}\<close> for y
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
    

lemma le_snoc_is : \<open>t \<le> s @ [x] \<longleftrightarrow> t = s @ [x] \<or> t \<le> s\<close>
  by (metis append_eq_first_pref_spec le_list_def order.trans self_append_conv)


lemma Cont_RenH2: \<open>finitary (EvExt f) \<longleftrightarrow> finitary f\<close>
proof -
  have inj_ev: \<open>inj ev\<close> by (simp add: inj_def)
  show \<open>finitary (EvExt f) \<longleftrightarrow> finitary f\<close>
    apply (subst finitary_comp_iff[of ev f, symmetric, OF inj_imp_finitary[OF inj_ev]])
  proof (intro iffI; subst finitary_def, intro allI)
    have inj_ev: \<open>inj ev\<close> by (simp add: inj_def)
    show \<open>finite ((ev \<circ> f) -` {x})\<close> if \<open>finitary (EvExt f)\<close> for x
      apply (fold vimage_comp)
    proof (cases \<open>x = tick\<close>, (insert finite.simps)[1], blast) 
      assume \<open>x \<noteq> tick\<close>
      with subset_singletonD[OF inj_vimage_singleton[OF inj_ev, of x]] obtain y 
        where f1: \<open>ev -` {x} = {y}\<close>
        by auto (metis empty_iff event.exhaust vimage_singleton_eq)
      have f2: \<open>(f -` {y}) = ev -` ev ` f -` {y}\<close> by (simp add: inj_ev inj_vimage_image_eq)
      show \<open>finite (f -` ev -` {x})\<close> 
        apply (subst f1, subst f2)
        apply (rule finite_vimageI[OF _ inj_ev]) 
        apply (rule finite_subset[OF vimage_subset_vimage_EvExt])
        apply (rule finite_Diff)
        using finitary_def that by fastforce
    qed
  next
    show \<open>finite (EvExt f -` {x})\<close> if \<open>finitary (ev \<circ> f)\<close> for x
    proof (cases \<open>x = tick\<close>,
           metis Diff_cancel anteced_EvExt_diff_tick finite.emptyI
                 infinite_remove vimage_empty)
      assume \<open>x \<noteq> tick\<close>
      with subset_singletonD[OF inj_vimage_singleton[OF inj_ev, of x]] obtain y 
        where f1: \<open>{x} = ev ` {y}\<close> using event.exhaust by auto
      show \<open>finite (EvExt f -` {x})\<close>
        apply (subst f1)
        apply (rule finite_subset[OF vimage_EvExt_subset_vimage])
        apply (subst finite_insert)
        apply (rule finite_imageI)
        by (fact finitary_comp_iff
                 [OF inj_imp_finitary[OF inj_ev], of f, 
                  simplified that, simplified, unfolded finitary_def, rule_format])
    qed
  qed 
qed



lemma Cont_RenH3:
  \<open>{s1 @ t1 |s1 t1. (\<exists> b. s1 = [b] & f b = a) \<and> list = map f t1} = 
   (\<Union> b \<in> f -`{a}. (\<lambda>t. b # t) ` {t. list = map f t})\<close>
  by auto (metis append_Cons append_Nil)


lemma Cont_RenH4: \<open>finitary f \<longleftrightarrow> (\<forall>s. finite {t. s = map f t})\<close>
proof (unfold finitary_def, intro iffI allI)
  show \<open>finite {t. s = map f t}\<close> if \<open>\<forall>x. finite (f -` {x})\<close>for s
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



lemma Cont_RenH5: \<open>finite (\<Union>t \<in> {t. t \<le> (s :: '\<alpha> trace)}. {s. t=map (EvExt f) s})\<close> if \<open>finitary f\<close>
  apply (rule finite_UN_I)
   apply (induct s rule: rev_induct)
    apply (simp; fail)
   apply (simp add: le_snoc_is; fail)
  using Cont_RenH2 Cont_RenH4 that by blast



lemma Cont_RenH6:
  \<open>{t. \<exists> t2. tickFree t \<and> front_tickFree t2 \<and> x = map (EvExt f) t @ t2} 
   \<subseteq> {y. \<exists>xa. xa \<in> {t. t \<le> x} \<and> y \<in> {s. xa = map (EvExt f) s}}\<close>
  by (auto simp add: le_list_def)



lemma Cont_RenH7:
  \<open>finite {t. \<exists>t2. tickFree t \<and> front_tickFree t2 \<and> s = map (EvExt f) t @ t2}\<close>
  if \<open>finitary f\<close>
proof -
  have f1: \<open>{y. map (EvExt f) y \<le> s} =
            (\<Union>z \<in> {z. z \<le> s}. {y. z = map (EvExt f) y})\<close> by fast
  show ?thesis
    apply (rule finite_subset[OF Cont_RenH6])
    apply (simp add: f1)
    apply (rule finite_UN_I)
     apply (induct s rule: rev_induct)
      apply (simp; fail)
     apply (simp add: le_snoc_is; fail)
    using Cont_RenH2 Cont_RenH4 that by blast
qed


lemma chain_Renaming: \<open>chain Y \<Longrightarrow> chain (\<lambda>i. Renaming (Y i) f)\<close>
  by (simp add: chain_def) 



text \<open>A key lemma for the continuity.\<close>

lemma Inter_nonempty_finite_chained_sets:
  \<open>\<forall>i. S i \<noteq> {} \<Longrightarrow> finite (S 0) \<Longrightarrow> \<forall>i. S (Suc i) \<subseteq> S i \<Longrightarrow> (\<Inter>i. S i) \<noteq> {}\<close>
proof (induct \<open>card (S 0)\<close> arbitrary: S rule: nat_less_induct)
  case 1
  show ?case
  proof (cases \<open>\<forall>i. S i = S 0\<close>)
    case True
    thus ?thesis by (metis "1.prems"(1) INT_iff ex_in_conv)
  next 
    case False
    have f1: \<open>i \<le> j \<Longrightarrow> S j \<subseteq> S i\<close> for i j by (simp add: "1.prems"(3) lift_Suc_antimono_le)
    with False obtain j m where f2: \<open>m < card (S 0)\<close> and f3: \<open>m = card (S j)\<close>
      by (metis "1.prems"(2) psubsetI psubset_card_mono zero_le)
    define T where \<open>T i \<equiv> S (i + j)\<close> for i
    have f4: \<open>m = card (T 0)\<close> unfolding T_def by (simp add: f3)
    from f1 have f5: \<open>(\<Inter>i. S i) = (\<Inter>i. T i)\<close>
      unfolding T_def by (auto intro: le_add1)
    show ?thesis
      apply (subst f5)
      apply (rule "1.hyps"[rule_format, OF f2, of T, OF f4], unfold T_def)
      by (simp_all add: "1.prems"(1, 3) lift_Suc_antimono_le)
         (metis "1.prems"(2) add_0 f1 finite_subset le_add1)
  qed
qed



subsubsection \<open>Finally, Continuity !\<close>

lemma Cont_Renaming_prem:
  \<open>(\<Squnion> i. Renaming (Y i) f) = (Renaming (\<Squnion> i. Y i) f)\<close> if finitary: \<open>finitary f\<close> 
   and chain: \<open>chain Y\<close>
proof (subst Process_eq_spec, safe)
  fix s
  define S where \<open>S i \<equiv> {s1. \<exists>t2. tickFree s1 \<and> front_tickFree t2 \<and>
                                   s = map (EvExt f) s1 @ t2 \<and> s1 \<in> \<D> (Y i)}\<close> for i
  assume \<open>s \<in> \<D> (\<Squnion>i. Renaming (Y i) f)\<close>
  hence \<open>s \<in> \<D> (Renaming (Y i) f)\<close> for i
    by (simp add: limproc_is_thelub chain chain_Renaming D_LUB)

  hence \<open>\<forall>i. S i \<noteq> {}\<close> by (simp add: S_def D_Renaming) blast
  moreover have \<open>finite (S 0)\<close>
    unfolding S_def 
    by (rule finite_subset[OF _ Cont_RenH7[OF finitary, of s]], blast)
  moreover have \<open>\<forall>i. S (Suc i) \<subseteq> S i\<close>
    unfolding S_def using NF_ND po_class.chainE[OF chain]
                          proc_ord2a le_approx_def by blast
  ultimately have \<open>(\<Inter>i. S i) \<noteq> {}\<close>
    by (rule Inter_nonempty_finite_chained_sets)    
  
  thus \<open>s \<in> \<D> (Renaming (Lub Y) f)\<close>
    by (simp add: limproc_is_thelub chain D_Renaming
                  D_LUB ex_in_conv[symmetric] S_def) blast
next
  show \<open>s \<in> \<D> (Renaming (Lub Y) f) \<Longrightarrow> s \<in> \<D> (\<Squnion>i. Renaming (Y i) f)\<close> for s
    by (auto simp add: limproc_is_thelub chain chain_Renaming D_Renaming D_LUB)
next
  fix s X
  define S where \<open>S i \<equiv> {s1. (s1, EvExt f -` X) \<in> \<F> (Y i) \<and> s = map (EvExt f) s1} \<union>
                         {s1. \<exists>t2. tickFree s1 \<and> front_tickFree t2 \<and> 
                                   s = map (EvExt f) s1 @ t2 \<and> s1 \<in> \<D> (Y i)}\<close> for i
  assume \<open>(s, X) \<in> \<F> (\<Squnion>i. Renaming (Y i) f)\<close>
  hence \<open>(s, X) \<in> \<F> (Renaming (Y i) f)\<close> for i
    by (simp add: limproc_is_thelub chain_Renaming[OF chain] F_LUB)

  hence \<open>\<forall>i. S i \<noteq> {}\<close> by (auto simp add: S_def F_Renaming)
  moreover have \<open>finite (S 0)\<close>
    unfolding S_def
    apply (subst finite_Un, intro conjI)
     apply (rule finite_subset[of _ \<open>{s1. s = map (EvExt f) s1}\<close>], blast)
     apply (insert Cont_RenH2 Cont_RenH4 finitary, blast)
    by (rule finite_subset[OF _ Cont_RenH7[OF finitary, of s]], blast)
  moreover have \<open>\<forall>i. S (Suc i) \<subseteq> S i\<close>
    unfolding S_def using NF_ND po_class.chainE[OF chain]
                          proc_ord2a le_approx_def by safe blast+
  ultimately have \<open>(\<Inter>i. S i) \<noteq> {}\<close>
    by (rule Inter_nonempty_finite_chained_sets)
   
  thus \<open>(s, X) \<in> \<F> (Renaming (Lub Y) f)\<close>
    by (simp add: F_Renaming limproc_is_thelub chain D_LUB 
                  F_LUB ex_in_conv[symmetric] S_def) (meson NF_ND)
next
  show \<open>(s, X) \<in> \<F> (Renaming (Lub Y) f) \<Longrightarrow> (s, X) \<in> \<F> (\<Squnion>i. Renaming (Y i) f)\<close> for s X
    by (auto simp add: limproc_is_thelub chain chain_Renaming F_Renaming D_LUB F_LUB)  
qed
 

lemma Renaming_cont[simp] : \<open>cont P \<Longrightarrow> finitary f \<Longrightarrow> cont (\<lambda>x. (Renaming (P x) f))\<close>
  by (rule contI2)
     (simp add: cont2monofunE monofunI, simp add: Cont_Renaming_prem ch2ch_cont cont2contlubE)


lemma RenamingF_cont : \<open>cont P \<Longrightarrow> cont (\<lambda>x. (P x)\<lbrakk>a := b\<rbrakk>)\<close>
  (* by simp *)
  by (simp only: Renaming_cont finitary_updated_iff inj_imp_finitary inj_on_id)


lemma \<open>cont P \<Longrightarrow> cont (\<lambda>x. (P x)\<lbrakk>a := b, c := d, e := f, g := a\<rbrakk>)\<close>
  (* by simp *)
  apply (erule Renaming_cont)
  apply (simp only: finitary_updated_iff)
  apply (rule inj_imp_finitary)
  by (rule inj_on_id)
  
 



subsection \<open>Nice Properties\<close>


lemma EvExt_comp: \<open>EvExt (g \<circ> f) = EvExt g \<circ> EvExt f\<close>
  unfolding EvExt_def by (auto split: event.split)  
  


lemma Renaming_comp : \<open>Renaming P (g o f) = Renaming (Renaming P f) g\<close>
proof (subst Process_eq_spec, intro conjI subset_antisym)
  show \<open>\<F> (Renaming P (g \<circ> f)) \<subseteq> \<F> (Renaming (Renaming P f) g)\<close>
    apply (simp add: F_Renaming D_Renaming subset_iff, safe)
    by (metis (no_types, opaque_lifting) EvExt_comp list.map_comp set.compositionality)
       (metis (no_types, opaque_lifting) EvExt_comp EvExt_tF append.right_neutral 
                                         front_tickFree_Nil list.map_comp)
next
  show \<open>\<F> (Renaming (Renaming P f) g) \<subseteq> \<F> (Renaming P (g \<circ> f))\<close>
    by (auto simp add: F_Renaming D_Renaming EvExt_comp EvExt_ftF EvExt_tF front_tickFree_append)
       (metis (no_types, opaque_lifting) EvExt_comp list.map_comp set.compositionality)
next
  show \<open>\<D> (Renaming P (g \<circ> f)) \<subseteq> \<D> (Renaming (Renaming P f) g)\<close>
    by (simp add: D_Renaming subset_iff, safe)
       (metis (no_types, opaque_lifting) EvExt_comp EvExt_tF append.right_neutral 
                                         front_tickFree_Nil list.map_comp)
next
  show \<open>\<D> (Renaming (Renaming P f) g) \<subseteq> \<D> (Renaming P (g \<circ> f))\<close>
    by (auto simp add: D_Renaming subset_iff)
       (metis EvExt_comp EvExt_tF front_tickFree_append)
qed




lemma Renaming_id: \<open>Renaming P id = P\<close>
  by (auto simp add: Process_eq_spec F_Renaming D_Renaming EvExt_id 
                     is_processT7_S is_processT8_S)
     (metis append.right_neutral front_tickFree_mono list.distinct(1) 
            nonTickFree_n_frontTickFree process_charn)
  

lemma Renaming_inv: \<open>Renaming (Renaming P f) (inv f) = P\<close> if \<open>inj f\<close>
  apply (subst Renaming_comp[symmetric])
  apply (subst inv_o_cancel[OF that])
  by (fact Renaming_id) 


subsection \<open>Renaming Laws\<close>

lemma Renaming_BOT: \<open>Renaming \<bottom> f = \<bottom>\<close>
  by (fastforce simp add: F_UU D_UU F_Renaming D_Renaming EvExt_tF EvExt_ftF
                          Process_eq_spec front_tickFree_append intro: tickFree_Nil)+
  

lemma Renaming_STOP: \<open>Renaming STOP f = STOP\<close>
  by (subst Process_eq_spec) (simp add: EvExt_ftF F_STOP D_STOP F_Renaming D_Renaming)


lemma Renaming_SKIP: \<open>Renaming SKIP f = SKIP\<close>
  by (subst Process_eq_spec) (force simp add: EvExt_def F_SKIP D_SKIP F_Renaming D_Renaming)



lemma Renaming_Ndet:
  \<open>Renaming (P \<sqinter> Q) f = Renaming P f \<sqinter> Renaming Q f\<close>
  by (subst Process_eq_spec) (auto simp add: F_Renaming D_Renaming F_Ndet D_Ndet)


lemma Renaming_Det:
  \<open>Renaming (P \<box> Q) f = Renaming P f \<box> Renaming Q f\<close>
proof (subst Process_eq_spec, intro iffI conjI subset_antisym)
  show \<open>\<F> (Renaming (P \<box> Q) f) \<subseteq> \<F> (Renaming P f \<box> Renaming Q f)\<close>
    apply (simp add: F_Renaming D_Renaming T_Renaming F_Det D_Det, safe,
           simp_all add: is_processT6_S2)
    by blast+ (metis EvExt_eq_tick, meson map_EvExt_tick)+
next 
  show \<open>\<F> (Renaming P f \<box> Renaming Q f) \<subseteq> \<F> (Renaming (P \<box> Q) f)\<close>
    apply (simp add: F_Renaming D_Renaming T_Renaming F_Det D_Det, safe, simp_all)
    by blast+ (metis EvExt_eq_tick, metis Cons_eq_append_conv EvExt_tF 
                     list.map_disc_iff tickFree_Cons)+
next
  show \<open>\<D> (Renaming (P \<box> Q) f) \<subseteq> \<D> (Renaming P f \<box> Renaming Q f)\<close>
    by (auto simp add: D_Renaming D_Det)
next
  show \<open>\<D> (Renaming P f \<box> Renaming Q f) \<subseteq> \<D> (Renaming (P \<box> Q) f)\<close>
    by (auto simp add: D_Renaming D_Det)
qed


lemma mono_Mprefix_eq: \<open>\<forall>a \<in> A. P a = Q a \<Longrightarrow> Mprefix A P = Mprefix A Q\<close>
  by (auto simp add: Process_eq_spec F_Mprefix D_Mprefix)

lemma mono_Mndetprefix_eq: \<open>\<forall>a \<in> A. P a = Q a \<Longrightarrow> Mndetprefix A P = Mndetprefix A Q\<close>
  by (subst Process_eq_spec, cases \<open>A = {}\<close>) (auto simp add: F_Mndetprefix D_Mndetprefix)




lemma Renaming_Mprefix:
  \<open>Renaming (\<box> a \<in> A \<rightarrow> P (f a)) f = \<box> b \<in> f ` A \<rightarrow> Renaming (P b) f\<close>
  (is \<open>?lhs = ?rhs\<close>)
proof (subst Process_eq_spec_optimized, safe)
  show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close> for s
    by (auto simp add: D_Mprefix D_Renaming hd_map_EvExt) 
       (metis map_tl tickFree_tl)
next
  fix s
  assume \<open>s \<in> \<D> ?rhs\<close>
  then obtain a s' where * : \<open>a \<in> A\<close> \<open>s = EvExt f (ev a) # s'\<close> \<open>s' \<in> \<D> (Renaming (P (f a)) f)\<close>
    by (auto simp add: D_Mprefix EvExt_def) (metis list.collapse)
  from "*"(3) obtain t1 t2
    where ** : \<open>tickFree t1\<close> \<open>front_tickFree t2\<close>
               \<open>s' = map (EvExt f) t1 @ t2\<close> \<open>t1 \<in> \<D> (P (f a))\<close>
    by (simp add: D_Renaming) blast
  show \<open>s \<in> \<D> ?lhs\<close>
    apply (simp add: D_Renaming "*"(2))
    apply (rule_tac x = \<open>ev a # t1\<close> in exI, simp add: "**"(1))
    by (rule_tac x = t2 in exI, simp add: "**"(2, 3, 4) "*"(1) D_Mprefix)
next
  fix s X
  assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
  assume \<open>(s, X) \<in> \<F> ?lhs\<close>
  then consider \<open>s \<in> \<D> ?lhs\<close>
    | \<open>\<exists>s1. (s1, EvExt f -` X) \<in> \<F> (\<box>a \<in> A \<rightarrow> P (f a)) \<and> s = map (EvExt f) s1\<close>
    by (simp add: F_Renaming D_Renaming) blast
  thus \<open>(s, X) \<in> \<F> ?rhs\<close>
  proof cases
    from same_div D_F show \<open>s \<in> \<D> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> by blast
  next
    assume \<open>\<exists>s1. (s1, EvExt f -` X) \<in> \<F> (\<box>a \<in> A \<rightarrow> P (f a)) \<and> s = map (EvExt f) s1\<close>
    then obtain s1 where * : \<open>(s1, EvExt f -` X) \<in> \<F> (\<box>a \<in> A \<rightarrow> P (f a))\<close>
                             \<open>s = map (EvExt f) s1\<close> by blast
    from "*"(1) consider \<open>s1 = []\<close> \<open>EvExt f -` X \<inter> ev ` A = {}\<close>
      | \<open>\<exists>a s1'. a \<in> A \<and> s1 = ev a # s1' \<and> (s1', EvExt f -` X) \<in> \<F> (P (f a))\<close>
      by (simp add: F_Mprefix) (metis event.inject imageE list.collapse)
    thus \<open>(s, X) \<in> \<F> ?rhs\<close>
    proof cases
      show \<open>s1 = [] \<Longrightarrow> EvExt f -` X \<inter> ev ` A = {} \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
        by (simp add: F_Mprefix "*"(2) disjoint_iff image_iff)
           (metis ev_elem_anteced1 vimage_eq)
    next
      assume \<open>\<exists>a s1'. a \<in> A \<and> s1 = ev a # s1' \<and> (s1', EvExt f -` X) \<in> \<F> (P (f a))\<close>
      then obtain a s1' where ** : \<open>a \<in> A\<close> \<open>s1 = ev a # s1'\<close> 
                                   \<open>(s1', EvExt f -` X) \<in> \<F> (P (f a))\<close> by blast
      have *** : \<open>EvExt f (ev a) = ev (f a)\<close>
        by (metis hd_map hd_map_EvExt list.discI list.sel(1))
      show \<open>(s, X) \<in> \<F> ?rhs\<close>
        apply (simp add: F_Mprefix "*"(2) "**"(2), intro conjI)
        using "**"(1) "***" 
         apply blast
        apply (rule_tac x = \<open>f a\<close> in exI, simp add: "***")
        using "**"(3) by (simp add: F_Renaming) blast
    qed
  qed
next
  fix s X 
  assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
  assume \<open>(s, X) \<in> \<F> ?rhs\<close>
  then consider \<open>s = []\<close> \<open>X \<inter> ev ` f ` A = {}\<close>
    | \<open>\<exists>a s'. a \<in> A \<and> s = EvExt f (ev a) # s' \<and> (s', X) \<in> \<F> (Renaming (P (f a)) f)\<close>
    by (auto simp add: F_Mprefix EvExt_def) (metis list.collapse)
  thus \<open>(s, X) \<in> \<F> ?lhs\<close>
  proof cases
    show \<open>s = [] \<Longrightarrow> X \<inter> ev ` f ` A = {} \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
      by (auto simp add: F_Renaming F_Mprefix disjoint_iff EvExt_def)
  next
    assume \<open>\<exists>a s'. a \<in> A \<and> s = EvExt f (ev a) # s' \<and> (s', X) \<in> \<F> (Renaming (P (f a)) f)\<close>
    then obtain a s' where * : \<open>a \<in> A\<close> \<open>s = EvExt f (ev a) # s'\<close>
                               \<open>(s', X) \<in> \<F> (Renaming (P (f a)) f)\<close> by blast
    from "*"(3) consider \<open>s' \<in> \<D> (Renaming (P (f a)) f)\<close>
      | \<open>\<exists>s1. (s1, EvExt f -` X) \<in> \<F> (P (f a)) \<and> s' = map (EvExt f) s1\<close>
      by (simp add: F_Renaming D_Renaming) blast
    thus \<open>(s, X) \<in> \<F> ?lhs\<close>
    proof cases
      assume \<open>s' \<in> \<D> (Renaming (P (f a)) f)\<close>
      hence \<open>s \<in> \<D> ?rhs\<close>
        by (simp add: D_Mprefix "*"(2))
           (metis "*"(1) ev_elem_anteced1 imageI singletonI vimage_singleton_eq)
      with same_div D_F show \<open>(s, X) \<in> \<F> ?lhs\<close> by blast
    next
      assume \<open>\<exists>s1. (s1, EvExt f -` X) \<in> \<F> (P (f a)) \<and> s' = map (EvExt f) s1\<close>
      then obtain s1 where ** : \<open>(s1, EvExt f -` X) \<in> \<F> (P (f a))\<close>
                                \<open>s' = map (EvExt f) s1\<close> by blast
      show \<open>(s, X) \<in> \<F> ?lhs\<close>
        apply (simp add: F_Renaming "*"(2) "**"(2), rule disjI1)
        by (rule_tac x = \<open>ev a # s1\<close> in exI, simp add: F_Mprefix "*"(1) "**"(1))
    qed
  qed
qed



lemma Renaming_Mprefix_inj_on:
  \<open>Renaming (Mprefix A P) f = \<box> b \<in> f ` A \<rightarrow> Renaming (P (THE a. a \<in> A \<and> f a = b)) f\<close> 
  if inj_on_f: \<open>inj_on f A\<close>
  apply (subst Renaming_Mprefix[symmetric])
  apply (intro arg_cong[where f = \<open>\<lambda>Q. Renaming Q f\<close>] mono_Mprefix_eq)
  by (metis that the_inv_into_def the_inv_into_f_f)


corollary Renaming_Mprefix_inj:
  \<open>Renaming (Mprefix A P) f = \<box> b \<in> f ` A \<rightarrow> Renaming (P (THE a. f a = b)) f\<close> if inj_f: \<open>inj f\<close>
  apply (subst Renaming_Mprefix_inj_on, metis inj_eq inj_onI that)
  apply (rule mono_Mprefix_eq[rule_format])
  by (metis imageE inj_eq[OF inj_f])



text \<open>A smart application (as \<^term>\<open>f\<close> is of course injective on the singleton \<^term>\<open>{a}\<close>)\<close>

corollary Renaming_prefix: \<open>Renaming (a \<rightarrow> P) f = (f a \<rightarrow> Renaming P f)\<close>
  unfolding write0_def by (simp add: Renaming_Mprefix_inj_on)

(* TODO: write corollaries on read and write *)



lemma Renaming_Mndetprefix:
  \<open>Renaming (\<sqinter> a \<in> A \<rightarrow> P (f a)) f = \<sqinter> b \<in> f ` A \<rightarrow> Renaming (P b) f\<close>
  apply (cases \<open>A = {}\<close>, simp add: Renaming_STOP)
  by (subst Process_eq_spec)
     (auto simp add: F_Renaming F_Mndetprefix D_Renaming D_Mndetprefix Renaming_prefix[symmetric])


corollary Renaming_Mndetprefix_inj_on:
  \<open>Renaming (Mndetprefix A P) f = \<sqinter> b \<in> f ` A \<rightarrow> Renaming (P (THE a. a \<in> A \<and> f a = b)) f\<close> 
  if inj_on_f: \<open>inj_on f A\<close>
  apply (subst Renaming_Mndetprefix[symmetric])
  apply (intro arg_cong[where f = \<open>\<lambda>Q. Renaming Q f\<close>] mono_Mndetprefix_eq)
  by (metis that the_inv_into_def the_inv_into_f_f)
  


corollary Renaming_Mndetprefix_inj:
  \<open>Renaming (Mndetprefix A P) f = \<sqinter> b \<in> f ` A \<rightarrow>  Renaming (P (THE a. f a = b)) f\<close> 
  if inj_f: \<open>inj f\<close>
  apply (subst Renaming_Mndetprefix_inj_on, metis inj_eq inj_onI that)
  apply (rule mono_Mndetprefix_eq[rule_format])
  by (metis imageE inj_eq[OF inj_f])



lemma Renaming_Seq: 
  \<open>Renaming (P \<^bold>; Q) f = Renaming P f \<^bold>; Renaming Q f\<close> (is \<open>?lhs = ?rhs\<close>)
proof (subst Process_eq_spec_optimized, safe)
  show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close> for s
    by (auto simp add: D_Seq D_Renaming T_Renaming)
       (metis map_EvExt_tick map_append)
next
  fix s
  assume \<open>s \<in> \<D> ?rhs\<close>
  then consider \<open>s \<in> \<D> (Renaming P f)\<close>
    | \<open>\<exists>s1 s2. s = s1 @ s2 \<and> s1 @ [tick] \<in> \<T> (Renaming P f) \<and> s2 \<in> \<D> (Renaming Q f)\<close>
    using D_Seq by blast
  thus \<open>s \<in> \<D> ?lhs\<close>
  proof cases
    show \<open>s \<in> \<D> (Renaming P f) \<Longrightarrow> s \<in> \<D> ?lhs\<close>
      by (auto simp add: D_Renaming D_Seq)
  next
    assume \<open>\<exists>s1 s2. s = s1 @ s2 \<and> s1 @ [tick] \<in> \<T> (Renaming P f) \<and> s2 \<in> \<D> (Renaming Q f)\<close>
    then obtain s1 s2
      where * : \<open>s = s1 @ s2\<close> \<open>s1 @ [tick] \<in> \<T> (Renaming P f)\<close> \<open>s2 \<in> \<D> (Renaming Q f)\<close> by blast
    then obtain t1 t2 u1 u2
      where ** :  \<open>t1 \<in> \<T> P \<and> s1 @ [tick] = map (EvExt f) t1 \<or>
                  tickFree t1 \<and> front_tickFree t2 \<and> 
                  s1 @ [tick] = map (EvExt f) t1 @ t2 \<and> t1 \<in> \<D> P\<close>
                 \<open>tickFree u1\<close> \<open>front_tickFree u2\<close> \<open>s2 = map (EvExt f) u1 @ u2\<close> \<open>u1 \<in> \<D> Q\<close>
      by (simp add: T_Renaming D_Renaming) blast
    have *** : \<open>tickFree (butlast t1)\<close>
      using "**"(1) front_tickFree_butlast is_processT2_TR tickFree_butlast by blast
    from "**"(1) show \<open>s \<in> \<D> ?lhs\<close>
      apply (rule disjE; simp add: D_Renaming D_Seq)
       apply (rule_tac x = \<open>butlast t1 @ u1\<close> in exI, simp add: "***" "**"(2))
       apply (rule_tac x = \<open>u2\<close> in exI, simp add: "**"(3), intro conjI,
          metis "*"(1) "**"(4) butlast_snoc map_butlast)
       apply (rule disjI2, rule_tac x = \<open>butlast t1\<close> in exI, rule_tac x = u1 in exI)
       apply (simp add: "**"(5), metis "***" EvExt_tF snoc_eq_iff_butlast tickFree_butlast)

      apply (rule_tac x = \<open>if t2 = [] then butlast t1 else t1\<close> in exI, intro conjI)
      using "***" 
       apply presburger
      apply (rule_tac x = \<open>butlast t2 @ s2\<close> in exI, intro conjI)
        apply (meson D_imp_front_tickFree \<open>s2 \<in> \<D> (Renaming Q f)\<close>
          front_tickFree_append front_tickFree_butlast)
       apply ((cases t1 rule: rev_cases; simp add: "*"(1) snoc_eq_iff_butlast),
          metis butlast.simps(2) butlast_append list.discI tick_eq_EvExt)
      by (metis EvExt_tF non_tickFree_tick tickFree_Nil tickFree_append)
  qed
next
  fix s X
  assume same_div: \<open>\<D> ?lhs = \<D> ?rhs\<close>
  assume \<open>(s, X) \<in> \<F> ?lhs\<close>
  then consider \<open>\<exists>s1. (s1, EvExt f -` X) \<in> \<F> (P \<^bold>; Q) \<and> s = map (EvExt f) s1\<close> | \<open>s \<in> \<D> ?lhs\<close>
    by (simp add: F_Renaming D_Renaming) blast
  thus \<open>(s, X) \<in> \<F> ?rhs\<close>
  proof cases
    assume \<open>\<exists>s1. (s1, EvExt f -` X) \<in> \<F> (P \<^bold>; Q) \<and> s = map (EvExt f) s1\<close>
    then obtain s1 where * : \<open>(s1, EvExt f -` X) \<in> \<F> (P \<^bold>; Q)\<close> \<open>s = map (EvExt f) s1\<close> by blast
    from this(1)[simplified F_Seq, simplified]
    show \<open>(s, X) \<in> \<F> ?rhs\<close>
      apply (elim disjE; simp add: F_Seq)
        apply (rule disjI1, simp add: F_Renaming, 
          metis (no_types, lifting) "*"(2) Diff_insert_absorb 
          EvExt_tF anteced_EvExt_diff_tick insertI1
          insert_Diff insert_absorb tick_elem_anteced1)
       apply (rule disjI2, rule disjI1, simp add: F_Renaming T_Renaming,
          metis (no_types, lifting) "*"(2) map_EvExt_tick map_append)
      apply (rule disjI2, rule disjI2, simp add: D_Renaming)
      apply (rule_tac x = \<open>if tickFree s1 then s1 else butlast s1\<close> in exI)
      by (auto simp add: "*"(2),
          metis NF_ND append_butlast_last_id front_tickFree_implies_tickFree
          is_processT2 tickFree_Nil,
          metis EvExt_tF front_tickFree_single map_butlast
          nonTickFree_n_frontTickFree process_charn snoc_eq_iff_butlast)
  next
    from NF_ND same_div show \<open>s \<in> \<D> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> by blast
  qed
next
  fix s X
  assume same_div: \<open>\<D> ?lhs = \<D> ?rhs\<close>
  assume \<open>(s, X) \<in> \<F> ?rhs\<close>
  then consider \<open>(s, insert tick X) \<in> \<F> (Renaming P f) \<and> tickFree s\<close>
    | \<open>\<exists>s1 s2. s = s1 @ s2 \<and> s1 @ [tick] \<in> \<T> (Renaming P f) \<and> (s2, X) \<in> \<F> (Renaming Q f)\<close>
    | \<open>s \<in> \<D> ?rhs\<close>
    by (simp add: F_Seq D_Seq) blast
  thus \<open>(s, X) \<in> \<F> ?lhs\<close>
  proof cases
    show \<open>(s, insert tick X) \<in> \<F> (Renaming P f) \<and> tickFree s \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
      by (auto simp add: F_Renaming F_Seq D_Seq)
         (metis (no_types, lifting) Diff_insert_absorb EvExt_tF anteced_EvExt_diff_tick
                                    insertCI insert_Diff insert_absorb tick_elem_anteced1)
  next
    assume \<open>\<exists>s1 s2. s = s1 @ s2 \<and> s1 @ [tick] \<in> \<T> (Renaming P f) \<and> (s2, X) \<in> \<F> (Renaming Q f)\<close>
    then obtain s1 s2 where * : \<open>s = s1 @ s2\<close> \<open>s1 @ [tick] \<in> \<T> (Renaming P f)\<close>
                                \<open>(s2, X) \<in> \<F> (Renaming Q f)\<close> by blast
    from "*"(2, 3) obtain t1 u1 where ** : 
      \<open>t1 \<in> \<T> P \<and> s1 @ [tick] = map (EvExt f) t1 \<or> 
       tickFree t1 \<and> (\<exists>t2. front_tickFree t2 \<and> s1 @ [tick] = map (EvExt f) t1 @ t2 \<and> t1 \<in> \<D> P)\<close>
      \<open>(u1, EvExt f -` X) \<in> \<F> Q \<and> s2 = map (EvExt f) u1 \<or>
       tickFree u1 \<and> (\<exists>u2. front_tickFree u2 \<and> s2 = map (EvExt f) u1 @ u2 \<and> u1 \<in> \<D> Q)\<close>
      by (simp add: F_Renaming T_Renaming) blast
    show \<open>(s, X) \<in> \<F> ?lhs\<close>
      using "**"(1) 
      apply (elim disjE conjE exE; simp add: "*"(1) F_Renaming D_Seq)
      using "**"(2) 
       apply (elim disjE conjE exE)
        apply (rule disjI1, simp add: F_Seq,
          metis (no_types, lifting) "*"(1) append_eq_map_conv map_EvExt_tick)
       apply (rule disjI2, simp add: D_Seq)
       apply (rule_tac x = \<open>butlast t1 @ u1\<close> in exI, intro conjI)
      using front_tickFree_butlast is_processT2_TR tickFree_append 
        apply blast
       apply (rule_tac x = u2 in exI, intro conjI, blast,
          metis append.assoc butlast_snoc map_append map_butlast,
          metis EvExt_tF T_nonTickFree_imp_decomp snoc_eq_iff_butlast tickFree_butlast)
      apply (rule disjI2)
      apply (rule_tac x = \<open>if t2 \<noteq> [] then t1 else tl t1\<close> in exI, intro conjI)
       apply (metis (mono_tags, opaque_lifting) tickFree_tl tl_Nil)
      apply (rule_tac x = \<open>(butlast t2) @ s2\<close> in exI, intro conjI)
        apply (meson "*"(3) front_tickFree_append front_tickFree_butlast process_charn)
       apply (simp, metis EvExt_tF butlast_append butlast_snoc non_tickFree_tick tickFree_append)
      by (metis EvExt_tF non_tickFree_tick self_append_conv tickFree_append)
  next
    from NF_ND same_div show \<open>s \<in> \<D> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> by blast
  qed
qed






lemma mono_Renaming_D: \<open>P \<sqsubseteq>\<^sub>D Q \<Longrightarrow> Renaming P f \<sqsubseteq>\<^sub>D Renaming Q f\<close>
  unfolding divergence_refine_def D_Renaming by blast


lemma mono_Renaming_FD: \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> Renaming P f \<sqsubseteq>\<^sub>F\<^sub>D Renaming Q f\<close>
  unfolding failure_divergence_refine_def le_ref_def
  apply (simp add: mono_Renaming_D[unfolded divergence_refine_def])
  unfolding F_Renaming D_Renaming by blast


lemma mono_Renaming_DT: \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> Renaming P f \<sqsubseteq>\<^sub>D\<^sub>T Renaming Q f\<close>
  unfolding trace_divergence_refine_def 
  apply (simp add: mono_Renaming_D)
  unfolding trace_refine_def divergence_refine_def T_Renaming by blast






section\<open>Assertions\<close>

abbreviation deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P :: "'a process \<Rightarrow> bool"
  where   "deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P \<equiv> deadlock_free_v2"


lemma deadlock_free_implies_lifelock_free: \<open>deadlock_free P \<Longrightarrow> lifelock_free P\<close>
  unfolding deadlock_free_def lifelock_free_def
  using CHAOS_DF_refine_FD trans_FD by blast

lemmas deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def = deadlock_free_v2_def
   and deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_is_right = deadlock_free_v2_is_right
   and deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_implies_div_free = deadlock_free_v2_implies_div_free
   and deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_FD = deadlock_free_v2_FD
   and deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_is_right_wrt_events = deadlock_free_v2_is_right_wrt_events
   and deadlock_free_is_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P = deadlock_free_is_deadlock_free_v2
   and deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_SKIP = deadlock_free_v2_SKIP
   and non_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_STOP = non_deadlock_free_v2_STOP


section \<open>Non-terminating Runs\<close>

definition non_terminating  :: "'a process \<Rightarrow> bool"
  where   "non_terminating P \<equiv> RUN UNIV \<sqsubseteq>\<^sub>T P"

corollary non_terminating_refine_DF: "non_terminating P = DF UNIV \<sqsubseteq>\<^sub>T P"
  and non_terminating_refine_CHAOS: "non_terminating P = CHAOS UNIV \<sqsubseteq>\<^sub>T P"
  by (simp_all add: DF_all_tickfree_traces1 RUN_all_tickfree_traces1 CHAOS_all_tickfree_traces1 
                    non_terminating_def trace_refine_def)

lemma non_terminating_is_right: "non_terminating P \<longleftrightarrow> (\<forall>s \<in> \<T> P. tickFree s)"
  apply (rule iffI)
  by (auto simp add:non_terminating_def trace_refine_def tickFree_def RUN_all_tickfree_traces1)[1]
     (auto simp add:non_terminating_def trace_refine_def RUN_all_tickfree_traces2)

lemma nonterminating_implies_div_free: "non_terminating P \<Longrightarrow> \<D> P = {}"
  unfolding non_terminating_is_right
  by (metis NT_ND equals0I front_tickFree_charn process_charn tickFree_Cons tickFree_append) 

lemma non_terminating_implies_F: "non_terminating P \<Longrightarrow> CHAOS UNIV \<sqsubseteq>\<^sub>F P"
  using CHAOS_has_all_tickFree_failures F_T 
  by (auto simp add: non_terminating_is_right failure_refine_def) blast


corollary non_terminating_F: "non_terminating P = CHAOS UNIV \<sqsubseteq>\<^sub>F P"
  by (auto simp add:non_terminating_implies_F non_terminating_refine_CHAOS leF_imp_leT)

corollary non_terminating_FD: "non_terminating P = CHAOS UNIV \<sqsubseteq>\<^sub>F\<^sub>D P"
  unfolding non_terminating_F
  using div_free_CHAOS nonterminating_implies_div_free leFD_imp_leF
        leF_leD_imp_leFD divergence_refine_def non_terminating_F 
  by fastforce 


section \<open>Lifelock Freeness\<close>

corollary lifelock_free_is_non_terminating: "lifelock_free P = non_terminating P"
  unfolding lifelock_free_def non_terminating_FD by simp

lemma div_free_divergence_refine:
  "\<D> P = {} \<longleftrightarrow> CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV \<sqsubseteq>\<^sub>D P" 
  "\<D> P = {} \<longleftrightarrow> CHAOS UNIV    \<sqsubseteq>\<^sub>D P" 
  "\<D> P = {} \<longleftrightarrow> RUN UNIV      \<sqsubseteq>\<^sub>D P" 
  "\<D> P = {} \<longleftrightarrow> DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV    \<sqsubseteq>\<^sub>D P" 
  "\<D> P = {} \<longleftrightarrow> DF UNIV       \<sqsubseteq>\<^sub>D P" 
  by (simp_all add: div_free_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P div_free_CHAOS div_free_RUN div_free_DF 
                    div_free_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P divergence_refine_def)

definition lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P :: "'a process \<Rightarrow> bool"
  where   "lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P P \<equiv> CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P UNIV \<sqsubseteq>\<^sub>F\<^sub>D P"

lemma div_free_is_lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P: "lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P P \<longleftrightarrow> \<D> P = {}"
  using CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_has_all_failures_Un leFD_imp_leD leF_leD_imp_leFD
        div_free_divergence_refine(1) lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_def 
  by blast
  
lemma lifelock_free_is_lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P: "lifelock_free P \<Longrightarrow> lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P P"
  by (simp add: leFD_imp_leD div_free_divergence_refine(2) div_free_is_lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P lifelock_free_def)

corollary deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_is_lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P: "deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P P \<Longrightarrow> lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P P"
  by (simp add: deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_implies_div_free div_free_is_lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P)


section \<open>New Laws\<close>

lemma non_terminating_Seq: 
  \<open>non_terminating P \<Longrightarrow> (P \<^bold>; Q) = P\<close>
  unfolding non_terminating_is_right apply (subst Process_eq_spec, intro conjI)
  apply (auto simp add: F_Seq is_processT7 F_T)[1]
  using is_processT4 apply blast
  using process_charn apply blast
   apply (metis F_T Un_commute insert_is_Un is_processT5_S2 non_tickFree_tick tickFree_append)
  by (auto simp add: D_Seq)
 

lemma non_terminating_Sync: 
  \<open>non_terminating P \<Longrightarrow> lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P Q \<Longrightarrow> non_terminating (P \<lbrakk>A\<rbrakk> Q)\<close>
  apply (simp add: non_terminating_is_right div_free_is_lifelock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P T_Sync)
  apply (intro ballI, simp add: non_terminating_is_right nonterminating_implies_div_free)
  by (metis empty_iff ftf_Sync1 ftf_Sync21 insertI1 tickFree_def)


lemmas non_terminating_Par = non_terminating_Sync[where A = \<open>UNIV\<close>]
   and non_terminating_Inter = non_terminating_Sync[where A = \<open>{}\<close>]





syntax
  "_writeS"  :: "['b \<Rightarrow> 'a, pttrn, 'b set, 'a process] => 'a process"  ("(4(_\<^bold>!_\<^bold>|_) /\<rightarrow> _)" [0,0,50,78] 50)
translations
  "_writeS c p b P"  => "CONST Mndetprefix (c ` {p. b}) (\<lambda>_. P)"





end
