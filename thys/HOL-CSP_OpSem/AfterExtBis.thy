(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : HOL-CSP_OpSem - Operational semantics for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Burkhart Wolff
 *
 * This file       : Extension of the After operator bis
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

chapter \<open> Extension of the After Operator, bis\<close>

theory  AfterExtBis
  imports After
begin

section \<open>The AfterExt Operator, bis\<close>


subsection \<open>Definition\<close>

text \<open>The refinements \<^term>\<open>(\<sqsubseteq>\<^sub>F)\<close> and \<^term>\<open>(\<sqsubseteq>\<^sub>T)\<close> are not verifying the locale axioms.
      In order to make the constructions available for these refinements, we
      will slightly modify the definition of AfterExt.\<close>

text \<open>If the event is \<^term>\<open>\<checkmark>\<close> we obtain \<^const>\<open>STOP\<close>
      anyway, even if the process was \<^term>\<open>\<bottom>\<close>. 

      At first this appears a little weird, but can be interpreted as the fact
      that even if a process if diverging, after accepting \<^term>\<open>\<checkmark>\<close> it has to stop.\<close>

definition AfterExt :: \<open>['\<alpha> process, '\<alpha> event] \<Rightarrow> '\<alpha> process\<close> (infixl \<open>afterExt\<close> 77)
  where \<open>P afterExt e \<equiv> case e of ev x \<Rightarrow> P after x | \<checkmark> \<Rightarrow> STOP\<close>


lemma not_ready_AfterExt: \<open>e \<notin> ready_set P \<Longrightarrow> P afterExt e = STOP\<close>
  by (auto simp add: AfterExt_def intro: not_ready_After split: event.split)

lemma ready_set_AfterExt: 
  \<open>ready_set (P afterExt e) = (if e = \<checkmark> then {} else {a. e # [a] \<in> \<T> P})\<close>
  by (simp add: AfterExt_def ready_set_After ready_set_STOP
         split: event.split) 


subsection \<open>Projections\<close>

lemma F_AfterExt: 
  \<open>\<F> (P afterExt e) = 
   (   if e \<in> ready_set P then {(tl s, X)| s X. (s, X) \<in> \<F> P \<and> s \<noteq> [] \<and> hd s = e}
     else {(s, X). s = []})\<close>
  (is \<open>_ = ?rhs\<close>)
proof (unfold AfterExt_def, split event.split, intro conjI allI impI)
  show \<open>e = ev x \<Longrightarrow> \<F> (P after x) = ?rhs\<close> for x
    by (simp add: F_After)
next
  show \<open>e = \<checkmark> \<Longrightarrow> \<F> STOP = ?rhs\<close>
    by (simp add: F_UU F_STOP BOT_iff_D ready_set_def set_eq_iff)
       (metis F_T T_nonTickFree_imp_decomp append_single_T_imp_tickFree hd_append2
              hd_in_set list.discI list.sel(1) list.sel(3) tickFree_def tick_T_F)
qed


lemma D_AfterExt: \<open>\<D> (P afterExt e) = (  if e = \<checkmark> \<and> P = \<bottom> then {} 
                                        else {tl s| s . s \<in> \<D> P \<and> s \<noteq> [] \<and> hd s = e})\<close>
  (is \<open>_ = ?rhs\<close>)
proof (unfold AfterExt_def, split event.split, intro conjI allI impI)
  show \<open>e = ev x \<Longrightarrow> \<D> (P after x) = ?rhs\<close> for x
    by (simp add: D_After)
       (metis Cons_in_T_imp_elem_ready_set D_T list.exhaust_sel)
next
  show \<open>e = \<checkmark> \<Longrightarrow> \<D> STOP = ?rhs\<close>
    by (simp add: D_UU D_STOP BOT_iff_D)
       (metis D_imp_front_tickFree front_tickFree_implies_tickFree hd_append2
              hd_in_set is_processT9 nonTickFree_n_frontTickFree tickFree_def)
qed


lemma T_AfterExt: \<open>\<T> (P afterExt e) = (  if e = \<checkmark> \<and> P = \<bottom> then {[]} 
                                       else insert [] {tl s| s . s \<in> \<T> P \<and> s \<noteq> [] \<and> hd s = e})\<close>
  (is \<open>_ = ?rhs\<close>)
proof (unfold AfterExt_def, split event.split, intro conjI allI impI)
  show \<open>e = ev x \<Longrightarrow> \<T> (P after x) = ?rhs\<close> for x
    by (simp add: T_After set_eq_iff subset_iff)
       (metis Cons_in_T_imp_elem_ready_set list.collapse
              list.distinct(1) list.sel(1, 3) mem_Collect_eq ready_set_def)
next
  show \<open>e = \<checkmark> \<Longrightarrow> \<T> STOP = ?rhs\<close>
  by (simp add: T_After T_UU T_STOP subset_iff)
     (metis front_tickFree_charn hd_append2 hd_in_set
            is_processT2_TR list.sel(3) tickFree_def tl_append_if)
qed



subsection \<open>Monotony\<close>

lemma mono_AfterExt : \<open>P \<sqsubseteq> Q \<Longrightarrow> P afterExt e \<sqsubseteq> Q afterExt e\<close>
  by (auto simp add: AfterExt_def mono_After split: event.split)

lemma mono_AfterExt_T : \<open>P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> P afterExt e \<sqsubseteq>\<^sub>T Q afterExt e\<close>
  by (auto simp add: AfterExt_def mono_After_T split: event.split)

lemma mono_AfterExt_F :
  \<open>P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> ev e \<notin> ready_set P \<or> ev e \<in> ready_set Q \<Longrightarrow>
   P afterExt ev e \<sqsubseteq>\<^sub>F Q afterExt ev e\<close>
  by (simp add: AfterExt_def mono_After_F) 

lemma mono_AfterExt_D : \<open>P \<sqsubseteq>\<^sub>D Q \<Longrightarrow> P afterExt e \<sqsubseteq>\<^sub>D Q afterExt e\<close>
  by (simp add: AfterExt_def mono_After_D split: event.split)

lemma mono_AfterExt_FD :
  \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> e \<notin> ready_set P \<or> e \<in> ready_set Q \<Longrightarrow> 
   P afterExt e \<sqsubseteq>\<^sub>F\<^sub>D Q afterExt e\<close>
  by (auto simp add: AfterExt_def mono_After_FD split: event.split)

lemma mono_AfterExt_DT : \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> P afterExt e \<sqsubseteq>\<^sub>D\<^sub>T Q afterExt e\<close>
  by (simp add: AfterExt_def mono_After_DT split: event.split)
 


subsection \<open>Behaviour of @{const [source] \<open>AfterExt\<close>} with \<^const>\<open>STOP\<close>, \<^const>\<open>SKIP\<close> and \<^term>\<open>\<bottom>\<close>\<close>

lemma AfterExt_STOP: \<open>STOP afterExt e = STOP\<close>
  by (simp add: STOP_neq_BOT STOP_iff_T T_AfterExt ready_set_STOP T_STOP)

lemma AfterExt_is_STOP_iff:
  \<open>P afterExt e = STOP \<longleftrightarrow> P = \<bottom> \<and> e = \<checkmark> \<or> (\<forall>s. e # s \<in> \<T> P \<longrightarrow> s = [])\<close>
  by (simp add: AfterExt_def After_is_STOP_iff split: event.split)
     (metis T_nonTickFree_imp_decomp append_single_T_imp_tickFree 
            butlast.simps(2) butlast_snoc tickFree_Cons)



lemma AfterExt_SKIP: \<open>SKIP afterExt e = STOP\<close>
  by (auto simp add: SKIP_neq_BOT STOP_iff_T T_AfterExt ready_set_SKIP T_SKIP)
 
lemma AfterExt_BOT : \<open>\<bottom> afterExt e = (if e = \<checkmark> then STOP else \<bottom>)\<close>
  by (metis AfterExt_def After_BOT event.case event.exhaust)

lemma AfterExt_is_BOT_iff: \<open>P afterExt e = \<bottom> \<longleftrightarrow> e \<noteq> \<checkmark> \<and> [e] \<in> \<D> P\<close>
  by (simp add: AfterExt_def After_is_BOT_iff STOP_neq_BOT split: event.split)
 
 

subsection \<open>Behaviour of @{const [source] \<open>AfterExt\<close>} with Operators of \<^session>\<open>HOL-CSP\<close>\<close>

text \<open>Here again, we lose determinism.\<close>

lemma AfterExt_Mprefix_is_AfterExt_Mndetprefix: 
  \<open>(\<box>a \<in> A \<rightarrow> P a) afterExt e = (\<sqinter>a \<in> A \<rightarrow> P a) afterExt e\<close>
  by (simp add: AfterExt_def After_Mprefix_is_After_Mndetprefix 
                Mprefix_neq_BOT Mndetprefix_neq_BOT split: event.split)
  
lemma AfterExt_Det_is_AfterExt_Ndet: \<open>P \<box> Q afterExt e = P \<sqinter> Q afterExt e\<close>
  by (simp add: AfterExt_def After_Det_is_After_Ndet Det_is_BOT_iff Ndet_is_BOT_iff
         split: event.split)


lemma AfterExt_Ndet: 
  \<open>P \<sqinter> Q afterExt e = ( case e of ev x \<Rightarrow>   if ev x \<in> ready_set P \<inter> ready_set Q
                                          then (P afterExt ev x) \<sqinter> (Q afterExt ev x)
                                          else   if ev x \<in> ready_set P
                                               then P afterExt ev x
                                               else Q afterExt ev x
                                | \<checkmark> \<Rightarrow> STOP)\<close>
  by (auto simp add: AfterExt_def After_Ndet not_ready_After split: event.split)
  
 
lemma AfterExt_Mprefix: 
  \<open>(\<box> a \<in> A \<rightarrow> P a) afterExt e =
   (case e of ev x \<Rightarrow> if x \<in> A then P x else STOP | \<checkmark> \<Rightarrow> STOP)\<close>
  by (simp add: AfterExt_def Mprefix_neq_BOT After_Mprefix split: event.split)

corollary AfterExt_prefix:
  \<open>(a \<rightarrow> P) afterExt e =
   (case e of ev x \<Rightarrow> if x = a then P else STOP | \<checkmark> \<Rightarrow> STOP)\<close>
  unfolding write0_def by (simp add: AfterExt_Mprefix split: event.split)


lemmas AfterExt_Det = AfterExt_Ndet[folded AfterExt_Det_is_AfterExt_Ndet]
   and AfterExt_Mndetprefix = AfterExt_Mprefix[unfolded AfterExt_Mprefix_is_AfterExt_Mndetprefix]


(* TODO : move this *)
lemma Renaming_is_BOT_iff: \<open>Renaming P f = \<bottom> \<longleftrightarrow> P = \<bottom>\<close>
  apply (intro iffI)
   apply (simp add: BOT_iff_D D_Renaming)
  by (simp add: Renaming_BOT)

lemma Renaming_is_STOP_iff: \<open>Renaming P f = STOP \<longleftrightarrow> P = STOP\<close>
  apply (intro iffI, simp_all add: Renaming_STOP)
  by (auto simp add: STOP_iff_T T_Renaming intro: Nil_elem_T)



lemma AfterExt_Renaming:
  \<open>Renaming P f afterExt e =
   (case e of \<checkmark> \<Rightarrow> STOP 
            | ev a \<Rightarrow> if P = \<bottom> then \<bottom> else
    \<sqinter>a \<in> {a. ev a \<in> ready_set P \<and> ev (f a) = e}. Renaming (P afterExt ev a) f)\<close>
  by (simp add: AfterExt_def After_Renaming Renaming_is_BOT_iff split: event.split)
   

\<comment>\<open>Move this result in \<^session>\<open>HOL-CSP\<close>\<close>
lemma Seq_is_BOT_iff: \<open>P \<^bold>; Q = \<bottom> \<longleftrightarrow> P = \<bottom> \<or> ([\<checkmark>] \<in> \<T> P \<and> Q = \<bottom>)\<close>
  by (auto simp add: BOT_iff_D D_Seq D_UU)


lemma AfterExt_Seq:
  \<open>(P \<^bold>; Q) afterExt e = 
   (     if e \<notin> ready_set P \<and> e \<notin> ready_set Q then STOP
    else if e \<notin> ready_set Q then P afterExt e \<^bold>; Q
    else if e \<notin> ready_set P then if \<checkmark> \<in> ready_set P then Q afterExt e else STOP 
    else if \<checkmark> \<in> ready_set P then (P afterExt e \<^bold>; Q) \<sqinter> (Q afterExt e)
    else P afterExt e \<^bold>; Q)\<close>
  by (simp add: AfterExt_def After_Seq Ndet_id Ndet_is_BOT_iff 
                Seq_is_BOT_iff ready_set_def T_UU STOP_Seq split: event.split)


theorem AfterExt_Sync: 
  \<open>(P \<lbrakk>S\<rbrakk> Q) afterExt e = 
   (  case e of \<checkmark> \<Rightarrow> STOP
                 | ev x \<Rightarrow>   if P = \<bottom> \<or> Q = \<bottom> then \<bottom>  
                           else if e \<in> ready_set P \<and> e \<in> ready_set Q
                           then   if x \<in> S 
                                then P afterExt e \<lbrakk>S\<rbrakk> Q afterExt e
                                else (P afterExt e \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q afterExt e)
                           else   if e \<in> ready_set P
                                then   if x \<in> S then STOP else P afterExt e \<lbrakk>S\<rbrakk> Q
                                else   if e \<in> ready_set Q
                                     then   if x \<in> S then STOP else P \<lbrakk>S\<rbrakk> Q afterExt e
                                     else STOP)\<close>
  by (simp add: AfterExt_def After_Sync split: event.split)
  



lemma Hiding_FD_Hiding_AfterExt_if_ready_inside:
  \<open>e \<in> B \<Longrightarrow> (P \ B) \<sqsubseteq>\<^sub>F\<^sub>D (P afterExt ev e \ B)\<close>
  and AfterExt_Hiding_FD_Hiding_AfterExt_if_ready_notin:
  \<open>e \<notin> B \<Longrightarrow> (P \ B) afterExt ev e \<sqsubseteq>\<^sub>F\<^sub>D (P afterExt ev e \ B)\<close>
  if ready: \<open>ev e \<in> ready_set P\<close>
  by (simp add: AfterExt_def Hiding_FD_Hiding_After_if_ready_inside that)
     (simp add: AfterExt_def After_Hiding_FD_Hiding_After_if_ready_notin that)
 


lemmas Hiding_F_Hiding_AfterExt_if_ready_inside = 
       Hiding_FD_Hiding_AfterExt_if_ready_inside[THEN leFD_imp_leF]
   and AfterExt_Hiding_F_Hiding_AfterExt_if_ready_notin = 
       AfterExt_Hiding_FD_Hiding_AfterExt_if_ready_notin[THEN leFD_imp_leF]
   and Hiding_D_Hiding_AfterExt_if_ready_inside = 
       Hiding_FD_Hiding_AfterExt_if_ready_inside[THEN leFD_imp_leD]
   and AfterExt_Hiding_D_Hiding_AfterExt_if_ready_notin = 
       AfterExt_Hiding_FD_Hiding_AfterExt_if_ready_notin[THEN leFD_imp_leD]
   and Hiding_T_Hiding_AfterExt_if_ready_inside = 
       Hiding_FD_Hiding_AfterExt_if_ready_inside[THEN leFD_imp_leF, THEN leF_imp_leT]   
   and AfterExt_Hiding_T_Hiding_AfterExt_if_ready_notin = 
       AfterExt_Hiding_FD_Hiding_AfterExt_if_ready_notin[THEN leFD_imp_leF, THEN leF_imp_leT]

corollary Hiding_DT_Hiding_AfterExt_if_ready_inside:
  \<open>\<lbrakk>ev e \<in> ready_set P; e \<in> B\<rbrakk> \<Longrightarrow> (P \ B) \<sqsubseteq>\<^sub>D\<^sub>T (P afterExt ev e \ B)\<close>
  and AfterExt_Hiding_DT_Hiding_AfterExt_if_ready_notin: 
  \<open>\<lbrakk>ev e \<in> ready_set P; e \<notin> B\<rbrakk> \<Longrightarrow> (P \ B) afterExt ev e \<sqsubseteq>\<^sub>D\<^sub>T (P afterExt ev e \ B)\<close>
  by (simp add: Hiding_D_Hiding_AfterExt_if_ready_inside 
                Hiding_T_Hiding_AfterExt_if_ready_inside leD_leT_imp_leDT)
     (simp add: AfterExt_Hiding_D_Hiding_AfterExt_if_ready_notin 
                AfterExt_Hiding_T_Hiding_AfterExt_if_ready_notin leD_leT_imp_leDT)




subsection \<open>Behaviour of @{const [source] \<open>AfterExt\<close>} with Operators of \<^session>\<open>HOL-CSPM\<close>\<close>

lemma AfterExt_MultiDet_is_AfterExt_MultiNdet:
  \<open>finite A \<Longrightarrow> (\<^bold>\<box> a \<in> A. P a) afterExt e = (\<Sqinter> a \<in> A. P a) afterExt e\<close>
  by (auto simp add: AfterExt_def After_MultiDet_is_After_MultiNdet
                     MultiDet_is_BOT_iff MultiNdet_is_BOT_iff split: event.split)
 

lemma AfterExt_GlobalNdet: 
  \<open>(\<sqinter> a \<in> A. P a) afterExt e =
   (  if e = \<checkmark> \<or> e \<notin> (\<Union>a \<in> A. ready_set (P a)) then STOP
    else (\<sqinter> a \<in> {a \<in> A. e \<in> ready_set (P a)}. P a) afterExt e)\<close>
  and AfterExt_MultiNdet: 
  \<open>finite A \<Longrightarrow> (\<Sqinter> a \<in> A. P a) afterExt e = 
   (  if e = \<checkmark> \<or> e \<notin> (\<Union>a \<in> A. ready_set (P a)) then STOP
    else (\<Sqinter> a \<in> {a \<in> A. e \<in> ready_set (P a)}. P a) afterExt e)\<close>
  and AfterExt_MultiDet: 
  \<open>finite A \<Longrightarrow> (\<^bold>\<box> a \<in> A. P a) afterExt e = 
   (  if e = \<checkmark> \<or> e \<notin> (\<Union>a \<in> A. ready_set (P a)) then STOP
    else (\<Sqinter> a \<in> {a \<in> A. e \<in> ready_set (P a)}. P a) afterExt e)\<close>
  by (simp_all add: AfterExt_def split: event.split)
     (simp add: After_GlobalNdet, simp add: After_MultiNdet, simp add: After_MultiDet)


(* TODO: formulate and prove for MultiSync and MultiSeq *)



subsection \<open>Behaviour of @{const [source] \<open>AfterExt\<close>} with Operators of \<^session>\<open>HOL-CSP_OpSem\<close>\<close>

lemma AfterExt_Sliding_is_AfterExt_Ndet:
  \<open>P \<rhd> Q afterExt e = P \<sqinter> Q afterExt e\<close>
  by (simp add: AfterExt_def After_Sliding_is_After_Ndet Sliding_is_BOT_iff Ndet_is_BOT_iff
         split: event.split)

lemmas AfterExt_Sliding = AfterExt_Ndet[folded AfterExt_Sliding_is_AfterExt_Ndet]


lemma AfterExt_Throw:
  \<open>(P \<Theta> a \<in> A. Q a) afterExt e = 
   (case e of \<checkmark> \<Rightarrow> STOP
            | ev x \<Rightarrow>   if P = \<bottom> then \<bottom> 
                      else    if ev x \<in> ready_set P then if x \<in> A then Q x
                           else (P after x) \<Theta> a \<in> A. Q a else STOP)\<close>
  by (simp add: AfterExt_def After_Throw Throw_is_BOT_iff split: event.split)


lemma AfterExt_Interrupt:
  \<open>(P \<triangle> Q) afterExt e = 
   (case e of \<checkmark> \<Rightarrow> STOP
            | ev x \<Rightarrow>   if P = \<bottom> \<or> Q = \<bottom> then \<bottom>
                      else   if ev x \<in> ready_set P \<and> ev x \<in> ready_set Q
                           then (Q after x) \<sqinter> (P after x \<triangle> Q)
                           else   if ev x \<in> ready_set P \<and> ev x \<notin> ready_set Q
                                then P after x \<triangle> Q
                                else   if ev x \<notin> ready_set P \<and> ev x \<in> ready_set Q
                                     then Q after x 
                                     else STOP)\<close>
  by (simp add: AfterExt_def After_Interrupt Interrupt_is_BOT_iff 
                Ndet_is_BOT_iff ready_set_BOT After_is_BOT_iff D_UU split: event.split)



subsection \<open>Behaviour of @{const [source] \<open>AfterExt\<close>} with Reference Processes\<close>
 
lemma AfterExt_DF: 
  \<open>DF A afterExt e =
   (case e of ev x \<Rightarrow> if x \<in> A then DF A else STOP | \<checkmark> \<Rightarrow> STOP)\<close>
  by (cases e) (simp_all add: AfterExt_def After_DF BOT_iff_D div_free_DF)

lemma AfterExt_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P:
  \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A afterExt e =
   (case e of ev x \<Rightarrow> if x \<in> A then DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A else STOP | \<checkmark> \<Rightarrow> STOP)\<close>
  by (cases e) (simp_all add: AfterExt_def After_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P BOT_iff_D div_free_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P)

lemma AfterExt_RUN:
  \<open>RUN A afterExt e =
   (case e of ev x \<Rightarrow> if x \<in> A then RUN A else STOP | \<checkmark> \<Rightarrow> STOP)\<close>
  by (cases e) (simp_all add: AfterExt_def After_RUN BOT_iff_D div_free_RUN)

lemma AfterExt_CHAOS:
  \<open>CHAOS A afterExt e =
   (case e of ev x \<Rightarrow> if x \<in> A then CHAOS A else STOP | \<checkmark> \<Rightarrow> STOP)\<close>
  by (cases e) (simp_all add: AfterExt_def After_CHAOS BOT_iff_D div_free_CHAOS)

lemma AfterExt_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P:
  \<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A afterExt e =
   (case e of ev x \<Rightarrow> if x \<in> A then CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A else STOP | \<checkmark> \<Rightarrow> STOP)\<close>
  by (cases e) (simp_all add: AfterExt_def After_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P BOT_iff_D div_free_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P)



lemma DF_FD_AfterExt:
  \<open>DF A \<sqsubseteq>\<^sub>F\<^sub>D P \<Longrightarrow> e \<in> ready_set P \<Longrightarrow> DF A \<sqsubseteq>\<^sub>F\<^sub>D P afterExt e\<close>
  apply (cases e, simp add: AfterExt_def DF_FD_After)
  by (metis anti_mono_ready_set_FD event.distinct(1) image_iff ready_set_DF subsetD)

lemma DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_FD_AfterExt:
  \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A \<sqsubseteq>\<^sub>F\<^sub>D P \<Longrightarrow> ev e \<in> ready_set P \<Longrightarrow> DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A \<sqsubseteq>\<^sub>F\<^sub>D P afterExt ev e\<close>
  by (simp add: AfterExt_def DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_FD_After)



lemma deadlock_free_AfterExt:
  \<open>deadlock_free P \<Longrightarrow> deadlock_free (P afterExt e) \<longleftrightarrow> 
                       (if e \<in> ready_set P \<and> e \<noteq> \<checkmark> then True else False)\<close>
  by (cases e)
     (simp add: AfterExt_def deadlock_free_After, 
     simp add: AfterExt_def BOT_iff_D deadlock_free_implies_div_free non_deadlock_free_STOP)

lemma deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_AfterExt:
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P P \<Longrightarrow> deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P (P afterExt e) \<longleftrightarrow> 
                          (if e \<in> ready_set P \<and> e \<noteq> \<checkmark> then True else False)\<close>
  by (cases e)
     (simp add: AfterExt_def deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_After, 
      simp add: AfterExt_def BOT_iff_D deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_implies_div_free non_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_STOP)



end