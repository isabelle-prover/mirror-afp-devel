(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : HOL-CSP_OpSem - Operational semantics for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Burkhart Wolff
 *
 * This file       : Ready set of a process
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

chapter \<open> The Ready Set Notion \<close>

theory  ReadySet
  imports Sliding Throw Interrupt
begin



text \<open>This will be discussed more precisely later, but we want to define a new operator 
      which would in some way be the reciprocal of the prefix operator \<^term>\<open>e \<rightarrow> P\<close>.

      A first observation is that by prefixing \<^term>\<open>P\<close> with \<^term>\<open>e\<close>,
      we force its traces to begin with \<^term>\<open>ev e\<close>.

      Therefore we must define a notion that captures this idea.\<close>


text \<open>We start by giving a notation to \<^const>\<open>tick\<close> to be closer to Roscoe's 
      book \<^cite>\<open>"roscoe:csp:1998"\<close> (and also closer to classic CSP literature).\<close>

notation tick (\<open>\<checkmark>\<close>)


section \<open>Definition\<close>

text \<open>The ready set notion captures the set of events that can be used to begin a given process.\<close>

definition ready_set :: \<open>'\<alpha> process \<Rightarrow> '\<alpha> event set\<close>
  where \<open>ready_set P \<equiv> {a. [a] \<in> \<T> P}\<close>

lemma ready_set_def_bis: \<open>ready_set P = {e. \<exists>s. e # s \<in> \<T> P}\<close>
  and Cons_in_T_imp_elem_ready_set: \<open>e # s \<in> \<T> P \<Longrightarrow> e \<in> ready_set P\<close>
  unfolding ready_set_def using is_processT3_ST by force+


text \<open>We say here that the \<^const>\<open>ready_set\<close> of a process \<^term>\<open>P\<close> is the set
      of events \<^term>\<open>e\<close> such that there is a trace of \<^term>\<open>P\<close> starting with \<^term>\<open>e\<close>.

      One could also think about defining \<^term>\<open>ready_set P\<close> as the set of events that
      \<^term>\<open>P\<close> can not refuse at first: \<^term>\<open>{e. {e} \<notin> \<R> P}\<close>.
      These two definitions are not equivalent (and the second one is more restrictive
      than the first one). Moreover, the second does not behave well with the 
      non-deterministic choice \<^const>\<open>Ndet\<close> (see the \<^theory_text>\<open>notepad\<close> below).
      
      Therefore, we will keep the first one.

      We also have a strong argument of authority: this is the definition
      given by Roscoe (where it is called \<open>initials\<close>)
      \<^cite>\<open>\<open>p.40\<close> in "Roscoe2010UnderstandingCS"\<close>.\<close>


notepad
begin
  fix e :: \<open>'\<alpha> event\<close> \<comment>\<open>just fixing \<^typ>\<open>'\<alpha>\<close> type\<close>

  define bad_ready_set
    where \<open>bad_ready_set (P :: '\<alpha> process) \<equiv> {e. {e} \<notin> \<R> P}\<close> for P

  have bad_ready_set_subset_ready_set:
    \<open>bad_ready_set P \<subseteq> ready_set P\<close> for P
    unfolding bad_ready_set_def ready_set_def Refusals_iff
    using F_T is_processT5_S6 by blast

  have bad_behaviour_with_Ndet: 
    \<open>\<exists>P Q. bad_ready_set (P \<sqinter> Q) \<noteq> bad_ready_set P \<union> bad_ready_set Q\<close>
  proof (intro exI)
    show \<open>bad_ready_set (SKIP \<sqinter> \<bottom>) \<noteq> bad_ready_set SKIP \<union> bad_ready_set \<bottom>\<close>
    by (simp add: Ndet_BOT)
       (simp add: bad_ready_set_def F_Ndet F_SKIP F_UU Refusals_iff)
  qed
end



section \<open>Anti-Mono Rules\<close>

lemma anti_mono_ready_set_T: \<open>P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> ready_set Q \<subseteq> ready_set P\<close>
  by (simp add: Collect_mono_iff trace_refine_def ready_set_def subsetD)

lemma anti_mono_ready_set_F: \<open>P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> ready_set Q \<subseteq> ready_set P\<close>
  unfolding failure_refine_def
  by (drule F_subset_imp_T_subset) (fact anti_mono_ready_set_T[unfolded trace_refine_def])

text \<open>Of course, this anti-monotony does not hold for \<^term>\<open>(\<sqsubseteq>\<^sub>D)\<close>.\<close>

lemma anti_mono_ready_set_FD: \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> ready_set Q \<subseteq> ready_set P\<close>
  by (simp add: anti_mono_ready_set_F leFD_imp_leF)

lemma anti_mono_ready_set: \<open>P \<sqsubseteq> Q \<Longrightarrow> ready_set Q \<subseteq> ready_set P\<close>
  by (simp add: anti_mono_ready_set_T le_approx_lemma_T trace_refine_def)

lemma anti_mono_ready_set_DT: \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> ready_set Q \<subseteq> ready_set P\<close>
  by (simp add: anti_mono_ready_set_T leDT_imp_leT)


section \<open>Behaviour of \<^const>\<open>ready_set\<close> with \<^const>\<open>STOP\<close>, \<^const>\<open>SKIP\<close> and \<^term>\<open>\<bottom>\<close>\<close>

lemma ready_set_STOP: \<open>ready_set STOP = {}\<close>
  by (simp add: ready_set_def T_STOP)

text \<open>We already had @{thm STOP_iff_T}. As an immediate consequence we obtain a 
      characterization of being \<^const>\<open>STOP\<close> involving \<^const>\<open>ready_set\<close>.\<close>

lemma ready_set_empty_iff_STOP: \<open>ready_set P = {} \<longleftrightarrow> P = STOP\<close>
proof (intro iffI)
  { assume \<open>\<T> P \<noteq> {[]}\<close>
    then obtain a s where \<open>a # s \<in> \<T> P\<close> 
      by (metis Nil_elem_T is_singleton_the_elem is_singletonI'
                list.exhaust_sel singletonI empty_iff)
  hence \<open>\<exists>a. [a] \<in> \<T> P\<close> by (metis append_Cons append_Nil is_processT3_ST)}
  thus \<open>ready_set P = {} \<Longrightarrow> P = STOP\<close> 
    by (simp add: STOP_iff_T ready_set_def) presburger
qed (simp add: ready_set_STOP)


lemma ready_set_SKIP: \<open>ready_set SKIP = {\<checkmark>}\<close>
  by (simp add: ready_set_def T_SKIP)

lemma ready_set_BOT: \<open>ready_set \<bottom> = UNIV\<close>
  by (simp add: ready_set_def T_UU)

text \<open>These two, on the other hand, are not characterizations.\<close>

lemma \<open>\<exists>P. ready_set P = {\<checkmark>} \<and> P \<noteq> SKIP\<close>
proof (intro exI)
  show \<open>ready_set (STOP \<sqinter> SKIP) = {\<checkmark>} \<and> STOP \<sqinter> SKIP \<noteq> SKIP\<close>
    by (simp add: ready_set_def T_Ndet T_STOP T_SKIP)
       (metis SKIP_F_iff SKIP_Neq_STOP idem_F mono_Ndet_F_left)
qed

lemma \<open>\<exists>P. ready_set P = UNIV \<and> P \<noteq> \<bottom>\<close>
proof (intro exI)
  show \<open>ready_set ((\<box>a \<in> UNIV \<rightarrow> \<bottom>) \<sqinter> SKIP) = UNIV \<and> (\<box>a \<in> UNIV \<rightarrow> \<bottom>) \<sqinter> SKIP \<noteq> \<bottom>\<close>
  by (auto simp add: ready_set_def T_Ndet T_Mprefix Nil_elem_T T_SKIP
                     Ndet_is_BOT_iff SKIP_neq_BOT Mprefix_neq_BOT
              intro: event.exhaust)
qed



section \<open>Behaviour of \<^const>\<open>ready_set\<close> with Operators of \<^session>\<open>HOL-CSP\<close>\<close>

lemma ready_set_Mprefix:     \<open>ready_set (\<box>a \<in> A \<rightarrow> P a) = ev ` A\<close>
  and ready_set_Mndetprefix: \<open>ready_set (\<sqinter>a \<in> A \<rightarrow> P a) = ev ` A\<close>
  and ready_set_prefix:      \<open>ready_set (a \<rightarrow> Q)        = {ev a}\<close>
  by (auto simp: ready_set_def T_Mndetprefix write0_def T_Mprefix Nil_elem_T)


text \<open>As discussed earlier, \<^const>\<open>ready_set\<close> behaves well with \<^term>\<open>(\<box>)\<close> and \<^term>\<open>(\<sqinter>)\<close>.\<close>

lemma ready_set_Det:  \<open>ready_set (P \<box> Q) = ready_set P \<union> ready_set Q\<close>
  and ready_set_Ndet: \<open>ready_set (P \<sqinter> Q) = ready_set P \<union> ready_set Q\<close>
  unfolding ready_set_def by (auto simp add: T_Det T_Ndet)


lemma ready_set_Seq: 
  \<open>ready_set (P \<^bold>; Q) = (if P = \<bottom> then UNIV else ready_set P - {\<checkmark>} \<union> 
                        (if \<checkmark> \<in> ready_set P then ready_set Q else {}))\<close>
proof -
  have \<open>ready_set (P \<^bold>; Q) = ready_set P\<close> if \<open>\<checkmark> \<notin> ready_set P\<close>
  proof (intro subset_antisym subsetI)
    fix e
    assume \<open>e \<in> ready_set (P \<^bold>; Q)\<close>
    then obtain s where \<open>e # s \<in> \<T> (P \<^bold>; Q)\<close> by (simp add: ready_set_def)
    then consider \<open>e # s \<in> \<T> P\<close>
      | \<open>\<exists>t1 t2. e # s = t1 @ t2 \<and> t1 @ [\<checkmark>] \<in> \<T> P \<and> t2 \<in> \<T> Q\<close>
      by (simp add: T_Seq) (metis F_T NF_ND)
    thus \<open>e \<in> ready_set P\<close>
    proof cases
      show \<open>e # s \<in> \<T> P \<Longrightarrow> e \<in> ready_set P\<close>
        by (simp add: Cons_in_T_imp_elem_ready_set)
    next
      assume \<open>\<exists>t1 t2. e # s = t1 @ t2 \<and> t1 @ [\<checkmark>] \<in> \<T> P \<and> t2 \<in> \<T> Q\<close>
      then obtain t1 t2 where * : \<open>e # s = t1 @ t2\<close> \<open>t1 @ [\<checkmark>] \<in> \<T> P\<close> by blast
      with that have \<open>t1 \<noteq> [] \<and> hd t1 = e\<close>
        by (metis Cons_in_T_imp_elem_ready_set append_Nil hd_append2 list.sel(1))
      thus \<open>e \<in> ready_set P\<close>
        by (metis Cons_in_T_imp_elem_ready_set "*"(2) is_processT3_ST list.exhaust_sel)
    qed
  next
    show \<open>e \<in> ready_set P \<Longrightarrow> e \<in> ready_set (P \<^bold>; Q)\<close> for e
      by (simp add: ready_set_def T_Seq)
         (metis Cons_in_T_imp_elem_ready_set Nil_elem_T that
                append.right_neutral is_processT5_S7 singletonD)
  qed
  also have \<open>ready_set (P \<^bold>; Q) = ready_set P - {\<checkmark>} \<union> ready_set Q\<close>
    if \<open>P \<noteq> \<bottom>\<close> and \<open>\<checkmark> \<in> ready_set P\<close>
  proof (intro subset_antisym subsetI)
    fix e
    assume \<open>e \<in> ready_set (P \<^bold>; Q)\<close>
    then obtain s where \<open>e # s \<in> \<T> (P \<^bold>; Q)\<close> by (simp add: ready_set_def)
    with \<open>P \<noteq> \<bottom>\<close> consider \<open>e # s \<in> \<T> P\<close> \<open>e \<noteq> \<checkmark>\<close>
      | \<open>\<exists>t1 t2. e # s = t1 @ t2 \<and> t1 @ [\<checkmark>] \<in> \<T> P \<and> t2 \<in> \<T> Q\<close>
      by (simp add: T_Seq BOT_iff_D)
         (metis F_T append_T_imp_tickFree append_butlast_last_id butlast.simps(2) 
                last_ConsL list.distinct(1) process_charn tickFree_Cons)
    thus \<open>e \<in> ready_set P - {\<checkmark>} \<union> ready_set Q\<close>
    proof cases
      show \<open>e # s \<in> \<T> P \<Longrightarrow> e \<noteq> \<checkmark> \<Longrightarrow> e \<in> ready_set P - {\<checkmark>} \<union> ready_set Q\<close>
        by (simp add: Cons_in_T_imp_elem_ready_set)
    next
      assume \<open>\<exists>t1 t2. e # s = t1 @ t2 \<and> t1 @ [\<checkmark>] \<in> \<T> P \<and> t2 \<in> \<T> Q\<close>
      then obtain t1 t2 where * : \<open>e # s = t1 @ t2\<close> \<open>t1 @ [\<checkmark>] \<in> \<T> P\<close> \<open>t2 \<in> \<T> Q\<close> by blast
      show \<open>e \<in> ready_set P - {\<checkmark>} \<union> ready_set Q\<close>
      proof (cases t1)
        from "*"(1, 3) show \<open>t1 = [] \<Longrightarrow> e \<in> ready_set P - {\<checkmark>} \<union> ready_set Q\<close>
          using Cons_in_T_imp_elem_ready_set by auto
      next
        fix e' t1'
        assume \<open>t1 = e' # t1'\<close>
        with "*"(1, 2) have \<open>t1 = e # t1' \<and> e \<noteq> \<checkmark>\<close>
          by (metis append_T_imp_tickFree hd_append list.sel(1) neq_Nil_conv tickFree_Cons)
        with "*"(2) show \<open>e \<in> ready_set P - {\<checkmark>} \<union> ready_set Q\<close>
          using Cons_in_T_imp_elem_ready_set by auto
      qed
    qed
  next
    fix e
    assume \<open>e \<in> ready_set P - {\<checkmark>} \<union> ready_set Q\<close>
    then obtain s where \<open>e \<noteq> \<checkmark> \<and> e # s \<in> \<T> P \<or> e # s \<in> \<T> Q\<close>
      unfolding ready_set_def by blast
    thus \<open>e \<in> ready_set (P \<^bold>; Q)\<close>
    proof (elim disjE conjE)
      show \<open>e \<noteq> \<checkmark> \<Longrightarrow> e # s \<in> \<T> P \<Longrightarrow> e \<in> ready_set (P \<^bold>; Q)\<close>
        by (simp add: ready_set_def T_Seq)
           (metis Nil_elem_T append_Cons append_Nil
                  is_processT3_ST is_processT5_S7 singletonD)
    next
      have \<open>[\<checkmark>] \<in> \<T> P\<close> using ready_set_def that(2) by auto
      thus \<open>e # s \<in> \<T> Q \<Longrightarrow> e \<in> ready_set (P \<^bold>; Q)\<close>
        by (simp add: ready_set_def T_Seq)
           (metis append_Cons append_Nil is_processT3_ST)
    qed
  qed
  ultimately show ?thesis by (simp add: BOT_Seq ready_set_BOT)
qed
  
  

lemma ready_set_Sync:
  \<open>ready_set (P \<lbrakk>S\<rbrakk> Q) =
   (  if P = \<bottom> \<or> Q = \<bottom> then UNIV
    else (ready_set P - insert \<checkmark> (ev ` S)) \<union> 
         (ready_set Q - insert \<checkmark> (ev ` S)) \<union>
          ready_set P \<inter> ready_set Q \<inter> insert \<checkmark> (ev ` S))\<close>
  (is \<open>ready_set (P \<lbrakk>S\<rbrakk> Q) = (if P = \<bottom> \<or> Q = \<bottom> then UNIV else ?rhs)\<close>)
proof -
  have \<open>ready_set (P \<lbrakk>S\<rbrakk> Q) = ?rhs\<close> if non_BOT : \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close>
  proof (intro subset_antisym subsetI)
    show \<open>e \<in> ?rhs \<Longrightarrow> e \<in> ready_set (P \<lbrakk>S\<rbrakk> Q)\<close> for e
      by (use Nil_elem_T in \<open>fastforce simp add: ready_set_def T_Sync\<close>)
  next
    fix e
    assume \<open>e \<in> ready_set (P \<lbrakk>S\<rbrakk> Q)\<close>
    then consider \<open>\<exists>t u. t \<in> \<T> P \<and> u \<in> \<T> Q \<and> [e] setinterleaves ((t, u), insert \<checkmark> (ev ` S))\<close>
      | \<open>\<exists>t u r v. front_tickFree v \<and> (tickFree r \<or> v = []) \<and> [e] = r @ v \<and>
                   r setinterleaves ((t, u), insert \<checkmark> (ev ` S)) \<and>
                   (t \<in> \<D> P \<and> u \<in> \<T> Q \<or> t \<in> \<D> Q \<and> u \<in> \<T> P)\<close>
      by (simp add: ready_set_def T_Sync) blast
    thus \<open>e \<in> ?rhs\<close>
    proof cases
      assume \<open>\<exists>t u. t \<in> \<T> P \<and> u \<in> \<T> Q \<and> [e] setinterleaves ((t, u), insert \<checkmark> (ev ` S))\<close>
      then obtain t u where assms : \<open>t \<in> \<T> P\<close> \<open>u \<in> \<T> Q\<close> 
                                    \<open>[e] setinterleaves ((t, u), insert \<checkmark> (ev ` S))\<close> by blast
      thus \<open>e \<in> ?rhs\<close>
        apply (cases t; cases u; simp add: ready_set_def split: if_split_asm)
        using empty_setinterleaving Sync.sym by blast+
    next
      assume \<open>\<exists>t u r v. front_tickFree v \<and> (tickFree r \<or> v = []) \<and> [e] = r @ v \<and>
                        r setinterleaves ((t, u), insert \<checkmark> (ev ` S)) \<and>
                        (t \<in> \<D> P \<and> u \<in> \<T> Q \<or> t \<in> \<D> Q \<and> u \<in> \<T> P)\<close> 
      then obtain t u r v
        where * : \<open>front_tickFree v\<close> \<open>tickFree r \<or> v = []\<close> \<open>[e] = r @ v\<close>
                  \<open>r setinterleaves ((t, u), insert \<checkmark> (ev ` S))\<close>
                  \<open>t \<in> \<D> P \<and> u \<in> \<T> Q \<or> t \<in> \<D> Q \<and> u \<in> \<T> P\<close> by blast
      have \<open>r \<noteq> []\<close> using "*"(4, 5) BOT_iff_D empty_setinterleaving that by blast
      hence \<open>r = [e] \<and> v = []\<close>
        by (metis (no_types, lifting) "*"(3) Nil_is_append_conv append_eq_Cons_conv)
      also obtain e' t' where \<open>t = e' # t'\<close>
        using "*"(5) BOT_iff_D non_BOT by (cases t; blast)
      ultimately show \<open>e \<in> ?rhs\<close> 
        using "*"(4, 5) apply (simp add: ready_set_def subset_iff T_Sync)
        apply (cases u; simp split: if_split_asm)
        by (metis (no_types, opaque_lifting) [[metis_verbose = false]]
                   D_T Sync.sym empty_setinterleaving)+
    qed
  qed
  thus \<open>ready_set (P \<lbrakk>S\<rbrakk> Q) = (if P = \<bottom> \<or> Q = \<bottom> then UNIV else ?rhs)\<close>
    by (simp add: Sync_BOT Sync_commute[of \<bottom>, simplified Sync_BOT] ready_set_BOT)
qed


lemma ready_set_Renaming:
  \<open>ready_set (Renaming P f) = (if P = \<bottom> then UNIV else EvExt f ` (ready_set P))\<close>
proof -
  { fix y t1 t2
    assume assms: \<open>[] \<notin> \<D> P\<close> \<open>[y] = map (EvExt f) t1 @ t2\<close> \<open>t1 \<in> \<D> P\<close>
    from assms have \<open>t2 = []\<close>
      by (metis Nil_is_append_conv list.map_disc_iff list.sel(3) tl_append2)
    with assms(2) D_T[OF assms(3)] have \<open>\<exists>x. [x] \<in> \<T> P \<and> y = EvExt f x\<close> by auto
  }
  thus ?thesis by (auto simp add: ready_set_def T_Renaming image_iff BOT_iff_D)
qed




text \<open>Because for the expression of its traces (and more specifically of its divergences),
      dealing with \<^const>\<open>Hiding\<close> is much more difficult.\<close>

text \<open>We start with two characterizations:
      \<^item> one to understand \<^prop>\<open>P \ S = \<bottom>\<close>
      \<^item> the other to understand \<^prop>\<open>[e] \<in> \<D> (P \ S)\<close>.\<close>

lemma Hiding_is_BOT_iff : 
  \<open>P \ S = \<bottom> \<longleftrightarrow> (\<exists>t. set t \<subseteq> ev ` S \<and> 
                      (t \<in> \<D> P \<or> (\<exists> f. isInfHiddenRun f P S \<and> t \<in> range f)))\<close>
  (is \<open>P \ S = \<bottom> \<longleftrightarrow> ?rhs\<close>)
proof (subst BOT_iff_D, intro iffI)
  show \<open>[] \<in> \<D> (P \ S) \<Longrightarrow> ?rhs\<close>
    by (simp add: D_Hiding)
       (metis (no_types, lifting) filter_empty_conv subsetI)
next
  assume \<open>?rhs\<close>
  then obtain t where * : \<open>set t \<subseteq> ev ` S\<close>
                          \<open>t \<in> \<D> P \<or> (\<exists>f. isInfHiddenRun f P S \<and> t \<in> range f)\<close> by blast
  hence \<open>tickFree t \<and> [] = trace_hide t (ev ` S)\<close>
    unfolding tickFree_def by (auto simp add: D_Hiding subset_iff)
  with "*"(2) show \<open>[] \<in> \<D> (P \ S)\<close> by (simp add: D_Hiding) metis
qed

lemma event_in_D_Hiding_iff :
  \<open>[e] \<in> \<D> (P \ S) \<longleftrightarrow>
   P \ S = \<bottom> \<or> (\<exists>x t. e = ev x \<and> x \<notin> S \<and> [ev x] = trace_hide t (ev ` S) \<and>
                      (t \<in> \<D> P \<or> (\<exists>f. isInfHiddenRun f P S \<and> t \<in> range f)))\<close>
  (is \<open>[e] \<in> \<D> (P \ S) \<longleftrightarrow> P \ S = \<bottom> \<or> ?ugly_assertion\<close>)
proof (intro iffI)
  assume assm : \<open>[e] \<in> \<D> (P \ S)\<close>
  show \<open>P \ S = \<bottom> \<or> ?ugly_assertion\<close>
  proof (cases e)
    assume \<open>e = \<checkmark>\<close>
    with assm have \<open>P \ S = \<bottom>\<close>
      using BOT_iff_D front_tickFree_Nil is_processT9_tick by blast
    thus \<open>P \ S = \<bottom> \<or> ?ugly_assertion\<close> by blast
  next
    fix x
    assume \<open>e = ev x\<close>
    with assm obtain t u
      where * : \<open>front_tickFree u\<close> \<open>tickFree t\<close>
                \<open>[ev x] = trace_hide t (ev ` S) @ u\<close>
                \<open>t \<in> \<D> P \<or> (\<exists> f. isInfHiddenRun f P S \<and> t \<in> range f)\<close>
      by (simp add: D_Hiding) blast
    from "*"(3) consider \<open>set t \<subseteq> ev ` S\<close> | \<open>x \<notin> S\<close> \<open>ev x \<in> set t\<close>
      by (metis (no_types, lifting) Cons_eq_append_conv empty_filter_conv
          filter_eq_Cons_iff filter_is_subset image_eqI list.set_intros(1) subset_code(1))
    thus \<open>P \ S = \<bottom> \<or> ?ugly_assertion\<close>
    proof cases
      assume \<open>set t \<subseteq> ev ` S\<close>
      hence \<open>P \ S = \<bottom>\<close> by (meson "*"(4) Hiding_is_BOT_iff)
      thus \<open>P \ S = \<bottom> \<or> ?ugly_assertion\<close> by blast
    next
      assume \<open>x \<notin> S\<close> \<open>ev x \<in> set t\<close>
      with "*"(3) have \<open>[ev x] = trace_hide t (ev ` S)\<close>
        by (induct t) (auto split: if_split_asm)
      with "*"(4) \<open>e = ev x\<close> \<open>x \<notin> S\<close> have \<open>?ugly_assertion\<close> by blast
      thus \<open>P \ S = \<bottom> \<or> ?ugly_assertion\<close> by blast
    qed
  qed
next
  show \<open>P \ S = \<bottom> \<or> ?ugly_assertion \<Longrightarrow> [e] \<in> \<D> (P \ S)\<close>
  proof (elim disjE)
    show \<open>P \ S = \<bottom> \<Longrightarrow> [e] \<in> \<D> (P \ S)\<close> by (simp add: D_UU)
  next
    show \<open>?ugly_assertion \<Longrightarrow> [e] \<in> \<D> (P \ S)\<close>
      by (elim exE, simp add: D_Hiding)
         (metis Hiding_tickFree append_Nil2 event.simps(3)
                front_tickFree_Nil tickFree_Cons tickFree_Nil)
  qed
qed


text \<open>Now we can express \<^term>\<open>ready_set (P \ S)\<close>.
      This result contains the term \<^term>\<open>P \ S = \<bottom>\<close> that can be unfolded with
      @{thm [source] Hiding_is_BOT_iff} and the term \<^term>\<open>[ev x] \<in> \<D> (P \ S)\<close>
      that can be unfolded with @{thm [source] event_in_D_Hiding_iff}.\<close>

lemma ready_set_Hiding:
  \<open>ready_set (P \ S) = 
   (if P \ S = \<bottom> then UNIV else
    {e. case e of \<checkmark> \<Rightarrow> \<exists>t. set t \<subseteq> ev ` S \<and> t @ [\<checkmark>] \<in> \<T> P
        | ev x \<Rightarrow> x \<notin> S \<and> ([ev x] \<in> \<D> (P \ S) \<or> 
                           (\<exists>t. [ev x] = trace_hide t (ev ` S) \<and> (t, ev ` S) \<in> \<F> P))})\<close>
  (is \<open>ready_set (P \ S) = (if P \ S = \<bottom> then UNIV else ?set)\<close>)
proof (split if_split, intro conjI impI)
  show \<open>P \ S = \<bottom> \<Longrightarrow> ready_set (P \ S) = UNIV\<close> by (simp add: ready_set_BOT)
next
  assume non_BOT : \<open>P \ S \<noteq> \<bottom>\<close>
  show \<open>ready_set (P \ S) = ?set\<close>
  proof (intro subset_antisym subsetI)
    fix e
    assume ready : \<open>e \<in> ready_set (P \ S)\<close>
    \<comment> \<open>This implies \<^prop>\<open>e \<notin> ev ` S\<close> with our other assumptions.\<close>
    { fix x
      assume assms : \<open>x \<in> S\<close> \<open>ev x \<in> ready_set (P \ S)\<close>
      then consider \<open>\<exists>t. [ev x] = trace_hide t (ev ` S) \<and> (t, ev ` S) \<in> \<F> P\<close>
        | \<open>\<exists>t u. front_tickFree u \<and> tickFree t \<and> [ev x] = trace_hide t (ev ` S) @ u \<and> 
                 (t \<in> \<D> P \<or> (\<exists> f. isInfHiddenRun f P S \<and> t \<in> range f))\<close>
        by (simp add: ready_set_def T_Hiding) blast
      hence \<open>P \ S = \<bottom>\<close>
      proof cases
        assume \<open>\<exists>t. [ev x] = trace_hide t (ev ` S) \<and> (t, ev ` S) \<in> \<F> P\<close>
        hence False by (metis Cons_eq_filterD image_eqI assms(1))
        thus \<open>P \ S = \<bottom>\<close> by blast
      next
        assume \<open>\<exists>t u. front_tickFree u \<and> tickFree t \<and> [ev x] = trace_hide t (ev ` S) @ u \<and>
                      (t \<in> \<D> P \<or> (\<exists> f. isInfHiddenRun f P S \<and> t \<in> range f))\<close>
        then obtain t u 
          where * : \<open>front_tickFree u\<close> \<open>tickFree t\<close> \<open>[ev x] = trace_hide t (ev ` S) @ u\<close>
                    \<open>t \<in> \<D> P \<or> (\<exists> f. isInfHiddenRun f P S \<and> t \<in> range f)\<close> by blast
        from *(3) have ** : \<open>set t \<subseteq> ev ` S\<close>
          by (induct t) (simp_all add: assms(1) split: if_split_asm)
        from *(4) "**" Hiding_is_BOT_iff show \<open>P \ S = \<bottom>\<close> by blast
      qed
    }
    with ready have * : \<open>e \<notin> ev ` S\<close> using non_BOT by blast

    from ready consider \<open>[e] \<in> \<D> (P \ S)\<close>
      | \<open>\<exists>t. [e] = trace_hide t (ev ` S) \<and> (t, ev ` S) \<in> \<F> P\<close>
      unfolding ready_set_def by (simp add: T_Hiding D_Hiding) blast
    thus \<open>e \<in> ?set\<close>
    proof cases
      assume assm : \<open>[e] \<in> \<D> (P \ S)\<close>
      then obtain x where \<open>e = ev x\<close>
        \<comment> \<open>because \<^prop>\<open>[tick] \<in> \<D> (P \ S) \<Longrightarrow> P \ S = \<bottom>\<close>\<close>
        by (metis BOT_iff_D append_Nil event.exhaust non_BOT process_charn)
      with assm "*" show \<open>e \<in> ?set\<close> by (simp add: image_iff)
    next
      assume \<open>\<exists>t. [e] = trace_hide t (ev ` S) \<and> (t, ev ` S) \<in> \<F> P\<close>
      then obtain t where ** : \<open>[e] = trace_hide t (ev ` S)\<close>
                               \<open>(t, ev ` S) \<in> \<F> P\<close> by blast
      thus \<open>e \<in> ?set\<close>
      proof (cases e)
        have \<open>e = \<checkmark> \<Longrightarrow> set (butlast t) \<subseteq> ev ` S \<and> butlast t @ [\<checkmark>] \<in> \<T> P\<close>
          using "**" apply (cases t rule: rev_cases; simp add: split: if_split_asm)
          by (metis F_T filter_empty_conv subset_code(1))
             (metis Hiding_tickFree front_tickFree_implies_tickFree process_charn tickFree_Cons)
        thus \<open>e = \<checkmark> \<Longrightarrow> e \<in> ?set\<close> by auto
      next
        fix x
        assume \<open>e = ev x\<close>
        with "*" have \<open>x \<notin> S\<close> by blast
        with \<open>e = ev x\<close> "**"(1) "**"(2) show \<open>e \<in> ?set\<close> by auto
      qed
    qed
  next
    fix e
    assume \<open>e \<in> ?set\<close>
    then consider \<open>e = \<checkmark>\<close> \<open>\<exists>t. set t \<subseteq> ev ` S \<and> t @ [\<checkmark>] \<in> \<T> P\<close>
      | \<open>\<exists>x. e = ev x \<and> x \<notin> S \<and>
             ([ev x] \<in> \<D> (P \ S) \<or>
              (\<exists>t. [ev x] = trace_hide t (ev ` S) \<and> (t, ev ` S) \<in> \<F> P))\<close> by (cases e; simp)
    thus \<open>e \<in> ready_set (P \ S)\<close>
    proof cases
      assume assms : \<open>e = \<checkmark>\<close> \<open>\<exists>t. set t \<subseteq> ev ` S \<and> t @ [\<checkmark>] \<in> \<T> P\<close>
      from assms(2) obtain t
        where * : \<open>set t \<subseteq> ev ` S\<close> \<open>t @ [\<checkmark>] \<in> \<T> P\<close> by blast
      have ** : \<open>[e] = trace_hide (t @ [\<checkmark>]) (ev ` S) \<and> (t @ [\<checkmark>], ev ` S) \<in> \<F> P\<close>
        using "*"(1) by (simp add: assms(1) image_iff tick_T_F[OF "*"(2)] subset_iff)
      show \<open>e \<in> ready_set (P \ S)\<close>
        unfolding ready_set_def by (simp add: T_Hiding) (use "**" in blast)
    next
      show \<open>\<exists>x. e = ev x \<and> x \<notin> S \<and>
             ([ev x] \<in> \<D> (P \ S) \<or>
              (\<exists>t. [ev x] = trace_hide t (ev ` S) \<and> (t, ev ` S) \<in> \<F> P)) \<Longrightarrow>
            e \<in> ready_set (P \ S)\<close>
        apply (elim exE conjE disjE)
        using Cons_in_T_imp_elem_ready_set D_T apply blast
        unfolding ready_set_def by (simp add: T_Hiding) blast
    qed
  qed
qed


text \<open>In the end the result would look something like this:

      @{thm ready_set_Hiding[unfolded event_in_D_Hiding_iff Hiding_is_BOT_iff, no_vars]}\<close>

text \<open>Obviously, it is not very easy to use. We will therefore rely more on the corollaries below.\<close>
 
corollary ready_tick_Hiding_iff :
  \<open>\<checkmark> \<in> ready_set (P \ B) \<longleftrightarrow> P \ B = \<bottom> \<or> (\<exists>t. set t \<subseteq> ev ` B \<and> t @ [\<checkmark>] \<in> \<T> P)\<close>
  by (simp add: ready_set_Hiding)

corollary ready_tick_imp_ready_tick_Hiding:
  \<open>\<checkmark> \<in> ready_set P \<Longrightarrow> \<checkmark> \<in> ready_set (P \ B)\<close>
  by (subst ready_set_Hiding, simp add: ready_set_def)
     (metis append_Nil empty_iff empty_set subset_iff)


corollary ready_inside_Hiding_iff :
  \<open>e \<in> S \<Longrightarrow> ev e \<in> ready_set (P \ S) \<longleftrightarrow> P \ S = \<bottom>\<close>
  by (simp add: ready_set_Hiding)


corollary ready_notin_Hiding_iff :
  \<open>e \<notin> S \<Longrightarrow> ev e \<in> ready_set (P \ S) \<longleftrightarrow>
   P \ S = \<bottom> \<or>
   (\<exists>t. [ev e] = trace_hide t (ev ` S) \<and>
        (t \<in> \<D> P \<or> (\<exists>f. isInfHiddenRun f P S \<and> t \<in> range f) \<or> (t, ev ` S) \<in> \<F> P))\<close>
  by (auto simp add: ready_set_Hiding event_in_D_Hiding_iff split: if_split_asm)


corollary ready_notin_imp_ready_Hiding:
  \<open>ev e \<in> ready_set (P \ S)\<close> if ready : \<open>ev e \<in> ready_set P\<close> and notin : \<open>e \<notin> S\<close>
proof -
  from inf_hidden[of S \<open>[ev e]\<close> P]
  consider \<open>\<exists>f. isInfHiddenRun f P S \<and> [ev e] \<in> range f\<close>  
    | \<open>\<exists>t. [ev e] = trace_hide t (ev ` S) \<and> (t, ev ` S) \<in> \<F> P\<close>
    by (simp add: ready_set_Hiding image_iff[of \<open>ev e\<close>] notin)
       (metis mem_Collect_eq ready ready_set_def)
  thus \<open>ev e \<in> ready_set (P \ S)\<close>
  proof cases
    show \<open>\<exists>f. isInfHiddenRun f P S \<and> [ev e] \<in> range f \<Longrightarrow> ev e \<in> ready_set (P \ S)\<close>
      apply (rule Cons_in_T_imp_elem_ready_set[of \<open>ev e\<close> \<open>[]\<close>], rule D_T)
      apply (simp add: event_in_D_Hiding_iff image_iff[of \<open>ev e\<close>] notin)
      by (metis (no_types, lifting) event.inject filter.simps image_iff notin)
  next
    assume \<open>\<exists>t. [ev e] = trace_hide t (ev ` S) \<and> (t, ev ` S) \<in> \<F> P\<close>
    thus \<open>ev e \<in> ready_set (P \ S)\<close> by (simp add: ready_set_Hiding notin)
  qed
qed


(* old proofs below 

lemma tick_not_hidden_ready_set_Hiding:
  \<open>\<checkmark> \<in> ready_set P \<Longrightarrow> \<checkmark> \<in> ready_set (P \ B)\<close>
  by (simp add: ready_set_def T_Hiding)
     (metis (no_types, lifting) append_Nil event.simps(3) filter.simps image_iff tick_T_F)


lemma ready_notin_ready_Hiding:
  \<open>ev e \<in> ready_set P \<Longrightarrow> e \<notin> B \<Longrightarrow> ev e \<in> ready_set (P \ B)\<close>
proof -
  have \<open>\<exists> t u. front_tickFree u \<and> tickFree t \<and> [ev e] = trace_hide t (ev ` B) @ u \<and> 
               (t \<in> \<D> P \<or> (\<exists> f. isInfHiddenRun f P B \<and> t \<in> range f))\<close>
    if a1 : \<open>[ev e] \<in> \<T> P\<close> and a2 : \<open>e \<notin> B\<close> 
   and a3 : \<open>\<forall>t. [ev e] = trace_hide t (ev ` B) \<longrightarrow> (t, ev ` B) \<notin> \<F> P\<close>
  proof -
    have   * : \<open>[ev e] = trace_hide [ev e] (ev ` B)\<close> by (simp add: a2 image_iff)
    hence ** : \<open>\<forall>t. trace_hide t (ev ` B) = trace_hide [ev e] (ev ` B) \<longrightarrow> (t, ev ` B) \<notin> \<F> P\<close>
      using a3 by presburger
    show \<open>\<exists> t u. front_tickFree u \<and> tickFree t \<and> [ev e] = trace_hide t (ev ` B) @ u \<and> 
                 (t \<in> \<D> P \<or> (\<exists> f. isInfHiddenRun f P B \<and> t \<in> range f))\<close>
      apply (rule_tac x = \<open>[ev e]\<close> in exI, rule_tac x = \<open>[]\<close> in exI, intro conjI)
         apply simp
        apply simp
       apply (simp only: append_Nil2, rule "*")
      by (rule disjI2, rule inf_hidden[OF ** a1])
  qed
  thus \<open>ev e \<in> ready_set P \<Longrightarrow> e \<notin> B \<Longrightarrow> ev e \<in> ready_set (P \ B)\<close>
    by (auto simp add: ready_set_def T_Hiding)
qed


lemma ready_Hiding_inside_iff : 
  \<open>ev e \<in> ready_set (P \ B) \<longleftrightarrow>  
   (\<exists>t. set t \<subseteq> ev ` B \<and>
   (t \<in> \<D> P \<or> (\<exists>f. isInfHiddenRun f P B \<and> t \<in> range f)))\<close> (is \<open>?lhs \<longleftrightarrow> ?rhs\<close>)
  if inside : \<open>e \<in> B\<close>
proof (intro iffI)
  assume ?lhs
  then consider \<open>\<exists>t. [ev e] = trace_hide t (ev ` B) \<and> (t, ev `B) \<in> \<F> P\<close>
    | \<open>\<exists>t u. front_tickFree u \<and> tickFree t \<and> [ev e] = trace_hide t (ev ` B) @ u \<and> 
             (t \<in> \<D> P \<or> (\<exists> f. isInfHiddenRun f P B \<and> t \<in> range f))\<close>
    by (simp add: ready_set_def T_Hiding) blast
  thus ?rhs
  proof cases
    assume \<open>\<exists>t. [ev e] = trace_hide t (ev ` B) \<and> (t, ev ` B) \<in> \<F> P\<close>
    hence False by (metis Cons_eq_filterD image_eqI inside)
    thus ?rhs by blast
  next
    assume \<open>\<exists>t u. front_tickFree u \<and> tickFree t \<and> [ev e] = trace_hide t (ev ` B) @ u \<and> 
                  (t \<in> \<D> P \<or> (\<exists> f. isInfHiddenRun f P B \<and> t \<in> range f))\<close>
    then obtain t u 
      where * : \<open>front_tickFree u\<close> \<open>tickFree t\<close> \<open>[ev e] = trace_hide t (ev ` B) @ u\<close>
                \<open>t \<in> \<D> P \<or> (\<exists> f. isInfHiddenRun f P B \<and> t \<in> range f)\<close> by blast
    from *(3) have ** : \<open>set t \<subseteq> insert \<checkmark> (ev ` B)\<close>
      by (induct t) (simp_all add: inside split: if_split_asm)
    from *(4) show ?rhs by (rule_tac x = t in exI)
                           (meson "*"(2) "**" subset_insert tickFree_def)
  qed
next
  assume ?rhs
  then obtain t
    where * : \<open>set t \<subseteq> ev ` B\<close>
              \<open>t \<in> \<D> P \<or> (\<exists>f. isInfHiddenRun f P B \<and> t \<in> range f)\<close> by blast
  show ?lhs
    apply (simp add: ready_set_def T_Hiding)
    apply (rule disjI2)
    apply (rule_tac x = t in exI, rule_tac x = \<open>[ev e]\<close> in exI, simp, intro conjI)
      apply (meson "*"(1) event.simps(3) image_iff subsetD tickFree_def)
     apply (meson "*"(1) filter_False subset_eq)
    using "*"(2) by blast
qed *)
  
  


section \<open>Behaviour of \<^const>\<open>ready_set\<close> with Operators of \<^session>\<open>HOL-CSPM\<close>\<close>
  
lemma ready_set_MultiDet:
  \<open>finite A \<Longrightarrow> ready_set (MultiDet A P) = (\<Union>a \<in> A. ready_set (P a))\<close>
  by (induct A rule: finite_induct)
     (simp_all add: ready_set_STOP ready_set_Det)


lemma ready_set_MultiNdet:
  \<open>finite A \<Longrightarrow> ready_set (MultiNdet A P) = (\<Union>a \<in> A. ready_set (P a))\<close>
  apply (cases \<open>A = {}\<close>, simp add: ready_set_STOP)
  by (rotate_tac, induct A rule: finite_set_induct_nonempty)
     (simp_all add: ready_set_Ndet)


lemma ready_set_GlobalNdet:
  \<open>ready_set (GlobalNdet A P) = (\<Union>a \<in> A. ready_set (P a))\<close>
  by (auto simp add: ready_set_def T_GlobalNdet)


lemma ready_set_MultiSeq:
  \<open>ready_set (MultiSeq L P) =
   (  if L = [] then {\<checkmark>}
    else   if P (hd L) = \<bottom> then UNIV
         else   if \<checkmark> \<in> ready_set (P (hd L)) 
              then ready_set (P (hd L)) - {\<checkmark>} \<union> ready_set (MultiSeq (tl L) P)
              else ready_set (P (hd L)))\<close>
  by (induct L) (simp_all add: ready_set_SKIP ready_set_Seq)


lemma ready_set_MultiSync:
  \<open>ready_set (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> m \<in># M. P m) =
   (  if M = {#} then {}
    else if \<exists>m \<in># M. P m = \<bottom> then UNIV
    else if \<exists>m. M = {#m#} then ready_set (P (THE m. M = {#m#}))
    else {e. \<exists>m \<in># M. e \<in> ready_set (P m) - insert \<checkmark> (ev ` S)} \<union>
         {e \<in> insert \<checkmark> (ev ` S). \<forall>m \<in># M. e \<in> ready_set (P m)})\<close>
proof -
  have * : \<open>ready_set (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> m \<in># M + {#a, a'#}. P m) = 
            {e. \<exists>m \<in># M + {#a, a'#}. e \<in> ready_set (P m) - insert \<checkmark> (ev ` S)} \<union>
            {e \<in> insert \<checkmark> (ev ` S). \<forall>m \<in># M + {#a, a'#}. e \<in> ready_set (P m)}\<close>
    if non_BOT : \<open>\<forall>m \<in># M + {#a, a'#}. P m \<noteq> \<bottom>\<close> for a a' M
  proof (induct M rule: msubset_induct'[OF subset_mset.refl])
    case 1
    then show ?case by (auto simp add: non_BOT ready_set_Sync)
  next
    case (2 a'' M')
    have * : \<open>MultiSync S (add_mset a'' M' + {#a, a'#}) P = 
              P a'' \<lbrakk>S\<rbrakk> (MultiSync S (M' + {#a, a'#}) P)\<close> 
      by (simp add: add_mset_commute)
    have ** : \<open>\<not> (P a'' = \<bottom> \<or> MultiSync S (M' + {#a, a'#}) P = \<bottom>)\<close>
      using "2.hyps"(1, 2) in_diffD non_BOT 
      by (auto simp add: MultiSync_is_BOT_iff Sync_is_BOT_iff, fastforce, meson mset_subset_eqD)
    show ?case
      by (auto simp only: * ready_set_Sync ** "2.hyps"(3), auto)
  qed

  show ?thesis
  proof (cases \<open>\<exists>m \<in># M. P m = \<bottom>\<close>)
    show \<open>\<exists>m \<in># M. P m = \<bottom> \<Longrightarrow> ?thesis\<close>
      by (simp add: ready_set_STOP) (metis MultiSync_BOT_absorb ready_set_BOT)
  next
    show \<open>\<not> (\<exists>m\<in>#M. P m = \<bottom>) \<Longrightarrow> ?thesis\<close>
    proof (cases \<open>\<exists>a a' M'. M = M' + {#a, a'#}\<close>)
      assume assms : \<open>\<not> (\<exists>m\<in>#M. P m = \<bottom>)\<close> \<open>\<exists>a a' M'. M = M' + {#a, a'#}\<close>
      from assms(2) obtain a a' M' where \<open>M = M' + {#a, a'#}\<close> by blast
      with * assms(1) show ?thesis by simp
    next
      assume \<open>\<nexists>a a' M'. M = M' + {#a, a'#}\<close>
      hence \<open>M = {#} \<or> (\<exists>m. M = {#m#})\<close>
        by (metis add.right_neutral multiset_cases union_mset_add_mset_right)
      thus ?thesis by (auto simp add: ready_set_STOP ready_set_BOT)
    qed
  qed
qed


 
section \<open>Behaviour of \<^const>\<open>ready_set\<close> with Operators of \<^session>\<open>HOL-CSP_OpSem\<close>\<close>

lemma ready_set_Sliding: 
  \<open>ready_set (P \<rhd> Q) = ready_set P \<union> ready_set Q\<close>
  unfolding ready_set_def by (auto simp add: T_Sliding)


lemma ready_set_Throw: \<open>ready_set (P \<Theta> a \<in> A. Q a) = ready_set P\<close>
  apply (intro subset_antisym subsetI;
      simp add: ready_set_def T_Throw image_iff)
   apply (elim disjE)
     apply (solves \<open>simp\<close>)
    apply (metis D_T process_charn)
   apply (metis Nil_is_append_conv list.sel(3) neq_Nil_conv self_append_conv2 tl_append2)
  by (metis Nil_elem_T append_Nil empty_set inf_bot_left)
 

corollary Throw_is_STOP_iff: \<open>P \<Theta> a \<in> A. Q a = STOP \<longleftrightarrow> P = STOP\<close>
  by (simp add: ready_set_empty_iff_STOP[symmetric] ready_set_Throw)


lemma ready_set_Interrupt: \<open>ready_set (P \<triangle> Q) = ready_set P \<union> ready_set Q\<close>
  apply (intro subset_antisym subsetI;
         simp add: ready_set_def T_Interrupt)
  by (metis Nil_is_append_conv append.left_neutral 
            append.right_neutral butlast.simps(2) butlast_append)
     (use Nil_elem_T tickFree_Nil in blast)

corollary Interrupt_is_STOP_iff: \<open>P \<triangle> Q = STOP \<longleftrightarrow> P = STOP \<and> Q = STOP\<close>
  by (simp add: ready_set_empty_iff_STOP[symmetric] ready_set_Interrupt)



section \<open>Behaviour of \<^const>\<open>ready_set\<close> with Reference Processes\<close>

lemma ready_set_DF: \<open>ready_set (DF A) = ev ` A\<close>
  by (subst DF_unfold) (simp add: ready_set_Mndetprefix)

lemma ready_set_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P: \<open>ready_set (DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) = insert \<checkmark> (ev ` A)\<close>
  by (subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold)
     (simp add: ready_set_Mndetprefix ready_set_Ndet ready_set_SKIP)

lemma ready_set_RUN: \<open>ready_set (RUN A) = ev ` A\<close>
  by (subst RUN_unfold) (simp add: ready_set_Mprefix)

lemma ready_set_CHAOS: \<open>ready_set (CHAOS A) = ev ` A\<close>
  by (subst CHAOS_unfold)
     (simp add: ready_set_Mprefix ready_set_Ndet ready_set_STOP)

lemma ready_set_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P: \<open>ready_set (CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A) = insert \<checkmark> (ev ` A)\<close>
  by (subst CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold)
     (simp add: ready_set_Mprefix ready_set_Ndet
                ready_set_STOP ready_set_SKIP)



end
