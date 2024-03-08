(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : HOL-CSP_OpSem - Operational semantics for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Burkhart Wolff
 *
 * This file       : Common work for operational semantics based on refinements bis
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

chapter\<open> Generic Operational Semantics as a Locale, bis\<close>

theory  OpSemGenericBis
  imports AfterTraceBis "HOL-CSPM.DeadlockResults"
begin

(*<*)
hide_const R
text \<open>We need to hide this because we want to be allowed to use the letter R in our lemmas.
      We can still access this notion via the notation \<^term>\<open>\<R> P\<close>.
      In further versions of \<^theory>\<open>HOL-CSP.Process\<close>, R will be renamed in Refusals 
      and we will remove this paragraph.\<close>
(*>*)

section \<open>Definition\<close>

locale OpSemGeneric = 
    fixes \<tau>_trans :: \<open>'\<alpha> process \<Rightarrow> '\<alpha> process \<Rightarrow> bool\<close> (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50)
  assumes \<tau>_trans_NdetL: \<open>P \<sqinter> Q \<leadsto>\<^sub>\<tau> P\<close>
      and \<tau>_trans_transitivity: \<open>P \<leadsto>\<^sub>\<tau> Q \<Longrightarrow> Q \<leadsto>\<^sub>\<tau> R \<Longrightarrow> P \<leadsto>\<^sub>\<tau> R\<close>
      and \<tau>_trans_anti_mono_ready_set: \<open>P \<leadsto>\<^sub>\<tau> Q \<Longrightarrow> ready_set Q \<subseteq> ready_set P\<close>
      and \<tau>_trans_mono_AfterExt:
          \<open>e \<in> ready_set Q \<Longrightarrow> P \<leadsto>\<^sub>\<tau> Q \<Longrightarrow> P afterExt e \<leadsto>\<^sub>\<tau> Q afterExt e\<close>
begin

text \<open>This locale needs to be instantiated with a binary
      relation @{term [show_types] \<open>(\<leadsto>\<^sub>\<tau>)\<close>} which:
      \<^item> is compatible with \<^const>\<open>Ndet\<close>
      \<^item> is transitive
      \<^item> makes \<^const>\<open>ready_set\<close> anti-monotonic
      \<^item> makes @{const [source] AfterExt} monotonic.\<close>

text \<open>From the \<open>\<tau>\<close> transition \<^term>\<open>P \<leadsto>\<^sub>\<tau> Q\<close> we derive the event transition as follows:\<close>

abbreviation event_trans :: \<open>'\<alpha> process \<Rightarrow> '\<alpha> event \<Rightarrow> '\<alpha> process \<Rightarrow> bool\<close> (\<open>_/ \<leadsto>_/ _\<close> [50, 3, 51] 50)
  where \<open>P \<leadsto>e Q \<equiv> e \<in> ready_set P \<and> P afterExt e \<leadsto>\<^sub>\<tau> Q\<close>


text \<open>From idempotence, commutativity and \<^term>\<open>\<bottom>\<close> absorbance of \<^term>\<open>(\<sqinter>)\<close>, 
      we get the following for free.\<close>

lemma \<tau>_trans_eq: \<open>P \<leadsto>\<^sub>\<tau> P\<close>
  and \<tau>_trans_NdetR: \<open>P \<sqinter> Q \<leadsto>\<^sub>\<tau> Q\<close>
  and BOT_\<tau>_trans_anything: \<open>\<bottom> \<leadsto>\<^sub>\<tau> P\<close>
  and BOT_ev_trans_anything: \<open>\<bottom> \<leadsto>(ev e) P\<close>
  by (metis Ndet_id \<tau>_trans_NdetL,
      metis Ndet_commute \<tau>_trans_NdetL,
      metis Ndet_BOT \<tau>_trans_NdetL,
      metis AfterExt_BOT Ndet_BOT UNIV_I \<tau>_trans_NdetL event.simps(3) ready_set_BOT) 


text \<open>As immediate consequences of the axioms, we prove that event transitions 
      absorb \<open>\<tau>\<close> transitions on right and on left.\<close>

lemma event_trans_\<tau>_trans: \<open>P \<leadsto> e P' \<Longrightarrow> P' \<leadsto>\<^sub>\<tau> P''  \<Longrightarrow> P \<leadsto> e P''\<close>
  by (meson \<tau>_trans_transitivity)

lemma \<tau>_trans_event_trans: \<open>P \<leadsto>\<^sub>\<tau> P'  \<Longrightarrow> P' \<leadsto> e P'' \<Longrightarrow> P \<leadsto> e P''\<close>
  using \<tau>_trans_mono_AfterExt \<tau>_trans_transitivity \<tau>_trans_anti_mono_ready_set by blast



text \<open>We can now define the concept of transition with a trace 
      and demonstrate the first properties.\<close>

inductive trace_trans :: \<open>'\<alpha> process \<Rightarrow> '\<alpha> trace \<Rightarrow> '\<alpha> process \<Rightarrow> bool\<close> (\<open>_/ \<leadsto>\<^sup>*_/ _\<close> [50, 3, 51] 50)
  where    trace_\<tau>_trans : \<open>P \<leadsto>\<^sub>\<tau> P' \<Longrightarrow> P \<leadsto>\<^sup>* [] P'\<close>
  |     trace_tick_trans : \<open>P \<leadsto>\<checkmark>  P' \<Longrightarrow> P \<leadsto>\<^sup>* [\<checkmark>] P'\<close>
  |  trace_Cons_ev_trans :
     \<open>P \<leadsto>(ev e) P' \<Longrightarrow> P' \<leadsto>\<^sup>* s P'' \<Longrightarrow> P \<leadsto>\<^sup>* (ev e) # s P''\<close>


lemma trace_trans_\<tau>_trans: \<open>P \<leadsto>\<^sup>*s P' \<Longrightarrow> P' \<leadsto>\<^sub>\<tau> P'' \<Longrightarrow> P \<leadsto>\<^sup>*s P''\<close>
  apply (induct rule: trace_trans.induct)
  subgoal using \<tau>_trans_transitivity trace_\<tau>_trans by blast
  subgoal using event_trans_\<tau>_trans trace_tick_trans by blast
  using trace_Cons_ev_trans by blast
  

lemma \<tau>_trans_trace_trans:  \<open>P \<leadsto>\<^sub>\<tau> P' \<Longrightarrow> P' \<leadsto>\<^sup>*s P'' \<Longrightarrow> P \<leadsto>\<^sup>*s P''\<close>
  apply (rotate_tac, induct rule: trace_trans.induct)
  subgoal using \<tau>_trans_transitivity trace_\<tau>_trans by blast
  subgoal using \<tau>_trans_event_trans trace_tick_trans by blast
  using \<tau>_trans_event_trans trace_Cons_ev_trans by blast


lemma tickFree_if_trans_trans_not_STOP : 
  \<open>P \<leadsto>\<^sup>*s Q \<Longrightarrow> Q \<noteq> STOP \<Longrightarrow> tickFree s\<close>
  by (induct rule: trace_trans.induct, simp_all)
     (metis \<tau>_trans_anti_mono_ready_set bot.extremum_uniqueI 
            ready_set_AfterExt ready_set_empty_iff_STOP)


lemma BOT_trace_trans_tickFree_anything : \<open>tickFree s \<Longrightarrow> \<bottom> \<leadsto>\<^sup>*s P\<close>
proof (induct s arbitrary: P)
  show \<open>\<And>P. tickFree [] \<Longrightarrow> \<bottom> \<leadsto>\<^sup>*[] P\<close>
    by (simp add: BOT_\<tau>_trans_anything trace_\<tau>_trans)
next
  fix e s P
  assume prem: \<open>tickFree (e # s)\<close> and hyp: \<open>tickFree s \<Longrightarrow> \<bottom> \<leadsto>\<^sup>*s P\<close> for P
  have * : \<open>tickFree s\<close> using prem by auto
  obtain e' where \<open>e = ev e'\<close> using event.exhaust prem by auto
  thus \<open>\<bottom> \<leadsto>\<^sup>*e # s P\<close>
    by simp (rule trace_Cons_ev_trans[OF _ hyp];
             simp add: * AfterExt_BOT BOT_\<tau>_trans_anything ready_set_BOT)
qed


section\<open>Consequences of \<^term>\<open>P \<leadsto>\<^sup>*s Q\<close> on \<^term>\<open>\<F>\<close>, \<^term>\<open>\<T>\<close> and \<^term>\<open>\<D>\<close>\<close>
  
lemma trace_trans_imp_F_if_\<tau>_trans_imp_leF: 
  \<open>P \<leadsto>\<^sup>*s Q \<Longrightarrow> X \<in> \<R> Q \<Longrightarrow> (s, X) \<in> \<F> P\<close>
  if \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>F Q\<close>
proof (induct rule: trace_trans.induct)
  show \<open>P \<leadsto>\<^sub>\<tau> Q \<Longrightarrow> X \<in> \<R> Q \<Longrightarrow> ([], X) \<in> \<F> P\<close> for P Q
    by (meson failure_refine_def in_mono Refusals_iff that)
next
  show \<open>P \<leadsto>\<checkmark> Q \<Longrightarrow> X \<in> \<R> Q \<Longrightarrow> ([\<checkmark>], X) \<in> \<F> P\<close> for P Q
    by (metis append_Nil mem_Collect_eq ready_set_def tick_T_F)
next
  fix P e Q s Q'
  assume * : \<open>P \<leadsto>(ev e) Q\<close> \<open>X \<in> \<R> Q' \<Longrightarrow> (s, X) \<in> \<F> Q\<close> \<open>X \<in> \<R> Q'\<close>
  have \<open>P afterExt ev e \<sqsubseteq>\<^sub>F Q\<close> using *(1) that by blast
  hence \<open>(s, X) \<in> \<F> (P afterExt ev e)\<close> by (simp add: failure_refine_def subsetD *(2, 3))
  thus \<open>(ev e # s, X) \<in> \<F> P\<close> by (simp add: F_AfterExt *(1)) (metis list.exhaust_sel)
qed


lemma trace_trans_imp_T_if_\<tau>_trans_imp_leT: \<open>P \<leadsto>\<^sup>*s Q \<Longrightarrow> s \<in> \<T> P\<close> 
  if \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>T Q\<close>
proof (induct rule: trace_trans.induct)
  show \<open>P \<leadsto>\<^sub>\<tau> Q \<Longrightarrow> [] \<in> \<T> P\<close> for P Q
    by (simp add: Nil_elem_T)
next
  show \<open>P \<leadsto>\<checkmark> Q \<Longrightarrow> [\<checkmark>] \<in> \<T> P\<close> for P Q
    by (simp add: ready_set_def)
next
  fix P e Q s Q'
  assume * : \<open>P \<leadsto>(ev e) Q\<close> \<open>s \<in> \<T> Q\<close>
  have \<open>P afterExt ev e \<sqsubseteq>\<^sub>T Q\<close> using *(1) that by blast
  hence \<open>s \<in> \<T> (P afterExt ev e)\<close> by (simp add: *(2) subsetD trace_refine_def)
  with *(1) list.collapse show \<open>ev e # s \<in> \<T> P\<close> 
    by (force simp add: T_AfterExt ready_set_def)
qed


lemma trace_trans_BOT_imp_D_if_\<tau>_trans_imp_leD: \<open>P \<leadsto>\<^sup>*s \<bottom> \<Longrightarrow> s \<in> \<D> P\<close> 
  if \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>D Q\<close>
proof (induct s arbitrary: P)
  show \<open>\<And>P. P \<leadsto>\<^sup>*[] \<bottom> \<Longrightarrow> [] \<in> \<D> P\<close>
    by (subst (asm) trace_trans.simps, auto) 
       (meson BOT_iff_D divergence_refine_def subsetD that)
next
  fix e s P
  assume prem : \<open>P \<leadsto>\<^sup>*e # s \<bottom>\<close> 
  assume hyp: \<open>P \<leadsto>\<^sup>*s \<bottom> \<Longrightarrow> s \<in> \<D> P\<close> for P
  have \<open>P afterExt e \<leadsto>\<^sup>*s \<bottom>\<close>
    using prem by (cases rule: trace_trans.cases)
                  (auto simp add:  trace_\<tau>_trans intro: \<tau>_trans_trace_trans)
  from hyp[OF this] show \<open>e # s \<in> \<D> P\<close>
    by (auto simp add: D_AfterExt D_UU split: if_split_asm)
qed



section\<open>Characterizations for \<^term>\<open>P \<leadsto>\<^sup>*s Q\<close>\<close>

text \<open>The following results require a lot of work, but will be very useful.\<close>

lemma trace_trans_iff :
  \<open>P \<leadsto>\<^sup>* [] Q \<longleftrightarrow> P \<leadsto>\<^sub>\<tau> Q\<close>
  \<open>P \<leadsto>\<^sup>* [\<checkmark>] Q \<longleftrightarrow> P \<leadsto>\<checkmark> Q\<close>
  \<open>P \<leadsto>\<^sup>* (ev e) # s Q' \<longleftrightarrow> (\<exists>Q. P \<leadsto>(ev e) Q \<and> Q \<leadsto>\<^sup>* s Q')\<close>
  \<open>tickFree s \<Longrightarrow> (P \<leadsto>\<^sup>* s @ [f] Q') \<longleftrightarrow> (\<exists>Q. P \<leadsto>\<^sup>*s Q \<and> Q \<leadsto>f Q')\<close>
  \<open>front_tickFree (s @ t) \<Longrightarrow> (P \<leadsto>\<^sup>*s @ t Q') \<longleftrightarrow> (\<exists>Q. P \<leadsto>\<^sup>*s Q \<and> Q \<leadsto>\<^sup>*t Q')\<close>
proof -
  show f1 : \<open>\<And>P Q. P \<leadsto>\<^sup>* [] Q \<longleftrightarrow> P \<leadsto>\<^sub>\<tau> Q\<close>
   and f2 : \<open>\<And>P Q. P \<leadsto>\<^sup>* [\<checkmark>] Q \<longleftrightarrow> P \<leadsto>\<checkmark>  Q\<close>
   and f3 : \<open>\<And>P Q' e. P \<leadsto>\<^sup>* (ev e) # s Q' \<longleftrightarrow> (\<exists>Q. P \<leadsto>(ev e) Q \<and> Q \<leadsto>\<^sup>* s Q')\<close>
    by ((subst trace_trans.simps, auto)[1])+
   
  show f4 : \<open>tickFree s \<Longrightarrow> (P \<leadsto>\<^sup>* s @ [f] Q') \<longleftrightarrow> (\<exists>Q. P \<leadsto>\<^sup>*s Q \<and> Q \<leadsto>f Q')\<close> for s f P Q'
  proof safe
    show \<open>P \<leadsto>\<^sup>* s @ [f] Q' \<Longrightarrow> \<exists>Q. P \<leadsto>\<^sup>*s Q \<and> Q \<leadsto>f Q'\<close>
    proof (induct s arbitrary: P)
      case Nil
      thus ?case 
        apply (subst (asm) trace_trans.simps, simp)
        using \<tau>_trans_eq \<tau>_trans_transitivity f1 by blast
    next
      case (Cons e s)
      from Cons.prems have * : \<open>e \<in> ready_set P \<and> P afterExt e \<leadsto>\<^sup>*s @ [f] Q'\<close>
        by (subst (asm) trace_trans.simps)
           (auto simp add:  intro: \<tau>_trans_trace_trans)
      with Cons.hyps obtain Q where ** : \<open>P afterExt e \<leadsto>\<^sup>*s Q\<close> \<open>Q \<leadsto>f Q'\<close> by blast
      have \<open>P \<leadsto>\<^sup>*e # s Q\<close>
      proof (cases e)
        fix e'
        assume \<open>e = ev e'\<close>
        thus \<open>P \<leadsto>\<^sup>*e # s Q\<close>
          apply simp
          by (rule trace_Cons_ev_trans[OF _ **(1)]) (use * \<tau>_trans_eq in blast)
      next
        from Cons.prems have \<open>e = \<checkmark> \<Longrightarrow> s = []\<close> by (subst (asm) trace_trans.simps) auto
        thus \<open>e = \<checkmark> \<Longrightarrow> P \<leadsto>\<^sup>*e # s Q\<close> using * **(1) f1 f2 by blast
      qed
      with "**"(2) show \<open>\<exists>Q. P \<leadsto>\<^sup>*e # s Q \<and> Q \<leadsto>f Q'\<close> by blast
    qed
  next
    show \<open>tickFree s \<Longrightarrow> P \<leadsto>\<^sup>*s Q \<Longrightarrow> f \<in> ready_set Q \<Longrightarrow> Q afterExt f \<leadsto>\<^sub>\<tau> Q' \<Longrightarrow>
          P \<leadsto>\<^sup>*s @ [f] Q'\<close> for Q
    proof (induct s arbitrary: P Q)
      show \<open>tickFree [] \<Longrightarrow> P \<leadsto>\<^sup>*[] Q \<Longrightarrow> f \<in> ready_set Q \<Longrightarrow> Q afterExt f \<leadsto>\<^sub>\<tau> Q' \<Longrightarrow> 
            P \<leadsto>\<^sup>*[] @ [f] Q'\<close> for P Q
        by (simp add: f1)
           (metis (full_types) \<tau>_trans_eq \<tau>_trans_event_trans event.exhaust 
                               trace_Cons_ev_trans trace_\<tau>_trans trace_tick_trans)
    next
      case (Cons e s)
      from Cons.prems(2) have * : \<open>e \<in> ready_set P \<and> P afterExt e \<leadsto>\<^sup>*s Q\<close>
        by (subst (asm) trace_trans.simps)
           (auto simp add: f1 intro: \<tau>_trans_trace_trans)
      show ?case
      proof (cases e)
        fix e'
        assume \<open>e = ev e'\<close>
        thus \<open>P \<leadsto>\<^sup>*(e # s) @ [f] Q'\<close> 
          apply simp
          by (rule trace_Cons_ev_trans
                   [OF _ Cons.hyps[OF tickFree_tl[OF Cons.prems(1), simplified] 
                                      *[THEN conjunct2] Cons.prems(3)]])
             (use * \<tau>_trans_eq Cons.prems(4) in \<open>blast+\<close>)
      next
        show \<open>e = \<checkmark> \<Longrightarrow> P \<leadsto>\<^sup>*(e # s) @ [f] Q'\<close> using Cons.prems(1) by auto
      qed
    qed
  qed

  show \<open>front_tickFree (s @ t) \<Longrightarrow> P \<leadsto>\<^sup>*s @ t Q' \<longleftrightarrow> (\<exists>Q. P \<leadsto>\<^sup>*s Q \<and> Q \<leadsto>\<^sup>*t Q')\<close>
  proof (induct t arbitrary: Q' rule: rev_induct)
    show \<open>P \<leadsto>\<^sup>*s @ [] Q' \<longleftrightarrow> (\<exists>Q. P \<leadsto>\<^sup>*s Q \<and> Q \<leadsto>\<^sup>*[] Q')\<close> for Q'
      by (metis \<tau>_trans_eq append.right_neutral trace_trans_\<tau>_trans f1)
  next
    case (snoc e t)
    show \<open>P \<leadsto>\<^sup>*s @ t @ [e] Q' \<longleftrightarrow> (\<exists>Q. P \<leadsto>\<^sup>*s Q \<and> Q \<leadsto>\<^sup>*t @ [e] Q')\<close>
    proof (intro iffI)
      assume assm : \<open>P \<leadsto>\<^sup>*s @ t @ [e] Q'\<close>
      from assm obtain Q where \<open>P \<leadsto>\<^sup>*s @ t Q\<close> \<open>Q \<leadsto>e Q'\<close>
        by (metis append.assoc f4 front_tickFree_implies_tickFree snoc.prems)
      also obtain R where ** : \<open>P \<leadsto>\<^sup>*s R\<close> \<open>R \<leadsto>\<^sup>*t Q\<close>
        by (metis calculation(1) append.assoc front_tickFree_dw_closed snoc.hyps snoc.prems)
      ultimately show \<open>\<exists>Q. P \<leadsto>\<^sup>*s Q \<and> Q \<leadsto>\<^sup>*t @ [e] Q'\<close>
        by (metis append_is_Nil_conv f4 front_tickFree_mono list.distinct(1) snoc.prems)
    next
      assume \<open>\<exists>Q. P \<leadsto>\<^sup>*s Q \<and> Q \<leadsto>\<^sup>*t @ [e] Q'\<close>
      then obtain Q where \<open>P \<leadsto>\<^sup>*s Q\<close> \<open>Q \<leadsto>\<^sup>*t @ [e] Q'\<close> by blast
      also obtain R where \<open>Q \<leadsto>\<^sup>*t R\<close> \<open>R \<leadsto>e Q'\<close>
        by (metis append_is_Nil_conv calculation(2) f4
                  front_tickFree_mono list.distinct(1) snoc.prems)
      ultimately show \<open>P \<leadsto>\<^sup>*s @ t @ [e] Q'\<close>
        by (metis append_assoc f4 front_tickFree_implies_tickFree snoc.hyps
                  snoc.prems tickFree_implies_front_tickFree)
    qed
  qed
qed



section\<open>Finally: \<^term>\<open>P \<leadsto>\<^sup>*s Q\<close> is \<^term>\<open>P afterTrace s \<leadsto>\<^sub>\<tau> Q\<close>\<close>

theorem T_imp_trace_trans_iff_AfterTrace_\<tau>_trans : 
  \<open>s \<in> \<T> P \<Longrightarrow> (P \<leadsto>\<^sup>*s Q) \<longleftrightarrow> P afterTrace s \<leadsto>\<^sub>\<tau> Q\<close>
proof (intro iffI)
  show \<open>P \<leadsto>\<^sup>*s Q \<Longrightarrow> s \<in> \<T> P \<Longrightarrow> P afterTrace s \<leadsto>\<^sub>\<tau> Q\<close>
  proof (induct s arbitrary: P Q rule: rev_induct)
    show \<open>\<And>P Q. P \<leadsto>\<^sup>*[] Q \<Longrightarrow> [] \<in> \<T> P \<Longrightarrow> P afterTrace [] \<leadsto>\<^sub>\<tau> Q\<close>
      using trace_trans.cases by auto
  next
    fix s e P Q
    assume   hyp : \<open>P \<leadsto>\<^sup>*s Q \<Longrightarrow> s \<in> \<T> P \<Longrightarrow> P afterTrace s \<leadsto>\<^sub>\<tau> Q\<close> for P Q
    assume prems : \<open>P \<leadsto>\<^sup>*s @ [e] Q\<close> \<open>s @ [e] \<in> \<T> P\<close>
    have * : \<open>e \<in> ready_set (P afterTrace s)\<close> 
      using prems(2) ready_set_AfterTrace by blast
    show \<open>P afterTrace (s @ [e]) \<leadsto>\<^sub>\<tau> Q\<close>
      by (metis AfterTrace_snoc \<tau>_trans_event_trans append_single_T_imp_tickFree 
                hyp is_processT3_ST prems trace_trans_iff(4))
  qed
next
  show \<open>P afterTrace s \<leadsto>\<^sub>\<tau> Q \<Longrightarrow> s \<in> \<T> P \<Longrightarrow> P \<leadsto>\<^sup>*s Q\<close>
  proof (induct arbitrary: P Q rule: AfterTrace.induct)
    show \<open>\<And>P Q. P afterTrace [] \<leadsto>\<^sub>\<tau> Q \<Longrightarrow> [] \<in> \<T> P \<Longrightarrow> P \<leadsto>\<^sup>*[] Q\<close>
      by (simp add: trace_\<tau>_trans)
  next
    fix e and s :: \<open>'\<alpha> trace\<close> and Q P
    assume   hyp : \<open>P afterTrace s \<leadsto>\<^sub>\<tau> Q \<Longrightarrow> s \<in> \<T> P \<Longrightarrow> P \<leadsto>\<^sup>*s Q\<close> for P Q
    assume prems : \<open>P afterTrace (e # s) \<leadsto>\<^sub>\<tau> Q\<close> \<open>e # s \<in> \<T> P\<close>
    have * : \<open>e \<in> ready_set P \<and> s \<in> \<T> (P afterExt e)\<close>
      by (metis AfterTrace.simps(1, 2) Cons_in_T_imp_elem_ready_set 
                T_AfterTrace append_Cons append_Nil prems(2))
    show \<open>P \<leadsto>\<^sup>*e # s Q\<close>
    proof (cases e)
      fix e'
      assume ** : \<open>e = ev e'\<close>
      from * ** have \<open>P \<leadsto>(ev e') P afterExt (ev e')\<close>
        by (simp add: \<tau>_trans_eq)
      thus \<open>P \<leadsto>\<^sup>*e # s Q\<close>
        by (subst **, rule trace_Cons_ev_trans[OF _ hyp[OF prems(1)[simplified] 
                                                        *[THEN conjunct2], simplified **]])
    next
      have \<open>e = \<checkmark> \<Longrightarrow> s = []\<close> by (metis butlast.simps(2) front_tickFree_butlast 
                                        is_processT2_TR tickFree_Cons prems(2))
      thus \<open>e = \<checkmark> \<Longrightarrow> P \<leadsto>\<^sup>*e # s Q\<close> 
        using * prems(1) trace_tick_trans by force
    qed
  qed
qed


text \<open>As corollaries we obtain the reciprocal results of 

      @{thm trace_trans_imp_F_if_\<tau>_trans_imp_leF
            trace_trans_imp_T_if_\<tau>_trans_imp_leT
            trace_trans_BOT_imp_D_if_\<tau>_trans_imp_leD}\<close>

lemma F_imp_exists_trace_trans: \<open>(s, X) \<in> \<F> P \<Longrightarrow> \<exists>Q. (P \<leadsto>\<^sup>*s Q) \<and> X \<in> \<R> Q\<close>
  by (meson F_T F_imp_refusal_AfterTrace Refusals_iff
            T_imp_trace_trans_iff_AfterTrace_\<tau>_trans \<tau>_trans_eq)

lemma T_imp_exists_trace_trans: \<open>s \<in> \<T> P \<Longrightarrow> \<exists>Q. P \<leadsto>\<^sup>*s Q\<close>
  using F_imp_exists_trace_trans T_F by blast

lemma D_imp_trace_trans_BOT: \<open>tickFree s \<Longrightarrow> s \<in> \<D> P \<Longrightarrow> P \<leadsto>\<^sup>*s \<bottom>\<close>
  by (simp add: D_T D_imp_AfterTrace_is_BOT 
                T_imp_trace_trans_iff_AfterTrace_\<tau>_trans \<tau>_trans_eq)
 



text \<open>When we have more information on \<^term>\<open>P \<leadsto>\<^sub>\<tau> Q\<close>, we obtain:\<close>

lemma \<tau>_trans_imp_leT_imp_STOP_trace_trans_iff: 
  \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> STOP \<leadsto>\<^sup>*s P \<longleftrightarrow> s = [] \<and> P = STOP\<close>
  using STOP_T_iff by (subst trace_trans.simps)
                      (auto simp add: ready_set_STOP \<tau>_trans_eq) 


lemma \<tau>_trans_imp_leF_imp_SKIP_trace_trans_iff: 
  \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>F Q \<Longrightarrow>
   SKIP \<leadsto>\<^sup>*s P \<longleftrightarrow> s = [] \<and> P = SKIP \<or> s = [\<checkmark>] \<and> P = STOP\<close>
  using SKIP_F_iff STOP_F_iff by (subst trace_trans.simps)
                                 (auto simp add: AfterExt_SKIP ready_set_SKIP \<tau>_trans_eq)
  
  
lemma \<tau>_trans_imp_leT_imp_trace_trans_ready_set_subset_ready_set_AfterTrace:
  \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> P \<leadsto>\<^sup>*s Q \<Longrightarrow>
   ready_set Q \<subseteq> ready_set (P afterTrace s)\<close>
  using T_imp_trace_trans_iff_AfterTrace_\<tau>_trans 
        anti_mono_ready_set_T trace_trans_imp_T_if_\<tau>_trans_imp_leT by blast


lemma \<tau>_trans_imp_leT_imp_trace_trans_imp_ready_set:
  \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> P \<leadsto>\<^sup>*(s @ e # t) Q \<Longrightarrow>
   e \<in> ready_set (P afterTrace s)\<close>
  using ready_set_AfterTrace trace_trans_imp_T_if_\<tau>_trans_imp_leT by blast


lemma trace_trans_iff_T_and_AfterTrace_\<tau>_trans_if_\<tau>_trans_imp_leT: 
  \<open>\<forall>P Q. P \<leadsto>\<^sub>\<tau> Q \<longrightarrow> P \<sqsubseteq>\<^sub>T Q \<Longrightarrow>
   (P \<leadsto>\<^sup>*s Q) \<longleftrightarrow> s \<in> \<T> P \<and> P afterTrace s \<leadsto>\<^sub>\<tau> Q\<close>
  using T_imp_trace_trans_iff_AfterTrace_\<tau>_trans trace_trans_imp_T_if_\<tau>_trans_imp_leT by blast
  


section\<open>General Rules of Operational Semantics\<close>

text \<open>Some rules of operational semantics are consequences of \<^locale>\<open>OpSemGeneric\<close>'s
      axioms without needing to specify more what \<^term>\<open>P \<leadsto>\<^sub>\<tau> Q\<close> is.\<close>

lemma SKIP_trans_tick: \<open>SKIP \<leadsto>\<checkmark> STOP\<close>
  by (simp add: AfterExt_SKIP \<tau>_trans_eq ready_set_SKIP)

lemma tick_trans_imp_BOT_L_or_STOP_R: \<open>P \<leadsto>\<checkmark> Q \<Longrightarrow> P = \<bottom> \<or> Q = STOP\<close>
  by (metis \<tau>_trans_anti_mono_ready_set ready_set_AfterExt ready_set_empty_iff_STOP subset_empty)

lemma STOP_trace_trans_iff : \<open>STOP \<leadsto>\<^sup>*s P \<longleftrightarrow> s = [] \<and> P = STOP\<close>
  by (metis AfterExt_SKIP SKIP_neq_BOT SKIP_trans_tick empty_iff trace_trans.cases
            ready_set_STOP tick_trans_imp_BOT_L_or_STOP_R trace_trans_iff(1))



lemma ready_tick_imp_\<tau>_trans_SKIP: \<open>P \<leadsto>\<^sub>\<tau> SKIP\<close> if \<open>\<checkmark> \<in> ready_set P\<close>
proof -
  from that have \<open>P \<sqsubseteq>\<^sub>F\<^sub>D SKIP\<close>
    unfolding failure_divergence_refine_def le_ref_def
    by (auto simp add: F_SKIP D_SKIP subset_iff ready_set_def is_processT6_S2)
       (metis append_Nil tick_T_F)
  then obtain Q where \<open>P = Q \<sqinter> SKIP\<close>
    by (metis mono_Ndet_FD mono_Ndet_FD_left FD_antisym Ndet_id idem_FD)
  thus \<open>P \<leadsto>\<^sub>\<tau> SKIP\<close> by (simp add: \<tau>_trans_NdetR)
qed
 

lemma exists_tick_trans_is_ready_tick: \<open>(\<exists>P'. P \<leadsto>\<checkmark> P') \<longleftrightarrow> \<checkmark> \<in> ready_set P\<close>
  using \<tau>_trans_eq by blast



lemma tick_trans_iff : \<open>P \<leadsto>\<checkmark> P' \<longleftrightarrow> P \<leadsto>\<^sub>\<tau> SKIP \<and> P' = STOP\<close>
  by (metis AfterExt_BOT AfterExt_SKIP SKIP_neq_BOT SKIP_trans_tick 
            \<tau>_trans_event_trans ready_tick_imp_\<tau>_trans_SKIP tick_trans_imp_BOT_L_or_STOP_R)
 

lemma SKIP_cant_ev_trans: \<open>\<not> SKIP \<leadsto>(ev e) STOP\<close>
  by (simp add: ready_set_SKIP)

lemma STOP_cant_event_trans: \<open>\<not> STOP \<leadsto>e P\<close>
  by (simp add: ready_set_STOP)




lemma ev_trans_Mprefix: \<open>e \<in> A \<Longrightarrow> \<box>a \<in> A \<rightarrow> P a \<leadsto>(ev e) (P e)\<close>
  by (simp add: AfterExt_def After_Mprefix \<tau>_trans_eq ready_set_Mprefix)

lemma ev_trans_Mndetprefix: \<open>e \<in> A \<Longrightarrow> \<sqinter>a \<in> A \<rightarrow> P a \<leadsto>(ev e) (P e)\<close>
  by (simp add: AfterExt_def After_Mndetprefix \<tau>_trans_eq ready_set_Mndetprefix)

lemma ev_trans_prefix: \<open>e \<rightarrow> P \<leadsto> (ev e) P\<close>
  by (metis ev_trans_Mprefix insertI1 write0_def)



lemma \<tau>_trans_MultiNdet: \<open>finite A \<Longrightarrow> x \<in> A \<Longrightarrow> (\<Sqinter>a \<in> A. P a) \<leadsto>\<^sub>\<tau> P x\<close>
  by (metis MultiNdet_insert' \<tau>_trans_NdetL emptyE insert_absorb)

lemma \<tau>_trans_GlobalNdet: \<open>(\<sqinter>a \<in> A. P a) \<leadsto>\<^sub>\<tau> P e\<close> if \<open>e \<in> A\<close>
proof -
  have \<open>(\<sqinter>a \<in> A. P a) = P e \<sqinter> (\<sqinter>a \<in> A. P a)\<close>
    by (metis GlobalNdet_factorization_union GlobalNdet_unit
              empty_iff insertI1 insert_absorb insert_is_Un that)
  thus \<open>(\<sqinter>a \<in> A. P a) \<leadsto>\<^sub>\<tau> P e\<close> by (metis \<tau>_trans_NdetL)
qed
  


lemma fix_point_\<tau>_trans: \<open>cont f \<Longrightarrow> P = (\<mu> X. f X) \<Longrightarrow> P \<leadsto>\<^sub>\<tau> f P\<close>
  by (metis \<tau>_trans_eq cont_process_rec)


lemma event_trans_DetL: \<open>P \<leadsto>e P' \<Longrightarrow> P \<box> Q \<leadsto>e P'\<close>
  by (metis AfterExt_Det_is_AfterExt_Ndet Un_iff \<tau>_trans_NdetL \<tau>_trans_event_trans ready_set_Det)
 
lemma event_trans_DetR: \<open>Q \<leadsto>e Q' \<Longrightarrow> P \<box> Q \<leadsto>e Q'\<close>
  by (metis Det_commute event_trans_DetL)

lemma event_trans_MultiDet:
  \<open>finite A \<Longrightarrow> a \<in> A \<Longrightarrow> P a \<leadsto>e Q \<Longrightarrow> (\<^bold>\<box>a \<in> A. P a) \<leadsto>e Q\<close>
  by (metis MultiDet_insert' event_trans_DetL insert_absorb)


 
lemma Sliding_event_transL: \<open>P \<leadsto>e P' \<Longrightarrow> P \<rhd> Q \<leadsto>e P'\<close>
  unfolding Sliding_def
  apply (drule event_trans_DetL[of e P P' Q])
  using \<tau>_trans_NdetL \<tau>_trans_event_trans by blast


lemma Sliding_\<tau>_transR: \<open>P \<rhd> Q \<leadsto>\<^sub>\<tau> Q\<close>
  unfolding Sliding_def by (simp add: \<tau>_trans_NdetR)



lemma \<open>\<exists>P P' Q. P \<leadsto>\<checkmark> P' \<and> \<not> P \<^bold>; Q \<leadsto>\<checkmark> P' \<^bold>; Q\<close>
  by (metis SKIP_Seq SKIP_trans_tick STOP_cant_event_trans)



lemma ev_trans_SeqR:
  \<open>\<checkmark> \<in> ready_set P \<Longrightarrow> Q \<leadsto>(ev e) Q' \<Longrightarrow> P \<^bold>; Q \<leadsto>(ev e) Q'\<close>
  by (simp add: AfterExt_Seq ready_set_Seq AfterExt_BOT BOT_Seq)
     (metis Ndet_commute \<tau>_trans_NdetL \<tau>_trans_transitivity)
  
 


lemma \<open>SKIP \<lbrakk>S\<rbrakk> SKIP \<leadsto>\<checkmark> STOP\<close>
  by (simp add: SKIP_trans_tick Sync_SKIP_SKIP)

lemma \<open>SKIP \<lbrakk>S\<rbrakk> SKIP \<leadsto>\<^sub>\<tau> SKIP\<close>
  by (simp add: Sync_SKIP_SKIP \<tau>_trans_eq)


lemma tick_trans_Hiding: \<open>P \ B \<leadsto>\<checkmark> STOP\<close> if \<open>P \<leadsto>\<checkmark> P'\<close>
proof -
  have \<open>(P \ B) afterExt \<checkmark> = STOP \<sqinter> (P \ B) afterExt \<checkmark>\<close>
    by (simp add: AfterExt_def)
  thus \<open>P \ B \<leadsto>\<checkmark> STOP\<close> 
    by (simp add: AfterExt_def \<tau>_trans_eq ready_tick_imp_ready_tick_Hiding that)
qed



text \<open>The following lemma is useless since the locale mechanism forces
      \<^term>\<open>f\<close> to be of type \<^typ>\<open>'\<alpha> \<Rightarrow> '\<alpha>\<close> while it could be \<^typ>\<open>'\<alpha> \<Rightarrow> '\<beta>\<close>. 
      We will have to prove it again on each instantiation.\<close>

lemma \<open>Renaming P f \<leadsto>\<checkmark> STOP\<close> if \<open>P \<leadsto>\<checkmark> P'\<close>
proof -
  have \<open>Renaming P f afterExt \<checkmark> = STOP \<sqinter> Renaming P f afterExt \<checkmark>\<close>
    by (metis \<tau>_trans_eq not_ready_AfterExt tick_trans_iff)
  thus \<open>Renaming P f \<leadsto>\<checkmark> STOP\<close>
    by (simp add: that tick_eq_EvExt AfterExt_def \<tau>_trans_eq
                  ready_set_Renaming BOT_\<tau>_trans_anything)
qed



end

end