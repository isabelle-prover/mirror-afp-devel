(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : HOL-CSP_OpSem - Operational semantics for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Burkhart Wolff
 *
 * This file       : The After operator
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

chapter \<open> Construction of the After Operator \<close>

theory  After
  imports ReadySet
begin


text \<open>Now that we have defined \<^term>\<open>ready_set P\<close>, we can talk about what
      happens to \<^term>\<open>P\<close> after an event belonging to this set.\<close>

section \<open>Definition\<close>

text \<open>We want to define a new operator on a process \<^term>\<open>P\<close> which would in
      some way be the reciprocal of the prefix operator \<^term>\<open>e \<rightarrow> P\<close>.\<close>

text \<open>The intuitive way of doing so is to only keep the tails of the traces
      beginning by \<^term>\<open>ev e\<close> (and similar for failures and divergences).
      However we have an issue if \<^term>\<open>ev e \<notin> ready_set P\<close> i.e. if no trace of
      \<^term>\<open>P\<close> begins with \<^term>\<open>ev e\<close>: the result would no longer verify the 
      invariant \<^const>\<open>is_process\<close> because its trace set would be empty.
      We must therefore distinguish this case and we agree to then obtain \<^const>\<open>STOP\<close>.
      This convention is not really decisive since we will only use this operator
      when \<^term>\<open>ev e \<in> ready_set P\<close> to define operational semantics.\<close>


lift_definition After :: \<open>['\<alpha> process, '\<alpha>] \<Rightarrow> '\<alpha> process\<close> (infixl \<open>after\<close> 77)
  is \<open>\<lambda>P e.   if ev e \<in> ready_set P
            then ({(tl s, X)| s X. (s, X) \<in> \<F> P \<and> s \<noteq> [] \<and> hd s = ev e},
                  { tl s    | s  .  s     \<in> \<D> P \<and> s \<noteq> [] \<and> hd s = ev e})
            else ({(s, X). s = []}, {})\<close>
proof -
  show \<open>?thesis P e\<close> (is \<open>is_process (if ev e \<in> ready_set P then (?f, ?d) 
                                      else ({(s, X). s = []}, {}))\<close>) for P e
  proof (split if_split, intro conjI impI)
    show \<open>is_process ({(s, X). s = []}, {})\<close> (* by (metis STOP.rsp eq_onp_def) *)
      by (simp add: is_process_REP_STOP)
  next
    assume ready: \<open>ev e \<in> ready_set P\<close>
    show \<open>is_process (?f, ?d)\<close>
      unfolding is_process_def FAILURES_def DIVERGENCES_def fst_conv snd_conv
    proof (intro conjI impI allI)
      show \<open>([], {}) \<in> ?f\<close>
        using ready[unfolded ready_set_def T_F_spec[symmetric]] by force
    next
      show \<open>(s, X) \<in> ?f \<Longrightarrow> front_tickFree s\<close> for s X
        by simp (metis butlast_rev butlast_tl front_tickFree_def is_processT2 tickFree_butlast)
    next
      show \<open>(s @ t, {}) \<in> ?f \<Longrightarrow> (s, {}) \<in> ?f\<close> for s t
        by simp (metis (no_types, opaque_lifting) append_Cons is_processT3 
                                                  list.sel(1, 3) neq_Nil_conv)
    next
      show \<open>(s, Y) \<in> ?f \<and> X \<subseteq> Y \<Longrightarrow> (s, X) \<in> ?f\<close> for s X Y
        using is_processT4 by simp blast
    next
      show \<open>(s, X) \<in> ?f \<and> (\<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> ?f) \<Longrightarrow> (s, X \<union> Y) \<in> ?f\<close> for s X Y
        using ready[unfolded ready_set_def T_F_spec[symmetric]]
        by auto (metis Nil_is_append_conv hd_append2 is_processT5 tl_append2)
    next
      show \<open>(s @ [\<checkmark>], {}) \<in> ?f \<Longrightarrow> (s, X - {\<checkmark>}) \<in> ?f\<close> for s X
        by simp (metis (no_types, lifting) Cons_eq_appendI is_processT6 list.collapse 
                                           list.distinct(1) list.sel(1, 3))
    next
      fix s t :: \<open>'\<alpha> trace\<close>
      assume \<open>s \<in> ?d \<and> tickFree s \<and> front_tickFree t\<close>
      hence \<open>s @ t = tl (ev e # s @ t) \<and> ev e # s @ t \<in> \<D> P \<and> 
             ev e # s @ t \<noteq> [] \<and> hd (ev e # s @ t) = ev e\<close>
        by simp (metis append_Cons event.distinct(1) is_processT7_S
                       list.sel(1, 3) neq_Nil_conv tickFree_Cons)
      show \<open>s @ t \<in> ?d\<close>
        apply simp 
        using \<open>?this\<close> by blast
    next
      show \<open>s \<in> ?d \<Longrightarrow> (s, X) \<in> ?f\<close> for s X
        using NF_ND by blast
    next
      show \<open>s @ [\<checkmark>] \<in> ?d \<Longrightarrow> s \<in> ?d\<close> for s
        by auto (metis Cons_eq_appendI is_processT9_S_swap list.sel(1, 3) neq_Nil_conv)
    qed
  qed
qed




section \<open>Projections\<close>

lemma F_After:
  \<open>\<F> (P after e) = (   if ev e \<in> ready_set P
                     then {(tl s, X)| s X. (s, X) \<in> \<F> P \<and> s \<noteq> [] \<and> hd s = ev e}
                     else {(s, X). s = []})\<close>
  by (simp add: Failures_def After.rep_eq FAILURES_def)
  (* by (simp add: Failures.rep_eq After.rep_eq FAILURES_def) *)

lemma D_After:
  \<open>\<D> (P after e) = (   if ev e \<in> ready_set P
                     then {tl s| s. s \<in> \<D> P \<and> s \<noteq> [] \<and> hd s = ev e}
                     else {})\<close> 
  by (simp add: Divergences_def After.rep_eq DIVERGENCES_def)
  (* by (simp add: Divergences.rep_eq After.rep_eq DIVERGENCES_def) *)


lemma T_After:
  \<open>\<T> (P after e) = (   if ev e \<in> ready_set P
                     then {tl s| s. s \<in> \<T> P \<and> s \<noteq> [] \<and> hd s = ev e}
                     else {[]})\<close>
  by (auto simp add: T_F_spec[symmetric] F_After)


lemma not_ready_After: \<open>ev e \<notin> ready_set P \<Longrightarrow> P after e = STOP\<close>
  by (simp add: STOP_iff_T T_After)

lemma ready_set_After: \<open>ready_set (P after e) = {a. ev e # [a] \<in> \<T> P}\<close>
  apply (simp add: T_After ready_set_def, safe)
    apply (metis list.exhaust_sel)
   apply (metis list.discI list.sel(1, 3))
  by (simp add: is_processT3_ST_pref le_list_def)



section \<open>Monotony\<close>

lemma mono_After : \<open>P after e \<sqsubseteq> Q after e\<close> if \<open>P \<sqsubseteq> Q\<close>
proof (subst le_approx_def, safe)
  from that[THEN anti_mono_ready_set] that[THEN le_approx1]
  show \<open>s \<in> \<D> (Q after e) \<Longrightarrow> s \<in> \<D> (P after e)\<close> for s
    by (simp add: D_After ready_set_def subset_iff split: if_split_asm) blast
next
  from that[THEN anti_mono_ready_set] that[THEN le_approx2]
  show \<open>s \<notin> \<D> (P after e) \<Longrightarrow> X \<in> \<R>\<^sub>a (P after e) s \<Longrightarrow> X \<in> \<R>\<^sub>a (Q after e) s\<close> for s X
  (* show \<open>\<forall>s. s \<notin> \<D> (P after e) \<longrightarrow> \<R>\<^sub>a (P after e) s = \<R>\<^sub>a (Q after e) s\<close> *)
    apply (simp add: Ra_def D_After F_After ready_set_def subset_iff split: if_split_asm)
    by (metis F_T append_Cons append_Nil is_processT3_ST list.exhaust_sel) blast
next
  from that[THEN anti_mono_ready_set] that[THEN le_approx2]
  show \<open>s \<notin> \<D> (P after e) \<Longrightarrow> X \<in> \<R>\<^sub>a (Q after e) s \<Longrightarrow> X \<in> \<R>\<^sub>a (P after e) s\<close> for s X
    apply (simp add: Ra_def D_After F_After ready_set_def subset_iff split: if_split_asm)
    by blast (metis T_F_spec list.distinct(1) list.sel(1, 3))
next
  show \<open>s \<in> min_elems (\<D> (P after e)) \<Longrightarrow> s \<in> \<T> (Q after e)\<close> for s 
  proof (cases \<open>P = \<bottom>\<close>)
    assume \<open>s \<in> min_elems (\<D> (P after e))\<close> and \<open>P = \<bottom>\<close>
    hence \<open>s = []\<close>
      by (simp add: BOT_iff_D D_After ready_set_BOT D_UU min_elems_def)
         (metis front_tickFree_single less_list_def list.distinct(1) list.sel(1, 3) nil_le)
    thus \<open>s \<in> \<T> (Q after e)\<close> by (simp add: Nil_elem_T)
  next
    assume assms : \<open>P \<noteq> \<bottom>\<close> \<open>s \<in> min_elems (\<D> (P after e))\<close>
    from assms(2)[THEN elem_min_elems] have * : \<open>ev e # s \<in> \<D> P\<close> 
      by (simp add: D_After split: if_split_asm) (metis list.collapse)
    { assume \<open>ev e # s \<notin> min_elems (\<D> P)\<close>
      with assms(1) "*" obtain a t where \<open>a # t \<in> \<D> P\<close> \<open>a # t < ev e # s\<close>
        by (simp add: BOT_iff_D min_elems_def) (metis list.exhaust)
      hence \<open>a = ev e \<and> t < s \<and> t \<in> \<D> (P after e)\<close>
        by (simp add: le_list_def less_list_def D_After) 
           (metis Cons_in_T_imp_elem_ready_set D_T list.discI list.sel(1, 3))
      hence False by (metis assms(2) less_list_def min_elems_no)
    }
    hence \<open>ev e # s \<in> min_elems (\<D> P)\<close> by blast
    with le_approx3 that have \<open>ev e # s \<in> \<T> Q\<close> by blast
    thus \<open>s \<in> \<T> (Q after e)\<close>
      by (simp add: T_After)
         (metis Cons_in_T_imp_elem_ready_set list.discI list.sel(1, 3))
  qed
qed


lemma mono_After_T : \<open>P \<sqsubseteq>\<^sub>T Q \<Longrightarrow> P after e \<sqsubseteq>\<^sub>T Q after e\<close>
  by (auto simp add: trace_refine_def T_After ready_set_def)
     (metis list.distinct(1) list.sel(1, 3))

lemma mono_After_F :
  \<open>P \<sqsubseteq>\<^sub>F Q \<Longrightarrow> ev e \<notin> ready_set P \<or> ev e \<in> ready_set Q \<Longrightarrow>
   P after e \<sqsubseteq>\<^sub>F Q after e\<close>
  using F_subset_imp_T_subset 
  by (auto simp add: failure_refine_def F_After ready_set_def)

lemma mono_After_D : \<open>P \<sqsubseteq>\<^sub>D Q \<Longrightarrow> P after e \<sqsubseteq>\<^sub>D Q after e\<close>
  by (auto simp add: divergence_refine_def D_After ready_set_def)
     (metis Cons_eq_appendI NT_ND append_self_conv2 is_processT3_ST list.collapse subset_iff)

lemma mono_After_FD :
  \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> ev e \<notin> ready_set P \<or> ev e \<in> ready_set Q \<Longrightarrow> 
   P after e \<sqsubseteq>\<^sub>F\<^sub>D Q after e\<close>
  using F_subset_imp_T_subset
  by (simp add: failure_divergence_refine_def le_ref_def F_After D_After ready_set_def) blast

lemma mono_After_DT : \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<Longrightarrow> P after e \<sqsubseteq>\<^sub>D\<^sub>T Q after e\<close>
  by (simp add: mono_After_D mono_After_T trace_divergence_refine_def)


  


section \<open>Behaviour of @{const [source] After} with \<^const>\<open>STOP\<close>, \<^const>\<open>SKIP\<close> and \<^term>\<open>\<bottom>\<close>\<close>

lemma After_STOP: \<open>STOP after e = STOP\<close>
  by (simp add: STOP_iff_T T_After ready_set_STOP)

lemma After_is_STOP_iff:
  \<open>P after e = STOP \<longleftrightarrow> (\<forall>s. ev e # s \<in> \<T> P \<longrightarrow> s = [])\<close>
  apply (simp add: STOP_iff_T T_After ready_set_def, safe)
     apply fastforce
    apply (metis list.collapse) 
  using is_processT3_ST by force+
  

lemma After_SKIP: \<open>SKIP after e = STOP\<close>
  by (simp add: STOP_iff_T T_After ready_set_SKIP)

 
lemma After_BOT: \<open>\<bottom> after e = \<bottom>\<close>
  by (force simp add: BOT_iff_D D_After ready_set_BOT D_UU)

lemma After_is_BOT_iff: \<open>P after e = \<bottom> \<longleftrightarrow> [ev e] \<in> \<D> P\<close>
  using hd_Cons_tl by (force simp add: BOT_iff_D D_After ready_set_def D_T)




section \<open>Behaviour of @{const [source] After} with Operators of \<^session>\<open>HOL-CSP\<close>\<close>

subsection \<open>Loss of Determinism\<close>

text \<open>A first interesting observation is that the @{const [source] After} 
      operator leads to the loss of determinism.\<close>

lemma After_Mprefix_is_After_Mndetprefix:
  \<open>(\<box>a \<in> A \<rightarrow> P a) after e = (\<sqinter>a \<in> A \<rightarrow> P a) after e\<close>
  by (subst Process_eq_spec)
     (force simp add: ready_set_Mprefix ready_set_Mndetprefix F_After D_After 
                      F_Mprefix D_Mprefix F_Mndetprefix D_Mndetprefix write0_def)

lemma After_Det_is_After_Ndet: \<open>P \<box> Q after e = P \<sqinter> Q after e\<close>
  by (subst Process_eq_spec)
     (auto simp add: ready_set_Det ready_set_Ndet F_After D_After F_Det F_Ndet D_Det D_Ndet)


lemma After_Ndet: 
  \<open>P \<sqinter> Q after e = 
   (     if ev e \<notin> ready_set P \<and> ev e \<notin> ready_set Q then STOP 
    else if ev e \<in> ready_set P \<and> ev e \<in> ready_set Q then (P after e) \<sqinter> (Q after e)
    else if ev e \<in> ready_set P then P after e else Q after e)\<close>
  (is \<open>P \<sqinter> Q after e =
       (if ?c1 then STOP else if ?c2 then (P after e) \<sqinter> (Q after e) else
        if ?c3 then P after e else Q after e)\<close>)
proof -
  have \<open>?c1 \<Longrightarrow> P \<sqinter> Q after e = STOP\<close>
    by (simp add: Process_eq_spec F_After D_After ready_set_Ndet F_STOP D_STOP)
  moreover have \<open>?c2 \<Longrightarrow> P \<sqinter> Q after e = (P after e) \<sqinter> (Q after e)\<close>
    by (auto simp add: Process_eq_spec F_After D_After F_Ndet D_Ndet ready_set_Ndet)
  moreover have \<open>\<not> ?c2 \<Longrightarrow> ?c3 \<Longrightarrow> P \<sqinter> Q after e = P after e\<close>
            and \<open>\<not> ?c2 \<Longrightarrow> \<not> ?c3 \<Longrightarrow> P \<sqinter> Q after e = Q after e\<close>
    by (auto simp add: Process_eq_spec F_After D_After F_Ndet D_Ndet ready_set_Ndet)
       (metis Cons_in_T_imp_elem_ready_set F_T list.collapse,
        metis Cons_in_T_imp_elem_ready_set D_T list.collapse)+
  ultimately show ?thesis by presburger
qed
  

lemma After_Mprefix: \<open>(\<box> a \<in> A \<rightarrow> P a) after e = (if e \<in> A then P e else STOP)\<close>
  by (subst Process_eq_spec, auto simp add: F_After D_After ready_set_Mprefix
                                            F_Mprefix D_Mprefix F_STOP D_STOP)
     (metis image_eqI list.distinct(1) list.sel(1, 3))+


lemmas After_Det = After_Ndet[folded After_Det_is_After_Ndet]
   and After_Mndetprefix = After_Mprefix[unfolded After_Mprefix_is_After_Mndetprefix]
   and After_prefix = After_Mprefix[of \<open>{a}\<close> \<open>\<lambda>a. P\<close>, folded write0_def, simplified] for a P


lemma \<open>(e \<rightarrow> P) after e = P\<close> by (simp add: After_prefix) 

text \<open>This result justifies seeing \<^term>\<open>P after e\<close> as the reciprocal operator of the 
      prefix \<^term>\<open>e \<rightarrow> P\<close>.

      However, we lose information with @{const [source] After}: in general,
      \<^term>\<open>e \<rightarrow> (P after e) \<noteq> P\<close> (even when \<^term>\<open>ev e \<in> ready_set P\<close> and \<^term>\<open>P \<noteq> \<bottom>\<close>).\<close>

lemma \<open>\<exists>P. (e \<rightarrow> (P after e) \<noteq> P)\<close>
proof (intro exI)
  show \<open>e \<rightarrow> (SKIP after e) \<noteq> SKIP\<close>
    by (metis Par_SKIP_SKIP SKIP_Neq_STOP prefix_Par_SKIP)
qed

lemma \<open>\<exists>P. ev e \<in> ready_set P \<and> (e \<rightarrow> (P after e) \<noteq> P)\<close>
proof (intro exI)
  show \<open>ev e \<in> ready_set \<bottom> \<and> (e \<rightarrow> (\<bottom> after e) \<noteq> \<bottom>)\<close>
    by (simp add: ready_set_BOT Mprefix_neq_BOT write0_def)
qed

lemma \<open>\<exists>P. ev e \<in> ready_set P \<and> P \<noteq> \<bottom> \<and> (e \<rightarrow> (P after e) \<noteq> P)\<close>
proof (intro exI)
  define P where P_def: \<open>P = (e \<rightarrow> STOP) \<box> SKIP\<close>
  have * : \<open>ev e \<in> ready_set P\<close> by (simp add: P_def ready_set_Det ready_set_prefix)
  moreover have \<open>P \<noteq> \<bottom>\<close> 
    by (simp add: Det_is_BOT_iff Mprefix_neq_BOT P_def SKIP_neq_BOT write0_def)
  moreover have \<open>e \<rightarrow> (P after e) = (e \<rightarrow> STOP)\<close>
    by (rule arg_cong[where f = \<open>\<lambda>P. (e \<rightarrow> P)\<close>])
       (simp add: P_def After_Det ready_set_SKIP ready_set_prefix After_prefix)
  moreover have \<open>e \<rightarrow> STOP \<noteq> P\<close>
    apply (rule contrapos_nn[of \<open>ready_set (e \<rightarrow> STOP) = ready_set P\<close> \<open>e \<rightarrow> STOP = P\<close>])
    by (simp add: P_def ready_set_Det ready_set_prefix ready_set_SKIP)
       (erule arg_cong)
  ultimately show \<open>ev e \<in> ready_set P \<and> P \<noteq> \<bottom> \<and> (e \<rightarrow> (P after e) \<noteq> P)\<close> by presburger
qed



subsection \<open>@{const [source] After} Sequential Composition\<close>

text \<open>The first goal is to obtain an equivalent of 
      @{thm Mprefix_Seq[of \<open>{e}\<close> \<open>\<lambda>a. P\<close> Q, folded write0_def]}.
      But in order to be exhaustive we also have to consider the possibility of \<^term>\<open>Q\<close> taking
      the lead when \<^term>\<open>\<checkmark> \<in> ready_set P\<close> in the sequential composition \<^term>\<open>P \<^bold>; Q\<close>.\<close>

lemma not_skippable_or_not_readyR_After_Seq: \<open>(P \<^bold>; Q) after e = P after e \<^bold>; Q\<close>
  if \<open>\<checkmark> \<notin> ready_set P \<or> ev e \<notin> ready_set Q\<close>
proof (cases \<open>P = \<bottom>\<close>)
  show \<open>P = \<bottom> \<Longrightarrow> (P \<^bold>; Q) after e = P after e \<^bold>; Q\<close>
    by (simp add: BOT_Seq After_BOT)
next
  assume non_BOT: \<open>P \<noteq> \<bottom>\<close>
  show \<open>(P \<^bold>; Q) after e = P after e \<^bold>; Q\<close>
  proof (subst Process_eq_spec_optimized, safe)
    fix s
    assume \<open>s \<in> \<D> ((P \<^bold>; Q) after e)\<close>
    hence * : \<open>ev e # s \<in> \<D> (P \<^bold>; Q)\<close>
      by (simp add: D_After split: if_split_asm) (metis list.exhaust_sel)
    then consider \<open>ev e # s \<in> \<D> P\<close> 
      | \<open>\<exists>t1 t2. ev e # s = t1 @ t2 \<and> t1 @ [\<checkmark>] \<in> \<T> P \<and> t2 \<in> \<D> Q\<close>
      by (simp add: D_Seq) blast
    thus \<open>s \<in> \<D> (P after e \<^bold>; Q)\<close>
    proof cases
      show \<open>ev e # s \<in> \<D> P \<Longrightarrow> s \<in> \<D> (P after e \<^bold>; Q)\<close>
        by (simp add: D_Seq D_After)
           (metis Cons_in_T_imp_elem_ready_set D_T list.discI list.sel(1, 3))
    next
      assume \<open>\<exists>t1 t2. ev e # s = t1 @ t2 \<and> t1 @ [\<checkmark>] \<in> \<T> P \<and> t2 \<in> \<D> Q\<close>
      then obtain t1 t2 where ** : \<open>ev e # s = t1 @ t2\<close> \<open>t1 @ [\<checkmark>] \<in> \<T> P\<close> \<open>t2 \<in> \<D> Q\<close> by blast
      have \<open>t1 \<noteq> []\<close> by (metis "**" Cons_in_T_imp_elem_ready_set D_T self_append_conv2 that)
      with "**"(1) obtain t1'
        where \<open>t1 = ev e # t1'\<close> \<open>s = t1' @ t2\<close> by (metis Cons_eq_append_conv)
      with "**"(2, 3) show \<open>s \<in> \<D> (P after e \<^bold>; Q)\<close>
        by (simp add: D_Seq T_After)
           (metis Cons_in_T_imp_elem_ready_set list.distinct(1) list.sel(1, 3))
    qed
  next
    fix s
    assume \<open>s \<in> \<D> (P after e \<^bold>; Q)\<close>
    hence \<open>ev e # s \<in> \<D> P \<or> (\<exists>t1 t2. s = t1 @ t2 \<and> ev e # t1 @ [\<checkmark>] \<in> \<T> P \<and> t2 \<in> \<D> Q)\<close>
      by (simp add: D_Seq D_After T_After split: if_split_asm) (metis list.collapse)
    hence \<open>ev e # s \<in> \<D> (P \<^bold>; Q)\<close>
      by (elim disjE; simp add: D_Seq) (metis append_Cons)
    thus \<open>s \<in> \<D> ((P \<^bold>; Q) after e)\<close>
      by (simp add: D_After)
         (metis Cons_in_T_imp_elem_ready_set D_T list.discI list.sel(1, 3))
  next
    fix s X
    assume same_div : \<open>\<D> ((P \<^bold>; Q) after e) = \<D> (P after e \<^bold>; Q)\<close>
    assume \<open>(s, X) \<in> \<F> ((P \<^bold>; Q) after e)\<close>
    then consider \<open>ev e \<in> ready_set (P \<^bold>; Q)\<close> \<open>(ev e # s, X) \<in> \<F> (P \<^bold>; Q)\<close>
      | \<open>ev e \<notin> ready_set (P \<^bold>; Q)\<close> \<open>s = []\<close>
      by (simp add: F_After split: if_split_asm) (metis list.exhaust_sel)
    thus \<open>(s, X) \<in> \<F> (P after e \<^bold>; Q)\<close>
    proof cases
      assume assms : \<open>ev e \<in> ready_set (P \<^bold>; Q)\<close> \<open>(ev e # s, X) \<in> \<F> (P \<^bold>; Q)\<close>
      from assms(2) consider \<open>ev e # s \<in> \<D> (P \<^bold>; Q)\<close>
        | \<open>(ev e # s, insert \<checkmark> X) \<in> \<F> P\<close> \<open>tickFree s\<close>
        | \<open>\<exists>t1 t2. ev e # s = t1 @ t2 \<and> t1 @ [\<checkmark>] \<in> \<T> P \<and> (t2, X) \<in> \<F> Q\<close>
        by (simp add: F_Seq D_Seq) blast
      thus \<open>(s, X) \<in> \<F> (P after e \<^bold>; Q)\<close>
      proof cases
        assume \<open>ev e # s \<in> \<D> (P \<^bold>; Q)\<close>
        hence \<open>s \<in> \<D> ((P \<^bold>; Q) after e)\<close>
          by (simp add: D_After assms(1)) (metis list.distinct(1) list.sel(1, 3))
        with same_div D_F show \<open>(s, X) \<in> \<F> (P after e \<^bold>; Q)\<close> by blast
      next
        show \<open>(ev e # s, insert \<checkmark> X) \<in> \<F> P \<Longrightarrow> tickFree s \<Longrightarrow> (s, X) \<in> \<F> (P after e \<^bold>; Q)\<close>
          by (simp add: F_Seq F_After)
             (metis Cons_in_T_imp_elem_ready_set F_T list.distinct(1) list.sel(1, 3))
      next
        assume \<open>\<exists>t1 t2. ev e # s = t1 @ t2 \<and> t1 @ [\<checkmark>] \<in> \<T> P \<and> (t2, X) \<in> \<F> Q\<close>
        then obtain t1 t2 where * : \<open>ev e # s = t1 @ t2\<close> \<open>t1 @ [\<checkmark>] \<in> \<T> P\<close> \<open>(t2, X) \<in> \<F> Q\<close> by blast
        have \<open>t1 \<noteq> []\<close> by (metis "*" Cons_in_T_imp_elem_ready_set F_T self_append_conv2 that)
        with "*"(1) obtain t1'
          where \<open>t1 = ev e # t1'\<close> \<open>s = t1' @ t2\<close> by (metis Cons_eq_append_conv)
        with "*"(2, 3) show \<open>(s, X) \<in> \<F> (P after e \<^bold>; Q)\<close>
          by (simp add: F_Seq T_After)
             (metis Cons_in_T_imp_elem_ready_set list.distinct(1) list.sel(1, 3))
      qed
    next
      show \<open>ev e \<notin> ready_set (P \<^bold>; Q) \<Longrightarrow> s = [] \<Longrightarrow> (s, X) \<in> \<F> (P after e \<^bold>; Q)\<close>
        by (simp add: F_Seq F_After non_BOT ready_set_Seq)
    qed
  next
    fix s X
    assume same_div : \<open>\<D> ((P \<^bold>; Q) after e) = \<D> (P after e \<^bold>; Q)\<close>
    assume \<open>(s, X) \<in> \<F> (P after e \<^bold>; Q)\<close>
    then consider \<open>s \<in> \<D> (P after e \<^bold>; Q)\<close>
      | \<open>(s, insert \<checkmark> X) \<in> \<F> (P after e)\<close> \<open>tickFree s\<close>
      | \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 @ [\<checkmark>] \<in> \<T> (P after e) \<and> (t2, X) \<in> \<F> Q\<close>
      by (simp add: F_Seq D_Seq) blast
    thus \<open>(s, X) \<in> \<F> ((P \<^bold>; Q) after e)\<close>
    proof cases
      from same_div D_F show \<open>s \<in> \<D> (P after e \<^bold>; Q) \<Longrightarrow> (s, X) \<in> \<F> ((P \<^bold>; Q) after e)\<close> by blast
    next
      from that show \<open>(s, insert \<checkmark> X) \<in> \<F> (P after e) \<Longrightarrow> tickFree s \<Longrightarrow>
                      (s, X) \<in> \<F> ((P \<^bold>; Q) after e)\<close>
        by (simp add: F_After ready_set_Seq F_Seq non_BOT split: if_split_asm)
           (metis event.distinct(1) list.collapse tickFree_Cons)
    next
      assume \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 @ [\<checkmark>] \<in> \<T> (P after e) \<and> (t2, X) \<in> \<F> Q\<close>
      then obtain t1 t2
        where * : \<open>s = t1 @ t2\<close> \<open>t1 @ [\<checkmark>] \<in> \<T> (P after e)\<close> \<open>(t2, X) \<in> \<F> Q\<close> by blast
      from "*"(2) have \<open>ev e # t1 @ [\<checkmark>] \<in> \<T> P\<close>
        by (simp add: T_After split: if_split_asm) (metis list.exhaust_sel)
      with "*"(1, 3) show \<open>(s, X) \<in> \<F> ((P \<^bold>; Q) after e)\<close>
        by (simp add: F_After F_Seq ready_set_Seq non_BOT)
           (metis Cons_in_T_imp_elem_ready_set append_Cons list.distinct(1) list.sel(1, 3))
    qed
  qed
qed


lemma \<open>(P \<^bold>; STOP) after e = P after e \<^bold>; STOP\<close>
  by (simp add: not_skippable_or_not_readyR_After_Seq ready_set_STOP)


lemma skippable_not_readyL_After_Seq: \<open>(P \<^bold>; Q) after e = Q after e\<close> 
  if \<open>\<checkmark> \<in> ready_set P\<close> and \<open>ev e \<notin> ready_set P\<close>
proof (cases \<open>P = \<bottom>\<close>)
  from that(2) ready_set_BOT show \<open>P = \<bottom> \<Longrightarrow> (P \<^bold>; Q) after e = Q after e\<close> by blast
next
  assume non_BOT : \<open>P \<noteq> \<bottom>\<close>
  show \<open>(P \<^bold>; Q) after e = Q after e\<close>
  proof (subst Process_eq_spec_optimized, safe)
    fix s
    assume \<open>s \<in> \<D> ((P \<^bold>; Q) after e)\<close>
    hence \<open>ev e # s \<in> \<D> (P \<^bold>; Q)\<close>
      by (simp add: D_After split: if_split_asm) (metis list.exhaust_sel)
    with that(2) obtain t1 t2 where * : \<open>ev e # s = t1 @ t2\<close> \<open>t1 @ [\<checkmark>] \<in> \<T> P\<close> \<open>t2 \<in> \<D> Q\<close>
      by (simp add: D_Seq) (meson Cons_in_T_imp_elem_ready_set NT_ND)
    from "*"(1, 2) that(2) Cons_in_T_imp_elem_ready_set have \<open>t1 = []\<close>
      by (cases t1; simp) blast
    with "*" show \<open>s \<in> \<D> (Q after e)\<close>
      by (simp add: D_After)
         (metis Cons_in_T_imp_elem_ready_set D_T list.discI list.sel(1, 3))
  next
    show \<open>s \<in> \<D> (Q after e) \<Longrightarrow> s \<in> \<D> ((P \<^bold>; Q) after e)\<close> for s
      by (simp add: D_After D_Seq ready_set_Seq non_BOT that split: if_split_asm)
         (metis append_Nil mem_Collect_eq ready_set_def that(1))
  next
    fix s X
    assume same_div : \<open>\<D> ((P \<^bold>; Q) after e) = \<D> (Q after e)\<close>
    assume \<open>(s, X) \<in> \<F> ((P \<^bold>; Q) after e)\<close>
    then consider \<open>ev e \<in> ready_set (P \<^bold>; Q)\<close> \<open>(ev e # s, X) \<in> \<F> (P \<^bold>; Q)\<close>
      | \<open>ev e \<notin> ready_set (P \<^bold>; Q)\<close> \<open>s = []\<close>
      by (simp add: F_After split: if_split_asm) (metis list.exhaust_sel)
    thus \<open>(s, X) \<in> \<F> (Q after e)\<close>
    proof cases
      show \<open>ev e \<in> ready_set (P \<^bold>; Q) \<Longrightarrow> (ev e # s, X) \<in> \<F> (P \<^bold>; Q) \<Longrightarrow>
            (s, X) \<in> \<F> (Q after e)\<close>
        by (simp add: F_After F_Seq)
           (metis Cons_in_T_imp_elem_ready_set D_T F_T append_Nil hd_append2 
                  is_processT3_ST list.exhaust_sel list.sel(1, 3) that(2))
    next
      show \<open>ev e \<notin> ready_set (P \<^bold>; Q) \<Longrightarrow> s = [] \<Longrightarrow> (s, X) \<in> \<F> (Q after e)\<close>
        by (simp add: F_After ready_set_Seq non_BOT that)
    qed
  next
    show \<open>(s, X) \<in> \<F> (Q after e) \<Longrightarrow> (s, X) \<in> \<F> ((P \<^bold>; Q) after e)\<close> for s X
      by (simp add: F_After F_Seq ready_set_Seq non_BOT that split: if_split_asm)
         (metis append_Nil mem_Collect_eq ready_set_def that(1))
  qed
qed


lemma skippable_readyL_readyR_After_Seq: \<open>(P \<^bold>; Q) after e = (P after e \<^bold>; Q) \<sqinter> (Q after e)\<close>
  if \<open>\<checkmark> \<in> ready_set P\<close> \<open>ev e \<in> ready_set P\<close> \<open>ev e \<in> ready_set Q\<close>
proof (cases \<open>P = \<bottom>\<close>)
  show \<open>P = \<bottom> \<Longrightarrow> (P \<^bold>; Q) after e = (P after e \<^bold>; Q) \<sqinter> (Q after e)\<close>
    by (simp add: BOT_Seq After_BOT Ndet_commute[of \<bottom>, simplified Ndet_BOT])
next
  assume non_BOT : \<open>P \<noteq> \<bottom>\<close>
  show \<open>(P \<^bold>; Q) after e = (P after e \<^bold>; Q) \<sqinter> (Q after e)\<close>
  proof (subst Process_eq_spec_optimized, safe)
    fix s
    assume \<open>s \<in> \<D> ((P \<^bold>; Q) after e)\<close>
    hence \<open>ev e # s \<in> \<D> (P \<^bold>; Q)\<close>
      by (simp add: D_After ready_set_Seq non_BOT that(2)) (metis list.exhaust_sel)
    then consider \<open>ev e # s \<in> \<D> P\<close>
      | \<open>\<exists>t1 t2. ev e # s = t1 @ t2 \<and> t1 @ [\<checkmark>] \<in> \<T> P \<and> t2 \<in> \<D> Q\<close>
      by (simp add: D_Seq) blast
    thus \<open>s \<in> \<D> ((P after e \<^bold>; Q) \<sqinter> (Q after e))\<close>
    proof cases
      show \<open>ev e # s \<in> \<D> P \<Longrightarrow> s \<in> \<D> ((P after e \<^bold>; Q) \<sqinter> (Q after e))\<close>
        by (simp add: D_After D_Seq D_Ndet non_BOT that)
           (metis list.distinct(1) list.sel(1, 3))
    next
      assume \<open>\<exists>t1 t2. ev e # s = t1 @ t2 \<and> t1 @ [\<checkmark>] \<in> \<T> P \<and> t2 \<in> \<D> Q\<close>
      then obtain t1 t2 where * : \<open>ev e # s = t1 @ t2\<close> \<open>t1 @ [\<checkmark>] \<in> \<T> P\<close> \<open>t2 \<in> \<D> Q\<close> by blast
      show \<open>s \<in> \<D> ((P after e \<^bold>; Q) \<sqinter> (Q after e))\<close>
      proof (cases \<open>t1 = []\<close>)
        from "*"(1, 3) show \<open>t1 = [] \<Longrightarrow> s \<in> \<D> ((P after e \<^bold>; Q) \<sqinter> (Q after e))\<close>
          by (simp add: D_After D_Ndet that(3))
             (metis list.distinct(1) list.sel(1, 3))
      next
        assume \<open>t1 \<noteq> []\<close>
        with "*"(1, 3) obtain t1' where \<open>t1 = ev e # t1'\<close> by (cases t1; simp)
        with "*" show \<open>s \<in> \<D> ((P after e \<^bold>; Q) \<sqinter> (Q after e))\<close>
          by (simp add: T_After D_Seq D_Ndet that(2))
             (metis list.distinct(1) list.sel(1, 3))
      qed
    qed
  next
    fix s
    assume \<open>s \<in> \<D> ((P after e \<^bold>; Q) \<sqinter> (Q after e))\<close>
    then consider \<open>s \<in> \<D> (P after e \<^bold>; Q)\<close> | \<open>s \<in> \<D> (Q after e)\<close>
      by (simp add: D_Ndet) blast
    thus \<open>s \<in> \<D> ((P \<^bold>; Q) after e)\<close>
    proof cases
      show \<open>s \<in> \<D> (P after e \<^bold>; Q) \<Longrightarrow> s \<in> \<D> ((P \<^bold>; Q) after e)\<close>
        apply (simp add: D_After T_After D_Seq ready_set_Seq non_BOT that(2), elim disjE)
        by blast (metis append_Cons list.distinct(1) list.exhaust_sel list.sel(1, 3))
    next
      from that show \<open>s \<in> \<D> (Q after e) \<Longrightarrow> s \<in> \<D> ((P \<^bold>; Q) after e)\<close>
        by (simp add: D_After D_Seq ready_set_Seq non_BOT)
           (metis append_Nil mem_Collect_eq ready_set_def)
    qed
  next
    fix s X
    assume same_div : \<open>\<D> ((P \<^bold>; Q) after e) = \<D> ((P after e \<^bold>; Q) \<sqinter> (Q after e))\<close>
    assume \<open>(s, X) \<in> \<F> ((P \<^bold>; Q) after e)\<close>
    hence \<open>(ev e # s, X) \<in> \<F> (P \<^bold>; Q)\<close>
      by (simp add: F_After ready_set_Seq non_BOT that(2)) (metis list.exhaust_sel)
    then consider \<open>ev e # s \<in> \<D> P\<close>
      | \<open>(ev e # s, insert \<checkmark> X) \<in> \<F> P\<close> \<open>tickFree s\<close>
      | \<open>\<exists>t1 t2. ev e # s = t1 @ t2 \<and> t1 @ [\<checkmark>] \<in> \<T> P \<and> (t2, X) \<in> \<F> Q\<close>
      by (simp add: F_Seq D_Seq) blast
    thus \<open>(s, X) \<in> \<F> ((P after e \<^bold>; Q) \<sqinter> (Q after e))\<close>
    proof cases
      assume \<open>ev e # s \<in> \<D> P\<close>
      hence \<open>s \<in> \<D> (P after e \<^bold>; Q)\<close> 
        by (simp add: D_After D_Seq that(2)) (metis list.distinct(1) list.sel(1, 3))
      with same_div D_Ndet D_F show \<open>(s, X) \<in> \<F> ((P after e \<^bold>; Q) \<sqinter> (Q after e))\<close> by blast
    next
      show \<open>(ev e # s, insert \<checkmark> X) \<in> \<F> P \<Longrightarrow> tickFree s \<Longrightarrow>
            (s, X) \<in> \<F> ((P after e \<^bold>; Q) \<sqinter> (Q after e))\<close>
        by (simp add: F_Ndet F_Seq F_After that(2))
           (metis list.distinct(1) list.sel(1, 3))
    next
      assume \<open>\<exists>t1 t2. ev e # s = t1 @ t2 \<and> t1 @ [\<checkmark>] \<in> \<T> P \<and> (t2, X) \<in> \<F> Q\<close>
      then obtain t1 t2
        where * : \<open>ev e # s = t1 @ t2\<close> \<open>t1 @ [\<checkmark>] \<in> \<T> P\<close> \<open>(t2, X) \<in> \<F> Q\<close> by blast
      show \<open>(s, X) \<in> \<F> ((P after e \<^bold>; Q) \<sqinter> (Q after e))\<close>
      proof (cases \<open>t1 = []\<close>)
        from "*"(1, 3) show \<open>t1 = [] \<Longrightarrow> (s, X) \<in> \<F> ((P after e \<^bold>; Q) \<sqinter> (Q after e))\<close>
          by (simp add: F_Ndet F_Seq F_After that(2, 3))
             (metis list.distinct(1) list.sel(1, 3))
      next
        assume \<open>t1 \<noteq> []\<close>
        with "*"(1, 3) obtain t1' where \<open>t1 = ev e # t1'\<close> by (cases t1; simp)
        with "*" show \<open>(s, X) \<in> \<F> ((P after e \<^bold>; Q) \<sqinter> (Q after e))\<close>
          by (simp add: F_Ndet F_Seq F_After T_After that(2))
             (metis list.distinct(1) list.sel(1, 3))
      qed
    qed
  next
    fix s X
    assume same_div : \<open>\<D> ((P \<^bold>; Q) after e) = \<D> ((P after e \<^bold>; Q) \<sqinter> (Q after e))\<close>
    assume \<open>(s, X) \<in> \<F> ((P after e \<^bold>; Q) \<sqinter> (Q after e))\<close>
    then consider \<open>(s, X) \<in> \<F> (P after e \<^bold>; Q)\<close> | \<open>(s, X) \<in> \<F> (Q after e)\<close>
      by (simp add: F_Ndet) blast
    thus \<open>(s, X) \<in> \<F> ((P \<^bold>; Q) after e)\<close>
    proof cases
      assume \<open>(s, X) \<in> \<F> (P after e \<^bold>; Q)\<close>
      then consider \<open>s \<in> \<D> (P after e \<^bold>; Q)\<close>
        | \<open>(s, insert \<checkmark> X) \<in> \<F> (P after e)\<close> \<open>tickFree s\<close>
        | \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 @ [\<checkmark>] \<in> \<T> (P after e) \<and> (t2, X) \<in> \<F> Q\<close>
        by (simp add: F_Seq D_Seq) blast
      thus \<open>(s, X) \<in> \<F> ((P \<^bold>; Q) after e)\<close>
      proof cases
        show \<open>s \<in> \<D> (P after e \<^bold>; Q) \<Longrightarrow> (s, X) \<in> \<F> ((P \<^bold>; Q) after e)\<close>
          using same_div D_Ndet D_F by blast
      next
        show \<open>(s, insert \<checkmark> X) \<in> \<F> (P after e) \<Longrightarrow> tickFree s \<Longrightarrow> (s, X) \<in> \<F> ((P \<^bold>; Q) after e)\<close>
          by (simp add: F_After F_Seq ready_set_Seq that(2))
             (metis event.distinct(1) list.collapse tickFree_Cons)
      next
        show \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 @ [\<checkmark>] \<in> \<T> (P after e) \<and> (t2, X) \<in> \<F> Q \<Longrightarrow>
                      (s, X) \<in> \<F> ((P \<^bold>; Q) after e)\<close>
          by (simp add: F_After T_After F_Seq ready_set_Seq non_BOT that(2))
             (metis append_Cons list.distinct(1) list.exhaust_sel list.sel(1, 3))
      qed
    next
      show \<open>(s, X) \<in> \<F> (Q after e) \<Longrightarrow> (s, X) \<in> \<F> ((P \<^bold>; Q) after e)\<close>
        by (simp add: F_After F_Seq ready_set_Seq that(3))
           (metis append_Nil mem_Collect_eq ready_set_def that(1))
    qed
  qed
qed


lemma not_readyL_not_skippable_or_not_readyR_After_Seq:
  \<open>ev e \<notin> ready_set P \<Longrightarrow> \<checkmark> \<notin> ready_set P \<or> ev e \<notin> ready_set Q \<Longrightarrow> 
   (P \<^bold>; Q) after e = STOP\<close> 
  by (simp add: not_skippable_or_not_readyR_After_Seq STOP_Seq not_ready_After)
 

lemma After_Seq:
  \<open>(P \<^bold>; Q) after e = 
   (     if ev e \<notin> ready_set P \<and> ev e \<notin> ready_set Q then STOP
    else if ev e \<notin> ready_set Q then P after e \<^bold>; Q
    else if ev e \<notin> ready_set P then if \<checkmark> \<in> ready_set P then Q after e else STOP
    else if  \<checkmark>   \<in> ready_set P then (P after e \<^bold>; Q) \<sqinter> (Q after e) else P after e \<^bold>; Q)\<close>
  by (simp add: STOP_Seq not_ready_After not_skippable_or_not_readyR_After_Seq 
                skippable_not_readyL_After_Seq skippable_readyL_readyR_After_Seq)


subsection \<open>@{const [source] After} Synchronization\<close>

text \<open>Now let's focus on \<^const>\<open>Sync\<close>.
      We want to obtain an equivalent of

      @{thm Mprefix_Sync_distr}

      We will also divide the task.\<close>

text \<open>@{const [source] After} version of

      @{thm Mprefix_Sync_distr_left
      [of \<open>{e}\<close> _ _ \<open>\<lambda>a. P\<close>, folded write0_def, simplified]}.\<close>

lemma tickFree_tl: \<open>tickFree s \<Longrightarrow> tickFree(tl s)\<close>
  \<comment>\<open>Remove this lemma, already in future versions of \<^session>\<open>HOL-CSP\<close>.\<close>
  by (metis Nil_tl tickFree_tl)

lemma readyL_not_readyR_not_in_After_Sync:
  \<open>(P \<lbrakk>S\<rbrakk> Q) after e = P after e \<lbrakk>S\<rbrakk> Q\<close>
  if ready_hyps: \<open>ev e \<in> ready_set P\<close> \<open>ev e \<notin> ready_set Q\<close> and notin: \<open>e \<notin> S\<close>
proof (subst Process_eq_spec_optimized, safe)

  { fix s X
    assume assms : \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close> \<open>(ev e # s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close>
       and same_div : \<open>\<D> ((P \<lbrakk>S\<rbrakk> Q) after e) = \<D> (P after e \<lbrakk>S\<rbrakk> Q)\<close>
    have \<open>(s, X) \<in> \<F> (P after e \<lbrakk>S\<rbrakk> Q)\<close>
    proof (cases \<open>ev e # s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>)
      case True
      hence \<open>s \<in> \<D> ((P \<lbrakk>S\<rbrakk> Q) after e)\<close>
        by (force simp add: D_After ready_set_Sync ready_hyps(1) assms(1, 2) notin)
      thus \<open>(s, X) \<in> \<F> (P after e \<lbrakk>S\<rbrakk> Q)\<close> using NF_ND same_div by blast
    next
      case False
      with assms(3) obtain s_P s_Q X_P X_Q 
        where * : \<open>(s_P, X_P) \<in> \<F> P\<close> \<open>(s_Q, X_Q) \<in> \<F> Q\<close> 
                  \<open>(ev e # s) setinterleaves ((s_P, s_Q), insert \<checkmark> (ev ` S))\<close>
                  \<open>X = (X_P \<union> X_Q) \<inter> insert \<checkmark> (ev ` S) \<union> X_P \<inter> X_Q\<close>
        by (simp add: F_Sync D_Sync) blast
      have ** : \<open>s_P \<noteq> [] \<and> hd s_P = ev e \<and> s setinterleaves ((tl s_P, s_Q), insert \<checkmark> (ev ` S))\<close>
        using *(3) by (cases s_P; cases s_Q, auto split: if_split_asm)
                      (metis *(2) After_is_STOP_iff CollectI F_T not_ready_After
                             ready_set_def ready_hyps(2))+
      hence \<open>(tl s_P, X_P) \<in> \<F> (P after e) \<and> (s_Q, X_Q) \<in> \<F> Q \<and>
             s setinterleaves ((tl s_P, s_Q), insert \<checkmark> (ev ` S)) \<and>
             X = (X_P \<union> X_Q) \<inter> insert \<checkmark> (ev ` S) \<union> X_P \<inter> X_Q\<close>
        apply (simp add: F_After "**" ready_hyps(1))
        using "*"(1, 2, 4) "**" by blast
      thus \<open>(s, X) \<in> \<F> (P after e \<lbrakk>S\<rbrakk> Q)\<close>
        by (simp add: F_Sync) blast
    qed
  } note * = this

  show \<open>(s, X) \<in> \<F> ((P \<lbrakk>S\<rbrakk> Q) after e) \<Longrightarrow> (s, X) \<in> \<F> (P after e \<lbrakk>S\<rbrakk> Q)\<close> 
      if same_div : \<open>\<D> ((P \<lbrakk>S\<rbrakk> Q) after e) = \<D> (P after e \<lbrakk>S\<rbrakk> Q)\<close> for s X
    apply (simp add: F_After ready_set_Sync ready_hyps notin image_iff 
              split: if_split_asm)
     apply (erule disjE; 
            simp add: After_BOT Sync_commute[of \<bottom>, simplified Sync_BOT] Sync_BOT F_UU,
            metis butlast_tl front_tickFree_butlast tickFree_tl)
    by (metis "*" list.exhaust_sel same_div)
next

  fix s X
  assume same_div : \<open>\<D> ((P \<lbrakk>S\<rbrakk> Q) after e) = \<D> (P after e \<lbrakk>S\<rbrakk> Q)\<close>
  { assume assms : \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close> \<open>(s, X) \<in> \<F> (P after e \<lbrakk>S\<rbrakk> Q)\<close>
    from assms(3) consider
      \<open>\<exists>s_P s_Q X_P X_Q. (s_P, X_P) \<in> \<F> (P after e) \<and> (s_Q, X_Q) \<in> \<F> Q \<and>
                          s setinterleaves ((s_P, s_Q), insert \<checkmark> (ev ` S)) \<and> 
                          X = (X_P \<union> X_Q) \<inter> insert \<checkmark> (ev ` S) \<union> X_P \<inter> X_Q\<close> |
      \<open>s \<in> \<D> (P after e \<lbrakk>S\<rbrakk> Q)\<close>
      by (simp add: F_Sync D_Sync) blast
    hence \<open>(ev e # s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close>
    proof cases
      case 1
      then obtain s_P s_Q X_P X_Q
        where * : \<open>(ev e # s_P, X_P) \<in> \<F> P\<close> \<open>(s_Q, X_Q) \<in> \<F> Q\<close> 
                  \<open>s setinterleaves ((s_P, s_Q), insert \<checkmark> (ev ` S))\<close>
                  \<open>X = (X_P \<union> X_Q) \<inter> insert \<checkmark> (ev ` S) \<union> X_P \<inter> X_Q\<close>
        by (simp add: F_After ready_hyps(1)) (metis list.collapse)
      have \<open>(s_Q, X_Q) \<in> \<F> Q \<and> 
            (ev e # s) setinterleaves ((ev e # s_P, s_Q), insert \<checkmark> (ev ` S)) \<and>
             X = (X_P \<union> X_Q) \<inter> insert \<checkmark> (ev ` S) \<union> X_P \<inter> X_Q\<close>
        apply (simp add: *(2, 4))
        using *(3) by (cases s_Q; simp add: notin image_iff)
      with "*"(1) show \<open>(ev e # s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close>
        by (simp add: F_Sync) blast
    next
      case 2
      from "2"[simplified same_div[symmetric]]
      have \<open>ev e # s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close> 
        by (simp add: D_After ready_hyps(1) ready_set_Sync 
                      assms(1, 2) notin image_iff, metis list.collapse)
      thus \<open>(ev e # s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close> using NF_ND by blast
    qed
  }
  thus \<open>(s, X) \<in> \<F> (P after e \<lbrakk>S\<rbrakk> Q) \<Longrightarrow> (s, X) \<in> \<F> ((P \<lbrakk>S\<rbrakk> Q) after e)\<close> 
    by (simp add: F_After ready_set_Sync ready_hyps After_BOT F_UU image_iff
                     Sync_commute[of \<bottom>, simplified Sync_BOT] Sync_BOT notin)
       (metis butlast.simps(2) event.distinct(1) front_tickFree_butlast front_tickFree_single
              list.distinct(1) list.sel(1, 3) process_charn tickFree_Cons)
next

  { fix s
    assume assms : \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close> \<open>ev e # s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
    from assms(3) obtain t u r v
      where * : \<open>front_tickFree v\<close> \<open>tickFree r \<or> v = []\<close> \<open>ev e # s = r @ v\<close> 
                \<open>r setinterleaves ((t, u), insert \<checkmark> (ev ` S))\<close>
                \<open>t \<in> \<D> P \<and> u \<in> \<T> Q \<or> t \<in> \<D> Q \<and> u \<in> \<T> P\<close> by (simp add: D_Sync) blast
    have ** : \<open>r \<noteq> [] \<and> hd r = ev e\<close>
      by (metis "*"(3, 4, 5) BOT_iff_D assms(1, 2) empty_setinterleaving hd_append list.sel(1))
    hence *** : \<open>(t \<in> \<D> P \<and> u \<in> \<T> Q \<longrightarrow> t \<noteq> [] \<and> hd t = ev e \<and> 
                              tl r setinterleaves ((tl t, u), insert \<checkmark> (ev ` S))) \<and> 
                 (t \<in> \<D> Q \<and> u \<in> \<T> P \<longrightarrow> u \<noteq> [] \<and> hd u = ev e \<and> 
                              tl r setinterleaves ((t, tl u), insert \<checkmark> (ev ` S)))\<close>
      using *(4) assms(1, 2)[simplified BOT_iff_D] ready_hyps[simplified ready_set_def]
      apply (cases t; cases u; simp split: if_split_asm)
      by (safe; simp; metis [[metis_verbose = false]] After_is_STOP_iff D_T 
                            not_ready_After ready_hyps(2))+
    from *(5) have \<open>s \<in> \<D> (P after e \<lbrakk>S\<rbrakk> Q)\<close>
    proof (elim disjE)
      assume \<open>t \<in> \<D> P \<and> u \<in> \<T> Q\<close>
      hence \<open>front_tickFree v \<and> (tickFree (tl r) \<or> v = []) \<and> s = tl r @ v \<and>
             tl r setinterleaves ((tl t, u), insert \<checkmark> (ev ` S)) \<and>
             tl t \<in> \<D> (P after e) \<and> u \<in> \<T> Q\<close>
        by (simp add: D_After ready_hyps,
            metis "*"(1, 2, 3) "**" "***" list.sel(3) tickFree_tl tl_append2)
      thus \<open>s \<in> \<D> (P after e \<lbrakk>S\<rbrakk> Q)\<close> by (simp add: D_Sync) blast
    next
      assume \<open>t \<in> \<D> Q \<and> u \<in> \<T> P\<close>
      hence \<open>front_tickFree v \<and> (tickFree (tl r) \<or> v = []) \<and> s = tl r @ v \<and>
             tl r setinterleaves ((t, tl u), insert \<checkmark> (ev ` S)) \<and>
             t \<in> \<D> Q \<and> tl u \<in> \<T> (P after e)\<close>
        by (simp add: D_After T_After ready_hyps,
            metis "*"(1, 2, 3) "**" "***" list.sel(3) tickFree_tl tl_append2)
      thus \<open>s \<in> \<D> (P after e \<lbrakk>S\<rbrakk> Q)\<close>
        by (simp add: D_Sync) blast
    qed
  } note * = this

  show \<open>s \<in> \<D> ((P \<lbrakk>S\<rbrakk> Q) after e) \<Longrightarrow> s \<in> \<D> (P after e \<lbrakk>S\<rbrakk> Q)\<close> for s
    apply (simp add: D_After ready_set_Sync ready_hyps notin image_iff 
              split: if_split_asm)
     apply (erule disjE;
            simp add: After_BOT Sync_commute[of \<bottom>, simplified Sync_BOT] Sync_BOT D_UU,
            metis butlast_tl front_tickFree_butlast tickFree_tl)
    by (metis "*" list.collapse)
next 

  fix s
  { assume assms : \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close> \<open>s \<in> \<D> (P after e \<lbrakk>S\<rbrakk> Q)\<close>
    from assms(3) obtain t u r v
        where * : \<open>front_tickFree v\<close> \<open>tickFree r \<or> v = []\<close> \<open>s = r @ v\<close> 
                  \<open>r setinterleaves ((t, u), insert \<checkmark> (ev ` S))\<close> 
                  \<open>t \<in> \<D> (P after e) \<and> u \<in> \<T> Q \<or> t \<in> \<D> Q \<and> u \<in> \<T> (P after e)\<close>
      by (simp add: D_Sync) blast
    from "*"(5) have \<open>ev e # s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
    proof (elim disjE)
      assume \<open>t \<in> \<D> (P after e) \<and> u \<in> \<T> Q\<close>
      with "*"(1, 2, 3, 4) ready_hyps(1)
      have ** : \<open>front_tickFree v \<and> (tickFree (ev e # r) \<or> v = []) \<and> s = r @ v \<and>
                 (ev e # r) setinterleaves ((ev e # t, u), insert \<checkmark> (ev ` S)) \<and>
                 ev e # t \<in> \<D> P \<and> u \<in> \<T> Q\<close>
        by (cases u; simp add: D_After notin image_iff, metis list.collapse)
      show \<open>ev e # s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
        by (simp add: D_Sync) (metis "**" Cons_eq_appendI)
    next
      assume \<open>t \<in> \<D> Q \<and> u \<in> \<T> (P after e)\<close>
      with "*"(1, 2, 3, 4) ready_hyps(1)
      have ** : \<open>front_tickFree v \<and> (tickFree (ev e # r) \<or> v = []) \<and> s = r @ v \<and>
                 (ev e # r) setinterleaves ((t, ev e # u), insert \<checkmark> (ev ` S)) \<and>
                 t \<in> \<D> Q \<and> ev e # u \<in> \<T> P\<close>
        by (cases t; simp add: T_After notin image_iff, metis list.collapse)
      show \<open>ev e # s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
        by (simp add: D_Sync) (metis "**" Cons_eq_appendI)
    qed
  }
  thus \<open>s \<in> \<D> (P after e \<lbrakk>S\<rbrakk> Q) \<Longrightarrow> s \<in> \<D> ((P \<lbrakk>S\<rbrakk> Q) after e)\<close>
    by (simp add: D_After ready_set_Sync ready_hyps After_BOT D_UU
                     Sync_commute[of \<bottom>, simplified Sync_BOT] Sync_BOT notin image_iff)
       (metis D_imp_front_tickFree butlast.simps(2) event.distinct(1) front_tickFree_butlast 
              list.discI list.sel(1, 3) tickFree_Cons tickFree_butlast)
qed



lemma not_readyL_in_After_Sync:
  \<open>ev e \<notin> ready_set P \<Longrightarrow> e \<in> S \<Longrightarrow> 
   (P \<lbrakk>S\<rbrakk> Q) after e = (if Q = \<bottom> then \<bottom> else STOP)\<close> 
  apply (simp, intro conjI impI)
  by (simp add: BOT_iff_D D_After Sync_BOT ready_set_BOT D_UU,
      metis front_tickFree_single list.sel(1) list.sel(3) not_Cons_self)
     (auto simp add: STOP_iff_T T_After ready_set_BOT ready_set_Sync)


text \<open>@{const [source] After} version of @{thm Mprefix_Sync_distr_subset
      [of \<open>{e}\<close> _ \<open>{e}\<close> \<open>\<lambda>a. P\<close> \<open>\<lambda>a. Q\<close>, simplified, folded write0_def]}.\<close>

lemma readyL_readyR_in_After_Sync:
  \<open>(P \<lbrakk>S\<rbrakk> Q) after e = P after e \<lbrakk>S\<rbrakk> Q after e\<close> 
  if ready_hyps: \<open>ev e \<in> ready_set P\<close> \<open>ev e \<in> ready_set Q\<close> and inside: \<open>e \<in> S\<close>
proof (subst Process_eq_spec_optimized, safe)

  { fix s X
    assume assms : \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close> \<open>(ev e # s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close> 
       and same_div : \<open>\<D> ((P \<lbrakk>S\<rbrakk> Q) after e) = \<D> (P after e \<lbrakk>S\<rbrakk> Q after e)\<close>
    from assms(3) consider
      \<open>\<exists>s_P s_Q X_P X_Q. (s_P, X_P) \<in> \<F> P \<and> (s_Q, X_Q) \<in> \<F> Q \<and>
                         (ev e # s) setinterleaves ((s_P, s_Q), insert \<checkmark> (ev ` S)) \<and> 
                         X = (X_P \<union> X_Q) \<inter> insert \<checkmark> (ev ` S) \<union> X_P \<inter> X_Q\<close> |
      \<open>ev e # s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
      by (simp add: F_Sync D_Sync) blast
    hence \<open>(s, X) \<in> \<F> (P after e \<lbrakk>S\<rbrakk> Q after e)\<close>
    proof cases
      case 1
      then obtain s_P s_Q X_P X_Q
        where * : \<open>(s_P, X_P) \<in> \<F> P\<close> \<open>(s_Q, X_Q) \<in> \<F> Q\<close>
                  \<open>(ev e # s) setinterleaves ((s_P, s_Q), insert \<checkmark> (ev ` S))\<close>
                  \<open>X = (X_P \<union> X_Q) \<inter> insert \<checkmark> (ev ` S) \<union> X_P \<inter> X_Q\<close> by blast
      from *(3) have \<open>s_P \<noteq> [] \<and> hd s_P = ev e \<and> s_Q \<noteq> [] \<and> hd s_Q = ev e \<and>
                      s setinterleaves ((tl s_P, tl s_Q), insert \<checkmark> (ev ` S))\<close>
        using inside by (cases s_P; cases s_Q, auto simp add: split: if_split_asm)
      hence \<open>(tl s_P, X_P) \<in> \<F> (P after e) \<and> (tl s_Q, X_Q) \<in> \<F> (Q after e) \<and>
            s setinterleaves ((tl s_P, tl s_Q), insert \<checkmark> (ev ` S)) \<and>
            X = (X_P \<union> X_Q) \<inter> insert \<checkmark> (ev ` S) \<union> X_P \<inter> X_Q\<close>
        using "*"(1, 2, 4) ready_hyps by (simp add: F_After) blast
      thus \<open>(s, X) \<in> \<F> (P after e \<lbrakk>S\<rbrakk> Q after e)\<close>
        by (simp add: F_Sync) blast
    next
      assume \<open>ev e # s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
      hence \<open>s \<in> \<D> ((P \<lbrakk>S\<rbrakk> Q) after e)\<close> 
        by (force simp add: D_After ready_set_Sync ready_hyps assms(1, 2))
      from this[simplified same_div]
      show \<open>(s, X) \<in> \<F> (P after e \<lbrakk>S\<rbrakk> Q after e)\<close> using NF_ND by blast
    qed
  } note * = this

  show \<open>(s, X) \<in> \<F> ((P \<lbrakk>S\<rbrakk> Q) after e) \<Longrightarrow> (s, X) \<in> \<F> (P after e \<lbrakk>S\<rbrakk> Q after e)\<close>
    if same_div : \<open>\<D> ((P \<lbrakk>S\<rbrakk> Q) after e) = \<D> (P after e \<lbrakk>S\<rbrakk> Q after e)\<close> for s X
    apply (simp add: F_After ready_set_Sync ready_hyps split: if_split_asm)
      apply (erule disjE; 
             simp add: After_BOT Sync_commute[of \<bottom>, simplified Sync_BOT] Sync_BOT F_UU,
             metis butlast_tl front_tickFree_butlast tickFree_tl)
    by (metis "*" list.exhaust_sel same_div)
next

  fix s X
  assume same_div : \<open>\<D> ((P \<lbrakk>S\<rbrakk> Q) after e) = \<D> (P after e \<lbrakk>S\<rbrakk> Q after e)\<close>
  { assume assms : \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close> \<open>(s, X) \<in> \<F> (P after e \<lbrakk>S\<rbrakk> Q after e)\<close>
    from assms(3) consider 
      \<open>\<exists>s_P s_Q X_P X_Q. (ev e # s_P, X_P) \<in> \<F> P \<and> (ev e # s_Q, X_Q) \<in> \<F> Q \<and>
                         s setinterleaves ((s_P, s_Q), insert \<checkmark> (ev ` S)) \<and> 
                         X = (X_P \<union> X_Q) \<inter> insert \<checkmark> (ev ` S) \<union> X_P \<inter> X_Q\<close> |
      \<open>s \<in> \<D> (P after e \<lbrakk>S\<rbrakk> Q after e)\<close>
      by (auto simp add: F_Sync D_Sync F_After ready_hyps) (metis list.collapse)
    hence \<open>(ev e # s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close>
    proof cases
      case 1
      then obtain s_P s_Q X_P X_Q 
        where * : \<open>(ev e # s_P, X_P) \<in> \<F> P\<close> \<open>(ev e # s_Q, X_Q) \<in> \<F> Q\<close> 
                  \<open>s setinterleaves ((s_P, s_Q), insert \<checkmark> (ev ` S))\<close>
                  \<open>X = (X_P \<union> X_Q) \<inter> insert \<checkmark> (ev ` S) \<union> X_P \<inter> X_Q\<close> by blast
      have ** : \<open>(ev e # s) setinterleaves ((ev e # s_P, ev e # s_Q), insert \<checkmark> (ev ` S))\<close>
        by (simp add: inside "*"(3))
      show \<open>(ev e # s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close>
        apply (simp add: F_Sync)
        using "*"(1, 2, 4) "**" by blast
    next
      assume \<open>s \<in> \<D> (P after e \<lbrakk>S\<rbrakk> Q after e)\<close>
      with same_div[symmetric] have \<open>ev e # s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
        by (simp add: D_After ready_hyps ready_set_Sync assms(1, 2)) (metis list.collapse)
      with D_F show \<open>(ev e # s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close> by blast
    qed
  }
  thus \<open>(s, X) \<in> \<F> (P after e \<lbrakk>S\<rbrakk> Q after e) \<Longrightarrow> (s, X) \<in> \<F> ((P \<lbrakk>S\<rbrakk> Q) after e)\<close>
    by (simp add: F_After ready_set_Sync ready_hyps After_BOT F_UU
                  Sync_commute[of \<bottom>, simplified Sync_BOT] Sync_BOT)
       (metis butlast.simps(2) event.distinct(1) front_tickFree_butlast is_processT2 
              list.distinct(1) list.sel(1, 3) tickFree_Cons tickFree_butlast)
next

  { fix s
    assume assms : \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close> \<open>ev e # s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close> 
    from assms(3) obtain t u r v
      where * : \<open>front_tickFree v\<close> \<open>tickFree r \<or> v = []\<close> \<open>ev e # s = r @ v\<close>
                \<open>r setinterleaves ((t, u), insert \<checkmark> (ev ` S))\<close> 
                \<open>t \<in> \<D> P \<and> u \<in> \<T> Q \<or> t \<in> \<D> Q \<and> u \<in> \<T> P\<close> by (simp add: D_Sync) blast
    have ** : \<open>r \<noteq> [] \<and> hd r = ev e \<and> t \<noteq> [] \<and> hd t = ev e \<and> u \<noteq> [] \<and> hd u = ev e \<and>
               tl r setinterleaves ((tl t, tl u), insert \<checkmark> (ev ` S))\<close>
      using *(3, 4, 5) inside assms(1, 2)[simplified BOT_iff_D] 
      by (cases t; cases u; force split: if_split_asm)
    have \<open>(tickFree (tl r) \<or> v = []) \<and> s = tl r @ v \<and>
          (tl t \<in> \<D> (P after e) \<and> tl u \<in> \<T> (Q after e) \<or> 
           tl t \<in> \<D> (Q after e) \<and> tl u \<in> \<T> (P after e))\<close>
      using "*"(2, 3, 5) "**" apply (simp add: D_After ready_hyps T_After)
      by (metis tickFree_tl list.sel(3) tl_append2)
    with "*"(1) "**" have \<open>s \<in> \<D> (P after e \<lbrakk>S\<rbrakk> Q after e)\<close> by (simp add: D_Sync) blast
  } note * = this

  show \<open>s \<in> \<D> ((P \<lbrakk>S\<rbrakk> Q) after e) \<Longrightarrow> s \<in> \<D> (P after e \<lbrakk>S\<rbrakk> Q after e)\<close> for s
    apply (simp add: D_After ready_set_Sync ready_hyps After_BOT D_UU
              split: if_split_asm)
     apply (erule disjE; 
            simp add: After_BOT Sync_commute[of \<bottom>, simplified Sync_BOT] Sync_BOT D_UU,
            metis butlast_tl front_tickFree_butlast tickFree_tl)
    by (metis "*" list.exhaust_sel)
next
  
  fix s
  { assume \<open>s \<in> \<D> (P after e \<lbrakk>S\<rbrakk> Q after e)\<close>
    from this obtain t u r v
      where * : \<open>front_tickFree v\<close> \<open>tickFree r \<or> v = []\<close> \<open>s = r @ v\<close>
                \<open>r setinterleaves ((t, u), insert \<checkmark> (ev ` S))\<close> 
                \<open>ev e # t \<in> \<D> P \<and> ev e # u \<in> \<T> Q \<or> ev e # t \<in> \<D> Q \<and> ev e # u \<in> \<T> P\<close> 
      by (simp add: D_Sync D_After T_After ready_hyps) (metis list.collapse)
    have ** : \<open>(ev e # r) setinterleaves ((ev e # t, ev e # u), insert \<checkmark> (ev ` S))\<close>
      by (simp add: inside "*"(4))
    have \<open>ev e # s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
      by (simp add: D_Sync inside)
         (metis "*"(1, 2, 3, 5) "**" append_Cons event.distinct(1) tickFree_Cons)
  }
  thus \<open>s \<in> \<D> (P after e \<lbrakk>S\<rbrakk> Q after e) \<Longrightarrow> s \<in> \<D> ((P \<lbrakk>S\<rbrakk> Q) after e)\<close>
    by (simp add: D_After ready_set_Sync ready_hyps After_BOT D_UU
                  Sync_commute[of \<bottom>, simplified Sync_BOT] Sync_BOT inside)
       (metis D_imp_front_tickFree list.distinct(1) list.sel(1, 3))
qed


text \<open>@{const [source] After} version of
     
      @{thm Mprefix_Sync_distr_indep
      [of \<open>{e}\<close> _ \<open>{e}\<close> \<open>\<lambda>a. P\<close> \<open>\<lambda>a. Q\<close>, simplified, folded write0_def]}.\<close>

lemma readyL_readyR_not_in_After_Sync: 
  \<open>(P \<lbrakk>S\<rbrakk> Q) after e = (P after e \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after e)\<close>
  if ready_hyps: \<open>ev e \<in> ready_set P\<close> \<open>ev e \<in> ready_set Q\<close> and notin: \<open>e \<notin> S\<close>
proof (subst Process_eq_spec_optimized, safe)

  { fix P Q s X s_P s_Q X_P X_Q
    assume assms : \<open>(s_P, X_P) \<in> \<F> P\<close> \<open>(s_Q, X_Q) \<in> \<F> Q\<close> 
                   \<open>X = (X_P \<union> X_Q) \<inter> insert \<checkmark> (ev ` S) \<union> X_P \<inter> X_Q\<close>
                   \<open>s_P \<noteq> []\<close> \<open>hd s_P = ev e\<close>
                   \<open>s setinterleaves ((tl s_P, s_Q), insert \<checkmark> (ev ` S))\<close>
                   \<open>ev e \<in> ready_set P\<close>
    from assms(1, 4, 5, 7) have \<open>(tl s_P, X_P) \<in> \<F> (P after e)\<close>
      by (simp add: F_After) blast
    with assms(2, 3, 6) have \<open>(s, X) \<in> \<F> (P after e \<lbrakk>S\<rbrakk> Q)\<close>
      by (simp add: F_Sync) blast
  } note * = this
  
  { fix s X
    assume assms : \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close> \<open>(ev e # s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close>
       and same_div : \<open>\<D> ((P \<lbrakk>S\<rbrakk> Q) after e) = \<D> ((P after e \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after e))\<close>
    from assms(3) consider
       \<open>\<exists>s_P s_Q X_P X_Q. (s_P, X_P) \<in> \<F> P \<and> (s_Q, X_Q) \<in> \<F> Q \<and>
                          (ev e # s) setinterleaves ((s_P, s_Q), insert \<checkmark> (ev ` S)) \<and> 
                          X = (X_P \<union> X_Q) \<inter> insert \<checkmark> (ev ` S) \<union> X_P \<inter> X_Q\<close> |
        \<open>s \<in> \<D> ((P \<lbrakk>S\<rbrakk> Q) after e)\<close>
      by (simp add: F_Sync D_After D_Sync ready_set_Sync assms(1, 2) ready_hyps)
         (metis (no_types, opaque_lifting) list.distinct(1) list.sel(1, 3))
    hence \<open>(s, X) \<in> \<F> ((P after e \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after e))\<close>
    proof cases
      case 1
      then obtain s_P s_Q X_P X_Q
        where ** : \<open>(s_P, X_P) \<in> \<F> P\<close> \<open>(s_Q, X_Q) \<in> \<F> Q\<close> 
                   \<open>(ev e # s) setinterleaves ((s_P, s_Q), insert \<checkmark> (ev ` S))\<close>
                   \<open>X = (X_P \<union> X_Q) \<inter> insert \<checkmark> (ev ` S) \<union> X_P \<inter> X_Q\<close> by blast
      have \<open>s_P \<noteq> [] \<and> hd s_P = ev e \<and> s setinterleaves ((tl s_P, s_Q), insert \<checkmark> (ev ` S)) \<or>
            s_Q \<noteq> [] \<and> hd s_Q = ev e \<and> s setinterleaves ((s_P, tl s_Q), insert \<checkmark> (ev ` S))\<close>
        using **(3) by (cases s_P; cases s_Q; simp add: notin image_iff split: if_split_asm) blast
      thus \<open>(s, X) \<in> \<F> ((P after e \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after e))\<close>
        apply (elim disjE; simp add: F_Ndet)
        subgoal using "*" "**"(1, 2, 4) ready_hyps(1) by blast
        apply (rule disjI2, subst Sync_commute, rule *[OF **(2, 1)])
        by (simp_all add: "**"(4) Int_commute Un_commute Sync_commute Sync.sym ready_hyps(2))
    next
      assume \<open>s \<in> \<D> ((P \<lbrakk>S\<rbrakk> Q) after e)\<close>
      from this[simplified same_div]
      show \<open>(s, X) \<in> \<F> ((P after e \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after e))\<close> using NF_ND by blast
    qed
  } note ** = this
    
  show \<open>(s, X) \<in> \<F> ((P \<lbrakk>S\<rbrakk> Q) after e) \<Longrightarrow> (s, X) \<in> \<F> ((P after e \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after e))\<close> 
    if same_div: \<open>\<D> ((P \<lbrakk>S\<rbrakk> Q) after e) = \<D> ((P after e \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after e))\<close> for s X
    apply (simp add: F_After ready_set_Sync ready_hyps split: if_split_asm)
     apply (erule disjE;
            simp add: After_BOT Sync_commute[of \<bottom>, simplified Sync_BOT] Sync_BOT F_UU Ndet_id,
            metis butlast_tl front_tickFree_butlast tickFree_tl)
    by (metis "**" same_div list.exhaust_sel)
next

  { fix s X P Q
    assume assms : \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close> \<open>(s, X) \<in> \<F> (P after e \<lbrakk>S\<rbrakk> Q)\<close> \<open>ev e \<in> ready_set P\<close>
       and same_div : \<open>\<D> ((P \<lbrakk>S\<rbrakk> Q) after e) = \<D> ((P after e \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after e))\<close>
    from assms(3)[simplified F_Sync, simplified] consider
      \<open>\<exists>s_P s_Q X_P X_Q. (ev e # s_P, X_P) \<in> \<F> P \<and> (s_Q, X_Q) \<in> \<F> Q \<and>
                         s setinterleaves ((s_P, s_Q), insert \<checkmark> (ev ` S)) \<and> 
                         X = (X_P \<union> X_Q) \<inter> insert \<checkmark> (ev ` S) \<union> X_P \<inter> X_Q\<close> |
      \<open>s \<in> \<D> (P after e \<lbrakk>S\<rbrakk> Q)\<close>
      by (simp add: F_Sync F_After assms(4) D_Sync)
         (metis (no_types, opaque_lifting) list.exhaust_sel)
    hence \<open>(ev e # s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close>
    proof cases
      case 1
      then obtain s_P s_Q X_P X_Q
        where * : \<open>(ev e # s_P, X_P) \<in> \<F> P\<close> \<open>(s_Q, X_Q) \<in> \<F> Q\<close>
                  \<open>s setinterleaves ((s_P, s_Q), insert \<checkmark> (ev ` S))\<close>
                  \<open>X = (X_P \<union> X_Q) \<inter> insert \<checkmark> (ev ` S) \<union> X_P \<inter> X_Q\<close> by blast
      have \<open>(ev e # s) setinterleaves ((ev e # s_P, s_Q), insert \<checkmark> (ev ` S))\<close>
        using "*"(3) by (cases s_Q; simp add: notin image_iff)
      with "*"(1, 2, 4) show \<open>(ev e # s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close>
        by (simp add: F_Sync) blast
    next
      assume \<open>s \<in> \<D> (P after e \<lbrakk>S\<rbrakk> Q)\<close>
      hence \<open>s \<in> \<D> ((P \<lbrakk>S\<rbrakk> Q) after e)\<close> using same_div[simplified D_Ndet] by fast
      hence \<open>(s, X) \<in> \<F> ((P \<lbrakk>S\<rbrakk> Q) after e)\<close> using process_charn by blast
      thus \<open>(ev e # s, X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close> 
        by (simp add: F_After ready_set_Sync assms(1, 2, 4) notin image_iff)
           (metis list.collapse)
    qed
  } note * = this

  show \<open>(s, X) \<in> \<F> ((P after e \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after e)) \<Longrightarrow> (s, X) \<in> \<F> ((P \<lbrakk>S\<rbrakk> Q) after e)\<close> 
    if same_div : \<open>\<D> ((P \<lbrakk>S\<rbrakk> Q) after e) = \<D> ((P after e \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after e))\<close> for s X
    apply (simp add: F_After ready_set_Sync ready_hyps After_BOT F_UU
                     Sync_commute[of \<bottom>, simplified Sync_BOT] Sync_BOT Ndet_id)
    apply (intro conjI impI)
      apply ((metis butlast.simps(2) event.simps(3) front_tickFree_butlast tickFree_Cons
                    front_tickFree_single is_processT2 list.distinct(1) list.sel(1, 3))+)[2]
    by (simp add: F_Ndet)
       (metis "*" Ndet_commute Sync_commute list.distinct(1) list.sel(1, 3) ready_hyps same_div)
next

  { fix s
    assume assms : \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close> \<open>ev e # s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
    from assms(3) obtain t u r v
      where ** : \<open>front_tickFree v\<close> \<open>tickFree r \<or> v = []\<close> \<open>ev e # s = r @ v\<close>
                 \<open>r setinterleaves ((t, u), insert \<checkmark> (ev ` S))\<close>
                 \<open>t \<in> \<D> P \<and> u \<in> \<T> Q \<or> t \<in> \<D> Q \<and> u \<in> \<T> P\<close> by (simp add: D_Sync) blast
    have *** : \<open>r \<noteq> []\<close> using "**"(4, 5) BOT_iff_D assms(1, 2) empty_setinterleaving by blast
    have \<open>t \<noteq> [] \<and> hd t = ev e \<and> tl r setinterleaves ((tl t, u), insert \<checkmark> (ev ` S)) \<or>
          u \<noteq> [] \<and> hd u = ev e \<and> tl r setinterleaves ((t, tl u), insert \<checkmark> (ev ` S))\<close>
      using **(3, 4) by (cases t; cases u, auto simp add: *** notin split: if_split_asm)
    with "**"(5) have \<open>s \<in> \<D> ((P after e \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after e))\<close>
    proof (elim disjE)
      assume * : \<open>t \<in> \<D> P \<and> u \<in> \<T> Q\<close>
                 \<open>t \<noteq> [] \<and> hd t = ev e \<and> tl r setinterleaves ((tl t, u), insert \<checkmark> (ev ` S))\<close>
      hence \<open>s = tl r @ v \<and> tl t \<in> \<D> (P after e) \<and> u \<in> \<T> Q\<close>
        using "**"(3) "***" ready_hyps(1) apply (simp add: D_After, intro conjI)
          by (metis list.sel(3) tl_append2) blast
      thus \<open>s \<in> \<D> ((P after e \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after e))\<close>
        using "*"(2) "**"(1, 2) tickFree_tl by (simp add: D_Ndet D_Sync) blast
    next
      assume * : \<open>t \<in> \<D> P \<and> u \<in> \<T> Q\<close>
                 \<open>u \<noteq> [] \<and> hd u = ev e \<and> tl r setinterleaves ((t, tl u), insert \<checkmark> (ev ` S))\<close>
      hence \<open>s = tl r @ v \<and> t \<in> \<D> P \<and> tl u \<in> \<T> (Q after e)\<close>
        using "**"(3) ready_hyps(2) "***" apply (simp add: T_After, intro conjI)
        by (metis list.sel(3) tl_append2) blast
      thus \<open>s \<in> \<D> ((P after e \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after e))\<close>
        using "*"(2) "**"(1, 2) tickFree_tl by (simp add: D_Ndet D_Sync) blast
    next
      assume * : \<open>t \<in> \<D> Q \<and> u \<in> \<T> P\<close>
                 \<open>t \<noteq> [] \<and> hd t = ev e \<and> tl r setinterleaves ((tl t, u), insert \<checkmark> (ev ` S))\<close>
      hence \<open>s = tl r @ v \<and> tl t \<in> \<D> (Q after e) \<and> u \<in> \<T> P\<close>
        using "**"(1, 2, 3) ready_hyps apply (simp add: D_After, intro conjI)
        by (metis "***" list.sel(3) tl_append2) blast
      thus \<open>s \<in> \<D> ((P after e \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after e))\<close>
        using "*"(2) "**"(1, 2) tickFree_tl by (simp add: D_Ndet D_Sync) blast
    next
      assume * : \<open>t \<in> \<D> Q \<and> u \<in> \<T> P\<close>
                 \<open>u \<noteq> [] \<and> hd u = ev e \<and> tl r setinterleaves ((t, tl u), insert \<checkmark> (ev ` S))\<close>
      hence \<open>s = tl r @ v \<and> t \<in> \<D> Q \<and> tl u \<in> \<T> (P after e)\<close>
        using "**"(1, 2, 3) ready_hyps apply (simp add: T_After, intro conjI)
        by (metis "***" list.sel(3) tl_append2) blast
      thus \<open>s \<in> \<D> ((P after e \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after e))\<close>
        using "*"(2) "**"(1, 2) tickFree_tl by (simp add: D_Ndet D_Sync) blast
    qed
  } note * = this

  show \<open>s \<in> \<D> ((P \<lbrakk>S\<rbrakk> Q) after e) \<Longrightarrow> s \<in> \<D> ((P after e \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after e))\<close> for s
     apply (simp add: D_After ready_set_Sync ready_hyps After_BOT D_UU
              split: if_split_asm)
     apply (erule disjE;
            simp add: After_BOT Sync_commute[of \<bottom>, simplified Sync_BOT] Sync_BOT Ndet_id D_UU,
            metis butlast_tl front_tickFree_butlast tickFree_tl)
    by (metis "*" list.collapse)
next

  { fix s P Q
    assume assms : \<open>P \<noteq> \<bottom>\<close> \<open>Q \<noteq> \<bottom>\<close> \<open>s \<in> \<D> ((P after e \<lbrakk>S\<rbrakk> Q))\<close> \<open>ev e \<in> ready_set P\<close>
    from assms(3)[simplified D_Sync, simplified] obtain t u r v
      where * : \<open>front_tickFree v\<close> \<open>tickFree r \<or> v = []\<close> \<open>s = r @ v\<close> 
                \<open>r setinterleaves ((t, u), insert \<checkmark> (ev ` S))\<close>
                \<open>ev e # t \<in> \<D> P \<and> u \<in> \<T> Q \<or> t \<in> \<D> Q \<and> ev e # u \<in> \<T> P\<close>
      by (simp add: D_Sync D_After T_After assms(4)) (metis list.collapse)
    from "*"(5) have \<open>ev e # s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
    proof (elim disjE)
      assume ** : \<open>ev e # t \<in> \<D> P \<and> u \<in> \<T> Q\<close>
      have *** : \<open>(ev e # r) setinterleaves ((ev e # t, u), insert \<checkmark> (ev ` S))\<close>
        using "*"(4) by (cases u; simp add: notin image_iff "*"(1, 2, 3))
      show \<open>ev e # s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
        by (simp add: D_Sync)
           (metis "*"(1, 2, 3) "**" "***" Cons_eq_appendI event.distinct(1) tickFree_Cons)
    next
      assume ** : \<open>t \<in> \<D> Q \<and> ev e # u \<in> \<T> P\<close>
      have *** : \<open>(ev e # r) setinterleaves ((t, ev e # u), insert \<checkmark> (ev ` S))\<close>
        using "*"(4) by (cases t; simp add: notin image_iff "*"(1, 2, 3))
      show \<open>ev e # s \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
        by (simp add: D_Sync)
           (metis "*"(1, 2, 3) "**" "***" Cons_eq_appendI event.distinct(1) tickFree_Cons)
    qed
  } note * = this 

  show \<open>s \<in> \<D> ((P after e \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after e)) \<Longrightarrow> s \<in> \<D> ((P \<lbrakk>S\<rbrakk> Q) after e)\<close> for s
    apply (simp add: D_After ready_set_Sync ready_hyps After_BOT D_UU
                     Sync_commute[of \<bottom>, simplified Sync_BOT] Sync_BOT notin Ndet_id)
    apply (intro conjI impI)
      apply ((metis D_imp_front_tickFree butlast.simps(2) event.distinct(1) tickFree_Cons
                    front_tickFree_single list.discI list.sel(1, 3) front_tickFree_butlast)+)[2]
    by (simp add: D_Ndet)
       (metis "*" list.distinct(1) list.sel(1, 3) mono_D_Sync ready_hyps)
qed


lemma not_readyL_not_readyR_After_Sync: \<open>(P \<lbrakk>S\<rbrakk> Q) after e = STOP\<close> 
  if ready_hyps: \<open>ev e \<notin> ready_set P\<close> \<open>ev e \<notin> ready_set Q\<close>
  apply (subst not_ready_After, simp add: ready_set_Sync)
  using ready_set_BOT ready_hyps by auto


text \<open>Finally, the monster theorem !\<close>

theorem After_Sync: 
  \<open>(P \<lbrakk>S\<rbrakk> Q) after e =
   (        if P = \<bottom> \<or> Q = \<bottom> then \<bottom> 
     else   if ev e \<in> ready_set P \<and> ev e \<in> ready_set Q
          then   if e \<in> S then P after e \<lbrakk>S\<rbrakk> Q after e 
               else (P after e \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after e)
     else   if e \<in> S then STOP
     else   if ev e \<in> ready_set P then P after e \<lbrakk>S\<rbrakk> Q
     else   if ev e \<in> ready_set Q then P \<lbrakk>S\<rbrakk> Q after e
     else STOP)\<close>
  by (simp add: Sync_commute[of \<bottom>, simplified Sync_BOT] Sync_BOT After_BOT
                readyL_readyR_in_After_Sync readyL_readyR_not_in_After_Sync
                not_readyL_in_After_Sync readyL_not_readyR_not_in_After_Sync 
                not_readyL_not_readyR_After_Sync)
     (metis Sync_commute not_readyL_in_After_Sync readyL_not_readyR_not_in_After_Sync)



subsection \<open>@{const [source] After} Hiding Operator\<close>

text \<open>\<^term>\<open>P \ A\<close> is harder to deal with, we will only obtain refinements results.\<close>

lemma Hiding_FD_Hiding_After_if_ready_inside:
      \<open>e \<in> B \<Longrightarrow> (P \ B) \<sqsubseteq>\<^sub>F\<^sub>D (P after e \ B)\<close>
  and After_Hiding_FD_Hiding_After_if_ready_notin:
      \<open>e \<notin> B \<Longrightarrow> (P \ B) after e \<sqsubseteq>\<^sub>F\<^sub>D (P after e \ B)\<close>
  if ready: \<open>ev e \<in> ready_set P\<close>
  supply ready' = ready_notin_imp_ready_Hiding[OF ready]
proof -
  { fix s
    assume \<open>s \<in> \<D> (P after e \ B)\<close>
    with D_Hiding obtain t u 
      where * : \<open>front_tickFree u\<close> \<open>tickFree t\<close> \<open>s = trace_hide t (ev ` B) @ u\<close> 
                \<open>t \<in> \<D> (P after e) \<or> (\<exists> f. isInfHiddenRun f (P after e) B \<and> t \<in> range f)\<close> 
      by blast
    from "*"(4) have \<open>s \<in> (if e \<in> B then \<D> (P \ B) else \<D> ((P \ B) after e))\<close>
    proof (elim disjE)
      assume \<open>t \<in> \<D> (P after e)\<close>
      hence ** : \<open>ev e # t \<in> \<D> P\<close> by (simp add: D_After ready) (metis list.exhaust_sel)
      show  \<open>s \<in> (if e \<in> B then \<D> (P \ B) else \<D> ((P \ B) after e))\<close>
      proof (split if_split, intro conjI impI)
        assume \<open>e \<in> B\<close>
        with "*"(3) have *** : \<open>s = trace_hide (ev e # t) (ev ` B) @ u\<close> by simp
        show \<open>s \<in> \<D> (P \ B)\<close>
          by (simp add: D_Hiding)
             (metis "*"(1, 2) "**" "***" event.distinct(1) tickFree_Cons)
      next
        assume \<open>e \<notin> B\<close>
        with "*"(3) have *** : \<open>ev e # s = trace_hide (ev e # t) (ev ` B) @ u\<close>
          by (simp add: image_iff)
        have \<open>ev e # s \<in> \<D> (P \ B)\<close>
          by (simp add: D_Hiding)
             (metis "*"(1, 2) "**" "***" event.distinct(1) tickFree_Cons)
        thus \<open>s \<in> \<D> ((P \ B) after e)\<close>
          by (simp add: D_After ready' \<open>e \<notin> B\<close>)
             (metis list.distinct(1) list.sel(1, 3))
      qed
    next
      assume \<open>\<exists>f. isInfHiddenRun f (P after e) B \<and> t \<in> range f\<close>
      then obtain f where \<open>isInfHiddenRun f (P after e) B\<close> \<open>t \<in> range f\<close> by blast
      hence ** : \<open>isInfHiddenRun (\<lambda>i. ev e # f i) P B \<and>
                  ev e # t \<in> range (\<lambda>i. ev e # f i)\<close>
        by (simp add: less_cons monotone_on_def T_After ready)
           (metis list.exhaust_sel rangeE rangeI)       
      show \<open>s \<in> (if e \<in> B then \<D> (P \ B) else \<D> ((P \ B) after e))\<close>
      proof (split if_split, intro conjI impI)
        assume \<open>e \<in> B\<close>
        with "*"(3) have *** : \<open>s = trace_hide (ev e # t) (ev ` B) @ u\<close> by simp
        show \<open>s \<in> \<D> (P \ B)\<close>
          by (simp add: D_Hiding)
             (metis "*"(1, 2) "**" "***" event.distinct(1) tickFree_Cons)
      next
        assume \<open>e \<notin> B\<close>
        with "*"(3) have *** : \<open>ev e # s = trace_hide (ev e # t) (ev ` B) @ u\<close>
          by (simp add: image_iff)
        have \<open>ev e # s \<in> \<D> (P \ B)\<close>
          by (simp add: D_Hiding)
             (metis "*"(1, 2) "**" "***" event.distinct(1) tickFree_Cons)
        thus \<open>s \<in> \<D> ((P \ B) after e)\<close>
          by (simp add: D_After ready' \<open>e \<notin> B\<close>)
             (metis list.distinct(1) list.sel(1, 3))
      qed
    qed
  } note div_ref = this

  { fix s X
    assume \<open>(s, X) \<in> \<F> (P after e \ B)\<close>
    with F_Hiding D_Hiding consider 
        \<open>\<exists>t. s = trace_hide t (ev ` B) \<and> (t, X \<union> ev ` B) \<in> \<F> (P after e)\<close> 
      | \<open>s \<in> \<D> (P after e \ B)\<close> by blast
    hence \<open>(s, X) \<in> (if e \<in> B then \<F> (P \ B) else \<F> ((P \ B) after e))\<close>
    proof cases
      assume \<open>\<exists>t. s = trace_hide t (ev ` B) \<and> (t, X \<union> ev ` B) \<in> \<F> (P after e)\<close>
      then obtain t where * : \<open>s = trace_hide t (ev ` B)\<close> \<open>(ev e # t, X \<union> ev ` B) \<in> \<F> P\<close>
        by (simp add: F_After ready) (metis list.exhaust_sel)
      show \<open>(s, X) \<in> (if e \<in> B then \<F> (P \ B) else \<F> ((P \ B) after e))\<close>
      proof (split if_split, intro conjI impI)
        from "*" show \<open>e \<in> B \<Longrightarrow> (s, X) \<in> \<F> (P \ B)\<close>
          by (simp add: F_Hiding) (metis filter.simps(2) image_eqI)
      next
        assume \<open>e \<notin> B\<close>
        with "*"(1) have ** : \<open>ev e # s = trace_hide (ev e # t) (ev ` B)\<close>
          by (simp add: image_iff)
        show \<open>(s, X) \<in> \<F> ((P \ B) after e)\<close>
          by (simp add: F_After ready' \<open>e \<notin> B\<close> F_Hiding)
             (metis "*"(2) "**" list.discI list.sel(1, 3)) 
      qed
    next
      show \<open>s \<in> \<D> (P after e \ B) \<Longrightarrow> (s, X) \<in> (if e \<in> B then \<F> (P \ B) else \<F> ((P \ B) after e))\<close>
        by (drule div_ref, simp split: if_split_asm; use NF_ND in blast)
    qed 
  } note fail_ref = this

  show \<open>e \<in> B \<Longrightarrow> (P \ B) \<sqsubseteq>\<^sub>F\<^sub>D (P after e \ B)\<close>
   and \<open>e \<notin> B \<Longrightarrow> (P \ B) after e \<sqsubseteq>\<^sub>F\<^sub>D (P after e \ B)\<close>
    unfolding failure_divergence_refine_def le_ref_def using div_ref fail_ref by auto
qed


lemmas Hiding_F_Hiding_After_if_ready_inside = 
       Hiding_FD_Hiding_After_if_ready_inside[THEN leFD_imp_leF]
   and After_Hiding_F_Hiding_After_if_ready_notin = 
       After_Hiding_FD_Hiding_After_if_ready_notin[THEN leFD_imp_leF]
   and Hiding_D_Hiding_After_if_ready_inside = 
       Hiding_FD_Hiding_After_if_ready_inside[THEN leFD_imp_leD]
   and After_Hiding_D_Hiding_After_if_ready_notin = 
       After_Hiding_FD_Hiding_After_if_ready_notin[THEN leFD_imp_leD]
   and Hiding_T_Hiding_After_if_ready_inside = 
       Hiding_FD_Hiding_After_if_ready_inside[THEN leFD_imp_leF, THEN leF_imp_leT]   
   and After_Hiding_T_Hiding_After_if_ready_notin = 
       After_Hiding_FD_Hiding_After_if_ready_notin[THEN leFD_imp_leF, THEN leF_imp_leT]

corollary Hiding_DT_Hiding_After_if_ready_inside:
  \<open>ev e \<in> ready_set P \<Longrightarrow> e \<in> B \<Longrightarrow> (P \ B) \<sqsubseteq>\<^sub>D\<^sub>T (P after e \ B)\<close>
  and After_Hiding_DT_Hiding_After_if_ready_notin: 
  \<open>ev e \<in> ready_set P \<Longrightarrow> e \<notin> B \<Longrightarrow> (P \ B) after e \<sqsubseteq>\<^sub>D\<^sub>T (P after e \ B)\<close>
  by (simp add: Hiding_D_Hiding_After_if_ready_inside 
                Hiding_T_Hiding_After_if_ready_inside leD_leT_imp_leDT)
     (simp add: After_Hiding_D_Hiding_After_if_ready_notin 
                After_Hiding_T_Hiding_After_if_ready_notin leD_leT_imp_leDT)


text \<open>This is the best we can obtain: even by restricting ourselves to two events, 
      we can already construct a counterexample.\<close>

lemma defines P_def: \<open>P \<equiv> (Suc 0 \<rightarrow> (0 \<rightarrow> STOP)) \<sqinter> (0 \<rightarrow> SKIP)\<close> 
          and B_def: \<open>B \<equiv> {Suc 0}\<close> and e_def : \<open>e \<equiv> 0\<close> and f_def: \<open>f \<equiv> Suc 0\<close>
        shows \<open>ev e \<in> ready_set P \<and> f \<in> B \<and> P \ B \<noteq> P after f \ B\<close>
          and \<open>ev e \<in> ready_set P \<and> e \<notin> B \<and> (P \ B) after e \<noteq> P after e \ B\<close> 
  unfolding e_def f_def P_def B_def
  apply (simp_all add: ready_set_Ndet ready_set_prefix)
  apply (simp_all add: After_Ndet ready_set_prefix After_prefix Hiding_set_SKIP)
  apply (simp_all add: Hiding_Ndet After_Ndet ready_set_prefix After_prefix Hiding_set_SKIP 
                       Hiding_set_STOP no_Hiding_write0 Hiding_write0)
  by (metis After_prefix Ndet_is_STOP_iff SKIP_Neq_STOP write0_Ndet)
     (metis mono_Ndet_FD_right Ndet_commute SKIP_FD_iff SKIP_Neq_STOP STOP_FD_iff)
  


subsection \<open>@{const [source] After} Renaming\<close>

lemma After_Renaming:
  \<open>Renaming P f after e = 
   (if P = \<bottom> then \<bottom> else
    \<sqinter>a \<in> {a. ev a \<in> ready_set P \<and> f a = e}. Renaming (P after a) f)\<close>
   (is \<open>?lhs = (if P = \<bottom> then \<bottom> else ?rhs)\<close>)
  \<comment>\<open>We treat the case \<^term>\<open>P = \<bottom>\<close> separately because the set \<^term>\<open>{a. f a = e}\<close> may
     be empty, which implies \<^term>\<open>?rhs = STOP\<close> while \<^term>\<open>?lhs = \<bottom>\<close>.\<close>

proof (split if_split, intro conjI impI)
  show \<open>P = \<bottom> \<Longrightarrow> ?lhs= \<bottom>\<close>
    by (simp add: Renaming_BOT After_BOT GlobalNdet_id)
next
  assume non_BOT: \<open>P \<noteq> \<bottom>\<close>
  show \<open>?lhs = ?rhs\<close>
  proof (subst Process_eq_spec_optimized, safe)
    fix s
    assume \<open>s \<in> \<D> ?lhs\<close>
    hence * : \<open>ev e \<in> ready_set (Renaming P f)\<close> \<open>ev e # s \<in> \<D> (Renaming P f)\<close>
      by (auto simp add: D_After split: if_split_asm) (metis list.exhaust_sel)
    from "*"(2) obtain t1 t2
      where ** : \<open>tickFree t1\<close> \<open>front_tickFree t2\<close>
                 \<open>ev e # s = map (EvExt f) t1 @ t2\<close> \<open>t1 \<in> \<D> P\<close>
      by (simp add: D_Renaming) blast
    from "**"(1, 3, 4) non_BOT obtain a t1'
      where *** : \<open>t1 = ev a # t1'\<close> \<open>f a = e\<close>
      by (cases t1; simp add: BOT_iff_D EvExt_def)
         (metis comp_apply event.exhaust event.inject event.simps(4))
    have \<open>ev a \<in> ready_set P\<close>
      using "**"(4) "***"(1) Cons_in_T_imp_elem_ready_set D_T by blast
    also have \<open>s \<in> \<D> (Renaming (P after a) f)\<close>
      using "**" "***"(1) by (simp add: D_Renaming D_After calculation)
                             (metis list.discI list.sel(1, 3))
    ultimately show \<open>s \<in> \<D> ?rhs\<close>
      using "***"(2) by (simp add: D_GlobalNdet) blast
  next
    show \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ?lhs\<close> for s
      apply (simp add: D_GlobalNdet D_Renaming D_After 
                       ready_set_Renaming non_BOT EvExt_def image_iff
                split: if_split_asm event.split, intro conjI)
      by (metis (no_types, lifting) Nil_is_append_conv event.distinct(1) 
          hd_append2 hd_map_EvExt list.collapse list.map_disc_iff 
          map_tl tickFree_Cons tl_append2) blast
  next
    fix s X
    assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
    assume \<open>(s, X) \<in> \<F> ?lhs\<close>
    then consider \<open>ev e \<notin> ready_set (Renaming P f)\<close> \<open>s = []\<close>
      | \<open>ev e \<in> ready_set (Renaming P f)\<close> \<open>(ev e # s, X) \<in> \<F> (Renaming P f)\<close>
      by (simp add: F_After split: if_split_asm) (metis list.exhaust_sel)
    thus \<open>(s, X) \<in> \<F> ?rhs\<close>
    proof cases
      show \<open>ev e \<notin> ready_set (Renaming P f) \<Longrightarrow> s = [] \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
        by (simp add: ready_set_Renaming non_BOT F_GlobalNdet F_Renaming F_After)
           (metis ev_elem_anteced1 imageI vimage_eq)
    next
      assume assms : \<open>ev e \<in> ready_set (Renaming P f)\<close>
                     \<open>(ev e # s, X) \<in> \<F> (Renaming P f)\<close>
      from assms(2) consider \<open>ev e # s \<in> \<D> (Renaming P f)\<close>
        | \<open>\<exists>s1. (s1, EvExt f -` X) \<in> \<F> P \<and> ev e # s = map (EvExt f) s1\<close>
        by (simp add: F_Renaming D_Renaming) blast
      thus \<open>(s, X) \<in> \<F> ?rhs\<close>
      proof cases
        assume \<open>ev e # s \<in> \<D> (Renaming P f)\<close>
        hence \<open>s \<in> \<D> ?lhs\<close> by (force simp add: D_After assms(1))
        with D_F same_div show \<open>(s, X) \<in> \<F> ?rhs\<close> by blast
      next
        assume \<open>\<exists>s1. (s1, EvExt f -` X) \<in> \<F> P \<and> ev e # s = map (EvExt f) s1\<close>
        then obtain s1 where * : \<open>(s1, EvExt f -` X) \<in> \<F> P\<close>
                                 \<open>ev e # s = map (EvExt f) s1\<close> by meson
        from "*"(2) obtain a s1'
          where ** : \<open>s1 = ev a # s1'\<close> \<open>f a = e\<close>
          by (cases s1; simp; metis "*"(2) EvExt_ev1 event.inject 
                                    hd_map_EvExt list.distinct(1) list.sel(1))
        have \<open>ev a \<in> ready_set P\<close>
          using "*"(1) "**"(1) Cons_in_T_imp_elem_ready_set F_T by blast
        also have \<open>(s, X) \<in> \<F> (Renaming (P after a) f)\<close>
          using "*"(1, 2) "**"(1) by (simp add: F_Renaming F_After calculation)
                                     (metis list.distinct(1) list.sel(1, 3))
        ultimately show \<open>(s, X) \<in> \<F> ?rhs\<close>
          using "**"(2) by (simp add: F_GlobalNdet) blast
      qed
    qed
  next
    fix s X
    assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
    assume \<open>(s, X) \<in> \<F> ?rhs\<close>    
    then consider \<open>\<forall>a. ev a \<in> ready_set P \<longrightarrow> f a \<noteq> e\<close> \<open>s = []\<close>
      | \<open>\<exists>a. f a = e \<and> ev a \<in> ready_set P \<and> (s, X) \<in> \<F> (Renaming (P after a) f)\<close>
      by (auto simp add: F_GlobalNdet split: if_split_asm)
    thus \<open>(s, X) \<in> \<F> ?lhs\<close>
    proof cases
      show \<open>\<forall>a. ev a \<in> ready_set P \<longrightarrow> f a \<noteq> e \<Longrightarrow> s = [] \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
        by (auto simp add: F_After F_Renaming ready_set_Renaming non_BOT)
           (metis (no_types, opaque_lifting) EvExt_ev1 event.inject 
                  hd_map_EvExt list.distinct(1) list.sel(1) list.simps(9))
    next
      assume \<open>\<exists>a. f a = e \<and> ev a \<in> ready_set P \<and> 
                  (s, X) \<in> \<F> (Renaming (P after a) f)\<close>
      then obtain a 
        where * : \<open>f a = e\<close> \<open>ev a \<in> ready_set P\<close> 
                  \<open>(s, X) \<in> \<F> (Renaming (P after a) f)\<close> by blast
      from "*"(3) consider \<open>s \<in> \<D> (Renaming (P after a) f)\<close>
        | \<open>\<exists>s1. (s1, EvExt f -` X) \<in> \<F> (P after a) \<and> s = map (EvExt f) s1\<close>
        by (simp add: F_Renaming D_Renaming) blast
      thus \<open>(s, X) \<in> \<F> ?lhs\<close>
      proof cases
        assume \<open>s \<in> \<D> (Renaming (P after a) f)\<close>
        with "*"(1, 2) have \<open>s \<in> \<D> ?rhs\<close> by (simp add: D_GlobalNdet) blast
        with D_F same_div show \<open>(s, X) \<in> \<F> ?lhs\<close> by blast
      next
        assume \<open>\<exists>s1. (s1, EvExt f -` X) \<in> \<F> (P after a) \<and> s = map (EvExt f) s1\<close>
        then obtain s1 where ** : \<open>(s1, EvExt f -` X) \<in> \<F> (P after a)\<close>
                                  \<open>s = map (EvExt f) s1\<close> by blast
        with "*"(1) have *** : \<open>ev e \<notin> ready_set (Renaming P f) \<Longrightarrow> s = []\<close>
          by (simp add: ready_set_Renaming non_BOT image_iff F_After 
                 split: if_split_asm) (metis hd_map hd_map_EvExt)
        { assume \<open>ev e \<in> ready_set (Renaming P f)\<close>
          hence \<open>(ev a # s1, EvExt f -` X) \<in> \<F> P \<and> ev e # s = map (EvExt f) (ev a # s1)\<close>
            using "*"(1, 2) "**" by (simp add: F_After "*"(2))
                                    (metis hd_map hd_map_EvExt list.collapse)
          hence \<open>(ev e # s, X) \<in> \<F> (Renaming P f)\<close>
            by (auto simp add: F_Renaming)
        }
        thus \<open>(s, X) \<in> \<F> ?lhs\<close>
          by (simp add: F_After "***") (metis list.discI list.sel(1, 3))
      qed
    qed
  qed
qed



section \<open>Behaviour of @{const [source] After} with Operators of \<^session>\<open>HOL-CSPM\<close>\<close>

lemma After_MultiDet_is_After_MultiNdet: 
  \<open>finite A \<Longrightarrow> (\<^bold>\<box> a \<in> A. P a) after e = (\<Sqinter> a \<in> A. P a) after e\<close>
  apply (cases \<open>A = {}\<close>, simp)
  apply (rotate_tac, induct rule: finite_set_induct_nonempty, simp)
  by (simp add: After_Det_is_After_Ndet After_Ndet 
                ready_set_MultiDet ready_set_MultiNdet)


lemma After_GlobalNdet: \<open>(\<sqinter> a \<in> A. P a) after e = 
                         (  if ev e \<notin> (\<Union>a \<in> A. ready_set (P a)) then STOP
                          else (\<sqinter> a \<in> {a \<in> A. ev e \<in> ready_set (P a)}. P a) after e)\<close>
  apply (subst Process_eq_spec, auto simp add: not_ready_After ready_set_GlobalNdet)
     apply (auto simp add: F_After F_GlobalNdet D_After D_GlobalNdet ready_set_GlobalNdet
                    split: if_split_asm, 
            auto simp add: ready_set_def)
  by (metis F_T append_Cons append_Nil is_processT3_ST list.exhaust list.sel(1))
     (metis D_T append_Cons append_Nil hd_Cons_tl is_processT3_ST)


lemma After_MultiNdet: \<open>finite A \<Longrightarrow> (\<Sqinter> a \<in> A. P a) after e = 
                        (  if ev e \<notin> (\<Union>a \<in> A. ready_set (P a)) then STOP
                         else (\<Sqinter> a \<in> {a \<in> A. ev e \<in> ready_set (P a)}. P a) after e)\<close>
  by (subst (1 2) finite_GlobalNdet_is_MultiNdet[symmetric], simp_all add: After_GlobalNdet)


lemma After_MultiDet: \<open>finite A \<Longrightarrow> 
                       (\<^bold>\<box> a \<in> A. P a) after e = 
                       (  if ev e \<notin> (\<Union>a \<in> A. ready_set (P a)) then STOP
                        else (\<Sqinter> a \<in> {a \<in> A. ev e \<in> ready_set (P a)}. P a) after e)\<close>
  by (simp add: After_MultiDet_is_After_MultiNdet After_MultiNdet)


(* TODO: formulate and prove for MultiSync and MultiSeq *)



section \<open>Behaviour of @{const [source] After} with Operators of \<^session>\<open>HOL-CSP_OpSem\<close>\<close>

subsection \<open>@{const [source] After} Sliding\<close>

lemma After_Sliding:
  \<open>P \<rhd> Q after e = 
   (  if ev e \<notin> ready_set P \<and> ev e \<notin> ready_set Q then STOP
    else   if ev e \<in> ready_set P \<and> ev e \<in> ready_set Q then (P after e) \<sqinter> (Q after e)
         else if ev e \<in> ready_set P then P after e else Q after e)\<close>
  by (simp add: Sliding_def After_Ndet After_Det ready_set_Det Ndet_id Ndet_assoc)

text \<open>An interesting corollary is that \<^const>\<open>Sliding\<close> is also
      concerned by the loss of determinism (see @{thm After_Det_is_After_Ndet}).\<close>

lemma After_Sliding_is_After_Ndet: \<open>P \<rhd> Q after e = P \<sqinter> Q after e\<close>
  by (simp add: After_Ndet After_Sliding)



subsection \<open>@{const [source] After} Throwing\<close>

lemma After_Throw: 
  \<open>(P \<Theta> a \<in> A. Q a) after e = 
   (  if P = \<bottom> then \<bottom>
    else   if ev e \<in> ready_set P then   if e \<in> A then Q e
                                 else (P after e) \<Theta> a \<in> A. Q a
         else STOP)\<close>
  (is \<open>?lhs = ?rhs\<close>)
proof -
  have \<open>?lhs = Q e\<close> if \<open>P \<noteq> \<bottom>\<close> and \<open>ev e \<in> ready_set P\<close> and \<open>e \<in> A\<close>
  proof (subst Process_eq_spec, safe)
    fix s
    assume \<open>s \<in> \<D> ?lhs\<close>
    with that(2) have \<open>ev e # s \<in> \<D> (P \<Theta> a \<in> A. Q a)\<close>
      by (simp add: D_After ready_set_Throw) (metis list.exhaust_sel)
    with that(1) show \<open>s \<in> \<D> (Q e)\<close>
      apply (simp add: D_Throw disjoint_iff BOT_iff_D, elim disjE)
      by (metis hd_append2 hd_in_set image_eqI list.sel(1) that(3))
         (metis append_self_conv2 event.inject hd_append2
                hd_in_set image_eqI list.sel(1, 3) that(3))
  next
    have \<open>[ev e] \<in> \<T> P \<and> e \<in> A\<close> using ready_set_def that(2, 3) by blast
    thus \<open>s \<in> \<D> (Q e) \<Longrightarrow> s \<in> \<D> ((P \<Theta> a \<in> A. Q a) after e)\<close> for s
      by (simp add: D_After ready_set_Throw that(2) D_Throw)
         (metis append_Nil empty_set inf_bot_left list.distinct(1) list.sel(1, 3))
  next
    fix s X
    assume \<open>(s, X) \<in> \<F> ?lhs\<close>
    with that(2) have \<open>(ev e # s, X) \<in> \<F> (P \<Theta> a \<in> A. Q a)\<close>
      by (simp add: F_After ready_set_Throw) (metis list.exhaust_sel)
    with that(1, 3) show \<open>(s, X) \<in> \<F> (Q e)\<close>
      apply (simp add: F_Throw image_iff BOT_iff_D, elim disjE)
      by (metis disjoint_iff hd_append2 hd_in_set image_eqI list.sel(1))
         (metis append_Nil event.inject hd_append2 imageI insert_disjoint(2) 
                list.exhaust_sel list.sel(1, 3) list.simps(15))
  next
    have \<open>[ev e] \<in> \<T> P \<and> e \<in> A\<close> using ready_set_def that(2, 3) by blast
    thus \<open>(s, X) \<in> \<F> (Q e) \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for s X
      by (simp add: F_After ready_set_Throw that(2) F_Throw)
         (metis append_Nil empty_set inf_bot_left list.distinct(1) list.sel(1, 3))
  qed

  also have \<open>?lhs = (P after e) \<Theta> a \<in> A. Q a\<close>
    if \<open>P \<noteq> \<bottom>\<close> and \<open>ev e \<in> ready_set P\<close> and \<open>e \<notin> A\<close>
  proof (subst Process_eq_spec_optimized, safe)
    fix s
    assume \<open>s \<in> \<D> ?lhs\<close>
    with that(2) have \<open>ev e # s \<in> \<D> (P \<Theta> a \<in> A. Q a)\<close>
      by (simp add: D_After ready_set_Throw) (metis list.exhaust_sel)
    then consider \<open>\<exists>t1 t2. ev e # s = t1 @ t2 \<and> t1 \<in> \<D> P \<and> tickFree t1 \<and>
                           set t1 \<inter> ev ` A = {} \<and> front_tickFree t2\<close>
      | \<open>\<exists>t1 a t2. ev e # s = t1 @ ev a # t2 \<and> t1 @ [ev a] \<in> \<T> P \<and> 
                   set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> t2 \<in> \<D> (Q a)\<close>
      by (simp add: D_Throw) blast
    thus \<open>s \<in> \<D> ((P after e) \<Theta> a \<in> A. Q a)\<close>
    proof cases
      assume \<open>\<exists>t1 t2. ev e # s = t1 @ t2 \<and> t1 \<in> \<D> P \<and> tickFree t1 \<and>
                      set t1 \<inter> ev ` A = {} \<and> front_tickFree t2\<close>
      then obtain t1 t2
        where * : \<open>ev e # s = t1 @ t2\<close> \<open>t1 \<in> \<D> P\<close> \<open>tickFree t1\<close>
                  \<open>set t1 \<inter> ev ` A = {}\<close> \<open>front_tickFree t2\<close> by blast
      from that(1) "*"(1, 2) BOT_iff_D obtain t1'
        where \<open>t1 = ev e # t1'\<close> by (cases t1) auto
      with "*"(1, 2, 3, 4) have \<open>s = t1' @ t2 \<and> t1' \<in> \<D> (P after e) \<and>
                                 tickFree t1' \<and> set t1' \<inter> ev ` A = {}\<close>
        by (simp add: D_After that(2)) (metis list.discI list.sel(1, 3))
      with "*"(5) show \<open>s \<in> \<D> ((P after e) \<Theta> a \<in> A. Q a)\<close>
        by (auto simp add: D_Throw) 
    next
      assume \<open>\<exists>t1 a t2. ev e # s = t1 @ ev a # t2 \<and> t1 @ [ev a] \<in> \<T> P \<and>
                   set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> t2 \<in> \<D> (Q a)\<close>
      then obtain t1 a t2
        where * : \<open>ev e # s = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close> 
                  \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>t2 \<in> \<D> (Q a)\<close> by blast
      have \<open>e \<noteq> a\<close> using "*"(4) that(3) by blast
      with "*"(1) obtain t1' where ** : \<open>t1 = ev e # t1'\<close> by (cases t1) auto
      with "*"(2) that(2) have \<open>t1' @ [ev a] \<in> \<T> (P after e)\<close>
        by (simp add: T_After) (metis list.distinct(1) list.sel(1, 3))
      thus \<open>s \<in> \<D> ((P after e) \<Theta> a \<in> A. Q a)\<close>
        using "*"(1, 3, 4, 5) "**" by (simp add: D_Throw) blast
    qed
  next
    fix s
    assume \<open>s \<in> \<D> ((P after e) \<Theta> a \<in> A. Q a)\<close>
    then consider \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<D> (P after e) \<and> tickFree t1 \<and>
                           set t1 \<inter> ev ` A = {} \<and> front_tickFree t2\<close>
      | \<open>\<exists>t1 a t2. s = t1 @ ev a # t2 \<and> t1 @ [ev a] \<in> \<T> (P after e) \<and>
                   set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> t2 \<in> \<D> (Q a)\<close>
      by (simp add: D_Throw) blast
    thus \<open>s \<in> \<D> ?lhs\<close>
    proof cases
      assume \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<D> (P after e) \<and> tickFree t1 \<and>
                      set t1 \<inter> ev ` A = {} \<and> front_tickFree t2\<close>
      then obtain t1 t2 
        where * : \<open>s = t1 @ t2\<close> \<open>t1 \<in> \<D> (P after e)\<close> \<open>tickFree t1\<close> 
                  \<open>set t1 \<inter> ev ` A = {}\<close> \<open>front_tickFree t2\<close> by blast
      from "*"(2) that(2) have ** : \<open>ev e # t1 \<in> \<D> P\<close>
        by (simp add: D_After) (metis list.exhaust_sel)
      have *** : \<open>tickFree (ev e # t1) \<and> set (ev e # t1) \<inter> ev ` A = {}\<close>
        by (simp add: image_iff "*"(3, 4) that(3))
      show \<open>s \<in> \<D> ?lhs\<close>
        by (simp add: D_After D_Throw ready_set_Throw that(2))
           (metis "*"(1, 5) "**" "***" Cons_eq_appendI list.discI list.sel(1, 3))
    next
      assume \<open>\<exists>t1 a t2. s = t1 @ ev a # t2 \<and> t1 @ [ev a] \<in> \<T> (P after e) \<and>
                        set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> t2 \<in> \<D> (Q a)\<close>
      then obtain t1 a t2
        where * : \<open>s = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> (P after e)\<close>
                  \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>t2 \<in> \<D> (Q a)\<close> by blast
      from "*"(2) that(2) have ** : \<open>ev e # t1 @ [ev a] \<in> \<T> P\<close>
        by (simp add: T_After) (metis list.exhaust_sel)
      have *** : \<open>set (ev e # t1) \<inter> ev ` A = {}\<close>
        by (simp add: image_iff "*"(3) that(3))
      show \<open>s \<in> \<D> ?lhs\<close>
        by (simp add: D_After D_Throw ready_set_Throw that(2)) 
           (metis "*"(1, 4, 5) "**" "***" Cons_eq_appendI list.discI list.sel(1, 3))
    qed
  next
    fix s X
    assume same_div : \<open>\<D> ?lhs = \<D> (Throw (P after e) A Q)\<close>
    assume \<open>(s, X) \<in> \<F> ?lhs\<close>
    with that(2) have \<open>(ev e # s, X) \<in> \<F> (P \<Theta> a \<in> A. Q a)\<close>
      by (simp add: F_After ready_set_Throw) (metis list.exhaust_sel)
    then consider \<open>ev e # s \<in> \<D> (P \<Theta> a \<in> A. Q a)\<close>
      | \<open>(ev e # s, X) \<in> \<F> P\<close> \<open>set s \<inter> ev ` A = {}\<close>
      | \<open>\<exists>t1 a t2. ev e # s = t1 @ ev a # t2 \<and> t1 @ [ev a] \<in> \<T> P \<and> 
                   set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> (t2, X) \<in> \<F> (Q a)\<close>
      by (simp add: F_Throw D_Throw) blast
    thus \<open>(s, X) \<in> \<F> ((P after e) \<Theta> a \<in> A. Q a)\<close>
    proof cases
      assume \<open>ev e # s \<in> \<D> (P \<Theta> a \<in> A. Q a)\<close>
      hence \<open>s \<in> \<D> ?lhs\<close> by (force simp add: D_After ready_set_Throw that(2))
      with same_div D_F show \<open>(s, X) \<in> \<F> ((P after e) \<Theta> a \<in> A. Q a)\<close> by blast
    next
      show \<open>(ev e # s, X) \<in> \<F> P \<Longrightarrow> set s \<inter> ev ` A = {} \<Longrightarrow>
            (s, X) \<in> \<F> ((P after e) \<Theta> a \<in> A. Q a)\<close>
        by (simp add: F_Throw F_After that(2))
           (metis list.distinct(1) list.sel(1, 3))
    next
      assume \<open>\<exists>t1 a t2. ev e # s = t1 @ ev a # t2 \<and> t1 @ [ev a] \<in> \<T> P \<and>
                        set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> (t2, X) \<in> \<F> (Q a)\<close>
      then obtain t1 a t2
        where * : \<open>ev e # s = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close> 
                  \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>(t2, X) \<in> \<F> (Q a)\<close> by blast
      have \<open>e \<noteq> a\<close> using "*"(4) that(3) by blast
      with "*"(1) obtain t1' where \<open>t1 = ev e # t1'\<close> by (cases t1) auto
      also have \<open>t1' @ [ev a] \<in> \<T> (P after e) \<and> set t1' \<inter> ev ` A = {}\<close>
        using "*"(2, 3) by (simp add: image_iff T_After that(2) calculation)
                           (metis list.distinct(1) list.sel(1, 3))
      ultimately show \<open>(s, X) \<in> \<F> ((P after e) \<Theta> a \<in> A. Q a)\<close>
        using "*"(1, 4, 5) by (simp add: F_Throw) blast
    qed
  next
    fix s X
    assume same_div : \<open>\<D> ?lhs = \<D> (Throw (P after e) A Q)\<close>
    assume \<open>(s, X) \<in> \<F> ((P after e) \<Theta> a \<in> A. Q a)\<close>
    then consider \<open>s \<in> \<D> ((P after e) \<Theta> a \<in> A. Q a)\<close>
      | \<open>(s, X) \<in> \<F> (P after e)\<close> \<open>set s \<inter> ev ` A = {}\<close>
      | \<open>\<exists>t1 a t2. s = t1 @ ev a # t2 \<and> t1 @ [ev a] \<in> \<T> (P after e) \<and>
                   set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> (t2, X) \<in> \<F> (Q a)\<close>
      by (simp add: F_Throw D_Throw) blast
    thus \<open>(s, X) \<in> \<F> ?lhs\<close>
    proof cases
      show \<open>s \<in> \<D> (Throw (P after e) A Q) \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
        using same_div D_F by blast
    next
      assume assms : \<open>(s, X) \<in> \<F> (P after e)\<close> \<open>set s \<inter> ev ` A = {}\<close>
      from assms(2) have * : \<open>set (ev e # s) \<inter> ev ` A = {}\<close>
        by (simp add: image_iff that(3) assms(2))
      from assms(1) have \<open>(ev e # s, X) \<in> \<F> P\<close>
        by (simp add: F_After that(2)) (metis list.exhaust_sel)
      thus \<open>(s, X) \<in> \<F> ?lhs\<close>
        by (simp add: F_After F_Throw ready_set_Throw that(2))
           (metis "*" list.discI list.sel(1, 3))
    next
      assume \<open>\<exists>t1 a t2. s = t1 @ ev a # t2 \<and> t1 @ [ev a] \<in> \<T> (P after e) \<and>
                        set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> (t2, X) \<in> \<F> (Q a)\<close>
      then obtain t1 a t2
        where * : \<open>s = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> (P after e)\<close>
                  \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>(t2, X) \<in> \<F> (Q a)\<close> by blast
      from "*"(2) that(2) have ** : \<open>ev e # t1 @ [ev a] \<in> \<T> P\<close>
        by (simp add: T_After) (metis list.exhaust_sel)
      have *** : \<open>set (ev e # t1) \<inter> ev ` A = {}\<close>
        by (simp add: image_iff "*"(3) that(3))
      from "*"(1, 4, 5) show \<open>(s, X) \<in> \<F> ?lhs\<close>
        by (simp add: F_After F_Throw ready_set_Throw that(2)) 
           (metis  "**" "***" append_Cons list.distinct(1) list.sel(1, 3))
    qed
  qed

  ultimately show \<open>?lhs = ?rhs\<close>
    by (simp add: Throw_BOT After_BOT STOP_iff_T T_After ready_set_Throw)
qed



subsection \<open>@{const [source] After} Interrupting\<close>

theorem After_Interrupt: 
  \<open>(P \<triangle> Q) after e =
   (   if ev e \<in> ready_set P \<and> ev e \<in> ready_set Q 
     then (Q after e) \<sqinter> (P after e \<triangle> Q)
     else    if ev e \<in> ready_set P \<and> ev e \<notin> ready_set Q
           then P after e \<triangle> Q 
           else   if ev e \<notin> ready_set P \<and> ev e \<in> ready_set Q
                then Q after e
                else STOP)\<close>
proof -
  have \<open>(P \<triangle> Q) after e \<sqsubseteq>\<^sub>F\<^sub>D Q after e\<close> if ready: \<open>ev e \<in> ready_set Q\<close>
  proof (unfold failure_divergence_refine_def le_ref_def, safe)
    fix s
    assume \<open>s \<in> \<D> (Q after e)\<close>
    hence \<open>ev e # s \<in> \<D> Q\<close>
      by (simp add: D_After ready) (metis list.exhaust_sel)
    thus \<open>s \<in> \<D> ((P \<triangle> Q) after e)\<close>
      by (simp add: D_After ready ready_set_Interrupt D_Interrupt)
         (metis Nil_elem_T append_Nil list.distinct(1) list.sel(1, 3) tickFree_Nil)
  next
    show \<open>(s, X) \<in> \<F> (Q after e) \<Longrightarrow> (s, X) \<in> \<F> ((P \<triangle> Q) after e)\<close> for s X
      by (simp add: F_After ready_set_Interrupt ready F_Interrupt)
         (metis Nil_elem_T append_Nil tickFree_Nil)
  qed

  moreover have \<open>(P \<triangle> Q) after e \<sqsubseteq>\<^sub>F\<^sub>D P after e \<triangle> Q\<close> if ready: \<open>ev e \<in> ready_set P\<close>
  proof (unfold failure_divergence_refine_def le_ref_def, safe)
    show \<open>s \<in> \<D> (P after e \<triangle> Q) \<Longrightarrow> s \<in> \<D> ((P \<triangle> Q) after e)\<close> for s
      apply (simp add: D_Interrupt D_After ready T_After ready_set_Interrupt,
             elim disjE)
      by blast (metis append_Cons event.simps(3) list.sel(1, 3) neq_Nil_conv tickFree_Cons)
  next
    show \<open>(s, X) \<in> \<F> (P after e \<triangle> Q) \<Longrightarrow> (s, X) \<in> \<F> ((P \<triangle> Q) after e)\<close> for s X
      apply (simp add: F_Interrupt F_After ready ready_set_Interrupt T_After D_After,
             elim disjE)
      by (metis (no_types, opaque_lifting) [[metis_verbose = false]] 
                append_Cons list.distinct(1) event.distinct(1) 
                list.exhaust_sel list.sel(1, 3) tickFree_Cons)+
  qed

  moreover have \<open>Q after e \<sqsubseteq>\<^sub>F\<^sub>D (P \<triangle> Q) after e\<close> if not_ready: \<open>ev e \<notin> ready_set P\<close>
  proof (unfold failure_divergence_refine_def le_ref_def, safe)
    show \<open>s \<in> \<D> ((P \<triangle> Q) after e) \<Longrightarrow> s \<in> \<D> (Q after e)\<close> for s
      by (simp add: D_After not_ready ready_set_Interrupt D_Interrupt
             split: if_split_asm)
         (metis Cons_in_T_imp_elem_ready_set D_T not_ready
                append_Nil hd_append2 list.exhaust_sel)
  next
    show \<open>(s, X) \<in> \<F> ((P \<triangle> Q) after e) \<Longrightarrow> (s, X) \<in> \<F> (Q after e)\<close> for s X
      by (simp add: F_After not_ready ready_set_Interrupt F_Interrupt
             split: if_split_asm, elim exE disjE conjE)
         (metis (no_types, opaque_lifting) [[metis_verbose = false]] 
                Cons_in_T_imp_elem_ready_set F_T NF_ND hd_Cons_tl 
                snoc_eq_iff_butlast append_self_conv2 hd_append2 not_ready)+
  qed

  moreover have \<open>P after e \<triangle> Q \<sqsubseteq>\<^sub>F\<^sub>D (P \<triangle> Q) after e\<close>
    if ready_hyps: \<open>ev e \<in> ready_set P\<close> \<open>ev e \<notin> ready_set Q\<close>
  proof (unfold failure_divergence_refine_def le_ref_def, safe)
    show \<open>s \<in> \<D> ((P \<triangle> Q) after e) \<Longrightarrow> s \<in> \<D> (P after e \<triangle> Q)\<close> for s
      by (simp add: D_After T_After ready_hyps ready_set_Interrupt D_Interrupt)
         (metis tickFree_tl Cons_in_T_imp_elem_ready_set D_T eq_Nil_appendI
                hd_append list.exhaust_sel ready_hyps(2) tl_append_if)
  next
    fix s X
    assume \<open>(s, X) \<in> \<F> ((P \<triangle> Q) after e)\<close>
    with ready_hyps(1) have \<open>(ev e # s, X) \<in> \<F> (P \<triangle> Q)\<close>
      by (simp add: F_After ready_set_Interrupt) (metis list.exhaust_sel)
    thus \<open>(s, X) \<in> \<F> (P after e \<triangle> Q)\<close>
      by (simp add: F_Interrupt F_After D_After T_After ready_hyps, elim disjE)
         (metis (no_types, opaque_lifting) [[metis_verbose = false]] tickFree_tl
                Cons_in_T_imp_elem_ready_set F_T NT_ND append_self_conv2 hd_append
                event.distinct(1) list.sel(1, 3) list.distinct(1) ready_hyps(2) tl_append2)+
  qed
  
  moreover have \<open>(Q after e) \<sqinter> (P after e \<triangle> Q) \<sqsubseteq>\<^sub>F\<^sub>D (P \<triangle> Q) after e\<close>
    if both_ready: \<open>ev e \<in> ready_set P\<close> \<open>ev e \<in> ready_set Q\<close>
  proof (unfold failure_divergence_refine_def le_ref_def, safe)
    fix s
    assume \<open>s \<in> \<D> ((P \<triangle> Q) after e)\<close>
    with both_ready(1) have \<open>ev e # s \<in> \<D> (P \<triangle> Q)\<close>
      by (simp add: D_After ready_set_Interrupt) (metis list.exhaust_sel)
    thus \<open>s \<in> \<D> ((Q after e) \<sqinter> (P after e \<triangle> Q))\<close>
      by (simp add: D_Interrupt D_After T_After D_Ndet both_ready)
         (metis tickFree_tl append_Cons append_Nil
                list.distinct(1) list.exhaust_sel list.sel(1, 3))
  next
    fix s X
    assume \<open>(s, X) \<in> \<F> ((P \<triangle> Q) after e)\<close>
    with both_ready(1) have \<open>(ev e # s, X) \<in> \<F> (P \<triangle> Q)\<close>
      by (simp add: F_After ready_set_Interrupt) (metis list.exhaust_sel)
    thus \<open>(s, X) \<in> \<F> ((Q after e) \<sqinter> (P after e \<triangle> Q))\<close>
      by (simp add: F_Interrupt F_After F_Ndet D_After T_After both_ready, elim disjE)
         (metis (no_types, opaque_lifting) [[metis_verbose = false]]
                event.distinct(1) hd_append2 list.distinct(1) list.sel(1, 3)
                process_charn self_append_conv2 tickFree_tl tl_append2)+
  qed

  ultimately show ?thesis
    by (auto simp add: STOP_FD_iff not_ready_After intro: FD_antisym)
       (metis mono_Ndet_FD FD_antisym Ndet_id)
qed
  


section \<open>Behaviour of @{const [source] After} with Reference Processes\<close>

lemma After_DF: \<open>DF A after e = (if e \<in> A then DF A else STOP)\<close>
  by (subst DF_unfold, subst After_Mndetprefix, simp)

lemma After_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P:
  \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A after e = (if e \<in> A then DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A else STOP)\<close>
  by (subst DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold)
     (simp add: ready_set_SKIP ready_set_Mndetprefix After_Ndet After_Mndetprefix)

lemma After_RUN: \<open>RUN A after e = (if e \<in> A then RUN A else STOP)\<close>
  by (subst RUN_unfold, subst After_Mprefix, simp)

lemma After_CHAOS: \<open>CHAOS A after e = (if e \<in> A then CHAOS A else STOP)\<close>
  by (subst CHAOS_unfold)
     (simp add: After_Ndet ready_set_STOP ready_set_Mprefix After_Mprefix)

lemma After_CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P:
  \<open>CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A after e = (if e \<in> A then CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P A else STOP)\<close>
  by (subst CHAOS\<^sub>S\<^sub>K\<^sub>I\<^sub>P_unfold)
     (simp add: ready_set_Ndet ready_set_STOP ready_set_SKIP 
                ready_set_Mprefix After_Ndet After_Mprefix)



lemma DF_FD_After: \<open>DF A \<sqsubseteq>\<^sub>F\<^sub>D P after e\<close>
  if \<open>DF A \<sqsubseteq>\<^sub>F\<^sub>D P\<close> and \<open>ev e \<in> ready_set P\<close>
proof -
  have \<open>DF A after e \<sqsubseteq>\<^sub>F\<^sub>D P after e\<close> by (rule mono_After_FD[OF that(1)]) 
                                       (use that(2) in \<open>simp add: ready_set_DF image_iff\<close>)
  also have \<open>e \<in> A\<close>
    by (metis After_DF DF_Univ_freeness DF_unfold STOP_FD_iff UNIV_I deadlock_free_def empty_iff 
              mono_After_FD mt_Mndetprefix non_deadlock_free_STOP ready_set_STOP that)
  ultimately show \<open>DF A \<sqsubseteq>\<^sub>F\<^sub>D P after e\<close> by (subst (asm) After_DF, simp split: if_splits)
qed


lemma DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_FD_After: \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A \<sqsubseteq>\<^sub>F\<^sub>D P after e\<close>
  if \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A \<sqsubseteq>\<^sub>F\<^sub>D P\<close> and \<open>ev e \<in> ready_set P\<close>
proof -
  have \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A after e \<sqsubseteq>\<^sub>F\<^sub>D P after e\<close> by (rule mono_After_FD[OF that(1)]) 
                                          (use that(2) in \<open>simp add: ready_set_DF image_iff\<close>)
  also have \<open>e \<in> A\<close> using anti_mono_ready_set_FD ready_set_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P that by fastforce
    
  ultimately show \<open>DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P A \<sqsubseteq>\<^sub>F\<^sub>D P after e\<close> by (subst (asm) After_DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P, simp split: if_splits)
qed
 

text \<open>We have corollaries on \<^const>\<open>deadlock_free\<close> and \<^const>\<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<close>.\<close>

corollary deadlock_free_After:
  \<open>deadlock_free P \<Longrightarrow> 
   deadlock_free (P after e) \<longleftrightarrow> (if ev e \<in> ready_set P then True else False)\<close>
  apply (simp add: non_deadlock_free_STOP not_ready_After)
  unfolding deadlock_free_def by (intro impI DF_FD_After)

corollary deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_After:
  \<open>deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P P \<Longrightarrow> 
   deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P (P after e) \<longleftrightarrow> (if ev e \<in> ready_set P then True else False)\<close>
  apply (simp add: non_deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_STOP not_ready_After)
  unfolding deadlock_free\<^sub>S\<^sub>K\<^sub>I\<^sub>P_FD by (intro impI DF\<^sub>S\<^sub>K\<^sub>I\<^sub>P_FD_After)


end
