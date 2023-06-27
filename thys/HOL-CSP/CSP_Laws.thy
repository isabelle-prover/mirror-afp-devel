(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in  Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Burkhart Wolff, Safouan Taha, Lina Ye, Benoît Ballenghien.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : A Combined CSP Theory
 *
 * Copyright (c) 2009 Université Paris-Sud, France
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


chapter\<open> The "Laws" of CSP \<close>

theory CSP_Laws                                               
  imports Bot Skip Stop Det Ndet Mprefix Mndetprefix Seq Hiding Sync  
          "HOL-Eisbach.Eisbach"
begin 

method exI for y::'a = (rule_tac exI[where x = y])


section\<open> General Laws\<close>

lemma SKIP_Neq_STOP: "SKIP \<noteq> STOP"
  by (auto simp: Process_eq_spec F_SKIP F_STOP D_SKIP D_STOP Un_def)

lemma BOT_less1[simp]: "\<bottom> \<le> (X::'a process)"
  by (simp add: le_approx_implies_le_ref)

lemma BOT_less2[simp]: "BOT \<le> (X::'a process)"
  by simp

section\<open> Deterministic Choice Operator Laws \<close>

lemma mono_Det_FD_onside[simp]: " P \<le> P' \<Longrightarrow> (P \<box> S) \<le> (P' \<box> S)"
  unfolding le_ref_def F_Det D_Det using F_subset_imp_T_subset by blast

lemma mono_Det_FD[simp]: " \<lbrakk>P \<le> P'; S \<le> S'\<rbrakk> \<Longrightarrow> (P \<box> S) \<le> (P' \<box> S')"
  by (metis Det_commute dual_order.trans mono_Det_FD_onside)

lemma mono_Det_ref: " \<lbrakk>P \<sqsubseteq> P'; S \<sqsubseteq> S'\<rbrakk> \<Longrightarrow> (P \<box> S) \<sqsubseteq> (P' \<box> S')"
  using below_trans mono_Det mono_Det_sym by blast

lemma Det_BOT : "(P \<box> \<bottom>) = \<bottom>"
  by (auto simp add:Process_eq_spec D_Det F_Det is_processT2 D_imp_front_tickFree F_UU D_UU) 

lemma Det_STOP: "(P \<box> STOP) = P"
  by (auto simp add: Process_eq_spec D_Det F_Det D_STOP F_STOP T_STOP 
                      Un_def Sigma_def is_processT8 is_processT6_S2)  

lemma Det_id: "(P \<box> P) = P"
  by (auto simp: Process_eq_spec D_Det F_Det Un_def Sigma_def is_processT8 is_processT6_S2)

lemma Det_assoc: "((M \<box> P) \<box> Q) = (M \<box> (P \<box> Q))"
  by (auto simp add: Process_eq_spec D_Det F_Det Un_def Sigma_def T_Det)  


section\<open> NonDeterministic Choice Operator Laws \<close>

lemma mono_Ndet_FD[simp]: " \<lbrakk>P \<le> P'; S \<le> S'\<rbrakk> \<Longrightarrow> (P \<sqinter> S) \<le> (P' \<sqinter> S')"
  by (auto simp: le_ref_def F_Ndet D_Ndet)

lemma mono_Ndet_FD_left[simp]: "P \<le> Q \<Longrightarrow> (P \<sqinter> S) \<le> Q" 
  by (metis D_Ndet F_Ndet dual_order.trans le_ref_def le_sup_iff order_refl)

lemma mono_Ndet_FD_right[simp]: "P \<le> Q \<Longrightarrow> (S \<sqinter> P) \<le> Q" 
  by (metis D_Ndet F_Ndet dual_order.trans le_ref_def le_sup_iff order_refl)

lemma mono_Ndet_ref: " \<lbrakk>P \<sqsubseteq> P'; S \<sqsubseteq> S'\<rbrakk> \<Longrightarrow> (P \<sqinter> S) \<sqsubseteq> (P' \<sqinter> S')"
  using below_trans mono_Ndet mono_Ndet_sym by blast

lemma Ndet_BOT: "(P \<sqinter> \<bottom>) = \<bottom>"
  by (auto simp: Process_eq_spec D_Ndet F_Ndet is_processT2 D_imp_front_tickFree F_UU D_UU)

lemma Ndet_id: "(P \<sqinter> P) = P"
  by (simp_all add: F_Ndet D_Ndet Process_eq_spec)  

lemma Ndet_assoc: "((M \<sqinter> P) \<sqinter> Q) = (M \<sqinter> (P \<sqinter> Q))"
  by (simp_all add: F_Ndet D_Ndet  Process_eq_spec Un_assoc)  

subsection\<open> Multi-Operators laws  \<close>

lemma Det_distrib: "(M \<box> (P \<sqinter> Q)) = ((M \<box> P) \<sqinter> (M \<box> Q))"
  by (auto simp add:  Process_eq_spec F_Det D_Det F_Ndet D_Ndet Un_def T_Ndet)

lemma Ndet_distrib: "(M \<sqinter> (P \<box> Q)) = ((M \<sqinter> P) \<box> (M \<sqinter> Q))"
  by (auto simp add:  Process_eq_spec F_Det D_Det F_Ndet 
                      D_Ndet Un_def T_Ndet is_processT8 is_processT6_S2)

lemma Ndet_FD_Det: "(P \<sqinter> Q) \<le> (P \<box> Q)"
  apply(auto simp add:le_ref_def D_Ndet D_Det F_Ndet F_Det T_Ndet T_Det Ra_def min_elems_def) 
  using is_processT6_S2 NF_ND by blast+


section\<open> Sequence Operator Laws \<close>

subsection\<open>Preliminaries\<close>

definition F_minus_D_Seq where 
    "F_minus_D_Seq P Q \<equiv> {(t, X). (t, X \<union> {tick}) \<in> \<F> P \<and> tickFree t} \<union>
                                {(t, X). \<exists>t1 t2. t = t1 @ t2 \<and> t1 @ [tick] \<in> \<T> P \<and> (t2, X) \<in> \<F> Q}"

lemma F_minus_D_Seq_opt: "(a,b) \<in> \<F>(P \<^bold>; Q) = (a \<in> \<D>(P \<^bold>; Q) \<or> (a,b) \<in> F_minus_D_Seq P Q)"
  by (auto simp add: F_Seq D_Seq F_minus_D_Seq_def)

lemma Process_eq_spec_optimized_Seq : 
"((P \<^bold>; Q) = (U \<^bold>; S)) = (\<D> (P \<^bold>; Q) = \<D> (U \<^bold>; S) \<and> 
                            F_minus_D_Seq P Q \<subseteq> \<F> (U \<^bold>; S) \<and> 
                            F_minus_D_Seq U S \<subseteq> \<F> (P \<^bold>; Q))"
  unfolding Process_eq_spec_optimized[of "(P \<^bold>; Q)" "(U \<^bold>; S)"] 
  by (auto simp:F_minus_D_Seq_opt)

subsection\<open>Laws\<close>

lemma mono_Seq_FD[simp]: " \<lbrakk>P \<le> P'; S \<le> S'\<rbrakk> \<Longrightarrow> (P \<^bold>; S) \<le> (P' \<^bold>; S')"
  apply (auto simp: le_ref_def F_Seq D_Seq)
  by (metis F_subset_imp_T_subset subsetCE)+

lemma mono_Seq_ref: " \<lbrakk>P \<sqsubseteq> P'; S \<sqsubseteq> S'\<rbrakk> \<Longrightarrow> (P \<^bold>; S) \<sqsubseteq> (P' \<^bold>; S')"
  using below_trans mono_Seq mono_Seq_sym by blast

lemma BOT_Seq: "(\<bottom> \<^bold>; P) = \<bottom>"
  apply(auto simp add: Process_eq_spec D_Seq F_Seq front_tickFree_append F_UU D_UU T_UU)
      using front_tickFree_append front_tickFree_implies_tickFree is_processT2 apply blast
     using D_imp_front_tickFree front_tickFree_append front_tickFree_implies_tickFree apply blast
    using front_tickFree_charn tickFree_Nil apply blast
   using D_imp_front_tickFree front_tickFree_append front_tickFree_implies_tickFree apply blast 
  using front_tickFree_Nil tickFree_Nil by blast

lemma Seq_SKIP: "(P \<^bold>; SKIP) = P"
  apply (auto simp add: Process_eq_spec F_Seq D_Seq F_SKIP D_SKIP is_processT7 is_processT8_S 
                        T_F_spec is_processT6_S1)
      apply (meson insertI2 is_processT4 subsetI)
     apply (meson append_T_imp_tickFree is_processT5_S7 non_tickFree_tick not_Cons_self2 tickFree_append)
    using T_F_spec insert_absorb is_processT5_S2 apply fastforce
   apply (metis F_T is_processT nonTickFree_n_frontTickFree)
  by (metis append_Nil2 front_tickFree_mono is_processT nonTickFree_n_frontTickFree not_Cons_self)

lemma SKIP_Seq: "(SKIP \<^bold>; P) = P"
  by (auto simp add: Process_eq_spec D_Seq T_SKIP F_Seq F_SKIP D_SKIP is_processT8_Pair)

lemma STOP_Seq: "(STOP \<^bold>; P) = STOP"
  by (auto simp: Process_eq_spec F_Seq D_Seq F_STOP D_STOP T_STOP Un_def)

subsection\<open> Multi-Operators laws  \<close>

lemma Seq_Ndet_distrR: "((P \<sqinter> Q) \<^bold>; S) = ((P \<^bold>; S) \<sqinter> (Q \<^bold>; S))"
  by (auto simp add: Process_eq_spec D_Seq D_Ndet T_Ndet Un_def F_Seq T_Seq F_Ndet)

lemma Seq_Ndet_distrL: "(P \<^bold>; (Q \<sqinter> S)) = ((P \<^bold>; Q) \<sqinter> (P \<^bold>; S))"
  by (auto simp add: Process_eq_spec D_Seq D_Ndet T_Ndet Un_def F_Seq F_Ndet)

lemma Seq_assoc_D: "\<D> (P \<^bold>; (Q \<^bold>; S)) = \<D> ((P \<^bold>; Q) \<^bold>; S)"
proof(safe, goal_cases)
  case (1 x)
  then show ?case 
    apply(auto simp add:D_Seq T_Seq) 
      using front_tickFree_Nil apply blast
     apply (metis append.assoc append_single_T_imp_tickFree tickFree_append)
    by (metis append.assoc)
next
  case (2 x)
  then show ?case 
  proof(auto simp add:D_Seq T_Seq, goal_cases)
    case (1 t2 t1a t2a)
    then show ?case using front_tickFree_append by fastforce 
  next
    case (2 t1 t2 t1a t2a)
    then obtain t2b where  "t2a = t2b@[tick]"
      by (metis T_nonTickFree_imp_decomp append_single_T_imp_tickFree non_tickFree_tick tickFree_append)
    with 2 show ?case by auto
  next
    case (3 t1 t2 t1a t2a)
    then show ?case by (metis front_tickFree_implies_tickFree process_charn)
  next
    case (4 t1 t2 t1a t2a)
    then obtain t2b where  "t2a = t2b@[tick]" 
      by (metis D_T T_nonTickFree_imp_decomp append_single_T_imp_tickFree non_tickFree_tick tickFree_append)
    with 4 show ?case 
      by (metis D_imp_front_tickFree append.assoc butlast_snoc front_tickFree_implies_tickFree process_charn)
  next
    case (5 t1 t2 t1a t2a)
    then show ?case by (metis front_tickFree_implies_tickFree process_charn)
  next
    case (6 t1 t2 t1a t2a)
    then obtain t2b where  "t2a = t2b@[tick]"
      by (metis D_T T_nonTickFree_imp_decomp append_single_T_imp_tickFree non_tickFree_tick tickFree_append)
    with 6 show ?case
      by (metis D_imp_front_tickFree append.assoc butlast_snoc front_tickFree_implies_tickFree process_charn)
  qed
qed
  
lemma Seq_assoc: "(P \<^bold>; (Q \<^bold>; S)) = ((P \<^bold>; Q) \<^bold>; S)"
proof (auto simp: Process_eq_spec_optimized_Seq Seq_assoc_D, goal_cases)
  case (1 a b)
  then show ?case
  proof(auto simp add:F_minus_D_Seq_def Seq_assoc_D F_minus_D_Seq_opt append_single_T_imp_tickFree del:conjI, 
        goal_cases 11 12)
    case (11 t1 t2)
    then show ?case by (metis (mono_tags, lifting) D_Seq Seq_assoc_D UnCI mem_Collect_eq)
  next
    case (12 t1 t1a t2a)
    hence "(t1 @ t1a) @ [tick] \<in> \<T> (P \<^bold>; Q)" by (auto simp:T_Seq)
    then show ?case
      using 12(2)[rule_format, of "t1@t1a" t2a] 12(4,5,6) by simp
  qed
next
  case (2 a b)
  then show ?case
  proof(auto simp add:F_minus_D_Seq_def Seq_assoc_D F_minus_D_Seq_opt append_single_T_imp_tickFree T_Seq del:conjI, 
      goal_cases 21 22 23 24 25 26)
    case 21
    then show ?case 
      by (metis (mono_tags, lifting) D_Seq UnCI append_Nil2 front_tickFree_Nil mem_Collect_eq)
  next
    case (22 t1 t2 t1a t2a)
    then obtain t2b where  "t2a = t2b@[tick]"
      by (metis T_nonTickFree_imp_decomp append_single_T_imp_tickFree non_tickFree_tick tickFree_append)
    with 22 show ?case using append.assoc butlast_snoc by auto
  next
    case (23 t1 t2 t1a t2a)
    hence "t1 \<in> \<D> (P \<^bold>; (Q \<^bold>; S))" 
      by (simp add:D_Seq) (metis append_Nil2 front_tickFree_implies_tickFree process_charn)
    with 23 Seq_assoc_D show ?case by (metis front_tickFree_implies_tickFree process_charn)
  next
    case (24 t1 t2 t1a t2a)
    then obtain t2b where  "t2a = t2b@[tick]"
      by (metis D_T T_nonTickFree_imp_decomp append_single_T_imp_tickFree non_tickFree_tick tickFree_append)
    with 24 show ?case by (metis D_T append.assoc butlast_snoc)
  next 
    case (25 t1 t2 t1a t2a)
    hence "t1 \<in> \<D> (P \<^bold>; (Q \<^bold>; S))" 
      by (simp add:D_Seq) (metis append_Nil2 front_tickFree_implies_tickFree process_charn)
    with 25 Seq_assoc_D show ?case by (metis front_tickFree_implies_tickFree process_charn)
  next
    case (26 t1 t2 t1a t2a)
    then obtain t2b where  "t2a = t2b@[tick]"
      by (metis D_T T_nonTickFree_imp_decomp append_single_T_imp_tickFree non_tickFree_tick tickFree_append)
    with 26 show ?case by (metis D_T append.assoc butlast_snoc)
  qed
qed


section\<open> The Multi-Prefix Operator Laws \<close>

lemma mono_Mprefix_FD[simp]: "\<forall>x \<in> A. P x \<le> P' x \<Longrightarrow> Mprefix A P \<le> Mprefix A P'"
  by (auto simp: le_ref_def F_Mprefix D_Mprefix) blast+

lemmas mono_Mprefix_ref =  mono_Mprefix0

lemma Mprefix_STOP: "(Mprefix {} P) = STOP"
  by (auto simp:Process_eq_spec F_Mprefix D_Mprefix D_STOP F_STOP)

subsection\<open> Multi-Operators laws  \<close>

lemma Mprefix_Un_distrib: "(Mprefix (A \<union> B) P) = ((Mprefix A P) \<box> (Mprefix B P))"
  apply (unfold Process_eq_spec, rule conjI)
  apply (auto, (elim disjE conjE | simp_all add: F_Det F_Mprefix Un_def image_def)+, auto)
  by (auto simp add: D_Det D_Mprefix Un_def)

lemma Mprefix_Seq: "((Mprefix A P) \<^bold>; Q) = (Mprefix A (\<lambda>x. (P x) \<^bold>; Q))"
proof (unfold Process_eq_spec, rule conjI, rule subset_antisym, goal_cases)
  case 1
  then show ?case   
    apply(unfold split_def F_Seq D_Seq F_Mprefix T_Mprefix D_Mprefix)
    apply(rule subsetI, simp_all, elim disjE conjE exE)
        apply(rule disjI1, simp, meson tickFree_tl)
       apply (rule disjI2, rule conjI, simp) apply auto[1]
      apply (auto simp add:hd_append)[1]
   using tickFree_tl apply fastforce
  by (auto simp add: hd_append)[1]
next
  case 2
  then show ?case 
    apply(unfold split_def F_Seq D_Seq F_Mprefix T_Mprefix D_Mprefix)
    apply(rule subsetI, simp_all, elim disjE conjE exE)
        apply(rule disjI1, simp, blast)
       apply(rule disjI1, metis event.simps(3) list.exhaust_sel tickFree_Cons)
  proof(goal_cases)
    case (1 x a t1 t2)
    then show ?case 
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac x="(ev a)#t1" in exI) 
      using hd_Cons_tl image_iff by fastforce
  next
    case (2 x a t1 t2)
    then show ?case       
      apply(rule_tac disjI2, rule_tac disjI2, rule_tac disjI1, rule_tac x="(ev a)#t1" in exI) 
      using hd_Cons_tl image_iff by fastforce
  next
    case (3 x a t1 t2)
    then show ?case 
      apply(rule_tac disjI2, rule_tac disjI2, rule_tac disjI2, rule_tac x="(ev a)#t1" in exI) 
      using hd_Cons_tl image_iff by fastforce
  qed
next
  case 3
  then show ?case     
    apply (auto simp add: D_Mprefix D_Seq T_Mprefix)
        using tickFree_tl apply blast
       apply (metis event.distinct(1) hd_append image_iff list.sel(1))
      apply (metis event.distinct(1) hd_append list.sel(1) tl_append2)
     apply (metis (no_types, opaque_lifting) append_Cons event.distinct(1) image_eqI list.distinct(1) 
                      list.exhaust_sel list.sel(1) list.sel(3) tickFree_Cons)
    by (metis append_Cons list.exhaust_sel list.sel(1) list.sel(3))
qed

subsection\<open> Derivative Operators laws  \<close>

lemma Mprefix_singl: "(Mprefix {a} P) = (a \<rightarrow> (P a))"
  by (simp add:write0_def Mprefix_def, rule arg_cong[of _ _ "\<lambda>x. Abs_process x"]) fastforce

lemma mono_read_FD: "(\<And>x. P x \<le> Q x) \<Longrightarrow>  (c\<^bold>?x \<rightarrow> (P x)) \<le> (c\<^bold>?x \<rightarrow> (Q x))"
  by (simp add: read_def)

lemma mono_write_FD: "(P \<le> Q) \<Longrightarrow>  (c\<^bold>!x \<rightarrow> P) \<le> (c\<^bold>!x \<rightarrow> Q)"
  by (simp add: write_def)

lemma mono_write0_FD: "P \<le> Q \<Longrightarrow> (a \<rightarrow> P) \<le> (a \<rightarrow> Q)"
  by (simp add: write0_def)

lemma mono_read_ref: "(\<And>x. P x \<sqsubseteq> Q x) \<Longrightarrow>  (c\<^bold>?x \<rightarrow> (P x)) \<sqsubseteq> (c\<^bold>?x \<rightarrow> (Q x))"
  by (simp add: mono_Mprefix0 read_def)
                                         
lemma mono_write_ref: "(P \<sqsubseteq> Q) \<Longrightarrow>  (c\<^bold>!x \<rightarrow> P) \<sqsubseteq> (c\<^bold>!x \<rightarrow> Q)"
  by (simp add: mono_Mprefix0 write_def)

lemma mono_write0_ref: "P \<sqsubseteq> Q \<Longrightarrow> (a \<rightarrow> P) \<sqsubseteq> (a \<rightarrow> Q)"
  by (simp add: mono_Mprefix0 write0_def)

lemma write0_Ndet: "(a \<rightarrow> (P \<sqinter> Q)) = ((a \<rightarrow> P) \<sqinter> (a \<rightarrow> Q))"
  by (auto simp: Process_eq_spec write0_def D_Ndet F_Ndet F_Mprefix D_Mprefix Un_def)

lemma write0_Det_Ndet: "((a \<rightarrow> P) \<box> (a \<rightarrow> Q)) = ((a \<rightarrow> P) \<sqinter> (a \<rightarrow> Q))"
  by (auto simp: Process_eq_spec write0_def D_Ndet F_Ndet F_Det D_Det) (simp add: F_Mprefix)+

lemma Mprefix_Det: \<open>(\<box>e\<in>A \<rightarrow> P e) \<box> (\<box>e\<in>A \<rightarrow> Q e) = \<box>e\<in>A \<rightarrow> (P e \<sqinter> Q e)\<close>
  by (auto simp: Process_eq_spec F_Det D_Det) (auto simp: D_Ndet F_Ndet F_Mprefix D_Mprefix)

section\<open> The Hiding Operator Laws \<close>

subsection\<open> Preliminaries \<close>

lemma elemDIselemHD: \<open>t \<in> \<D> P \<Longrightarrow> trace_hide t (ev ` A) \<in> \<D> (P \ A)\<close>
proof (cases "tickFree t")
  case True
  assume "t \<in> \<D> P"
  with True show ?thesis by (simp add:D_Hiding, rule_tac x=t in exI, rule_tac x="[]" in exI, simp)
next
  case False
  assume a:"t \<in> \<D> P"
  with False obtain t' where "t = t'@[tick]" using D_imp_front_tickFree nonTickFree_n_frontTickFree by blast
  with a show ?thesis apply (auto simp add:D_Hiding, rule_tac x=t' in exI, rule_tac x="[tick]" in exI)  
    by (meson front_tickFree_implies_tickFree front_tickFree_single is_processT)
qed

lemma length_strict_mono: "strict_mono (f::nat \<Rightarrow> 'a list) \<Longrightarrow> length (f i) \<ge> i + length (f 0)"
  apply(induct i, simp)
  by (metis dual_order.trans lessI less_length_mono not_less not_less_eq_eq plus_nat.simps(2) strict_mono_def)

lemma mono_trace_hide: "a \<le> b \<Longrightarrow> trace_hide a (ev ` A) \<le> trace_hide b (ev ` A)"
  by (metis filter_append le_list_def)

lemma mono_constant: 
  assumes "mono (f::nat \<Rightarrow> 'a event list)" and "\<forall>i. f i \<le> a"
  shows "\<exists>i. \<forall>j\<ge>i. f j = f i"
proof -
  from assms(2) have "\<forall>i. length (f i) \<le> length a"
    by (simp add: le_length_mono)
  hence aa:"finite {length (f i)|i. True}" 
    using finite_nat_set_iff_bounded_le by auto
  define lm where l2:"lm = Max {length (f i)|i. True}"
  with aa obtain im where "length (f im) = lm" using Max_in by fastforce
  with l2 assms(1) show ?thesis 
    apply(rule_tac x=im in exI, intro impI allI)
    by (metis (mono_tags, lifting) Max_ge aa antisym le_length_mono le_neq_trans less_length_mono 
              mem_Collect_eq mono_def order_less_irrefl)
qed
  
lemma elemTIselemHT: \<open>t \<in> \<T> P \<Longrightarrow> trace_hide t (ev ` A) \<in> \<T> (P \ A)\<close>
proof (cases "tickFree t")
  case True
  assume a:"t \<in> \<T> P"
  with True show ?thesis
  proof (cases "(\<exists>ta. trace_hide t (ev ` A) = trace_hide ta (ev ` A) \<and> (ta, ev ` A) \<in> \<F> P)")
    case True
    thus ?thesis by (simp add:T_Hiding)
  next
    case False
    with a False inf_hidden[of A t P] obtain f where "isInfHiddenRun f P A \<and> t \<in> range f" by auto
    with True show ?thesis 
      by (simp add:T_Hiding, rule_tac disjI2, rule_tac x=t in exI, rule_tac x="[]" in exI, auto)
  qed
next
  case False
  assume a:"t \<in> \<T> P"
  with False obtain t' where tt:"t = t'@[tick]" using T_nonTickFree_imp_decomp by auto
  with a show ?thesis 
  proof (cases "(\<exists>ta. trace_hide t (ev ` A) = trace_hide ta (ev ` A) \<and> (ta, ev ` A) \<in> \<F> P)")
    case True
    thus ?thesis by (simp add:T_Hiding)
  next
    case False
    assume "t \<in> \<T> P"
    with False inf_hidden[of A t P] obtain f where "isInfHiddenRun f P A \<and> t \<in> range f" by auto
    then show ?thesis 
      apply (simp add:T_Hiding, rule_tac disjI2, rule_tac x=t' in exI, rule_tac x="[tick]" in exI, auto)
        apply (metis append_T_imp_tickFree list.distinct(1) tt)
       using tt apply force
      by (metis False append_T_imp_tickFree is_processT5_S7 non_tickFree_tick not_Cons_self2 tickFree_append tt)
  qed
qed

lemma Hiding_Un_D1: \<open>\<D> (P \ (A \<union> B)) \<subseteq> \<D> ((P \ A) \ B)\<close>
proof (simp add:conj_commute D_Hiding, intro conjI subset_antisym subsetI, simp_all, goal_cases)
  case (1 x)
  then obtain t u where B1:"x = trace_hide t (ev ` (A \<union> B)) @ u" and B2:"tickFree t" and B3:"front_tickFree u" and 
             B4:"(t \<in> \<D> P \<or> (\<exists>(f:: nat \<Rightarrow> 'a event list). isInfHiddenRun f P (A \<union> B) \<and> t \<in> range f))" by auto
  thus ?case
    apply(erule_tac  disjE)
    apply(rule_tac x="trace_hide t (ev ` A)" in exI, rule_tac x=u in exI)
    apply(simp add:Hiding_tickFree tickFree_def)
    apply(rule disjI1, rule_tac x=t in exI, rule_tac x="[]" in exI, simp) 
  proof(goal_cases)
    case 1
    then obtain f n where fc:"isInfHiddenRun f P (A \<union> B) \<and> t = f n" by auto
    define ff where "ff = (\<lambda>i. take (i + length (f 0)) (f i))"
    with fc have ffc:"isInfHiddenRun ff P (A \<union> B) \<and> t \<in> range ff" 
    proof (auto, goal_cases)
      case 1
      { fix x
        from length_strict_mono[of f "Suc x ", OF 1(2)]
        have a:"take (x + length (f 0)) (f (Suc x)) < take ((Suc x) + length (f 0)) (f (Suc x))"
          by (simp add: take_Suc_conv_app_nth)
        from 1(2)[THEN strict_monoD, of x "Suc x", simplified] 
          obtain t where "f (Suc x) = (f x @ t)" by (metis le_list_def less_imp_le)
        with length_strict_mono[of f x, OF 1(2)]
          have "take (x + length (f 0)) (f x) = take (x + length (f 0)) (f (Suc x))" by simp
        with a have "take (x + length (f 0)) (f x) < take (Suc x + length (f 0)) (f (Suc x))" by simp
      }
      thus ?case by (meson lift_Suc_mono_less strict_mono_def)
    next
      case (2 i)
      have "take (i + length (f 0)) (f i) \<le> f i"
        using append_take_drop_id le_list_def by blast
      also have "\<forall>x y. x \<le> y \<and> y \<in> \<T> P \<longrightarrow> x \<in> \<T> P" using is_processT3_ST_pref by blast
      ultimately show ?case using "2"(3) by blast 
    next
      case (3 i)
      hence "(f i) \<ge> (f 0)" using strict_mono_less_eq by blast
      hence "take (i + length (f 0)) (f i) \<ge> (f 0)"
        by (metis add.commute append_eq_conv_conj le_list_def take_add)
      hence a:"[x\<leftarrow>take (i + length (f 0)) (f i) . x \<notin> ev ` A \<and> x \<notin> ev ` B] \<ge> [x\<leftarrow>f 0 . x \<notin> ev ` A \<and> x \<notin> ev ` B]"
        by (metis (no_types, lifting) filter_append le_list_def)
      have "take (i + length (f 0)) (f i) \<le> f i"
        using append_take_drop_id le_list_def by blast
      hence "[x\<leftarrow>take (i + length (f 0)) (f i) . x \<notin> ev ` A \<and> x \<notin> ev ` B] \<le> [x\<leftarrow>f i . x \<notin> ev ` A \<and> x \<notin> ev ` B]"
        by (metis (no_types, lifting) filter_append le_list_def)
      with a 3(4) show ?case by (metis (no_types, lifting) dual_order.antisym)
    next
      case 4
      have "f (length (f n) - length (f 0)) \<ge> f n"
        by (simp add: "4"(2) add_le_imp_le_diff length_strict_mono strict_mono_less_eq)
      hence "f n = (\<lambda>i. take (i + length (f 0)) (f i)) (length (f n) - length (f 0))" 
        by (metis "4"(2) add.commute append_eq_conv_conj diff_is_0_eq' 
                  le_add_diff_inverse le_list_def le_zero_eq nat_le_linear strict_mono_less_eq)
      then show ?case by blast
    qed
    thus ?case proof(cases "\<exists>m. (\<forall>i>m. last (ff i) \<in> (ev ` A))")
      case True
      then obtain m where mc:"\<forall>i>m. last (ff i) \<in> (ev ` A)" by blast
      hence mc2:"tickFree (ff m)" 
        by (metis (no_types, lifting) B2 event.distinct(1) ffc 
                                      image_iff mem_Collect_eq set_filter tickFree_def)
      with mc mc2 1 ffc show ?thesis 
        apply(rule_tac x="trace_hide (ff m) (ev ` A)" in exI, rule_tac x=u in exI, simp, intro conjI)    
        apply (metis (no_types, lifting) mem_Collect_eq set_filter tickFree_def)
        apply (metis (no_types, lifting) rangeE)
        apply(rule disjI1, rule_tac x="ff m" in exI, rule_tac x="[]" in exI, intro conjI, simp_all)
        apply(rule disjI2, rule_tac x="\<lambda>i. ff(i + m)" in exI, intro conjI)
           apply (metis (no_types, lifting) add.commute add.right_neutral rangeI) 
          apply (simp add: strict_mono_def)
         apply blast
        proof(rule allI, goal_cases)
          case (1 i)
          from ffc ff_def True have "\<exists>t. (ff (i + m)) = (ff m) @ t \<and> set t \<subseteq> (ev ` A)" 
          proof(induct i)
            case 0
            then show ?case by fastforce
          next
            case (Suc i)
            then obtain tt where tc:"(ff (i + m)) = (ff m) @ tt \<and> set tt \<subseteq> (ev ` A)" by blast
            from ffc ff_def length_strict_mono[of ff] have lc:"length (ff (Suc i + m)) = Suc (length (ff (i + m)))" 
              by (metis (no_types, lifting) add_Suc fc length_strict_mono length_take min.absorb2)
            from True obtain l where lc2:"l = last (ff (Suc i + m)) \<and> l \<in> (ev ` A)"
              by (meson less_add_same_cancel2 mc zero_less_Suc)
            from ffc obtain r where rc:"ff (Suc i + m) = ff (i + m)@r"
              by (metis add.commute add_Suc_right le_list_def lessI less_imp_le strict_mono_less_eq)
            with lc have "length r = 1" by (metis Suc_eq_plus1 add_left_cancel length_append)
            with rc lc2 have "r = [l]"
              by (metis (no_types, lifting) Nil_is_append_conv Suc_eq_plus1 append_butlast_last_id 
                        append_eq_append_conv append_eq_append_conv2 length_Cons length_append)
            with Suc lc2 tc rc show ?case by (rule_tac x="tt@[l]" in exI, auto) 
          qed
          then show ?case using filter_empty_conv by fastforce
        qed
    next
      case False
      { fix i
        assume as:"(i::nat) > 0"
        with ffc obtain tt where ttc:"ff i = ff 0 @ tt \<and> set tt \<subseteq> ev ` (A \<union> B)" 
          unfolding isInfHiddenRun_1 by blast
        with ffc as have "tt \<noteq> []" using strict_mono_eq by fastforce
        with ttc have "last (ff i) \<in> ev ` (A \<union> B)" by auto
      }
      hence as2:"\<forall>i. \<exists>j>i. last(ff j) \<in> ((ev ` B) - (ev ` A))"
        by (metis DiffI False UnE gr_implies_not_zero gr_zeroI image_Un)
      define ffb where "ffb = rec_nat t (\<lambda>i t. (let j = SOME j. ff j > t \<and> 
                              last(ff j) \<in> ((ev ` B) - (ev ` A)) in ff j))"
      with as2 have ffbff:"\<And>n. ffb n \<in> range ff"
        by (metis (no_types, lifting) ffc old.nat.exhaust old.nat.simps(6) old.nat.simps(7) rangeI)
      from 1 ffb_def show ?thesis
        apply(rule_tac x="trace_hide t (ev ` A)" in exI, rule_tac x=u in exI, simp, intro conjI)
         apply (meson filter_is_subset set_rev_mp tickFree_def)        
      proof(rule disjI2, rule_tac x="\<lambda>i. trace_hide (ffb i) (ev ` A)" in exI, intro conjI, goal_cases)
        case 1
        then show ?case by (metis (no_types, lifting) old.nat.simps(6) rangeI) 
      next
        case 2
        { fix n
          have a0:"(ffb (Suc n)) = ff (SOME j. ff j > ffb n \<and> last(ff j) \<in> ((ev ` B) - (ev ` A)))" 
            by (simp add: ffb_def)
          from ffbff obtain i where a1:"ffb n = ff i" by blast
          with as2 have "\<exists>j. ff j > ffb n \<and> last(ff j) \<in> ((ev ` B) - (ev ` A))"
            by (metis ffc strict_mono_def)
          with a0 a1 have a:"(ffb (Suc n)) > (ffb n) \<and> last (ffb (Suc n)) \<notin> (ev ` A)"
            by (metis (no_types, lifting) Diff_iff tfl_some) 
          then obtain r where  "ffb (Suc n) =  (ffb n)@r \<and> last r \<notin> (ev ` A)"
            by (metis append_self_conv last_append le_list_def less_list_def) 
          hence "trace_hide (ffb (Suc n)) (ev ` A) > trace_hide (ffb n) (ev ` A)"
            by (metis (no_types, lifting) a append_self_conv filter_append filter_empty_conv 
                                          last_in_set le_list_def less_list_def)
        }
        then show ?case by (metis (mono_tags, lifting) lift_Suc_mono_less_iff strict_monoI)
      next
        case 3
        then show ?case by (metis (mono_tags) elemTIselemHT ffbff ffc rangeE)  
      next
        case 4
        from ffbff ffc show ?case by (metis rangeE trace_hide_union)
      qed
    qed
  qed
qed

lemma Hiding_Un_D2: \<open>finite A \<Longrightarrow> \<D> ((P \ A) \ B) \<subseteq> \<D> (P \ (A \<union> B))\<close>
proof (simp add:conj_commute D_Hiding, intro conjI subset_antisym subsetI, simp_all, goal_cases)
  case (1 x)
  then obtain t u where B1:"x = trace_hide t (ev ` B) @ u" 
                   and  B2:"tickFree t" 
                   and  B3:"front_tickFree u" 
                   and  B4:"(t \<in> \<D> (P \\ A) \<or> 
                            (\<exists>(f:: nat \<Rightarrow> 'a event list). isInfHiddenRun f (P \\ A) B \<and> t \<in> range f))" 
    by (simp add:D_Hiding) blast
  thus ?case
  proof(erule_tac disjE, auto simp add:D_Hiding, goal_cases)
    case (1 ta ua)
    then show ?case 
      by (rule_tac x=ta in exI, rule_tac x = "trace_hide ua (ev ` B) @ u" in exI, 
          auto simp add: front_tickFree_append tickFree_def)
  next
    case (2 ua f xa)
    then show ?case 
      apply(rule_tac x="f xa" in exI, rule_tac x="trace_hide ua (ev ` B) @ u" in exI, 
            intro conjI disjI2)
         apply(auto simp add: front_tickFree_append tickFree_def)
      by (rule_tac x="f" in exI) (metis (no_types) filter_filter rangeI)
  next
    case (3 f xx)
    note "3a" = 3
    then show ?case
    proof(cases "\<exists>i. f i \<in> \<D> (P \\ A)")
      case True
      with 3 show ?thesis 
      proof(auto simp add:D_Hiding, goal_cases)
        case (1 i ta ua)
        then show ?case 
        apply (rule_tac x=ta in exI, rule_tac x="trace_hide ua (ev ` B) @ u" in exI, intro conjI)
           apply (metis (full_types) front_tickFree_append Hiding_tickFree tickFree_append)
          apply(subgoal_tac "trace_hide (f xx) (ev ` B) = trace_hide (f i) (ev ` B)", auto)
         apply (metis (full_types) filter_append filter_filter)
        by (metis (full_types) filter_append filter_filter)
      next
        case (2 i ua fa xa)
        hence "trace_hide (f xx) (ev ` B) = trace_hide (f i) (ev ` B)" by metis
        with 2 show ?case
          apply (rule_tac x="fa xa" in exI, rule_tac x="trace_hide ua (ev ` B) @ u" in exI, intro conjI)
             apply (metis (full_types) front_tickFree_append Hiding_tickFree tickFree_append)
            apply (simp_all) 
          apply(rule_tac disjI2, rule_tac x=fa in exI, auto)
          by (metis (no_types) filter_filter)      
      qed
    next
      case False
      with 3 have Falsebis:"\<forall>i. (f i \<in> \<T> (P \\ A) \<and> f i \<notin> \<D> (P \\ A))" by blast
      with T_Hiding[of P A] D_Hiding[of P A] 
      have "\<forall>i. (f i \<in> {trace_hide t (ev ` A) |t. (t, ev ` A) \<in> \<F> P})" 
        by (metis (no_types, lifting) UnE)
      hence ff0:"\<forall>i. (\<exists>t. f i = trace_hide t (ev ` A) \<and> t \<in> \<T> P)" using F_T by fastforce
      define ff where ff1:"ff = (\<lambda>i. SOME t. f i = trace_hide t (ev ` A) \<and> t \<in> \<T> P)"
      hence "inj ff" unfolding inj_def by (metis (mono_tags, lifting) "3"(4) ff0 strict_mono_eq tfl_some)
      hence ff2:"infinite (range ff)" using finite_imageD by blast
      { fix tt i
        assume "tt \<in> range ff"
        then obtain k where "ff k = tt" using finite_nat_set_iff_bounded_le by blast
        hence kk0:"f k = trace_hide tt (ev ` A) \<and> tt \<in> \<T> P" using ff1 
          by (metis (mono_tags, lifting) ff0 someI_ex)
        hence "set (take i tt) \<subseteq> set (f i) \<union> (ev ` A)"
        proof(cases "k \<le> i")
          case True
          hence "set (f k) \<subseteq> set (f i)" 
            by (metis "3"(4) le_list_def set_append strict_mono_less_eq sup.cobounded1)
          moreover from kk0 have "set (take i tt) \<subseteq> set (f k) \<union> (ev ` A)" using in_set_takeD by fastforce
          ultimately show ?thesis by blast
        next
          case False
          have a:"length (f i) \<ge> i" by (meson "3"(4) dual_order.trans le_add1 length_strict_mono)
          have b:"f i \<le> f k" using "3"(4) False nat_le_linear strict_mono_less_eq by blast
          with a have c:"take i (f k) \<le> (f i)"
            by (metis append_eq_conv_conj le_add_diff_inverse le_list_def take_add)
          from kk0[THEN conjunct1] have c1:"f k = (trace_hide (take i tt) (ev ` A)) @
                                                  (trace_hide (drop i tt) (ev ` A))"
            by (metis append_take_drop_id filter_append)
          have "length (trace_hide (take i tt) (ev ` A)) \<le> i"
            by (metis length_filter_le length_take min.absorb2 nat_le_linear order.trans take_all)
          with c1 have "take i (f k) \<ge> (trace_hide (take i tt) (ev ` A))" by (simp add: le_list_def)
          with c obtain t where d:"f i = (trace_hide (take i tt) (ev ` A))@t"
            by (metis append.assoc le_list_def)
          then show ?thesis using in_set_takeD by fastforce
        qed
      } note ee=this
      { fix i
        have "finite {(take i t)|t. t \<in> range ff}" 
        proof(induct i, simp)
          case (Suc i)
          have ff:"{take (Suc i) t|t. t \<in> range ff} \<subseteq> {(take i t)|t. t \<in> range ff} \<union>
                      (\<Union>e\<in>(set (f (Suc i)) \<union> (ev ` A)). {(take i t)@[e]|t. t \<in> range ff})" (is "?AA \<subseteq> ?BB")
            proof
              fix t
              assume "t \<in> ?AA"
              then obtain t' where hh:"t' \<in> range ff \<and> t = take (Suc i) t'" 
                using finite_nat_set_iff_bounded_le by blast
              with ee[of t'] show "t \<in> ?BB"
                proof(cases "length t' > i")
                  case True
                  hence ii:"take (Suc i) t' = take i t' @ [t'!i]" by (simp add: take_Suc_conv_app_nth)
                  with ee[of t' "Suc i"] have "t'!i \<in> set (f (Suc i)) \<union> (ev ` A)" by (simp add: hh)
                  with ii hh show ?thesis by blast
                next
                  case False
                  hence "take (Suc i) t' = take i t'" by fastforce
                  with hh show ?thesis by auto
                qed
            qed
          { fix e 
            have "{x @ [e] |x. \<exists>t. x = take i t \<and> t \<in> range ff} = {take i t' @ [e] |t'. t' \<in> range ff}"
              by auto
            hence "finite({(take i t') @ [e] |t'. t'\<in>range ff})"
              using finite_image_set[of _ "\<lambda>t. t@[e]", OF Suc] by auto 
          } note gg=this
          have "finite(set (f (Suc i)) \<union> (ev ` A))" using 1(1) by simp
          with ff gg Suc show ?case by (metis (no_types, lifting) finite_UN finite_Un finite_subset)
        qed
      } note ff=this
      hence "\<forall>i. {take i t |t. t \<in> range ff} = {t. \<exists>t'. t = take i (ff t')}" by auto
      with KoenigLemma[of "range ff"] ff ff2
      obtain f' where gg:"strict_mono (f':: nat \<Rightarrow> 'a event list) \<and> 
                                            range f' \<subseteq> {t. \<exists>t'\<in>range ff. t \<le> t'}" by auto
      { fix i
        from gg obtain n where aa:"f' i \<le> ff n" by blast
        have "\<exists>t. f n = f 0 @ t" by (metis "3a"(4) le0 le_list_def strict_mono_less_eq)
        with mono_trace_hide[OF aa, of A] ff0 ff1 have "\<exists>t. trace_hide (f' i) (ev ` A) \<le> f 0 @ t" 
          by (metis (mono_tags, lifting) someI_ex)
      } note zz=this
      {
        define ff' where "ff' = (\<lambda>i. trace_hide (f' i) (ev ` A))"
        with gg have "mono ff'"
          by (rule_tac monoI, simp add: mono_trace_hide strict_mono_less_eq)
        assume aa:"\<forall>i. trace_hide (f' i) (ev ` A) \<le> f 0"
        with aa mono_constant have "\<exists>i. \<forall>j\<ge>i. ff' j = ff' i" using \<open>mono ff'\<close> ff'_def by blast
        then obtain m where bb:"\<forall>j\<ge>m. ff' j = ff' m" by blast
        have "ff' m \<in> \<D> (P \\ A)" 
        proof(simp add:D_Hiding, rule_tac x="f' m" in exI, rule_tac x="[]" in exI, intro conjI, simp, goal_cases)
          case 1
          from gg have "f' m < f' (Suc m)" by (meson lessI strict_monoD)
          moreover from gg obtain k where "f' (Suc m) \<le> ff k" by blast
          moreover have "ff k \<in> \<T> P" by (metis (mono_tags, lifting) ff0 ff1 someI_ex)
          ultimately show ?case
          by (metis NF_NT append_Nil2 front_tickFree_mono is_processT le_list_def less_list_def)
        next
          case 2
          then show ?case unfolding ff'_def by simp
        next
          case 3
          then show ?case
          proof(rule disjI2, rule_tac x="\<lambda>i. f' (m + i)" in exI, simp_all, intro conjI allI, goal_cases)
            case 1
            show ?case using gg[THEN conjunct1] 
              by (rule_tac strict_monoI, simp add: strict_monoD) 
          next
            case (2 i)
            from gg obtain k where "f' (m + i) \<le> ff k" by blast
            moreover from ff0 ff1 have "ff k \<in> \<T> P" by (metis (mono_tags, lifting) someI_ex)
            ultimately have "f' (m + i) \<in> \<T> P" using is_processT3_ST_pref by blast
            then show ?case by (simp add: add.commute)
          next
            case (3 i)
            then show ?case using bb[THEN spec, of "m+i", simplified] unfolding ff'_def by assumption
          next
            case 4
            then show ?case by (metis Nat.add_0_right rangeI) 
          qed
        qed 
        with gg False have "False"
          by (metis (no_types, lifting) Falsebis aa append_Nil2 ff'_def front_tickFree_mono 
                                        is_processT is_processT2_TR le_list_def) 
      }
      with zz obtain m where hh:"trace_hide (f' m) (ev ` A) \<ge> f 0"
        unfolding le_list_def by (metis append_eq_append_conv2)
      from ff0 ff1 gg show ?thesis
      proof(auto simp add:T_Hiding, rule_tac x="f' m" in exI, rule_tac x=u in exI, 
                          intro conjI, simp_all add:3(3), goal_cases)
        case 1
        hence "f' m < f' (Suc m)" by (meson lessI strict_monoD)
        moreover from gg obtain k where "f' (Suc m) \<le> ff k" by blast
        moreover have "ff k \<in> \<T> P" by (metis (mono_tags, lifting) ff0 ff1 someI_ex)
        ultimately show ?case
          by (metis NF_NT append_Nil2 front_tickFree_mono is_processT le_list_def less_list_def)
      next
        case 2
        from gg obtain k where "f' m \<le> ff k" by blast
        with ff0 ff1 mono_trace_hide[of "f' m"] have "trace_hide (f' m) (ev ` A) \<le> f k" 
          by (metis (mono_tags, lifting) someI_ex)
        with mono_trace_hide[OF this, of B] mono_trace_hide[OF hh, of B] 3(6)[THEN spec, of k] 3(6)
        show ?case by (metis (full_types) dual_order.antisym filter_filter)
      next
        case 3 show ?case 
        proof(rule disjI2, rule_tac x="\<lambda>i. f' (m + i)" in exI, simp_all, intro conjI allI, goal_cases)
          case 1
          then show ?case by (metis Nat.add_0_right rangeI) 
        next
          case 2 with 3(4) show ?case 
            by (rule_tac strict_monoI, simp add: strict_monoD)
        next
          case (3 i)
          from gg obtain k where "f' (m + i) \<le> ff k" by blast
          moreover from ff0 ff1 have "ff k \<in> \<T> P" by (metis (mono_tags, lifting) someI_ex)
          ultimately have "f' (m + i) \<in> \<T> P" using is_processT3_ST_pref by blast
          then show ?case by (simp add: add.commute)
        next
          case (4 i)
          from gg obtain k where "f' (m + i) \<le> ff k" by blast
          with ff0 ff1 mono_trace_hide[of "f' (m + i)"] have ll:"trace_hide (f' (m + i)) (ev ` A) \<le> f k" 
            by (metis (mono_tags, lifting) someI_ex)
          { fix a b c assume "(a::'a event list) \<le> b" and "b \<le> c" and "c \<le> a" hence "b = c" by auto}
          note jj=this
          from jj[OF mono_trace_hide[OF hh, of B],
                  OF mono_trace_hide[THEN mono_trace_hide, of "f' m" "f' (m + i)" B A, 
                               OF gg[THEN conjunct1, THEN strict_mono_mono, 
                               THEN monoD, of "m" "m+i", simplified]]]
               mono_trace_hide[OF ll, of B]
          show ?case unfolding "3a"(6) [THEN spec, of k] by simp
        qed
      qed
    qed
  qed
qed

lemma Hiding_Un_D: \<open>finite A \<Longrightarrow> \<D> ((P \ A) \ B) = \<D> (P \ (A \<union> B))\<close>
  using Hiding_Un_D1 Hiding_Un_D2 by blast
 
subsection\<open> Laws \<close>

lemma mono_Hiding_FD[simp]: \<open>P \<le> Q \<Longrightarrow> P \ A \<le> Q \ A\<close>
  apply (auto simp: le_ref_def F_Hiding D_Hiding) 
  using F_subset_imp_T_subset by blast+

lemmas mono_Hiding_ref = mono_Hiding

lemma Hiding_Un: \<open>finite A \<Longrightarrow> P \ (A \<union> B) = (P \ A) \ B\<close>
proof (simp add:Process_eq_spec, intro conjI, unfold F_Hiding, goal_cases)
  case 1
  thus ?case (is "{(s, X). ?A s X} \<union> {(s, X). ?B s} = 
                  {(s, X). (\<exists>t. (?C1 s t \<and> (t, X \<union> ev ` B) \<in> ?C2 \<union> ?C3))} \<union> {(s, X). ?D s}")
  proof(unfold F_Hiding set_eq_subset Un_subset_iff, intro conjI, goal_cases)
    case 1
    then show ?case
      by (auto, metis (no_types) filter_filter image_Un sup_commute sup_left_commute)
  next
    case 2
    then show ?case 
      by (rule_tac Un_mono[of "{}", simplified], insert Hiding_Un_D[of A P B], simp add: D_Hiding)
  next
    case 3
    have "{(s, X). (\<exists>t. (?C1 s t \<and> (t, X \<union> ev ` B) \<in> ?C2))} \<subseteq> {(s, X). ?A s X}" 
      by (auto, metis (no_types) filter_filter image_Un sup_commute sup_left_commute)
    moreover have "{(s, X). (\<exists>t. (?C1 s t \<and> (t, X \<union> ev ` B) \<in> ?C3))} \<subseteq> {(s, X). ?B s}"
    proof(auto,goal_cases)
      case (1 ta u)
      then show ?case using Hiding_fronttickFree by blast
    next
      case (2 u f x)
      then show ?case 
         apply(rule_tac x="f x" in exI, rule_tac x="trace_hide u (ev ` B)" in exI, auto)
         using Hiding_fronttickFree apply blast
        apply(erule_tac x=f in allE) by (metis (no_types) filter_filter rangeI)
    qed
    moreover have "{(s, X). (\<exists>t. (?C1 s t \<and> (t, X \<union> ev ` B) \<in> ?C2 \<union> ?C3))} = 
                                  {(s, X). (\<exists>t. (?C1 s t \<and> (t, X \<union> ev ` B) \<in> ?C2 ))} \<union> 
                                  {(s, X). (\<exists>t. (?C1 s t \<and> (t, X \<union> ev ` B) \<in> ?C3))}" by blast 
    ultimately show ?case by (metis (no_types, lifting) Un_mono) 
  next
    case 4
    then show ?case  
      by (rule_tac Un_mono[of "{}", simplified], insert Hiding_Un_D[of A P B], simp add:D_Hiding)
  qed
next
  case 2
  then show ?case by (simp add: Hiding_Un_D)
qed

lemma Hiding_set_BOT: "(\<bottom> \\ A) = \<bottom>"
  apply(auto simp add:Process_eq_spec D_Hiding F_Hiding F_UU D_UU)
        using Hiding_fronttickFree apply blast
       using front_tickFree_append Hiding_tickFree apply blast
      using front_tickFree_append Hiding_tickFree apply blast
     apply (metis (full_types) append_Nil filter.simps(1) tickFree_Nil tickFree_implies_front_tickFree)
    using front_tickFree_append Hiding_tickFree apply blast 
   using front_tickFree_append Hiding_tickFree apply blast
  using tickFree_Nil by fastforce 

lemma Hiding_set_STOP: "(STOP \\ A) = STOP"
  apply(auto simp add:Process_eq_spec D_Hiding F_Hiding F_STOP D_STOP T_STOP)
  by (metis (full_types) lessI less_irrefl strict_mono_eq) +

lemma Hiding_set_SKIP: "(SKIP \\ A) = SKIP"  
  apply(auto simp add:Process_eq_spec D_Hiding F_Hiding F_SKIP D_SKIP T_SKIP split:if_splits)
       apply (metis filter.simps(1) non_tickFree_tick)
      apply (metis (full_types) Hiding_tickFree n_not_Suc_n non_tickFree_tick strict_mono_eq)
     apply (metis (full_types) Hiding_tickFree n_not_Suc_n non_tickFree_tick strict_mono_eq)
    apply (metis event.distinct(1) filter.simps(1) imageE)
   apply (metis event.distinct(1) filter.simps(1) filter.simps(2) imageE)
  by (metis (full_types) Hiding_tickFree n_not_Suc_n non_tickFree_tick strict_mono_eq)

lemma Hiding_set_empty: "(P \\ {}) = P"
  apply(auto simp add:Process_eq_spec D_Hiding F_Hiding is_processT7 is_processT8_S strict_mono_eq)
  by (metis append_Nil2 front_tickFree_implies_tickFree front_tickFree_single is_processT 
            nonTickFree_n_frontTickFree)

subsection\<open> Multi-Operators laws  \<close>

lemma Hiding_Ndet: "(P \<sqinter> Q) \\ A = ((P \\ A) \<sqinter> (Q \\ A))"  
proof(auto simp add:Process_eq_spec D_Hiding F_Hiding, 
      simp_all add: F_Ndet T_Ndet D_Ndet D_Hiding F_Hiding, goal_cases)
  case (1 b t)
  then show ?case by blast
next
  case (2 b t u)
  then show ?case by blast
next
  case (3 b u f x)
  from 3(4) have A:"infinite ({i. f i \<in> \<T> P}) \<or> infinite ({i. f i \<in> \<T> Q})"
    using finite_nat_set_iff_bounded by auto
  hence "(\<forall>i. f i \<in> \<T> P) \<or> (\<forall>i. f i \<in> \<T> Q)" 
    by (metis (no_types, lifting) 3(3) finite_nat_set_iff_bounded 
            is_processT3_ST_pref mem_Collect_eq not_less strict_mono_less_eq)
  with A show ?case by (metis (no_types, lifting) 3(1,2,3,5) rangeI)
next
  case (4 a b)
  then show ?case by blast
next
  case (5 t u)
  then show ?case by blast
next
  case (6 u f x)
  from 6(4) have A:"infinite ({i. f i \<in> \<T> P}) \<or> infinite ({i. f i \<in> \<T> Q})"
    using finite_nat_set_iff_bounded by auto
  hence "(\<forall>i. f i \<in> \<T> P) \<or> (\<forall>i. f i \<in> \<T> Q)" 
    by (metis (no_types, lifting) 6(3) finite_nat_set_iff_bounded 
            is_processT3_ST_pref mem_Collect_eq not_less strict_mono_less_eq)
  with A show ?case by (metis (no_types, lifting) 6(1,2,3,5) rangeI)
next
  case (7 x)
  then show ?case by blast
qed

lemma Hiding_Mprefix_distr: 
  "(B \<inter> A) = {} \<Longrightarrow> ((Mprefix A P) \\ B) = (Mprefix A (\<lambda>x. ((P x) \\ B)))"
proof (auto simp add: Process_eq_spec, 
     simp_all add: F_Mprefix T_Mprefix D_Mprefix D_Hiding F_Hiding,
     goal_cases)
  case (1 x b) then show ?case
  proof(elim exE disjE conjE, goal_cases)
    case (1 t)
    then show ?case by (simp add: inf_sup_distrib2)
  next
    case (2 t a)
    then show ?case 
      by (metis (no_types, lifting) disjoint_iff_not_equal event.inject filter.simps(2) 
                                    imageE list.sel(1) list.sel(3) list.collapse neq_Nil_conv)
  next
    case (3 t u a)    
    hence "hd t \<notin> ev ` B" by force
    with 3 have"x = hd t # trace_hide (tl t) (ev ` B) @ u"
      by (metis append_Cons filter.simps(2) list.exhaust_sel)
    with 3 show ?case by (metis list.distinct(1) list.sel(1) list.sel(3) tickFree_tl) 
  next
    case (4 t u f)
    then obtain k where kk:"t = f k" by blast
    from 4 obtain a where "f 1 \<noteq> [] \<and> ev a = hd (f 1)" and aa:"a \<in> A"
      by (metis less_numeral_extra(1) nil_le not_less strict_mono_less_eq) 
    with 4(1) 4(6)[THEN spec, of 0] 4(7)[THEN spec, of 1] have "f 0 \<noteq> [] \<and> hd (f 0) = ev a" 
      apply auto 
        apply (metis (no_types, lifting) disjoint_iff_not_equal event.inject 
                                         filter.simps(2) hd_Cons_tl imageE list.distinct(1))
       apply (metis (no_types, lifting) disjoint_iff_not_equal event.inject filter.simps(2) 
                                        hd_Cons_tl imageE list.distinct(1)) 
      by (metis (no_types, lifting) disjoint_iff_not_equal event.inject filter.simps(2)
                                    hd_Cons_tl imageE list.sel(1))
    with 4(1, 7) aa have nf: "\<forall>i. f i \<noteq> [] \<and> hd (f i) = ev a"    
      by (metis (mono_tags, opaque_lifting) "4"(5) append_Cons le_list_def le_simps(2) list.distinct(1) 
                list.exhaust_sel list.sel(1) neq0_conv old.nat.distinct(1) strict_mono_less_eq) 
    with 4(5) have sm:"strict_mono (tl \<circ> f)" by (simp add: less_tail strict_mono_def)
    with 4 aa kk nf show ?case
      apply(rule_tac disjI2, intro conjI) 
        apply (metis (no_types, lifting) Nil_is_append_conv disjoint_iff_not_equal event.inject 
                                          filter.simps(2) hd_Cons_tl imageE list.distinct(1))
       apply (metis (no_types, lifting) disjoint_iff_not_equal event.inject filter.simps(2) 
                                        hd_Cons_tl hd_append2 image_iff list.distinct(1) list.sel(1))
      apply(rule_tac x=a in exI, intro conjI disjI2) 
       apply (metis disjoint_iff_not_equal event.inject filter.simps(2) 
                    hd_Cons_tl hd_append2 image_iff list.distinct(1) list.sel(1))
     apply(rule_tac x="tl t" in exI, rule_tac x="u" in exI, intro conjI, simp_all) 
        apply (metis tickFree_tl)
       apply (metis (no_types, lifting) disjoint_iff_not_equal event.inject filter.simps(2) 
                                        hd_Cons_tl imageE list.distinct(1) list.sel(3) tl_append2)
      apply(subst disj_commute, rule_tac disjCI)
      apply(rule_tac x="tl \<circ> f" in exI, intro conjI)
         apply auto         
      apply (metis (no_types, lifting) filter.simps(2) hd_Cons_tl list.sel(3))
      done
  qed
next
  case (2 x b)
  then show ?case proof(elim exE disjE conjE, goal_cases)
    case 1 then show ?case 
      apply(rule_tac disjI1, rule_tac x="[]" in exI) 
      by (simp add: disjoint_iff_not_equal inf_sup_distrib2)
  next
    case (2 a t) then show ?case 
      apply(rule_tac disjI1, rule_tac  x="(ev a)#t" in exI) 
      using list.collapse by fastforce
  next
    case (3 a t u)
    then show ?case 
      apply(rule_tac disjI2, rule_tac  x="(ev a)#t" in exI, rule_tac x=u in exI) 
      using list.collapse by fastforce
  next
    case (4 a t u f)
    then show ?case 
      apply(rule_tac disjI2)        
      apply(rule_tac x="(ev a) # t" in exI, rule_tac x="u" in exI, intro conjI, simp)
        apply auto[1]
       using hd_Cons_tl apply fastforce
      apply(rule_tac disjI2, rule_tac x="\<lambda>i. (ev a) # (f i)" in exI)
      by (auto simp add: less_cons strict_mono_def)
  qed
next
  case (3 x) then show ?case
  proof(elim exE disjE conjE, goal_cases)
    case (1 t u a)
    hence aa: "hd (trace_hide t (ev ` B)) = ev a \<and> trace_hide t (ev ` B) \<noteq> []"
      by (metis (no_types, lifting) disjoint_iff_not_equal event.inject filter.simps(2) hd_Cons_tl 
                                    imageE list.distinct(1) list.sel(1))
    with 1 have  "hd x = ev a \<and> x \<noteq> []" by simp 
    with 1 show ?case 
      apply(intro conjI, simp_all, rule_tac x=a in exI, simp)
      apply(rule_tac x="tl t" in exI, rule_tac x="u" in exI, intro conjI, simp_all)
       using tickFree_tl apply blast
       using aa by (metis (no_types, lifting) disjoint_iff_not_equal event.inject filter.simps(2) 
                          hd_Cons_tl imageE list.sel(3) tl_append2)
  next
    case (2 t u f)
    then obtain k where kk:"t = f k" by blast
    from 2 obtain a where "f 1 \<noteq> [] \<and> ev a = hd (f 1)" and aa:"a \<in> A"
      by (metis less_numeral_extra(1) nil_le not_less strict_mono_less_eq) 
    with 2(1) 2(6)[THEN spec, of 0] 2(7)[THEN spec, of 1] have "f 0 \<noteq> [] \<and> hd (f 0) = ev a" 
      apply auto 
        apply (metis (no_types, lifting) disjoint_iff_not_equal event.inject 
                                         filter.simps(2) hd_Cons_tl imageE list.distinct(1))
       apply (metis (no_types, lifting) disjoint_iff_not_equal event.inject filter.simps(2) 
                                        hd_Cons_tl imageE list.distinct(1)) 
      by (metis (no_types, lifting) disjoint_iff_not_equal event.inject filter.simps(2)
                                    hd_Cons_tl imageE list.sel(1))
    with 2(1, 7) aa have nf: "\<forall>i. f i \<noteq> [] \<and> hd (f i) = ev a"    
      by (metis (mono_tags, opaque_lifting) 2(5) append_Cons le_list_def le_simps(2) list.distinct(1) 
                list.exhaust_sel list.sel(1) neq0_conv old.nat.distinct(1) strict_mono_less_eq) 
    with 2(5) have sm:"strict_mono (tl \<circ> f)" by (simp add: less_tail strict_mono_def)
    from 2(1,4) nf aa kk have x1:"x \<noteq> []"
      by (metis Nil_is_append_conv disjoint_iff_not_equal event.inject filter.simps(2) 
                hd_Cons_tl imageE list.distinct(1))
    with 2(1,4) nf aa kk have x2: "hd (trace_hide t (ev ` B)) = ev a \<and> trace_hide t (ev ` B) \<noteq> []"
      by (metis (no_types, lifting) disjoint_iff_not_equal event.inject filter.simps(2) hd_Cons_tl 
                                    imageE list.distinct(1) list.sel(1))
    with 2(1,4) nf aa kk x1 have x3:"hd x = ev a" by simp    
    with 2 aa kk nf sm x1  show ?case
      apply(intro conjI, simp_all)
     apply(rule_tac x="tl t" in exI, rule_tac x="u" in exI, intro conjI, simp_all) 
        apply (metis tickFree_tl)
       apply (metis (no_types, lifting) disjoint_iff_not_equal event.inject filter.simps(2) 
                                        hd_Cons_tl imageE list.distinct(1) list.sel(3) tl_append2)
      apply(subst disj_commute, rule_tac disjCI)
      apply(rule_tac x="tl \<circ> f" in exI, intro conjI)
         apply auto         
       apply (metis (no_types, lifting) filter.simps(2) hd_Cons_tl list.sel(3))
      by (metis (no_types, lifting) filter.simps(2) hd_Cons_tl list.sel(3))
  qed
next
  case (4 x) then show ?case
  proof(elim exE disjE conjE, goal_cases)
    case (1 a t u)
    then show ?case
      apply(rule_tac  x="(ev a)#t" in exI, rule_tac x=u in exI) 
      using list.collapse by fastforce
  next
    case (2 a t u f) 
    then show ?case 
      apply(rule_tac x="(ev a) # t" in exI, rule_tac x="u" in exI, intro conjI, simp_all)
        apply auto[1]
       using hd_Cons_tl apply fastforce
      apply(rule_tac disjI2, rule_tac x="\<lambda>i. (ev a) # (f i)" in exI)
      by (auto simp add: less_cons strict_mono_def)
  qed
qed

lemma no_Hiding_read: "(\<forall>y. c y \<notin> B) \<Longrightarrow> ((c\<^bold>?x \<rightarrow> (P x)) \\ B) = (c\<^bold>?x \<rightarrow> ((P x) \\ B))"
  by (simp add: read_def o_def, subst Hiding_Mprefix_distr, auto)

lemma no_Hiding_write0: "a \<notin> B \<Longrightarrow> ((a \<rightarrow> P) \\ B) = (a \<rightarrow> (P \\ B))"
  by (simp add: Hiding_Mprefix_distr write0_def)

lemma Hiding_write0: "a \<in> B  \<Longrightarrow> ((a \<rightarrow> P) \\ B) = (P \\ B)"
proof (auto simp add: write0_def Process_eq_spec, 
       simp_all add: F_Mprefix T_Mprefix D_Mprefix D_Hiding F_Hiding,
       goal_cases)
  case (1 x b)
  then show ?case
    apply(elim exE disjE conjE)
      apply (metis filter.simps(2) hd_Cons_tl image_eqI)
     apply (metis (no_types, lifting) filter.simps(2) image_eqI list.sel(1) 
                                      list.sel(3) neq_Nil_conv tickFree_tl)
  proof(goal_cases)
    case (1 t u f)
    have fS: "strict_mono (f \<circ> Suc)" by (metis "1"(5) Suc_mono comp_def strict_mono_def)
    from  1 have aa:"\<forall>i. f (Suc i) \<noteq> []"
      by (metis (full_types) less_Suc_eq_le less_irrefl nil_le strict_mono_less_eq)      
    with fS have sm:"strict_mono (tl \<circ> f \<circ> Suc)" by (simp add: less_tail strict_mono_def)
    with 1 aa show ?case
      apply(subst disj_commute, rule_tac disjCI, simp)        
      apply(rule_tac x="tl (f 1)" in exI, rule_tac x="u" in exI, intro conjI, simp_all) 
        apply (metis Hiding_tickFree imageE tickFree_tl)
      apply (metis (no_types, lifting) filter.simps(2) hd_Cons_tl image_eqI rangeE)
      apply(subst disj_commute, rule_tac disjCI)        
      apply(rule_tac x="tl \<circ> f \<circ> Suc" in exI, intro conjI)
         apply auto
         apply (metis (no_types, lifting) filter.simps(2) hd_Cons_tl list.sel(3))
      done
  qed
next
  case (2 aa b)
  then show ?case     
    apply(elim exE disjE conjE)
      apply (metis (no_types, lifting) filter.simps(2) image_eqI list.distinct(1) 
                                        list.sel(1) list.sel(3))
  proof(goal_cases)
    case (1 t u)
    then show ?case by (rule_tac disjI2, rule_tac x="(ev a)#t" in exI, auto)
  next
    case (2 t u f)
    then show ?case
      apply(rule_tac disjI2)         
      apply(rule_tac x="(ev a) # t" in exI, rule_tac x="u" in exI, intro conjI, simp_all)
      apply(rule_tac disjI2)       
      apply(rule_tac x="\<lambda>i. (ev a) # (f i)" in exI, intro conjI)
      by (auto simp add: less_cons strict_mono_def)
  qed
next
  case (3 x)
  then show ?case 
    apply(elim exE disjE conjE)
     apply(rule_tac x="tl t" in exI, rule_tac x="u" in exI, intro conjI, simp_all)
    using tickFree_tl apply blast
     apply (metis filter.simps(2) hd_Cons_tl image_eqI)
  proof(goal_cases)
    case (1 t u f)
    have fS: "strict_mono (f \<circ> Suc)" by (metis "1"(5) Suc_mono comp_def strict_mono_def)
    from  1 have aa:"\<forall>i. f (Suc i) \<noteq> []"
      by (metis (full_types) less_Suc_eq_le less_irrefl nil_le strict_mono_less_eq)      
    with fS have sm:"strict_mono (tl \<circ> f \<circ> Suc)" by (simp add: less_tail strict_mono_def)
    with 1 aa show ?case
      apply(rule_tac x="tl (f 1)" in exI, rule_tac x="u" in exI, intro conjI, simp_all) 
        apply (metis Hiding_tickFree imageE tickFree_tl)
      apply (metis (no_types, lifting) filter.simps(2) hd_Cons_tl image_eqI rangeE)
      apply(subst disj_commute, rule_tac disjCI)        
      apply(rule_tac x="tl \<circ> f \<circ> Suc" in exI, intro conjI)
         apply auto
         apply (metis (no_types, lifting) filter.simps(2) hd_Cons_tl list.sel(3))
      done
  qed
next
  case (4 x)
  then show ?case
    apply(elim exE disjE conjE)
  proof(goal_cases)
    case (1 t u)
    then show ?case by (rule_tac x="(ev a)#t" in exI, auto)
  next
    case (2 t u f)
    then show ?case
      apply(rule_tac x="(ev a) # t" in exI, rule_tac x="u" in exI, intro conjI, simp_all)
      apply(rule_tac disjI2)       
      apply(rule_tac x="\<lambda>i. (ev a) # (f i)" in exI, intro conjI)
      by (auto simp add: less_cons strict_mono_def)
  qed
qed

lemma no_Hiding_write: "(\<forall>y. c y \<notin> B) \<Longrightarrow> ((c\<^bold>!a \<rightarrow> P) \\ B) = (c\<^bold>!a \<rightarrow> (P \\ B))"
  by(simp add: write_def, subst Hiding_Mprefix_distr, auto)

lemma Hiding_write: "(c a) \<in> B ==> ((c\<^bold>!a \<rightarrow> P) \\ B) = (P \\ B)"
  by (simp add: write_def Hiding_write0 Mprefix_singl)


section\<open> The Sync Operator Laws \<close>  

subsection\<open> Preliminaries \<close>

lemma SyncTlEmpty:"a setinterleaves (([], u), A) \<Longrightarrow> tl a setinterleaves (([], tl u), A)"
  by (case_tac u, simp, case_tac a, simp_all split:if_splits)

lemma SyncHd_Tl: 
   "a setinterleaves ((t, u), A) \<and> hd t \<in> A \<and> hd u \<notin> A
    \<Longrightarrow> hd a = hd u \<and> tl a setinterleaves ((t, tl u), A)"
  by (case_tac u) (case_tac t, auto split:if_splits)+
 
lemma SyncHdAddEmpty: 
   "(tl a) setinterleaves (([], u), A) \<and> hd a \<notin> A \<and> a \<noteq> [] 
    \<Longrightarrow> a setinterleaves (([], hd a # u), A)"  
  using hd_Cons_tl by fastforce 

lemma SyncHdAdd: 
  "(tl a) setinterleaves ((t, u), A) \<and> hd a \<notin> A \<and> hd t \<in> A \<and> a \<noteq> [] 
   \<Longrightarrow> a setinterleaves ((t, hd a # u), A)" 
  by (case_tac a, simp, case_tac t, auto) 

lemmas SyncHdAdd1 = SyncHdAdd[of "a#r", simplified] for a r

lemma SyncSameHdTl:
  "a setinterleaves ((t, u), A) \<and> hd t \<in> A \<and> hd u \<in> A
   \<Longrightarrow> hd t = hd u \<and> hd a = hd t \<and> (tl a) setinterleaves ((tl t, tl u), A)"
  by (case_tac u) (case_tac t, auto split:if_splits)+

lemma SyncSingleHeadAdd: 
   "a setinterleaves ((t, u), A) \<and> h \<notin> A
    \<Longrightarrow> (h#a) setinterleaves ((h#t, u), A)"
  by (case_tac u, auto split:if_splits)

lemma TickLeftSync:
   "tick \<in> A \<and> front_tickFree t \<and> s setinterleaves (([tick], t), A) \<Longrightarrow> s = t \<and> last t = tick"
proof(induct t arbitrary: s)
  case Nil
  then show ?case by (simp add: Nil.prems)
next
  case (Cons a t)
  then show ?case
    apply (auto split:if_splits)
      using emptyLeftProperty apply blast
     apply (metis last_ConsR last_snoc nonTickFree_n_frontTickFree tickFree_Cons)
    by (metis append_Cons append_Nil front_tickFree_mono)+
qed  
  
lemma EmptyLeftSync:"s setinterleaves (([], t), A) \<Longrightarrow> s = t \<and> set t \<inter> A = {}"
  by (meson Int_emptyI emptyLeftNonSync emptyLeftProperty)

lemma tick_T_F:"t@[tick] \<in> \<T> P \<Longrightarrow> (t@[tick], X) \<in> \<F> P"
  using append_T_imp_tickFree is_processT5_S7 by force

lemma event_set: "(e::'a event) \<in> insert tick (range ev)"
  by (metis event.exhaust insert_iff rangeI)

lemma Mprefix_Sync_distr1_D: 
  " A \<subseteq> S 
    \<Longrightarrow> B \<subseteq> S 
    \<Longrightarrow>  \<D> (Mprefix A P \<lbrakk>S\<rbrakk> Mprefix B Q) =  \<D> (\<box> x \<in>  A \<inter> B \<rightarrow> (P x \<lbrakk>S\<rbrakk> Q x))"  
  apply(auto,simp_all add:D_Sync F_Sync F_Mprefix T_Mprefix D_Mprefix)  
   apply(elim exE disjE conjE)  
          apply (metis (no_types, lifting) Sync.sym empty_iff image_iff insertI2 
                       list.exhaust_sel setinterleaving.simps(2) subsetCE)
proof(goal_cases)
  case (1 x t u r v a aa)
  from 1(1,2,6,8,11,13) have aa1: "hd t\<in>insert tick (ev ` S)\<and>hd u\<in>insert tick (ev ` S)"   
    by blast
  from 1(5,6,7,8,11,13) aa1 have aa2: " hd x \<in> ev ` (A \<inter> B)"  
    by (metis (no_types, lifting) IntI empty_setinterleaving event.inject hd_append2 image_iff SyncSameHdTl)
  then show ?case  
    using 1(3,4,5,6,7,9,10,13,14) by (metis (no_types, lifting)  Nil_is_append_conv aa1 
                                            empty_setinterleaving event.inject hd_append2 
                                            SyncSameHdTl tickFree_tl tl_append2)
next
  case (2 x t u r v a)
  then show ?case      
    by (metis (no_types, lifting) Sync.si_empty3 equals0D imageE image_eqI insertI2 list.exhaust_sel subsetCE) 
next
  case (3 x t u r v a aa)
  from 3(1,2,6,8,11,13) have aa1: "hd t\<in>insert tick (ev ` S)\<and>hd u\<in>insert tick (ev ` S)"   
    by blast
  from 3(5,6,7,8,11,13) aa1 have aa2: " hd x \<in> ev ` (A \<inter> B)"  
    by (metis (no_types, lifting) IntI empty_setinterleaving event.inject hd_append2 image_iff SyncSameHdTl)
  then show ?case 
    using 3(3,4,5,6,7,9,10,13,14) 
    by (metis (no_types, lifting)  Nil_is_append_conv aa1 empty_setinterleaving event.inject 
                                   hd_append2 SyncSameHdTl  tickFree_tl tl_append2) 
next
  case (4 x t u r v a)
  then show ?case        
    by (metis (no_types, lifting) Sync.si_empty3 equals0D imageE image_eqI insertI2 list.exhaust_sel subsetCE)  
next
  case (5 x t u r v a aa)
  from 5(1,2,6,8,11,13) have aa1: "hd t\<in>insert tick (ev ` S)\<and>hd u\<in>insert tick (ev ` S)"   
    by blast
  from 5(5,6,7,8,11,13) aa1 have aa2: " hd x \<in> ev ` (A \<inter> B)"  
    by (metis (no_types, lifting) IntI empty_setinterleaving event.inject hd_append2 image_iff SyncSameHdTl)
  then show ?case 
    using 5(3,4,5,6,7,9,10,13,14) by (metis  aa1 append_Nil2 empty_setinterleaving event.inject SyncSameHdTl)   
next
  case (6 x t u r v a)
  then show ?case       
    by (metis (no_types, lifting) Sync.si_empty3 equals0D imageE image_eqI insertI2 list.exhaust_sel subsetCE) 
next
  case (7 x t u r v a aa)
  from 7(1,2,6,8,11,13) have aa1: "hd t\<in>insert tick (ev ` S)\<and>hd u\<in>insert tick (ev ` S)"   
    by blast
  from 7(5,6,7,8,11,13) aa1 have aa2: " hd x \<in> ev ` (A \<inter> B)"  
    by (metis (no_types, lifting) IntI empty_setinterleaving event.inject hd_append2 image_iff SyncSameHdTl)
  then show ?case  
      using 7(3,4,5,6,7,9,10,13,14) by (metis  aa1 append_Nil2 empty_setinterleaving event.inject SyncSameHdTl) 
next
  case (8 x)
  then show ?case 
    apply(elim exE disjE conjE)  
  proof(goal_cases)
    case (1 a t u r v)
    obtain r1 t1 u1 where aa0: "r1=hd x#r\<and>t1=hd x#t\<and>u1=hd x#u" 
      by auto
    from 1(3,4,5,7,8,9) have aa1: "tickFree r1\<and>x = r1 @ v" 
      by (metis  Cons_eq_appendI aa0 event.distinct(1) list.exhaust_sel tickFree_Cons)
    from 1(2,4,9) have aa2: "r1 setinterleaves ((t1, u1), insert tick (ev ` S))\<and>t1 \<noteq> []"   
      using aa0 subsetCE by auto
    from 1(4,5,10,11) aa0 
    have aa3: "(tl t1) \<in> \<D> (P a) \<and> (tl u1) \<in> \<T> (Q a) \<and> ev a = hd t1 \<and> ev a = hd u1 \<and> 
               hd t1 \<in> ev ` A\<and> hd u1 \<in> ev ` B"  
       by auto
    then show ?case      
      using "1"(6) aa1 aa2 by fastforce 
  next
    case (2 a t u r v)
    obtain r1 t1 u1 where aa0: "r1=hd x#r\<and>t1=hd x#t\<and>u1=hd x#u" 
      by auto
    from 2(3,4,5,7,8,9) have aa1: "tickFree r1\<and>x = r1 @ v" 
      by (metis  Cons_eq_appendI aa0 event.distinct(1) list.exhaust_sel tickFree_Cons)
    from 2(2,4,9) have aa2: "r1 setinterleaves ((t1, u1), insert tick (ev ` S))\<and>t1 \<noteq> []"   
      using aa0 subsetCE by auto
    from 2(4,5,10,11) aa0 
    have aa3: "(tl t1) \<in> \<D> (Q a) \<and> (tl u1) \<in> \<T> (P a) \<and> ev a = hd t1 \<and> ev a = hd u1 \<and> 
               hd t1 \<in> ev ` A\<and> hd u1 \<in> ev ` B"  
       by auto
    then show ?case      
      using "2"(6) aa1 aa2 by fastforce
  next
    case (3 a t u r v)
    obtain r1 t1 u1 where aa0: "r1=hd x#r\<and>t1=hd x#t\<and>u1=hd x#u" 
      by auto
    from 3(2,4,9) have aa2: "r1 setinterleaves ((t1, u1), insert tick (ev ` S))\<and>t1 \<noteq> []"   
      using aa0 subsetCE by auto
    from 3(3,4,5,7,8,10,11) aa0 
    have aa3: "(tl t1) \<in> \<D>(P a)\<and>(tl u1) \<in> \<T> (Q a)\<and> ev a = hd t1\<and>ev a = hd u1 \<and> 
               hd t1 \<in> ev ` A\<and> hd u1 \<in> ev ` B\<and>x = r1 @ v"  
      by (metis (no_types, lifting)  Int_lower1 Int_lower2 append_Nil2 imageE image_eqI 
                                     list.exhaust_sel list.sel(1) list.sel(3) subsetCE)    
    then show ?case   
      by (metis (no_types, lifting) "3"(6) "3"(7) aa2 event.inject imageE)     
  next
    case (4 a t u r v)
    obtain r1 t1 u1 where aa0: "r1=hd x#r\<and>t1=hd x#t\<and>u1=hd x#u" 
      by auto
    from 4(2,4,9) have aa2: "r1 setinterleaves ((t1, u1), insert tick (ev ` S))\<and>t1 \<noteq> []"   
      using aa0 subsetCE by auto
    from 4(3,4,5,7,8,10,11) aa0 
    have aa3: "(tl t1) \<in> \<D> (Q a)\<and>(tl u1) \<in> \<T> (P a) \<and> ev a = hd t1\<and>ev a = hd u1\<and> 
               hd t1 \<in> ev ` A\<and> hd u1 \<in> ev ` B\<and>x = r1 @ v"  
      by (metis (no_types, lifting)  Int_lower1 Int_lower2 append_Nil2 imageE image_eqI 
                list.exhaust_sel list.sel(1) list.sel(3) subsetCE)    
    then show ?case   
      by (metis (no_types, lifting) "4"(6) "4"(7) aa2 event.inject imageE)  
  qed
qed

lemma Hiding_interleave: 
  "A \<inter> C = {} 
  \<Longrightarrow> r setinterleaves ((t, u), C) 
  \<Longrightarrow> (trace_hide r A) setinterleaves ((trace_hide t A, trace_hide u A), C)"
proof(induct r arbitrary:t u)
  case Nil
  then show ?case
    using EmptyLeftSync empty_setinterleaving by fastforce
next
  case (Cons a r)
  then show ?case
    apply(cases t) using EmptyLeftSync apply fastforce
    apply(cases u) apply fastforce
  proof(simp split:if_splits, goal_cases)
    case (1 a list lista)
    then show ?case by fastforce
  next
    case (2 a list aa lista)
    then show ?case 
      apply(erule_tac disjE)
       using Cons(1)[of list u] 
       apply (metis (no_types, lifting) filter.simps(2) SyncSingleHeadAdd)
      using Cons(1)[of t lista]
      by (metis (no_types, lifting) Sync.sym filter.simps(2) SyncSingleHeadAdd)
  next
    case (3 a list lista)
    then show ?case by fastforce
  qed
qed

lemma non_Sync_interleaving: 
  "(set t \<union> set u) \<inter> C = {} \<Longrightarrow> setinterleaving (t, C, u) \<noteq> {}" (* FINALLY NON-USED*)
proof(induct t arbitrary:u)
  case Nil
  then show ?case 
    by (metis Un_empty_left disjoint_iff_not_equal emptyLeftSelf empty_iff empty_set)
next
  case (Cons a t)
  then show ?case 
  proof(induct u)
    case Nil
    then show ?case using Sync.sym by auto
  next
    case (Cons a u)
    then show ?case by auto
  qed
qed
  
lemma interleave_Hiding: 
  "A \<inter> C = {} 
  \<Longrightarrow> ra setinterleaves ((trace_hide t A, trace_hide u A), C) 
  \<Longrightarrow> \<exists>r. ra = trace_hide r A \<and> r setinterleaves ((t, u), C)"
proof(induct "length t + length u" arbitrary:ra t u rule:nat_less_induct)
  case Ind:1
  then show ?case
  proof (cases t)
    case Nilt: Nil
    from Ind(2) have a:"set (trace_hide u A) \<inter> C = {} \<Longrightarrow> set u \<inter> C = {}" by auto
    hence b: "u setinterleaves ((t, u), C)"
      by (metis (no_types, lifting) Ind(3) EmptyLeftSync Nilt disjoint_iff_not_equal 
                emptyLeftSelf filter.simps(1))
    then show ?thesis 
      apply(rule_tac x=u in exI)
      using EmptyLeftSync[of "ra" C "trace_hide u A"] a b Cons Nilt Ind(3) by auto
  next  
    case Const: (Cons ta tlist)
    then show ?thesis
    proof(cases u)
      case Nilu: Nil
      from Ind(2) have a:"set (trace_hide t A) \<inter> C = {} \<Longrightarrow> set t \<inter> C = {}" by auto
      hence b: "t setinterleaves ((t, u), C)" 
        by (metis Ind(3) Nilu EmptyLeftSync disjoint_iff_not_equal emptyLeftSelf filter.simps(1) Sync.sym)
      then show ?thesis 
        apply(rule_tac x=t in exI)
        using EmptyLeftSync[of "ra" C "trace_hide t A"] a b Ind Nilu by (metis Sync.sym filter.simps(1))
    next
      case Consu: (Cons ua ulist)
      with Const Ind(2,3) show ?thesis
      proof(auto split:if_splits simp del:setinterleaving.simps, goal_cases)
        case 1
        then show ?case
        proof (auto, goal_cases)
          case (1 raa)
          with Ind(1)[THEN spec, of "length tlist + length u", simplified Const, simplified, 
                        THEN spec, THEN spec, of tlist u, simplified Ind, simplified, 
                        THEN spec, of raa] obtain r where 
            "raa = trace_hide r A \<and> r setinterleaves ((tlist, u), C)" by auto  
          then show ?case using "1"(4) Consu by force
        next
          case (2 raa)
          with Ind(1)[THEN spec, of "length t + length ulist", simplified Consu, simplified, 
                    THEN spec, THEN spec, of t ulist, simplified Ind, simplified, 
                    THEN spec, of raa] obtain r where 
            "raa = trace_hide r A \<and> r setinterleaves ((t, ulist), C)" by auto
          then show ?case using "2"(2) "2"(4) by force
        next
          case (3 raa)
            with Ind(1)[THEN spec, of "length tlist + length ulist", simplified Const Consu, simplified, 
                      THEN spec, THEN spec, of tlist ulist, simplified Ind, simplified, 
                      THEN spec, of raa] obtain r where 
            "raa = trace_hide r A \<and> r setinterleaves ((tlist, ulist), C)" by auto
          then show ?case using "3"(4) by force
        next
          case (4 raa)
          with Ind(1)[THEN spec, of "length t + length ulist", simplified Consu, simplified, 
                    THEN spec, THEN spec, of t ulist, simplified Ind, simplified, 
                    THEN spec, of raa] obtain r where 
            "raa = trace_hide r A \<and> r setinterleaves ((t, ulist), C)" by auto
          then show ?case using "4"(5) Const by force
        next
          case (5 raa)
          with Ind(1)[THEN spec, of "length tlist + length u", simplified Const, simplified, 
                        THEN spec, THEN spec, of tlist u, simplified Ind, simplified, 
                        THEN spec, of raa] obtain r where 
            "raa = trace_hide r A \<and> r setinterleaves ((tlist, u), C)" by auto  
          then show ?case using "5"(4) Consu by force
        next
          case (6 raa)
          with Ind(1)[THEN spec, of "length t + length ulist", simplified Consu, simplified, 
                    THEN spec, THEN spec, of t ulist, simplified Ind, simplified, 
                    THEN spec, of raa] obtain r where 
            "raa = trace_hide r A \<and> r setinterleaves ((t, ulist), C)" by auto
          then show ?case using "6"(5) Const by force
        next
          case (7 raa)
          with Ind(1)[THEN spec, of "length tlist + length u", simplified Const, simplified, 
                        THEN spec, THEN spec, of tlist u, simplified Ind, simplified, 
                        THEN spec, of raa] obtain r where 
            "raa = trace_hide r A \<and> r setinterleaves ((tlist, u), C)" by auto  
          then show ?case using "7"(4) Consu by force
        qed
      next
        case 2
        with Ind(1)[THEN spec, of "length t + length ulist", simplified Consu, simplified, 
                      THEN spec, THEN spec, of t ulist, simplified Ind, simplified, 
                      THEN spec, of ra] obtain r where 
          "ra = trace_hide r A \<and> r setinterleaves ((t, ulist), C)" by auto   
        then show ?case 
          apply(rule_tac x="ua#r" in exI)
          using "2"(5) Const Ind.prems(1) by auto
      next
        case 3
        with Ind(1)[THEN spec, of "length tlist + length u", simplified Const, simplified, 
                      THEN spec, THEN spec, of tlist u, simplified Ind, simplified, 
                      THEN spec, of ra] obtain r where 
          "ra = trace_hide r A \<and> r setinterleaves ((tlist, u), C)" by auto   
        then show ?case
          apply(rule_tac x="ta#r" in exI)
          using "3"(4) Consu Ind.prems(1) by auto
      next
        case 4
        with Ind(1)[THEN spec, of "length tlist + length ulist", simplified Const Consu, simplified, 
                      THEN spec, THEN spec, of tlist ulist, simplified Ind, simplified, 
                      THEN spec, of ra] obtain r where 
          "ra = trace_hide r A \<and> r setinterleaves ((tlist, ulist), C)" by auto
        then show ?case
          apply(rule_tac x="ta#ua#r" in exI)
          using "4"(4,5) Consu Const Ind.prems(1) apply auto
           using SyncSingleHeadAdd apply blast 
          by (metis Sync.sym SyncSingleHeadAdd)
      qed
    qed
  qed
qed

lemma interleave_size: 
  "s setinterleaves ((t,u), C) \<Longrightarrow> length s = length t + length u - length(filter (\<lambda>x. x\<in>C) t)"
proof(induct s arbitrary:t u)
  case Nil
  then show ?case using EmptyLeftSync empty_setinterleaving by fastforce
next
  case (Cons a list)
  then show ?case
    apply(cases t) using emptyLeftProperty apply fastforce
    apply(cases u) 
     apply (metis (no_types, lifting) Sync.sym add_diff_cancel_right' emptyLeftNonSync 
                  emptyLeftProperty filter_empty_conv)
    proof(auto split:if_splits, goal_cases 11 12 13 14 15)
      case (11 tlist ulist)
      then show ?case 
        by (metis (no_types, lifting) Suc_diff_le le_add1 length_filter_le order_trans)
    next
      case (12 ta tlist ulist)
      with 12(3)[rule_format, of "ta#tlist" ulist] show ?case 
        by simp (metis Suc_diff_le le_add1 length_filter_le order_trans)
    next
      case (13 tlist ua ulist)
      with 13(3)[rule_format, of tlist "ua#ulist"] show ?case 
        by simp (metis Suc_diff_le le_less_trans length_filter_le less_SucI less_Suc_eq_le less_add_Suc1)
    next
      case (14 ta tlist ulist)
      with 14(3)[rule_format, of "ta#tlist" ulist] show ?case 
        by simp (metis Suc_diff_le le_less_trans length_filter_le less_SucI less_Suc_eq_le less_add_Suc1)
    next
      case (15 tlist ua ulist)
      with 15(3)[rule_format, of tlist "ua#ulist"] show ?case
        by simp (metis Suc_diff_le le_less_trans length_filter_le less_SucI less_Suc_eq_le less_add_Suc1)
    qed
qed 

lemma interleave_eq_size: 
  "s setinterleaves ((t,u), C) \<Longrightarrow> s' setinterleaves ((t,u), C) \<Longrightarrow> length s = length s'"
  by (simp add: interleave_size)

lemma interleave_set: "s setinterleaves ((t,u), C) \<Longrightarrow> set t \<union> set u \<subseteq> set s"
proof(induct s arbitrary: t u)
  case Nil
  then show ?case using EmptyLeftSync empty_setinterleaving by blast
next
  case (Cons a s)
  then show ?case
    apply(cases t) using emptyLeftProperty apply fastforce
    apply(cases u) apply (metis Sync.sym Un_empty_right emptyLeftProperty empty_set eq_refl)
    by (auto simp add: subset_iff split:if_splits) 
qed 

lemma interleave_order: "s setinterleaves ((t1@t2,u), C) \<Longrightarrow> set(t2) \<subseteq> set(drop (length t1) s)"
proof(induct s arbitrary: t1 t2 u)
  case Nil
  then show ?case using empty_setinterleaving by auto
next
  case (Cons a s)
  then show ?case
  apply(cases t1) using append_self_conv2 interleave_set apply fastforce
  apply(cases u) apply (metis EmptyLeftSync Sync.sym append_eq_conv_conj order_refl) 
  proof (auto simp add: subset_iff split:if_splits, goal_cases)
    case (1 a list lista t)
    then show ?case using Cons(1)[of "a#list" "t2" "lista", simplified, OF 1(6)]
      by (meson Suc_n_not_le_n contra_subsetD nat_le_linear set_drop_subset_set_drop)
  next
    case (2 a list lista t)
    then show ?case using Cons(1)[of "a#list" "t2" "lista", simplified, OF 2(7)]
      by (meson Suc_n_not_le_n contra_subsetD nat_le_linear set_drop_subset_set_drop)
  qed
qed 

lemma interleave_append: 
  "s setinterleaves ((t1@t2,u), C) 
   \<Longrightarrow> \<exists> u1 u2 s1 s2. u = u1@u2 \<and> s = s1@s2 \<and> 
                      s1 setinterleaves ((t1,u1), C) \<and> s2 setinterleaves ((t2,u2), C)"
proof(induct s arbitrary: t1 t2 u)
  case Nil
  then show ?case using empty_setinterleaving by fastforce
next
  case (Cons a s)
  then show ?case
  apply(cases t1) using append_self_conv2 interleave_set apply fastforce
  apply(cases u) apply(exI "[]", exI "[]") apply auto[1]
    apply (metis (no_types, opaque_lifting) Nil_is_append_conv append_Cons)
  proof (auto simp add: subset_iff split:if_splits, goal_cases)
    case (1 list lista)
    with Cons(1)[of "list" "t2" "lista", simplified, OF 1(5)] show ?case
    proof(elim exE conjE, goal_cases)
      case (1 u1 u2 s1 s2)
      then show ?case 
        by (exI "a#u1", exI "u2", simp) (metis append_Cons)
    qed      
  next
    case (2 aa list lista)
    with Cons(1)[of "aa#list" "t2" "lista", simplified, OF 2(6)] show ?case
    proof(elim exE conjE, goal_cases)
      case (1 u1 u2 s1 s2)
      then show ?case 
        by (exI "a#u1", exI "u2", simp) (metis append_Cons)
    qed  
  next
    case (3 list aa lista)
    with Cons(1)[of "list" "t2" "aa#lista", simplified, OF 3(6)] show ?case
    proof(elim exE conjE, goal_cases)
      case (1 u1 u2 s1 s2)
      then show ?case 
        apply (exI "u1", exI "u2", simp) by (metis append_Cons SyncSingleHeadAdd)
    qed  
  next
    case (4 aa list lista)
    with Cons(1)[of "aa#list" "t2" "lista", simplified, OF 4(6)] show ?case
    proof(elim exE conjE, goal_cases)
      case (1 u1 u2 s1 s2)
      then show ?case 
        by (exI "a#u1", exI "u2", simp) (metis append_Cons)
    qed 
  next
    case (5 list aa lista)
    with Cons(1)[of "list" "t2" "aa#lista", simplified, OF 5(6)] show ?case
    proof(elim exE conjE, goal_cases)
      case (1 u1 u2 s1 s2)
      then show ?case 
        apply (exI "u1", exI "u2", simp) by (metis append_Cons SyncSingleHeadAdd)
    qed
  qed
qed 

lemma interleave_append_sym: 
  "s setinterleaves ((t,u1@u2), C) 
   \<Longrightarrow> \<exists> t1 t2 s1 s2. t = t1@t2 \<and> s = s1@s2 \<and> 
                      s1 setinterleaves ((t1,u1), C) \<and> s2 setinterleaves ((t2,u2), C)"
  by (metis (no_types) Sync.sym interleave_append)

lemma interleave_append_tail: 
  "s setinterleaves ((t1,u), C) \<Longrightarrow> (set t2) \<inter> C = {} \<Longrightarrow> (s@t2) setinterleaves ((t1@t2,u), C)"
proof(induct s arbitrary: t1 t2 u)
  case Nil
  then show ?case by (metis Set.set_insert Sync.sym append_Nil disjoint_insert(2) 
                            emptyLeftSelf empty_setinterleaving)
next
  case (Cons a s)
  then show ?case
    apply(cases u) using EmptyLeftSync Sync.sym apply fastforce 
    apply(cases t1, cases t2) apply simp apply fastforce 
  proof(auto, goal_cases)
    case (1 list lista)
    with 1(1)[OF 1(7) 1(2)] show ?case by simp
  next
    case (2 list aa lista)
    with 2(1)[OF 2(2)] show ?case by simp  
  next
    case (3 list aa lista)
    with 3(1)[OF 3(9) 3(2)] show ?case by simp
  next
    case (4 list aa lista)
    with 4(1)[OF 4(9) 4(2)] show ?case by simp
  qed
qed

lemma interleave_append_tail_sym: 
  "s setinterleaves ((t,u1), C) \<Longrightarrow> (set u2) \<inter> C = {} \<Longrightarrow> (s@u2) setinterleaves ((t,u1@u2), C)"
  by (metis (no_types) Sync.sym interleave_append_tail)

lemma interleave_assoc_1: 
  "tu setinterleaves ((t, u), A) 
   \<Longrightarrow> tuv setinterleaves ((tu, v), A) 
   \<Longrightarrow> \<exists>uv. uv setinterleaves ((u, v), A) \<and> tuv setinterleaves ((t, uv), A)"
proof(induct tuv arbitrary: t tu u v)
  case Nil
  then show ?case using EmptyLeftSync empty_setinterleaving by blast
next
  case Cons_tuv:(Cons a tuv)
  then show ?case
  proof(cases t)
    case Nil_t:Nil
    with Cons_tuv(2) have *:"tu = u" using EmptyLeftSync by blast
    show ?thesis
    proof(cases u)
      case Nil_u:Nil
      with Nil_t Cons_tuv show ?thesis using EmptyLeftSync by fastforce
    next
      case Cons_u:(Cons ua ulist)
      with Nil_t Cons_tuv(2) have "ua \<notin> A" by force  
      show ?thesis 
      proof(cases v)
        case Nil_v:Nil
        with * Nil_t Cons_tuv(2,3) Cons_u show ?thesis using Sync.sym by blast
      next
        case Cons_v:(Cons va vlist)
        with * Nil_t Cons_tuv(2,3) Cons_u show ?thesis apply(exI "a#tuv", auto split:if_splits) 
          using Cons_tuv.hyps Cons_tuv.prems(1) emptyLeftProperty by blast+
      qed
    qed
  next
    case Cons_t:(Cons ta tlist)
    show ?thesis
    proof(cases u)
      case Nil_u:Nil
      with Cons_t Cons_tuv show ?thesis
        by (metis Sync.sym emptyLeftProperty emptyLeftSelf empty_set equals0D ftf_Sync21)
    next
      case Cons_u:(Cons ua ulist)
      show ?thesis 
      proof(cases v)
        case Nil_v:Nil
        with Cons_tuv(3) have "a # tuv = tu" by (simp add: Nil_v EmptyLeftSync Sync.sym)
        with Nil_v Cons_u Cons_t Cons_tuv show ?thesis apply(exI u, auto split:if_splits)
           apply (metis Cons_t Nil_v Sync.sym emptyLeftNonSync list.set_intros(1))
          using Cons_tuv(1)[of tuv tlist u] 
            apply(metis (no_types, lifting) Sync.sym emptyLeftNonSync emptyLeftSelf list.sel(3) SyncTlEmpty)
        by (metis Cons_t Sync.sym emptyLeftProperty) fastforce+  
      next
        case Cons_v:(Cons va vlist)
        with Cons_t Cons_u Cons_tuv(2,3) show ?thesis 
        proof(auto split:if_splits, goal_cases)
          case (1 tulist)
          from Cons_tuv(1)[OF 1(5) 1(10)] obtain uvlist 
            where "uvlist setinterleaves ((ulist, vlist), A) \<and> tuv setinterleaves ((tlist, uvlist), A)" by blast
          with 1 show ?case by(exI "va#uvlist", simp)
        next
          case (2 u)
          then show ?case by (metis Cons_tuv.hyps Cons_tuv.prems(1) Sync.sym SyncSingleHeadAdd)
        next
          case (3 u)
          then show ?case by (metis Cons_tuv.hyps Sync.sym SyncSingleHeadAdd) 
        next
          case (4 u)
          then show ?case by (metis Cons_tuv.hyps Cons_tuv.prems(1) Sync.sym SyncSingleHeadAdd)
        next
          case (5 u)
          then show ?case by (metis Cons_tuv.hyps Sync.sym SyncSingleHeadAdd)
        next
          case (6 u)
          then show ?case by (metis Cons_tuv.hyps Cons_tuv.prems(1) Sync.sym SyncSingleHeadAdd)
        next
          case (7 u)
          then show ?case by (metis Cons_tuv.hyps Sync.sym SyncSingleHeadAdd)
        next
          case (8 tulist)
          from Cons_tuv(1)[OF 8(5) 8(9)] obtain uvlist 
            where "uvlist setinterleaves ((va#ulist, va#vlist), A) \<and> 
                   tuv setinterleaves ((tlist, uvlist), A)" by blast
          with 8 show ?case using SyncSingleHeadAdd by (exI "uvlist", simp) blast
        next
          case (9 u)
          then show ?case by (metis Cons_tuv.hyps Cons_tuv.prems(1) Sync.sym SyncSingleHeadAdd)
        next
          case (10 tulist)
          from Cons_tuv(1)[OF 10(6) 10(10)] obtain uvlist 
            where "uvlist setinterleaves ((ua#ulist, va#vlist), A) \<and> 
                   tuv setinterleaves ((tlist, uvlist), A)" by blast
          with 10 show ?case using SyncSingleHeadAdd by (exI "uvlist", simp) blast
        next
          case (11 u)
          then show ?case by (metis Cons_tuv.hyps Cons_tuv.prems(1) Sync.sym SyncSingleHeadAdd)
        next
          case (12 u)
          then show ?case using Cons_tuv.hyps by fastforce
        next
          case (13 u)
          then show ?case by (metis Cons_tuv.hyps Sync.sym SyncSingleHeadAdd)
        next
          case (14 u)
          then show ?case by (metis Cons_tuv.hyps Sync.sym SyncSingleHeadAdd)
        next
          case (15 u)
          then show ?case by (metis Cons_tuv.hyps Sync.sym SyncSingleHeadAdd)
        next
          case (16 u)
          then show ?case by (metis Cons_tuv.hyps Cons_tuv.prems(1) Sync.sym SyncSingleHeadAdd)
        next
          case (17 u)
          then show ?case by (metis Cons_tuv.hyps Sync.sym SyncSingleHeadAdd)
        next
          case (18 u)
          then show ?case using Cons_tuv.hyps by fastforce
        next
          case (19 u)
          then show ?case using Cons_tuv.hyps by fastforce
        next
          case (20 u)
          then show ?case by (metis Cons_tuv.hyps Cons_tuv.prems(1) Sync.sym SyncSingleHeadAdd)
        next
          case (21 u)
          then show ?case using Cons_tuv.hyps by fastforce
        qed
      qed
    qed
  qed 
qed

lemma interleave_assoc_2:
  assumes  *:"uv setinterleaves ((u, v), A)" and 
         **:"tuv setinterleaves ((t, uv), A)"
  shows "\<exists>tu. tu setinterleaves ((t, u), A) \<and> tuv setinterleaves ((tu, v), A)"
  using "*" "**" Sync.sym interleave_assoc_1 by blast

subsection\<open> Laws \<close>

lemma Sync_commute: "(P \<lbrakk> S \<rbrakk> Q) = (Q \<lbrakk> S \<rbrakk> P)"
  by (simp add: Process_eq_spec mono_D_Sync mono_F_Sync)

lemma mono_Sync_FD_oneside[simp]: "P \<le> P' \<Longrightarrow> (P \<lbrakk> S \<rbrakk> Q) \<le> (P' \<lbrakk> S \<rbrakk> Q)"
  apply(auto simp:le_ref_def F_Sync D_Sync) 
  using F_subset_imp_T_subset front_tickFree_Nil by blast+

lemma mono_Sync_FD[simp]: "\<lbrakk>P \<le> P'; Q \<le> Q'\<rbrakk> \<Longrightarrow> (P \<lbrakk> S \<rbrakk> Q) \<le> (P' \<lbrakk> S \<rbrakk> Q')"
  using mono_Sync_FD_oneside[of P P' S Q] mono_Sync_FD_oneside[of Q Q' S P]
  by (simp add: order_trans Sync_commute)

lemma mono_Sync_ref: "\<lbrakk>P \<sqsubseteq> P'; Q \<sqsubseteq> Q'\<rbrakk> \<Longrightarrow> (P \<lbrakk> S \<rbrakk> Q) \<sqsubseteq> (P' \<lbrakk> S \<rbrakk> Q')"
  using mono_Sync_sym[of Q Q' P S] mono_Sync[of P P' S Q'] below_trans by blast

lemma Sync_BOT: "(P \<lbrakk> S \<rbrakk> \<bottom>) = \<bottom>"
  apply(auto simp add:Process_eq_spec, simp_all add:D_Sync F_Sync F_UU D_UU)
     apply (metis D_imp_front_tickFree append_Nil2 front_tickFree_append ftf_Sync is_processT is_processT2_TR)
    apply (metis Nil_elem_T Sync.si_empty1 append_Nil front_tickFree_Nil insertI1 non_tickFree_implies_nonMt)
   apply (metis D_imp_front_tickFree append_Nil2 front_tickFree_append ftf_Sync is_processT2_TR)
  by (metis Nil_elem_T Sync.si_empty1 append_Nil front_tickFree_Nil insertI1 non_tickFree_implies_nonMt)

lemma Sync_SKIP_SKIP: "(SKIP \<lbrakk> S \<rbrakk> SKIP) = SKIP"
  apply(auto simp add:Process_eq_spec, simp_all add:D_Sync F_Sync F_SKIP D_SKIP)
  apply(elim exE conjE disjE, auto)
   apply (metis Sync.si_empty1 inf.idem insertI1 sup_commute sup_inf_absorb)
  apply(exI "[tick]", exI "[tick]", simp) 
  by blast

lemma Sync_SKIP_STOP: "(SKIP \<lbrakk>S\<rbrakk> STOP) = STOP"
proof(auto simp add:Process_eq_spec, simp_all add:D_Sync F_Sync F_SKIP D_SKIP F_STOP D_STOP, goal_cases)
  case (1 a b)
  then show ?case by (elim exE conjE disjE, auto)
next
  case (2 a b)
  then show ?case
    apply(rule_tac x="[]" in exI, simp, rule_tac x="b-{tick}" in exI, simp, rule_tac x="b" in exI) 
    by blast  
qed



subsection\<open> Multi-Operators laws  \<close>

lemma Mprefix_Sync_distr: 
  "\<lbrakk>A \<inter> S = {}; A' \<subseteq> S; B \<inter> S = {}; B' \<subseteq> S\<rbrakk> \<Longrightarrow> 
       (\<box> x \<in> A \<union> A' \<rightarrow> P x) \<lbrakk> S \<rbrakk> (\<box> y \<in> B \<union> B' \<rightarrow> Q y) = (\<box> x \<in> A       \<rightarrow> (                 P x  \<lbrakk> S \<rbrakk> (\<box> y \<in> B \<union> B' \<rightarrow> Q y)))
                                                         \<box> (\<box> y \<in> B       \<rightarrow> ((\<box> x \<in> A \<union> A' \<rightarrow> P x) \<lbrakk> S \<rbrakk>                  Q y))
                                                         \<box> (\<box> x \<in> A' \<inter> B' \<rightarrow> (                 P x  \<lbrakk> S \<rbrakk>                  Q x))"    
proof(auto simp add:Process_eq_spec, simp_all add:D_Sync F_Sync D_Mprefix F_Mprefix T_Mprefix D_Det F_Det T_Det,
      elim exE disjE conjE, goal_cases)
  case (1 a b t u X Y)
  then show ?case by auto
next
  case (2 a b t u X Y aa)
  have 21:\<open>a = u\<close> 
    using 2(5,7) EmptyLeftSync by blast
  hence 22:\<open>hd a \<in> ev ` B\<close>  
    using emptyLeftNonSync[rule_format, of a \<open>insert tick (ev ` S)\<close> u \<open>hd u\<close>, simplified]
          2(10,4,5,7,9) by auto
   with 2 show ?case 
     apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, simp add:21)
     apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, simp add:21) 
     apply(intro disjI2 conjI, simp_all add:21 22) 
     apply(exI aa, simp add:21) 
     apply(rule_tac disjI1, exI t, exI \<open>tl u\<close>, exI X, rule_tac conjI, simp, exI Y, simp) 
     by (meson SyncTlEmpty)
next
  case (3 a b t u X Y aa)
  have 31:\<open>a = t\<close>
     using "3"(6) "3"(8) EmptyLeftSync Sync.sym by blast
  hence 32:\<open>hd a \<in> ev ` A\<close>  
    using emptyLeftNonSync[rule_format, of a \<open>insert tick (ev ` S)\<close> t \<open>hd t\<close>] 
          3(10,2,5,6,8) Sync.sym by auto blast
  with 3 show ?case 
    apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, simp add:31)
    apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, simp add:31) 
    apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, simp_all add:31 32) 
    apply(exI aa, simp) 
    apply(rule_tac disjI1, exI \<open>tl t\<close>, exI u, exI X, rule_tac conjI, simp, exI Y, simp) 
    by (simp add: Sync.sym SyncTlEmpty)
next
  case (4 a b t u X Y aa ab)
  hence \<open>   (hd a = ev aa \<and> hd a \<in> ev ` A \<and> tl a setinterleaves ((tl t, u), insert tick (ev ` S))) 
             \<or> (hd a = ev ab \<and> hd a \<in> ev ` B \<and> tl a setinterleaves ((t, tl u), insert tick (ev ` S)))
             \<or> (hd a = ev ab \<and> aa = ab \<and> hd a \<in> ev ` (A' \<inter> B') \<and> tl a setinterleaves ((tl t, tl u), insert tick (ev ` S)))\<close> 
    using si_neq[of \<open>hd t\<close> \<open>tl t\<close> \<open>insert tick (ev ` S)\<close> \<open>hd u\<close> \<open>tl u\<close>]
    apply (simp del:si_neq split:if_splits) 
    apply (metis (no_types, lifting) IntI UnE disjoint_iff event.simps(1) event.simps(3) imageE imageI list.sel(1) list.sel(3))
    by(metis (no_types, opaque_lifting) UnE image_Un list.sel(1) list.sel(3) subset_eq subset_image_iff)+
  with 4 show ?case 
  proof(elim disjE conjE, goal_cases)
    case 41:1
    then show ?case
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis empty_setinterleaving)
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis empty_setinterleaving) 
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis empty_setinterleaving, simp_all)
      apply(exI aa, simp) 
      apply(rule_tac disjI1, exI \<open>tl t\<close>, exI u, exI X, rule_tac conjI, simp, exI Y, simp) 
      by blast
  next
    case 42:2
    then show ?case
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis empty_setinterleaving)
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis empty_setinterleaving) 
      apply(rule_tac disjI2, rule_tac disjI2, rule_tac disjI2, rule_tac conjI, metis empty_setinterleaving, simp_all)
      apply(exI ab, simp) 
      apply(rule_tac disjI1, exI t, exI \<open>tl u\<close>, exI X, rule_tac conjI)
      by blast+
  next
    case 43:3
    then show ?case
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis empty_setinterleaving)
      apply(rule_tac disjI2, rule_tac disjI2, rule_tac disjI2, rule_tac disjI2, rule_tac conjI, metis empty_setinterleaving, simp) 
      by(exI aa, simp, rule_tac disjI1, exI \<open>tl t\<close>, exI \<open>tl u\<close>, exI X, rule_tac conjI, simp, exI Y, simp)
  qed
next
  case (5 a b t u r v aa)
  have 51:\<open>a = t@v\<close>
     using 5(7,8,11) EmptyLeftSync Sync.sym by blast
  hence 52:\<open>hd a \<in> ev ` A\<close>  
    using emptyLeftNonSync[rule_format, of r \<open>insert tick (ev ` S)\<close> t \<open>hd t\<close>] 
          5(10,11,2,8,9) Sync.sym by auto blast
  with 5 show ?case 
    apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, simp add:51)
    apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, simp_all add:51) 
    apply(rule_tac disjI1, exI aa, simp)
    apply(rule_tac disjI2, exI \<open>tl t\<close>, exI u, exI \<open>tl r\<close>, exI v, simp)
    by (simp add: Sync.sym SyncTlEmpty tickFree_tl)
next
  case (6 a b t u r v aa ab)
  hence \<open>(hd r = ev aa \<and> hd r \<in> ev ` A \<and> tl r setinterleaves ((tl t, u), insert tick (ev ` S))) 
         \<or> (hd r = ev ab \<and> hd r \<in> ev ` B \<and> tl r setinterleaves ((t, tl u), insert tick (ev ` S)))\<close>  
    using si_neq[of \<open>hd t\<close> \<open>tl t\<close> \<open>insert tick (ev ` S)\<close> \<open>hd u\<close> \<open>tl u\<close>]
    apply(simp del:si_neq split:if_splits, blast, metis empty_iff list.collapse) 
      apply(metis (no_types, lifting) event.simps(3) image_eqI insert_iff SyncHd_Tl)
     defer
     apply blast

  proof -
    assume a1: \<open>hd t \<notin> ev ` S\<close>
       and a2: \<open>setinterleaving (t, insert tick (ev ` S), ev ab # tl u) =
                {hd t # ua |ua. ua setinterleaves ((tl t, ev ab # tl u), insert tick (ev ` S))}
                \<union> {ev ab # ua |ua. ua setinterleaves ((t, tl u), insert tick (ev ` S))}\<close>
    have f3: "ev ab \<in> ev ` B"
      using "6"(13) by blast
    have f4: "hd t \<in> ev ` A"
      using a1 "6"(10) "6"(2) by blast
    show \<open>hd r = hd t \<and> hd r \<in> ev ` A \<and> tl r setinterleaves ((tl t, u), insert tick (ev ` S)) \<or>
          hd r = ev ab \<and> hd r \<in> ev ` B \<and> tl r setinterleaves ((t, tl u), insert tick (ev ` S))\<close>
      apply auto
      using "6"(8) a2 "6"(14) "6"(15) hd_Cons_tl apply fastforce
      using "6"(8) a2 "6"(14) "6"(15) f4 hd_Cons_tl apply fastforce
      using "6"(8) a2 "6"(14) "6"(15) hd_Cons_tl apply fastforce
      using "6"(8) a2 "6"(14) "6"(15) f3 hd_Cons_tl apply fastforce
      using "6"(8) a2 "6"(14) "6"(15) f3 hd_Cons_tl apply fastforce
      using "6"(8) a2 "6"(14) "6"(15) f4 f3 hd_Cons_tl apply fastforce
      using "6"(13) "6"(8) a2 "6"(14) "6"(15) hd_Cons_tl apply fastforce
      using "6"(8) a2 "6"(14) "6"(15) f4 hd_Cons_tl apply fastforce
      using "6"(8) a2 "6"(14) "6"(15) hd_Cons_tl by fastforce
  qed
  with 6 show ?case
  proof(elim disjE conjE, goal_cases)
    case 61:1
    then show ?case
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving) 
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving) 
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving, simp_all)
      apply(rule_tac conjI, metis empty_setinterleaving hd_append2)
      apply(exI aa, rule_tac conjI, metis empty_setinterleaving hd_append2)   
      apply(rule_tac disjI2, exI \<open>tl t\<close>, exI u, exI \<open>tl r\<close>, exI v) 
      by (metis empty_setinterleaving tickFree_tl tl_append2)    
  next
    case 62:2
    then show ?case
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving)
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving) 
      apply(rule_tac disjI2, rule_tac disjI2, rule_tac disjI2, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving)
      apply(rule_tac conjI, metis empty_setinterleaving hd_append2)
      apply(exI ab, rule_tac conjI, metis empty_setinterleaving hd_append2) 
      apply(rule_tac disjI2, exI t, exI \<open>tl u\<close>, exI \<open>tl r\<close>, exI v)       
      by (metis empty_setinterleaving tickFree_tl tl_append2)    
  qed
next
  case (7 a b t u r v aa ab)
  hence \<open>   (hd r = ev aa \<and> hd r \<in> ev ` A \<and> tl r setinterleaves ((tl t, u), insert tick (ev ` S))) 
             \<or> (hd r = ev ab \<and> aa = ab \<and> hd r \<in> ev ` (A' \<inter> B') \<and> tl r setinterleaves ((tl t, tl u), insert tick (ev ` S)))\<close> 
    using si_neq[of \<open>hd t\<close> \<open>tl t\<close> \<open>insert tick (ev ` S)\<close> \<open>hd u\<close> \<open>tl u\<close>]
    apply (simp del:si_neq split:if_splits)
    apply (metis (no_types, opaque_lifting) IntI UnE empty_iff event.inject imageE imageI insert_iff SyncSameHdTl) 
       apply (metis empty_iff hd_Cons_tl, blast, blast) 
  proof
    assume a1: "ev ab \<in> ev ` S"
    assume a2: "hd t \<notin> ev ` S"
    assume a3: "hd t \<noteq> tick"
    assume a4: "hd u = ev ab"
    assume a5: "hd t \<in> ev ` (A \<union> A')"
    assume a7: "A' \<subseteq> S"
    show \<open>hd r = hd t \<and> hd r \<in> ev ` A \<and> tl r setinterleaves ((tl t, u), insert tick (ev ` S))\<close>
      apply safe
        apply (metis "7"(8) Sync.sym a1 a2 a3 a4 insertCI insertE SyncHd_Tl)
       apply (metis "7"(8) Sync.sym Un_iff a1 a2 a4 a5 a7 image_Un insert_iff sup.absorb_iff2 SyncHd_Tl SyncSameHdTl)
      by (metis "7"(8) Sync.sym a1 a2 a3 a4 insertCI insertE SyncHd_Tl)
  qed
  with 7 show ?case 
  proof(elim disjE conjE, goal_cases)
    case 71:1
    then show ?case
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving) 
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving) 
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving, simp_all)
      apply(rule_tac conjI, metis empty_setinterleaving hd_append2)
      apply(exI aa, rule_tac conjI, metis empty_setinterleaving hd_append2)   
      apply(rule_tac disjI2, exI \<open>tl t\<close>, exI u, exI \<open>tl r\<close>, exI v) 
      by (metis empty_setinterleaving tickFree_tl tl_append2)    
  next
    case 72:2
    then show ?case
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving)
      apply(rule_tac disjI2, rule_tac disjI2, rule_tac disjI2, rule_tac disjI2, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving) 
      apply(rule_tac conjI, metis empty_setinterleaving hd_append2)
      apply (exI aa, rule_tac conjI, metis empty_setinterleaving hd_append2)
      apply (rule_tac disjI2, exI \<open>tl t\<close>, exI \<open>tl u\<close>, exI \<open>tl r\<close>, exI v) 
      by (metis empty_setinterleaving tickFree_tl tl_append2)    
  qed    
next
  case (8 a b u t r v aa)
  have 81:\<open>r = u\<close>
     using 8 EmptyLeftSync Sync.sym by blast
  hence 82:\<open>hd r \<in> ev ` B\<close>  
    using emptyLeftNonSync[rule_format, of r \<open>insert tick (ev ` S)\<close> u \<open>hd u\<close>] 
          8 Sync.sym by auto blast
  with 8 show ?case 
     apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, simp add:81) 
     apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving) 
     apply(intro disjI2 conjI, simp_all add:81 82) 
     apply(exI aa, simp add:81) 
     apply(rule_tac disjI2,  exI \<open>tl u\<close>, exI t, exI \<open>tl r\<close>, exI v) 
    by (simp add: "81" Sync.sym SyncTlEmpty tickFree_tl)
next
  case (9 a b u t r v ab aa)
  hence \<open>(hd r = ev aa \<and> hd r \<in> ev ` A \<and> tl r setinterleaves ((tl t, u), insert tick (ev ` S))) 
         \<or> (hd r = ev ab \<and> hd r \<in> ev ` B \<and> tl r setinterleaves ((t, tl u), insert tick (ev ` S)))\<close>  
    using si_neq[of \<open>hd t\<close> \<open>tl t\<close> \<open>insert tick (ev ` S)\<close> \<open>hd u\<close> \<open>tl u\<close>]
    apply(simp del:si_neq split:if_splits, metis disjoint_iff event.inject image_iff, blast, blast) 
     apply (simp add: Sync.sym image_Un list.exhaust_sel rev_image_eqI sup.absorb_iff2)
     defer
    apply (metis (no_types, lifting) Sync.sym event.simps(3) imageI insertE insertI2 SyncHd_Tl) 
  proof -
    assume a1: "hd u \<in> ev ` B \<or> hd u \<in> ev ` B'"
    assume a2: "r setinterleaves ((t, u), insert tick (ev ` S))"
    assume a3: "setinterleaving (u, insert tick (ev ` S), ev aa # tl t) = 
                {ev aa # ua |ua. ua setinterleaves ((u, tl t), insert tick (ev ` S))} \<union> 
                {hd u # ua |ua. ua setinterleaves ((tl u, ev aa # tl t), insert tick (ev ` S))}"
    assume a4: "hd t = ev aa"
    assume a5: "t \<noteq> []"
    assume a6: "aa \<in> A"
    assume a7: "hd u \<notin> ev ` S"
    assume a8: "B' \<union> S = S"
    obtain ees :: "'a event list \<Rightarrow> 'a event list" where
      f9: "((\<nexists>es. r = hd u # es \<and> es setinterleaves ((tl u, ev aa # tl t), insert tick (ev ` S))) \<or> 
           r = hd u # ees r \<and> ees r setinterleaves ((tl u, ev aa # tl t), insert tick (ev ` S))) \<and> 
          ((\<exists>es. r = hd u # es \<and> es setinterleaves ((tl u, ev aa # tl t), insert tick (ev ` S))) \<or> 
          (\<forall>es. r \<noteq> hd u # es \<or> es \<notin> setinterleaving (tl u, insert tick (ev ` S), ev aa # tl t)))"
      by fastforce
    have f10: "ev aa # tl t = t"
      using a5 a4 hd_Cons_tl by fastforce
    then have f11: "r \<in> {ev aa # es |es. es setinterleaves ((u, tl t), insert tick (ev ` S))} \<union> 
                        {hd u # es |es. es setinterleaves ((tl u, ev aa # tl t), insert tick (ev ` S))}"
      using a3 a2 by (simp add: Sync.sym)
    have f12: "\<forall>e f a A. (e::'a event) \<noteq> f (a::'a) \<or> a \<notin> A \<or> e \<in> f ` A"
      by (meson image_eqI)
    moreover
    { assume "r \<noteq> hd u # ees r \<or> ees r \<notin> setinterleaving (tl u, insert tick (ev ` S), ev aa # tl t)"
      then obtain eesa :: "'a event list \<Rightarrow> 'a event list" where
        "r = ev aa # eesa r \<and> eesa r setinterleaves ((u, tl t), insert tick (ev ` S))"
        using f11 f9 by fast
      then have "hd r = ev aa \<and> hd r \<in> ev ` A \<and> tl r setinterleaves ((u, tl t), insert tick (ev ` S)) \<or> hd r = hd u \<and> hd r \<in> ev ` B \<and> tl r setinterleaves ((t, tl u), insert tick (ev ` S))"
        using f12 a6 by (metis list.sel(1) list.sel(3)) }
    ultimately show "hd r = ev aa \<and> hd r \<in> ev ` A \<and> tl r setinterleaves ((u, tl t), insert tick (ev ` S)) \<or> hd r = hd u \<and> hd r \<in> ev ` B \<and> tl r setinterleaves ((t, tl u), insert tick (ev ` S))"
      using f10 a8 a7 a1 by (metis Sync.sym UnI1 image_Un list.sel(1) list.sel(3))
  qed
  with 9 show ?case 
  proof(elim disjE conjE, goal_cases)
    case 91:1
    then show ?case
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving) 
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving) 
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving, simp)
      apply(rule_tac conjI, metis empty_setinterleaving hd_append image_eqI)
      apply(exI aa, rule_tac conjI, metis empty_setinterleaving hd_append2)   
      apply(rule_tac disjI2, exI u, exI \<open>tl t\<close>, exI \<open>tl r\<close>, exI v, simp)  
      by (metis Sync.sym empty_setinterleaving tickFree_tl tl_append2)
  next
    case 92:2
    then show ?case
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving) 
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving) 
      apply(rule_tac disjI2, rule_tac disjI2, rule_tac disjI2, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving, simp)
      apply(rule_tac conjI, metis empty_setinterleaving hd_append)
      apply(exI ab, rule_tac conjI, metis empty_setinterleaving hd_append2)   
      apply(rule_tac disjI2, exI \<open>tl u\<close>, exI \<open>t\<close>, exI \<open>tl r\<close>, exI v, simp)  
      by (metis Sync.sym empty_setinterleaving tickFree_tl tl_append2)
  qed 
next
  case (10 a b u t r v ab aa)
  hence \<open>   (hd r = ev ab \<and> hd r \<in> ev ` B \<and> tl r setinterleaves ((t, tl u), insert tick (ev ` S))) 
             \<or> (hd r = ev ab \<and> aa = ab \<and> hd r \<in> ev ` (A' \<inter> B') \<and> tl r setinterleaves ((tl t, tl u), insert tick (ev ` S)))\<close> 
    using si_neq[of \<open>hd t\<close> \<open>tl t\<close> \<open>insert tick (ev ` S)\<close> \<open>hd u\<close> \<open>tl u\<close>]
    apply (simp del:si_neq split:if_splits) 
    apply (metis (no_types, opaque_lifting) IntI Sync.sym UnE empty_iff event.inject image_iff insert_iff SyncSameHdTl)
       apply (metis insert_iff SyncSameHdTl)
    defer
      apply (metis imageI subsetD)
     apply (metis imageI subsetD)
  proof 
    assume a1: "hd u \<noteq> tick \<and> hd u \<notin> ev ` S"
    assume a2: "ev aa \<in> ev ` S"
    assume a3: "hd t = ev aa"
    assume a4: "r setinterleaves ((u, t), insert tick (ev ` S))"
    assume a5: "B' \<subseteq> S"
    show \<open>hd r = hd u \<and> hd r \<in> ev ` B \<and> tl r setinterleaves ((t, tl u), insert tick (ev ` S))\<close>
      apply safe
        apply (metis "10"(8) Sync.sym a1 a2 a3 insertCI insertE SyncHd_Tl)
       apply (metis (no_types, opaque_lifting) "10"(10) "10"(8) Sync.sym UnE a1 a2 a3 a5 image_Un insert_iff subset_eq subset_image_iff SyncHd_Tl)
      by (metis Sync.sym a1 a2 a3 a4 insertCI insertE SyncHd_Tl)
  qed
  with 10 show ?case 
  proof(elim disjE conjE, goal_cases)
    case 101:1
    then show ?case
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving) 
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving) 
      apply(rule_tac disjI2, rule_tac disjI2, rule_tac disjI2, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving, simp)
      apply(rule_tac conjI, metis empty_setinterleaving hd_append)
      apply(exI ab, rule_tac conjI, metis empty_setinterleaving hd_append2)   
      apply(rule_tac disjI2, exI \<open>tl u\<close>, exI \<open>t\<close>, exI \<open>tl r\<close>, exI v, simp)  
      by (metis Sync.sym empty_setinterleaving tickFree_tl tl_append2)   
  next
    case 102:2
    then show ?case
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving)
      apply(rule_tac disjI2, rule_tac disjI2, rule_tac disjI2, rule_tac disjI2, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving) 
      apply(rule_tac conjI, metis empty_setinterleaving hd_append2)
      apply (exI aa, rule_tac conjI, metis empty_setinterleaving hd_append2)
      apply (rule_tac disjI2, exI \<open>tl u\<close>, exI \<open>tl t\<close>, exI \<open>tl r\<close>, exI v, simp)
      by (metis Sync.sym empty_setinterleaving tickFree_tl tl_append2)
  qed    
next
  case (11 a b t u r v aa)
  have 111:\<open>a = t@v\<close>
     using 11(7,8,11) EmptyLeftSync Sync.sym by blast
  hence 112:\<open>hd a \<in> ev ` A\<close>  
    using emptyLeftNonSync[rule_format, of r \<open>insert tick (ev ` S)\<close> t \<open>hd t\<close>] 
          11(10,11,2,8,9) Sync.sym by auto blast
  with 11 show ?case 
    apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, simp add:111)
    apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, simp_all add:111) 
    apply(rule_tac disjI1, exI aa, simp)
    apply(rule_tac disjI2, exI \<open>tl t\<close>, exI u, exI \<open>tl r\<close>, exI v, simp)
    by (simp add: Sync.sym SyncTlEmpty tickFree_tl)
next
  case (12 a b t u r v aa ab)
  hence \<open>(hd r = ev aa \<and> hd r \<in> ev ` A \<and> tl r setinterleaves ((tl t, u), insert tick (ev ` S))) 
         \<or> (hd r = ev ab \<and> hd r \<in> ev ` B \<and> tl r setinterleaves ((t, tl u), insert tick (ev ` S)))\<close>  
    using si_neq[of \<open>hd t\<close> \<open>tl t\<close> \<open>insert tick (ev ` S)\<close> \<open>hd u\<close> \<open>tl u\<close>] 
    apply(simp del:si_neq split:if_splits, metis disjoint_iff event.inject image_iff, blast) 
      apply (metis (no_types, lifting) event.simps(3) imageI insert_iff SyncHd_Tl)
     defer apply blast
  proof -
    assume a1: "ab \<in> B"
    assume a2: "r setinterleaves ((t, u), insert tick (ev ` S))"
    assume a3: "setinterleaving (t, insert tick (ev ` S), ev ab # tl u) = 
                {hd t # ua |ua. ua setinterleaves ((tl t, ev ab # tl u), insert tick (ev ` S))} \<union> 
                {ev ab # ua |ua. ua setinterleaves ((t, tl u), insert tick (ev ` S))}"
    assume a4: "hd u = ev ab"
    assume a5: "u \<noteq> []"
    assume a6: "hd t \<in> ev ` (A \<union> A')"
    assume a7: "A' \<subseteq> S"
    assume a8: "hd t \<notin> ev ` S"
    have f9: "hd t \<in> ev ` A"
      using a8 a7 a6 by blast
    show "hd r = hd t \<and> hd r \<in> ev ` A \<and> tl r setinterleaves ((tl t, u), insert tick (ev ` S)) \<or> 
          hd r = ev ab \<and> hd r \<in> ev ` B \<and> tl r setinterleaves ((t, tl u), insert tick (ev ` S))"
    proof -
      obtain ees :: "'a event list \<Rightarrow> 'a event list" where
        f1: "((\<nexists>es. r = hd t # es \<and> es setinterleaves ((tl t, ev ab # tl u), insert tick (ev ` S))) \<or> 
              r = hd t # ees r \<and> ees r setinterleaves ((tl t, ev ab # tl u), insert tick (ev ` S))) \<and> 
             ((\<exists>es. r = hd t # es \<and> es setinterleaves ((tl t, ev ab # tl u), insert tick (ev ` S))) \<or> 
              (\<forall>es. r \<noteq> hd t # es \<or> es \<notin> setinterleaving (tl t, insert tick (ev ` S), ev ab # tl u)))"
        by meson
      have f2: "ev ab # tl u = u"
        using a5 by (subst a4[symmetric], rule list.collapse)
      moreover
      { assume "r \<noteq> hd t # ees r \<or> ees r \<notin> setinterleaving (tl t, insert tick (ev ` S), ev ab # tl u)"
        then obtain eesa :: "'a event list \<Rightarrow> 'a event list" where
          "r = ev ab # eesa r \<and> eesa r setinterleaves ((t, tl u), insert tick (ev ` S))"
          using f2 f1 a2 a3 by fastforce
        then have ?thesis
          by (metis a1 imageI list.sel(1) list.sel(3)) }
      ultimately show ?thesis
        by (metis (no_types) f9 list.sel(1) list.sel(3))
    qed 
  qed    
  with 12 show ?case 
  proof(elim disjE conjE, goal_cases)
    case 121:1
    then show ?case
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving) 
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving) 
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving, simp)
      apply(exI aa, rule_tac conjI, simp)   
      by (rule_tac disjI2, exI \<open>tl t\<close>, exI u, exI \<open>tl r\<close>, exI v, simp)  
  next
    case 122:2
    then show ?case
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving) 
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving) 
      apply(rule_tac disjI2, rule_tac disjI2, rule_tac disjI2, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving, simp)
      by (rule_tac disjI2, exI \<open>t\<close>, exI \<open>tl u\<close>, exI \<open>tl r\<close>, exI v, simp)  blast
  qed
next
  case (13 a b t u r v aa ab)
  hence \<open>   (hd r = ev aa \<and> hd r \<in> ev ` A \<and> tl r setinterleaves ((tl t, u), insert tick (ev ` S))) 
             \<or> (hd r = ev ab \<and> aa = ab \<and> hd r \<in> ev ` (A' \<inter> B') \<and> tl r setinterleaves ((tl t, tl u), insert tick (ev ` S)))\<close> 
    using si_neq[of \<open>hd t\<close> \<open>tl t\<close> \<open>insert tick (ev ` S)\<close> \<open>hd u\<close> \<open>tl u\<close>]
    apply (simp del:si_neq split:if_splits)
    apply (metis (no_types, opaque_lifting) IntI UnE empty_iff event.inject image_iff insert_iff SyncSameHdTl) 
       apply (metis empty_iff hd_Cons_tl, blast, blast) 
  proof
    assume a1: \<open>r setinterleaves ((t, u), insert tick (ev ` S))\<close>
    assume a2: \<open>hd t \<in> ev ` (A \<union> A')\<close>
    assume a3: \<open>hd t \<noteq> tick\<close>
    assume a4: \<open>hd t \<notin> ev ` S\<close>
    assume a5: \<open>ev ab \<in> ev ` S\<close>
    assume a6: \<open>setinterleaving (t, insert tick (ev ` S), ev ab # tl u) = {hd t # ua |ua. ua setinterleaves ((tl t, ev ab # tl u), insert tick (ev ` S))}\<close>
    show \<open>hd r = hd t \<and> hd r \<in> ev ` A \<and> tl r setinterleaves ((tl t, u), insert tick (ev ` S))\<close>
      apply safe
      using "13"(14) "13"(15) "13"(8) a6 list.collapse apply fastforce 
      using "13"(14) "13"(15) "13"(2) a1 a2 a4 a6 list.collapse apply fastforce
      by (metis "13"(15) Sync.sym a5 a3 a4 a1 insertCI insertE SyncHd_Tl)
  qed
  with 13 show ?case 
  proof(elim disjE conjE, goal_cases)
    case 131:1
    then show ?case
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving) 
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving) 
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving, simp_all)
      apply(exI aa, rule_tac conjI, simp)   
      apply(rule_tac disjI2, exI \<open>tl t\<close>, exI u, exI \<open>tl r\<close>, exI v)
      using 131(5) by blast 
  next
    case 132:2
    then show ?case
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving)
      apply(rule_tac disjI2, rule_tac disjI2, rule_tac disjI2, rule_tac disjI2, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving) 
      apply(rule_tac conjI, metis empty_setinterleaving hd_append2)
      apply (exI aa, rule_tac conjI, metis empty_setinterleaving hd_append2)
      apply (rule_tac disjI2, exI \<open>tl t\<close>, exI \<open>tl u\<close>, exI \<open>tl r\<close>, exI v) 
      by (metis empty_setinterleaving tl_append2)    
  qed    
next
  case (14 a b u t r v aa)
  have 141:\<open>r = u\<close>
     using 14 EmptyLeftSync Sync.sym by blast
  hence 142:\<open>hd r \<in> ev ` B\<close>  
    using emptyLeftNonSync[rule_format, of r \<open>insert tick (ev ` S)\<close> u \<open>hd u\<close>] 
          14 Sync.sym by auto blast
  with 14 show ?case 
     apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, simp add:141) 
     apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving) 
     apply(intro disjI2 conjI, simp_all add:141 142) 
     apply(exI aa, simp add:141) 
     apply(rule_tac disjI2,  exI \<open>tl u\<close>, exI t, exI \<open>tl r\<close>, exI v) 
    by (simp add: "141" Sync.sym SyncTlEmpty tickFree_tl)
next
  case (15 a b u t r v ab aa)
  hence \<open>(hd r = ev aa \<and> hd r \<in> ev ` A \<and> tl r setinterleaves ((tl t, u), insert tick (ev ` S))) 
         \<or> (hd r = ev ab \<and> hd r \<in> ev ` B \<and> tl r setinterleaves ((t, tl u), insert tick (ev ` S)))\<close>  
    using si_neq[of \<open>hd t\<close> \<open>tl t\<close> \<open>insert tick (ev ` S)\<close> \<open>hd u\<close> \<open>tl u\<close>]
    apply(simp del:si_neq split:if_splits, metis disjoint_iff event.inject image_iff, blast, blast) 
    defer
     apply (metis (no_types, lifting) Sync.sym event.simps(3) imageI insertE insertI2 SyncHd_Tl)
  proof -
    assume a1: "hd u \<in> ev ` (B \<union> B')"
    assume a2: "B' \<subseteq> S"
    assume a3: "hd u \<notin> ev ` S"
    assume a4: "r setinterleaves ((u, t), insert tick (ev ` S))"
    assume a5: "setinterleaving (ev aa # tl t, insert tick (ev ` S), u) = 
                {ev aa # ua |ua. ua setinterleaves ((tl t, u), insert tick (ev ` S))} \<union> 
                {hd u # ua |ua. ua setinterleaves ((ev aa # tl t, tl u), insert tick (ev ` S))}"
    assume a6: "hd t = ev aa"
    assume a7: "t \<noteq> []"
    assume a8: "aa \<in> A"
    have f9: "hd u \<in> ev ` B"
      using a3 a2 a1 by fast
    have f10: "ev aa # tl t = t"
      using a7 a6 hd_Cons_tl by fastforce
    then have "r \<in> {ev aa # es |es. es setinterleaves ((tl t, u), insert tick (ev ` S))} \<union> 
                   {hd u # es |es. es setinterleaves ((ev aa # tl t, tl u), insert tick (ev ` S))}"
      using a5 a4 by (simp add: Sync.sym)
    then show "hd r = ev aa \<and> hd r \<in> ev ` A \<and> tl r setinterleaves ((tl t, u), insert tick (ev ` S)) \<or> 
               hd r = hd u \<and> hd r \<in> ev ` B \<and> tl r setinterleaves ((t, tl u), insert tick (ev ` S))"
      using f10 f9 a8 by fastforce
  qed  
  with 15 show ?case 
  proof(elim disjE conjE, goal_cases)
    case 151:1
    then show ?case
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving) 
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving) 
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving, simp)
      apply(rule_tac disjI2, exI u, exI \<open>tl t\<close>, exI \<open>tl r\<close>, exI v, simp)
      using Sync.sym by blast
  next
    case 152:2
    then show ?case
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving) 
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving) 
      apply(rule_tac disjI2, rule_tac disjI2, rule_tac disjI2, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving, simp)
      apply(exI ab, rule_tac conjI, simp)   
      apply(rule_tac disjI2, exI \<open>tl u\<close>, exI \<open>t\<close>, exI \<open>tl r\<close>, exI v, simp)  
      by (metis Sync.sym)
  qed 
next
  case (16 a b u t r v ab aa)
  hence \<open>   (hd r = ev ab \<and> hd r \<in> ev ` B \<and> tl r setinterleaves ((t, tl u), insert tick (ev ` S))) 
             \<or> (hd r = ev ab \<and> aa = ab \<and> hd r \<in> ev ` (A' \<inter> B') \<and> tl r setinterleaves ((tl t, tl u), insert tick (ev ` S)))\<close> 
    using si_neq[of \<open>hd t\<close> \<open>tl t\<close> \<open>insert tick (ev ` S)\<close> \<open>hd u\<close> \<open>tl u\<close>]
    apply (simp del:si_neq split:if_splits) 
        apply (metis (no_types, opaque_lifting) "16"(11) "16"(3) Int_iff Sync.sym UnE empty_iff event.inject imageE imageI insertCI SyncSameHdTl)
       apply (metis insert_iff SyncSameHdTl)
      defer
      apply (metis imageI subsetD)
     apply (metis imageI subsetD)
  proof -
    assume a1: "hd u \<noteq> tick \<and> hd u \<notin> ev ` S"
    assume a2: "B' \<subseteq> S"
    assume a3: "hd u \<in> ev ` (B \<union> B')"
    assume a4: "r setinterleaves ((u, t), insert tick (ev ` S))"
    assume a5: "setinterleaving (ev aa # tl t, insert tick (ev ` S), u) = 
                {hd u # ua |ua. ua setinterleaves ((ev aa # tl t, tl u), insert tick (ev ` S))}"
    assume a6: "hd t = ev aa"
    assume a7: "t \<noteq> []"
    have f8: "B' \<union> S = S"
      using a2 by blast
    have f9: "ev aa # tl t = t"
      using a7 a6 hd_Cons_tl by fastforce
    then have "\<exists>es. r = hd u # es \<and> es setinterleaves ((ev aa # tl t, tl u), insert tick (ev ` S))"
      using a5 a4 by (simp add: Sync.sym)
    then show "hd r = hd u \<and> hd r \<in> ev ` B \<and> tl r setinterleaves ((t, tl u), insert tick (ev ` S)) \<or> 
               hd r = hd u \<and> aa = ab \<and> hd r \<in> ev ` (A' \<inter> B') \<and> tl r setinterleaves ((tl t, tl u), insert tick (ev ` S))"
      using f9 f8 a3 a1 by (metis Un_iff image_Un list.sel(1) list.sel(3))
  qed
  with 16 show ?case 
  proof(elim disjE conjE, goal_cases)
    case 161:1
    then show ?case
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving) 
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving) 
      apply(rule_tac disjI2, rule_tac disjI2, rule_tac disjI2, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving, simp)
      apply(exI ab, rule_tac conjI, simp)   
      apply(rule_tac disjI2, exI \<open>tl u\<close>, exI \<open>t\<close>, exI \<open>tl r\<close>, exI v, simp)  
      by (metis Sync.sym)   
  next
    case 162:2
    then show ?case
      apply(rule_tac disjI2, rule_tac disjI1, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving)
      apply(rule_tac disjI2, rule_tac disjI2, rule_tac disjI2, rule_tac disjI2, rule_tac conjI, metis append_is_Nil_conv empty_setinterleaving) 
      apply(rule_tac conjI, metis empty_setinterleaving hd_append2)
      apply (exI aa, rule_tac conjI, metis empty_setinterleaving hd_append2)
      apply (rule_tac disjI2, exI \<open>tl u\<close>, exI \<open>tl t\<close>, exI \<open>tl r\<close>, exI v, simp)
      by (metis Sync.sym)
  qed 
next 
  case (17 aA bB)
  have tact:\<open>\<And>P Q. \<nexists>t u r v. P t u r v \<Longrightarrow> Q \<or> (\<exists> t u r v. P t u r v) \<Longrightarrow> Q\<close>
    by fastforce
  from 17 show ?case 
  proof (safe, goal_cases)
    case 1
    obtain X where 11: "(X::'a event set)= bB - ev ` A'" by auto 
    obtain Y where 12: "(Y::'a event set)= bB - ev ` B'" by auto 
    from 1 11 12 have 13: "bB = (X \<union> Y) \<inter> insert tick (ev ` S) \<union> X \<inter> Y" 
      by auto
    with 11 12 1 show ?case 
      apply(exI \<open>[]\<close>, exI \<open>[]\<close>, exI X, rule_tac conjI) 
       apply safe
            apply (metis disjoint_iff_not_equal imageI)
           apply (metis image_iff)
          apply (metis disjoint_iff imageI)  
         apply (metis IntI image_eqI)
        apply (metis image_eqI)
       apply (metis rev_image_eqI)
      by (exI Y) (simp add: disjoint_iff image_Un)
  next
    case (2 x a t u X Y)
    then show ?case
      apply(erule_tac tact)
      apply(rule_tac disjI1, exI \<open>ev x#t\<close>, exI \<open>[]\<close>, exI X, rule conjI, simp)
      by (exI Y, simp, metis disjoint_iff event.inject hd_Cons_tl imageE)
  next
    case (3 x a t u X Y xa aa)
    then show ?case 
      apply(erule_tac tact)
      apply(rule_tac disjI1, exI \<open>ev x#t\<close>, exI \<open>u\<close>, exI X, rule conjI, simp)
      apply (exI Y, simp)
      using hd_Cons_tl SyncSingleHeadAdd by fastforce+
  next
    case (4 x a t u X Y xa aa)
    then show ?case
      apply(erule_tac tact)
      apply(rule_tac disjI1, exI \<open>ev x#t\<close>, exI \<open>u\<close>, exI X, rule conjI, simp)
      apply (exI Y, simp)
      using hd_Cons_tl SyncSingleHeadAdd by fastforce+
  next
    case (5 x a t u r v)
    then show ?case
      apply(erule_tac tact)
      apply(rule_tac disjI2, exI \<open>ev x#t\<close>, exI \<open>[]\<close>, exI \<open>ev x#r\<close>, exI v, simp)   
      by (metis disjoint_iff event.inject hd_Cons_tl imageE)
  next
    case (6 x a t u r v aa)
    then show ?case
      apply(erule_tac tact)
      apply(rule_tac disjI2, exI \<open>ev x#t\<close>, exI \<open>u\<close>, exI \<open>ev x#r\<close>, exI v, simp)      
      using hd_Cons_tl SyncSingleHeadAdd by fastforce+
  next
    case (7 x a t u r v aa)
    then show ?case
      apply(erule_tac tact)
      apply(rule_tac disjI2, exI \<open>ev x#t\<close>, exI \<open>u\<close>, exI \<open>ev x#r\<close>, exI v, simp)      
      using hd_Cons_tl SyncSingleHeadAdd by fastforce+
  next
    case (8 x a u t r v xa aa)
    then show ?case 
      apply(erule_tac tact)
      apply(rule_tac disjI2, exI \<open>u\<close>, exI \<open>ev x#t\<close>, exI \<open>ev x#r\<close>, exI \<open>v\<close>, simp)           
      using si_neq[of \<open>ev x\<close> \<open>t\<close> \<open>insert tick (ev ` S)\<close> \<open>hd u\<close> \<open>tl u\<close>]    
      apply (simp add: SyncSingleHeadAdd split: if_splits, blast, blast)
      by (metis Sync.sym SyncSingleHeadAdd event.distinct(1) insert_iff list.collapse) blast
  next
    case (9 x a u t r v xa aa)
    then show ?case      
      apply(erule_tac tact)
      apply(rule_tac disjI2, exI \<open>u\<close>, exI \<open>ev x#t\<close>, exI \<open>ev x#r\<close>, exI \<open>v\<close>, simp)           
      using si_neq[of \<open>ev x\<close> \<open>t\<close> \<open>insert tick (ev ` S)\<close> \<open>hd u\<close> \<open>tl u\<close>]    
      apply (simp add: SyncSingleHeadAdd split: if_splits, blast, blast, blast) 
      by (metis SyncHdAdd1 event.distinct(1) insert_iff list.collapse)
  next
    case (10 x a t u r v)
    then show ?case 
      apply(erule_tac tact)
      apply(rule_tac disjI2, exI \<open>ev x#t\<close>, exI \<open>[]\<close>, exI \<open>ev x#r\<close>, exI \<open>[]\<close>, simp)      
      by (metis disjoint_iff event.inject hd_Cons_tl imageE)
  next
    case (11 x a t u r v aa)
    then show ?case
      apply(erule_tac tact)
      apply(rule_tac disjI2, exI \<open>ev x#t\<close>, exI \<open>u\<close>, exI \<open>ev x#r\<close>, exI \<open>[]\<close>, simp)
      using SyncSingleHeadAdd list.collapse by fastforce
  next
    case (12 x a t u r v aa)
    then show ?case 
      apply(erule_tac tact)
      apply(rule_tac disjI2, exI \<open>ev x#t\<close>, exI \<open>u\<close>, exI \<open>ev x#r\<close>, exI \<open>[]\<close>, simp)
      using SyncSingleHeadAdd list.collapse by fastforce
  next
    case (13 x a u t r v xa aa)
    then show ?case
      apply(erule_tac tact)
      apply(rule_tac disjI2, exI \<open>u\<close>, exI \<open>ev x#t\<close>, exI \<open>ev x#r\<close>, exI \<open>[]\<close>, simp)      
      using si_neq[of \<open>ev x\<close> \<open>t\<close> \<open>insert tick (ev ` S)\<close> \<open>hd u\<close> \<open>tl u\<close>]
      apply (simp add: SyncSingleHeadAdd split: if_splits, blast, blast)
      by (metis Sync.sym SyncSingleHeadAdd event.distinct(1) insert_iff list.collapse) blast
  next
    case (14 x a u t r v xa aa)
    then show ?case 
      apply(erule_tac tact)
      apply(rule_tac disjI2, exI \<open>u\<close>, exI \<open>ev x#t\<close>, exI \<open>ev x#r\<close>, exI \<open>[]\<close>, simp)   
      using si_neq[of \<open>ev x\<close> \<open>t\<close> \<open>insert tick (ev ` S)\<close> \<open>hd u\<close> \<open>tl u\<close>]    
      apply (simp add: SyncSingleHeadAdd split: if_splits, blast, blast, blast)
      by (metis SyncHdAdd1 event.distinct(1) insert_iff list.collapse)
  next
    case (15 x a t u X Y)
    then show ?case 
      apply(erule_tac tact)
      apply(rule_tac disjI1, exI \<open>[]\<close>, exI \<open>ev x#u\<close>, exI X, rule conjI, simp)
      by (exI Y, simp, metis disjoint_iff event.inject hd_Cons_tl imageE)
  next
    case (16 x a t u X Y xa aa)
    then show ?case 
      apply(erule_tac tact)
      apply(rule_tac disjI1, exI \<open>t\<close>, exI \<open>ev x#u\<close>, exI X, rule conjI, simp, exI Y, simp)
      using si_neq[of \<open>hd t\<close> \<open>tl t\<close> \<open>insert tick (ev ` S)\<close> \<open>ev x\<close> \<open>tl u\<close>]    
      apply (simp add: SyncSingleHeadAdd split: if_splits, blast, blast, blast)
      by (metis Sync.sym SyncSingleHeadAdd event.distinct(1) insert_iff list.collapse) blast
  next
    case (17 x a t u X Y xa aa)
    then show ?case 
      apply(erule_tac tact)
      apply(rule_tac disjI1, exI \<open>t\<close>, exI \<open>ev x#u\<close>, exI X, rule conjI, simp)      
      apply (exI Y, simp) 
      using si_neq[of \<open>hd t\<close> \<open>tl t\<close> \<open>insert tick (ev ` S)\<close> \<open>ev x\<close> \<open>tl u\<close>]    
      apply (simp add: SyncSingleHeadAdd split: if_splits, blast, blast) sledgehammer
      using SyncHdAdd by fastforce blast+
  next
    case (18 x a t u r v xa aa)
    then show ?case
      apply(erule_tac tact)
      apply(rule_tac disjI2, exI \<open>t\<close>, exI \<open>ev x#u\<close>, exI \<open>ev x#r\<close>, exI \<open>v\<close>, simp)           
      using si_neq[of \<open>hd t\<close> \<open>tl t\<close> \<open>insert tick (ev ` S)\<close> \<open>ev x\<close> \<open>u\<close>]    
      apply (simp add: SyncSingleHeadAdd split: if_splits, blast, blast, blast)
      by (metis Sync.sym SyncSingleHeadAdd event.distinct(1) insert_iff list.collapse) blast
  next
    case (19 x a t u r v xa aa)
    then show ?case 
      apply(erule_tac tact)
      apply(rule_tac disjI2, exI \<open>t\<close>, exI \<open>ev x#u\<close>, exI \<open>ev x#r\<close>, exI \<open>v\<close>, simp)           
      using si_neq[of \<open>hd t\<close> \<open>tl t\<close> \<open>insert tick (ev ` S)\<close> \<open>ev x\<close> \<open>u\<close>]    
      apply (simp add: SyncSingleHeadAdd split: if_splits, blast, blast)
      by (metis SyncHdAdd1 event.distinct(1) insert_iff list.collapse) blast+
  next
    case (20 x a u t r v)
    then show ?case 
      apply(erule_tac tact)
      apply(rule_tac disjI2, exI \<open>ev x#u\<close>, exI \<open>[]\<close>, exI \<open>ev x#r\<close>, exI \<open>v\<close>, simp)      
      by (metis disjoint_iff event.inject hd_Cons_tl imageE)
  next
    case (21 x a u t r v aa)
    then show ?case 
      apply(erule_tac tact)
      apply(rule_tac disjI2, exI \<open>ev x#u\<close>, exI \<open>t\<close>, exI \<open>ev x#r\<close>, exI \<open>v\<close>, simp)
      using si_neq[of \<open>hd t\<close> \<open>tl t\<close> \<open>insert tick (ev ` S)\<close> \<open>ev x\<close> \<open>u\<close>]
      apply (simp add: SyncSingleHeadAdd split: if_splits, blast, blast, blast)
      by (metis list.collapse) blast
  next
    case (22 x a u t r v aa)
    then show ?case
      apply(erule_tac tact) 
      apply(rule_tac disjI2, exI \<open>ev x#u\<close>, exI \<open>t\<close>, exI \<open>ev x#r\<close>, exI \<open>v\<close>, simp)      
      using si_neq[of \<open>hd t\<close> \<open>tl t\<close> \<open>insert tick (ev ` S)\<close> \<open>ev x\<close> \<open>u\<close>]    
      apply (simp add: SyncSingleHeadAdd split: if_splits, blast, blast)
      by (metis list.exhaust_sel) blast+
  next
    case (23 x a t u r v xa aa)
    then show ?case
      apply(erule_tac tact)
      apply(rule_tac disjI2, exI \<open>t\<close>, exI \<open>ev x#u\<close>, exI \<open>ev x#r\<close>, exI \<open>[]\<close>, simp)           
      using si_neq[of \<open>hd t\<close> \<open>tl t\<close> \<open>insert tick (ev ` S)\<close> \<open>ev x\<close> \<open>u\<close>]    
      apply (simp add: SyncSingleHeadAdd split: if_splits, blast, blast, blast)
      by (metis Sync.sym SyncSingleHeadAdd event.distinct(1) insert_iff list.collapse) blast   
  next
    case (24 x a t u r v xa aa)
    then show ?case 
      apply(erule_tac tact)
      apply(rule_tac disjI2, exI \<open>t\<close>, exI \<open>ev x#u\<close>, exI \<open>ev x#r\<close>, exI \<open>[]\<close>, simp)           
      using si_neq[of \<open>hd t\<close> \<open>tl t\<close> \<open>insert tick (ev ` S)\<close> \<open>ev x\<close> \<open>u\<close>]    
      apply (simp add: SyncSingleHeadAdd split: if_splits, blast, blast) sledgehammer
      using SyncHdAdd1 list.collapse by fastforce blast+
  next
    case (25 x a t u r v)
    then show ?case 
      apply(erule_tac tact)
      apply(rule_tac disjI2, exI \<open>ev x#t\<close>, exI \<open>[]\<close>, exI \<open>ev x#r\<close>, exI \<open>[]\<close>, simp)      
      by (metis disjoint_iff event.inject hd_Cons_tl imageE)
  next
    case (26 x a u t r v aa)
    then show ?case 
      apply(erule_tac tact) 
      apply(rule_tac disjI2, exI \<open>ev x#u\<close>, exI \<open>t\<close>, exI \<open>ev x#r\<close>, exI \<open>[]\<close>, simp)      
      using si_neq[of \<open>hd t\<close> \<open>tl t\<close> \<open>insert tick (ev ` S)\<close> \<open>ev x\<close> \<open>u\<close>]    
      apply (simp add: SyncSingleHeadAdd split: if_splits, blast, blast, blast)
      by (metis list.collapse) blast
  next
    case (27 x a u t r v aa)
    then show ?case 
      apply(erule_tac tact) 
      apply(rule_tac disjI2, exI \<open>ev x#u\<close>, exI \<open>t\<close>, exI \<open>ev x#r\<close>, exI \<open>[]\<close>, simp)      
      using si_neq[of \<open>hd t\<close> \<open>tl t\<close> \<open>insert tick (ev ` S)\<close> \<open>ev x\<close> \<open>u\<close>]    
      apply (simp add: SyncSingleHeadAdd split: if_splits, blast, blast) sledgehammer
      by (metis list.collapse) blast+
  next
    case (28 x a t u X Y)
    then show ?case 
      apply(erule_tac tact)
      apply(rule_tac disjI1, exI \<open>ev x#t\<close>, exI \<open>ev x#u\<close>, exI X, rule conjI, simp)
      by (exI Y, simp, metis hd_Cons_tl image_eqI in_mono)
  next
    case (29 x a t u r v)
    then show ?case 
      apply(erule_tac tact)
      apply(rule_tac disjI2, exI \<open>ev x#t\<close>, exI \<open>ev x#u\<close>, exI \<open>ev x#r\<close>, exI \<open>v\<close>, simp)  
      by (metis image_eqI list.exhaust_sel subsetD)  
  next
    case (30 x a t u r v)
    then show ?case 
      apply(erule_tac tact)
      apply(rule_tac disjI2, exI \<open>ev x#t\<close>, exI \<open>ev x#u\<close>, exI \<open>ev x#r\<close>, exI \<open>v\<close>, simp)  
      by (metis image_eqI list.exhaust_sel subsetD)  
  next
    case (31 x a t u r v)
    then show ?case       
      apply(erule_tac tact)
      apply(rule_tac disjI2, exI \<open>ev x#t\<close>, exI \<open>ev x#u\<close>, exI \<open>ev x#r\<close>, exI \<open>[]\<close>, simp)  
      by (metis image_eqI list.exhaust_sel subsetD) 
  next
    case (32 x a t u r v)
    then show ?case 
      apply(erule_tac tact)
      apply(rule_tac disjI2, exI \<open>ev x#t\<close>, exI \<open>ev x#u\<close>, exI \<open>ev x#r\<close>, exI \<open>[]\<close>, simp)  
      by (metis image_eqI list.exhaust_sel subsetD) 
  qed
next
  case (18 aA)
  then show ?case
  proof(elim exE disjE conjE, goal_cases)
    case (1 t u r v a)
      have 11:\<open>r = t\<close>
        using 1 EmptyLeftSync Sync.sym by blast
      hence 12:\<open>hd aA \<in> ev ` A\<close>  
        using emptyLeftNonSync[rule_format, of r \<open>insert tick (ev ` S)\<close> t \<open>hd t\<close>] 
          1 Sync.sym by auto blast
    with 1 11 show ?case 
      apply(rule_tac disjI1, simp) 
      by (metis Sync.sym SyncTlEmpty tickFree_tl)
  next
    case (2 t u r v a aa)
    hence \<open>(hd r = ev a \<and> hd r \<in> ev ` A \<and> tl r setinterleaves ((tl t, u), insert tick (ev ` S))) 
         \<or> (hd r = ev aa \<and> hd r \<in> ev ` B \<and> tl r setinterleaves ((t, tl u), insert tick (ev ` S)))\<close>  
      using si_neq[of \<open>hd t\<close> \<open>tl t\<close> \<open>insert tick (ev ` S)\<close> \<open>hd u\<close> \<open>tl u\<close>]
      apply(simp del:si_neq split:if_splits, blast , metis empty_iff hd_Cons_tl) 
        apply (metis (no_types, lifting) event.simps(3) imageI insert_iff SyncHd_Tl) 
       defer
       apply blast
    proof(safe, simp_all add: in_mono, goal_cases)
      case (1 x)
      show ?case
        using "1"(18) "1"(21) "2"(14) "2"(15) "2"(8) list.collapse by fastforce
    next
      case (2 x)
      show ?case
        using "2"(13) "2"(14) "2"(18) "2"(20) "2"(21) "2"(8) list.collapse by fastforce
    next
      case (3 x)
      show ?case
        using "2"(14) "2"(15) "2"(8) "3"(18) "3"(21) list.collapse by fastforce
    next
      case (4 x)
      show ?case
        using "2"(13) "2"(14) "2"(15) "2"(8) "4"(18) "4"(21) list.collapse by fastforce 
    next
      case (5 x)
      show ?case
        using "2"(14) "2"(15) "2"(8) "5"(18) "5"(21) list.collapse by fastforce
    next
      case (6 x)
      show ?case
        using "6"(13) "6"(14) "6"(18) "6"(8) hd_Cons_tl "2"(13) "6"(20) "6"(21) by fastforce
    next
      case (7 x)
      show ?case
        using "2"(13) "2"(14) "2"(15) "2"(8) "7"(18) "7"(21) list.collapse by fastforce 
    next
      case (8 x)
      show ?case
        using "8"(20) "8"(21) "8"(13) "8"(14) "8"(18) "8"(8) hd_Cons_tl by fastforce
    next
      case (9 x)
      show ?case
        using "9"(21) "9"(13) "9"(14) "9"(13) "9"(14) "9"(18) "9"(8) hd_Cons_tl by fastforce
    qed
    with 2 show ?case 
      by (simp add: hd_append) (metis empty_setinterleaving tickFree_tl)
  next
    case (3 t u r v a aa)
    hence \<open>   (hd r = ev a \<and> hd r \<in> ev ` A \<and> tl r setinterleaves ((tl t, u), insert tick (ev ` S))) 
               \<or> (hd r = ev aa \<and> aa = a \<and> hd r \<in> ev ` (A' \<inter> B') \<and> tl r setinterleaves ((tl t, tl u), insert tick (ev ` S)))\<close> 
      using si_neq[of \<open>hd t\<close> \<open>tl t\<close> \<open>insert tick (ev ` S)\<close> \<open>hd u\<close> \<open>tl u\<close>]
      apply (simp del:si_neq split:if_splits) 
            apply (simp add:  UnE disjoint_iff imageE insertI2 rev_image_eqI)
            apply (metis (no_types, lifting) Int_iff Un_iff event.inject imageE image_eqI insertCI SyncSameHdTl)
         apply (metis insert_iff SyncSameHdTl)
        apply (metis imageI subsetD)
       apply (metis imageI subsetD) 
      by (metis (no_types, opaque_lifting) "3"(10) "3"(2) Sync.sym Un_iff image_Un subset_insertI sup.orderE SyncHd_Tl SyncSameHdTl)
    with 3 show ?case 
      by (simp add: hd_append) (metis Sync.sym empty_setinterleaving tickFree_tl)
  next
    case (4 u t r v a)
    have 41:\<open>r = u\<close>
      using 4 EmptyLeftSync Sync.sym by blast
    hence 42:\<open>hd aA \<in> ev ` B\<close>  
      using emptyLeftNonSync[rule_format, of r \<open>insert tick (ev ` S)\<close> u \<open>hd u\<close>] 
            4 Sync.sym by auto blast
    with 4 41 show ?case 
      apply(rule_tac disjI2, rule_tac disjI1, simp)       
      by (metis Sync.sym SyncTlEmpty tickFree_tl)
  next
    case (5 u t r v aa a)
    hence \<open>(hd r = ev a \<and> hd r \<in> ev ` A \<and> tl r setinterleaves ((tl t, u), insert tick (ev ` S))) 
         \<or> (hd r = ev aa \<and> hd r \<in> ev ` B \<and> tl r setinterleaves ((t, tl u), insert tick (ev ` S)))\<close>  
      using si_neq[of \<open>hd u\<close> \<open>tl u\<close> \<open>insert tick (ev ` S)\<close> \<open>hd t\<close> \<open>tl t\<close> ]
      apply(simp del:si_neq split:if_splits, blast, blast) 
        apply (metis (no_types, lifting) Sync.sym event.simps(3) imageI insert_iff SyncHd_Tl)
       defer
       apply blast
      proof(safe, simp_all add: in_mono, goal_cases)
      case (1 x)
      show ?case
        using "1"(13) "1"(14) "1"(18) "1"(21) "5"(8) list.collapse by fastforce
    next
      case (2 x)
      show ?case
        using "5"(14) "5"(15) "2"(18) "5"(8) "2"(21) "5"(13) list.collapse by fastforce 
    next
      case (3 x)
      show ?case
        using "3"(18) "3"(21) "5"(14) "5"(15) "5"(8) Sync.sym hd_Cons_tl by fastforce 
    next 
      case (4 x)
      show ?case
        using "4"(18) "4"(20) "4"(21) "5"(14) "5"(15) "5"(8) list.collapse by fastforce 
    next
      case (5 x)
      show ?case
        using "5"(13) "5"(14) "5"(18) "5"(21) "5"(8) Sync.sym hd_Cons_tl by fastforce
    next
      case (6 x)
      show ?case
        using "6"(20) "6"(21) "6"(13) "6"(14) "6"(18) "6"(8) "6"(12) Sync.sym hd_Cons_tl by fastforce
    next
      case (7 x)
      show ?case
        using "7"(18) "7"(13) "7"(14) "7"(8) "7"(20) "7"(21) Sync.sym hd_Cons_tl by fastforce
    next
      case (8 x)
      show ?case
        using "8"(13) "8"(14) hd_Cons_tl Sync.sym "8"(18) "8"(8) "8"(21) "8"(12) by fastforce
    next
      case (9 x)
      show ?case
        using "9"(14) "9"(13) list.collapse "9"(21) Sync.sym "9"(18) "9"(8) by fastforce
    qed
    with 5 show ?case
      by (simp add: hd_append) (metis Sync.sym empty_setinterleaving tickFree_tl)
  next
    case (6 u t r v aa a)
      hence \<open>   (hd r = ev aa \<and> hd r \<in> ev ` B \<and> tl r setinterleaves ((t, tl u), insert tick (ev ` S))) 
               \<or> (hd r = ev aa \<and> aa = a \<and> hd r \<in> ev ` (A' \<inter> B') \<and> tl r setinterleaves ((tl t, tl u), insert tick (ev ` S)))\<close> 
        using si_neq[of \<open>hd t\<close> \<open>tl t\<close> \<open>insert tick (ev ` S)\<close> \<open>hd u\<close> \<open>tl u\<close>]
        apply (simp del:si_neq split:if_splits) 
            apply (simp add:  UnE disjoint_iff imageE insertI2 rev_image_eqI)
            apply (metis (no_types, lifting) Int_iff Sync.sym Un_iff event.inject imageE image_eqI insertCI SyncSameHdTl)
           apply (metis insert_iff SyncSameHdTl)
          apply (metis (no_types, opaque_lifting) Sync.sym UnE image_Un insert_iff subset_eq subset_image_iff SyncHd_Tl SyncSameHdTl) 
         apply (metis imageI subsetD) 
        by (metis image_eqI subsetD)
      with 6 show ?case
        by (simp add: hd_append) (metis Sync.sym empty_setinterleaving tickFree_tl)
  next
    case (7 t u r v a)
    have 71:\<open>r = t\<close>
      using 7 EmptyLeftSync Sync.sym by blast
    hence 72:\<open>hd aA \<in> ev ` A\<close>  
      using emptyLeftNonSync[rule_format, of r \<open>insert tick (ev ` S)\<close> t \<open>hd t\<close>] 
        7 Sync.sym by auto blast
    with 7 71 show ?case 
      apply(rule_tac disjI1, simp) 
      by (metis Sync.sym append_self_conv front_tickFree_Nil SyncTlEmpty)
  next
    case (8 t u r v a aa)
    hence \<open>(hd r = ev a \<and> hd r \<in> ev ` A \<and> tl r setinterleaves ((tl t, u), insert tick (ev ` S))) 
         \<or> (hd r = ev aa \<and> hd r \<in> ev ` B \<and> tl r setinterleaves ((t, tl u), insert tick (ev ` S)))\<close>  
      using si_neq[of \<open>hd t\<close> \<open>tl t\<close> \<open>insert tick (ev ` S)\<close> \<open>hd u\<close> \<open>tl u\<close>]
      apply(simp del:si_neq split:if_splits, blast , metis empty_iff hd_Cons_tl) 
        apply (metis (no_types, lifting) event.simps(3) imageI insert_iff SyncHd_Tl) 
       defer
       apply blast
    proof(safe, simp_all add: in_mono, goal_cases)
      case (1 x)
      show ?case
        using "1"(17) "1"(20) "8"(14) "8"(15) "8"(8) list.collapse by fastforce
    next
      case (2 x)
      show ?case
        using "2"(12) "2"(13) hd_Cons_tl "2"(11) "8"(8) "2"(17) "2"(20) "2"(19) by fastforce
    next
      case (3 x)
      show ?case
        using "3"(12) "3"(13) "3"(17) "3"(20) "3"(7) "3"(8) Sync.sym hd_Cons_tl by fastforce
    next
      case (4 x)
      show ?case
        using "4"(11) "4"(17) "4"(20) "8"(14) "8"(15) "8"(8) list.collapse by fastforce
    next
      case (5 x)
      show ?case
        using "5"(17) "5"(12) "5"(13) "5"(7) "5"(8) "5"(20) list.collapse Sync.sym hd_Cons_tl by fastforce
    next
      case (6 x)
      show ?case
        using "6"(11) "6"(12) "6"(13) "6"(17) "6"(19) "6"(20) "6"(7) list.collapse by fastforce
    next
      case (7 x)
      show ?case
        using "7"(17) "7"(20) "8"(13) "8"(14) "8"(15) "8"(8) list.collapse by fastforce
    next
      case (8 x)
      show ?case
        using "8"(12) "8"(13) "8"(17) "8"(19) "8"(20) "8"(7) list.collapse by fastforce
    next
      case (9 x)
      show ?case
        using "9"(20) Sync.sym "9"(12) "9"(13) list.exhaust_sel "9"(12) "9"(13) "9"(17) "9"(7) Sync.sym hd_Cons_tl by fastforce
    qed
    with 8 show ?case 
      by (metis empty_setinterleaving self_append_conv)
  next
    case (9 t u r v a aa)
      hence \<open>   (hd r = ev a \<and> hd r \<in> ev ` A \<and> tl r setinterleaves ((tl t, u), insert tick (ev ` S))) 
               \<or> (hd r = ev aa \<and> aa = a \<and> hd r \<in> ev ` (A' \<inter> B') \<and> tl r setinterleaves ((tl t, tl u), insert tick (ev ` S)))\<close> 
        using si_neq[of \<open>hd t\<close> \<open>tl t\<close> \<open>insert tick (ev ` S)\<close> \<open>hd u\<close> \<open>tl u\<close>]
        apply (simp del:si_neq split:if_splits) 
            apply (simp add: disjoint_iff)
            apply (metis (no_types, lifting) Int_iff Un_iff event.inject imageE image_eqI insertCI SyncSameHdTl)
           apply (metis insert_iff SyncSameHdTl)
          apply (metis rev_image_eqI subsetD)
         apply (metis imageI subsetD) 
        by (metis (no_types, opaque_lifting) Sync.sym Un_iff image_Un insert_iff sup.absorb_iff2 SyncHd_Tl)
      with 9 show ?case
        by (metis empty_setinterleaving self_append_conv)
    next
      case (10 u t r v a)
      have 101:\<open>r = u\<close>
        using 10 EmptyLeftSync Sync.sym by blast
      hence 102:\<open>hd aA \<in> ev ` B\<close>  
        using emptyLeftNonSync[rule_format, of r \<open>insert tick (ev ` S)\<close> u \<open>hd u\<close>] 
            10 Sync.sym by auto blast
      with 10 101 show ?case 
        apply(rule_tac disjI2, rule_tac disjI1, simp) 
        by (metis Sync.sym append.right_neutral front_tickFree_Nil SyncTlEmpty)   
    next
      case (11 u t r v aa a)
      hence \<open>(hd r = ev a \<and> hd r \<in> ev ` A \<and> tl r setinterleaves ((tl t, u), insert tick (ev ` S))) 
         \<or> (hd r = ev aa \<and> hd r \<in> ev ` B \<and> tl r setinterleaves ((t, tl u), insert tick (ev ` S)))\<close>  
        using si_neq[of \<open>hd u\<close> \<open>tl u\<close> \<open>insert tick (ev ` S)\<close> \<open>hd t\<close> \<open>tl t\<close> ]
        apply(simp del:si_neq split:if_splits, blast, blast) 
          apply (metis (no_types, lifting) Sync.sym event.simps(3) imageI insert_iff SyncHd_Tl)
         defer
         apply blast
      proof(safe, simp_all add: in_mono, goal_cases)
        case (1 x)
        show ?case
          using "1"(17) "1"(20) "11"(14) "11"(15) "11"(8) list.collapse by fastforce
      next
        case (2 x)
        show ?case
          using "2"(12) "2"(13) hd_Cons_tl "2"(11) "11"(8) "2"(17) "2"(20) by fastforce
      next
        case (3 x)
        show ?case
          using "3"(12) "3"(13) "3"(17) "3"(20) "3"(7) "3"(8) Sync.sym hd_Cons_tl by fastforce
      next
        case (4 x)
        show ?case
          using "11"(14) "11"(15) "11"(8) "4"(17) "4"(19) "4"(20) list.collapse by fastforce
      next
        case (5 x)
        show ?case
          using "5"(17) "5"(12) "5"(13) "5"(7) "5"(8) "5"(20) list.collapse Sync.sym hd_Cons_tl by fastforce
      next
        case (6 x)
        show ?case
          using "6"(11) "6"(12) "6"(13) "6"(17) "6"(19) "6"(20) "6"(7) list.collapse by fastforce
      next
        case (7 x)
        show ?case
          using "7"(12) "7"(13) "7"(17) "7"(19) "7"(20) "7"(7) Sync.sym list.collapse by fastforce
      next
        case (8 x)
        show ?case
          using "8"(20) "8"(12) "8"(11) "8"(13) list.collapse Sync.sym "8"(12) "8"(13) "8"(17) "8"(7) hd_Cons_tl by fastforce
      next
        case (9 x)
        show ?case
          using "9"(20) Sync.sym "9"(12) "9"(13) list.exhaust_sel "9"(12) "9"(13) "9"(17) "9"(7) Sync.sym hd_Cons_tl by fastforce
      qed
      with 11 show ?case
        by (metis Sync.sym append.right_neutral empty_setinterleaving)
    next
      case (12 u t r v aa a)
      hence \<open>   (hd r = ev aa \<and> hd r \<in> ev ` B \<and> tl r setinterleaves ((t, tl u), insert tick (ev ` S))) 
             \<or> (hd r = ev aa \<and> aa = a \<and> hd r \<in> ev ` (A' \<inter> B') \<and> tl r setinterleaves ((tl t, tl u), insert tick (ev ` S)))\<close> 
      using si_neq[of \<open>hd t\<close> \<open>tl t\<close> \<open>insert tick (ev ` S)\<close> \<open>hd u\<close> \<open>tl u\<close>]
      apply (simp del:si_neq split:if_splits) 
            apply (simp add:  UnE disjoint_iff imageE insertI2 rev_image_eqI)
            apply (metis (no_types, lifting) Int_iff Sync.sym Un_iff event.inject imageE image_eqI insertCI SyncSameHdTl)
           apply (metis insert_iff SyncSameHdTl)
          apply (metis (no_types, opaque_lifting) Sync.sym UnE image_Un insert_iff subset_eq subset_image_iff SyncHd_Tl SyncSameHdTl) 
         apply (metis imageI subsetD) 
        by (metis image_eqI subsetD)
    with 12 show ?case
      by (metis (no_types, lifting) Sync.sym append_Nil2 empty_setinterleaving)
  qed    
next
  case (19 x)
  then show ?case 
  proof(elim exE disjE conjE, goal_cases)
    case (1 a t u r v)
    then show ?case 
      apply(exI \<open>ev a#t\<close>, exI u, exI \<open>ev a#r\<close>, exI v, simp)
      apply (safe, simp_all add: disjoint_iff image_iff SyncSingleHeadAdd)
       by (metis list.exhaust_sel)
  next
    case (2 a t u r v aa)
    then show ?case 
      apply(exI \<open>ev a#t\<close>, exI u, exI \<open>ev a#r\<close>, exI v, simp) 
      apply (safe, simp_all add: disjoint_iff image_iff SyncSingleHeadAdd)
       by (metis list.exhaust_sel)
  next
    case (3 a t u r v aa)
    then show ?case 
      apply(exI \<open>ev a#t\<close>, exI u, exI \<open>ev a#r\<close>, exI v, simp) 
      apply (safe, simp_all add: disjoint_iff image_iff SyncSingleHeadAdd)
       by (metis list.exhaust_sel)
  next
    case (4 a t u r v aa)
    then show ?case 
      apply(exI \<open>t\<close>, exI  \<open>ev a#u\<close>, exI \<open>ev a#r\<close>, exI v, simp)
      apply (safe, simp_all add: disjoint_iff image_iff in_mono SyncHdAdd1 SyncSingleHeadAdd)
        apply (metis list.exhaust_sel)
      apply (metis (no_types, opaque_lifting) Sync.sym event.inject event.simps(3) imageE insertE SyncSingleHeadAdd)
       by (metis list.exhaust_sel)
  next
    case (5 a t u r v)
    then show ?case
      apply(exI \<open>ev a#t\<close>, exI u, exI \<open>ev a#r\<close>, exI v, simp)
      apply (safe, simp_all)
       apply blast
      by (metis list.exhaust_sel)
  next
    case (6 a t u r v aa)
    then show ?case
      apply(exI \<open>ev a#t\<close>, exI u, exI \<open>ev a#r\<close>, exI v, simp) 
      apply (safe, simp_all add: disjoint_iff_not_equal image_iff SyncSingleHeadAdd)
       by (metis list.exhaust_sel)
  next
    case (7 a t u r v aa)
    then show ?case 
      apply(exI \<open>ev a#t\<close>, exI u, exI \<open>ev a#r\<close>, exI v, simp) 
      apply (safe, simp_all add: disjoint_iff_not_equal image_iff SyncSingleHeadAdd)
       by (metis list.exhaust_sel)
  next
    case (8 a t u r v aa)
    then show ?case 
      apply(exI \<open>t\<close>, exI  \<open>ev a#u\<close>, exI \<open>ev a#r\<close>, exI v, simp)
      apply (safe, simp_all add: disjoint_iff image_iff in_mono SyncHdAdd1)
        apply (metis list.exhaust_sel)
       apply (metis (no_types, lifting) Sync.sym event.distinct(1) event.inject imageE insertE SyncSingleHeadAdd)
      by (metis list.collapse)
  next
    case (9 a t u r v aa)
    then show ?case 
      apply(exI \<open>t\<close>, exI  \<open>ev a#u\<close>, exI \<open>ev a#r\<close>, exI v, simp)
      apply (safe, simp_all add: disjoint_iff image_iff in_mono SyncHdAdd1)
        apply (metis list.exhaust_sel)
       apply (metis (no_types, lifting) Sync.sym event.distinct(1) event.inject imageE insertE SyncSingleHeadAdd)
      by (metis list.collapse)
  next
    case (10 a t u r v)
    then show ?case 
      apply(exI \<open>ev a#t\<close>, exI u, exI \<open>ev a#r\<close>, exI v, simp)
      apply (safe, simp_all add: disjoint_iff image_iff SyncSingleHeadAdd)
      by (metis list.exhaust_sel)
  next
    case (11 a t u r v aa)
    then show ?case 
      apply(exI \<open>ev a#t\<close>, exI  \<open>u\<close>, exI \<open>ev a#r\<close>, exI v, simp) 
      apply (safe, simp_all add: disjoint_iff image_iff SyncSingleHeadAdd)
      by (metis list.exhaust_sel)
  next
    case (12 a t u r v aa)
    then show ?case      
      apply(exI \<open>ev a#t\<close>, exI  \<open>u\<close>, exI \<open>ev a#r\<close>, exI v, simp) 
      apply (safe, simp_all add: disjoint_iff image_iff SyncSingleHeadAdd)
      by (metis list.exhaust_sel)
  next
    case (13 a t u r v aa)
    then show ?case
      apply(exI \<open>t\<close>, exI  \<open>ev a#u\<close>, exI \<open>ev a#r\<close>, exI v, simp)
      apply (safe, auto simp add: disjoint_iff image_iff subset_eq SyncHdAdd1)
         apply (metis list.exhaust_sel)
        apply (metis (no_types, lifting) Sync.sym  event.inject event.simps(3) imageE insertE SyncSingleHeadAdd)
       by (metis hd_Cons_tl)
  next
    case (14 a t u r v)
    then show ?case 
      apply(exI \<open>ev a#t\<close>, exI u, exI \<open>ev a#r\<close>, exI v, simp)
      apply (safe, simp_all add: disjoint_iff image_iff SyncSingleHeadAdd)
      by (metis list.collapse)
  next
    case (15 a t u r v aa)
    then show ?case 
      apply(exI \<open>ev a#t\<close>, exI  \<open>u\<close>, exI \<open>ev a#r\<close>, exI v, simp) 
      apply (safe, simp_all add: disjoint_iff image_iff SyncSingleHeadAdd)
      by (metis list.exhaust_sel)
  next
    case (16 a t u r v aa)
    then show ?case 
      apply(exI \<open>ev a#t\<close>, exI  \<open>u\<close>, exI \<open>ev a#r\<close>, exI v, simp) 
      apply (safe, simp_all add: disjoint_iff image_iff SyncSingleHeadAdd)
      by (metis list.exhaust_sel)
  next
    case (17 a t u r v)
    then show ?case 
      apply(exI \<open>ev a#t\<close>, exI  \<open>ev a#u\<close>, exI \<open>ev a#r\<close>, exI v, simp) 
      apply (safe, simp_all)
        apply (metis list.exhaust_sel)
      by blast+
  next
    case (18 a t u r v)
    then show ?case 
      apply(exI \<open>ev a#t\<close>, exI  \<open>ev a#u\<close>, exI \<open>ev a#r\<close>, exI v, simp) 
      apply (safe, simp_all)
        apply (metis list.exhaust_sel)
      by blast+
  next
    case (19 a t u r v)
    then show ?case 
      apply(exI \<open>ev a#t\<close>, exI  \<open>ev a#u\<close>, exI \<open>ev a#r\<close>, exI v, simp) 
      apply (safe, simp_all)
        apply (metis list.exhaust_sel)
      by blast+
  next
    case (20 a t u r v)
    then show ?case 
      apply(exI \<open>ev a#t\<close>, exI  \<open>ev a#u\<close>, exI \<open>ev a#r\<close>, exI v, simp) 
      apply (safe, simp_all)
        apply (metis list.exhaust_sel)
      by blast+
  qed
qed


(* useful version for later *)
lemma Mprefix_Sync_distr_bis: 
  \<open>(Mprefix A P) \<lbrakk>S\<rbrakk> (Mprefix B Q) =
   (\<box>x\<in>A - S \<rightarrow> (P x \<lbrakk>S\<rbrakk> Mprefix B Q)) \<box> (\<box>y\<in>B - S \<rightarrow> (Mprefix A P \<lbrakk>S\<rbrakk> Q y)) \<box> (\<box>x\<in>A \<inter> B \<inter> S \<rightarrow> (P x \<lbrakk>S\<rbrakk> Q x))\<close>
  by (subst Mprefix_Sync_distr[of \<open>A - S\<close> S \<open>A \<inter> S\<close> \<open>B - S\<close> \<open>B \<inter> S\<close>, simplified Un_Diff_Int])
     (simp_all add: Int_commute inf_left_commute)


lemmas Mprefix_Sync_distr_subset = Mprefix_Sync_distr[where A = \<open>{}\<close> and B = \<open>{}\<close>, simplified, simplified Mprefix_STOP Det_STOP trans[OF Det_commute Det_STOP]]
   and  Mprefix_Sync_distr_indep = Mprefix_Sync_distr[where A'= \<open>{}\<close> and B'= \<open>{}\<close>, simplified, simplified Mprefix_STOP Det_STOP] 
   and  Mprefix_Sync_distr_right = Mprefix_Sync_distr[where A = \<open>{}\<close> and B'= \<open>{}\<close>, simplified, simplified Mprefix_STOP Det_STOP trans[OF Det_commute Det_STOP], rotated] 
   and   Mprefix_Sync_distr_left = Mprefix_Sync_distr[where A'= \<open>{}\<close> and B = \<open>{}\<close>, simplified, simplified Mprefix_STOP Det_STOP trans[OF Det_commute Det_STOP]]


lemma Mprefix_Sync_SKIP: "(Mprefix B P \<lbrakk> S \<rbrakk> SKIP) = (\<box> x \<in>  B - S \<rightarrow> (P x \<lbrakk> S \<rbrakk> SKIP))"
proof (auto simp add:Process_eq_spec_optimized, goal_cases)
  case (1 x)
  then show ?case
  proof(simp_all add:D_Sync D_Mprefix D_SKIP T_SKIP, elim exE conjE, goal_cases)
      case (1 t u r v a)
      then show ?case 
        apply(intro conjI) 
          using empty_setinterleaving apply blast
         apply(elim disjE)
            apply (metis (no_types, lifting) DiffI Sync.sym emptyLeftProperty empty_iff hd_append2 image_diff_subset insertI2 list.exhaust_sel setinterleaving.simps(2) subsetCE)
           apply (metis D_imp_front_tickFree Sync.sym TickLeftSync empty_iff empty_setinterleaving event.distinct(1) ftf_Sync21 insertI1 list.expand list.sel(1) list.set_intros(1) SyncHd_Tl SyncSameHdTl tickFree_def)
          using Sync.sym emptyLeftNonSync emptyLeftProperty hd_in_set apply fastforce
         apply (metis (no_types, lifting) DiffI Sync.sym append_Nil2 event.distinct(1) image_diff_subset insertI1 insertI2 list.sel(1) subsetCE SyncHd_Tl SyncSameHdTl)
        apply(rule_tac x="a" in exI, intro conjI) 
         apply (metis Sync.sym emptyLeftProperty empty_setinterleaving hd_append2 insertI1 list.sel(1) SyncHd_Tl SyncSameHdTl)
        apply(rule_tac x="tl t" in exI, rule_tac x="u" in exI, rule_tac x="tl r" in exI, rule_tac x="v" in exI)
        by (metis (no_types, lifting) Sync.sym empty_setinterleaving event.distinct(1) insertI1 list.sel(1) SyncHd_Tl SyncSameHdTl SyncTlEmpty tickFree_tl tl_append2)
  qed
next
  case (2 x)
  then show ?case 
    proof(simp_all add:D_Sync D_Mprefix D_SKIP T_SKIP, elim exE conjE, goal_cases)
      case (1 a t u r v)
      then show ?case  
        apply(rule_tac x="hd x#t" in exI, rule_tac x="u" in exI, rule_tac x="hd x#r" in exI,
              rule_tac x="v" in exI, auto)      
        using hd_Cons_tl list.exhaust_sel by force+
    qed 
next
  case (3 a b)
  then show ?case
  proof(simp add:F_Sync F_Mprefix F_SKIP, elim exE disjE, simp_all, goal_cases)
    case (1 t u X)
    { fix X Y A B
      assume "b = (X \<union> Y) \<inter> insert tick (ev ` B) \<union> X \<inter> Y" and "X \<inter> ev ` A = {}" and "tick \<notin> Y"
      hence "b \<inter> ev ` (A - B) = {}" by (rule_tac equals0I, auto) 
    } note l1 = this
    from 1 show ?case
      apply(elim exE conjE disjE)
          using l1 apply simp
         apply(rule disjI2, simp)
        apply(intro disjI2 conjI)
          using empty_setinterleaving apply blast
         apply (metis (no_types, opaque_lifting) DiffI Sync.sym UnI2 contra_subsetD emptyLeftNonSync 
                emptyLeftProperty hd_in_set image_diff_subset insert_is_Un) 
        apply (metis Sync.sym Un_commute emptyLeftProperty list.sel(1) list.sel(3) neq_Nil_conv SyncTlEmpty)
       apply(intro disjI2 conjI)       
         using empty_setinterleaving apply blast
        apply (metis (no_types, opaque_lifting) DiffI Sync.sym event.distinct(1) event.inject 
                     imageE image_eqI insertI1 insertI2 list.sel(1) SyncHd_Tl SyncSameHdTl)
       apply (metis Sync.sym event.distinct(1) insertI1 list.sel(1) SyncHd_Tl SyncSameHdTl)
       done
  next
    case (2 t u r v)
    from 2(2) have "a \<in> \<D> (Mprefix B P \<lbrakk>S\<rbrakk> SKIP)" 
      apply(simp add:D_Sync) using T_SKIP by blast
    with 2(3) have "a \<in> \<D> (\<box> x \<in>  B - S \<rightarrow> (P x \<lbrakk> S \<rbrakk> SKIP))" by simp
    with 2(2) show ?case 
      by (simp add:D_Sync D_Mprefix, rule_tac disjI2, metis)
  qed
next  
  case (4 a b)
  then show ?case
  proof(simp add: F_Sync F_Mprefix F_SKIP, elim exE disjE, simp_all, goal_cases)
    case 1
    then show ?case
      apply(rule_tac disjI1, rule_tac x="[]" in exI, simp, rule_tac x="[]" in exI, simp) 
      apply(rule_tac x="b - (ev ` B)" in exI, rule_tac conjI)
       by (blast, rule_tac x="b - {tick}" in exI, blast) 
  next
    case 2
    then show ?case 
    proof (elim conjE exE, elim disjE exE, simp_all, goal_cases)
      case (1 aa t u X)
      then show ?case      
        apply(erule_tac conjE, erule_tac exE, simp_all)
        apply(rule_tac disjI1, rule_tac x="(ev aa)#t" in exI, rule_tac x=u in exI, 
              rule_tac x=X in exI, intro conjI, simp_all)
        apply auto[1] 
        by (metis (no_types, lifting) DiffE event.distinct(1) event.inject 
            imageE insertE list.exhaust_sel SyncSingleHeadAdd)
    next
      case (2 aa t u r v)
      from 2(2) have "a \<in> \<D> (\<box> x \<in>  B - S \<rightarrow> (P x \<lbrakk> S \<rbrakk> SKIP))" 
        apply(simp add:D_Mprefix D_Sync) by (metis "2"(1) "2"(3) "2"(4))
      with 2(5) have "a \<in> \<D> (Mprefix B P \<lbrakk>S\<rbrakk> SKIP)" by simp
      with 2(2) show ?case by (simp add:D_Sync D_Mprefix)
    qed
  qed
qed

lemma Sync_Ndet_left_distrib: "((P \<sqinter> Q) \<lbrakk> S \<rbrakk> M) = ((P \<lbrakk> S \<rbrakk> M) \<sqinter> (Q \<lbrakk> S \<rbrakk> M))"
  by (auto simp: Process_eq_spec, simp_all add: D_Sync F_Sync D_Ndet F_Ndet T_Ndet) blast+

lemma Sync_Ndet_right_distrib: "(M \<lbrakk> S \<rbrakk> (P \<sqinter> Q)) = ((M \<lbrakk> S \<rbrakk> P) \<sqinter> (M \<lbrakk> S \<rbrakk> Q))"
  by (metis Sync_commute Sync_Ndet_left_distrib)

lemma prefix_Sync_SKIP1:  "a \<notin> S \<Longrightarrow> (a \<rightarrow> P \<lbrakk>S\<rbrakk> SKIP) = (a \<rightarrow> (P \<lbrakk>S\<rbrakk> SKIP))"
  by (metis (no_types, lifting) write0_def empty_Diff insert_Diff_if Mprefix_Sync_SKIP Mprefix_singl)

lemma prefix_Sync_SKIP2: "a \<in> S \<Longrightarrow> (a \<rightarrow> P \<lbrakk>S\<rbrakk> SKIP) = STOP"
  by (simp add: Mprefix_STOP Mprefix_Sync_SKIP write0_def)

lemma prefix_Sync_SKIP: "(a \<rightarrow> P \<lbrakk>S\<rbrakk> SKIP) = (if a \<in> S then STOP else (a \<rightarrow> (P \<lbrakk>S\<rbrakk> SKIP)))"
  by (auto simp add: prefix_Sync_SKIP2 prefix_Sync_SKIP1)
  
lemma prefix_Sync1: "\<lbrakk>a \<in> S; b \<in> S; a \<noteq> b\<rbrakk> \<Longrightarrow> (a \<rightarrow> P \<lbrakk>S\<rbrakk> (b \<rightarrow> Q)) = STOP"  
  using Mprefix_Sync_distr_subset[of "{a}" S "{b}" "\<lambda>x. P" "\<lambda>x. Q", simplified]
  by (auto, simp add: Mprefix_STOP Mprefix_singl)
   
lemma prefix_Sync2: "a \<in> S \<Longrightarrow> ((a \<rightarrow> P) \<lbrakk>S\<rbrakk> (a \<rightarrow> Q)) = (a \<rightarrow> (P \<lbrakk>S\<rbrakk> Q))"  
  by (simp add:write0_def Mprefix_Sync_distr_subset[of "{a}" S "{a}" "\<lambda>x. P" "\<lambda>x. Q", simplified])

lemma prefix_Sync3: "\<lbrakk>a \<in> S; b \<notin> S\<rbrakk> \<Longrightarrow> (a \<rightarrow> P \<lbrakk>S\<rbrakk> (b \<rightarrow> Q)) = (b \<rightarrow> ((a \<rightarrow> P) \<lbrakk>S\<rbrakk> Q))"
  using Mprefix_Sync_distr_right[of "{b}" S "{a}" "\<lambda>x. P" "\<lambda>x. Q", simplified]
  by (auto simp add:write0_def Sync_commute)

lemma Hiding_Sync_D1: \<open>finite A \<Longrightarrow> A \<inter> S = {} \<Longrightarrow>  \<D> ((P \<lbrakk>S\<rbrakk> Q) \ A) \<subseteq> \<D> ((P \ A) \<lbrakk>S\<rbrakk> (Q \ A))\<close>
proof (simp only:D_Sync T_Sync D_Hiding T_Hiding, intro subsetI CollectI, 
                  elim CollectE exE conjE, elim exE CollectE disjE, goal_cases)
  case (1 x t u ta ua r v)
  then show ?case (is "\<exists>t ua ra va. ?P t ua ra va")
    apply (subgoal_tac "?P (trace_hide ta (ev ` A)) (trace_hide ua (ev ` A)) 
                        (trace_hide r (ev ` A)) ((trace_hide v (ev ` A))@u)") 
     apply (metis (no_types, lifting)) 
    apply(simp_all add:front_tickFree_append Hiding_tickFree tickFree_def disjoint_iff_not_equal
                        Hiding_interleave[of "ev ` A" "insert tick (ev ` S)" r ta ua])
      apply(elim conjE, erule_tac disjE, rule_tac disjI1, rule_tac conjI, case_tac "tickFree ta") 
      apply(meson front_tickFree_charn self_append_conv tickFree_def) 
      apply (metis D_imp_front_tickFree emptyLeftNonSync ftf_Sync21 ftf_Sync32 in_set_conv_decomp_last 
                  insertI1 is_processT2_TR nonTickFree_n_frontTickFree tickFree_Nil tickFree_def)
    apply(subst disj_commute, rule_tac disjCI, simp)
    subgoal proof(goal_cases)
      case 1
      hence a:"tickFree ua" by (metis front_tickFree_implies_tickFree is_processT2_TR is_processT5_S7)
      from 1(11) 1(10) inf_hidden[of A ua Q] obtain ff where "isInfHiddenRun ff Q A \<and> ua \<in> range ff" by auto
      with 1(2,3,4,7) a show ?case
        apply(rule_tac x=ua in exI, rule_tac x="[]" in exI)
        using front_tickFree_Nil tickFree_def by blast
    qed
    apply(rule_tac disjI2, rule_tac conjI, case_tac "tickFree ta") 
      apply(meson front_tickFree_charn self_append_conv tickFree_def) 
      apply (metis D_imp_front_tickFree emptyLeftNonSync ftf_Sync21 ftf_Sync32 in_set_conv_decomp_last 
                  insertI1 is_processT2_TR nonTickFree_n_frontTickFree tickFree_Nil tickFree_def)
    apply(subst disj_commute, rule_tac disjCI, simp)
    proof(goal_cases)
      case 1
      hence a:"tickFree ua" by (metis front_tickFree_implies_tickFree is_processT2_TR is_processT5_S7)
      from 1(10) 1(11) inf_hidden[of A ua P] obtain ff where "isInfHiddenRun ff P A \<and> ua \<in> range ff" by auto
      with 1(2,3,4,7) a show ?case
        apply(rule_tac x=ua in exI, rule_tac x="[]" in exI)
        using front_tickFree_Nil tickFree_def by blast
    qed
next
  case (2 x t u f)
  then show ?case (is "\<exists>t ua ra va. ?P t ua ra va")
  proof(elim UnE exE conjE rangeE CollectE, goal_cases 21)
    case (21 xa)
    note aa = 21(7)[rule_format, of xa] 
    with 21 show ?case
    proof(elim UnE exE conjE rangeE CollectE, goal_cases 211 212)
      case (211 taa uaa)
      then show ?case (is "\<exists>t ua ra va. ?P t ua ra va")
      proof (cases "\<forall>i. f i \<in> {s. \<exists>t u. t \<in> \<T> P \<and> u \<in> \<T> Q \<and> s setinterleaves ((t, u), ev ` S \<union> {tick})}")
        case True
        define ftu where "ftu \<equiv> \<lambda>i. (SOME (t,u). t \<in> \<T> P \<and> u \<in> \<T> Q \<and> 
                                (f i) setinterleaves ((t, u), ev ` S \<union> {tick}))"
        define ft fu where "ft \<equiv> fst \<circ> ftu" and "fu \<equiv> snd \<circ> ftu"
        have "inj ftu"
        proof
          fix x y
          assume ftuxy: "ftu x = ftu y"
          obtain t u where tu:"(t, u) = ftu x" by (metis surj_pair)
          have "\<exists>t u. t \<in> \<T> P \<and> u \<in> \<T> Q \<and> f x setinterleaves ((t, u), ev ` S \<union> {tick})" 
            using True[rule_format, of x] by simp
          with tu have a:"(f x) setinterleaves ((t, u), ev ` S \<union> {tick})"
            unfolding ftu_def by (metis (mono_tags, lifting) exE_some old.prod.case tu)
          have "\<exists>t u. t \<in> \<T> P \<and> u \<in> \<T> Q \<and> f y setinterleaves ((t, u), ev ` S \<union> {tick})" 
            using True[rule_format, of y] by simp
          with ftuxy tu have b:"(f y) setinterleaves ((t, u), ev ` S \<union> {tick})"
            unfolding ftu_def by (metis (mono_tags, lifting) exE_some old.prod.case tu)
          from interleave_eq_size[OF a b] have "length (f x) = length (f y)" by assumption
          with 211(6) show "x = y"
            by (metis add.left_neutral less_length_mono linorder_neqE_nat not_add_less2 strict_mono_def)
        qed
        hence inf_ftu: "infinite (range ftu)" using finite_imageD by blast
        have "range ftu \<subseteq> range ft \<times> range fu" 
          by (clarify, metis comp_apply fst_conv ft_def fu_def rangeI snd_conv)
        with inf_ftu have inf_ft_fu: "infinite (range ft) \<or> infinite (range fu)" 
          by (meson finite_SigmaI infinite_super)
        have a:"isInfHiddenRun f (P \<lbrakk>S\<rbrakk> Q) A"
          using "2"(6) T_Sync by blast
        { fix i
          from a obtain t where "f i = f 0 @ t \<and> set t \<subseteq>  (ev ` A)"
            unfolding isInfHiddenRun_1 by blast
          hence "set (f i) \<subseteq> set (f 0) \<union> (ev ` A)" by auto
        } note b = this
        { fix x
          obtain t u where tu:"(t, u) = ftu x" by (metis surj_pair)
          have "\<exists>t u. t \<in> \<T> P \<and> u \<in> \<T> Q \<and> f x setinterleaves ((t, u), ev ` S \<union> {tick})" 
           using True[rule_format, of x] by simp
          with tu have a:"t \<in> \<T> P \<and> u \<in> \<T> Q \<and> (f x) setinterleaves ((t, u), ev ` S \<union> {tick})"
           unfolding ftu_def by (metis (mono_tags, lifting) exE_some old.prod.case tu)
          hence "ft x \<in> \<T> P \<and> fu x \<in> \<T> Q \<and> (f x) setinterleaves ((ft x, fu x), ev ` S \<union> {tick})"
            by (metis comp_apply fst_conv ft_def fu_def snd_conv tu)
          hence "ft x \<in> \<T> P \<and> fu x \<in> \<T> Q \<and> set (ft x) \<union> set (fu x) \<subseteq> set (f x) 
                  \<and> (f x) setinterleaves ((ft x, fu x), ev ` S \<union> {tick})" using interleave_set by blast
        } note ft_fu_f = this
        with b have c:"ft i \<in> \<T> P \<and> fu i \<in> \<T> Q \<and> set (ft i) \<union> set (fu i) \<subseteq> set (f 0) \<union> ev ` A" for i by blast        
        with inf_ft_fu show ?thesis
        proof(elim disjE, goal_cases 2111 2112)
          case 2111
          have "\<exists>t'\<in>range ft. t = take i t' \<longrightarrow> (set t \<subseteq> set (f 0) \<union> ev ` A \<and> length t \<le> i)" for i
            by simp (metis "211"(9) b)
          hence "{t. \<exists>t'\<in>range ft. t = take i t'} \<subseteq> {t. set t \<subseteq> set (f 0) \<union> ev ` A \<and> length t \<le> i} " for i 
            by auto (meson UnE c in_set_takeD subsetCE sup.boundedE)
          with 2(1) finite_lists_length_le[of "set (f 0) \<union> ev ` A"] have "finite {t. \<exists>t'\<in>range ft. t = take i t'}" for i
            by (meson List.finite_set finite_Un finite_imageI finite_subset)
          from KoenigLemma[of "range ft", OF 2111(2), rule_format, OF this] obtain ftf::"nat \<Rightarrow> 'a event list" where 
            d:"strict_mono ftf \<and> range ftf \<subseteq> {t. \<exists>t'\<in>range ft. t \<le> t'}" by blast
          with c d[THEN conjunct2] have e:"range ftf \<subseteq> \<T> P" using is_processT3_ST_pref by blast
          define ftfs where f:"ftfs = ftf \<circ> (\<lambda>n. n + length (f 0))"
          from e d[THEN conjunct1] strict_mono_def have f1:"range ftfs \<subseteq> \<T> P" and f2:"strict_mono ftfs"
            by (auto simp add: strict_mono_def f)
          { fix i
            have t0:"length (ftfs 0) \<ge> length (f 0)" 
              by (metis d[THEN conjunct1] add_leE comp_def f length_strict_mono)
            obtain tt where t1:"ftfs i = (ftfs 0) @ tt" 
              by (metis f2 le0 le_list_def strict_mono_less_eq)
            from d[THEN conjunct2] f obtain j where t2:"ftfs i \<le> ft j" by simp blast
            obtain tt1 where t3: "ft j = (ftfs 0) @ tt @ tt1" 
              by (metis append.assoc le_list_def t1 t2)
            with t0 interleave_order[of "f j" "ftfs 0" "tt@tt1" "ev ` S \<union> {tick}" "fu j"] ft_fu_f 
              have t4:"set tt \<subseteq> set (drop (length (f 0)) (f j))"
                by (metis Un_subset_iff set_append set_drop_subset_set_drop subset_Un_eq)
            with 21 isInfHiddenRun_1[of f _ A] have t5: "set (drop (length (f 0)) (f j)) \<subseteq> ev ` A"
              by (metis (full_types) a append_eq_conv_conj) 
            with t4 have "set tt \<subseteq> ev ` A" by simp
            with t1 have "trace_hide (ftfs i) (ev ` A) = trace_hide (ftfs 0) (ev ` A)"
              by (simp add: subset_eq)
          } note f3 = this
          from d[THEN conjunct2] f obtain i where f4:"ftfs 0 \<le> ft i" by simp blast
          show ?case 
            apply(rule_tac x="trace_hide (ft i) (ev ` A)" in exI, rule_tac x="trace_hide (fu i) (ev ` A)" in exI)
            apply(rule_tac x="trace_hide (f i) (ev ` A)" in exI, rule_tac x="u" in exI)
          proof (intro conjI, goal_cases 21111 21112 21113 21114 21115)
            case 21111
            then show ?case using 2 by (simp add: "211"(3))
          next
            case 21112
            then show ?case by (metis "211"(4) "211"(9) a Hiding_tickFree) 
          next
            case 21113
            then show ?case by (metis "211"(5) "211"(8) "211"(9)) 
          next
            case 21114
            then show ?case 
              apply(rule Hiding_interleave)
               using "211"(2) apply blast 
              using ft_fu_f by simp
          next
            case 21115
            from f4 obtain u where f5:"ft i = (ftfs 0) @ u" by (metis le_list_def)
            have "tickFree (f i)" by (metis "211"(4) "211"(8) "211"(9) Hiding_tickFree)
            with ft_fu_f have f6:"tickFree (ft i)" by (meson subsetCE sup.boundedE tickFree_def)
            show ?case
              apply (rule disjI1, rule conjI, simp)
               apply(rule_tac x="ftfs 0" in exI, rule_tac x="trace_hide u (ev ` A)" in exI, intro conjI)
              apply (metis f5 front_tickFree_Nil front_tickFree_mono ft_fu_f Hiding_fronttickFree is_processT2_TR)
              apply (metis f5 f6 tickFree_append)
                apply (simp add: f5, rule disjI2, rule_tac x=ftfs in exI)  
               using f1 f2 f3 apply blast
              using elemTIselemHT[of "fu i" Q A, simplified T_Hiding] ft_fu_f by blast
          qed 
        next
          case 2112
          have "\<exists>t'\<in>range fu. t = take i t' \<longrightarrow> (set t \<subseteq> set (f 0) \<union> ev ` A \<and> length t \<le> i)" for i
            by simp (metis "211"(9) b)
          hence "{t. \<exists>t'\<in>range fu. t = take i t'} \<subseteq> {t. set t \<subseteq> set (f 0) \<union> ev ` A \<and> length t \<le> i} " for i 
            by auto (meson UnE c in_set_takeD subsetCE sup.boundedE)
          with 2(1) finite_lists_length_le[of "set (f 0) \<union> ev ` A"] have "finite {t. \<exists>t'\<in>range fu. t = take i t'}" for i
            by (meson List.finite_set finite_Un finite_imageI finite_subset)
          from KoenigLemma[of "range fu", OF 2112(2), rule_format, OF this] obtain fuf::"nat \<Rightarrow> 'a event list" where 
            d:"strict_mono fuf \<and> range fuf \<subseteq> {t. \<exists>t'\<in>range fu. t \<le> t'}" by blast
          with c d[THEN conjunct2] have e:"range fuf \<subseteq> \<T> Q" using is_processT3_ST_pref by blast
          define fufs where f:"fufs = fuf \<circ> (\<lambda>n. n + length (f 0))"
          from e d[THEN conjunct1] strict_mono_def have f1:"range fufs \<subseteq> \<T> Q" and f2:"strict_mono fufs"
            by (auto simp add: strict_mono_def f)
          { fix i
            have t0:"length (fufs 0) \<ge> length (f 0)" 
              by (metis d[THEN conjunct1] add_leE comp_def f length_strict_mono)
            obtain tt where t1:"fufs i = (fufs 0) @ tt" 
              by (metis f2 le0 le_list_def strict_mono_less_eq)
            from d[THEN conjunct2] f obtain j where t2:"fufs i \<le> fu j" by simp blast
            obtain tt1 where t3: "fu j = (fufs 0) @ tt @ tt1" by (metis append.assoc le_list_def t1 t2)
            with t0 interleave_order[of "f j" "fufs 0" "tt@tt1" "ev ` S \<union> {tick}" "ft j"] ft_fu_f 
              have t4:"set tt \<subseteq> set (drop (length (f 0)) (f j))"
                by (metis (no_types, opaque_lifting) Sync.sym Un_subset_iff order_trans 
                                                set_append set_drop_subset_set_drop)
            with 21 isInfHiddenRun_1[of f _ A] have t5: "set (drop (length (f 0)) (f j)) \<subseteq> ev ` A"
              by (metis (full_types) a append_eq_conv_conj) 
            with t4 have "set tt \<subseteq> ev ` A" by simp
            with t1 have "trace_hide (fufs i) (ev ` A) = trace_hide (fufs 0) (ev ` A)"
              by (simp add: subset_eq)
          } note f3 = this
          from d[THEN conjunct2] f obtain i where f4:"fufs 0 \<le> fu i" by simp blast
          show ?case 
            apply(rule_tac x="trace_hide (fu i) (ev ` A)" in exI, 
                  rule_tac x="trace_hide (ft i) (ev ` A)" in exI)
            apply(rule_tac x="trace_hide (f i) (ev ` A)" in exI, rule_tac x="u" in exI)
          proof (intro conjI, goal_cases 21111 21112 21113 21114 21115)
            case 21111
            then show ?case using 2 by (simp add: "211"(3))
          next
            case 21112
            then show ?case by (metis "211"(4) "211"(9) a Hiding_tickFree) 
          next
            case 21113
            then show ?case by (metis "211"(5) "211"(8) "211"(9)) 
          next
            case 21114
            then show ?case 
              apply(rule Hiding_interleave)
               using "211"(2) apply blast 
              using ft_fu_f using Sync.sym by blast
          next
            case 21115
            from f4 obtain u where f5:"fu i = (fufs 0) @ u" by (metis le_list_def)
            have "tickFree (f i)" by (metis "211"(4) "211"(8) "211"(9) Hiding_tickFree)
            with ft_fu_f have f6:"tickFree (fu i)" by (meson subsetCE sup.boundedE tickFree_def)
            show ?case
              apply (rule disjI2, rule conjI, simp)
               apply(rule_tac x="fufs 0" in exI, rule_tac x="trace_hide u (ev ` A)" in exI, intro conjI)
              apply (metis f5 front_tickFree_Nil front_tickFree_mono ft_fu_f Hiding_fronttickFree is_processT2_TR)
              apply (metis f5 f6 tickFree_append)
                apply (simp add: f5, rule disjI2, rule_tac x=fufs in exI)  
               using f1 f2 f3 apply blast
              using elemTIselemHT[of "ft i" P A, simplified T_Hiding] ft_fu_f by blast             
          qed 
        qed
      next
        case False
        then obtain xaa 
          where "f xaa \<notin> {s. \<exists>t u. t \<in> \<T> P \<and> u \<in> \<T> Q \<and> s setinterleaves ((t, u), ev ` S \<union> {tick})}" 
            by blast
        with 211(7)[rule_format, of xaa] obtain ta ua ra va 
          where bb:"front_tickFree va \<and> (tickFree ra \<or> va = []) \<and> 
                    f xaa = ra @ va \<and> ra setinterleaves ((ta, ua), ev ` S \<union> {tick}) \<and> 
                    (ta \<in> \<D> P \<and> ua \<in> \<T> Q \<or> ta \<in> \<D> Q \<and> ua \<in> \<T> P)" by blast
        from 211 have cc:"x = trace_hide (f xaa) (ev ` A) @ u" by (metis (no_types, lifting))
        from bb 211(9) "211"(8) "21"(4) have "tickFree ra \<and> tickFree va" 
          by (metis Hiding_tickFree tickFree_append)
        with cc bb 211 show ?thesis
          apply(subgoal_tac "?P (trace_hide ta (ev ` A)) (trace_hide ua (ev ` A)) 
                             (trace_hide ra (ev ` A))  ((trace_hide va (ev ` A))@u)")
           apply (metis (no_types, lifting))
          apply(simp_all add:front_tickFree_append Hiding_tickFree tickFree_def disjoint_iff_not_equal 
                                      Hiding_interleave[of "ev ` A" "insert tick (ev ` S)" ra ta ua])
            apply(elim conjE disjE, rule_tac disjI1, rule_tac conjI, case_tac "tickFree ta") 
              apply(meson front_tickFree_charn self_append_conv tickFree_def) 
              apply (metis D_imp_front_tickFree emptyLeftNonSync ftf_Sync21 ftf_Sync32 in_set_conv_decomp_last 
                          insertI1 is_processT2_TR nonTickFree_n_frontTickFree tickFree_Nil tickFree_def)
         apply(subst disj_commute, rule_tac disjCI, simp)
          subgoal proof(goal_cases 2111)
          case 2111
          hence a:"tickFree ua" by (metis front_tickFree_implies_tickFree is_processT2_TR is_processT5_S7)
          from 2111(20) 2111(21) inf_hidden[of A ua Q] obtain ff 
            where "isInfHiddenRun ff Q A \<and> ua \<in> range ff" by auto
          with 2111(2,3,4,7) a show ?case
            apply(rule_tac x=ua in exI, rule_tac x="[]" in exI)
            using front_tickFree_Nil tickFree_def by blast
          qed
          apply(rule_tac disjI2, rule_tac conjI, case_tac "tickFree ta") 
            apply(meson front_tickFree_charn self_append_conv tickFree_def) 
            apply (metis D_imp_front_tickFree emptyLeftNonSync ftf_Sync21 ftf_Sync32 in_set_conv_decomp_last 
                        insertI1 is_processT2_TR nonTickFree_n_frontTickFree tickFree_Nil tickFree_def)
          apply(subst disj_commute, rule_tac disjCI, simp)
          proof(goal_cases 2111)
            case 2111
            hence a:"tickFree ua" by (metis front_tickFree_implies_tickFree is_processT2_TR is_processT5_S7)
            from 2111(20) 2111(21) inf_hidden[of A ua P] obtain ff 
              where "isInfHiddenRun ff P A \<and> ua \<in> range ff" by auto
            with 2111(2,3,4,7) a show ?case
              apply(rule_tac x=ua in exI, rule_tac x="[]" in exI)
              using front_tickFree_Nil tickFree_def by blast
          qed
      qed      
    next
      case (212 ta ua r v)
      then show ?case (is "\<exists>t ua ra va. ?P t ua ra va")
        apply (subgoal_tac "?P (trace_hide ta (ev ` A)) (trace_hide ua (ev ` A)) 
                               (trace_hide r (ev ` A)) ((trace_hide v (ev ` A))@u)") 
       apply (metis (no_types, lifting))
      apply(simp_all add:front_tickFree_append Hiding_tickFree tickFree_def disjoint_iff_not_equal
                         Hiding_interleave[of "ev ` A" "insert tick (ev ` S)" r ta ua])
      apply(erule_tac disjE, rule_tac disjI1, rule_tac conjI, case_tac "tickFree ta") 
        apply(meson front_tickFree_charn self_append_conv tickFree_def) 
        apply (metis D_imp_front_tickFree emptyLeftNonSync ftf_Sync21 ftf_Sync32 in_set_conv_decomp_last 
                    insertI1 is_processT2_TR nonTickFree_n_frontTickFree tickFree_Nil tickFree_def)
      apply(subst disj_commute, rule_tac disjCI, simp)
      subgoal proof(goal_cases 2121)
        case 2121
        hence a:"tickFree ua" by (metis front_tickFree_implies_tickFree is_processT2_TR is_processT5_S7)
        from 2121(14) 2121(13) inf_hidden[of A ua Q] obtain ff 
          where "isInfHiddenRun ff Q A \<and> ua \<in> range ff" by auto
        with 2121(2,3,4,7) a show ?case
          apply(rule_tac x=ua in exI, rule_tac x="[]" in exI)
          using front_tickFree_Nil tickFree_def by blast
      qed
      apply(rule_tac disjI2, rule_tac conjI, case_tac "tickFree ta") 
        apply(meson front_tickFree_charn self_append_conv tickFree_def) 
        apply (metis D_imp_front_tickFree emptyLeftNonSync ftf_Sync21 ftf_Sync32 in_set_conv_decomp_last 
                    insertI1 is_processT2_TR nonTickFree_n_frontTickFree tickFree_Nil tickFree_def)
      apply(subst disj_commute, rule_tac disjCI, simp)
      proof(goal_cases 2121)
        case 2121
        hence a:"tickFree ua" by (metis front_tickFree_implies_tickFree is_processT2_TR is_processT5_S7)
        from 2121(14) 2121(13) inf_hidden[of A ua P] obtain ff 
          where "isInfHiddenRun ff P A \<and> ua \<in> range ff" by auto
        with 2121(2,3,4,7) a show ?case
          apply(rule_tac x=ua in exI, rule_tac x="[]" in exI)
          using front_tickFree_Nil tickFree_def by blast
      qed
    qed
  qed
qed

lemma Hiding_Sync_D2: 
  assumes *:"A \<inter> S = {}"
  shows     \<open>\<D> ((P \ A) \<lbrakk>S\<rbrakk> (Q \ A)) \<subseteq> \<D> ((P \<lbrakk>S\<rbrakk> Q) \ A)\<close>
proof -
  { fix P Q   
    have "{s. \<exists>t u r v. front_tickFree v \<and> (tickFree r \<or> v = []) \<and>
           s = r @ v \<and> r setinterleaves ((t, u), insert tick (ev ` S)) \<and>
           (t \<in> \<D> (P \\ A) \<and> u \<in> \<T> (Q \\ A))} \<subseteq> \<D> ((P \<lbrakk>S\<rbrakk> Q) \\ A)"
    proof(simp add:D_Hiding D_Sync, intro subsetI CollectI, elim exE conjE CollectE, goal_cases a)
      case (a x t u r v ta1 ta2)
      from a(1,3-9) show ?case
      proof(erule_tac disjE, goal_cases)
        case 1
        with interleave_append[of r "trace_hide ta1 (ev ` A)" "ta2" "insert tick (ev ` S)" u] 
        obtain u1 u2 r1 r2
          where a1:"u = u1 @ u2" and a2:"r = r1 @ r2" and 
                a3:"r1 setinterleaves ((trace_hide ta1 (ev ` A), u1), insert tick (ev ` S))" and
                a4:"r2 setinterleaves ((ta2, u2), insert tick (ev ` S))" by blast
        with 1 show ?case
        proof(auto simp only:T_Hiding, goal_cases 11 12 13)
          case (11 ua) 
          from trace_hide_append[OF 11(12)] 
          obtain ua1 where a5:"u1 = trace_hide ua1 (ev ` A) \<and> ua1 \<le> ua \<and> ua1 \<in> \<T> Q" 
            using "11"(13) F_T is_processT3_ST_pref le_list_def by blast
          from interleave_Hiding[OF _ 11(10)[simplified a5]] obtain ra1
            where a6:"r1 = trace_hide ra1 (ev ` A) \<and> ra1 setinterleaves ((ta1, ua1), insert tick (ev ` S))"
            using * by blast
          from a(2) 11 a5 a6 show ?case
            apply(exI ra1, exI "r2@v", intro conjI, simp_all (asm_lr))
              apply (metis a(5) append_Nil2 front_tickFree_append front_tickFree_mono ftf_Sync is_processT2_TR)
             apply (metis equals0D ftf_Sync1 ftf_Sync21 insertI1 tickFree_def)
            using front_tickFree_Nil by blast
        next
          case (12 ua1 ua2)          
          then show ?case 
          proof(cases "u1 \<le> trace_hide ua1 (ev ` A)")
            case True
            then obtain uu1 where  "u1@uu1 = trace_hide ua1 (ev ` A)" using le_list_def by blast
            with trace_hide_append[OF this] obtain uaa1 
              where a5:"u1 = trace_hide uaa1 (ev ` A) \<and> uaa1 \<le> ua1 \<and> uaa1 \<in> \<T> Q"
              using "12"(15) NT_ND is_processT3_ST_pref le_list_def by blast
            from interleave_Hiding[OF _ 12(10)[simplified a5]] obtain rr1
              where a6:"r1 = trace_hide rr1 (ev ` A) \<and> 
                        rr1 setinterleaves ((ta1, uaa1), insert tick (ev ` S))"
              using * by blast
            from a(2) 12 a5 a6 show ?thesis
            apply(exI rr1, exI "r2@v", intro conjI, simp_all (asm_lr))
              apply (metis a(5) append_Nil2 front_tickFree_append front_tickFree_mono ftf_Sync is_processT2_TR)
             apply (metis equals0D ftf_Sync1 ftf_Sync21 insertI1 tickFree_def)
            using front_tickFree_Nil by blast
          next
            case False
            with 12(14) obtain uaa1 where "u1 = trace_hide ua1 (ev ` A)@uaa1"
              by (metis append_eq_append_conv2 le_list_def)
            with a3 interleave_append_sym[of r1 "trace_hide ta1 (ev ` A)" "insert tick (ev ` S)"  
                 "trace_hide ua1 (ev ` A)" uaa1]  
            obtain taa1 taa2 ra1 ra2
              where aa1:"trace_hide ta1 (ev ` A) = taa1 @ taa2" and aa2:"r1 = ra1 @ ra2" and 
                aa3:"ra1 setinterleaves ((taa1, trace_hide ua1 (ev ` A)), insert tick (ev ` S))" and
                aa4:"ra2 setinterleaves ((taa2,uaa1), insert tick (ev ` S))" by blast
            with trace_hide_append[OF aa1[symmetric]] 
            obtain taaa1 where a5:"taa1 = trace_hide taaa1 (ev ` A) \<and> taaa1 \<le> ta1 \<and> taaa1 \<in> \<T> P"
              using "12"(7) D_T is_processT3_ST_pref le_list_def by blast
            with interleave_Hiding[OF _ aa3[simplified a5]] obtain rr1
              where a6:"ra1 = trace_hide rr1 (ev ` A) \<and> rr1 setinterleaves ((taaa1, ua1), insert tick (ev ` S))"
              using * by blast
            from a(2) 12 a5 show ?thesis
              apply(exI rr1, exI "ra2@r2@v", intro conjI, simp_all (asm_lr))
                 apply (metis aa2 front_tickFree_append front_tickFree_mono ftf_Sync 
                              Hiding_tickFree self_append_conv tickFree_append)          
                apply (metis a6 ftf_Sync1 le_list_def tickFree_append tickFree_def)
               using a6 aa2 apply blast 
              using Sync.sym a6 front_tickFree_Nil by blast
          qed
        next
          case (13 ua fa xa)
          with isInfHiddenRun_1[of fa Q] have a0:"\<forall>i. \<exists>t. fa i = fa 0 @ t \<and> set t \<subseteq>  (ev ` A)" by simp
          define tlf where "tlf \<equiv> \<lambda>i. drop (length (fa 0)) (fa i)"
          have tlf_def2:"(fa x) = (fa 0) @ (tlf x)" for x by (metis a0 append_eq_conv_conj tlf_def)
          { fix x y
            assume *:"(x::nat) < y"
            hence "fa x = fa 0 @ tlf x \<and> fa y = fa 0 @ tlf y" by (metis tlf_def2)
            hence  "tlf x < tlf y"
              using strict_monoD[OF 13(16), of x y] by (simp add: A "*" le_list_def)
          } note tlf_strict_mono = this
          have tlf_range:"set (tlf i)  \<subseteq>  (ev ` A)" for i 
            by (metis a0 append_eq_conv_conj tlf_def)
          from 13 show ?case 
          proof(cases "u1 \<le> trace_hide (fa xa) (ev ` A)")
            case True
            then obtain uu1 where  "u1@uu1 = trace_hide (fa xa) (ev ` A)" using le_list_def by blast
            with trace_hide_append[OF this] 
            obtain uaa1 where a5:"u1 = trace_hide uaa1 (ev ` A) \<and> uaa1 \<le> (fa xa) \<and> uaa1 \<in> \<T> Q"
              by (metis "13"(17) is_processT3_ST le_list_def)
            from interleave_Hiding[OF _ 13(10)[simplified a5]] obtain rr1
              where a6:"r1 = trace_hide rr1 (ev ` A) \<and> rr1 setinterleaves ((ta1, uaa1), insert tick (ev ` S))"
              using * by blast
            from a(2) 13 a5 a6 show ?thesis
            apply(exI rr1, exI "r2@v", intro conjI, simp_all (asm_lr))
              apply (metis a(5) append_Nil2 front_tickFree_append front_tickFree_mono ftf_Sync is_processT2_TR)
             apply (metis equals0D ftf_Sync1 ftf_Sync21 insertI1 tickFree_def)
            using front_tickFree_Nil by blast
          next
            case False
            with 13(14) obtain uaa1 where "u1 = trace_hide (fa 0) (ev ` A)@uaa1"
              by (metis "13"(18) append_eq_append_conv2 le_list_def)
            with a3 interleave_append_sym[of r1 "trace_hide ta1 (ev ` A)" "insert tick (ev ` S)"  
                 "trace_hide (fa 0) (ev ` A)" uaa1]  
            obtain taa1 taa2 ra1 ra2
              where aa1:"trace_hide ta1 (ev ` A) = taa1 @ taa2" and aa2:"r1 = ra1 @ ra2" and 
                aa3:"ra1 setinterleaves ((taa1, trace_hide (fa 0) (ev ` A)), insert tick (ev ` S))" and
                aa4:"ra2 setinterleaves ((taa2,uaa1), insert tick (ev ` S))" by blast
            with trace_hide_append[OF aa1[symmetric]] 
            obtain taaa1 where a5:"taa1 = trace_hide taaa1 (ev ` A) \<and> taaa1 \<le> ta1 \<and> taaa1 \<in> \<T> P"
              using "13"(7) D_T is_processT3_ST_pref le_list_def by blast
            with interleave_Hiding[OF _ aa3[simplified a5]] obtain rr1
              where a6:"ra1 = trace_hide rr1 (ev ` A) \<and> 
                        rr1 setinterleaves ((taaa1, (fa 0)), insert tick (ev ` S))"
              using * by blast
            from a(2) 13 a0 a5 a6 aa1 aa2 aa3 show ?thesis
              apply(exI rr1, exI "ra2@r2@v", intro conjI, simp_all (asm_lr))
                apply (metis front_tickFree_append front_tickFree_mono ftf_Sync 
                             Hiding_tickFree self_append_conv tickFree_append)          
                apply (metis a6 ftf_Sync1 le_list_def tickFree_append tickFree_def)
             proof (rule_tac disjI2, exI "\<lambda>i. rr1@(tlf i)", intro conjI, goal_cases 131 132 133 134)
               case 131
               then show ?case 
                 apply(rule_tac strict_monoI, drule_tac tlf_strict_mono,rule_tac less_append) by assumption
             next
               case 132
               have "(rr1@tlf i) setinterleaves ((taaa1, fa i),insert tick (ev ` S))" for i
                 apply(subst tlf_def2, rule interleave_append_tail_sym[OF a6[THEN conjunct2], of "tlf i"])
                 using * tlf_range by blast
               then show ?case
                 unfolding T_Sync using a5 13(17) by auto
             next
               case 133
               from tlf_range have "trace_hide (y @ tlf i) (ev ` A) = trace_hide y (ev ` A)" for i y 
                 apply(induct y) using filter_empty_conv apply fastforce by simp
               then show ?case by simp
             next
               case 134
               have "tlf 0 = []"
                 by (simp add: tlf_def)
               then show ?case by simp
             qed  
          qed  
        qed
      next
        case 2
        from 2(8) obtain nta::nat and ff::"nat \<Rightarrow> 'a event list" 
          where "strict_mono ff" and ff:"(\<forall>i. ff i \<in> \<T> P) \<and> ta1 = ff nta \<and> 
                (\<forall>i. trace_hide (ff i) (ev ` A) = trace_hide (ff 0) (ev ` A))" by blast
        define f where "f \<equiv> (\<lambda>i. ff (i + nta))"
        with ff have f1:"strict_mono f" and f2:"(\<forall>i. f i \<in> \<T> P)" and f3:"ta1 = f 0" and 
                f4:"(\<forall>i. trace_hide (f i) (ev ` A) = trace_hide ta1 (ev ` A))"
          apply auto apply(rule strict_monoI, rule \<open>strict_mono ff\<close>[THEN strict_monoD])
          by simp metis
        with isInfHiddenRun_1[of f P] have a0:"\<forall>i. \<exists>t. f i = f 0 @ t \<and> set t \<subseteq>  (ev ` A)" by simp
        define tlf where "tlf \<equiv> \<lambda>i. drop (length (f 0)) (f i)"
        have tlf_def2:"(f x) = ta1 @ (tlf x)" for x by (metis a0 f3 append_eq_conv_conj tlf_def)
        { fix x y
          assume *:"(x::nat) < y"
          hence "f x = f 0 @ tlf x \<and> f y = f 0 @ tlf y" by (metis f3 tlf_def2)
          hence  "tlf x < tlf y"
            using strict_monoD[OF f1, of x y] by (simp add: A "*" le_list_def)
        } note tlf_strict_mono = this
        have tlf_range:"set (tlf i)  \<subseteq>  (ev ` A)" for i 
          by (metis a0 append_eq_conv_conj tlf_def)
        with 2 interleave_append[of r "trace_hide ta1 (ev ` A)" "ta2" "insert tick (ev ` S)" u] 
        obtain u1 u2 r1 r2
          where a1:"u = u1 @ u2" and a2:"r = r1 @ r2" and 
                a3:"r1 setinterleaves ((trace_hide ta1 (ev ` A), u1), insert tick (ev ` S))" and
                a4:"r2 setinterleaves ((ta2, u2), insert tick (ev ` S))" by blast
        with 2(1-6) f1 f2 f3 f4 show ?case
        proof(auto simp only:T_Hiding, goal_cases 21 22 23)
          case (21 ua) 
          from trace_hide_append[OF 21(14)] obtain ua1 
            where a5:"u1 = trace_hide ua1 (ev ` A) \<and> ua1 \<le> ua \<and> ua1 \<in> \<T> Q" 
            using "21"(15) F_T is_processT3_ST_pref le_list_def by blast
          from interleave_Hiding[OF _ a3[simplified a5]] obtain ra1
            where a6:"r1 = trace_hide ra1 (ev ` A) \<and> ra1 setinterleaves ((ta1, ua1), insert tick (ev ` S))"
            using * by blast
          from a(2) 21 a5 a6 show ?case 
            apply(exI ra1, exI "r2@v", intro conjI, simp_all (asm_lr))
              apply (metis a(5) append_Nil2 front_tickFree_append front_tickFree_mono ftf_Sync is_processT2_TR)
             apply (metis equals0D ftf_Sync1 ftf_Sync21 insertI1 tickFree_def) 
             proof (rule_tac disjI2, exI "\<lambda>i. ra1@(tlf i)", intro conjI, goal_cases 211 212 213 214)
               case 211
               then show ?case 
                 by(rule_tac strict_monoI, drule_tac tlf_strict_mono, rule_tac less_append)(assumption)
             next
               case 212
               have "(ra1@tlf i) setinterleaves ((f i, ua1),insert tick (ev ` S))" for i
                 apply(subst tlf_def2, rule interleave_append_tail[OF a6[THEN conjunct2], of "tlf i"])
                 using * tlf_range by blast
               then show ?case
                 unfolding T_Sync using a5 21(15) f2 by auto
             next
               case 213
               from tlf_range have "trace_hide (y @ tlf i) (ev ` A) = trace_hide y (ev ` A)" for i y 
                 apply(induct y) using filter_empty_conv apply fastforce by simp
               then show ?case by simp
             next
               case 214
               have "tlf 0 = []"
                 by (simp add: tlf_def)
               then show ?case by simp
             qed              
        next
          case (22 ua1 ua2)
          then show ?case
          proof(cases "u1 \<le> trace_hide ua1 (ev ` A)")
            case True
            then obtain uu1 where  "u1@uu1 = trace_hide ua1 (ev ` A)" using le_list_def by blast
            from trace_hide_append[OF this] 
            obtain uaa1 where a5:"u1 = trace_hide uaa1 (ev ` A) \<and> uaa1 \<le> ua1 \<and> uaa1 \<in> \<T> Q" 
              using "22"(17) D_T is_processT3_ST le_list_def by blast
            from interleave_Hiding[OF _ a3[simplified a5]] 
            obtain ra1
              where a6:"r1 = trace_hide ra1 (ev ` A) \<and> ra1 setinterleaves ((ta1, uaa1), insert tick (ev ` S))"
              using * by blast
            from a(2) 22 a5 a6 show ?thesis
              apply(exI ra1, exI "r2@v", intro conjI, simp_all (asm_lr))
                apply (metis a(5) append_Nil2 front_tickFree_append front_tickFree_mono ftf_Sync is_processT2_TR)
               apply (metis equals0D ftf_Sync1 ftf_Sync21 insertI1 tickFree_def)
             proof (rule_tac disjI2, exI "\<lambda>i. ra1@(tlf i)", intro conjI, goal_cases 211 212 213 214)
               case 211
               then show ?case apply(rule_tac strict_monoI, drule_tac tlf_strict_mono, rule_tac less_append) by assumption
             next
               case 212
               have "(ra1@tlf i) setinterleaves ((f i, uaa1),insert tick (ev ` S))" for i
                 apply(subst tlf_def2, rule interleave_append_tail[OF a6[THEN conjunct2], of "tlf i"])
                 using * tlf_range by blast
               then show ?case
                 unfolding T_Sync using a5 22(15) f2 by auto
             next
               case 213
               from tlf_range have "trace_hide (y @ tlf i) (ev ` A) = trace_hide y (ev ` A)" for i y 
                 apply(induct y) using filter_empty_conv apply fastforce by simp
               then show ?case by simp
             next
               case 214
               have "tlf 0 = []"
                 by (simp add: tlf_def)
               then show ?case by simp
             qed  
          next
            case False
            with 22(16) obtain uaa1 where "u1 = trace_hide ua1 (ev ` A)@uaa1"
              by (metis append_eq_append_conv2 le_list_def)
            with a3 interleave_append_sym[of r1 "trace_hide ta1 (ev ` A)" "insert tick (ev ` S)"  "
                 trace_hide ua1 (ev ` A)" uaa1]  
            obtain taa1 taa2 ra1 ra2
              where aa1:"trace_hide ta1 (ev ` A) = taa1 @ taa2" and aa2:"r1 = ra1 @ ra2" and 
                aa3:"ra1 setinterleaves ((taa1, trace_hide ua1 (ev ` A)), insert tick (ev ` S))" and
                aa4:"ra2 setinterleaves ((taa2,uaa1), insert tick (ev ` S))" by blast
            with trace_hide_append[OF aa1[symmetric]] 
            obtain taaa1 where a5:"taa1 = trace_hide taaa1 (ev ` A) \<and> taaa1 \<le> ta1 \<and> taaa1 \<in> \<T> P"
              using f2 f3 is_processT3_ST_pref le_list_def by metis
            with interleave_Hiding[OF _ aa3[simplified a5]] obtain rr1
              where a6:"ra1 = trace_hide rr1 (ev ` A) \<and> 
                        rr1 setinterleaves ((taaa1, ua1), insert tick (ev ` S))"
              using * by blast
            from a(2) 22 a5 show ?thesis
              apply(exI rr1, exI "ra2@r2@v", intro conjI, simp_all (asm_lr))
                 apply (metis a(5) a(8) aa2 front_tickFree_append front_tickFree_mono ftf_Sync Hiding_tickFree 
                              is_processT2_TR self_append_conv tickFree_append)                
                apply (metis a6 ftf_Sync1 le_list_def tickFree_append tickFree_def)
               using a6 aa2 apply blast 
              using Sync.sym a6[THEN conjunct2] front_tickFree_Nil by (metis append_Nil2)
          qed
        next
          case (23 ua fa xa)
          with isInfHiddenRun_1[of fa Q] have a0:"\<forall>i. \<exists>t. fa i = fa 0 @ t \<and> set t \<subseteq>  (ev ` A)" by simp
          define tlfa where "tlfa \<equiv> \<lambda>i. drop (length (fa 0)) (fa i)"
          have tlfa_def2:"(fa x) = (fa 0) @ (tlfa x)" for x by (metis a0 append_eq_conv_conj tlfa_def)
          { fix x y
            assume *:"(x::nat) < y"
            hence "fa x = fa 0 @ tlfa x \<and> fa y = fa 0 @ tlfa y" by (metis tlfa_def2)
            hence  "tlfa x < tlfa y"
              using strict_monoD[OF 23(18), of x y] by (simp add: A "*" le_list_def)
          } note tlfa_strict_mono = this
          have tlfa_range:"set (tlfa i)  \<subseteq>  (ev ` A)" for i 
            by (metis a0 append_eq_conv_conj tlfa_def)
          from 23 show ?case 
          proof(cases "u1 \<le> trace_hide (fa xa) (ev ` A)")
            case True
            then obtain uu1 where  "u1@uu1 = trace_hide (fa xa) (ev ` A)" using le_list_def by blast
            with trace_hide_append[OF this] 
            obtain uaa1 where a5:"u1 = trace_hide uaa1 (ev ` A) \<and> uaa1 \<le> (fa xa) \<and> uaa1 \<in> \<T> Q"
              by (metis "23"(19) is_processT3_ST le_list_def)
            from interleave_Hiding[OF _ a3[simplified a5]] 
            obtain rr1
              where a6:"r1 = trace_hide rr1 (ev ` A) \<and> rr1 setinterleaves ((ta1, uaa1), insert tick (ev ` S))"
              using * by blast
            from a(2) 23 a5 a6 show ?thesis
            apply(exI rr1, exI "r2@v", intro conjI, simp_all (asm_lr))
              apply (metis a(5) append_Nil2 front_tickFree_append front_tickFree_mono ftf_Sync is_processT2_TR)
             apply (metis equals0D ftf_Sync1 ftf_Sync21 insertI1 tickFree_def)
            proof (rule_tac disjI2, exI "\<lambda>i. rr1@(tlf i)", intro conjI, goal_cases 211 212 213 214)
               case 211
               then show ?case apply(rule_tac strict_monoI, drule_tac tlf_strict_mono, rule_tac less_append) by assumption
             next
               case 212
               have "(rr1@tlf i) setinterleaves ((f i, uaa1),insert tick (ev ` S))" for i
                 apply(subst tlf_def2, rule interleave_append_tail[OF a6[THEN conjunct2], of "tlf i"])
                 using * tlf_range by blast
               then show ?case
                 unfolding T_Sync using a5 23(17) f2 by auto
             next
               case 213
               from tlf_range have "trace_hide (y @ tlf i) (ev ` A) = trace_hide y (ev ` A)" for i y 
                 apply(induct y) using filter_empty_conv apply fastforce by simp
               then show ?case by simp
             next
               case 214
               have "tlf 0 = []"
                 by (simp add: tlf_def)
               then show ?case by simp
             qed  
          next
            case False
            with 23(16) obtain uaa1 where "u1 = trace_hide (fa 0) (ev ` A)@uaa1"
              by (metis "23"(20) append_eq_append_conv2 le_list_def)
            with a3 interleave_append_sym[of r1 "trace_hide ta1 (ev ` A)" "insert tick (ev ` S)"  "trace_hide (fa 0) (ev ` A)" uaa1]  
            obtain taa1 taa2 ra1 ra2
              where aa1:"trace_hide ta1 (ev ` A) = taa1 @ taa2" and aa2:"r1 = ra1 @ ra2" and 
                aa3:"ra1 setinterleaves ((taa1, trace_hide (fa 0) (ev ` A)), insert tick (ev ` S))" and
                aa4:"ra2 setinterleaves ((taa2,uaa1), insert tick (ev ` S))" by blast
            with trace_hide_append[OF aa1[symmetric]] 
            obtain taaa1 where a5:"taa1 = trace_hide taaa1 (ev ` A) \<and> taaa1 \<le> ta1 \<and> taaa1 \<in> \<T> P"
              by (metis f2 f3 is_processT3_ST le_list_def)
            with interleave_Hiding[OF _ aa3[simplified a5]] obtain rr1
              where a6:"ra1 = trace_hide rr1 (ev ` A) \<and> 
                        rr1 setinterleaves ((taaa1, (fa 0)), insert tick (ev ` S))"
              using * by blast
            from a(2) 23 a0 a5 a6 aa1 aa2 aa3 show ?thesis
              apply(exI rr1, exI "ra2@r2@v", intro conjI, simp_all (asm_lr))
                apply (metis a(5) a(8) front_tickFree_append front_tickFree_mono ftf_Sync 
                                       Hiding_tickFree is_processT2_TR self_append_conv)
                apply (metis a6 ftf_Sync1 le_list_def tickFree_append tickFree_def)
             proof (rule_tac disjI2, exI "\<lambda>i. rr1@(tlfa i)", intro conjI, goal_cases 131 132 133 134)
               case 131
               then show ?case 
                 by(rule_tac strict_monoI, drule_tac tlfa_strict_mono, rule_tac less_append) assumption
             next
               case 132
               have "(rr1@tlfa i) setinterleaves ((taaa1, fa i),insert tick (ev ` S))" for i
                 apply(subst tlfa_def2, rule interleave_append_tail_sym[OF a6[THEN conjunct2], of "tlfa i"])
                 using * tlfa_range by blast
               then show ?case
                 unfolding T_Sync using a5 23(19) by auto
             next
               case 133
               from tlfa_range have "trace_hide (y @ tlfa i) (ev ` A) = trace_hide y (ev ` A)" for i y 
                 apply(induct y) using filter_empty_conv apply fastforce by simp
               then show ?case by simp
             next
               case 134
               have "tlfa 0 = []"
                 by (simp add: tlfa_def)
               then show ?case by simp
             qed  
          qed  
        qed
      qed
    qed
  }
  from this[of P Q] this[of Q P] Sync_commute[of P S Q] show ?thesis
    by (simp add:D_Sync T_Sync) blast
qed

lemma Hiding_Sync: 
  \<open>finite A \<Longrightarrow> A \<inter> S = {} \<Longrightarrow> ((P \<lbrakk>S\<rbrakk> Q) \ A) = ((P \ A) \<lbrakk>S\<rbrakk> (Q \ A))\<close>
proof(auto simp add: Process_eq_spec_optimized subset_antisym[OF Hiding_Sync_D1 Hiding_Sync_D2], 
      simp_all add: F_Sync F_Hiding,
      goal_cases)
  case (1 a b)
  then show ?case 
  proof(elim disjE, goal_cases 11 12)
    case 11
    then show ?case
    proof(elim exE conjE, elim disjE, goal_cases 111 112)
      case (111 c)
      from 111(7) obtain t u X Y where
        a: "(t, X) \<in> \<F> P" and
        b: "(u, Y) \<in> \<F> Q" and 
        c: "c setinterleaves ((t, u), insert tick (ev ` S))" and
        d: "b  \<union> ev ` A = (X \<union> Y) \<inter> insert tick (ev ` S) \<union> X \<inter> Y" by auto
      from 1(2) d have e:"ev ` A \<subseteq> X \<inter> Y" by blast 
      from a b c d e 111(2,3) show ?case
        apply(rule_tac disjI1)
        apply(rule_tac x="trace_hide t (ev ` A)" in exI, rule_tac x="trace_hide u (ev ` A)" in exI)
        apply(rule_tac x="X - ((ev ` A) - b)" in exI, intro conjI disjI1, rule_tac x="t" in exI)
         apply (metis Int_subset_iff Un_Diff_Int Un_least is_processT4 sup_ge1)
        apply(rule_tac x="Y - ((ev ` A) - b)" in exI, intro conjI disjI1, rule_tac x="u" in exI)
         apply (metis Int_subset_iff Un_Diff_Int Un_least is_processT4 sup_ge1)
        using Hiding_interleave[of "ev ` A" "insert tick (ev ` S)" c t u] by blast+
    next
      case (112 t)
      from 112(7) have a:"front_tickFree t" 
        by (metis (mono_tags, opaque_lifting) D_imp_front_tickFree append_Nil2 
                  front_tickFree_append ftf_Sync is_processT2_TR)
      from 112 have "t \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)" by (simp add:D_Sync)
      with 112(1,2,3) have "a \<in> \<D> ((P \<lbrakk>S\<rbrakk> Q) \\ A)" 
        apply (simp add:D_Hiding)
        proof(case_tac "tickFree t", goal_cases 1121 1122)
          case 1121
          then show ?case 
            by (rule_tac x=t in exI, rule_tac x="[]" in exI, simp)
        next
          case 1122
          with a obtain t' where "t = t'@[tick]" using nonTickFree_n_frontTickFree by blast
          with a show ?case 
            apply (rule_tac x="t'" in exI, rule_tac x="[tick]" in exI, auto)
             using front_tickFree_mono apply blast
            using 1122(4) is_processT9 by blast
        qed
      then show ?case
        apply(rule_tac disjI2)
        using Hiding_Sync_D1[of A S P Q, OF 112(1,2)] D_Sync[of "P \\ A" S "Q \\ A"] by auto
    qed
  next
    case 12
    hence "a \<in> \<D> ((P \<lbrakk>S\<rbrakk> Q) \\ A)" by (simp add:D_Hiding)
    then show ?case
      apply(rule_tac disjI2)
      using Hiding_Sync_D1[of A S P Q, OF 12(1,2)] D_Sync[of "P \\ A" S "Q \\ A"] by auto
  qed 
next
  case (2 a b)
  then show ?case
  proof(elim disjE, goal_cases 21 22)
    case 21
    then show ?case
    proof(elim exE conjE, elim disjE, goal_cases 211 212 213 214)
      case (211 t u X Y)
      then obtain ta ua where t211: "t = trace_hide ta (ev ` A) \<and> (ta, X \<union> ev ` A) \<in> \<F> P" and 
                              u211: "u = trace_hide ua (ev ` A) \<and> (ua, Y \<union> ev ` A) \<in> \<F> Q" by blast
      from interleave_Hiding[of "(ev ` A)" "insert tick (ev ` S)" a ta ua] "211"(1,2,3) t211 u211 
      obtain aa  where a211: "a = trace_hide aa  (ev ` A) \<and> 
                              aa setinterleaves ((ta, ua), insert tick (ev ` S))" by blast
      with 211(1,2,3,4) t211 u211 show ?case
        apply(rule_tac disjI1, rule_tac x="aa" in exI, simp)
        apply(rule_tac disjI1, rule_tac x="ta" in exI, rule_tac x="ua" in exI)
        apply(rule_tac x="X \<union> ev ` A" in exI, rule conjI) using is_processT4 apply blast
        apply(rule_tac x="Y \<union> ev ` A" in exI, rule conjI) using is_processT4 by blast+
    next
      case (212 t u X Y)
      hence "u \<in> \<D> (Q \\ A)" and "t \<in> \<T> (P \\ A)"  
         apply (simp add:D_Hiding)
        using "212"(8) F_T elemTIselemHT by blast
      with 212(3,8) have "a \<in> \<D> (((P \\ A) \<lbrakk>S\<rbrakk> (Q \\ A)))" 
        apply (simp add:D_Sync)
        using Sync.sym front_tickFree_charn by blast
      then show ?case
        apply (rule_tac disjI2)
        using Hiding_Sync_D2[of A S P Q, OF 2(2)] D_Hiding[of "(P \<lbrakk>S\<rbrakk> Q)", simplified] by auto
    next
      case (213 t u X Y)
      hence "u \<in> \<T> (Q \\ A)" and "t \<in> \<D> (P \\ A)"  
        by (simp_all add:D_Hiding, metis F_T elemTIselemHT)
      with 213(3,8) have "a \<in> \<D> (((P \\ A) \<lbrakk>S\<rbrakk> (Q \\ A)))"
        apply (simp add:D_Sync)
        using Sync.sym front_tickFree_charn by blast
      then show ?case
        apply (rule_tac disjI2)
        using Hiding_Sync_D2[of A S P Q, OF 2(2)] D_Hiding[of "(P \<lbrakk>S\<rbrakk> Q)", simplified] by auto
    next
      case (214 t u X Y)
      hence "u \<in> \<T> (Q \\ A)" and "t \<in> \<D> (P \\ A)"
        by (simp_all add:D_Hiding T_Hiding)
      with 214(3,8) have "a \<in> \<D> (((P \\ A) \<lbrakk>S\<rbrakk> (Q \\ A)))"
        apply (simp add:D_Sync)
        using Sync.sym front_tickFree_charn by blast
      then show ?case
        apply (rule_tac disjI2)
        using Hiding_Sync_D2[of A S P Q, OF 2(2)] D_Hiding[of "(P \<lbrakk>S\<rbrakk> Q)", simplified] by auto
    qed
  next
    case 22
    hence \<open>a \<in> \<D> (((P \ A) \<lbrakk>S\<rbrakk> (Q \ A)))\<close> by (simp add:D_Sync)
    then show ?case
      apply (rule_tac disjI2)
      using Hiding_Sync_D2[of A S P Q, OF 2(2)] D_Hiding[of "(P \<lbrakk>S\<rbrakk> Q)", simplified] by auto
  qed 
qed

lemma Sync_assoc_oneside_D: "\<D> (P \<lbrakk>S\<rbrakk> (Q \<lbrakk>S\<rbrakk> T)) \<subseteq> \<D> (P \<lbrakk>S\<rbrakk> Q \<lbrakk>S\<rbrakk> T)"
proof(auto simp add:D_Sync T_Sync del:disjE, goal_cases a)
  case (a tt uu rr vv)
  from a(3,4) show ?case
  proof(auto, goal_cases)
    case (1 t u)
    with interleave_assoc_2[OF 1(5) 1(1)] obtain tu 
      where *:"tu setinterleaves ((tt, t), insert tick (ev ` S))" 
        and **:"rr setinterleaves ((tu, u), insert tick (ev ` S))"
      by blast
    with a(1,2) 1 show ?case by (metis append.right_neutral front_tickFree_charn) 
  next
    case (2 t u u1 u2)
    with interleave_append_sym [OF 2(1)] obtain t1 t2 r1 r2
      where a1:"tt = t1 @ t2" and a2:"rr = r1 @ r2" 
        and a3:"r1 setinterleaves ((t1, u1), insert tick (ev ` S))" 
        and a4:"r2 setinterleaves ((t2, u2), insert tick (ev ` S))" by blast
    with interleave_assoc_2[OF 2(5) a3] obtain tu 
      where *:"tu setinterleaves ((t1, t), insert tick (ev ` S))" 
       and **:"r1 setinterleaves ((tu, u), insert tick (ev ` S))"
      by blast
    with a1 a2 a3 a(1,2) 2 show ?case 
      apply(exI tu, exI u, exI r1, exI "r2@vv", intro conjI, simp_all) 
        apply (metis D_imp_front_tickFree append_Nil2 front_tickFree_append front_tickFree_mono ftf_Sync)
       using D_imp_front_tickFree front_tickFree_append front_tickFree_mono ftf_Sync apply blast
      by (metis NT_ND Sync.sym append_Nil2 front_tickFree_Nil is_processT3_ST)
  next
    case (3 v u u1 u2)
    with interleave_append_sym [OF 3(1)] obtain t1 t2 r1 r2
      where a1:"tt = t1 @ t2" and a2:"rr = r1 @ r2" 
       and  a3:"r1 setinterleaves ((t1, u1), insert tick (ev ` S))" 
       and  a4:"r2 setinterleaves ((t2, u2), insert tick (ev ` S))" by blast
    with interleave_assoc_2[OF _ a3, of u v] obtain tu 
      where *:"tu setinterleaves ((t1, u), insert tick (ev ` S))" 
       and **:"r1 setinterleaves ((tu, v), insert tick (ev ` S))"
      using Sync.sym 3(5) by blast
    with a1 a2 a3 a(1,2) 3 show ?case 
      apply(exI v, exI tu, exI r1, exI "r2@vv", intro conjI, simp_all) 
        apply (metis D_imp_front_tickFree append_Nil2 front_tickFree_append front_tickFree_mono ftf_Sync)
      using D_imp_front_tickFree front_tickFree_append front_tickFree_mono ftf_Sync apply blast
      using Sync.sym apply blast by (meson D_T is_processT3_ST)
  next
    case (4 t u)
    with interleave_assoc_2[OF 4(3) 4(1)] obtain tu 
      where *:"tu setinterleaves ((tt, t), insert tick (ev ` S))" 
       and **:"rr setinterleaves ((tu, u), insert tick (ev ` S))"
      by blast
    with a(1,2) 4 show ?case 
      apply(exI tu, exI u, exI rr, exI vv, simp) using NT_ND front_tickFree_Nil by blast
  next
    case (5 t u)
    with interleave_assoc_2[OF _ 5(1), of u t] obtain tu 
      where *:"tu setinterleaves ((tt, u), insert tick (ev ` S))" 
       and **:"rr setinterleaves ((tu, t), insert tick (ev ` S))"
      using Sync.sym by blast
    with a(1,2) 5 show ?case 
      apply(exI tu, exI t, exI rr, exI vv, simp) using NT_ND front_tickFree_Nil by blast
  next
    case (6 t u u1 u2)
    with interleave_append [OF 6(1)] obtain t1 t2 r1 r2
      where a1:"uu = t1 @ t2" and a2:"rr = r1 @ r2" 
        and a3:"r1 setinterleaves ((t1, u1), insert tick (ev ` S))" 
        and a4:"r2 setinterleaves ((t2, u2), insert tick (ev ` S))" using Sync.sym by blast
    with interleave_assoc_2[OF 6(5) a3] obtain tu 
      where *:"tu setinterleaves ((t1, t), insert tick (ev ` S))" 
       and **:"r1 setinterleaves ((tu, u), insert tick (ev ` S))"
      by blast
    with a1 a2 a3 a(1,2) 6 show ?case 
      apply(exI tu, exI u, exI r1, exI "r2@vv", intro conjI, simp_all) 
        apply (metis append_Nil2 front_tickFree_append front_tickFree_mono ftf_Sync is_processT2_TR) 
       apply (meson front_tickFree_append front_tickFree_mono ftf_Sync is_processT2_TR) 
      by (metis Sync.sym append_Nil2 front_tickFree_Nil is_processT3_ST)
  next
    case (7 v u t1 t2)
    with interleave_append [OF 7(1)] obtain u1 u2 r1 r2
      where a1:"uu = u1 @ u2" and a2:"rr = r1 @ r2" 
       and  a3:"r1 setinterleaves ((t1, u1), insert tick (ev ` S))" 
       and  a4:"r2 setinterleaves ((t2, u2), insert tick (ev ` S))" by blast
    with interleave_assoc_2[of t1 u _ v r1 u1] obtain tu 
      where *:"tu setinterleaves ((u1, u), insert tick (ev ` S))" 
       and **:"r1 setinterleaves ((tu, v), insert tick (ev ` S))"
      using 7(5) Sync.sym by blast
    with a1 a2 a3 a(1,2) 7 show ?case 
      apply(exI v, exI tu, exI r1, exI "r2@vv", intro conjI, simp_all) 
        apply (metis append_Nil2 front_tickFree_append front_tickFree_mono ftf_Sync is_processT2_TR) 
       apply (meson front_tickFree_append front_tickFree_mono ftf_Sync is_processT2_TR) 
      using Sync.sym apply blast by (meson D_T is_processT3_ST)
  next
    case (8 t u)
    with interleave_assoc_2[OF 8(3), of rr uu] obtain tu 
      where *:"tu setinterleaves ((uu, t), insert tick (ev ` S))" 
       and **:"rr setinterleaves ((tu, u), insert tick (ev ` S))"
      using Sync.sym by blast
    with a(1,2) 8 show ?case 
      apply(exI tu, exI u, exI rr, exI vv, simp) using Sync.sym front_tickFree_Nil by blast
  next
    case (9 t u)
    with interleave_assoc_1[OF 9(3), of rr uu] obtain uv 
      where *:"uv setinterleaves ((u, uu), insert tick (ev ` S))" 
       and **:"rr setinterleaves ((t, uv), insert tick (ev ` S))"
      by blast
    with a(1,2) 9 show ?case 
      apply(exI t, exI uv, exI rr, exI vv, simp) using Sync.sym front_tickFree_Nil by blast
  qed
qed

lemma Sync_assoc_oneside: "((P \<lbrakk>S\<rbrakk> Q) \<lbrakk>S\<rbrakk> T) \<le> (P \<lbrakk>S\<rbrakk> (Q \<lbrakk>S\<rbrakk> T))"
proof(unfold le_ref_def, rule conjI, goal_cases D F)
  case D
  then show ?case using Sync_assoc_oneside_D by assumption
next
  case F
  then show ?case
  unfolding F_Sync proof(rule Un_least, goal_cases FF DD)
    case (FF)
    then show ?case
    proof(rule subsetI, simp add:D_Sync T_Sync split_paired_all, elim exE conjE disjE, goal_cases)
      case (1 r Xtuv t uv Xt Xuv u v Xu Xv)
      with interleave_assoc_2[OF 1(6), OF 1(2)] obtain tu
        where *:"tu setinterleaves ((t, u), insert tick (ev ` S))" 
        and **:"r setinterleaves ((tu, v), insert tick (ev ` S))" by blast
      with 1(1,3,4,5,7) show ?case 
        apply(rule_tac disjI1, exI tu, exI v, exI "(Xt \<union> Xu) \<inter> insert tick (ev ` S) \<union> Xt \<inter> Xu", 
              intro conjI disjI1, simp_all) 
        by blast+
    next
      case (2 r Xtuv t uv Xt Xuv u v uv1 uv2)
      with interleave_append_sym [of r t _ uv1 uv2] obtain t1 t2 r1 r2
        where a1:"t = t1 @ t2" and a2:"r = r1 @ r2" 
          and a3:"r1 setinterleaves ((t1, uv1), insert tick (ev ` S))" 
          and a4:"r2 setinterleaves ((t2, uv2), insert tick (ev ` S))" by metis
      with interleave_assoc_2[OF 2(6), OF a3] obtain tu
        where *:"tu setinterleaves ((t1, u), insert tick (ev ` S))" 
         and **:"r1 setinterleaves ((tu, v), insert tick (ev ` S))" by blast
      from 2(1) a1 obtain Xt1 where ***:"(t1, Xt1) \<in> \<F> P" using is_processT3_SR by blast
      from 2 a1 a2 a3 a4 * ** *** show ?case
        apply(rule_tac disjI2, exI tu, exI v, exI r1, exI r2, intro conjI disjI1, simp_all) 
          apply (metis front_tickFree_charn front_tickFree_mono ftf_Sync is_processT2) 
         apply (metis equals0D ftf_Sync1 ftf_Sync21 insertI1 tickFree_def)
        using F_T Sync.sym front_tickFree_Nil by blast
    next
      case (3 r Xtuv t uv Xt Xuv v u uv1 uv2)
      with interleave_append_sym [of r t _ uv1 uv2] obtain t1 t2 r1 r2
        where a1:"t = t1 @ t2" and a2:"r = r1 @ r2" 
         and  a3:"r1 setinterleaves ((t1, uv1), insert tick (ev ` S))" 
         and  a4:"r2 setinterleaves ((t2, uv2), insert tick (ev ` S))" by metis
      with interleave_assoc_2[OF _ a3, of u v] obtain tu
        where *:"tu setinterleaves ((t1, u), insert tick (ev ` S))" 
         and **:"r1 setinterleaves ((tu, v), insert tick (ev ` S))" using "3"(6) Sync.sym by blast
      from 3(1) a1 obtain Xt1 
        where ***:"(t1, Xt1) \<in> \<F> P" using is_processT3_SR by blast
      from 3 a1 a2 a3 a4 * ** *** show ?case
        apply(rule_tac disjI2, exI v, exI tu, exI r1, exI r2, intro conjI, simp_all) 
          apply (metis front_tickFree_charn front_tickFree_mono ftf_Sync is_processT2) 
         apply (metis equals0D ftf_Sync1 ftf_Sync21 insertI1 tickFree_def)
        using Sync.sym F_T by blast+ 
    next
      case (4 r Xtuv t uv Xt Xuv u v uv1 uv2)
      with interleave_assoc_2[OF 4(6), of r t] obtain tu
        where *:"tu setinterleaves ((t, u), insert tick (ev ` S))" 
         and **:"r setinterleaves ((tu, v), insert tick (ev ` S))" by auto
      from 4 * **  show ?case
        apply(rule_tac disjI2, exI tu, exI v, exI r, exI "[]", intro conjI, simp_all) 
        by (metis "4"(4) F_T Sync.sym append.right_neutral)
    next
      case (5 r Xtuv t uv Xt Xuv v u uv1 uv2)
      from 5(2,7,5,6)  interleave_assoc_2[of uv u _ v r t] obtain tu
        where *:"tu setinterleaves ((t, u), insert tick (ev ` S))" 
         and **:"r setinterleaves ((tu, v), insert tick (ev ` S))" by (metis Sync.sym append_Nil2)
      from 5 * **  show ?case
        apply(rule_tac disjI2, exI v, exI tu, exI r, exI "[]", intro conjI, simp_all)
        using Sync.sym F_T by blast+
    qed
  next
    case (DD)
    then show ?case
      using Sync_assoc_oneside_D[of P S Q T] by (simp add:D_Sync Collect_mono_iff sup.coboundedI2) 
  qed
qed

lemma Sync_assoc: "((P \<lbrakk>S\<rbrakk> Q) \<lbrakk>S\<rbrakk> T) = (P \<lbrakk>S\<rbrakk> (Q \<lbrakk>S\<rbrakk> T))"
  by (metis antisym_conv Sync_assoc_oneside Sync_commute)

subsection\<open> Derivative Operators laws  \<close>

(* Trivial results have been removed *)
lemmas Par_BOT = Sync_BOT[where S = \<open>UNIV\<close>]
   and Par_SKIP_SKIP = Sync_SKIP_SKIP[where S = \<open>UNIV\<close>]
   and Par_SKIP_STOP = Sync_SKIP_STOP[where S = \<open>UNIV\<close>]
   and Par_commute = Sync_commute[where S = \<open>UNIV\<close>]
   and Par_assoc = Sync_assoc[where S = \<open>UNIV\<close>]
   and Par_Ndet_right_distrib = Sync_Ndet_right_distrib[where S = \<open>UNIV\<close>]
   and Par_Ndet_left_distrib = Sync_Ndet_left_distrib[where S = \<open>UNIV\<close>]
   and Mprefix_Par_SKIP = Mprefix_Sync_SKIP[where S = \<open>UNIV\<close>]
   and prefix_Par_SKIP = prefix_Sync_SKIP[where S = \<open>UNIV\<close>, simplified]
   and mono_Par_FD = mono_Sync_FD[where S = \<open>UNIV\<close>]
   and mono_Par_ref = mono_Sync_ref[where S = \<open>UNIV\<close>]
   and prefix_Par1 = prefix_Sync1[where S = \<open>UNIV\<close>, simplified]
   and prefix_Par2 = prefix_Sync2[where S = \<open>UNIV\<close>, simplified]
   and Mprefix_Par_distr = Mprefix_Sync_distr_subset[where S = \<open>UNIV\<close>, simplified]

   and Inter_BOT = Sync_BOT[where S = \<open>{}\<close>]
   and Inter_SKIP_SKIP = Sync_SKIP_SKIP[where S = \<open>{}\<close>]
   and Inter_SKIP_STOP = Sync_SKIP_STOP[where S = \<open>{}\<close>]
   and Inter_commute = Sync_commute[where S = \<open>{}\<close>]
   and Inter_assoc = Sync_assoc[where S = \<open>{}\<close>]
   and Inter_Ndet_right_distrib = Sync_Ndet_right_distrib[where S = \<open>{}\<close>]
   and Inter_Ndet_left_distrib = Sync_Ndet_left_distrib[where S = \<open>{}\<close>]
   and Mprefix_Inter_SKIP = Mprefix_Sync_SKIP[where S = \<open>{}\<close>, simplified, simplified Mprefix_STOP]
   and prefix_Inter_SKIP = prefix_Sync_SKIP[where S = \<open>{}\<close>, simplified]
   and mono_Inter_FD = mono_Sync_FD[where S = \<open>{}\<close>]
   and mono_Inter_ref = mono_Sync_ref[where S = \<open>{}\<close>]
   and Hiding_Inter = Hiding_Sync[where S = \<open>{}\<close>, simplified]
   and Mprefix_Inter_distr = Mprefix_Sync_distr_indep[where S = \<open>{}\<close>, simplified]
   and prefix_Inter = Mprefix_Sync_distr_indep[of \<open>{a}\<close> \<open>{}\<close> \<open>{b}\<close> \<open>\<lambda>x. P\<close> \<open>\<lambda>x. Q\<close>,
                                               simplified, folded write0_def] for a P b Q



lemma Inter_SKIP: "(P ||| SKIP) = P"  
proof(auto simp:Process_eq_spec D_Sync F_Sync F_SKIP D_SKIP T_SKIP, goal_cases)
  case (1 a t X Y)
  then have aa:"(X \<union> Y) \<inter> {tick} \<union> X \<inter> Y \<subseteq> X" by (simp add: Int_Un_distrib2)
  have "front_tickFree t" using "1"(1) is_processT2 by blast
  with 1 EmptyLeftSync[of a "{tick}" t] have bb:"a=t"
    using Sync.sym by blast
  from 1(1) aa bb show ?case using is_processT4 by blast
next
  case (2 a t X Y)
  have "front_tickFree t" using 2(1) is_processT2 by blast
  with 2 TickLeftSync[of "{tick}" t a] have bb:"a=t \<and> last t=tick"
    using Sync.sym by blast
  with 2 have "a \<in> \<T> P \<and> last a = tick" using F_T by blast
  with tick_T_F[of "butlast a" P "(X \<union> Y) \<inter> {tick} \<union> X \<inter> Y"] show ?case 
    by (metis "2"(2) EmptyLeftSync bb self_append_conv2 snoc_eq_iff_butlast)
next
  case (3 b t r v)
  with 3 EmptyLeftSync[of r "{tick}" t] have bb:"r=t"
    using Sync.sym by blast
  with 3 show ?case using is_processT by blast
next
  case (4 b t r v)
  with TickLeftSync[of "{tick}" t r, simplified] have bb:"r=t"
    using D_imp_front_tickFree Sync.sym by blast
  with 4 show ?case using is_processT by blast
next
  case (5 b t r)
  with EmptyLeftSync[of r "{tick}" t] have bb:"r=t"
    using Sync.sym by blast
  with 5 show ?case using is_processT by blast
next
  case (6 b t r)
  with TickLeftSync[of "{tick}" t r, simplified] have bb:"r=t"
    using D_imp_front_tickFree Sync.sym by blast
  with 6 show ?case using is_processT by blast
next
  case (7 a b)
  then show ?case 
    apply(cases "tickFree a")
     apply(rule_tac x=a in exI, rule_tac x="[]" in exI, rule_tac x=b in exI, simp)
     apply(rule_tac x="b - {tick}" in exI, simp, intro conjI)
      using emptyLeftSelf[of a "{tick}"] Sync.sym tickFree_def apply fastforce
     apply blast
    apply(rule_tac x=a in exI, rule_tac x="[tick]" in exI, rule_tac x=b in exI, simp, rule conjI)
    subgoal proof -
      assume a1: "\<not> tickFree a"
      assume a2: "(a, b) \<in> \<F> P"
      then obtain ees :: "'a event list \<Rightarrow> 'a event list" where
        f3: "a = ees a @ [tick]"
        using a1 by (meson is_processT2 nonTickFree_n_frontTickFree)
      then have "ees a setinterleaves (([], ees a), {tick})"
        using a2 by (metis (no_types) DiffD2 Diff_insert_absorb emptyLeftSelf 
                                      front_tickFree_implies_tickFree is_processT2 tickFree_def)
      then show "a setinterleaves ((a, [tick]), {tick})"
        using f3 by (metis (no_types) Sync.sym addSyncEmpty insertI1)
    qed
    apply(rule_tac x="b - {tick}" in exI) by blast
next
  case (8 t r v)
  with EmptyLeftSync[of r "{tick}" t] have bb:"r=t"
    using Sync.sym by blast
  with 8 show ?case using is_processT by blast
next
  case (9 t r v)
  with TickLeftSync[of "{tick}" t r, simplified] have bb:"r=t"
    using D_imp_front_tickFree Sync.sym by blast
  with 9 show ?case using is_processT by blast
next
  case (10 t r)
  with EmptyLeftSync[of r "{tick}" t] have bb:"r=t"
    using Sync.sym by blast
  with 10 show ?case by simp
next
  case (11 t r)
  with TickLeftSync[of "{tick}" t r, simplified] have bb:"r=t"
    using D_imp_front_tickFree Sync.sym by blast
  with 11 show ?case by simp
next
  case (12 x)
  then show ?case 
  proof(cases "tickFree x")
    case True
    with 12 show ?thesis 
      apply(rule_tac x=x in exI, rule_tac x="[]" in exI, 
            rule_tac x=x in exI, rule_tac x="[]" in exI, simp)
      by (metis Sync.sym emptyLeftSelf singletonD tickFree_def)
  next
    case False
    with 12 show ?thesis 
      apply(rule_tac x="butlast x" in exI, rule_tac x="[]" in exI, 
            rule_tac x="butlast x" in exI, rule_tac x="[tick]" in exI, simp, intro conjI)
         apply (metis D_imp_front_tickFree append_butlast_last_id front_tickFree_mono 
                      list.distinct(1) tickFree_Nil)  
      using NT_ND T_nonTickFree_imp_decomp apply fastforce 
       apply (metis NT_ND Sync.sym append_T_imp_tickFree append_butlast_last_id emptyLeftSelf 
                    list.distinct(1) singletonD tickFree_Nil tickFree_def)
      using D_imp_front_tickFree is_processT9 nonTickFree_n_frontTickFree by fastforce
  qed
qed

lemma Inter_STOP_Seq_STOP: "(P ||| STOP) = (P  \<^bold>;  STOP)"
proof (auto simp add:Process_eq_spec D_Sync F_Sync F_STOP D_STOP T_STOP F_Seq D_Seq, goal_cases)
  case (1 a t X Y)
  have "insert tick ((X \<union> Y) \<inter> {tick} \<union> X \<inter> Y) \<subseteq> X \<union> {tick}" by blast
  with 1 show ?case
    by (metis (mono_tags, lifting) EmptyLeftSync Sync.sym is_processT 
                                   is_processT5_S2 no_Trace_implies_no_Failure)
next
  case (2 a t X)
  then show ?case using EmptyLeftSync Sync.sym tickFree_def by fastforce
next
  case (3 b t r v)
  then show ?case using EmptyLeftSync Sync.sym tickFree_def by blast
next
  case (4 t r v)
  then show ?case using EmptyLeftSync Sync.sym by blast
next
  case (5 b t r)
  then show ?case by (metis EmptyLeftSync Sync.sym is_processT)
next
  case (6 t r)
  then show ?case using EmptyLeftSync Sync.sym tickFree_def by fastforce
next
  case (7 a b)
  then show ?case 
    apply(rule_tac x=a in exI, rule_tac x="b" in exI, intro conjI)
      apply (meson insert_iff is_processT subsetI)
     using emptyLeftSelf[of a "{tick}"] Sync.sym tickFree_def apply fastforce   
    by blast
next
  case (8 a b)
  then show ?case 
    apply(rule_tac x=a in exI, rule_tac x="b-{tick}" in exI, intro conjI)
      apply (meson NF_NT is_processT6)
     using emptyLeftSelf[of a "{tick}"] Sync.sym tickFree_def 
     apply (metis append_T_imp_tickFree list.distinct(1) singletonD)
    by blast
next
  case (9 b t1 t2)
  hence "t1 setinterleaves ((t1, []), {tick})"
    using emptyLeftSelf[of t1 "{tick}"] Sync.sym tickFree_def by fastforce
  with 9(1)[THEN spec, THEN spec, of t1 t1, simplified] have False
    using "9"(2) "9"(3) "9"(4) by blast
  then show ?case ..
next
  case (10 t r v)
  then show ?case
    apply(rule_tac x=r in exI, rule_tac x="v" in exI, auto)
    using EmptyLeftSync Sync.sym by blast
next
  case (11 t r)
  then show ?case
    apply(rule_tac x=r in exI, rule_tac x="[]" in exI, simp)
    using EmptyLeftSync Sync.sym tickFree_def by fastforce
next
  case (12 t1 t2)
  then show ?case
    apply(rule_tac x=t1 in exI, rule_tac x=t1 in exI, rule_tac x=t2 in exI, simp)
    by (metis Sync.sym emptyLeftSelf singletonD tickFree_def)
qed


lemma Par_STOP: "P \<noteq> \<bottom> \<Longrightarrow> (P || STOP) = STOP"  
proof(auto simp add:Process_eq_spec, 
      simp_all add:D_Sync F_Sync F_STOP D_STOP T_STOP is_processT2 D_imp_front_tickFree F_UU D_UU,
      goal_cases)
  case (1 a b aa ba)
  then show ?case
  proof(elim exE conjE disjE, goal_cases)
    case (1 t X Y)
    then show ?case
      proof(cases t)
        case Nil then show ?thesis using "1"(4) EmptyLeftSync by blast
      next
        case (Cons a list)
        with 1 show ?thesis by (simp split:if_splits, cases a, simp_all)
      qed 
  next
    case (2 t r v)
    hence "[] \<in> \<D> P"
    proof(cases t)
      case Nil with 2 show ?thesis by simp
    next
      case (Cons a list)
      with 2 show ?thesis by (simp split:if_splits, cases a, simp_all)
    qed 
    with 2(1,2) show ?case using NF_ND is_processT7 by fastforce 
  next
    case (3 t r v)
    hence "[] \<in> \<D> P"
    proof(cases t)
      case Nil with 3 show ?thesis by simp
    next
      case (Cons a list)
      with 3 show ?thesis by (simp split:if_splits, cases a, simp_all)
    qed 
    with 3(1,2) show ?case using NF_ND is_processT7 by fastforce 
  qed
next
  case (2 a b aa ba)
  then show ?case
    apply(rule_tac disjI1, rule_tac x="[]" in exI, rule_tac x="{}" in exI, simp, rule_tac conjI)
    using is_processT apply blast
    apply(rule_tac x=ba in exI, rule_tac set_eqI, rule_tac iffI)
    using event_set apply blast
    by fast
next
  case (3 a b x)
  then show ?case 
  proof(elim exE conjE disjE, goal_cases)
    case (1 t r v)
    hence "[] \<in> \<D> P"
    proof(cases t)
      case Nil with 1 show ?thesis by simp
    next
      case (Cons a list)
      with 1 show ?thesis by (simp split:if_splits, cases a, simp_all)
    qed 
    with 3(1,2) show ?case using NF_ND is_processT7 by fastforce
  next
    case (2 t r v)
    hence "[] \<in> \<D> P"
    proof(cases t)
      case Nil with 2 show ?thesis by simp
    next
      case (Cons a list)
      with 2 show ?thesis by (simp split:if_splits, cases a, simp_all)
    qed 
    with 3(1,2) show ?case using NF_ND is_processT7 by fastforce
  qed
next
  case (4 x a b)
  then show ?case
  proof(elim exE conjE disjE, goal_cases)
    case (1 t X Y)
    then show ?case
      proof(cases t)
        case Nil then show ?thesis using "1"(4) EmptyLeftSync by blast
      next
        case (Cons a list)
        with 1 show ?thesis by (simp split:if_splits, cases a, simp_all)
      qed 
  next
    case (2 t r v)
    hence "[] \<in> \<D> P"
    proof(cases t)
      case Nil with 2 show ?thesis by simp
    next
      case (Cons a list)
      with 2 show ?thesis by (simp split:if_splits, cases a, simp_all)
    qed 
    with 2(1,2) show ?case using NF_ND is_processT7 by fastforce 
  next
    case (3 t r v)
    hence "[] \<in> \<D> P"
    proof(cases t)
      case Nil with 3 show ?thesis by simp
    next
      case (Cons a list)
      with 3 show ?thesis by (simp split:if_splits, cases a, simp_all)
    qed 
  with 3(1,2) show ?case using NF_ND is_processT7 by fastforce 
  qed 
next
  case (5 x a b)
  then show ?case
  apply(rule_tac disjI1, rule_tac x="[]" in exI, rule_tac x="{}" in exI, simp, rule_tac conjI)
  using is_processT apply blast
  apply(rule_tac x=b in exI, rule_tac set_eqI, rule_tac iffI)
  using event_set apply blast
  by fast
next
  case (6 x xa)
  then show ?case
  proof(elim exE conjE disjE, goal_cases)
    case (1 t r v)
    hence "[] \<in> \<D> P"
    proof(cases t)
      case Nil with 1 show ?thesis by simp
    next
      case (Cons a list)
      with 1 show ?thesis by (simp split:if_splits, cases a, simp_all)
    qed 
    with 6(1,2) show ?case using NF_ND is_processT7 by fastforce
  next
    case (2 t r v)
    hence "[] \<in> \<D> P"
    proof(cases t)
      case Nil with 2 show ?thesis by simp
    next
      case (Cons a list)
      with 2 show ?thesis by (simp split:if_splits, cases a, simp_all)
    qed 
    with 6(1,2) show ?case using NF_ND is_processT7 by fastforce
  qed
qed


  
section\<open>Multiple Non Deterministic Operator Laws\<close>

lemma Mprefix_refines_Mndetprefix: "(\<sqinter> x \<in> A \<rightarrow> P x) \<le> (\<box> x \<in> A \<rightarrow> P x)"
proof(cases "A = {}")
  case True
  then show ?thesis by (simp add: Mprefix_STOP)
next
  case False
  then show ?thesis 
    by (auto simp add:le_ref_def D_Mprefix write0_def F_Mprefix F_Mndetprefix D_Mndetprefix)
qed

lemma Mndetprefix_refine_FD: "a \<in> A \<Longrightarrow> (\<sqinter> x \<in> A \<rightarrow> (P x)) \<le> (a \<rightarrow> (P a))"
  by(subgoal_tac "A \<noteq> {}", auto simp:le_ref_def D_Mndetprefix F_Mndetprefix)

lemma Mndetprefix_subset_FD:"A \<noteq> {} \<Longrightarrow> (\<sqinter>xa\<in> A \<union> B \<rightarrow>  P) \<le> (\<sqinter>xa\<in> A \<rightarrow>  P)"
  by (simp add: D_Mndetprefix F_Mndetprefix le_ref_def)

lemma mono_Mndetprefix_FD[simp]: "\<forall>x \<in> A. P x \<le> P' x \<Longrightarrow> (\<sqinter> x \<in> A \<rightarrow> (P x)) \<le> (\<sqinter> x \<in> A \<rightarrow> (P' x))"
  apply(cases "A \<noteq> {}", auto simp:le_ref_def D_Mndetprefix F_Mndetprefix)
  by(meson contra_subsetD le_ref_def mono_write0_FD)+ 

lemma Mndetprefix_FD_subset : "A \<noteq> {} \<Longrightarrow> A \<subseteq> B \<Longrightarrow> ((\<sqinter> x \<in> B \<rightarrow> P x)  \<le> (\<sqinter> x \<in> A \<rightarrow> P x))"
  by (metis bot.extremum_uniqueI Mndetprefix_Un_distrib mono_Ndet_FD_right order_refl sup.absorb_iff1)

section \<open> Infra-structure for Communication Primitives \<close>

lemma read_read_Sync:
  assumes contained: "(\<And>y. c y \<in> S)"
    shows "((c\<^bold>?x \<rightarrow> P x) \<lbrakk>S\<rbrakk> (c\<^bold>?x \<rightarrow> Q x)) = (c\<^bold>?x \<rightarrow> ((P x) \<lbrakk>S\<rbrakk> (Q x)))"
proof -
  have A: "range c \<subseteq> S" by (insert contained, auto)
  show ?thesis by (auto simp: read_def o_def Set.Int_absorb2 Mprefix_Sync_distr_subset A)
qed

lemma read_read_non_Sync:
  "\<lbrakk>\<And>y. c y \<notin> S; \<And>y. d y \<in> S\<rbrakk> \<Longrightarrow> (c\<^bold>?x \<rightarrow> (P x)) \<lbrakk>S\<rbrakk> (d\<^bold>?x \<rightarrow>(Q x)) = c\<^bold>?x \<rightarrow> ((P x) \<lbrakk>S\<rbrakk> (d\<^bold>?x \<rightarrow>(Q x)))"
  apply (auto simp add: read_def o_def)
  using Mprefix_Sync_distr_right[of "range c" S "range d" "\<lambda>x. Q (inv d x)" "\<lambda>x. P (inv c x)"]
  apply (subst (1 2) Sync_commute)
  by auto

lemma write_read_Sync:
  assumes contained: "\<And>y. c y \<in> S"
      and is_construct: "inj c"
    shows "(c\<^bold>!a \<rightarrow> P) \<lbrakk>S\<rbrakk> (c\<^bold>?x \<rightarrow> Q x) = (c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk> Q a))"
proof -
  have A : "range c \<subseteq> S" by (insert contained, auto)
  have B : " {c a} \<inter> range c \<inter> S = {c a}" by (insert contained, auto)
  show ?thesis
    apply (simp add: read_def write_def o_def, subst Mprefix_Sync_distr_subset)
    by (simp_all add: A B contained Mprefix_singl is_construct)
qed

lemma write_read_non_Sync:
  "\<lbrakk>d a \<notin> S; \<And>y. c y \<in> S \<rbrakk> \<Longrightarrow> (d\<^bold>!a \<rightarrow> P) \<lbrakk>S\<rbrakk> (c\<^bold>?x \<rightarrow> Q x) = d\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk> (c\<^bold>?x \<rightarrow> Q x))"
  apply (simp add: read_def o_def write_def)
  using Mprefix_Sync_distr_right[of "{d a}" S "range c" "\<lambda>x. (Q (inv c x))" "\<lambda>x. P"]
  apply (subst (1 2) Sync_commute)
  by auto
 
lemma write0_read_non_Sync:
  "\<lbrakk>d \<in> S; \<And>y. c y \<notin> S\<rbrakk> \<Longrightarrow> (d \<rightarrow> P) \<lbrakk>S\<rbrakk> (c\<^bold>?x \<rightarrow> Q x) = c\<^bold>?x \<rightarrow> ((d \<rightarrow> P) \<lbrakk>S\<rbrakk> Q x)"
  apply (simp add: read_def o_def)
  apply (subst (1 2)  Mprefix_singl[symmetric])
  apply (subst Mprefix_Sync_distr_right)
  by auto
  
lemma write0_write_non_Sync:
 "\<lbrakk>d a \<notin> C; c \<in> C\<rbrakk> \<Longrightarrow> (c \<rightarrow> Q) \<lbrakk>C\<rbrakk> (d\<^bold>!a \<rightarrow> P) = d\<^bold>!a \<rightarrow> ((c \<rightarrow> Q) \<lbrakk>C\<rbrakk> P)"
  apply(simp add: write_def )
  apply(subst (1 2) Mprefix_singl[symmetric])
  by (auto simp: Mprefix_Sync_distr_right)


  


(* ************************************************************************* *)
(* 	                                                    								     *)
(* Setup for rewriting							                                         *)
(* 									                                                         *)
(* ************************************************************************* *)

lemmas Sync_rules =  prefix_Sync2 
                     read_read_Sync read_read_non_Sync 
                     write_read_Sync write_read_non_Sync 
                     write0_read_non_Sync 
                     write0_write_non_Sync

lemmas Hiding_rules = no_Hiding_read no_Hiding_write Hiding_write Hiding_write0

lemmas mono_rules = mono_read_ref mono_write_ref mono_write0_ref

end

