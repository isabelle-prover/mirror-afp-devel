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




subsubsection \<open>Useful Results about \<^const>\<open>finitary\<close>, and Preliminaries Lemmas for Continuity.\<close>


lemma le_snoc_is : \<open>t \<le> s @ [x] \<longleftrightarrow> t = s @ [x] \<or> t \<le> s\<close>
  by (metis append_eq_first_pref_spec le_list_def order.trans self_append_conv)

lemma Cont_RenH5: \<open>finite (\<Union>t \<in> {t. t \<le> (s :: '\<alpha> trace)}. {s. t=map (EvExt f) s})\<close> if \<open>finitary f\<close>
  apply (rule finite_UN_I)
   apply (induct s rule: rev_induct)
    apply (simp; fail)
   apply (simp add: le_snoc_is; fail)
  using Cont_RenH2 Cont_RenH4 that by blast


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


subsection \<open>Nice Properties\<close>


lemma Renaming_inv: \<open>Renaming (Renaming P f) (inv f) = P\<close> if \<open>inj f\<close>
  apply (subst Renaming_comp[symmetric])
  apply (subst inv_o_cancel[OF that])
  by (fact Renaming_id) 


subsection \<open>Renaming Laws\<close>


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



(* TODO: write corollaries on read and write *)


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


section \<open>Lifelock Freeness\<close>

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
