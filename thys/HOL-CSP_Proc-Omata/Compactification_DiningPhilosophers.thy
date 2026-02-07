(***********************************************************************************
 * Copyright (c) 2025 Université Paris-Saclay
 *
 * Author: Benoît Ballenghien, Université Paris-Saclay,
 *         CNRS, ENS Paris-Saclay, LMF
 * Author: Burkhart Wolff, Université Paris-Saclay,
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


chapter \<open>Application : May Philosophers dine ? \<close>

(*<*)
theory Compactification_DiningPhilosophers
  imports Compactification_Synchronization_Product "HOL-CSPM.DiningPhilosophers"
begin

unbundle option_type_syntax
  (*>*)



section \<open>Preliminaries\<close>

subsection \<open>Preliminary lemmas for proof automation\<close>

lemma Suc_mod: \<open>n > 1 \<Longrightarrow> i \<noteq> Suc i mod n\<close>
  by (metis One_nat_def mod_Suc mod_if mod_mod_trivial n_not_Suc_n)

lemmas suc_mods = Suc_mod Suc_mod[symmetric]

lemma l_suc: \<open>n > 1 \<Longrightarrow> \<not> n \<le> Suc 0\<close>
  by simp 

lemma minus_suc: \<open>n > 0 \<Longrightarrow> n - Suc 0 \<noteq> n\<close>
  by linarith

declare Un_insert_right[simp del] Un_insert_left[simp del] 

(*declare Mprefix_Un_distrib[simp]  is there an issue declaring this lemma simp ? *)


section \<open>The dining processes definition\<close>

context DiningPhilosophers begin

lemma RPHIL_restriction_fix_def:
  \<open>RPHIL i = (\<upsilon> X. picks i i \<rightarrow> picks i ((i - 1) mod N) \<rightarrow>
                   putsdown i ((i - 1) mod N) \<rightarrow> putsdown i i \<rightarrow> X)\<close>
  by (simp add: RPHIL_def restriction_fix_is_fix)

lemma LPHIL0_restriction_fix_def:
  \<open>LPHIL0 = (\<upsilon> X. picks 0 (N - 1) \<rightarrow> picks 0 0 \<rightarrow>
                  putsdown 0 0 \<rightarrow> putsdown 0 (N - 1) \<rightarrow> X)\<close>
  by (simp add: LPHIL0_def restriction_fix_is_fix)

lemma FORK_restriction_fix_def:
  \<open>FORK i = (\<upsilon> X. (picks i i \<rightarrow> putsdown i i \<rightarrow> X) \<box>
                  (picks ((i + 1) mod N) i \<rightarrow> putsdown ((i + 1) mod N) i \<rightarrow> X))\<close>
  by (simp add: FORK_def restriction_fix_is_fix)



subsection \<open>Unfolding rules\<close>

lemmas  RPHIL_rec = cont_process_rec[OF  RPHIL_def[THEN meta_eq_to_obj_eq], simplified]
  and LPHIL0_rec = cont_process_rec[OF LPHIL0_def[THEN meta_eq_to_obj_eq], simplified]
  and   FORK_rec = cont_process_rec[OF   FORK_def[THEN meta_eq_to_obj_eq], simplified]



section \<open>Translation into normal form\<close>

lemma N_pos[simp]: \<open>N > 0\<close>
  using N_g1 neq0_conv by blast

lemmas N_pos_simps[simp] = suc_mods[OF N_g1] l_suc[OF N_g1] minus_suc[OF N_pos]



subsection \<open>\<^const>\<open>FORK\<close>, \<^const>\<open>LPHIL0\<close> and \<^const>\<open>RPHIL\<close> are normalizable\<close>

text \<open>Definition of one \<^emph>\<open>fork\<close> and one \<^emph>\<open>philosopher\<close> automata\<close>

type_synonym id\<^sub>f\<^sub>o\<^sub>r\<^sub>k = nat
type_synonym \<sigma>\<^sub>f\<^sub>o\<^sub>r\<^sub>k  = nat
type_synonym id\<^sub>p\<^sub>h\<^sub>i\<^sub>l = nat
type_synonym \<sigma>\<^sub>p\<^sub>h\<^sub>i\<^sub>l  = nat



definition   fork_A :: \<open>id\<^sub>f\<^sub>o\<^sub>r\<^sub>k \<Rightarrow> (\<sigma>\<^sub>f\<^sub>o\<^sub>r\<^sub>k, dining_event, unit) A\<^sub>d\<close> (\<open>A\<^sub>f\<close>)
  where \<open>A\<^sub>f i \<equiv> recursive_constructor_A\<^sub>d
                [((0, picks i i),    \<lfloor>1\<rfloor>), ((0, picks ((i + 1) mod N) i),    \<lfloor>2\<rfloor>),
                 ((1, putsdown i i), \<lfloor>0\<rfloor>), ((2, putsdown ((i + 1) mod N) i), \<lfloor>0\<rfloor>)] (\<lambda>\<sigma>. \<diamond>)\<close>


definition  rphil_A :: \<open>id\<^sub>p\<^sub>h\<^sub>i\<^sub>l \<Rightarrow> (\<sigma>\<^sub>p\<^sub>h\<^sub>i\<^sub>l, dining_event, unit) A\<^sub>d\<close> (\<open>A\<^sub>r\<^sub>p\<close>)
  where \<open>A\<^sub>r\<^sub>p i \<equiv> recursive_constructor_A\<^sub>d
                 [((0, picks i i),                \<lfloor>1\<rfloor>), ((1, picks i ((i-1) mod N)), \<lfloor>2\<rfloor>),
                  ((2, putsdown i ((i-1) mod N)), \<lfloor>3\<rfloor>), ((3, putsdown i i),          \<lfloor>0\<rfloor>)] (\<lambda>\<sigma>. \<diamond>)\<close>


definition lphil0_A :: \<open>(\<sigma>\<^sub>p\<^sub>h\<^sub>i\<^sub>l, dining_event, unit) A\<^sub>d\<close> (\<open>A\<^sub>l\<^sub>p\<close>)
  where \<open>A\<^sub>l\<^sub>p \<equiv> recursive_constructor_A\<^sub>d
               [((0, picks 0 (N - 1)), \<lfloor>1\<rfloor>), ((1, picks 0 0),          \<lfloor>2\<rfloor>),
                ((2, putsdown 0 0),    \<lfloor>3\<rfloor>), ((3, putsdown 0 (N - 1)), \<lfloor>0\<rfloor>)] (\<lambda>\<sigma>. \<diamond>)\<close>



text \<open>Definition and first properties of associated normal processes\<close>

definition fork_P_d :: \<open>id\<^sub>f\<^sub>o\<^sub>r\<^sub>k \<Rightarrow> \<sigma>\<^sub>f\<^sub>o\<^sub>r\<^sub>k \<Rightarrow> dining_event process\<close>  where \<open>fork_P_d  i \<equiv> P\<llangle>A\<^sub>f i\<rrangle>\<^sub>d\<close>
definition rphil_P_d :: \<open>id\<^sub>p\<^sub>h\<^sub>i\<^sub>l \<Rightarrow> \<sigma>\<^sub>p\<^sub>h\<^sub>i\<^sub>l \<Rightarrow> dining_event process\<close> where \<open>rphil_P_d i \<equiv> P\<llangle>A\<^sub>r\<^sub>p i\<rrangle>\<^sub>d\<close>
definition lphil0_P_d :: \<open>\<sigma>\<^sub>p\<^sub>h\<^sub>i\<^sub>l \<Rightarrow> dining_event process\<close>         where \<open>lphil0_P_d  \<equiv> P\<llangle>A\<^sub>l\<^sub>p\<rrangle>\<^sub>d\<close>


lemmas   fork_P_d_rec = P_d_rec[of \<open>A\<^sub>f _\<close>,  folded fork_P_d_def]
  and  rphil_P_d_rec = P_d_rec[of \<open>A\<^sub>r\<^sub>p _\<close>, folded rphil_P_d_def]
  and lphil0_P_d_rec = P_d_rec[of \<open>A\<^sub>l\<^sub>p\<close>,   folded lphil0_P_d_def]




schematic_goal   fork_\<epsilon>: \<open>\<epsilon> (A\<^sub>f i) \<sigma> = ?S\<close>
  and  rphil_\<epsilon>: \<open>\<epsilon> (A\<^sub>r\<^sub>p i) \<sigma> = ?T\<close>
  and lphil0_\<epsilon>: \<open>\<epsilon> A\<^sub>l\<^sub>p \<sigma> = ?U\<close> 
  unfolding fork_A_def rphil_A_def lphil0_A_def by (all \<epsilon>_det_calc)

schematic_goal   fork_\<tau>: \<open>\<tau> (A\<^sub>f i) \<sigma> = ?S\<close>
  and  rphil_\<tau>: \<open>\<tau> (A\<^sub>r\<^sub>p i) \<sigma> = ?T\<close>
  and lphil0_\<tau>: \<open>\<tau> A\<^sub>l\<^sub>p \<sigma> = ?U\<close>
  unfolding fork_A_def rphil_A_def lphil0_A_def by (all \<tau>_det_calc)


corollary   ev_id\<^sub>f\<^sub>o\<^sub>r\<^sub>kx: \<open>e \<in> \<epsilon> (A\<^sub>f i) \<sigma> \<Longrightarrow> fork e = i\<close> 
  and  rphil_phil: \<open>e \<in> \<epsilon> (A\<^sub>r\<^sub>p i) \<sigma> \<Longrightarrow> phil e = i\<close>
  and lphil0_phil: \<open>e \<in> \<epsilon> A\<^sub>l\<^sub>p \<sigma>     \<Longrightarrow> phil e = 0\<close>
  by (auto simp add: fork_\<epsilon> rphil_\<epsilon> lphil0_\<epsilon> split: if_split_asm)

corollary ev_id\<^sub>p\<^sub>h\<^sub>i\<^sub>lx: \<open>i < n \<Longrightarrow> \<sigma> \<in> \<epsilon> ((A\<^sub>l\<^sub>p # map A\<^sub>r\<^sub>p [1..< n]) ! i) s \<Longrightarrow> phil \<sigma> = i\<close>
  by (cases \<open>i = 0\<close>) (simp_all add: lphil0_phil rphil_phil) 


lemma indep_forks: \<open>i \<noteq> j \<Longrightarrow> \<epsilon> (A\<^sub>f i) \<sigma> \<inter> \<epsilon> (A\<^sub>f j) \<sigma>' = {}\<close>
  and indep_phils: \<open>i \<noteq> 0 \<Longrightarrow> \<epsilon> A\<^sub>l\<^sub>p \<sigma> \<inter> \<epsilon> (A\<^sub>r\<^sub>p i) \<sigma>' = {}\<close>
  \<open>i \<noteq> j \<Longrightarrow> \<epsilon> (A\<^sub>r\<^sub>p i) \<sigma> \<inter> \<epsilon> (A\<^sub>r\<^sub>p j) \<sigma>' = {}\<close>
  using ev_id\<^sub>f\<^sub>o\<^sub>r\<^sub>kx lphil0_phil rphil_phil by (blast, simp, fastforce, blast)



text \<open>Equalities between \<^const>\<open>FORK\<close>, \<^const>\<open>RPHIL\<close>, \<^const>\<open>LPHIL0\<close>
      and respectively \<^const>\<open>fork_P_d\<close>, \<^const>\<open>rphil_P_d\<close>, \<^const>\<open>lphil0_P_d\<close>\<close>

lemma FORK_is_fork_P_d: \<open>FORK i = fork_P_d i 0\<close>
proof (unfold fork_P_d_def)
  have \<open>(0 :: nat) < 2\<close> by simp
  thus \<open>FORK i = P\<llangle>A\<^sub>f i\<rrangle>\<^sub>d 0\<close>
  proof (induct rule: P_d_induct_iterated)
    show \<open>FORK i = X 0 \<Longrightarrow> FORK i = (P_d_step (\<epsilon> (A\<^sub>f i)) (\<tau> (A\<^sub>f i)) ^^ 2) X 0\<close> for X
      by (subst FORK_rec)
        (auto simp add: Mprefix_Det_Mprefix write0_def numeral_eq_Suc
          fork_\<epsilon> fork_\<tau> Un_commute intro!: mono_Mprefix_eq)
  qed simp_all
qed


lemma RPHIL_is_rphil_P_d: \<open>RPHIL i = rphil_P_d i 0\<close>
proof (unfold rphil_P_d_def)
  have \<open>(0 :: nat) < 4\<close> by simp
  thus \<open>RPHIL i = P\<llangle>A\<^sub>r\<^sub>p i\<rrangle>\<^sub>d 0\<close>
  proof (induct rule: P_d_induct_iterated)
    show \<open>RPHIL i = X 0 \<Longrightarrow> RPHIL i = (P_d_step (\<epsilon> (A\<^sub>r\<^sub>p i)) (\<tau> (A\<^sub>r\<^sub>p i)) ^^ 4) X 0\<close> for X
      by (subst RPHIL_rec)
        (auto simp add: write0_def numeral_eq_Suc rphil_\<epsilon> rphil_\<tau> intro!: mono_Mprefix_eq)
  qed simp_all
qed


lemma LPHIL0_is_lphil0_P_d: \<open>LPHIL0 = lphil0_P_d 0\<close>
proof (unfold lphil0_P_d_def)
  have \<open>(0 :: nat) < 4\<close> by simp
  thus \<open>LPHIL0 = P\<llangle>A\<^sub>l\<^sub>p\<rrangle>\<^sub>d 0\<close>
  proof (induct rule: P_d_induct_iterated)
    show \<open>LPHIL0 = X 0 \<Longrightarrow> LPHIL0 = (P_d_step (\<epsilon> A\<^sub>l\<^sub>p) (\<tau> A\<^sub>l\<^sub>p) ^^ 4) X 0\<close> for X
      by (subst LPHIL0_rec)
        (auto simp add: write0_def numeral_eq_Suc lphil0_\<epsilon> lphil0_\<tau> intro!: mono_Mprefix_eq)
  qed simp_all
qed



subsection \<open>\<^const>\<open>FORKS\<close> is normalizable\<close>

text \<open>Definition of the all-forks automaton\<close>

type_synonym \<sigma>\<^sub>f\<^sub>o\<^sub>r\<^sub>k\<^sub>s = \<open>nat list\<close>


definition forks_A :: \<open>(\<sigma>\<^sub>f\<^sub>o\<^sub>r\<^sub>k\<^sub>s, dining_event, unit) A\<^sub>d\<close> (\<open>A\<^sub>F\<close>) where \<open>A\<^sub>F \<equiv> \<llangle>\<^sub>d\<Otimes>\<lbrakk>{}\<rbrakk> map A\<^sub>f [0..<N]\<rrangle>\<close>



text \<open>Definition and first properties of the associated normal process\<close>

definition forks_P_d:: \<open>\<sigma>\<^sub>f\<^sub>o\<^sub>r\<^sub>k\<^sub>s \<Rightarrow> dining_event process\<close> where \<open>forks_P_d \<equiv> P\<llangle>A\<^sub>F\<rrangle>\<^sub>d\<close>


lemma forks_\<epsilon>: \<open>length fs = N \<Longrightarrow> \<epsilon> A\<^sub>F fs = (\<Union>i<N. \<epsilon> (A\<^sub>f i) (fs ! i))\<close>
  unfolding forks_A_def using N_pos by (subst \<epsilon>_iterated_combine\<^sub>d_Sync_general_form) force+ 



text \<open>Equality between \<^const>\<open>FORKS\<close> and \<^const>\<open>forks_P_d\<close>\<close>

lemma NFORKS_is_forks_P_d: \<open>FORKS = forks_P_d (replicate N 0)\<close>
  unfolding forks_P_d_def forks_A_def FORKS_def
  apply (subst P_d_compactification_Sync_upt_version)
  by (simp_all add: FORK_is_fork_P_d[unfolded fork_P_d_def] indep_forks indep_enabl_def)



subsection \<open>\<^const>\<open>PHILS\<close> is normalizable\<close>

text \<open>Definition of the all-philosophers automaton\<close>

type_synonym \<sigma>\<^sub>p\<^sub>h\<^sub>i\<^sub>l\<^sub>s = \<open>nat list\<close>


definition phils_A :: \<open>(\<sigma>\<^sub>p\<^sub>h\<^sub>i\<^sub>l\<^sub>s, dining_event, unit) A\<^sub>d\<close> (\<open>A\<^sub>P\<close>) where \<open>A\<^sub>P \<equiv> \<llangle>\<^sub>d\<Otimes>\<lbrakk>{}\<rbrakk> A\<^sub>l\<^sub>p # map A\<^sub>r\<^sub>p [1..< N]\<rrangle>\<close>

lemma phils_A_def_bis: \<open>A\<^sub>P = \<llangle>\<^sub>d\<Otimes>\<lbrakk>{}\<rbrakk> map (\<lambda>i. if i = 0 then A\<^sub>l\<^sub>p else A\<^sub>r\<^sub>p i) [0..<N]\<rrangle>\<close>
  unfolding phils_A_def apply (subst (2) upt_rec, simp)
  apply (subgoal_tac \<open>map (\<lambda>i. if i = 0 then A\<^sub>l\<^sub>p else A\<^sub>r\<^sub>p i) [Suc 0..<N] = map A\<^sub>r\<^sub>p [Suc 0..<N]\<close>)
  by (presburger, subst list_eq_iff_nth_eq, simp)



text \<open>Definition and first properties of the associated normal process\<close>

definition phils_P_d:: \<open>\<sigma>\<^sub>p\<^sub>h\<^sub>i\<^sub>l\<^sub>s \<Rightarrow> dining_event process\<close> where \<open>phils_P_d \<equiv> P\<llangle>A\<^sub>P\<rrangle>\<^sub>d\<close>


lemma phils_\<epsilon>: \<open>length ps = N \<Longrightarrow> \<epsilon> A\<^sub>P ps = \<epsilon> A\<^sub>l\<^sub>p (ps ! 0) \<union> (\<Union>i\<in>{1..<N}. \<epsilon> (A\<^sub>r\<^sub>p i) (ps ! i))\<close>
  unfolding phils_A_def_bis using N_pos
  by (subst \<epsilon>_iterated_combine\<^sub>d_Sync_general_form, (auto split: if_splits)+)



text \<open>Equality between \<^const>\<open>PHILS\<close> and \<^const>\<open>phils_P_d\<close>\<close>

lemma NPHILS_is_phils_P_d: \<open>PHILS = phils_P_d (replicate N 0)\<close>
  unfolding phils_P_d_def phils_A_def_bis PHILS_def
  apply (subst P_d_compactification_Sync_upt_version[symmetric])
    apply (simp_all add: indep_enabl_def indep_phils(1,2) inf_sup_aci(1))
  apply (subgoal_tac \<open>{0..<N} = insert 0 {1..<N}\<close>)
   apply (simp add: LPHIL0_is_lphil0_P_d lphil0_P_d_def)
  by (rule arg_cong[OF image_mset_cong]) (auto simp add: RPHIL_is_rphil_P_d rphil_P_d_def)



subsection \<open>The complete process \<^const>\<open>DINING\<close> is normalizable\<close>

text \<open>Definition of the dining automaton\<close>

definition dining_A :: \<open>(\<sigma>\<^sub>p\<^sub>h\<^sub>i\<^sub>l\<^sub>s \<times> \<sigma>\<^sub>f\<^sub>o\<^sub>r\<^sub>k\<^sub>s, dining_event, unit) A\<^sub>d\<close> (\<open>A\<^sub>D\<close>) where \<open>A\<^sub>D \<equiv> \<llangle>A\<^sub>P \<^sub>d\<otimes>\<lbrakk>UNIV\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>F\<rrangle>\<close>



text \<open>Definition and first properties of the associated normal process\<close>

definition dining_P_d:: \<open>\<sigma>\<^sub>p\<^sub>h\<^sub>i\<^sub>l\<^sub>s \<times> \<sigma>\<^sub>f\<^sub>o\<^sub>r\<^sub>k\<^sub>s \<Rightarrow> dining_event process\<close> where \<open>dining_P_d \<equiv> P\<llangle>A\<^sub>D\<rrangle>\<^sub>d\<close>

lemma dining_\<epsilon>:
  \<open>length ps = N \<Longrightarrow> length fs = N \<Longrightarrow>
   \<epsilon> A\<^sub>D (ps, fs) = (\<epsilon> A\<^sub>l\<^sub>p (ps ! 0) \<union> (\<Union>i\<in>{1..<N}. \<epsilon> (A\<^sub>r\<^sub>p i) (ps ! i))) \<inter> (\<Union>i<N. \<epsilon> (A\<^sub>f i) (fs ! i))\<close>
  by (simp add: dining_A_def \<epsilon>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync combine_Sync_\<epsilon>_def forks_\<epsilon> phils_\<epsilon>)


text \<open>Equality between \<^const>\<open>DINING\<close> and \<^const>\<open>dining_P_d\<close>\<close>

lemma DINING_is_dining_P_d: \<open>DINING = dining_P_d (replicate N 0, replicate N 0)\<close>
  unfolding dining_P_d_def dining_A_def
  apply (subst P_d_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync[symmetric])
   apply (simp add: indep_enabl_def)
  by (simp add: DINING_def NFORKS_is_forks_P_d NPHILS_is_phils_P_d Sync_commute forks_P_d_def phils_P_d_def)



section \<open>And finally: Philosophers may dine ! Always !\<close>

method \<epsilon>_sets_simp uses opt = (simp_all split: if_split_asm)?,
  simp_all add: fork_\<epsilon> lphil0_\<epsilon> rphil_\<epsilon> opt split: if_splits
method A_defs_simp uses opt = (simp_all split: if_split_asm)?,
  simp_all add: fork_A_def lphil0_A_def rphil_A_def opt split: if_splits



subsection \<open>Construction of an invariant for the dining automaton\<close>

definition \<open>inv_dining ps fs \<equiv>
            length fs = N \<and> length ps = N
          \<and> (\<forall>i < N. fs ! i = 0 \<or> fs ! i = 1 \<or> fs ! i = 2) 
          \<and> (\<forall>i < N. ps ! i = 0 \<or> ps ! i = 1 \<or> ps ! i = 2 \<or> ps ! i = 3)
          \<and> (\<forall>i. Suc i < N \<longrightarrow> ((fs ! Suc i = 1) \<longleftrightarrow> ps ! Suc i \<noteq> 0)) \<and> (fs ! (N - 1) = 2 \<longleftrightarrow> ps ! 0 \<noteq> 0)
          \<and> (\<forall>i < N - 1.           fs ! i = 2    \<longleftrightarrow> ps ! Suc i = 2)  \<and>    (fs ! 0  = 1   \<longleftrightarrow> ps ! 0 = 2)\<close> 


lemma show_inv_dining: 
  \<open>length fs = N \<and> length ps = N \<Longrightarrow>
   (\<forall>i < N. fs ! i = 0 \<or> fs ! i = 1 \<or> fs ! i = 2) \<Longrightarrow>
   (\<forall>i < N. ps ! i = 0 \<or> ps ! i = 1 \<or> ps ! i = 2 \<or> ps ! i = 3) \<Longrightarrow>
   (\<forall>i. Suc i < N \<longrightarrow> (fs ! Suc i = 1 \<longleftrightarrow> ps ! Suc i \<noteq> 0)) \<Longrightarrow> (fs ! (N - 1) = 2 \<longleftrightarrow> ps ! 0 \<noteq> 0) \<Longrightarrow>
   (\<forall>i < N - 1. fs ! i = 2 \<longleftrightarrow> ps ! Suc i = 2) \<Longrightarrow> (fs ! 0  = 1 \<longleftrightarrow> ps ! 0 = 2) \<Longrightarrow> 
   inv_dining ps fs\<close>
  by (simp add: inv_dining_def)



lemma inv_DINING: \<open>s \<in> \<R>\<^sub>d A\<^sub>D (replicate N 0, replicate N 0) \<Longrightarrow> inv_dining (fst s) (snd s)\<close>
proof(induct rule: \<R>\<^sub>d.induct)
  case init show ?case by (simp add: inv_dining_def)
next
  case (step t u e)
  obtain t_ps t_fs u_ps u_fs where t_pair: \<open>t = (t_ps, t_fs)\<close> and u_pair: \<open>u = (u_ps, u_fs)\<close> by fastforce
  hence inv_hyp: \<open>length t_fs = N\<close> \<open>length t_ps = N\<close> 
    \<open>i < N \<Longrightarrow> t_fs ! i = 0 \<or> t_fs ! i = 1 \<or> t_fs ! i = 2\<close>
    \<open>i < N \<Longrightarrow> t_ps ! i = 0 \<or> t_ps ! i = 1 \<or> t_ps ! i = 2 \<or> t_ps ! i = 3\<close>
    \<open>Suc i < N \<Longrightarrow> (t_fs ! Suc i = 1) = (t_ps ! Suc i \<noteq> 0)\<close>
    \<open>(t_fs ! (N - 1) = 2) = (t_ps ! 0 \<noteq> 0)\<close>
    \<open>i < N - 1 \<Longrightarrow> (t_fs ! i = 2) = (t_ps ! Suc i = 2)\<close>
    \<open>(t_fs ! 0 = 1) = (t_ps ! 0 = 2)\<close> for i
    using step.hyps(2)[simplified inv_dining_def] by simp_all

  have u_in_\<R>\<^sub>d_prem: \<open>(u_ps, u_fs) \<in> \<R>\<^sub>d A\<^sub>P (replicate N 0) \<times> \<R>\<^sub>d A\<^sub>F (replicate N 0)\<close>
    using \<R>\<^sub>d.step[OF step.hyps(1, 3), simplified dining_A_def]
    by (simp add: u_pair[symmetric], rule set_mp[OF \<R>\<^sub>d_combine\<^sub>d\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_subset])
  note u_in_\<R>\<^sub>d = u_in_\<R>\<^sub>d_prem[simplified mem_Times_iff, THEN conjunct1, simplified]
    u_in_\<R>\<^sub>d_prem[simplified mem_Times_iff, THEN conjunct2, simplified]

  have same_length_u: \<open>length u_ps = N\<close> \<open>length u_fs = N\<close> 
    using same_length_\<R>\<^sub>d_iterated_combine\<^sub>d_Sync_description[rotated, OF u_in_\<R>\<^sub>d(1)[unfolded phils_A_def]]
      same_length_\<R>\<^sub>d_iterated_combine\<^sub>d_Sync_description[rotated, OF u_in_\<R>\<^sub>d(2)[unfolded forks_A_def]]
    by simp+

  have u_is: \<open>\<lfloor>u_ps\<rfloor> = \<tau> A\<^sub>P t_ps e\<close> \<open>\<lfloor>u_fs\<rfloor> = \<tau> A\<^sub>F t_fs e\<close>
    using step(3)[simplified dining_A_def, simplified combine_Sync_defs]
    by (simp_all add: t_pair u_pair option.case_eq_if map_option_case split: if_splits)

  have e_in: \<open>e \<in> \<epsilon> A\<^sub>l\<^sub>p (t_ps ! 0) \<union> (\<Union>i\<in>{1..<N}. \<epsilon> (A\<^sub>r\<^sub>p i) (t_ps ! i))\<close>
    \<open>e \<in> (\<Union>i<N. \<epsilon> (A\<^sub>f i) (t_fs ! i))\<close>
    by (subst phils_\<epsilon>[symmetric], fact inv_hyp(2), simp add: \<epsilon>_simps, metis u_is(1))
      (subst forks_\<epsilon>[symmetric], fact inv_hyp(1), simp add: \<epsilon>_simps, metis u_is(2))

  have u_nth:
    \<open>i < N \<Longrightarrow> u_ps ! i = 
    (if i = 0 then (if e \<in> \<epsilon> A\<^sub>l\<^sub>p (t_ps ! 0) then \<lceil>\<tau> A\<^sub>l\<^sub>p (t_ps ! 0) e\<rceil> else t_ps ! 0)
     else if e \<in> \<epsilon> (A\<^sub>r\<^sub>p i) (t_ps ! i) then \<lceil>\<tau> (A\<^sub>r\<^sub>p i) (t_ps ! i) e\<rceil> else t_ps ! i)\<close> 
    \<open>i < N \<Longrightarrow> u_fs ! i =
     (if e \<in> \<epsilon> (A\<^sub>f i) (t_fs ! i) then \<lceil>\<tau> (A\<^sub>f i) (t_fs ! i) e\<rceil> else t_fs ! i)\<close> for i
    by (insert u_is(1), unfold phils_A_def, subst (asm) \<tau>_iterated_combine\<^sub>d_Sync_general_form,
        simp_all add: inv_hyp(2) split: if_splits)
      (insert u_is(2), unfold forks_A_def, subst (asm) \<tau>_iterated_combine\<^sub>d_Sync_general_form,
        simp_all add: inv_hyp(1) split: if_splits)
  have \<open>e \<in> \<epsilon> A\<^sub>P t_ps\<close> \<open>e \<in> \<epsilon> A\<^sub>F t_fs\<close> using u_is \<epsilon>_simps by fastforce+
  hence e_equiv: \<open>e \<in> \<epsilon> A\<^sub>l\<^sub>p (t_ps ! 0) \<longleftrightarrow> phil e = 0\<close>
    \<open>Suc i < N \<Longrightarrow> e \<in> \<epsilon> (A\<^sub>r\<^sub>p (Suc i)) (t_ps ! Suc i) \<longleftrightarrow> phil e = Suc i\<close>
    \<open>i < N \<Longrightarrow> e \<in> \<epsilon> (A\<^sub>f i) (t_fs ! i) \<longleftrightarrow> fork e = i\<close> for i
      apply (simp_all add: phils_\<epsilon>[OF inv_hyp(2)] forks_\<epsilon>[OF inv_hyp(1)])
    using rphil_phil lphil0_phil ev_id\<^sub>f\<^sub>o\<^sub>r\<^sub>kx by auto (metis Suc_le_eq less_irrefl_nat, blast, metis) 

  show ?case
  proof (simp add: u_pair, rule show_inv_dining[rule_format], simp add: same_length_u, goal_cases)
    case (1 i) thus ?case using u_nth(2)[of i] inv_hyp(3) by \<epsilon>_sets_simp A_defs_simp
  next
    case (2 i) thus ?case using u_nth(1)[of i] inv_hyp(4) by \<epsilon>_sets_simp A_defs_simp
  next
    case (3 i)
    with u_nth(1)[of \<open>Suc i\<close>] u_nth(2)[of \<open>Suc i\<close>] show ?case
      using inv_hyp(5)[of i] apply \<epsilon>_sets_simp apply A_defs_simp
      using e_equiv(3) fork_\<epsilon> e_equiv(2) rphil_\<epsilon> by fastforce+
  next
    case 4
    with u_nth(1)[of 0] u_nth(2) show ?case using inv_hyp(6) N_g1 apply \<epsilon>_sets_simp apply A_defs_simp
         apply (metis N_pos One_nat_def Suc_pred fork_\<epsilon> dining_event.sel(3) 
          dining_event.simps(3) inv_hyp(3) lessI singletonD e_equiv(3))
      using lphil0_\<epsilon> e_equiv(1) by force+
  next
    case (5 i)
    hence \<open>Suc i < N\<close> by linarith
    with u_nth(1)[of \<open>Suc i\<close>] u_nth(2)[of i] "5" show ?case 
      using inv_hyp(7)[of i] apply \<epsilon>_sets_simp apply A_defs_simp
          apply (metis Suc_lessD fork_\<epsilon> dining_event.sel(3) dining_event.simps(3) singletonD e_equiv(3))
         apply (metis One_nat_def Suc_lessD bot_nat_0.not_eq_extremum inv_hyp(3))
      using rphil_\<epsilon> e_equiv(2) by force+
  next
    case 6
    with u_nth(1)[of 0] u_nth(2)[of 0] show ?case
      using N_g1 inv_hyp(8) apply (simp split: if_split_asm) apply \<epsilon>_sets_simp apply A_defs_simp
      using lphil0_\<epsilon> e_equiv(1) fork_\<epsilon> e_equiv(3) by force+
  qed
qed


subsection \<open>The invariant \<^const>\<open>inv_dining\<close> implies that \<^const>\<open>DINING\<close> is \<^const>\<open>deadlock_free\<close>\<close>

method nonempty_Int_by_common_element for x = rule_tac ex_in_conv[THEN iffD1, OF exI, OF IntI, of x]

lemma inv_implies_DF: \<open>\<epsilon> A\<^sub>D (ps, fs) \<noteq> {}\<close> if hyp_inv: \<open>inv_dining ps fs\<close>
  apply (subst dining_\<epsilon>)
    apply (insert hyp_inv, unfold inv_dining_def, simp_all add: lphil0_\<epsilon>)
proof(elim conjE, intro conjI impI, goal_cases)
  case 1
  with 1(3)[rule_format, of 0, OF N_pos] show ?case
  proof(elim disjE, goal_cases)
    case 11:1 (* fs ! 0 = 0 *)
    thus ?case
      using 1(3)[rule_format, of 1, OF N_g1] apply(elim disjE) 
        (* fs ! 1 = 0 *)
        apply (subgoal_tac \<open>ps ! 1 = 0\<close>, nonempty_Int_by_common_element \<open>picks 1 1\<close>)
      using N_g1 apply \<epsilon>_sets_simp[3]
          apply (metis atLeastLessThan_iff le_refl less_irrefl_nat, blast, 
          metis less_zeroE linorder_neqE_nat)
        (* fs ! 1 = 1 *)
       apply (cases \<open>ps ! 1 = 1\<close>, nonempty_Int_by_common_element \<open>picks 1 0\<close>) (* ps ! 1 = 1 *)
      using N_g1 apply \<epsilon>_sets_simp[2]
         apply (metis One_nat_def atLeastLessThan_iff diff_self_eq_0 le_refl less_numeral_extra(1) mod_mod_trivial mod_self,
          metis N_pos lessThan_iff mod_less) 
       apply (nonempty_Int_by_common_element \<open>putsdown 1 1\<close>) (* ps ! 1 = 3 *)
      using N_g1 apply \<epsilon>_sets_simp[2]
        apply (metis atLeastLessThan_iff le_refl less_numeral_extra(3) zero_less_diff,
          metis gr0_conv_Suc lessThan_iff)
        (* fs ! 1 = 2 *)
      apply (cases \<open>N = 2\<close>, simp)
      apply (subgoal_tac \<open>ps ! 2 = 2\<close>, nonempty_Int_by_common_element \<open>putsdown 2 1\<close>)
      using N_g1 apply \<epsilon>_sets_simp
      by (metis One_nat_def Suc_lessI atLeastLessThan_iff diff_Suc_1 le_SucI le_numeral_extra(4)
          mod_less n_not_Suc_n numeral_2_eq_2 zero_less_Suc,
          metis One_nat_def Suc_1 Suc_lessI gr0_conv_Suc lessThan_iff
          less_diff_conv mod_less plus_1_eq_Suc,
          metis One_nat_def Suc_1)
  next
    case 12:2 (* fs ! 0 = 1 *)
    thus ?case by linarith
  next
    case 13:3 (* fs ! 0 = 2 *)
    thus ?case 
      apply (subgoal_tac \<open>ps ! 1 = 2\<close>, nonempty_Int_by_common_element \<open>putsdown 1 0\<close>)
      using N_g1 apply \<epsilon>_sets_simp
       apply (metis atLeastLessThan_iff diff_self_eq_0 dvd_1_left le_Suc_eq less_2_cases_iff mod_0 odd_one)
      by (metis "13"(10) N_pos lessThan_iff mod_less n_not_Suc_n numeral_2_eq_2 zero_less_Suc)
  qed
next
  case 2
  from "2"(3, 7, 8, 10) N_g1 have f1: \<open>fs ! 0 \<noteq> 0 \<Longrightarrow> ps ! 1 = 2 \<and> fs ! 0 = 2\<close> by auto
  from 2 show ?case
    apply (cases \<open>fs ! 0 = 0\<close>)
     apply (nonempty_Int_by_common_element \<open>picks 0 0\<close>)
    using N_g1 apply \<epsilon>_sets_simp[2]
    using N_pos apply blast
    apply (nonempty_Int_by_common_element \<open>putsdown 1 0\<close>)
     apply \<epsilon>_sets_simp
     apply (metis N_g1 One_nat_def atLeastLessThan_iff bot_nat_0.not_eq_extremum
        cancel_comm_monoid_add_class.diff_cancel dual_order.refl local.f1 mod_0)
    by (metis N_g1 N_pos One_nat_def lessThan_iff less_irrefl_nat mod_less)
next
  case 3 thus ?case by (nonempty_Int_by_common_element \<open>putsdown 0 0\<close>)
      (\<epsilon>_sets_simp, metis N_pos lessThan_iff zero_less_Suc)
next
  case 4 thus ?case by (nonempty_Int_by_common_element \<open>putsdown 0 (N - 1)\<close>)
      (\<epsilon>_sets_simp, metis N_pos One_nat_def Suc_1 Suc_diff_1 diff_less
        gr0_conv_Suc lessThan_iff mod_self n_not_Suc_n)
next
  case 5 thus ?case using 5(4)[rule_format, of 0] by simp
qed 



subsection \<open>Conclusion\<close>

corollary deadlock_free_DINING: \<open>deadlock_free DINING\<close>
  unfolding DINING_is_dining_P_d dining_P_d_def
  apply (subst deadlock_free_P_d_iff)
  using inv_DINING inv_implies_DF by force






section \<open>Alternative version with only right-handed philosophers
         (in order to show that it's not \<^const>\<open>deadlock_free\<close>)\<close>

subsection \<open>Setup\<close>

definition \<open>RPHILS \<equiv> \<^bold>|\<^bold>|\<^bold>| P \<in># mset (map RPHIL [0..< N]). P\<close>

corollary \<open>N = 3 \<Longrightarrow> RPHILS = (RPHIL 0 ||| RPHIL 1 ||| RPHIL 2)\<close>
  unfolding RPHILS_def by (simp add: eval_nat_numeral upt_rec Sync_assoc)

definition RDINING :: \<open>dining_event process\<close>
  where \<open>RDINING = (FORKS || RPHILS)\<close>


subsection \<open>Normalization\<close>

definition rphils_A :: \<open>(\<sigma>\<^sub>p\<^sub>h\<^sub>i\<^sub>l\<^sub>s, dining_event, unit) A\<^sub>d\<close> (\<open>A\<^sub>R\<^sub>P\<close>) where \<open>A\<^sub>R\<^sub>P \<equiv> \<llangle>\<^sub>d\<Otimes>\<lbrakk>{}\<rbrakk> map A\<^sub>r\<^sub>p [0..< N]\<rrangle>\<close>

definition rphils_P_d:: \<open>\<sigma>\<^sub>p\<^sub>h\<^sub>i\<^sub>l\<^sub>s \<Rightarrow> dining_event process\<close> where \<open>rphils_P_d \<equiv> P\<llangle>A\<^sub>R\<^sub>P\<rrangle>\<^sub>d\<close>

definition rdining_A :: \<open>(\<sigma>\<^sub>p\<^sub>h\<^sub>i\<^sub>l\<^sub>s \<times> \<sigma>\<^sub>f\<^sub>o\<^sub>r\<^sub>k\<^sub>s, dining_event, unit) A\<^sub>d\<close> (\<open>A\<^sub>R\<^sub>D\<close>) where \<open>A\<^sub>R\<^sub>D \<equiv> \<llangle>A\<^sub>R\<^sub>P \<^sub>d\<otimes>\<lbrakk>UNIV\<rbrakk>\<^sub>P\<^sub>a\<^sub>i\<^sub>r A\<^sub>F\<rrangle>\<close>

definition rdining_P_d:: \<open>\<sigma>\<^sub>p\<^sub>h\<^sub>i\<^sub>l\<^sub>s \<times> \<sigma>\<^sub>f\<^sub>o\<^sub>r\<^sub>k\<^sub>s \<Rightarrow> dining_event process\<close> where \<open>rdining_P_d \<equiv> P\<llangle>A\<^sub>R\<^sub>D\<rrangle>\<^sub>d\<close>


subsection \<open>Correspondance between our normalized processes and the previous definitions\<close>

lemma rphils_\<epsilon>: \<open>length ps = N \<Longrightarrow> \<epsilon> A\<^sub>R\<^sub>P ps = (\<Union>i\<in>{0..<N}. \<epsilon> (A\<^sub>r\<^sub>p i) (ps ! i))\<close>
  unfolding rphils_A_def using N_pos
  by (subst \<epsilon>_iterated_combine\<^sub>d_Sync_general_form, (auto split: if_splits)+)

lemma NRPHILS_is_rphils_P_d: \<open>RPHILS = rphils_P_d (replicate N 0)\<close>
  unfolding rphils_P_d_def rphils_A_def RPHILS_def
  apply (subst P_d_compactification_Sync_upt_version)
  by (simp_all add: RPHIL_is_rphil_P_d[unfolded rphil_P_d_def] indep_phils indep_enabl_def)


lemma rdining_\<epsilon>:
  \<open>length ps = N \<Longrightarrow> length fs = N \<Longrightarrow>
   \<epsilon> A\<^sub>R\<^sub>D (ps, fs) = (\<Union>i\<in>{0..<N}. \<epsilon> (A\<^sub>r\<^sub>p i) (ps ! i)) \<inter> (\<Union>i<N. \<epsilon> (A\<^sub>f i) (fs ! i))\<close>
  by (simp add: rdining_A_def \<epsilon>_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync combine_Sync_\<epsilon>_def forks_\<epsilon> rphils_\<epsilon>)

lemma RDINING_is_rdining_P_d: \<open>RDINING = rdining_P_d (replicate N 0, replicate N 0)\<close>
  apply (unfold rdining_P_d_def rdining_A_def)
  apply (subst P_d_combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync[symmetric])
   apply (simp add: indep_enabl_def)
  by (simp add: NFORKS_is_forks_P_d NRPHILS_is_rphils_P_d RDINING_def Sync_commute forks_P_d_def
      rphils_P_d_def)


subsection \<open>Proof that we have a deadlock in the state \<^term>\<open>(replicate N 1, replicate N 1)\<close>\<close>

lemma empty_enabl_replicate1: \<open>\<epsilon> A\<^sub>R\<^sub>D (replicate N 1, replicate N 1) = {}\<close>
  by (subst rdining_\<epsilon>, auto simp add: rphil_\<epsilon> fork_\<epsilon>)

corollary non_dealock_free_rdining: \<open>\<not> deadlock_free (rdining_P_d (replicate N 1, replicate N 1))\<close>
  unfolding rdining_P_d_def
  by (subst P_d_rec, subst empty_enabl_replicate1, simp add: non_deadlock_free_STOP)


subsection \<open>Proof that this state is reachable from our initial state, i.e.
            \<^term>\<open>(replicate N 1, replicate N 1) \<in> \<R>\<^sub>d A\<^sub>R\<^sub>D (replicate N 0, replicate N 0)\<close>\<close>

lemma rdining_\<tau>: \<open>length ps = N \<Longrightarrow> length fs = N \<Longrightarrow> e \<in> \<epsilon> A\<^sub>R\<^sub>D (ps, fs) \<Longrightarrow>
                  \<tau> A\<^sub>R\<^sub>D (ps, fs) e = \<lfloor>(\<lceil>\<tau> A\<^sub>R\<^sub>P ps e\<rceil>,  \<lceil>\<tau> A\<^sub>F fs e\<rceil>)\<rfloor>\<close>
  by (auto simp add: rdining_A_def combine\<^sub>P\<^sub>a\<^sub>i\<^sub>r_Sync_defs \<epsilon>_simps split: if_split_asm)

lemma replicate1_reachable_from_replicate0_prelim:
  \<open>n \<le> N \<Longrightarrow> (replicate n 1 @ replicate (N - n) 0, replicate n 1 @ replicate (N - n) 0) \<in> \<R>\<^sub>d A\<^sub>R\<^sub>D (replicate N 0, replicate N 0)\<close>
proof (induct n, simp add: \<R>\<^sub>d.init)
  case (Suc n)
  have \<open>n \<le> N\<close> by (simp add: Suc.prems Suc_leD)
  define \<sigma>s \<sigma>t where a1: \<open>\<sigma>s \<equiv> replicate    n    (1::nat) @ replicate (N -   n)   0\<close>
    and a2: \<open>\<sigma>t \<equiv> replicate (Suc n) (1::nat) @ replicate (N - Suc n) 0\<close>
  have \<open>length \<sigma>s = N\<close> \<open>length \<sigma>t = N\<close> \<open>length \<sigma>s = length \<sigma>t\<close>
    by (simp_all add: \<open>n \<le> N\<close> a1 a2 Suc.prems)
  have f1: \<open>(\<sigma>s, \<sigma>s) \<in> \<R>\<^sub>d A\<^sub>R\<^sub>D (replicate N 0, replicate N 0)\<close>
    using Suc.hyps(1) a1 Suc.prems Suc_leD by presburger
  have f2: \<open>picks n n \<in> \<epsilon> A\<^sub>R\<^sub>P \<sigma>s\<close> \<open>picks n n \<in> \<epsilon> A\<^sub>F \<sigma>s\<close> \<open>picks n n \<in> \<epsilon> A\<^sub>R\<^sub>D (\<sigma>s, \<sigma>s)\<close>
    by (subst rphils_\<epsilon> forks_\<epsilon>, insert Suc.prems Suc_le_eq Suc_leD a1,
        auto simp add: rdining_\<epsilon> rphil_\<epsilon> fork_\<epsilon> nth_append)+

  have \<open>a \<in> \<epsilon> (A\<^sub>r\<^sub>p i) (\<sigma>s ! i) \<Longrightarrow> i < N \<Longrightarrow> a \<in> \<epsilon> (A\<^sub>r\<^sub>p j) (\<sigma>s ! j) \<Longrightarrow> j < N \<Longrightarrow> j = i\<close> for i j a
    by (metis rphil_phil)
  hence * : \<open>a \<in> \<epsilon> (A\<^sub>r\<^sub>p i) (\<sigma>s ! i) \<Longrightarrow> i < N \<Longrightarrow>
             (THE j. j < N \<and> a \<in> \<epsilon> (map A\<^sub>r\<^sub>p [0..<N] ! j) (\<sigma>s ! j)) = i\<close> for i a by auto

  have \<open>a \<in> \<epsilon> (A\<^sub>f i) (\<sigma>s ! i) \<Longrightarrow> i < N \<Longrightarrow> a \<in> \<epsilon> (A\<^sub>f j) (\<sigma>s ! j) \<Longrightarrow> j < N \<Longrightarrow> j = i\<close> for i j a
    by (metis ev_id\<^sub>f\<^sub>o\<^sub>r\<^sub>kx)
  hence ** : \<open>a \<in> \<epsilon> (A\<^sub>f i) (\<sigma>s ! i) \<Longrightarrow> i < N \<Longrightarrow>
              (THE j. j < N \<and> a \<in> \<epsilon> (map A\<^sub>f [0..<N] ! j) (\<sigma>s ! j)) = i\<close> for i a by auto

  have f3: \<open>\<sigma>t = \<lceil>\<tau> A\<^sub>R\<^sub>P \<sigma>s (picks n n)\<rceil>\<close>
    apply (unfold rphils_A_def, subst \<tau>_iterated_combine\<^sub>d_Sync_general_form_when_indep)
    subgoal by (simp add: \<open>length \<sigma>s = N\<close>)
    subgoal by (simp add: indep_enablI indep_phils(2))
    using N_pos apply (auto simp del: N_pos)
    subgoal by (metis N_g1 N_pos lessThan_iff rphil_phil zero_neq_one)
    subgoal
      apply (subst "*", simp_all)
      apply (auto simp add: \<open>length \<sigma>s = length \<sigma>t\<close> intro!: nth_equalityI)
      apply (auto simp add: a1 a2 nth_Cons nth_append nth_list_update dest: rphil_phil split: if_split_asm nat.split)
      by (simp_all add: rphil_A_def)
    using rphils_\<epsilon> \<open>length \<sigma>s = N\<close> atLeast0LessThan f2(1) by force

  have f4: \<open>\<sigma>t = \<lceil>\<tau> A\<^sub>F \<sigma>s (picks n n)\<rceil>\<close>
    apply (unfold forks_A_def, subst \<tau>_iterated_combine\<^sub>d_Sync_general_form_when_indep)
    subgoal by (simp add: \<open>length \<sigma>s = N\<close>)
    subgoal by (simp add: indep_enabl_def indep_forks)
    using N_pos apply (auto simp del: N_pos)
    subgoal by (metis N_g1 N_pos ev_id\<^sub>f\<^sub>o\<^sub>r\<^sub>kx lessThan_iff zero_neq_one)
    subgoal
      apply (subst "**", simp_all)
      apply (auto simp add: \<open>length \<sigma>s = length \<sigma>t\<close> intro!: nth_equalityI)
      apply (auto simp add: a1 a2 nth_Cons nth_append nth_list_update dest: ev_id\<^sub>f\<^sub>o\<^sub>r\<^sub>kx split: if_split_asm nat.split)
      using N_pos_simps(1) Suc_lessI by (auto simp add: fork_A_def intro: Suc_lessI)
    using forks_\<epsilon> \<open>length \<sigma>s = N\<close> atLeast0LessThan f2(2) by force
  show \<open>(\<sigma>t, \<sigma>t) \<in> \<R>\<^sub>d A\<^sub>R\<^sub>D (replicate N 0, replicate N 0)\<close>
    apply (rule \<R>\<^sub>d.step[OF f1], subst rdining_\<tau>)
    using Suc.prems a1 apply fastforce
     apply (rule f2)
    using f3 f4 by blast
qed


corollary replicate1_reachable_from_replicate0: \<open>(replicate N 1, replicate N 1) \<in> \<R>\<^sub>d A\<^sub>R\<^sub>D (replicate N 0, replicate N 0)\<close>
  by (simp add: replicate1_reachable_from_replicate0_prelim[of N, simplified])


theorem not_deadlock_free_RDINING: \<open>\<not> deadlock_free RDINING\<close>
  apply (subst RDINING_is_rdining_P_d[unfolded rdining_P_d_def])
  apply (subst deadlock_free_P_d_iff)
  using empty_enabl_replicate1 replicate1_reachable_from_replicate0 by blast



end


(*<*)
end
  (*>*)
