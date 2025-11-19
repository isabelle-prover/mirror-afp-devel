(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff, Lina Ye.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : Distributivity of non determinism
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

chapter\<open>Algebraic Rules of CSP\<close>

section\<open> The Non-Deterministic Distributivity \<close>

(*<*)
theory Non_Deterministic_CSP_Distributivity                                               
  imports Constant_Processes Deterministic_Choice Non_Deterministic_Choice
    Global_Non_Deterministic_Choice Sliding_Choice
    Multi_Deterministic_Prefix_Choice Multi_Non_Deterministic_Prefix_Choice
    Sequential_Composition Synchronization_Product Hiding Renaming
begin
  (*>*)

text \<open>CSP operators are distributive over non deterministic choice.\<close>

subsection \<open>Global Distributivity\<close>

lemma Mndetprefix_distrib_GlobalNdet :
  \<open>B \<noteq> {} \<Longrightarrow> (\<sqinter>a \<in> A \<rightarrow> \<sqinter>b \<in> B. P a b) = \<sqinter>b \<in> B. \<sqinter>a \<in> A \<rightarrow> P a b\<close>
  by (simp add: Mndetprefix_GlobalNdet GlobalNdet_sets_commute[of A] write0_GlobalNdet)

lemma Det_distrib_GlobalNdet_left :
  \<open>P \<box> (\<sqinter>a\<in>A. Q a) = (if A = {} then P else \<sqinter>a\<in>A. P \<box> Q a)\<close>
  by (auto simp add: Process_eq_spec Det_projs GlobalNdet_projs
      intro: is_processT8 is_processT6_TR_notin)

corollary Det_distrib_GlobalNdet_right :
  \<open>(\<sqinter>a\<in>A. P a) \<box> Q = (if A = {} then Q else \<sqinter>a\<in>A. P a \<box> Q)\<close>
  by (simp add: Det_commute Det_distrib_GlobalNdet_left)


lemma Sliding_distrib_GlobalNdet_left :
  \<open>P \<rhd> (\<sqinter>a\<in>A. Q a) = (if A = {} then P \<sqinter> STOP else \<sqinter>a\<in>A. P \<rhd> Q a)\<close>
  by (auto simp add: Process_eq_spec GlobalNdet_projs
      Sliding_projs Ndet_projs STOP_projs)

lemma Sliding_distrib_GlobalNdet_right :
  \<open>(\<sqinter>a\<in>A. P a) \<rhd> Q = (if A = {} then Q else \<sqinter>a\<in>A. P a \<rhd> Q)\<close>
  by (auto simp add: Process_eq_spec GlobalNdet_projs Sliding_projs)


lemma Sync_distrib_GlobalNdet_left : 
  \<open>P \<lbrakk>S\<rbrakk> (\<sqinter> a\<in>A. Q a) = (if A = {} then P \<lbrakk>S\<rbrakk> STOP else \<sqinter> a\<in>A. (P \<lbrakk>S\<rbrakk> Q a))\<close>
proof (split if_split, intro conjI impI)
  show \<open>A = {} \<Longrightarrow> P \<lbrakk>S\<rbrakk> (\<sqinter> a\<in>A. Q a) = P \<lbrakk>S\<rbrakk> STOP\<close>
    by (simp add: GlobalNdet.abs_eq STOP.abs_eq)
next
  show \<open>A \<noteq> {} \<Longrightarrow> P \<lbrakk>S\<rbrakk> (\<sqinter> a\<in>A. Q a) = \<sqinter> a\<in>A. (P \<lbrakk>S\<rbrakk> Q a)\<close>
    by (simp add: Process_eq_spec Sync_projs F_GlobalNdet D_GlobalNdet T_GlobalNdet)
      (safe; simp; use front_tickFree_Nil in blast) \<comment> \<open>quicker than auto proof\<close>
qed

corollary Sync_distrib_GlobalNdet_right : 
  \<open>(\<sqinter> a\<in>A. P a) \<lbrakk>S\<rbrakk> Q = (if A = {} then STOP \<lbrakk>S\<rbrakk> Q else \<sqinter> a\<in>A. (P a \<lbrakk>S\<rbrakk> Q))\<close>
  by (simp add: Sync_commute Sync_distrib_GlobalNdet_left)

lemmas Inter_distrib_GlobalNdet_left = Sync_distrib_GlobalNdet_left[where S = \<open>{}\<close>]
  and Par_distrib_GlobalNdet_left = Sync_distrib_GlobalNdet_left[where S = UNIV]
  and Inter_distrib_GlobalNdet_right = Sync_distrib_GlobalNdet_right[where S = \<open>{}\<close>]
  and Par_distrib_GlobalNdet_right = Sync_distrib_GlobalNdet_right[where S = UNIV]


lemma Seq_distrib_GlobalNdet_left :
  \<open>P \<^bold>; \<sqinter> a\<in>A. Q a = (if A = {} then P \<^bold>; STOP else \<sqinter> a\<in>A. (P \<^bold>; Q a))\<close>
  by (simp add: Process_eq_spec GlobalNdet_projs STOP_projs Seq_projs) blast

lemma Seq_distrib_GlobalNdet_right : \<open>(\<sqinter> a\<in>A. P a) \<^bold>; Q = \<sqinter> a\<in>A. (P a \<^bold>; Q)\<close>
  by (simp add: Process_eq_spec GlobalNdet_projs STOP_projs Seq_projs)
    (safe; simp; blast) \<comment> \<open>quicker than auto proof\<close>



lemma Renaming_distrib_GlobalNdet : \<open>Renaming (\<sqinter> a\<in>A. P a) f g = \<sqinter> a\<in>A. Renaming (P a) f g\<close>
  by (simp add: Process_eq_spec Renaming_projs GlobalNdet_projs)
    (safe; simp; blast) \<comment> \<open>quicker than auto proof\<close>


text \<open>The \<^const>\<open>Hiding\<close> operator does not distribute the \<^const>\<open>GlobalNdet\<close> in general.
      We give a finite version derived from the binary version below.\<close>



subsection \<open>Binary Distributivity\<close>

lemma Mndetprefix_distrib_Ndet :
  \<open>(\<sqinter>a \<in> A \<rightarrow> P a \<sqinter> Q a) = (\<sqinter>a \<in> A \<rightarrow> P a) \<sqinter> (\<sqinter>a \<in> A \<rightarrow> Q a)\<close>
  by (simp add: Process_eq_spec Mndetprefix_projs Ndet_projs, safe) auto

lemma Det_distrib_Ndet_left : \<open>P \<box> Q \<sqinter> R = (P \<box> Q) \<sqinter> (P \<box> R)\<close>
  by (auto simp add: Process_eq_spec Det_projs Ndet_projs)

corollary Det_distrib_Ndet_right : \<open>P \<sqinter> Q \<box> R = (P \<box> R) \<sqinter> (Q \<box> R)\<close>
  by (simp add: Det_commute Det_distrib_Ndet_left)


lemma Ndet_distrib_Det_left : \<open>P \<sqinter> (Q \<box> R) = P \<sqinter> Q \<box> P \<sqinter> R\<close>
  by (auto simp add: Process_eq_spec Det_projs Ndet_projs
      is_processT8 is_processT6_TR_notin)

corollary Ndet_distrib_Det_right : \<open>(P \<box> Q) \<sqinter> R = P \<sqinter> R \<box> Q \<sqinter> R\<close>
  by (simp add: Ndet_commute Ndet_distrib_Det_left)


lemma Sliding_distrib_Ndet_left  : \<open>P \<rhd> (Q \<sqinter> R) = (P \<rhd> Q) \<sqinter> (P \<rhd> R)\<close>
  and Sliding_distrib_Ndet_right : \<open>(P \<sqinter> Q) \<rhd> R = (P \<rhd> R) \<sqinter> (Q \<rhd> R)\<close>
  by (auto simp add: Process_eq_spec Ndet_projs Sliding_projs)


lemma Sync_distrib_Ndet_left : \<open>M \<lbrakk>S\<rbrakk> P \<sqinter> Q = (M \<lbrakk>S\<rbrakk> P) \<sqinter> (M \<lbrakk>S\<rbrakk> Q)\<close>
  by (auto simp: Process_eq_spec, simp_all add: Sync_projs Ndet_projs) blast+

corollary Sync_distrib_Ndet_right : \<open>P \<sqinter> Q \<lbrakk>S\<rbrakk> M = (P \<lbrakk>S\<rbrakk> M) \<sqinter> (Q \<lbrakk>S\<rbrakk> M)\<close>
  by (metis Sync_commute Sync_distrib_Ndet_left)


lemma Seq_distrib_Ndet_left : \<open>P \<^bold>; Q \<sqinter> R = (P \<^bold>; Q) \<sqinter> (P \<^bold>; R)\<close>
  by (fact Seq_distrib_GlobalNdet_left[of P \<open>{0 :: nat, 1}\<close>
        \<open>\<lambda>n. if n = 0 then Q else if n = 1 then R else undefined\<close>,
        simplified GlobalNdet_distrib_unit_bis, simplified])


lemma Seq_distrib_Ndet_right : \<open>P \<sqinter> Q \<^bold>; R = (P \<^bold>; R) \<sqinter> (Q \<^bold>; R)\<close>
  by (fact Seq_distrib_GlobalNdet_right[of \<open>{0 :: nat, 1}\<close>
        \<open>\<lambda>n. if n = 0 then P else if n = 1 then Q else undefined\<close> R,
        simplified GlobalNdet_distrib_unit_bis, simplified])



lemma Renaming_distrib_Ndet : \<open>Renaming (P \<sqinter> Q) f g = Renaming P f g \<sqinter> Renaming Q f g\<close>
  by (fact Renaming_distrib_GlobalNdet[of \<open>{0 :: nat, 1}\<close>
        \<open>\<lambda>n. if n = 0 then P else if n = 1 then Q else undefined\<close>,
        simplified GlobalNdet_distrib_unit_bis, simplified])


lemma Hiding_distrib_Ndet : \<open>P \<sqinter> Q \ S = (P \ S) \<sqinter> (Q \ S)\<close>
proof (subst Process_eq_spec_optimized, safe)
  fix s assume \<open>s \<in> \<D> (P \<sqinter> Q \ S)\<close>
  then obtain t u
    where * : \<open>front_tickFree u\<close> \<open>tickFree t\<close> \<open>s = trace_hide t (ev ` S) @ u\<close>
      \<open>t \<in> \<D> (P \<sqinter> Q) \<or> (\<exists>f. isInfHiddenRun f (P \<sqinter> Q) S \<and> t \<in> range f)\<close>
    unfolding D_Hiding by blast
  from "*"(4) show \<open>s \<in> \<D> ((P \ S) \<sqinter> (Q \ S))\<close>
  proof (elim disjE exE)
    from "*"(1, 2) show \<open>t \<in> \<D> (P \<sqinter> Q) \<Longrightarrow> s \<in> \<D> ((P \ S) \<sqinter> (Q \ S))\<close>
      unfolding D_Ndet D_Hiding "*"(3) by blast
  next
    fix f assume \<open>isInfHiddenRun f (P \<sqinter> Q) S \<and> t \<in> range f\<close>
    hence \<open>isInfHiddenRun f P S \<or> isInfHiddenRun f Q S\<close>
      by (simp add: T_Ndet) (meson is_processT3_TR linorder_le_cases strict_mono_less_eq)
    with "*"(1, 2) \<open>isInfHiddenRun f (P \<sqinter> Q) S \<and> t \<in> range f\<close>
    show \<open>s \<in> \<D> ((P \ S) \<sqinter> (Q \ S))\<close> unfolding D_Ndet D_Hiding "*"(3) by blast
  qed
next
  show \<open>s \<in> \<D> ((P \ S) \<sqinter> (Q \ S)) \<Longrightarrow> s \<in> \<D> (P \<sqinter> Q \ S)\<close> for s
    unfolding Ndet_projs D_Hiding by blast
next
  assume same_div : \<open>\<D> (P \<sqinter> Q \ S) = \<D> ((P \ S) \<sqinter> (Q \ S))\<close>
  fix s X assume \<open>(s, X) \<in> \<F> (P \<sqinter> Q \ S)\<close>
  then consider \<open>s \<in> \<D> (P \<sqinter> Q \ S)\<close>
    | t where \<open>s = trace_hide t (ev ` S)\<close> \<open>(t, X \<union> ev ` S) \<in> \<F> (P \<sqinter> Q)\<close>
    by (simp add: F_Hiding D_Hiding) blast
  thus \<open>(s, X) \<in> \<F> ((P \ S) \<sqinter> (Q \ S))\<close>
  proof cases
    from same_div D_F show \<open>s \<in> \<D> (P \<sqinter> Q \ S) \<Longrightarrow> (s, X) \<in> \<F> ((P \ S) \<sqinter> (Q \ S))\<close> by blast
  next
    show \<open>s = trace_hide t (ev ` S) \<Longrightarrow> (t, X \<union> ev ` S) \<in> \<F> (P \<sqinter> Q)
          \<Longrightarrow> (s, X) \<in> \<F> ((P \ S) \<sqinter> (Q \ S))\<close> for t
      by (auto simp add: F_Ndet F_Hiding)
  qed
next
  show \<open>(s, X) \<in> \<F> ((P \ S) \<sqinter> (Q \ S)) \<Longrightarrow> (s, X) \<in> \<F> (P \<sqinter> Q \ S)\<close> for s X
    unfolding Ndet_projs F_Hiding by blast
qed


lemma Hiding_distrib_finite_GlobalNdet :
  \<open>finite A \<Longrightarrow> (\<sqinter>a \<in> A. P a) \ S = \<sqinter>a \<in> A. (P a \ S)\<close>
proof (induct A rule: finite_induct)
  show \<open>(\<sqinter>a \<in> {}. P a) \ S = \<sqinter>a \<in> {}. (P a \ S)\<close>
    by (auto simp add: Process_eq_spec GlobalNdet_projs
        Hiding_seqRun_projs seqRun_def)
next
  fix A a assume \<open>finite A\<close> \<open>a \<notin> A\<close> and hyp : \<open>(\<sqinter>a \<in> A. P a) \ S = \<sqinter>a \<in> A. (P a \ S)\<close>
  show \<open>(\<sqinter>a \<in> insert a A. P a) \ S = \<sqinter>a \<in> insert a A. (P a \ S)\<close> (is \<open>?lhs = ?rhs\<close>)
  proof (cases \<open>A = {}\<close>)
    show \<open>A = {} \<Longrightarrow> ?lhs = ?rhs\<close> by simp
  next
    assume \<open>A \<noteq> {}\<close>
    have \<open>?lhs = P a \<sqinter> (\<sqinter>a \<in> A. P a) \ S\<close>
      by (simp add: GlobalNdet_distrib_unit \<open>A \<noteq> {}\<close> \<open>a \<notin> A\<close>)
    also have \<open>\<dots> = (P a \ S) \<sqinter> ((\<sqinter>a \<in> A. P a) \ S)\<close> by (simp add: Hiding_distrib_Ndet)
    also have \<open>\<dots> = (P a \ S) \<sqinter> (\<sqinter>a \<in> A. (P a \ S))\<close> by (simp add: hyp)
    also have \<open>\<dots> = ?rhs\<close> by (simp add: GlobalNdet_distrib_unit_bis \<open>A \<noteq> {}\<close> \<open>a \<notin> A\<close>)
    finally show \<open>?lhs = ?rhs\<close> .
  qed
qed



text \<open>For the \<^const>\<open>Mprefix\<close> operator, we obviously do not have a
      conventional distributivity: \<^term>\<open>(\<sqinter>)\<close> becomes \<^term>\<open>(\<box>)\<close>.\<close>

lemma Mprefix_distrib_Ndet :
  \<open>(\<box>a \<in> A \<rightarrow> P \<sqinter> Q) = (\<box>a \<in> A \<rightarrow> P) \<box> (\<box>a \<in> A \<rightarrow> Q)\<close> (is \<open>?lhs = ?rhs\<close>)
proof (subst Process_eq_spec, safe)
  show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close>
    and \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ?lhs\<close> for s
    by (auto simp add: D_Det D_Ndet D_Mprefix)
next
  show \<open>(s, X) \<in> \<F> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for s X
    by (cases s) (auto simp add: F_Mprefix F_Det F_Ndet)
next
  show \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for s X
    by (auto simp add: F_Mprefix F_Det F_Ndet)
qed


(*<*)
end
  (*>*)