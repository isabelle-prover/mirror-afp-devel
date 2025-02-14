(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff, Lina Ye.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : Step laws
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


section\<open> The Step-Laws \<close>

(*<*)
theory Step_CSP_Laws                                               
  imports Constant_Processes Deterministic_Choice Non_Deterministic_Choice
    Global_Non_Deterministic_Choice Sliding_Choice
    Multi_Deterministic_Prefix_Choice Multi_Non_Deterministic_Prefix_Choice
    Sequential_Composition Synchronization_Product Hiding Renaming
begin 
  (*>*)

text \<open>The step-laws describe the behaviour of the operators wrt. the multi-prefix choice.\<close>

subsection \<open>Deterministic Choice\<close>

lemma Mprefix_Det_Mprefix:
  \<open>(\<box>a \<in> A \<rightarrow> P a) \<box> (\<box>b \<in> B \<rightarrow> Q b) =
   \<box>x \<in> (A \<union> B) \<rightarrow> (if x \<in> A \<inter> B then P x \<sqinter> Q x else if x \<in> A then P x else Q x)\<close>
  (is \<open>?lhs = ?rhs\<close>)
proof (subst Process_eq_spec, safe)
  show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close> for s
    by (cases s) (auto simp add: D_Det D_Ndet D_Mprefix)
next
  show \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ?lhs\<close> for s
    by (auto simp add: D_Det D_Ndet D_Mprefix split: if_split_asm)
next
  show \<open>(s, X) \<in> \<F> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for s X
    by (cases s) (auto simp add: F_Det F_Ndet F_Mprefix)
next
  show \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for s X
    by (cases s) (auto simp add: F_Det F_Ndet F_Mprefix split: if_split_asm)
qed

corollary Mprefix_Un_distrib:
  \<open>\<box>a \<in> (A \<union> B) \<rightarrow> P a = (\<box>a \<in> A \<rightarrow> P a) \<box> (\<box>b \<in> B \<rightarrow> P b)\<close>
  by (simp add: Mprefix_Det_Mprefix) (rule mono_Mprefix_eq, simp)


subsection \<open>Non-Deterministic Choice\<close>

lemma Mprefix_Ndet_Mprefix :
  \<open>(\<box>a \<in> A \<rightarrow> P a) \<sqinter> (\<box>b \<in> B \<rightarrow> Q b) =
   (\<box>a \<in> (A - B) \<rightarrow> P a) \<sqinter> (\<box>b \<in> (B - A) \<rightarrow> Q b) \<box> (\<box>x \<in> (A \<inter> B) \<rightarrow> P x \<sqinter> Q x)\<close>
  (is \<open>?lhs = ?rhs\<close>)
proof (subst Process_eq_spec, safe)
  show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close> and \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ?lhs\<close> for s
    by (auto simp add: D_Ndet D_Mprefix D_Det)
next
  show \<open>(s, X) \<in> \<F> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
    and \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for s X
    by (cases s; auto simp add: F_Ndet F_Det F_Mprefix D_Mprefix D_Ndet T_Ndet)+
qed



subsection \<open>Sliding Choice\<close>

lemma Mprefix_Sliding_Mprefix :
  \<open>(\<box>a\<in> A \<rightarrow> P a) \<rhd> (\<box>b \<in> B \<rightarrow> Q b) =
   (\<box>x \<in> (A \<union> B) \<rightarrow> (if x \<in> A \<inter> B then P x \<sqinter> Q x else if x \<in> A then P x else Q x)) \<sqinter>
   (\<box>b \<in> B \<rightarrow> (if b \<in> A then P b \<sqinter> Q b else Q b))\<close>
  (is \<open>?lhs = ?rhs\<close>)
  \<comment> \<open>It is not so much a ``step law'' as a rewriting.\<close>
proof (subst Process_eq_spec, safe)
  show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close>
    and \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ?lhs\<close> for s
    by (auto simp add: D_Sliding D_Mprefix D_Ndet split: if_split_asm)
next
  show \<open>(s, X) \<in> \<F> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for s X
    by (cases s) (auto simp add: F_Sliding F_Mprefix F_Ndet)
next
  show \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for s X
    by (cases s) (auto simp add: F_Sliding F_Mprefix F_Ndet split: if_split_asm)
qed


corollary Mprefix_Sliding_superset_Mprefix :
  \<open>(\<box>a\<in> A \<rightarrow> P a) \<rhd> (\<box>b \<in> B \<rightarrow> Q b) =
   \<box>b \<in> B \<rightarrow> (if b \<in> A then P b \<sqinter> Q b else Q b)\<close> if \<open>A \<subseteq> B\<close>
  \<comment> \<open>This one (with the additional assumption \<^term>\<open>A \<subseteq> B\<close>) is a ``step law''.\<close>
proof -
  have \<open>(\<box>a\<in> A \<rightarrow> P a) \<rhd> (\<box>b \<in> B \<rightarrow> Q b) =
        (\<box>b \<in> B \<rightarrow> (if b \<in> A \<inter> B then P b \<sqinter> Q b else if b \<in> A then P b else Q b)) \<sqinter>
        (\<box>b \<in> B \<rightarrow> (if b \<in> A then P b \<sqinter> Q b else Q b))\<close>
    by (simp add: Mprefix_Sliding_Mprefix Un_absorb1 \<open>A \<subseteq> B\<close>)
  also have \<open>(\<box>b \<in> B \<rightarrow> (if b \<in> A \<inter> B then P b \<sqinter> Q b else if b \<in> A then P b else Q b)) =
              \<box>b \<in> B \<rightarrow> (if b \<in> A then P b \<sqinter> Q b else Q b)\<close>
    by (rule mono_Mprefix_eq) simp
  finally show \<open>(\<box>a\<in> A \<rightarrow> P a) \<rhd> (\<box>b \<in> B \<rightarrow> Q b) =
                \<box>b \<in> B \<rightarrow> (if b \<in> A then P b \<sqinter> Q b else Q b)\<close> by simp
qed

corollary Mprefix_Sliding_same_set_Mprefix :
  \<open>(\<box>a\<in> A \<rightarrow> P a) \<rhd> (\<box>a \<in> A \<rightarrow> Q a) = \<box>a \<in> A \<rightarrow> P a \<sqinter> Q a\<close>
  by (simp add: Mprefix_Sliding_superset_Mprefix)
    (rule mono_Mprefix_eq, simp)



subsection \<open>Sequential Composition\<close>

lemma Mprefix_Seq: \<open>\<box>a \<in> A \<rightarrow> P a \<^bold>; Q = \<box>a \<in> A \<rightarrow> (P a \<^bold>; Q)\<close>
proof (subst Process_eq_spec_optimized, safe)
  show \<open>s \<in> \<D> (\<box>a \<in> A \<rightarrow> P a \<^bold>; Q) \<Longrightarrow> s \<in> \<D> (\<box>a \<in> A \<rightarrow> (P a \<^bold>; Q))\<close> for s
    by (cases s; simp add: D_Seq D_Mprefix T_Mprefix image_iff)
      (metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.distinct(1) hd_append list.sel(1, 3) tl_append2)
next
  show \<open>s \<in> \<D> (\<box>a\<in>A \<rightarrow> (P a \<^bold>; Q)) \<Longrightarrow> s \<in> \<D> (\<box>a \<in> A \<rightarrow> P a \<^bold>; Q)\<close> for s
    by (cases s; simp add: D_Seq D_Mprefix T_Mprefix image_iff) (metis append_Cons)
next
  show \<open>(s, X) \<in> \<F> (\<box>a\<in>A \<rightarrow> (P a \<^bold>; Q)) \<Longrightarrow> (s, X) \<in> \<F> (\<box>a \<in> A \<rightarrow> P a \<^bold>; Q)\<close> for s X
    apply (cases s; simp add: F_Mprefix T_Mprefix D_Mprefix F_Seq disjoint_iff image_iff)
    by blast (metis Cons_eq_appendI event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1))
next
  assume same_div: \<open>\<D> (\<box>a \<in> A \<rightarrow> P a \<^bold>; Q) = \<D> (\<box>a \<in> A \<rightarrow> (P a \<^bold>; Q))\<close>
  show \<open>(s, X) \<in> \<F> (\<box>a \<in> A \<rightarrow> P a \<^bold>; Q) \<Longrightarrow> (s, X) \<in> \<F> (\<box>a \<in> A \<rightarrow> (P a \<^bold>; Q))\<close> for s X
    apply (simp add: F_Seq, elim disjE exE conjE)
    subgoal by (cases s; simp add: F_Mprefix image_iff F_Seq; blast)
    subgoal by (cases s; simp add: F_Mprefix T_Mprefix F_Seq image_iff)
        (metis append_self_conv2 event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.simps(4) hd_append2 list.sel(1, 3) tl_append_if)
    using same_div D_F D_Seq by blast
qed



subsection \<open>Hiding\<close>

text \<open>We use a context to hide the intermediate results.\<close>

context begin

subsubsection \<open>Two intermediate Results\<close>

private lemma D_Hiding_Mprefix_dir2:
  \<open>s \<in> \<D> (\<box>a \<in> A \<rightarrow> P a \ S)\<close> if \<open>s \<in> \<D> (\<box>a \<in> (A - S) \<rightarrow> (P a \ S))\<close>
proof -
  from that obtain a s'
    where * : \<open>a \<in> A\<close> \<open>a \<notin> S\<close> \<open>s = ev a # s'\<close> \<open>s' \<in> \<D> (P a \ S)\<close>
    by (auto simp add: D_Mprefix)
  from "*"(4) obtain t u 
    where ** : \<open>ftF u\<close> \<open>tF t\<close> \<open>s' = trace_hide t (ev ` S) @ u\<close>
      \<open>t \<in> \<D> (P a) \<or> (\<exists> f. isInfHiddenRun f (P a) S \<and> t \<in> range f)\<close>
    by (simp add: D_Hiding) blast
  from "**"(4) show \<open>s \<in> \<D> (\<box>a \<in> A \<rightarrow> P a \ S)\<close>
  proof (elim disjE)
    assume \<open>t \<in> \<D> (P a)\<close>
    hence \<open>tF (ev a # t) \<and> s = trace_hide (ev a # t) (ev ` S) @ u \<and>
           ev a # t \<in> \<D> (Mprefix A P)\<close>
      by (simp add: "*"(1, 2, 3) "**"(2, 3) image_iff[of \<open>ev a\<close>] D_Mprefix)
    show \<open>s \<in> \<D> (Mprefix A P \ S)\<close>
      unfolding D_Hiding using "**"(1) \<open>?this\<close> by blast
  next
    assume \<open>\<exists>f. isInfHiddenRun f (P a) S \<and> t \<in> range f\<close>
    then obtain f where *** : \<open>isInfHiddenRun f (P a) S\<close> \<open>t \<in> range f\<close> by blast
    hence \<open>tF (ev a # t) \<and> s = trace_hide (ev a # t) (ev ` S) @ u \<and>
           isInfHiddenRun (\<lambda>i. ev a # f i) (Mprefix A P) S \<and> 
           ev a # t \<in> range (\<lambda>i. ev a # f i)\<close>
      by (auto simp add: "*"(1, 2, 3) "**"(2, 3) image_iff[of \<open>ev a\<close>] 
          T_Mprefix strict_mono_Suc_iff)
    show \<open>s \<in> \<D> (Mprefix A P \ S)\<close>
      unfolding D_Hiding using "**"(1) \<open>?this\<close> by blast
  qed
qed


private lemma F_Hiding_Mprefix_dir2: 
  \<open>(s, X) \<in> \<F> (\<box>a \<in> A \<rightarrow> P a \ S)\<close> if \<open>s \<noteq> []\<close> and \<open>(s, X) \<in> \<F> (\<box>a \<in> (A - S) \<rightarrow> (P a \ S))\<close>
proof -
  from that obtain a s'
    where * : \<open>a \<in> A\<close> \<open>a \<notin> S\<close> \<open>s = ev a # s'\<close> \<open>(s', X) \<in> \<F> (P a \ S)\<close>
    by (auto simp add: F_Mprefix)
  from "*"(4) consider \<open>s' \<in> \<D> (P a \ S)\<close>
    | t where \<open>s' = trace_hide t (ev ` S)\<close> \<open>(t, X \<union> ev ` S) \<in> \<F> (P a)\<close>
    by (simp add: F_Hiding D_Hiding) blast
  thus \<open>(s, X) \<in> \<F> (Mprefix A P \ S)\<close>
  proof cases
    assume \<open>s' \<in> \<D> (P a \ S)\<close>
    then obtain t u
      where ** : \<open>ftF u\<close> \<open>tF t\<close> 
        \<open>s' = trace_hide t (ev ` S) @ u\<close> 
        \<open>t \<in> \<D> (P a) \<or> (\<exists> f. isInfHiddenRun f (P a) S \<and> t \<in> range f)\<close>
      by (simp add: D_Hiding) blast
    from "**"(4) show \<open>(s, X) \<in> \<F> (Mprefix A P \ S)\<close>
    proof (elim disjE)
      assume \<open>t \<in> \<D> (P a)\<close>
      hence \<open>tF (ev a # t) \<and> s = trace_hide (ev a # t) (ev ` S) @ u \<and>
             ev a # t \<in> \<D> (Mprefix A P)\<close>
        by (simp add: "*"(1, 2, 3) "**"(2, 3) D_Mprefix image_iff[of \<open>ev a\<close>])
      show \<open>(s, X) \<in> \<F> (Mprefix A P \ S)\<close>
        unfolding F_Hiding using "**"(1) \<open>?this\<close> by blast
    next
      assume \<open>\<exists>f. isInfHiddenRun f (P a) S \<and> t \<in> range f\<close>
      then obtain f where \<open>isInfHiddenRun f (P a) S\<close> \<open>t \<in> range f\<close> by blast
      hence \<open>tF (ev a # t) \<and> s = trace_hide (ev a # t) (ev ` S) @ u \<and>
             (isInfHiddenRun (\<lambda>i. ev a # f i) (Mprefix A P) S \<and> 
             ev a # t \<in> range (\<lambda>i. ev a # f i))\<close>
        by (auto simp add: "*"(1, 2, 3) "**"(2, 3) monotone_on_def T_Mprefix)
      show \<open>(s, X) \<in> \<F> (Mprefix A P \ S)\<close>
        unfolding F_Hiding using "**"(1) \<open>?this\<close> by blast
    qed
  next
    fix t assume ** : \<open>s' = trace_hide t (ev ` S)\<close> \<open>(t, X \<union> ev ` S) \<in> \<F> (P a)\<close>
    have \<open>s = trace_hide (ev a # t) (ev ` S) \<and> (ev a # t, X \<union> ev ` S) \<in> \<F> (Mprefix A P)\<close>
      by (simp add: "*"(1, 2, 3) "**" F_Mprefix image_iff)
    show \<open>(s, X) \<in> \<F> (Mprefix A P \ S)\<close>
      unfolding F_Hiding using \<open>?this\<close> by blast
  qed
qed



subsubsection \<open>\<^const>\<open>Hiding\<close> and \<^const>\<open>Mprefix\<close> for disjoint Sets\<close>

theorem Hiding_Mprefix_disjoint: 
  \<open>\<box>a \<in> A \<rightarrow> P a \ S = \<box>a \<in> A \<rightarrow> (P a \ S)\<close> 
  (is \<open>?lhs = ?rhs\<close>) if disjoint: \<open>A \<inter> S = {}\<close>
proof (subst Process_eq_spec_optimized, safe)
  fix s
  assume \<open>s \<in> \<D> ?lhs\<close>
  then obtain t u 
    where * : \<open>ftF u\<close> \<open>tF t\<close> \<open>s = trace_hide t (ev ` S) @ u\<close>
      \<open>t \<in> \<D> (Mprefix A P) \<or> 
               (\<exists> f. isInfHiddenRun f (Mprefix A P) S \<and> t \<in> range f)\<close>
    by (simp add: D_Hiding) blast
  from "*"(4) show \<open>s \<in> \<D> ?rhs\<close>
  proof (elim disjE)
    assume \<open>t \<in> \<D> (Mprefix A P)\<close>
    then obtain a t' where ** : \<open>a \<in> A\<close> \<open>a \<notin> S\<close> \<open>t = ev a # t'\<close> \<open>t' \<in> \<D> (P a)\<close>
      by (simp add: D_Mprefix) (metis disjoint_iff disjoint)
    have \<open>ftF u \<and> tF t' \<and> trace_hide t' (ev ` S) @ u = trace_hide t' (ev ` S) @ u \<and> t' \<in> \<D> (P a)\<close>
      apply (simp add: "*"(1) "**"(4))
      using "*"(2) "**"(3) tickFree_Cons_iff by blast
    show \<open>s \<in> \<D> ?rhs\<close>
      apply (simp add: D_Mprefix "*"(3) "**"(1, 2, 3) image_iff[of \<open>ev _\<close>] D_Hiding)
      using \<open>?this\<close> by blast
  next
    assume \<open>\<exists>f. isInfHiddenRun f (Mprefix A P) S \<and> t \<in> range f\<close>
    then obtain f where ** : \<open>isInfHiddenRun f (Mprefix A P) S\<close>
      \<open>t \<in> range f\<close> by blast
    from "**"(1) T_Mprefix obtain a
      where *** : \<open>a \<in> A\<close> \<open>a \<notin> S\<close> \<open>f (Suc 0) \<noteq> []\<close> \<open>hd (f (Suc 0)) = ev a\<close>
      by (simp add: T_Mprefix)
        (metis disjoint disjoint_iff list.sel(1) nil_less strict_mono_Suc_iff)
    from "**"(1)[THEN conjunct2, THEN conjunct2, rule_format, of 1]
      "**"(1)[simplified isInfHiddenRun_1] "***"(1, 4) disjoint
    have **** : \<open>f j \<noteq> [] \<and> hd (f j) = ev a\<close> for j
      using "**"(1)[THEN conjunct2, THEN conjunct1, rule_format, of j]
      apply (cases \<open>f 1\<close>; simp add: T_Mprefix "***"(3) split: if_split_asm)
      by (metis Nil_is_append_conv filter.simps(1)
          hd_append2 list.distinct(1) list.sel(1)) blast
    then obtain t' where \<open>t = ev a # t'\<close>
      by (metis "**"(2) list.exhaust_sel rangeE)
    hence \<open>tF t' \<and> trace_hide t' (ev ` S) @ u = trace_hide t' (ev ` S) @ u \<and>
           isInfHiddenRun (\<lambda>i. tl (f i)) (P a) S \<and> t' \<in> range (\<lambda>i. tl (f i))\<close>
      apply (simp, intro conjI)
      using "*"(2) tickFree_Cons_iff apply blast
      apply (meson "**"(1) "****" less_tail strict_mono_Suc_iff)
      using "**"(1) apply (simp add: T_Mprefix "****") 
      apply (metis "****" event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inject(1) list.sel(1, 3))
      apply (subst (1 2) list.collapse[OF "****"[THEN conjunct1], symmetric])
      apply (metis (no_types, lifting) "**"(1) "****" filter.simps(2) list.exhaust_sel list.sel(3))
      by (metis (no_types, lifting) "**"(2) image_iff list.sel(3))
    show \<open>s \<in> \<D> ?rhs\<close>
      apply (simp add: D_Mprefix "*"(3) image_iff[of \<open>ev a\<close>] "***"(1, 2) D_Hiding \<open>t = ev a # t'\<close>)
      using "*"(1) \<open>?this\<close> by blast
  qed
next
  show \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ?lhs\<close> for s
    by (simp add: D_Hiding_Mprefix_dir2 Diff_triv that)
next
  fix s X
  assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
  assume \<open>(s, X) \<in> \<F> ?lhs\<close>
  then consider \<open>s \<in> \<D> ?lhs\<close>
    | t where \<open>s = trace_hide t (ev ` S)\<close> \<open>(t, X \<union> ev ` S) \<in> \<F> (Mprefix A P)\<close>
    by (simp add: F_Hiding D_Hiding) blast
  thus \<open>(s, X) \<in> \<F> ?rhs\<close>
  proof cases
    from same_div D_F show \<open>s \<in> \<D> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> by blast
  next
    fix t assume * : \<open>s = trace_hide t (ev ` S)\<close> \<open>(t, X \<union> ev ` S) \<in> \<F> (Mprefix A P)\<close>
    show \<open>(s, X) \<in> \<F> ?rhs\<close>
    proof (cases \<open>t = []\<close>)
      from "*" show \<open>t = [] \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
        by (auto simp add: F_Mprefix)
    next
      assume \<open>t \<noteq> []\<close>
      with "*"(2) disjoint obtain a t'
        where ** : \<open>a \<in> A\<close> \<open>a \<notin> S\<close> \<open>t = ev a # t'\<close> \<open>(t', X \<union> ev ` S) \<in> \<F> (P a)\<close>
        by (cases t, auto simp add: F_Mprefix)
      show \<open>(s, X) \<in> \<F> ?rhs\<close>
        apply (simp add: F_Mprefix "*"(1) "**"(1, 2, 3) image_iff[of \<open>ev a\<close>])
        by (simp add: F_Hiding, rule disjI1, auto simp add: "**"(4))
    qed
  qed
next
  from disjoint show \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for s X
    apply (cases \<open>s = []\<close>)
    apply (simp add: F_Mprefix F_Hiding disjoint_iff,
        metis event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inject(1) filter.simps(1) imageE)
    by (simp add: Diff_triv F_Hiding_Mprefix_dir2)
qed



subsubsection \<open>\<^const>\<open>Hiding\<close> and \<^const>\<open>Mprefix\<close> for non disjoint Sets\<close>

theorem Hiding_Mprefix_non_disjoint:
  \<comment> \<open>Rework this proof\<close>
  \<open>\<box>a \<in> A \<rightarrow> P a \ S = (\<box>a \<in> (A - S) \<rightarrow> (P a \ S)) \<rhd> (\<sqinter>a \<in> (A \<inter> S). (P a \ S))\<close>
  (is \<open>?lhs = ?rhs\<close>) if non_disjoint: \<open>A \<inter> S \<noteq> {}\<close>
proof (subst Process_eq_spec_optimized, safe)
  fix s
  assume \<open>s \<in> \<D> ?lhs\<close>
  then obtain t u 
    where * : \<open>ftF u\<close> \<open>tF t\<close> \<open>s = trace_hide t (ev ` S) @ u\<close>
      \<open>t \<in> \<D> (Mprefix A P) \<or> (\<exists> f. isInfHiddenRun f (Mprefix A P) S \<and> t \<in> range f)\<close>
    by (simp add: D_Hiding) blast
  from "*"(4) show \<open>s \<in> \<D> ?rhs\<close>
  proof (elim disjE)
    assume \<open>t \<in> \<D> (Mprefix A P)\<close>
    then obtain a t' where ** : \<open>a \<in> A\<close> \<open>t = ev a # t'\<close> \<open>t' \<in> \<D> (P a)\<close>
      by (auto simp add: D_Mprefix) 
    have \<open>tF t' \<and> (if a \<in> S then s else tl s) = trace_hide t' (ev ` S) @ u \<and>
          (t' \<in> \<D> (P a) \<or> (\<exists>f. isInfHiddenRun f (P a) S \<and> t' \<in> range f))\<close>
      using "*"(2) "**"(2, 3) by (auto simp add: "*"(1, 3) "**"(2) image_iff)
    with "*"(1) have *** : \<open>(if a \<in> S then s else tl s) \<in> \<D> (P a \ S)\<close> 
      by (simp add: D_Hiding) blast
    show \<open>s \<in> \<D> ?rhs\<close>
    proof (cases \<open>a \<in> S\<close>)
      assume \<open>a \<in> S\<close>
      hence \<open>a \<in> A \<inter> S\<close> by (simp add: "**"(1))
      with "***" show \<open>s \<in> \<D> ?rhs\<close>
        by (auto simp add: D_Sliding D_GlobalNdet)
    next
      assume \<open>a \<notin> S\<close>
      hence \<open>a \<in> A - S\<close> by (simp add: "**"(1))
      with "***" show \<open>s \<in> \<D> ?rhs\<close>
        by (auto simp add: D_Sliding D_Mprefix "*"(3) "**"(2) image_iff)
    qed
  next
    assume \<open>\<exists> f. isInfHiddenRun f (Mprefix A P) S \<and> t \<in> range f\<close>
    then obtain f  
      where ** : \<open>isInfHiddenRun f (Mprefix A P) S\<close> \<open>t \<in> range f\<close> by blast
    obtain k where \<open>t = f k\<close> using "**"(2) by blast
    show \<open>s \<in> \<D> ?rhs\<close>
    proof (cases \<open>f 0 = []\<close>)
      assume \<open>f 0 = []\<close>
      hence \<open>f 1 \<noteq> []\<close>
        by (metis "**"(1) One_nat_def monotoneD nil_less zero_less_Suc)
      with "**"(1)[THEN conjunct2, THEN conjunct1, rule_format, of 1]
      obtain a where *** : \<open>a \<in> A\<close> \<open>f 1 \<noteq> []\<close> \<open>hd (f 1) = ev a\<close>
        by (auto simp add: T_Mprefix)
      have **** : \<open>0 < j \<Longrightarrow> f j \<noteq> [] \<and> hd (f j) = ev a\<close> for j
      proof (induct j rule: nat_induct_non_zero)
        from "***"(2, 3) show \<open>f 1 \<noteq> [] \<and> hd (f 1) = ev a\<close> by blast
      next
        case (Suc j)
        have \<open>j < Suc j\<close> by simp
        from "**"(1)[THEN conjunct1, THEN strict_monoD, OF this]
        obtain v where \<open>f (Suc j) = f j @ v\<close> by (meson strict_prefixE')
        thus ?case by (simp add: Suc.hyps(2))
      qed
      from "***"(1) have *****: \<open>a \<in> A \<inter> S\<close>
        by simp (metis (no_types, lifting) "**"(1) "***"(2, 3)
            \<open>f 0 = []\<close> empty_filter_conv event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inject(1)
            filter.simps(1) image_iff list.set_sel(1))
      have \<open>(if i = 0 \<and> t = [] then [] else tl (f (Suc i))) \<in> \<T> (P a)\<close> for i
      proof -
        from "**"(1) "****"[of \<open>Suc i\<close>] have \<open>tl (f (Suc i)) \<in> \<T> (P a)\<close>
          by (auto simp add: T_Mprefix)
        thus \<open>(if i = 0 \<and> t = [] then [] else tl (f (Suc i))) \<in> \<T> (P a)\<close> by simp
      qed
      hence ****** :
        \<open>ftF u \<and> tF (tl t) \<and> s = trace_hide (tl t) (ev ` S) @ u \<and>
         isInfHiddenRun (\<lambda>i. if i = 0 \<and> t = [] then [] else tl (f (Suc i))) (P a) S \<and> 
         tl t \<in> range (\<lambda>i. if i = 0 \<and> t = [] then [] else tl (f (Suc i)))\<close>
        apply (intro conjI)
        apply (use "*"(1) in blast)
        apply (metis "*"(2) tickFree_tl)
        apply (metis "*"(3) "**"(1) \<open>f 0 = []\<close> \<open>t = f k\<close> empty_filter_conv
            filter.simps(1) list.sel(2) list.set_sel(2))
        apply (simp add: monotone_on_def,
            metis "**"(1) strict_prefix_simps(1) Suc_less_eq less_tail
            nil_le nless_le not_less_less_Suc_eq strict_monoD)
        apply blast
        apply (simp, metis "**"(1) "****" \<open>f 0 = []\<close> empty_filter_conv
            filter.simps(1) list.set_sel(2) zero_less_Suc)
        by (simp add: image_iff,
            metis Suc_pred \<open>f 0 = []\<close> \<open>t = f k\<close> bot_nat_0.not_eq_extremum)
      have \<open>a \<in> A \<inter> S \<and> s \<in> \<D> (P a \ S)\<close>
        apply (simp add: D_Hiding "*****"[simplified])
        using ****** by blast
      hence \<open>s \<in> \<D> (\<sqinter>a \<in> (A \<inter> S). (P a \ S))\<close> by (simp add: D_GlobalNdet) blast
      thus \<open>s \<in> \<D> ?rhs\<close> by (simp add: D_Sliding)
    next
      assume \<open>f 0 \<noteq> []\<close>
      with "**"(1)[THEN conjunct2, THEN conjunct1, rule_format, of 0]
      obtain a where *** : \<open>a \<in> A\<close> \<open>f 0 \<noteq> []\<close> \<open>hd (f 0) = ev a\<close>
        by (auto simp add: T_Mprefix)
      have **** : \<open>f j \<noteq> [] \<and> hd (f j) = ev a\<close> for j
      proof (induct j)
        from "***"(2, 3) show \<open>f 0 \<noteq> [] \<and> hd (f 0) = ev a\<close> by blast
      next
        case (Suc j)
        have \<open>j < Suc j\<close> by simp
        from "**"(1)[THEN conjunct1, THEN strict_monoD, OF this]
        obtain v where \<open>f (Suc j) = f j @ v\<close> by (meson strict_prefixE')
        thus ?case by (simp add: Suc.hyps(1))
      qed
      show \<open>s \<in> \<D> ?rhs\<close>
      proof (cases \<open>a \<in> S\<close>)
        assume \<open>a \<in> S\<close>
        hence \<open>a \<in> A \<inter> S\<close> by (simp add: "***"(1))
        have \<open>tF (tl t) \<and> s = trace_hide (tl t) (ev ` S) @ u \<and>
              isInfHiddenRun (\<lambda>i. tl (f i)) (P a) S \<and> tl t \<in> range (\<lambda>i. tl (f i))\<close>
          apply (simp add: "*"(3), intro conjI)
          apply (metis "*"(2) tickFree_tl)
          apply (cases t; simp; metis "****" \<open>a \<in> S\<close> \<open>t = f k\<close> image_iff list.sel(1))
          apply (meson "**"(1) "****" less_tail strict_mono_Suc_iff)
          using "**"(1) apply (simp add: T_Mprefix "****")
          apply (metis "****" event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inject(1) list.sel(1, 3))
          apply (metis (no_types, lifting) "**"(1) "****" filter.simps(2) list.exhaust_sel list.sel(3))
          using "**"(2) by blast
        have \<open>s \<in> \<D> (\<sqinter>a \<in> (A \<inter> S). (P a \ S))\<close>
          apply (simp add: D_GlobalNdet D_Hiding)
          using "*"(1) \<open>a \<in> A \<inter> S\<close> \<open>?this\<close> by blast
        thus \<open>s \<in> \<D> ?rhs\<close> by (simp add: D_Sliding)
      next
        assume \<open>a \<notin> S\<close>
        have \<open>tF (tl t) \<and> trace_hide (tl t) (ev ` S) @ u = trace_hide (tl t) (ev ` S) @ u \<and>
              isInfHiddenRun (\<lambda>i. tl (f i)) (P a) S \<and> tl t \<in> range (\<lambda>i. tl (f i))\<close>
          apply (simp add: "*"(3), intro conjI)
          apply (metis "*"(2) tickFree_tl)
          apply (meson "**"(1) "****" less_tail strict_mono_Suc_iff)
          using "**"(1) apply (simp add: T_Mprefix "****")
          apply (metis "****" event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.inject(1) list.sel(1, 3))
          apply (metis (no_types, lifting) "**"(1) "****" filter.simps(2) list.exhaust_sel list.sel(3))
          using "**"(2) by blast
        from \<open>a \<notin> S\<close> have \<open>s \<in> \<D> (\<box>a \<in> (A - S) \<rightarrow> (P a \ S))\<close>
          apply (simp add: D_Mprefix "*"(3) \<open>t = f k\<close>)
          using "***"(1) "****"[of k]
          apply (cases \<open>f k\<close>; simp add: \<open>a \<notin> S\<close> image_iff[of \<open>ev a\<close>] D_Hiding)
          using \<open>?this\<close> by (metis "*"(1) \<open>t = f k\<close> list.sel(3))
        thus \<open>s \<in> \<D> ?rhs\<close> by (simp add: D_Sliding)
      qed
    qed
  qed
next
  fix s
  assume \<open>s \<in> \<D> ?rhs\<close>
  then consider \<open>s \<in> \<D> (\<box>a \<in> (A - S) \<rightarrow> (P a \ S))\<close> 
    | \<open>s \<in> \<D> (\<sqinter>a \<in> (A \<inter> S). (P a \ S))\<close> by (simp add: D_Sliding) blast
  thus \<open>s \<in> \<D> ?lhs\<close>
  proof cases
    show \<open>s \<in> \<D> (\<box>a \<in> (A - S) \<rightarrow> (P a \ S)) \<Longrightarrow> s \<in> \<D> ?lhs\<close>
      by (rule D_Hiding_Mprefix_dir2)
  next
    assume \<open>s \<in> \<D> (\<sqinter>a \<in> (A \<inter> S). (P a \ S))\<close>
    then obtain a where * : \<open>a \<in> A\<close> \<open>a \<in> S\<close> \<open>s \<in> \<D> (P a \ S)\<close>
      by (auto simp add: D_GlobalNdet)
    from "*"(3) obtain t u 
      where ** : \<open>ftF u\<close> \<open>tF t\<close> \<open>s = trace_hide t (ev ` S) @ u\<close>
        \<open>t \<in> \<D> (P a) \<or> (\<exists> f. isInfHiddenRun f (P a) S \<and> t \<in> range f)\<close>
      by (simp add: D_Hiding) blast
    from "**"(4) show \<open>s \<in> \<D> ?lhs\<close>
    proof (elim disjE)
      assume \<open>t \<in> \<D> (P a)\<close>
      hence $ : \<open>tF (ev a # t) \<and> ev a # t \<in> \<D> (Mprefix A P) \<and>
                 s = trace_hide (ev a # t) (ev ` S) @ u\<close>
        by (simp add: "*"(1, 2) "**"(2, 3) D_Mprefix)
      show \<open>s \<in> \<D> ?lhs\<close>
        apply (simp add: D_Hiding)
        using "$" "**"(1) by blast
    next
      assume \<open>\<exists>f. isInfHiddenRun f (P a) S \<and> t \<in> range f\<close>
      then obtain f where \<open>isInfHiddenRun f (P a) S\<close> \<open>t \<in> range f\<close> by blast
      hence $ : \<open>tF (ev a # t) \<and> 
                 s = trace_hide (ev a # t) (ev ` S) @ u \<and>
                 isInfHiddenRun (\<lambda>i. ev a # f i) (Mprefix A P) S \<and> 
                 ev a # t \<in> range (\<lambda>i. ev a # f i)\<close>
        by (auto simp add: "*"(1, 2) "**"(2, 3) monotone_on_def T_Mprefix)
      show \<open>s \<in> \<D> ?lhs\<close>
        apply (simp add: D_Hiding)
        using "$" "**"(1) by blast
    qed
  qed
next
  fix s X
  assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
  assume \<open>(s, X) \<in> \<F> ?lhs\<close>
  then consider \<open>s \<in> \<D> ?lhs\<close>
    | t where \<open>s = trace_hide t (ev ` S)\<close> \<open>(t, X \<union> ev ` S) \<in> \<F> (Mprefix A P)\<close>
    by (simp add: F_Hiding D_Hiding) blast
  thus \<open>(s, X) \<in> \<F> ?rhs\<close>
  proof cases
    from D_F same_div show \<open>s \<in> \<D> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> by blast
  next
    fix t assume * : \<open>s = trace_hide t (ev ` S)\<close> \<open>(t, X \<union> ev ` S) \<in> \<F> (Mprefix A P)\<close>
    from "*"(2) consider \<open>t = []\<close> \<open>(X \<union> ev ` S) \<inter> ev ` A = {}\<close>
      | a t' where \<open>a \<in> A\<close> \<open>t = ev a # t'\<close> \<open>(t', X \<union> ev ` S) \<in> \<F> (P a)\<close>
      by (auto simp add: F_Mprefix)
    thus \<open>(s, X) \<in> \<F> ?rhs\<close>
    proof cases
      show \<open>t = [] \<Longrightarrow> (X \<union> ev ` S) \<inter> ev ` A = {} \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
        using "*"(1) by (auto simp add: F_Sliding F_GlobalNdet)
    next
      fix a t' assume ** : \<open>a \<in> A\<close> \<open>t = ev a # t'\<close> \<open>(t', X \<union> ev ` S) \<in> \<F> (P a)\<close>
      show \<open>(s, X) \<in> \<F> ?rhs\<close>
      proof (cases \<open>a \<in> S\<close>)
        show \<open>a \<in> S \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
          using "*"(1) "**" by (auto simp add: F_Sliding F_GlobalNdet F_Hiding)
      next
        show \<open>a \<notin> S \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
          using "*"(1) "**"(1, 2, 3) by (auto simp add: F_Sliding F_Mprefix F_Hiding)
      qed
    qed
  qed
next
  fix s X
  assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
  assume \<open>(s, X) \<in> \<F> ?rhs\<close>
  then consider \<open>(s, X) \<in> \<F> (\<sqinter>a \<in> (A \<inter> S). (P a \ S))\<close>
    | \<open>s \<noteq> []\<close> \<open>(s, X) \<in> \<F> (\<box>a \<in> (A - S) \<rightarrow> (P a \ S))\<close>
    by (auto simp add: F_Sliding)
  thus \<open>(s, X) \<in> \<F> ?lhs\<close>
  proof cases
    assume \<open>(s, X) \<in> \<F> (\<sqinter>a \<in> (A \<inter> S). (P a \ S))\<close>
    then obtain a where * : \<open>a \<in> A\<close> \<open>a \<in> S\<close> \<open>(s, X) \<in> \<F> (P a \ S)\<close>
      by (simp add: F_GlobalNdet non_disjoint) blast
    from "*"(3) consider \<open>s \<in> \<D> (P a \ S)\<close>
      | t where \<open>s = trace_hide t (ev ` S)\<close> \<open>(t, X \<union> ev ` S) \<in> \<F> (P a)\<close>
      by (simp add: F_Hiding D_Hiding) blast
    thus \<open>(s, X) \<in> \<F> ?lhs\<close>
    proof cases
      assume \<open>s \<in> \<D> (P a \ S)\<close>
      then obtain t u
        where ** : \<open>ftF u\<close> \<open>tF t\<close> \<open>s = trace_hide t (ev ` S) @ u\<close> 
          \<open>t \<in> \<D> (P a) \<or> (\<exists> f. isInfHiddenRun f (P a) S \<and> t \<in> range f)\<close>
        by (simp add: D_Hiding) blast
      from "**"(4) show \<open>(s, X) \<in> \<F> ?lhs\<close>
      proof (elim disjE)
        assume \<open>t \<in> \<D> (P a)\<close>
        hence $ : \<open>tF (ev a # t) \<and> s = trace_hide (ev a # t) (ev ` S) @ u \<and> 
                   ev a # t \<in> \<D> (Mprefix A P)\<close>
          by (simp add: D_Mprefix "*"(1, 2) "**"(2, 3) image_iff[of \<open>ev a\<close>])
        show \<open>(s, X) \<in> \<F> ?lhs\<close>
          apply (simp add: F_Hiding)
          using "$" "**"(1) by blast
      next
        assume \<open>\<exists>f. isInfHiddenRun f (P a) S \<and> t \<in> range f\<close>
        then obtain f where \<open>isInfHiddenRun f (P a) S\<close> \<open>t \<in> range f\<close> by blast
        hence $ : \<open>tF (ev a # t) \<and> s = trace_hide (ev a # t) (ev ` S) @ u \<and>
                   isInfHiddenRun (\<lambda>i. ev a # f i) (Mprefix A P) S \<and> 
                   ev a # t \<in> range (\<lambda>i. ev a # f i)\<close>
          by (simp add: T_Mprefix "*"(1, 2) "**"(2, 3) 
              image_iff[of \<open>ev a\<close>] monotone_on_def) blast
        show \<open>(s, X) \<in> \<F> ?lhs\<close>
          apply (simp add: F_Hiding)
          using "$" "**"(1) by blast
      qed
    next
      fix t assume \<open>s = trace_hide t (ev ` S)\<close> \<open>(t, X \<union> ev ` S) \<in> \<F> (P a)\<close>
      hence \<open>s = trace_hide (ev a # t) (ev ` S) \<and> 
             (ev a # t, X \<union> ev ` S) \<in> \<F> (Mprefix A P)\<close>
        by (simp add: "*"(1, 2) F_Mprefix)
      show \<open>(s, X) \<in> \<F> ?lhs\<close>
        apply (simp add: F_Hiding, rule disjI1)
        using \<open>?this\<close> by blast
    qed
  next
    show \<open>s \<noteq> [] \<Longrightarrow> (s, X) \<in> \<F> (\<box>a \<in> (A - S) \<rightarrow> (P a \ S)) \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
      by (rule F_Hiding_Mprefix_dir2)
  qed
qed

end



subsection \<open>Synchronization\<close>

lemma Mprefix_Sync_Mprefix_bis :
  \<open>Mprefix (A \<union> A') P \<lbrakk>S\<rbrakk> Mprefix (B \<union> B') Q =
     (\<box>a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk> Mprefix (B \<union> B') Q))
   \<box> (\<box>b\<in>B \<rightarrow> (Mprefix (A \<union> A') P \<lbrakk>S\<rbrakk> Q b))
   \<box> (\<box>x\<in>(A' \<inter> B') \<rightarrow> (P x \<lbrakk>S\<rbrakk> Q x))\<close>
  (is \<open>?lhs A A' P B B' Q = ?rhs A A' P B B' Q\<close>) 
  if sets_assms: \<open>A \<inter> S = {}\<close> \<open>A' \<subseteq> S\<close> \<open>B \<inter> S = {}\<close> \<open>B' \<subseteq> S\<close>
  for P Q :: \<open>'a \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof (subst Process_eq_spec_optimized, safe)
  fix s X
  assume \<open>(s, X) \<in> \<F> (?lhs A A' P B B' Q)\<close>
    and same_div : \<open>\<D> (?lhs A A' P B B' Q) = \<D> (?rhs A A' P B B' Q)\<close>
  from this(1) consider (fail) s_P s_Q X_P X_Q
    where \<open>(s_P, X_P) \<in> \<F> (Mprefix (A \<union> A') P)\<close> \<open>(s_Q, X_Q) \<in> \<F> (Mprefix (B \<union> B') Q)\<close>
      \<open>s setinterleaves ((s_P, s_Q), range tick \<union> (ev ` S))\<close>
      \<open>X = (X_P \<union> X_Q) \<inter> (range tick \<union> (ev ` S)) \<union> X_P \<inter> X_Q\<close>
    | \<open>s \<in> \<D> (?lhs A A' P B B' Q)\<close>
    by (simp add: F_Sync D_Sync) blast
  thus \<open>(s, X) \<in> \<F> (?rhs A A' P B B' Q)\<close>
  proof cases
    case fail
    show \<open>(s, X) \<in> \<F> (?rhs A A' P B B' Q)\<close>
    proof (cases \<open>\<exists>r. s = [] \<or> hd s = tick r\<close>)
      case True
      with fail(1, 2, 3) have ** : \<open>s = [] \<and> s_P = [] \<and> s_Q = []\<close>
        by (cases s_P; cases s_Q; force simp add: F_Mprefix subset_iff split: if_split_asm)
      with fail(1, 2, 4) sets_assms(1, 3) show \<open>(s, X) \<in> \<F> (?rhs A A' P B B' Q)\<close>
        by (auto simp add: subset_iff F_Det D_Det T_Det F_Mprefix image_Un)
    next
      case False
      then obtain e where *** : \<open>s \<noteq> []\<close> \<open>hd s = ev e\<close> by (meson event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.exhaust)
      from fail(1, 2, 3) *** sets_assms consider
        \<open>e \<in> A \<and> s_P \<noteq> [] \<and> hd s_P = ev e \<and> (tl s_P, X_P) \<in> \<F> (P e) \<and> 
         tl s setinterleaves ((tl s_P, s_Q), range tick \<union> (ev ` S))\<close> | 
        \<open>e \<in> B \<and> s_Q \<noteq> [] \<and> hd s_Q = ev e \<and> (tl s_Q, X_Q) \<in> \<F> (Q e) \<and> 
         tl s setinterleaves ((s_P, tl s_Q), range tick \<union> (ev ` S))\<close> | 
        \<open>e \<in> A' \<and> e \<in> B' \<and> s_P \<noteq> [] \<and> s_Q \<noteq> [] \<and> hd s_P = ev e \<and> hd s_Q = ev e \<and> (tl s_P, X_P) \<in> \<F> (P e) \<and> 
         (tl s_Q, X_Q) \<in> \<F> (Q e) \<and> tl s setinterleaves ((tl s_P, tl s_Q), range tick \<union> (ev ` S))\<close>
        by (cases s_P; cases s_Q) (simp_all add: F_Mprefix split: if_split_asm, safe, auto)
      thus \<open>(s, X) \<in> \<F> (?rhs A A' P B B' Q)\<close>
        apply cases
        apply (simp_all add: F_Det ***(1))
        apply (rule disjI1, simp add: F_Mprefix ***, simp add: F_Sync)
        apply (rule exI[of _ e], rule exI[of _ \<open>tl s\<close>], simp, intro conjI)
        apply (metis "***"(1) "***"(2) list.exhaust_sel)
        using fail(2, 4) apply blast
        apply (rule disjI2, rule disjI1, simp add: F_Mprefix ***, simp add: F_Sync)
        apply (rule exI[of _ e], rule exI[of _ \<open>tl s\<close>], simp, intro conjI)
        apply (metis "***"(1) "***"(2) list.exhaust_sel)
        using fail(1, 4) apply blast

        apply (rule disjI2, rule disjI2, simp add: F_Mprefix *** F_Sync)
        apply (rule exI[of _ e], rule exI[of _ \<open>tl s\<close>], simp, intro conjI)
        apply (metis "***"(1) "***"(2) list.exhaust_sel)
        using fail(4) by blast
    qed
  next
    show \<open>s \<in> \<D> (?lhs A A' P B B' Q) \<Longrightarrow> (s, X) \<in> \<F> (?rhs A A' P B B' Q)\<close> 
      using same_div D_F by blast
  qed
next

  fix s X
  { fix P Q A A' B B'
    assume assms : \<open>s \<noteq> []\<close> \<open>(s, X) \<in> \<F> (\<box>x \<in> A \<rightarrow> (P x \<lbrakk>S\<rbrakk> Mprefix (B \<union> B') Q))\<close>
      \<open>A \<inter> S = {}\<close> \<open>A' \<subseteq> S\<close> \<open>B \<inter> S = {}\<close> \<open>B' \<subseteq> S\<close>
      and same_div : \<open>\<D> (?lhs A A' P B B' Q) = \<D> (?rhs A A' P B B' Q)\<close>
    from assms(1, 2) obtain e 
      where * : \<open>e \<in> A\<close> \<open>hd s = ev e\<close> \<open>(tl s, X) \<in> \<F> (P e \<lbrakk>S\<rbrakk> Mprefix (B \<union> B') Q)\<close>
      by (auto simp add: F_Mprefix)
    from "*" assms(1) consider (fail) s_P s_Q X_P X_Q
      where \<open>(s_P, X_P) \<in> \<F> (P e)\<close> \<open>(s_Q, X_Q) \<in> \<F> (Mprefix (B \<union> B') Q)\<close>
        \<open>tl s setinterleaves ((s_P, s_Q), range tick \<union> (ev ` S))\<close>
        \<open>X = (X_P \<union> X_Q) \<inter> (range tick \<union> (ev ` S)) \<union> X_P \<inter> X_Q\<close>
      | \<open>s \<in> \<D> (\<box>x \<in> A \<rightarrow> (P x \<lbrakk>S\<rbrakk> Mprefix (B \<union> B') Q))\<close> 
      by (simp add: F_Sync D_Mprefix D_Sync) (metis (no_types) list.collapse)
    hence \<open>(s, X) \<in> \<F> (?lhs A A' P B B' Q)\<close>
    proof cases
      case fail
      show \<open>(s, X) \<in> \<F> (?lhs A A' P B B' Q)\<close>
        apply (simp add: F_Sync, rule disjI1)
        apply (rule exI[of _ \<open>ev e # s_P\<close>], rule exI[of _ s_Q],
            rule exI[of _ X_P], intro conjI)
        apply (simp add: F_Mprefix image_iff "*"(1) fail(1))
        apply (rule exI[of _ X_Q], simp add: fail(2, 4))
        apply (subst list.collapse[OF assms(1), symmetric])
        using "*"(1, 2) fail(3) assms(3) by (cases s_Q) auto 
    next
      assume \<open>s \<in> \<D> (\<box>x\<in>A \<rightarrow> (P x \<lbrakk>S\<rbrakk> Mprefix (B \<union> B') Q))\<close>
      hence \<open>s \<in> \<D> (?lhs A A' P B B' Q)\<close> by (simp add: same_div D_Det)
      thus \<open>(s, X) \<in> \<F> (?lhs A A' P B B' Q)\<close> using D_F by blast
    qed
  } note * = this

  { assume assms : \<open>s \<noteq> []\<close> \<open>(s, X) \<in> \<F> (\<box>x\<in>(A' \<inter> B') \<rightarrow> (P x \<lbrakk>S\<rbrakk> Q x))\<close>
      and same_div : \<open>\<D> (?lhs A A' P B B' Q) = \<D> (?rhs A A' P B B' Q)\<close>
    then obtain e where * : \<open>e \<in> A'\<close> \<open>e \<in> B'\<close> \<open>hd s = ev e\<close> \<open>(tl s, X) \<in> \<F> (P e \<lbrakk>S\<rbrakk> Q e)\<close>
      by (auto simp add: F_Mprefix)
    have inside: \<open>e \<in> S\<close> using "*"(2) that(4) by blast
    from "*" assms(1) consider (fail) s_P s_Q X_P X_Q where
      \<open>(s_P, X_P) \<in> \<F> (P e)\<close> \<open>(s_Q, X_Q) \<in> \<F> (Q e)\<close>
      \<open>tl s setinterleaves ((s_P, s_Q), range tick \<union> (ev ` S))\<close>
      \<open>X = (X_P \<union> X_Q) \<inter> (range tick \<union> (ev ` S)) \<union> X_P \<inter> X_Q\<close>
    | \<open>s \<in> \<D> (\<box>x\<in>(A' \<inter> B') \<rightarrow> (P x \<lbrakk>S\<rbrakk> Q x))\<close>
      by (simp add: F_Sync D_Mprefix D_Sync) (metis (no_types) list.collapse)
    hence \<open>(s, X) \<in> \<F> (?lhs A A' P B B' Q)\<close>
    proof cases
      case fail
      show \<open>(s, X) \<in> \<F> (?lhs A A' P B B' Q)\<close>
        apply (subst list.collapse[OF assms(1), symmetric], simp add: F_Sync "*"(3), rule disjI1)
        apply (rule exI[of _ \<open>ev e # s_P\<close>], rule exI[of _ \<open>ev e # s_Q\<close>])
        apply (rule exI[of _ X_P], intro conjI, simp add: F_Mprefix "*"(1) fail(1))
        by (rule exI[of _ X_Q]) (use fail(3) in \<open>simp add: "*"(2) fail(2, 4) inside F_Mprefix\<close>)
    next
      assume \<open>s \<in> \<D> (\<box>x\<in>(A' \<inter> B') \<rightarrow> (P x \<lbrakk>S\<rbrakk> Q x))\<close>
      hence \<open>s \<in> \<D> (?lhs A A' P B B' Q)\<close> by (simp add: same_div D_Det)
      thus \<open>(s, X) \<in> \<F> (?lhs A A' P B B' Q)\<close> using D_F by blast
    qed
  } note ** = this

  have *** : \<open>X \<inter> ev ` (A' \<inter> B') = {} \<Longrightarrow> X \<inter> ev ` A = {} \<Longrightarrow> X \<inter> ev ` B = {} \<Longrightarrow> 
              ([], X) \<in> \<F> (?lhs A A' P B B' Q)\<close>
    apply (simp add: F_Sync, rule disjI1)
    apply (rule exI[of _ \<open>[]\<close>], rule exI[of _ \<open>[]\<close>], simp add: F_Mprefix)
    apply (rule exI[of _ \<open>X - (ev ` (A' - B'))\<close>], intro conjI, fastforce)
    apply (rule exI[of _ \<open>X - (ev ` (B' - A'))\<close>], intro conjI, fastforce)
    using sets_assms(2, 4) by auto

  assume same_div : \<open>\<D> (?lhs A A' P B B' Q) = \<D> (?rhs A A' P B B' Q)\<close>
  hence same_div_sym : \<open>\<D> (?lhs B B' Q A A' P) = \<D> (?rhs B B' Q A A' P)\<close>
    by (subst Sync_commute, subst Int_commute, subst Det_commute, simp add: Sync_commute)
  show \<open>(s, X) \<in> \<F> (?rhs A A' P B B' Q) \<Longrightarrow> (s, X) \<in> \<F> (?lhs A A' P B B' Q)\<close>
    apply (unfold F_Det, safe, simp_all)
    apply (rule "***"; simp add: F_Mprefix)
    apply (rule "*"; simp add: sets_assms same_div)
    apply (subst (asm) Sync_commute, subst Sync_commute)
    apply (rule "*"; simp add: sets_assms same_div_sym)
    apply (erule "**", assumption, rule same_div)
    apply (simp add: D_Mprefix D_Det)[1]
    by (simp add: T_Mprefix T_Det)
next

  { fix s t u r v and P Q :: \<open>'a \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and A A' B B'
    assume assms : \<open>ftF v\<close> \<open>tF r \<or> v = []\<close> \<open>s = r @ v\<close> 
      \<open>r setinterleaves ((t, u), range tick \<union> (ev ` S))\<close> 
      \<open>t \<in> \<D> (Mprefix (A \<union> A') P)\<close> \<open>u \<in> \<T> (Mprefix (B \<union> B') Q)\<close>
      \<open>A \<inter> S = {}\<close> \<open>A' \<subseteq> S\<close> \<open>B \<inter> S = {}\<close> \<open>B' \<subseteq> S\<close>
    from assms(5) obtain e where * : \<open>t \<noteq> []\<close> \<open>hd t = ev e\<close> \<open>tl t \<in> \<D> (P e)\<close> \<open>e \<in> A \<or> e \<in> A'\<close>
      by (force simp add: D_Mprefix)
    have nonNil: \<open>r \<noteq> [] \<and> s \<noteq> []\<close>
      using *(1) assms(3, 4) empty_setinterleaving by blast
    have \<open>s \<in> \<D> (?rhs A A' P B B' Q)\<close>
    proof (cases \<open>u = []\<close>)
      case True
      hence \<open>hd s = ev e\<close> by (metis "*"(2) EmptyLeftSync setinterleaving_sym assms(3, 4) hd_append nonNil)
      also from "*"(1, 2, 4) setinterleaving_sym assms(4, 8)[simplified True] have \<open>e \<in> A\<close> 
        using emptyLeftNonSync hd_in_set by fastforce
      ultimately show \<open>s \<in> \<D> (?rhs A A' P B B' Q)\<close>
        apply (simp add: D_Det)
        apply (rule disjI1, simp add: D_Mprefix nonNil D_Sync)
        apply (rule exI[of _ e], rule exI[of _ \<open>tl s\<close>], simp, intro conjI)
        apply (metis list.collapse nonNil)
        apply (rule exI[of _ \<open>tl t\<close>], rule exI[of _ \<open>[]\<close>],
            rule exI[of _ \<open>tl r\<close>], rule exI[of _ v])
        apply (auto simp add: assms(1, 3, 6)[simplified True] * nonNil)[1]
        apply (metis assms(2) tickFree_tl)
        using setinterleaving_sym SyncTlEmpty True assms(4) by blast
    next
      case False
      with assms(6) obtain e' where ** : \<open>hd u = ev e'\<close> \<open>tl u \<in> \<T> (Q e')\<close> \<open>e' \<in> B \<or> e' \<in> B'\<close>
        by (auto simp add: T_Mprefix)
      consider \<open>e  \<in> A \<and> hd s = ev e  \<and> tl r setinterleaves ((tl t, u), range tick \<union> ev ` S)\<close> | 
        \<open>e' \<in> B \<and> hd s = ev e' \<and> tl r setinterleaves ((t, tl u), range tick \<union> ev ` S)\<close> | 
        \<open>e = e' \<and> e \<in> A' \<and> e \<in> B' \<and> hd s = ev e \<and> 
                tl r setinterleaves ((tl t, tl u), range tick \<union> ev ` S)\<close>
        using assms(4) 
        apply (subst (asm) list.collapse[OF nonNil[THEN conjunct1], symmetric],
            subst (asm) list.collapse[OF *(1), symmetric, simplified *(2)],
            subst (asm) list.collapse[OF False, symmetric, simplified **(1)])
        apply (simp add: assms(3) nonNil image_iff split: if_split_asm)
        apply (metis (no_types, opaque_lifting) *(4) **(3) Int_iff 
            assms(7, 9) empty_iff list.sel(1, 3))
        apply (metis (no_types, opaque_lifting) *(1, 2) **(3) Int_iff 
            assms(10) inf.order_iff list.exhaust_sel list.sel(1, 3))
        apply (metis (no_types, opaque_lifting) *(1, 2, 4) **(1, 3) Int_iff
            False assms(8, 10) inf.order_iff list.exhaust_sel list.sel(1, 3))
        by (metis (no_types, opaque_lifting) *(4) **(1) False assms(8) 
            list.collapse list.sel(1, 3) subsetD)
      thus \<open>s \<in> \<D> (?rhs A A' P B B' Q)\<close>
        apply cases
        apply (simp_all add: D_Det)
        apply (rule disjI1, simp add: D_Mprefix nonNil D_Sync)
        apply (rule exI[of _ e], rule exI[of _ \<open>tl s\<close>], simp, intro conjI)
        apply (metis list.exhaust_sel nonNil)
        apply (rule exI[of _ \<open>tl t\<close>], rule exI[of _ u],
            rule exI[of _ \<open>tl r\<close>], rule exI[of _ v])
        apply (simp add: assms(1, 3, 6) *(3) nonNil, use assms(2) nonNil tickFree_tl in blast)
        apply (rule disjI2, rule disjI1, simp add: D_Mprefix nonNil D_Sync)
        apply (rule exI[of _ e'], rule exI[of _ \<open>tl s\<close>], simp, intro conjI)
        apply (metis list.exhaust_sel nonNil)
        apply (rule exI[of _ t], rule exI[of _ \<open>tl u\<close>],
            rule exI[of _ \<open>tl r\<close>], rule exI[of _ v])
        apply (metis "*" "**"(2) assms(1, 2, 3) list.exhaust_sel nonNil tickFree_tl tl_append2)
        apply (rule disjI2, rule disjI2, auto simp add: D_Mprefix nonNil image_iff)
        apply (simp add: D_Sync)
        apply (rule exI[of _ e'], rule exI[of _ \<open>tl s\<close>], simp, intro conjI)
        apply (metis list.collapse nonNil)
        apply (rule exI[of _ \<open>tl t\<close>], rule exI[of _ \<open>tl u\<close>],
            rule exI[of _ \<open>tl r\<close>], rule exI[of _ v])
        by (use *(3) **(2) assms(1, 2, 3) nonNil tickFree_tl in \<open>auto simp add: nonNil\<close>)
    qed
  } note * = this

  fix s
  assume \<open>s \<in> \<D> (?lhs A A' P B B' Q)\<close>
  then obtain t u r v
    where ** : \<open>ftF v\<close> \<open>tF r \<or> v = []\<close> \<open>s = r @ v\<close> 
      \<open>r setinterleaves ((t, u), range tick \<union> ev ` S)\<close> 
      \<open>t \<in> \<D> (Mprefix (A \<union> A') P) \<and> u \<in> \<T> (Mprefix (B \<union> B') Q) \<or>
                t \<in> \<D> (Mprefix (B \<union> B') Q) \<and> u \<in> \<T> (Mprefix (A \<union> A') P)\<close> 
    by (simp add: D_Sync) blast
  have same_div : \<open>\<D> (?rhs A A' P B B' Q) = \<D> (?rhs B B' Q A A' P)\<close>
    by (subst Det_commute, subst Int_commute, simp add: Sync_commute)
  from **(5) show \<open>s \<in> \<D> (?rhs A A' P B B' Q)\<close>
    apply (rule disjE)
    by (rule *[OF **(1, 2, 3, 4)]; simp add: sets_assms)
      (subst same_div, rule *[OF **(1, 2, 3, 4)]; simp add: sets_assms)
next

  { fix A A' B B' P Q s
    assume set_assm : \<open>A \<inter> S = {}\<close>
    have \<open>s \<in> \<D> (?lhs A A' P B B' Q)\<close> if \<open>s \<in> \<D> (\<box>x\<in>A \<rightarrow> (P x \<lbrakk>S\<rbrakk> Mprefix (B \<union> B') Q))\<close>
    proof -
      from that obtain e s' where assms: \<open>s = ev e # s'\<close> \<open>e \<in> A\<close> \<open>s' \<in> \<D> (P e \<lbrakk>S\<rbrakk> Mprefix (B \<union> B') Q)\<close>
        by (simp add: D_Mprefix) blast
      from assms(3) obtain t u r v 
        where * : \<open>ftF v\<close> \<open>tF r \<or> v = []\<close> \<open>s' = r @ v\<close>
          \<open>r setinterleaves ((t, u), range tick \<union> ev ` S)\<close>
          \<open>t \<in> \<D> (P e) \<and> u \<in> \<T> (Mprefix (B \<union> B') Q) \<or> 
                   t \<in> \<D> (Mprefix (B \<union> B') Q) \<and> u \<in> \<T> (P e)\<close> by (simp add: D_Sync) blast
      have notin: \<open>e \<notin> S\<close> using assms(2) set_assm by blast
      show \<open>s \<in> \<D> (?lhs A A' P B B' Q)\<close>
        apply (simp add: assms(1) D_Sync)
        using *(5) apply (elim disjE)

        apply (rule exI[of _ \<open>ev e # t\<close>], rule exI[of _ u], 
            rule exI[of _ \<open>ev e # r\<close>], rule exI[of _ v])
        apply (simp add: *(1, 2, 3, 4))
        apply (cases u; simp add: notin image_iff T_Mprefix D_Mprefix)
        using "*"(4) assms(2) apply (blast+)[2]

        apply (rule exI[of _ t], rule exI[of _ \<open>ev e # u\<close>],
            rule exI[of _ \<open>ev e # r\<close>], rule exI[of _ v])
        apply (simp add: *(1, 2, 3, 4))
        apply (cases t; simp add: notin image_iff T_Mprefix D_Mprefix)
        using "*"(4) assms(2) by blast
    qed
  } note * = this

  show \<open>s \<in> \<D> (?rhs A A' P B B' Q) \<Longrightarrow> s \<in> \<D> (?lhs A A' P B B' Q)\<close> for s
    apply (simp add: D_Det)
    apply (erule disjE, rule *, simp_all add: sets_assms(1))
    apply (erule disjE, subst Sync_commute, rule *, simp_all add: sets_assms(3) Sync_commute)
    subgoal
    proof -
      assume \<open>s \<in> \<D> (\<box>x \<in> (A' \<inter> B') \<rightarrow> (P x \<lbrakk>S\<rbrakk> Q x))\<close>
      then obtain e t u r v
        where * : \<open>e \<in> A'\<close> \<open>e \<in> B'\<close> \<open>s \<noteq> []\<close> \<open>hd s = ev e\<close> \<open>ftF v\<close> \<open>tF r \<or> v = []\<close>
          \<open>tl s = r @ v\<close> \<open>r setinterleaves ((t, u), range tick \<union> ev ` S)\<close>
          \<open>t \<in> \<D> (P e) \<and> u \<in> \<T> (Q e) \<or> t \<in> \<D> (Q e) \<and> u \<in> \<T> (P e)\<close> 
        by (simp add: D_Mprefix D_Sync) force
      have inside: \<open>e \<in> S\<close> using *(1) sets_assms(2) by blast
      show \<open>s \<in> \<D> (?lhs A A' P B B' Q)\<close>
        apply (subst list.collapse[OF *(3), symmetric], simp add: D_Sync)
        apply (rule exI[of _ \<open>ev e # t\<close>], rule exI[of _ \<open>ev e # u\<close>],
            rule exI[of _ \<open>ev e # r\<close>], rule exI[of _ v])
        by (simp add: * inside D_Mprefix T_Mprefix image_iff)
    qed .
qed

corollary Mprefix_Sync_Mprefix:
  \<comment>\<open>This version is easier to use.\<close>
  \<open>\<box>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> \<box>b\<in>B \<rightarrow> Q b =
   (\<box>a\<in>(A - S) \<rightarrow> (P a \<lbrakk>S\<rbrakk> \<box>b\<in>B \<rightarrow> Q b)) \<box>
   (\<box>b\<in>(B - S) \<rightarrow> (\<box>a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> Q b)) \<box>
   (\<box>x\<in>(A \<inter> B \<inter> S) \<rightarrow> (P x \<lbrakk>S\<rbrakk> Q x))\<close>
  by (subst Mprefix_Sync_Mprefix_bis[of \<open>A - S\<close> S \<open>A \<inter> S\<close> \<open>B - S\<close> \<open>B \<inter> S\<close>, simplified Un_Diff_Int])
    (simp_all add: Int_commute inf_left_commute)



subsubsection \<open>Renaming\<close>

lemma Renaming_Mprefix:
  \<open>Renaming (\<box>a \<in> A \<rightarrow> P a) f g = 
   \<box>y \<in> f ` A \<rightarrow> \<sqinter>a \<in> {x \<in> A. y = f x}. Renaming (P a) f g\<close> (is \<open>?lhs = ?rhs\<close>)
proof (subst Process_eq_spec_optimized, safe)
  show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close> for s
    by (auto simp add: D_Renaming D_Mprefix D_GlobalNdet)
      (use list.map_sel(2) tickFree_tl in blast)
next
  fix s
  assume \<open>s \<in> \<D> ?rhs\<close>
  then obtain a s' where * : \<open>a \<in> A\<close> \<open>s = map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g (ev a) # s'\<close>
    \<open>s' \<in> \<D> (Renaming (P a) f g)\<close>
    by (auto simp add: D_Mprefix D_GlobalNdet split: if_split_asm)
  from "*"(3) obtain s1 s2 
    where ** : \<open>tF s1\<close> \<open>ftF s2\<close> 
      \<open>s' = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1 @ s2\<close> \<open>s1 \<in> \<D> (P a)\<close>
    by (simp add: D_Renaming) blast
  have *** : \<open>tF (ev a # s1) \<and> 
              s = map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g (ev a) # map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1 @ s2 \<and> ev a # s1 \<in> \<D> (Mprefix A P)\<close>
    by (simp add: D_Mprefix "*"(1, 2) "**"(1, 3, 4))
  show \<open>s \<in> \<D> ?lhs\<close>
    by (simp add: D_Renaming)
      (metis "**"(2) "***" append_Cons list.simps(9))
next
  fix s X
  assume same_div: \<open>\<D> ?lhs = \<D> ?rhs\<close>
  assume \<open>(s, X) \<in> \<F> ?lhs\<close>
  then consider \<open>s \<in> \<D> ?lhs\<close>
    | t where \<open>(t, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (Mprefix A P)\<close> \<open>s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t\<close>
    by (simp add: F_Renaming D_Renaming) blast
  thus \<open>(s, X) \<in> \<F> ?rhs\<close>
  proof cases
    from D_F same_div show \<open>s \<in> \<D> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> by blast
  next
    fix t assume * : \<open>(t, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (Mprefix A P)\<close> 
      \<open>s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t\<close>
    show \<open>(s, X) \<in> \<F> ?rhs\<close>
    proof (cases \<open>t = []\<close>)
      from "*" show \<open>t = [] \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
        by (auto simp add: F_Mprefix disjoint_iff_not_equal)
    next
      assume \<open>t \<noteq> []\<close>
      with "*"(1) obtain a t'
        where ** : \<open>a \<in> A\<close> \<open>t = ev a # t'\<close> \<open>(t', map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (P a)\<close>
        by (auto simp add: F_Mprefix)
      have *** : \<open>s \<noteq> [] \<and> hd s \<in> ev ` f ` A\<close>
        using "*"(2) "**"(1, 2) by simp 
      with "**" have \<open>ev (f a) = hd s \<and> 
                     (tl s, X) \<in> \<F> (\<sqinter>a \<in> {x \<in> A. f a = f x}. Renaming (P a) f g)\<close>
        by (auto simp add: F_GlobalNdet "*"(2) F_Renaming)
      with "***" show \<open>(s, X) \<in> \<F> ?rhs\<close>
        by (simp add: F_Mprefix image_iff) (metis (no_types, lifting) "**"(1) list.collapse)
    qed
  qed
next
  show \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for s X
  proof (cases s)
    show \<open>s = [] \<Longrightarrow> (s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
      by (auto simp add: F_Mprefix F_Renaming)
  next
    fix b s'
    assume \<open>s = b # s'\<close> \<open>(s, X) \<in> \<F> ?rhs\<close>
    then obtain a
      where * : \<open>a \<in> A\<close> \<open>s = (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (ev a) # s'\<close> (* \<open>b = ev (f a)\<close> *)
        \<open>(s', X) \<in> \<F> (\<sqinter>a \<in> {x \<in> A. f a = f x}. Renaming (P a) f g)\<close>
      by (auto simp add: F_Mprefix)
    from "*"(1, 3) obtain a'
      where ** : \<open>a' \<in> A\<close> \<open>f a' = f a\<close> \<open>(s', X) \<in> \<F> (Renaming (P a') f g)\<close>
      by (auto simp add: F_GlobalNdet split: if_split_asm)
    from "**"(3) consider 
      t where \<open>(t, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (P a')\<close> \<open>s' = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t\<close>
    | s1 s2 where \<open>tF s1\<close> \<open>ftF s2\<close>
      \<open>s' = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1 @ s2\<close> \<open>s1 \<in> \<D> (P a')\<close>
      by (simp add: F_Renaming) blast
    thus \<open>(s, X) \<in> \<F> ?lhs\<close>
    proof cases
      fix t assume *** : \<open>(t, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (P a')\<close>
        \<open>s' = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) t\<close>
      have **** : \<open>(ev a' # t, map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g -` X) \<in> \<F> (Mprefix A P) \<and> 
                   s = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) (ev a' # t)\<close>
        by (auto simp add: F_Mprefix "*"(2) "**"(1, 2) "***"(1, 2))
      with "****" show \<open>(s, X) \<in> \<F> ?lhs\<close> by (auto simp add: F_Renaming)
    next
      fix s1 s2 assume *** : \<open>tF s1\<close> \<open>ftF s2\<close> 
        \<open>s' = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1 @ s2\<close> \<open>s1 \<in> \<D> (P a')\<close>
      have \<open>tF (ev a' # s1) \<and> 
            s = map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g (ev a') # map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) s1 @ s2 \<and> 
            ev a' # s1 \<in> \<D> (Mprefix A P)\<close>
        by (auto simp add: "*"(2) "**"(1, 2) "***" D_Mprefix) 
      with "***"(2) show \<open>(s, X) \<in> \<F> ?lhs\<close> by (auto simp add: F_Renaming)
    qed
  qed
qed


(*<*)
end
  (*>*)