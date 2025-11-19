(***********************************************************************************
 * Copyright (c) 2025 Université Paris-Saclay
 *
 * Author: Benoît Ballenghien, Université Paris-Saclay,
           CNRS, ENS Paris-Saclay, LMF
 * Author: Burkhart Wolff, Université Paris-Saclay,
           CNRS, ENS Paris-Saclay, LMF
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

section \<open>Non too Destructiveness of After\<close>

(*<*)
theory After_Operator_Non_Too_Destructive
  imports Process_Restriction_Space
    "HOL-CSP_OpSem.After_Trace_Operator" 
begin
  (*>*)


subsection \<open>Equality\<close>

lemma initials_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k: \<open>(P \<down> n)\<^sup>0 = (if n = 0 then UNIV else P\<^sup>0)\<close>
  by (cases n, solves simp)
    (auto simp add: initials_def T_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k,
      metis append.right_neutral append_eq_conv_conj drop_Nil drop_Suc_Cons)


lemma (in After) restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_After:
  \<open>P after e \<down> n = (if ev e \<in> P\<^sup>0 then (P \<down> Suc n) after e else \<Psi> P e \<down> n)\<close>
proof (split if_split, intro conjI impI)
  show \<open>ev e \<notin> P\<^sup>0 \<Longrightarrow> P after e \<down> n = \<Psi> P e \<down> n\<close> by (simp add: not_initial_After)
next
  assume \<open>ev e \<in> P\<^sup>0\<close>
  show \<open>P after e \<down> n = (P \<down> Suc n) after e\<close> (is \<open>?lhs = ?rhs\<close>)
  proof (subst Process_eq_spec, safe)
    show \<open>t \<in> \<D> ?lhs \<Longrightarrow> t \<in> \<D> ?rhs\<close> for t
      by (elim D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
        (simp_all add: \<open>ev e \<in> P\<^sup>0\<close> After_projs
          initials_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k,
          meson Cons_eq_appendI event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) length_Cons tickFree_Cons_iff)
  next
    show \<open>t \<in> \<D> ?rhs \<Longrightarrow> t \<in> \<D> ?lhs\<close> for t
      by (auto simp add: D_After initials_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<open>ev e \<in> P\<^sup>0\<close>
          D_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k T_After Cons_eq_append_conv)
  next
    show \<open>(t, X) \<in> \<F> ?lhs \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close> for t X
      by (elim F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>kE)
        (simp_all add: \<open>ev e \<in> P\<^sup>0\<close> After_projs
          initials_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k,
          meson Cons_eq_appendI event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(1) length_Cons tickFree_Cons_iff)
  next
    show \<open>(t, X) \<in> \<F> ?rhs \<Longrightarrow> (t, X) \<in> \<F> ?lhs\<close> for t X
      by (auto simp add: F_After initials_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<open>ev e \<in> P\<^sup>0\<close>
          F_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k T_After Cons_eq_append_conv)
  qed
qed

lemma (in AfterExt) restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k:
  \<open>P after\<^sub>\<checkmark> e \<down> n =
   (case e of \<checkmark>(r) \<Rightarrow> \<Omega> P r \<down> n | ev x \<Rightarrow> if e \<in> P\<^sup>0 then (P \<down> Suc n) after\<^sub>\<checkmark> e else \<Psi> P x \<down> n)\<close>
  by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_After split: event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.split )

lemma (in AfterExt) restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e:
  \<open>t \<in> \<T> P \<Longrightarrow> tF t \<Longrightarrow> P after\<^sub>\<T> t \<down> n = (P \<down> (n + length t)) after\<^sub>\<T> t\<close>
proof (induct t arbitrary: n rule: rev_induct)
  show \<open>P after\<^sub>\<T> [] \<down> n = (P \<down> (n + length [])) after\<^sub>\<T> []\<close> for n by simp
next
  fix e t n
  assume   hyp : \<open>t \<in> \<T> P \<Longrightarrow> tF t \<Longrightarrow> P after\<^sub>\<T> t \<down> n = (P \<down> (n + length t)) after\<^sub>\<T> t\<close> for n
  assume prems : \<open>t @ [e] \<in> \<T> P\<close> \<open>tickFree (t @ [e])\<close>
  from prems(2) obtain a where \<open>e = ev a\<close> by (cases e) simp_all
  with initials_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e[OF prems(1)] have \<open>ev a \<in> (P after\<^sub>\<T> t)\<^sup>0\<close> by simp
  from prems is_processT3_TR_append have \<open>t \<in> \<T> P\<close> \<open>tF t\<close> by auto
  from hyp[OF this] have \<open>P after\<^sub>\<T> t \<down> Suc n = (P \<down> (Suc n + length t)) after\<^sub>\<T> t\<close> .
  thus \<open>P after\<^sub>\<T> (t @ [e]) \<down> n = (P \<down> (n + length (t @ [e]))) after\<^sub>\<T> (t @ [e])\<close>
    by (simp add: After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_snoc restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k
        \<open>e = ev a\<close> \<open>ev a \<in> (P after\<^sub>\<T> t)\<^sup>0\<close>)
qed



subsection \<open>Non too Destructiveness\<close>

lemma (in After) non_too_destructive_on_After :
  \<open>non_too_destructive_on (\<lambda>P. P after e) {P. ev e \<in> P\<^sup>0}\<close>
  by (auto intro!: non_too_destructive_onI simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_After)

lemma (in AfterExt) non_too_destructive_on_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>non_too_destructive_on (\<lambda>P. P after\<^sub>\<checkmark> e) {P. e \<in> P\<^sup>0}\<close>
  if \<open>\<And>r. e = \<checkmark>(r) \<Longrightarrow> non_too_destructive_on \<Omega> {P. \<checkmark>(r) \<in> P\<^sup>0}\<close>
proof (intro non_too_destructive_onI, clarify)
  fix P Q n assume * : \<open>P \<down> Suc n = Q \<down> Suc n\<close> \<open>e \<in> P\<^sup>0\<close> \<open>e \<in> Q\<^sup>0\<close>
  show \<open>P after\<^sub>\<checkmark> e \<down> n = Q after\<^sub>\<checkmark> e \<down> n\<close>
  proof (cases e)
    from "*" show \<open>e = ev a \<Longrightarrow> P after\<^sub>\<checkmark> e \<down> n = Q after\<^sub>\<checkmark> e \<down> n\<close> for a
      by (simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
  next
    fix r assume \<open>e = \<checkmark>(r)\<close>
    with "*"(2, 3) have \<open>P \<in> {P. \<checkmark>(r) \<in> P\<^sup>0}\<close> \<open>Q \<in> {P. \<checkmark>(r) \<in> P\<^sup>0}\<close> by auto
    from non_too_destructive_onD[OF that[simplified \<open>e = \<checkmark>(r)\<close>, OF refl] this "*"(1)]
    have \<open>\<Omega> P \<down> n = \<Omega> Q \<down> n\<close> .
    with \<open>e = \<checkmark>(r)\<close> show \<open>P after\<^sub>\<checkmark> e \<down> n = Q after\<^sub>\<checkmark> e \<down> n\<close>
      by (simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k) (metis restriction_fun_def)
  qed
qed



lemma (in After) non_too_destructive_After :
  \<open>non_too_destructive (\<lambda>P. P after e)\<close> if * : \<open>non_too_destructive_on \<Psi> {P. ev e \<notin> P\<^sup>0}\<close>
proof (rule non_too_destructiveI)
  fix P Q :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> and n
  assume \<open>P \<down> Suc n = Q \<down> Suc n\<close>
  hence \<open>ev e \<in> P\<^sup>0 \<and> ev e \<in> Q\<^sup>0 \<or> ev e \<notin> P\<^sup>0 \<and> ev e \<notin> Q\<^sup>0\<close>
    by (metis initials_restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k nat.distinct(1))
  thus \<open>P after e \<down> n = Q after e \<down> n\<close>
  proof (elim disjE conjE)
    show \<open>ev e \<in> P\<^sup>0 \<Longrightarrow> ev e \<in> Q\<^sup>0 \<Longrightarrow> P after e \<down> n = Q after e \<down> n\<close>
      by (simp add: restriction_process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_After \<open>P \<down> Suc n = Q \<down> Suc n\<close>)
  next
    assume \<open>ev e \<notin> P\<^sup>0\<close> \<open>ev e \<notin> Q\<^sup>0\<close>
    hence \<open>P after e = \<Psi> P e\<close> \<open>Q after e = \<Psi> Q e\<close>
      by (simp_all add: not_initial_After)
    from \<open>P \<down> Suc n = Q \<down> Suc n\<close> have \<open>\<Psi> P \<down> n = \<Psi> Q \<down> n\<close>
      by (intro "*"[THEN non_too_destructive_onD, of P Q])
        (simp_all add: \<open>ev e \<notin> P\<^sup>0\<close> \<open>ev e \<notin> Q\<^sup>0\<close>)
    with \<open>P after e = \<Psi> P e\<close> \<open>Q after e = \<Psi> Q e\<close>
    show \<open>P after e \<down> n = Q after e \<down> n\<close> 
      by (metis restriction_fun_def)
  qed
qed


lemma (in AfterExt) non_too_destructive_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k :
  \<open>non_too_destructive (\<lambda>P. P after\<^sub>\<checkmark> e)\<close>
  if * : \<open>\<And>a. e = ev a \<Longrightarrow> non_too_destructive_on \<Psi> {P. ev a \<notin> P\<^sup>0}\<close>
    \<open>\<And>r. e = \<checkmark>(r) \<Longrightarrow> non_too_destructive (\<lambda>P. \<Omega> P r)\<close>
proof (rule non_too_destructiveI)
  show \<open>P after\<^sub>\<checkmark> e \<down> n = Q after\<^sub>\<checkmark> e \<down> n\<close> if \<open>P \<down> Suc n = Q \<down> Suc n\<close> for P Q n
  proof (cases e)
    show \<open>P after\<^sub>\<checkmark> e \<down> n = Q after\<^sub>\<checkmark> e \<down> n\<close> if \<open>e = ev a\<close> for a
      by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def \<open>e = ev a\<close>)
        (fact non_too_destructive_After[OF "*"(1)[simplified \<open>e = ev a\<close>, OF refl],
            THEN non_too_destructiveD, OF \<open>P \<down> Suc n = Q \<down> Suc n\<close>])
  next
    fix r assume \<open>e = \<checkmark>(r)\<close>
    from "*"(2)[unfolded \<open>e = \<checkmark>(r)\<close>, OF refl,
        THEN non_too_destructiveD, OF \<open>P \<down> Suc n = Q \<down> Suc n\<close>]
    have \<open>\<Omega> P r \<down> n = \<Omega> Q r \<down> n\<close> .
    thus \<open>P after\<^sub>\<checkmark> e \<down> n = Q after\<^sub>\<checkmark> e \<down> n\<close>
      by (simp add: After\<^sub>t\<^sub>i\<^sub>c\<^sub>k_def \<open>e = \<checkmark>(r)\<close>)
  qed
qed


lemma (in AfterExt) restriction_shift_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e :
  \<open>restriction_shift (\<lambda>P. P after\<^sub>\<T> t) (- int (length t))\<close>
  if \<open>non_too_destructive \<Psi>\<close> \<open>non_too_destructive \<Omega>\<close>
    \<comment> \<open>We could imagine more precise assumptions, but is it useful?\<close>
proof (induct t)
  case Nil show ?case by (simp add: restriction_shiftI)
next
  case (Cons e t)
  have \<open>non_too_destructive (\<lambda>P. P after\<^sub>\<checkmark> e)\<close>
    by (rule non_too_destructive_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k)
      (simp add: \<open>non_too_destructive \<Psi>\<close>,
        metis non_too_destructive_fun_iff \<open>non_too_destructive \<Omega>\<close>)
  hence * : \<open>restriction_shift (\<lambda>P. P after\<^sub>\<checkmark> e) (- 1)\<close>
    unfolding non_too_destructive_def
      non_too_destructive_on_def restriction_shift_def .
  from restriction_shift_comp_restriction_shift[OF Cons.hyps "*"]
  show ?case by simp
qed


(*<*)
end
  (*>*)