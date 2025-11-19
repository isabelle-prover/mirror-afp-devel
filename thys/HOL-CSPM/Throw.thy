(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSPM - Architectural operators for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff.
 *
 * This file       : The Throw operator
 *
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

section\<open> The Throw Operator \<close>

(*<*)
theory  Throw
  imports "HOL-CSP.CSP"
begin
  (*>*)


subsection \<open>Definition\<close>

text \<open>The Throw operator allows error handling. Whenever an error (or more generally any 
      event \<^term>\<open>ev e \<in> ev ` A\<close>) occurs in \<^term>\<open>P\<close>, \<^term>\<open>P\<close> is shut down and \<^term>\<open>Q e\<close> is started.

      This operator can somehow be seen as a generalization of sequential composition \<^const>\<open>Seq\<close>:
      \<^term>\<open>P\<close> terminates on any event in \<^term>\<open>ev ` A\<close> rather than \<^const>\<open>tick\<close>
      (however it do not hide these events like \<^const>\<open>Seq\<close> do for \<^const>\<open>tick\<close>,
      but we can use an additional \<^term>\<open>\<lambda>P. (P \ A)\<close>).

      This is a relatively new addition to CSP 
      (see \<^cite>\<open>\<open>p.140\<close> in "Roscoe2010UnderstandingCS"\<close>).\<close>

lift_definition Throw :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a set, 'a \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  is \<open>\<lambda> P A Q. 
  ({(t1, X). (t1, X) \<in> \<F> P \<and> set t1 \<inter> ev ` A = {}} \<union>
   {(t1 @ t2, X) |t1 t2 X. t1 \<in> \<D> P \<and> tF t1 \<and> set t1 \<inter> ev ` A = {} \<and> ftF t2} \<union>
   {(t1 @ ev a # t2, X) |t1 a t2 X.
    t1 @ [ev a] \<in> \<T> P \<and> set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> (t2, X) \<in> \<F> (Q a)},
   {t1 @ t2 |t1 t2. t1 \<in> \<D> P \<and> tF t1 \<and> set t1 \<inter> ev ` A = {} \<and> ftF t2} \<union>
   {t1 @ ev a # t2 |t1 a t2. t1 @ [ev a] \<in> \<T> P \<and> set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> t2 \<in> \<D> (Q a)})\<close>
proof -
  show \<open>?thesis P A Q\<close> (is \<open>is_process (?f, ?d)\<close>) for P A Q
    unfolding is_process_def FAILURES_def DIVERGENCES_def fst_conv snd_conv
  proof (intro conjI allI impI; (elim conjE)?)
    show \<open>([], {}) \<in> ?f\<close> by (simp add: is_processT1)
  next
    show \<open>(s, X) \<in> ?f \<Longrightarrow> ftF s\<close> for s X
      apply (simp, elim disjE exE)
        apply (metis is_processT)
       apply (simp add: front_tickFree_append)
      by (metis F_imp_front_tickFree T_nonTickFree_imp_decomp append1_eq_conv event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.distinct(1)
          front_tickFree_Cons_iff front_tickFree_append tickFree_Cons_iff tickFree_append_iff)
  next
    show \<open>(s @ t, {}) \<in> ?f \<Longrightarrow> (s, {}) \<in> ?f\<close> for s t
    proof (induct t rule: rev_induct)
      case Nil
      thus \<open>(s, {}) \<in> ?f\<close> by simp
    next
      case (snoc b t)
      consider \<open>(s @ t @ [b], {}) \<in> \<F> P\<close> \<open>(set s \<union> set t) \<inter> ev ` A = {}\<close>
        | t1 t2 where \<open>s @ t @ [b] = t1 @ t2\<close> \<open>t1 \<in> \<D> P\<close> \<open>tF t1\<close> \<open>set t1 \<inter> ev ` A = {}\<close> \<open>ftF t2\<close>
        | t1 a t2 where \<open>s @ t @ [b] = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close>
          \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>(t2, {}) \<in> \<F> (Q a)\<close>
        using snoc.prems by auto
      thus \<open>(s, {}) \<in> ?f\<close>
      proof cases
        show \<open>(s @ t @ [b], {}) \<in> \<F> P \<Longrightarrow> (set s \<union> set t) \<inter> ev ` A = {} \<Longrightarrow> (s, {}) \<in> ?f\<close>
          by (drule is_processT3[rule_format]) (simp add: Int_Un_distrib2)
      next
        show \<open>\<lbrakk>s @ t @ [b] = t1 @ t2; t1 \<in> \<D> P; tF t1; set t1 \<inter> ev ` A = {}; ftF t2\<rbrakk>
              \<Longrightarrow> (s, {}) \<in> ?f\<close> for t1 t2
          by (rule snoc.hyps, cases t2 rule: rev_cases, simp_all)
            (metis (no_types, opaque_lifting) Int_Un_distrib2 append_assoc is_processT3
              is_processT8 set_append sup.idem sup_bot.right_neutral,
              metis front_tickFree_dw_closed)
      next
        show \<open>\<lbrakk>s @ t @ [b] = t1 @ ev a # t2; t1 @ [ev a] \<in> \<T> P; set t1 \<inter> ev ` A = {};
               a \<in> A; (t2, {}) \<in> \<F> (Q a)\<rbrakk> \<Longrightarrow> (s, {}) \<in> ?f\<close> for t1 a t2
          by (rule snoc.hyps, cases t2 rule: rev_cases, simp_all)
            (metis T_F is_processT3, metis is_processT3)
      qed
    qed
  next
    show \<open>(s, Y) \<in> ?f \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> (s, X) \<in> ?f\<close> for s X Y
      by simp (metis is_processT4)
  next
    fix s X Y
    assume assms : \<open>(s, X) \<in> ?f\<close> \<open>\<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> ?f\<close>
    consider \<open>(s, X) \<in> \<F> P\<close> \<open>set s \<inter> ev ` A = {}\<close>
      | t1 t2   where \<open>s = t1 @ t2\<close> \<open>t1 \<in> \<D> P\<close> \<open>tF t1\<close> \<open>set t1 \<inter> ev ` A = {}\<close> \<open>ftF t2\<close>
      | t1 a t2 where \<open>s = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close> \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>(t2, X) \<in> \<F> (Q a)\<close>
      using assms(1) by blast
    thus \<open>(s, X \<union> Y) \<in> ?f\<close>
    proof cases
      assume * : \<open>(s, X) \<in> \<F> P\<close> \<open>set s \<inter> ev ` A = {}\<close>
      have \<open>(s @ [c], {}) \<notin> \<F> P\<close> if \<open>c \<in> Y\<close> for c
      proof (cases \<open>c \<in> ev ` A\<close>)
        from "*"(2) assms(2)[rule_format, OF that]
        show \<open>c \<in> ev ` A \<Longrightarrow> (s @ [c], {}) \<notin> \<F> P\<close>
          by auto (metis F_T is_processT1)
      next
        from "*"(2) assms(2)[rule_format, OF that]
        show \<open>c \<notin> ev ` A \<Longrightarrow> (s @ [c], {}) \<notin> \<F> P\<close> by simp
      qed
      with "*"(1) is_processT5 have \<open>(s, X \<union> Y) \<in> \<F> P\<close> by blast
      with "*"(2) show \<open>(s, X \<union> Y) \<in> ?f\<close> by blast
    next
      show \<open>\<lbrakk>s = t1 @ t2; t1 \<in> \<D> P; tF t1; set t1 \<inter> ev ` A = {}; ftF t2\<rbrakk>
            \<Longrightarrow> (s, X \<union> Y) \<in> ?f\<close> for t1 t2 by blast
    next
      fix t1 a t2
      assume * : \<open>s = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close> 
        \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>(t2, X) \<in> \<F> (Q a)\<close>
      have \<open>(t2 @ [c], {}) \<notin> \<F> (Q a)\<close> if \<open>c \<in> Y\<close> for c
        using assms(2)[rule_format, OF that, simplified, THEN conjunct2,
            THEN conjunct2, rule_format, of a t1 \<open>t2 @ [c]\<close>]
        by (simp add: "*"(1, 2, 3, 4))
      with "*"(5) is_processT5 have ** : \<open>(t2, X \<union> Y) \<in> \<F> (Q a)\<close> by blast
      show \<open>(s, X \<union> Y) \<in> ?f\<close>
        using "*"(1, 2, 3, 4) "**" by blast
    qed
  next
    have * : \<open>\<And>s t1 a t2 r. s @ [\<checkmark>(r)] = t1 @ ev a # t2 \<Longrightarrow> \<exists>t2'. t2 = t2' @ [\<checkmark>(r)]\<close>
      by (simp add: snoc_eq_iff_butlast split: if_split_asm)
        (metis append_butlast_last_id)
    show \<open>(s @ [\<checkmark>(r)], {}) \<in> ?f \<Longrightarrow> (s, X - {\<checkmark>(r)}) \<in> ?f\<close> for s r X
      apply (simp, elim disjE exE conjE)
        apply (solves \<open>simp add: is_processT6\<close>)
       apply (metis append1_eq_conv append_assoc front_tickFree_dw_closed
          nonTickFree_n_frontTickFree non_tickFree_tick tickFree_append_iff)
      by (frule "*", elim exE, simp, metis is_processT6)
  next
    show \<open>\<lbrakk>s \<in> ?d; tF s; ftF t\<rbrakk> \<Longrightarrow> s @ t \<in> ?d\<close> for s t
      by (simp, elim disjE) 
        (meson append_assoc front_tickFree_append tickFree_append_iff,
          use append_self_conv2 is_processT7 tickFree_append_iff in fastforce)
  next
    show \<open>s \<in> ?d \<Longrightarrow> (s, X) \<in> ?f\<close> for s X
      by simp (metis is_processT8)     
  next
    show \<open>s @ [\<checkmark>(r)] \<in> ?d \<Longrightarrow> s \<in> ?d\<close> for s r
      by (simp, elim disjE)
        (metis butlast_append butlast_snoc front_tickFree_iff_tickFree_butlast
          non_tickFree_tick tickFree_Nil tickFree_append_iff tickFree_imp_front_tickFree,
          metis (no_types, lifting) append_butlast_last_id butlast.simps(2) butlast_append
          butlast_snoc event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.distinct(1) is_processT9 last.simps last_appendR list.distinct(1))
  qed
qed


text \<open>We add some syntactic sugar.\<close>

syntax "_Throw" :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, pttrn, 'a set, 'a \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  (\<open>((_) \<Theta> (_\<in>_)./ (_))\<close> [78,78,78,77] 77)
syntax_consts "_Throw" \<rightleftharpoons> Throw
translations "P \<Theta> a \<in> A. Q" \<rightleftharpoons> "CONST Throw P A (\<lambda>a. Q)"

(* abbreviation Throw_without_free_var ::
  \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a set, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (\<open>((_) \<Theta> (_)/ (_))\<close> [73, 0, 73] 72)
  where \<open>P \<Theta> A Q \<equiv> P \<Theta> a \<in> A. Q\<close>

text \<open>Now we can write @{term [eta_contract = false] \<open>P \<Theta> a \<in> A. Q a\<close>}, and when
      we do not want \<^term>\<open>Q\<close> to be parameterized we can just write \<^term>\<open>P \<Theta> A Q\<close>.\<close>

lemma \<open>P \<Theta> a \<in> A. Q = P \<Theta> A Q\<close> by (fact refl) *)



subsection \<open>Projections\<close>

lemma F_Throw:
  \<open>\<F> (P \<Theta> a \<in> A. Q a) =
   {(t1, X). (t1, X) \<in> \<F> P \<and> set t1 \<inter> ev ` A = {}} \<union>
   {(t1 @ t2, X) |t1 t2 X. t1 \<in> \<D> P \<and> tF t1 \<and> set t1 \<inter> ev ` A = {} \<and> ftF t2} \<union>
   {(t1 @ ev a # t2, X) |t1 a t2 X.
    t1 @ [ev a] \<in> \<T> P \<and> set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> (t2, X) \<in> \<F> (Q a)}\<close>
  by (simp add: Failures.rep_eq FAILURES_def Throw.rep_eq)


lemma D_Throw:
  \<open>\<D> (P \<Theta> a \<in> A. Q a) =
   {t1 @ t2 |t1 t2. t1 \<in> \<D> P \<and> tF t1 \<and> set t1 \<inter> ev ` A = {} \<and> ftF t2} \<union>
   {t1 @ ev a # t2 |t1 a t2. t1 @ [ev a] \<in> \<T> P \<and> set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> t2 \<in> \<D> (Q a)}\<close>
  by (simp add: Divergences.rep_eq DIVERGENCES_def Throw.rep_eq)


lemma T_Throw:
  \<open>\<T> (P \<Theta> a \<in> A. Q a) =
   {t1 \<in> \<T> P. set t1 \<inter> ev ` A = {}} \<union>
   {t1 @ t2 |t1 t2. t1 \<in> \<D> P \<and> tF t1 \<and> set t1 \<inter> ev ` A = {} \<and> ftF t2} \<union>
   {t1 @ ev a # t2 |t1 a t2. t1 @ [ev a] \<in> \<T> P \<and> set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> t2 \<in> \<T> (Q a)}\<close>
  by (auto simp add: Traces.rep_eq TRACES_def Failures.rep_eq[symmetric] F_Throw) blast+

lemmas Throw_projs = F_Throw D_Throw T_Throw


lemma Throw_T_third_clause_breaker :
  \<open>\<lbrakk>set t \<inter> S = {}; set t' \<inter> S = {}; e \<in> S; e' \<in> S\<rbrakk> \<Longrightarrow>
   t @ e # u = t' @ e' # u' \<longleftrightarrow> t = t' \<and> e = e' \<and> u = u'\<close>
proof (induct t arbitrary: t')
  case Nil thus ?case
    by (metis append_Nil disjoint_iff hd_append2 list.sel(1, 3) list.set_sel(1))
next
  case (Cons a t)
  show ?case
  proof (rule iffI)
    assume \<open>(a # t) @ e # u = t' @ e' # u'\<close>
    then obtain t'' where \<open>t' = a # t''\<close>
      by (metis Cons.prems(1, 4) append_Cons append_Nil disjoint_iff
          list.exhaust_sel list.sel(1) list.set_intros(1))
    with Cons.hyps Cons.prems \<open>(a # t) @ e # u = t' @ e' # u'\<close>
    show \<open>a # t = t' \<and> e = e' \<and> u = u'\<close> by auto
  next
    show \<open>a # t = t' \<and> e = e' \<and> u = u' \<Longrightarrow> (a # t) @ e # u = t' @ e' # u'\<close> by simp
  qed
qed



subsection \<open>Monotony\<close>

(* TODO: move this and use it somewhere else ? *)
lemma min_elems_Un_subset:
  \<open>min_elems (A \<union> B) \<subseteq> min_elems A \<union> (min_elems B - A)\<close>
  by (auto simp add: min_elems_def subset_iff)

lemma mono_Throw[simp] : \<open>P \<Theta> a \<in> A. Q a \<sqsubseteq> P' \<Theta> a \<in> A. Q' a\<close> 
  if \<open>P \<sqsubseteq> P'\<close> and \<open>\<And>a. a \<in> A \<Longrightarrow> a \<in> \<alpha>(P) \<Longrightarrow> Q a \<sqsubseteq> Q' a\<close>
proof (unfold le_approx_def Refusals_after_def, safe)
  from le_approx1[OF that(1)] le_approx_lemma_T[OF that(1)] 
    le_approx1[OF that(2)[rule_format]] 
  show \<open>s \<in> \<D> (P' \<Theta> a \<in> A. Q' a) \<Longrightarrow> s \<in> \<D> (P \<Theta> a \<in> A. Q a)\<close> for s 
    by (simp add: D_Throw subset_iff)
      (metis events_of_memI in_set_conv_decomp)
next
  fix s X
  assume assms : \<open>s \<notin> \<D> (P \<Theta> a \<in> A. Q a)\<close> \<open>(s, X) \<in> \<F> (P \<Theta> a \<in> A. Q a)\<close>
  from assms(2) consider \<open>(s, X) \<in> \<F> P\<close> \<open>set s \<inter> ev ` A = {}\<close>
    | t1 t2   where \<open>s = t1 @ t2\<close> \<open>t1 \<in> \<D> P\<close> \<open>tF t1\<close> \<open>set t1 \<inter> ev ` A = {}\<close> \<open>ftF t2\<close>
    | t1 a t2 where \<open>s = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close> \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>(t2, X) \<in> \<F> (Q a)\<close>
    by (simp add: F_Throw) blast
  thus \<open>(s, X) \<in> \<F> (P' \<Theta> a \<in> A. Q' a)\<close>
  proof cases
    assume * : \<open>(s, X) \<in> \<F> P\<close> \<open>set s \<inter> ev ` A = {}\<close>
    from assms(1)[simplified D_Throw, simplified, THEN conjunct1, rule_format, of s]
      assms(1)[simplified D_Throw, simplified, THEN conjunct1, rule_format, of \<open>butlast s\<close>]
    have ** : \<open>s \<notin> \<D> P\<close> 
      using "*"(2) apply (cases \<open>tF s\<close>, auto simp add: disjoint_iff)
      by (metis "*"(1) D_imp_front_tickFree F_T T_nonTickFree_imp_decomp butlast_snoc
          front_tickFree_append_iff in_set_butlastD is_processT9 list.distinct(1))
    show \<open>(s, X) \<in> \<F> P \<Longrightarrow> set s \<inter> ev ` A = {} \<Longrightarrow> (s, X) \<in> \<F> (Throw P' A Q')\<close>
      by (simp add: F_Throw le_approx2[OF that(1) "**"])
  next
    from assms(1) show \<open>\<lbrakk>s = t1 @ t2; t1 \<in> \<D> P; tF t1; set t1 \<inter> ev ` A = {}; ftF t2\<rbrakk>
                        \<Longrightarrow> (s, X) \<in> \<F> (Throw P' A Q')\<close> for t1 t2
      by (simp add: F_Throw D_Throw)
  next
    fix t1 a t2 assume * : \<open>s = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close> 
      \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>(t2, X) \<in> \<F> (Q a)\<close>
    from "*"(2) have ** : \<open>tF t1\<close> by (simp add: append_T_imp_tickFree)
    have *** : \<open>(t2, X) \<in> \<F> (Q' a)\<close>
      using assms(1)[simplified D_Throw, simplified, THEN conjunct2, rule_format, OF "*"(4, 3, 2, 1)]
      by (metis "*"(2, 4, 5) events_of_memI last_in_set le_approx2 snoc_eq_iff_butlast that(2))
    have **** : \<open>t1 \<notin> \<D> P\<close>
      apply (rule ccontr, simp, 
          drule assms(1)[simplified D_Throw, simplified, THEN conjunct1, rule_format,
            OF "*"(3) "**", of \<open>ev a # t2\<close>, simplified "*"(1), simplified])
      by (metis "*"(1) F_imp_front_tickFree assms(2) front_tickFree_append_iff list.discI)
    show \<open>(s, X) \<in> \<F> (Throw P' A Q')\<close>
      by (simp add: F_Throw D_Throw "*"(1))
        (metis "*"(2, 3, 4) "***" "****" T_F_spec le_approx2 min_elems6 that(1))
  qed
next
  from le_approx1[OF that(1)] le_approx2[OF that(1)] le_approx2T[OF that(1)]
    le_approx2[OF that(2)[rule_format]]
  show \<open>s \<notin> \<D> (P \<Theta> a \<in> A. Q a) \<Longrightarrow> (s, X) \<in> \<F> (P' \<Theta> a \<in> A. Q' a)
        \<Longrightarrow> (s, X) \<in> \<F> (P \<Theta> a \<in> A. Q a)\<close> for s X
    by (simp add: F_Throw D_Throw subset_eq, safe, simp_all)
      (metis is_processT8, (metis D_T events_of_memI in_set_conv_decomp)+)
next
  define S_left 
    where \<open>S_left \<equiv> {t1 @ t2 |t1 t2. t1 \<in> \<D> P \<and> tF t1 \<and> 
                     set t1 \<inter> ev ` A = {} \<and> ftF t2}\<close>
  define S_right 
    where \<open>S_right \<equiv> {t1 @ ev a # t2 |t1 a t2. t1 @ [ev a] \<in> \<T> P \<and>
                      set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> t2 \<in> \<D> (Q a)}\<close>

  have * : \<open>min_elems (\<D> (P \<Theta> a \<in> A. Q a)) \<subseteq> min_elems S_left \<union> (min_elems S_right - S_left)\<close>
    unfolding S_left_def S_right_def 
    by (simp add: D_Throw min_elems_Un_subset)
  have ** : \<open>min_elems S_left = {t1 \<in> min_elems (\<D> P). set t1 \<inter> ev ` A = {}}\<close>
    unfolding S_left_def min_elems_def less_list_def less_eq_list_def prefix_def
    apply (simp, safe)
        apply (solves \<open>meson is_processT7\<close>)
       apply (metis (no_types, lifting) append.right_neutral front_tickFree_Nil front_tickFree_append
        front_tickFree_nonempty_append_imp inf_bot_right inf_sup_absorb inf_sup_aci(2) set_append)
      apply (metis Int_iff Un_iff append.right_neutral front_tickFree_Nil image_eqI set_append)
     apply (metis D_T prefixI same_prefix_nil T_nonTickFree_imp_decomp append.right_neutral front_tickFree_Nil is_processT9 list.distinct(1)) 
    by (metis Nil_is_append_conv append_eq_appendI self_append_conv) 

  { fix t1 a t2
    assume assms : \<open>t1 @ [ev a] \<in> \<T> P\<close> \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close>
      \<open>t2 \<in> (\<D> (Q a))\<close> \<open>t1 @ ev a # t2 \<in> min_elems S_right\<close> \<open>t1 @ ev a # t2 \<notin> S_left\<close>
    have \<open>t2 \<in> min_elems (\<D> (Q a))\<close> 
      \<open>t1 @ [ev a] \<in> \<D> P \<Longrightarrow> t1 @ [ev a] \<in> min_elems (\<D> P)\<close>
    proof (all \<open>rule ccontr\<close>)
      assume \<open>t2 \<notin> min_elems (\<D> (Q a))\<close>
      with assms(4) obtain t2' where \<open>t2' < t2 \<close> \<open>t2' \<in> \<D> (Q a)\<close> 
        unfolding min_elems_def by blast
      hence \<open>t1 @ ev a # t2' \<in> S_right\<close> \<open>t1 @ ev a # t2' < t1 @ ev a # t2\<close> 
        unfolding S_right_def using assms(1, 2, 3) by auto
      with assms(5) min_elems_no nless_le show False by blast
    next
      assume \<open>t1 @ [ev a] \<in> \<D> P\<close> \<open>t1 @ [ev a] \<notin> min_elems (\<D> P)\<close>
      hence \<open>t1 \<in> \<D> P\<close> using min_elems1 by blast
      with \<open>t1 @ [ev a] \<in> \<D> P\<close> have \<open>t1 @ ev a # t2 \<in> S_left\<close>
        apply (simp add: S_left_def)
        by (metis D_imp_front_tickFree T_nonTickFree_imp_decomp append1_eq_conv assms(1)
            assms(2, 4) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.distinct(1) front_tickFree_Cons_iff tickFree_Cons_iff tickFree_append_iff)
      with assms(6) show False by simp
    qed
  } note *** = this
  have **** : \<open>min_elems S_right - S_left \<subseteq> 
               {t1 @ ev a # t2 |t1 a t2. t1 @ [ev a] \<in> \<T> P - \<D> P \<and>
                set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> t2 \<in> min_elems (\<D> (Q a))} \<union>
               {t1 @ ev a # t2 |t1 a t2. t1 @ [ev a] \<in> min_elems (\<D> P) \<and>
                set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> t2 \<in> min_elems (\<D> (Q a))}\<close>
    apply (intro subsetI, simp, elim conjE)
    apply (frule set_mp[OF min_elems_le_self], subst (asm) (2) S_right_def)
    using "***" by fast

  fix s
  assume assm: \<open>s \<in> min_elems (\<D> (P \<Theta> a \<in> A. Q a))\<close>
  from set_mp[OF "*", OF this] 
  consider \<open>s \<in> min_elems (\<D> P)\<close> \<open>set s \<inter> ev ` A = {}\<close>
    | t1 a t2 where \<open>s = t1 @ ev a # t2\<close> \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>t2 \<in> min_elems (\<D> (Q a))\<close>
      \<open>t1 @ [ev a] \<in> min_elems (\<D> P) \<or> t1 @ [ev a] \<in> \<T> P \<and> t1 @ [ev a] \<notin> \<D> P\<close>
    using "****" by (simp add: "**") blast 
  thus \<open>s \<in> \<T> (P' \<Theta> a \<in> A. Q' a)\<close>
  proof cases
    show \<open>s \<in> min_elems (\<D> P) \<Longrightarrow> set s \<inter> ev ` A = {} \<Longrightarrow> s \<in> \<T> (Throw P' A Q')\<close>
      by (drule set_mp[OF le_approx3[OF that(1)]], simp add: T_Throw)
  next
    fix t1 a t2
    assume ***** : \<open>s = t1 @ ev a # t2\<close> \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>t2 \<in> min_elems (\<D> (Q a))\<close>
      \<open>t1 @ [ev a] \<in> min_elems (\<D> P) \<or> t1 @ [ev a] \<in> \<T> P \<and> t1 @ [ev a] \<notin> \<D> P\<close>
    have \<open>t1 @ [ev a] \<in> \<T> P' \<and> t2 \<in> \<T> (Q' a)\<close>
      by (meson "*****"(3-5) D_T events_of_memI in_set_conv_decomp le_approx2T le_approx_def subsetD that)
    with "*****" show \<open>s \<in> \<T> (Throw P' A Q')\<close>
      by (simp add: T_Throw) blast
  qed
qed


lemma mono_Throw_eq :
  \<open>(\<And>a. a \<in> A \<Longrightarrow> a \<in> \<alpha>(P) \<Longrightarrow> Q a = Q' a) \<Longrightarrow>
   P \<Theta> a \<in> A. Q a = P \<Theta> a \<in> A. Q' a\<close>
  by (subst Process_eq_spec) (auto simp add: Throw_projs events_of_memI)



subsection \<open>Properties\<close>

lemma Throw_STOP [simp] : \<open>STOP \<Theta> a \<in> A. Q a = STOP\<close>
  by (auto simp add: STOP_iff_T T_Throw T_STOP D_STOP)

lemma Throw_is_STOP_iff : \<open>P \<Theta> a \<in> A. Q a = STOP \<longleftrightarrow> P = STOP\<close>
proof (rule iffI)
  show \<open>P = STOP\<close> if \<open>P \<Theta> a \<in> A. Q a = STOP\<close>
  proof (rule ccontr)
    assume \<open>P \<noteq> STOP\<close>
    then obtain t where \<open>t \<noteq> []\<close> \<open>t \<in> \<T> P\<close> by (auto simp add: STOP_iff_T)
    hence \<open>[hd t] \<in> \<T> P\<close>
      by (metis append_Cons append_Nil is_processT3_TR_append list.sel(1) neq_Nil_conv)
    hence \<open>[hd t] \<in> \<T> (P \<Theta> a \<in> A. Q a)\<close> by (auto simp add: T_Throw Cons_eq_append_conv)
    with \<open>P \<Theta> a \<in> A. Q a = STOP\<close> show False by (simp add: STOP_iff_T)
  qed
next
  show \<open>P = STOP \<Longrightarrow> P \<Theta> a \<in> A. Q a = STOP\<close> by simp
qed

lemma Throw_SKIP [simp] : \<open>SKIP r \<Theta> a \<in> A. Q a = SKIP r\<close>
  by (auto simp add: Process_eq_spec F_Throw F_SKIP D_Throw D_SKIP T_SKIP)

lemma Throw_BOT [simp] : \<open>\<bottom> \<Theta> a \<in> A. Q a = \<bottom>\<close>
  by (simp add: BOT_iff_Nil_D D_Throw D_BOT)

lemma Throw_is_BOT_iff: \<open>P \<Theta> a \<in> A. Q a = \<bottom> \<longleftrightarrow> P = \<bottom>\<close>
  by (simp add: BOT_iff_Nil_D D_Throw) 


lemma Throw_empty_set [simp] : \<open>P \<Theta> a \<in> {}. Q a = P\<close>
  by (auto simp add: Process_eq_spec F_Throw D_Throw intro: is_processT7 is_processT8)
    (metis append.right_neutral front_tickFree_nonempty_append_imp
      nonTickFree_n_frontTickFree process_charn snoc_eq_iff_butlast)



lemma Throw_is_restrictable_on_events_of :
  \<open>P \<Theta> a \<in> A. Q a = P \<Theta> a \<in> (A \<inter> \<alpha>(P)). Q a\<close> (is \<open>?lhs = ?rhs\<close>)
  \<comment>\<open>A stronger version where \<^term>\<open>\<alpha>(P)\<close> is replaced by
    \<^term>\<open>\<^bold>\<alpha>(P) \<union> {a. \<exists>t. t @ [ev a] \<in> min_elems (\<D> P)}\<close> is probably true.\<close>
proof (cases \<open>\<D> P = {}\<close>)
  show \<open>?lhs = ?rhs\<close> if \<open>\<D> P = {}\<close>
  proof (rule Process_eq_optimizedI)
    fix t assume \<open>t \<in> \<D> ?lhs\<close>
    with \<open>\<D> P = {}\<close> obtain t1 a t2
      where * : \<open>t = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close>
        \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>t2 \<in> \<D> (Q a)\<close>
      unfolding D_Throw by blast
    from "*"(3) have \<open>set t1 \<inter> ev ` (A \<inter> \<alpha>(P)) = {}\<close> by blast
    moreover from "*"(2, 4) have \<open>a \<in> A \<inter> \<alpha>(P)\<close> by (simp add: events_of_memI)
    ultimately show \<open>t \<in> \<D> ?rhs\<close> using "*"(1, 2, 5) by (auto simp add: D_Throw)
  next
    fix t assume \<open>t \<in> \<D> ?rhs\<close>
    with \<open>\<D> P = {}\<close> obtain t1 a t2
      where * : \<open>t = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close>
        \<open>set t1 \<inter> ev ` (A \<inter> \<alpha>(P)) = {}\<close> \<open>a \<in> A \<inter> \<alpha>(P)\<close> \<open>t2 \<in> \<D> (Q a)\<close>
      unfolding D_Throw by blast
    from "*"(2, 3) events_of_memI have \<open>set t1 \<inter> ev ` A = {}\<close> by fastforce
    with "*"(1, 2, 4, 5) show \<open>t \<in> \<D> ?lhs\<close> by (auto simp add: D_Throw)
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?lhs\<close>
    with \<open>\<D> P = {}\<close> consider \<open>(t, X) \<in> \<F> P\<close> \<open>set t \<inter> ev ` A = {}\<close>
      | (failR) t1 a t2 where \<open>t = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close>
        \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>(t2, X) \<in> \<F> (Q a)\<close>
      unfolding F_Throw by blast
    thus \<open>(t, X) \<in> \<F> ?rhs\<close>
    proof cases
      show \<open>(t, X) \<in> \<F> P \<Longrightarrow> set t \<inter> ev ` A = {} \<Longrightarrow> (t, X) \<in> \<F> ?rhs\<close>
        by (simp add: F_Throw disjoint_iff image_iff)
    next
      case failR
      from failR(3) have \<open>set t1 \<inter> ev ` (A \<inter> \<alpha>(P)) = {}\<close> by blast
      moreover from failR(2, 4) have \<open>a \<in> A \<inter> \<alpha>(P)\<close> by (simp add: events_of_memI)
      ultimately show \<open>(t, X) \<in> \<F> ?rhs\<close> using failR(1, 2, 5) by (auto simp add: F_Throw)
    qed
  next
    fix t X assume \<open>(t, X) \<in> \<F> ?rhs\<close>
    with \<open>\<D> P = {}\<close> consider \<open>(t, X) \<in> \<F> P\<close> \<open>set t \<inter> ev ` (A \<inter> \<alpha>(P)) = {}\<close>
      | (failR) t1 a t2 where \<open>t = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close>
        \<open>set t1 \<inter> ev ` (A \<inter> \<alpha>(P)) = {}\<close> \<open>a \<in> A\<close>
        \<open>a \<in> \<alpha>(P)\<close> \<open>(t2, X) \<in> \<F> (Q a)\<close>
      unfolding F_Throw by blast
    thus \<open>(t, X) \<in> \<F> ?lhs\<close>
    proof cases
      assume \<open>(t, X) \<in> \<F> P\<close> \<open>set t \<inter> ev ` (A \<inter> \<alpha>(P)) = {}\<close>
      from \<open>(t, X) \<in> \<F> P\<close> have \<open>t \<in> \<T> P\<close> by (simp add: F_T)
      with \<open>set t \<inter> ev ` (A \<inter> \<alpha>(P)) = {}\<close> events_of_memI
      have \<open>set t \<inter> ev ` A = {}\<close> by fast
      with \<open>(t, X) \<in> \<F> P\<close> show \<open>(t, X) \<in> \<F> ?lhs\<close> by (simp add: F_Throw)
    next
      case failR
      from failR(2, 3) events_of_memI have \<open>set t1 \<inter> ev ` A = {}\<close> by fastforce
      with failR(1, 2, 4-6) show \<open>(t, X) \<in> \<F> ?lhs\<close> by (auto simp add: F_Throw)
    qed
  qed
next
  assume \<open>\<D> P \<noteq> {}\<close>
  hence \<open>\<alpha>(P) = UNIV\<close> by (simp add: events_of_is_strict_events_of_or_UNIV)
  thus \<open>?lhs = ?rhs\<close> by simp
qed


lemma Throw_disjoint_events_of: \<open>A \<inter> \<alpha>(P) = {} \<Longrightarrow> P \<Theta> a \<in> A. Q a = P\<close>
  by (metis Throw_empty_set Throw_is_restrictable_on_events_of)



subsection \<open>Continuity\<close>

context begin

private lemma chain_Throw_left  : \<open>chain Y \<Longrightarrow> chain (\<lambda>i. Y i \<Theta> a \<in> A. Q a)\<close>
  by (simp add: chain_def)

private lemma chain_Throw_right : \<open>chain Y \<Longrightarrow> chain (\<lambda>i. P \<Theta> a \<in> A. Y i a)\<close>
  by (simp add: chain_def fun_belowD)


private lemma cont_left_prem_Throw :
  \<open>(\<Squnion> i. Y i) \<Theta> a \<in> A. Q a = (\<Squnion> i. Y i \<Theta> a \<in> A. Q a)\<close>
  (is \<open>?lhs = ?rhs\<close>) if \<open>chain Y\<close>
proof (subst Process_eq_spec_optimized, safe)
  show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close> for s
    by (auto simp add: limproc_is_thelub \<open>chain Y\<close> chain_Throw_left D_Throw T_LUB D_LUB)
next
  fix s
  define S
    where \<open>S i \<equiv> {t1. \<exists>t2. s = t1 @ t2 \<and> t1 \<in> \<D> (Y i) \<and> tickFree t1 \<and>
                           set t1 \<inter> ev ` A = {} \<and> front_tickFree t2} \<union>
                 {t1. \<exists>a t2. s = t1 @ ev a # t2 \<and> t1 @ [ev a] \<in> \<T> (Y i) \<and> tickFree t1 \<and>
                             set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> t2 \<in> \<D> (Q a)}\<close> for i
  assume \<open>s \<in> \<D> ?rhs\<close>
  hence ftF: \<open>front_tickFree s\<close> using D_imp_front_tickFree by blast
  from \<open>s \<in> \<D> ?rhs\<close> have \<open>s \<in> \<D> (Y i \<Theta> a \<in> A. Q a)\<close> for i
    by (simp add: limproc_is_thelub D_LUB chain_Throw_left \<open>chain Y\<close>)
  hence \<open>S i \<noteq> {}\<close> for i by (simp add: S_def D_Throw)
      (metis append_T_imp_tickFree not_Cons_self2)
  moreover have \<open>finite (S 0)\<close>
    unfolding S_def by (prove_finite_subset_of_prefixes s)
  moreover have \<open>S (Suc i) \<subseteq> S i\<close> for i
    unfolding S_def apply (intro allI Un_mono subsetI; simp)
    by (metis in_mono le_approx1 po_class.chainE \<open>chain Y\<close>)
      (metis le_approx_lemma_T po_class.chain_def subset_eq \<open>chain Y\<close>)
  ultimately have \<open>(\<Inter>i. S i) \<noteq> {}\<close>
    by (rule Inter_nonempty_finite_chained_sets)
  then obtain t1 where * : \<open>\<forall>i. t1 \<in> S i\<close>
    by (meson INT_iff ex_in_conv iso_tuple_UNIV_I)
  show \<open>s \<in> \<D> ?lhs\<close>
  proof (cases \<open>\<exists>j a t2. s = t1 @ ev a # t2 \<and> t1 @ [ev a] \<in> \<T> (Y j) \<and> a \<in> A \<and> t2 \<in> \<D> (Q a)\<close>)
    case True
    then obtain j a t2 where ** : \<open>s = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> (Y j)\<close>
      \<open>a \<in> A\<close> \<open>t2 \<in> \<D> (Q a)\<close> by blast
    from "*" "**"(1) have \<open>\<forall>i. t1 @ [ev a] \<in> \<T> (Y i)\<close>
      by (simp add: S_def) (meson D_T front_tickFree_single is_processT7)
    with "*" "**"(1, 3, 4) show \<open>s \<in> \<D> ?lhs\<close>
      by (simp add: S_def D_Throw limproc_is_thelub \<open>chain Y\<close> T_LUB) blast
  next
    case False
    with "*" have \<open>\<forall>i. \<exists>t2. s = t1 @ t2 \<and> t1 \<in> \<D> (Y i) \<and> front_tickFree t2\<close>
      by (simp add: S_def) blast
    hence \<open>\<exists>t2. s = t1 @ t2 \<and> (\<forall>i. t1 \<in> \<D> (Y i)) \<and> front_tickFree t2\<close> by blast
    with "*" show \<open>s \<in> \<D> ?lhs\<close>
      by (simp add: S_def D_Throw limproc_is_thelub \<open>chain Y\<close> D_LUB) blast
  qed
next
  show \<open>(s, X) \<in> \<F> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for s X
    by (auto simp add: limproc_is_thelub \<open>chain Y\<close> chain_Throw_left F_Throw F_LUB T_LUB D_LUB)
next
  assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
  fix s X assume \<open>(s, X) \<in> \<F> ?rhs\<close>
  show \<open>(s, X) \<in> \<F> ?lhs\<close>
  proof (cases \<open>s \<in> \<D> ?rhs\<close>)
    show \<open>s \<in> \<D> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> by (simp add: is_processT8 same_div)
  next
    assume \<open>s \<notin> \<D> ?rhs\<close>
    have \<open>\<forall>a\<in>A. Q a \<sqsubseteq> Q a\<close> by simp
    moreover from \<open>s \<notin> \<D> ?rhs\<close> obtain j where \<open>s \<notin> \<D> (Y j \<Theta> a \<in> A. Q a)\<close>
      by (auto simp add: limproc_is_thelub chain_Throw_left \<open>chain Y\<close> D_LUB)
    moreover from \<open>(s, X) \<in> \<F> ?rhs\<close> have \<open>(s, X) \<in> \<F> (Y j \<Theta> a \<in> A. Q a)\<close>
      by (simp add: limproc_is_thelub chain_Throw_left \<open>chain Y\<close> F_LUB)
    ultimately show \<open>(s, X) \<in> \<F> ?lhs\<close>
      by (meson is_ub_thelub le_approx2 mono_Throw \<open>chain Y\<close>)
  qed
qed



private lemma cont_right_prem_Throw : 
  \<open>P \<Theta> a \<in> A. (\<Squnion> i. Y i a) = (\<Squnion> i. P \<Theta> a \<in> A. Y i a)\<close>
  (is \<open>?lhs = ?rhs\<close>) if \<open>chain Y\<close>
proof (subst Process_eq_spec_optimized, safe)
  show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close> for s
    by (simp add: limproc_is_thelub \<open>chain Y\<close> chain_Throw_right ch2ch_fun[OF \<open>chain Y\<close>] D_Throw D_LUB) blast
next
  fix s
  assume \<open>s \<in> \<D> ?rhs\<close>
  define S
    where \<open>S i \<equiv> {t1. \<exists>t2. s = t1 @ t2 \<and> t1 \<in> \<D> P \<and> tF t1 \<and>
                           set t1 \<inter> ev ` A = {} \<and> ftF t2} \<union>
                 {t1. \<exists>a t2. s = t1 @ ev a # t2 \<and> t1 @ [ev a] \<in> \<T> P \<and>
                             set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> t2 \<in> \<D> (Y i a)}\<close> for i
  assume \<open>s \<in> \<D> ?rhs\<close>
  hence \<open>s \<in> \<D> (P \<Theta> a \<in> A. Y i a)\<close> for i
    by (simp add: limproc_is_thelub D_LUB chain_Throw_right \<open>chain Y\<close>)
  hence \<open>S i \<noteq> {}\<close> for i by (simp add: S_def D_Throw) metis
  moreover have \<open>finite (S 0)\<close>
    unfolding S_def by (prove_finite_subset_of_prefixes s)
  moreover have \<open>S (Suc i) \<subseteq> S i\<close> for i
    unfolding S_def apply (intro allI Un_mono subsetI; simp)
    by (metis fun_belowD le_approx1 po_class.chainE subset_iff \<open>chain Y\<close>)
  ultimately have \<open>(\<Inter>i. S i) \<noteq> {}\<close>
    by (rule Inter_nonempty_finite_chained_sets)
  then obtain t1 where \<open>\<forall>i. t1 \<in> S i\<close> 
    by (meson INT_iff ex_in_conv iso_tuple_UNIV_I)
  then consider \<open>t1 \<in> \<D> P\<close> \<open>tF t1\<close>
    \<open>set t1 \<inter> ev ` A = {}\<close> \<open>\<exists>t2. s = t1 @ t2 \<and> ftF t2\<close>
    | \<open>set t1 \<inter> ev ` A = {}\<close>
      \<open>\<forall>i. \<exists>a t2. s = t1 @ ev a # t2 \<and> t1 @ [ev a] \<in> \<T> P \<and> a \<in> A \<and> t2 \<in> \<D> (Y i a)\<close>
    by (simp add: S_def) blast
  thus \<open>s \<in> \<D> ?lhs\<close>
  proof cases
    show \<open>t1 \<in> \<D> P \<Longrightarrow> tickFree t1 \<Longrightarrow> set t1 \<inter> ev ` A = {} \<Longrightarrow>
          \<exists>t2. s = t1 @ t2 \<and> front_tickFree t2 \<Longrightarrow> s \<in> \<D> ?lhs\<close>
      by (simp add: D_Throw) blast
  next
    assume assms: \<open>set t1 \<inter> ev ` A = {}\<close>
      \<open>\<forall>i. \<exists>a t2. s = t1 @ ev a # t2 \<and> t1 @ [ev a] \<in> \<T> P \<and> 
                              a \<in> A \<and> t2 \<in> \<D> (Y i a)\<close>
    from assms(2) obtain a t2
      where * : \<open>s = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close> \<open>a \<in> A\<close> by blast
    with assms(2) have \<open>\<forall>i. t2 \<in> \<D> (Y i a)\<close> by blast
    with assms(1) "*"(1, 2, 3) show \<open>s \<in> \<D> ?lhs\<close>
      by (simp add: D_Throw limproc_is_thelub \<open>chain Y\<close> ch2ch_fun D_LUB) blast
  qed
next
  show \<open>(s, X) \<in> \<F> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for s X
    by (simp add: limproc_is_thelub \<open>chain Y\<close> chain_Throw_right ch2ch_fun[OF \<open>chain Y\<close>] F_Throw F_LUB T_LUB D_LUB) blast
next
  assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
  fix s X assume \<open>(s, X) \<in> \<F> ?rhs\<close>
  show \<open>(s, X) \<in> \<F> ?lhs\<close>
  proof (cases \<open>s \<in> \<D> ?rhs\<close>)
    show \<open>s \<in> \<D> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> by (simp add: is_processT8 same_div)
  next
    assume \<open>s \<notin> \<D> ?rhs\<close>
    have \<open>\<forall>a\<in>A. Y i a \<sqsubseteq> (\<Squnion>i. Y i a)\<close> for i by (metis ch2ch_fun is_ub_thelub \<open>chain Y\<close>)
    moreover from \<open>s \<notin> \<D> ?rhs\<close> obtain j where \<open>s \<notin> \<D> (P \<Theta> a \<in> A. Y j a)\<close>
      by (auto simp add: limproc_is_thelub chain_Throw_right \<open>chain Y\<close> D_LUB)
    moreover from \<open>(s, X) \<in> \<F> ?rhs\<close> have \<open>(s, X) \<in> \<F> (P \<Theta> a \<in> A. Y j a)\<close>
      by (simp add: limproc_is_thelub chain_Throw_right \<open>chain Y\<close> F_LUB)
    find_theorems \<open>chain (\<lambda>a. ?P)\<close>
    ultimately show \<open>(s, X) \<in> \<F> ?lhs\<close>
      by (metis (mono_tags, lifting) below_refl le_approx2 mono_Throw)
  qed
qed




lemma Throw_cont[simp] : 
  assumes cont_f : \<open>cont f\<close> and cont_g : \<open>\<forall>a. cont (g a)\<close>
  shows \<open>cont (\<lambda>x. f x \<Theta> a \<in> A. g a x)\<close>
proof -
  have * : \<open>cont (\<lambda>y. y \<Theta> a \<in> A. g a x)\<close> for x
    by (rule contI2, rule monofunI, solves simp, simp add: cont_left_prem_Throw)
  have \<open>\<And>y. cont (Throw y A)\<close>
    by (simp add: contI2 cont_right_prem_Throw fun_belowD lub_fun monofunI)
  hence ** : \<open>cont (\<lambda>x. y \<Theta> a \<in> A. g a x)\<close> for y
    by (rule cont_compose) (simp add: cont_g)
  show ?thesis by (fact cont_apply[OF cont_f "*" "**"])
qed


end

(*<*)
end
  (*>*)

