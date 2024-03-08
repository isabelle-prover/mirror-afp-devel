(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : HOL-CSP_OpSem - Operational semantics for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Burkhart Wolff
 *
 * This file       : The Throw operator
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

section\<open> The Throw Operator \<close>

theory  Throw
  imports "HOL-CSPM.CSPM"
begin


(*<*)
hide_const R
text \<open>We need to hide this because we want to be allowed to use the letter R in our lemmas.
      We can still access this notion via the notation \<^term>\<open>\<R> P\<close>.
      In further versions of \<^theory>\<open>HOL-CSP.Process\<close>, R will be renamed in Refusals 
      and we will remove this paragraph.\<close>

\<comment>\<open>This result should be in \<^session>\<open>HOL-CSP\<close>.\<close>
lemma Refusals_iff : \<open>X \<in> \<R> P \<longleftrightarrow> ([], X) \<in> \<F> P\<close>
  by (simp add: Failures_def R_def REFUSALS_def)
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

lift_definition Throw :: \<open>['\<alpha> process, '\<alpha> set, '\<alpha> \<Rightarrow> '\<alpha> process] \<Rightarrow> '\<alpha> process\<close>
  is \<open>\<lambda> P A Q. 
  ({(t1, X) \<in> \<F> P. set t1 \<inter> ev ` A = {}} \<union>
   {(t1 @ t2, X)| t1 t2 X. t1 \<in> \<D> P \<and> tickFree t1 \<and> 
                           set t1 \<inter> ev ` A = {} \<and> front_tickFree t2} \<union>
   {(t1 @ ev a # t2, X)| t1 a t2 X. t1 @ [ev a] \<in> \<T> P \<and> set t1 \<inter> ev ` A = {} \<and>
                                    a \<in> A \<and> (t2, X) \<in> \<F> (Q a)},
   {t1 @ t2| t1 t2. t1 \<in> \<D> P \<and> tickFree t1 \<and> 
                    set t1 \<inter> ev ` A = {} \<and> front_tickFree t2} \<union> 
   {t1 @ ev a # t2| t1 a t2. t1 @ [ev a] \<in> \<T> P \<and> set t1 \<inter> ev ` A = {} \<and> 
                             a \<in> A \<and> t2 \<in> \<D> (Q a)})\<close>
proof -
  show \<open>?thesis P A Q\<close> (is \<open>is_process (?f, ?d)\<close>) for P A Q
    unfolding is_process_def FAILURES_def DIVERGENCES_def fst_conv snd_conv
  proof (intro conjI allI impI; (elim conjE)?)
    show \<open>([], {}) \<in> ?f\<close> by (simp add: is_processT1)
  next
    show \<open>(s, X) \<in> ?f \<Longrightarrow> front_tickFree s\<close> for s X
      apply (simp, elim disjE exE)
      subgoal by (metis is_processT)
      subgoal by (solves \<open>simp add: front_tickFree_append\<close>)
      by (metis F_T append_Cons append_Nil append_T_imp_tickFree butlast.simps(2) event.simps(3)
                front_tickFree_append is_processT2_TR last_ConsL not_Cons_self tickFree_butlast)
  next
    show \<open>(s @ t, {}) \<in> ?f \<Longrightarrow> (s, {}) \<in> ?f\<close> for s t
    proof (induct t rule: rev_induct)
      case Nil
      thus \<open>(s, {}) \<in> ?f\<close> by simp
    next
      case (snoc b t)
      consider \<open>(s @ t @ [b], {}) \<in> \<F> P\<close> \<open>(set s \<union> set t) \<inter> ev ` A = {}\<close>
        | \<open>\<exists>t1 t2. s @ t @ [b] = t1 @ t2 \<and> t1 \<in> \<D> P \<and> tickFree t1 \<and> 
                   set t1 \<inter> ev ` A = {} \<and> front_tickFree t2 \<or>
                   (\<exists>a. s @ t @ [b] = t1 @ ev a # t2 \<and> t1 @ [ev a] \<in> \<T> P \<and> 
                        set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> (t2, {}) \<in> \<F> (Q a))\<close>
        using snoc.prems by simp blast
      thus \<open>(s, {}) \<in> ?f\<close>
      proof cases
        show \<open>(s @ t @ [b], {}) \<in> \<F> P \<Longrightarrow> (set s \<union> set t) \<inter> ev ` A = {} \<Longrightarrow> (s, {}) \<in> ?f\<close>
          by (drule is_processT3[rule_format]) (simp add: Int_Un_distrib2)
      next
        assume \<open>\<exists>t1 t2. s @ t @ [b] = t1 @ t2 \<and> t1 \<in> \<D> P \<and> tickFree t1 \<and> 
                   set t1 \<inter> ev ` A = {} \<and> front_tickFree t2 \<or>
                   (\<exists>a. s @ t @ [b] = t1 @ ev a # t2 \<and> t1 @ [ev a] \<in> \<T> P \<and> 
                        set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> (t2, {}) \<in> \<F> (Q a))\<close>
           (is \<open>\<exists>t1 t2. ?disj t1 t2\<close>)
        then obtain t1 t2 where \<open>?disj t1 t2\<close> by blast
        show \<open>(s, {}) \<in> ?f\<close>
        apply (rule snoc.hyps)
          using \<open>?disj t1 t2\<close> apply (elim disjE exE)
           apply (all \<open>cases t2 rule: rev_cases\<close>, simp_all)
          subgoal by (metis Int_Un_distrib2 T_F D_T Un_empty append.assoc is_processT3_SR set_append)
          subgoal by (metis front_tickFree_dw_closed) 
          subgoal by (meson T_F process_charn)
          by (metis process_charn)
      qed
    qed
  next
    show \<open>(s, Y) \<in> ?f \<Longrightarrow> X \<subseteq> Y \<Longrightarrow> (s, X) \<in> ?f\<close> for s X Y
      by simp (metis is_processT4)
  next
    fix s X Y
    assume assms : \<open>(s, X) \<in> ?f\<close> \<open>\<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> ?f\<close>
    consider \<open>(s, X) \<in> \<F> P\<close> \<open>set s \<inter> ev ` A = {}\<close>
      | \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<D> P \<and> tickFree t1 \<and> 
                 set t1 \<inter> ev ` A = {} \<and> front_tickFree t2\<close>
      | \<open>\<exists>t1 a t2. s = t1 @ ev a # t2 \<and> t1 @ [ev a] \<in> \<T> P \<and> 
                   set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> (t2, X) \<in> \<F> (Q a)\<close>
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
      assume \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<D> P \<and> tickFree t1 \<and> 
                      set t1 \<inter> ev ` A = {} \<and> front_tickFree t2\<close>
      hence \<open>s \<in> ?d\<close> by blast
      thus \<open>(s, X \<union> Y) \<in> ?f\<close> by simp (metis NF_ND)
    next
      assume \<open>\<exists>t1 a t2. s = t1 @ ev a # t2 \<and> t1 @ [ev a] \<in> \<T> P \<and> 
                        set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> (t2, X) \<in> \<F> (Q a)\<close>
      then obtain t1 a t2
        where * : \<open>s = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close> 
                  \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>(t2, X) \<in> \<F> (Q a)\<close> by blast
      have \<open>(t2 @ [c], {}) \<notin> \<F> (Q a)\<close> if \<open>c \<in> Y\<close> for c
        using assms(2)[rule_format, OF that, simplified, THEN conjunct2,
                       THEN conjunct2, rule_format, of a t1 \<open>t2 @ [c]\<close>]
        by (simp add: "*"(1, 2, 3, 4))
      with "*"(5) is_processT5 have ** : \<open>(t2, X \<union> Y) \<in> \<F> (Q a)\<close> by blast
      show \<open>(s, X \<union> Y) \<in> ?f\<close>
        using "*"(1, 2, 3, 4) "**" by blast
    qed
  next
    have * : \<open>\<And>s t1 a t2. s @ [tick] = t1 @ ev a # t2 \<Longrightarrow> \<exists>t2'. t2 = t2' @ [tick]\<close>
      by (simp add: snoc_eq_iff_butlast split: if_split_asm)
         (metis append_butlast_last_id)
    show \<open>(s @ [tick], {}) \<in> ?f \<Longrightarrow> (s, X - {tick}) \<in> ?f\<close> for s X
      apply (simp, elim disjE exE conjE)
      subgoal by (solves \<open>simp add: is_processT6\<close>)
      subgoal by (metis butlast_append butlast_snoc front_tickFree_butlast 
            non_tickFree_tick tickFree_Nil tickFree_append 
            tickFree_implies_front_tickFree)
      by (frule "*", elim exE, simp, metis is_processT6)
  next
    show \<open>\<lbrakk>s \<in> ?d; tickFree s; front_tickFree t\<rbrakk> \<Longrightarrow> s @ t \<in> ?d\<close> for s t
      by auto (metis front_tickFree_append, metis is_processT7)
  next
    show \<open>s \<in> ?d \<Longrightarrow> (s, X) \<in> ?f\<close> for s X
      by simp (metis NF_ND)
     
  next
    show \<open>s @ [tick] \<in> ?d \<Longrightarrow> s \<in> ?d\<close> for s 
      apply (simp, elim disjE)
      by (metis butlast_append butlast_snoc front_tickFree_butlast non_tickFree_tick
                tickFree_Nil tickFree_append tickFree_implies_front_tickFree)
         (metis D_T T_nonTickFree_imp_decomp append_single_T_imp_tickFree
                butlast.simps(2) butlast_append butlast_snoc event.distinct(1)
                process_charn tickFree_Cons tickFree_append)
  qed
qed


text \<open>We add some syntactic sugar.\<close>

syntax "_Throw" :: \<open>['\<alpha> process, pttrn, '\<alpha> set, '\<alpha> \<Rightarrow> '\<alpha> process] \<Rightarrow> '\<alpha> process\<close>
                   (\<open>((_) \<Theta> (_\<in>_)./ (_))\<close> [73, 0, 0, 73] 72)
translations "P \<Theta> a \<in> A. Q" \<rightleftharpoons> "CONST Throw P A (\<lambda>a. Q)"

abbreviation Throw_without_free_var :: 
  \<open>['\<alpha> process, '\<alpha> set, '\<alpha> process] \<Rightarrow> '\<alpha> process\<close> (\<open>((_) \<Theta> (_)/ (_))\<close> [73, 0, 73] 72)
  where \<open>P \<Theta> A Q \<equiv> P \<Theta> a \<in> A. Q\<close>

text \<open>Now we can write @{term [eta_contract = false] \<open>P \<Theta> a \<in> A. Q a\<close>}, and when
      we do not want \<^term>\<open>Q\<close> to be parameterized we can just write \<^term>\<open>P \<Theta> A Q\<close>.\<close>

lemma \<open>P \<Theta> a \<in> A. Q = P \<Theta> A Q\<close> by (fact refl)



subsection \<open>Projections\<close>

lemma F_Throw:
  \<open>\<F> (P \<Theta> a \<in> A. Q a) =
   {(t1, X) \<in> \<F> P. set t1 \<inter> ev ` A = {}} \<union>
   {(t1 @ t2, X)| t1 t2 X.
    t1 \<in> \<D> P \<and> tickFree t1 \<and> set t1 \<inter> ev ` A = {} \<and> front_tickFree t2} \<union>
   {(t1 @ ev a # t2, X)| t1 a t2 X.
    t1 @ [ev a] \<in> \<T> P \<and> set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> (t2, X) \<in> \<F> (Q a)}\<close>
  by (simp add: Failures_def FAILURES_def Throw.rep_eq)
  (* by (simp add: Failures.rep_eq FAILURES_def Throw.rep_eq) *)


lemma D_Throw:
  \<open>\<D> (P \<Theta> a \<in> A. Q a) =
   {t1 @ t2| t1 t2.
    t1 \<in> \<D> P \<and> tickFree t1 \<and> set t1 \<inter> ev ` A = {} \<and> front_tickFree t2} \<union>
   {t1 @ ev a # t2| t1 a t2.
    t1 @ [ev a] \<in> \<T> P \<and> set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> t2 \<in> \<D> (Q a)}\<close>
  by (simp add: Divergences_def DIVERGENCES_def Throw.rep_eq)
  (* by (simp add: Divergences.rep_eq DIVERGENCES_def Throw.rep_eq) *)


lemma T_Throw:
  \<open>\<T> (P \<Theta> a \<in> A. Q a) =
   {t1 \<in> \<T> P. set t1 \<inter> ev ` A = {}} \<union>
   {t1 @ t2| t1 t2.
    t1 \<in> \<D> P \<and> tickFree t1 \<and> set t1 \<inter> ev ` A = {} \<and> front_tickFree t2} \<union>
   {t1 @ ev a # t2| t1 a t2. 
    t1 @ [ev a] \<in> \<T> P \<and> set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> t2 \<in> \<T> (Q a)}\<close>
  by (auto simp add: Traces_def TRACES_def Failures_def[symmetric] F_Throw) blast+
  (* by (auto simp add: Traces.rep_eq TRACES_def Failures.rep_eq[symmetric] F_Throw) blast+ *)



subsection \<open>Monotony\<close>

lemma min_elems_Un_subset:
  \<open>min_elems (A \<union> B) \<subseteq> min_elems A \<union> (min_elems B - A)\<close>
  by (auto simp add: min_elems_def subset_iff)

lemma mono_Throw[simp] : \<open>P \<Theta> a \<in> A. Q a \<sqsubseteq> P' \<Theta> a \<in> A. Q' a\<close> 
  if \<open>P \<sqsubseteq> P'\<close> and \<open>\<forall>a \<in> A. Q a \<sqsubseteq> Q' a\<close>
proof (unfold le_approx_def Ra_def, safe)
  from le_approx1[OF that(1)] le_approx_lemma_T[OF that(1)] 
       le_approx1[OF that(2)[rule_format]] 
  show \<open>s \<in> \<D> (P' \<Theta> a \<in> A. Q' a) \<Longrightarrow> s \<in> \<D> (P \<Theta> a \<in> A. Q a)\<close> for s 
    by (simp add: D_Throw subset_iff) metis
next
  fix s X
  assume assms : \<open>s \<notin> \<D> (P \<Theta> a \<in> A. Q a)\<close> \<open>(s, X) \<in> \<F> (P \<Theta> a \<in> A. Q a)\<close>
  from assms(2) consider \<open>(s, X) \<in> \<F> P\<close> \<open>set s \<inter> ev ` A = {}\<close>
    | \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<D> P \<and> tickFree t1 \<and> 
               set t1 \<inter> ev ` A = {} \<and> front_tickFree t2\<close>
    | \<open>\<exists>t1 a t2. s = t1 @ ev a # t2 \<and> t1 @ [ev a] \<in> \<T> P \<and>
                 set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> (t2, X) \<in> \<F> (Q a)\<close>
    by (simp add: F_Throw) blast
  thus \<open>(s, X) \<in> \<F> (P' \<Theta> a \<in> A. Q' a)\<close>
  proof cases
    assume * : \<open>(s, X) \<in> \<F> P\<close> \<open>set s \<inter> ev ` A = {}\<close>
    from assms(1)[simplified D_Throw, simplified, THEN conjunct1, rule_format, of s]
         assms(1)[simplified D_Throw, simplified, THEN conjunct1, rule_format, of \<open>butlast s\<close>]
    have ** : \<open>s \<notin> \<D> P\<close> 
      using "*"(2) apply (cases \<open>tickFree s\<close>, auto)
      by (metis append_butlast_last_id disjoint_iff front_tickFree_butlast 
          front_tickFree_single in_set_butlastD process_charn tickFree_butlast)
    show \<open>(s, X) \<in> \<F> P \<Longrightarrow> set s \<inter> ev ` A = {} \<Longrightarrow> (s, X) \<in> \<F> (Throw P' A Q')\<close>
      by (simp add: F_Throw le_approx2[OF that(1) "**"])
  next
    assume \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<D> P \<and> tickFree t1 \<and> 
                    set t1 \<inter> ev ` A = {} \<and> front_tickFree t2\<close>
    with assms(1) show \<open>(s, X) \<in> \<F> (Throw P' A Q')\<close> 
      by (simp add: F_Throw D_Throw)
  next
    assume \<open>\<exists>t1 a t2. s = t1 @ ev a # t2 \<and> t1 @ [ev a] \<in> \<T> P \<and> 
                      set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> (t2, X) \<in> \<F> (Q a)\<close>
    then obtain t1 a t2 
      where * : \<open>s = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close> 
                \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>(t2, X) \<in> \<F> (Q a)\<close> by blast
    from "*"(2) append_single_T_imp_tickFree have ** : \<open>tickFree t1\<close> by blast
    have *** : \<open>(t2, X) \<in> \<F> (Q' a)\<close> 
      by (fact assms(1)[simplified D_Throw, simplified, THEN conjunct2, rule_format,
                        OF "*"(4, 3, 2, 1), THEN le_approx2[OF that(2)[rule_format, OF "*"(4)]], 
                        of X, simplified "*"(5), simplified])
    have **** : \<open>t1 \<notin> \<D> P\<close>
      apply (rule notI)
      apply (drule assms(1)[simplified D_Throw, simplified, THEN conjunct1, rule_format,
                            OF "*"(3) "**", of \<open>ev a # t2\<close>, simplified "*"(1), simplified])
      by (metis "*"(1) assms(2) front_tickFree_mono process_charn)
    show \<open>(s, X) \<in> \<F> (Throw P' A Q')\<close>
      apply (simp add: F_Throw D_Throw "*"(1))
      by (metis "*"(2, 3, 4) "***" "****" T_F_spec le_approx2 min_elems6 that(1))
  qed
next
  from le_approx1[OF that(1)] le_approx2[OF that(1)] le_approx2T[OF that(1)]
       le_approx2[OF that(2)[rule_format]]
  show \<open>s \<notin> \<D> (P \<Theta> a \<in> A. Q a) \<Longrightarrow> 
        (s, X) \<in> \<F> (P' \<Theta> a \<in> A. Q' a) \<Longrightarrow> (s, X) \<in> \<F> (P \<Theta> a \<in> A. Q a)\<close> for s X
    apply (simp add: F_Throw D_Throw subset_eq, safe, simp_all)
    by (meson NF_ND) (metis D_T)+
next
  define S_left 
    where \<open>S_left \<equiv> {t1 @ t2 |t1 t2. t1 \<in> \<D> P \<and> tickFree t1 \<and> 
                     set t1 \<inter> ev ` A = {} \<and> front_tickFree t2}\<close>
  define S_right 
    where \<open>S_right \<equiv> {t1 @ ev a # t2 |t1 a t2. t1 @ [ev a] \<in> \<T> P \<and>
                      set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> t2 \<in> \<D> (Q a)}\<close>

  have * : \<open>min_elems (\<D> (P \<Theta> a \<in> A. Q a)) \<subseteq> min_elems S_left \<union> (min_elems S_right - S_left)\<close>
    unfolding S_left_def S_right_def 
    by (simp add: D_Throw min_elems_Un_subset)
  have ** : \<open>min_elems S_left = {t1 \<in> min_elems (\<D> P). set t1 \<inter> ev ` A = {}}\<close>
    unfolding S_left_def min_elems_def le_list_def less_list_def
    apply (simp, safe)
    subgoal by (solves \<open>meson is_processT7_S\<close>) 
    subgoal by (metis Int_Un_distrib2 Un_empty append.right_neutral front_tickFree_Nil
          front_tickFree_append front_tickFree_mono set_append)
    subgoal by (metis IntI append_Nil2 front_tickFree_Nil imageI)  
    subgoal by (metis list.distinct(1) nonTickFree_n_frontTickFree process_charn self_append_conv)
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
        unfolding S_right_def using assms(1, 2, 3) 
        by (auto simp add: less_append less_cons)
      with assms(5) min_elems_no nless_le show False by blast
    next
      assume \<open>t1 @ [ev a] \<in> \<D> P\<close> \<open>t1 @ [ev a] \<notin> min_elems (\<D> P)\<close>
      hence \<open>t1 \<in> \<D> P\<close> using min_elems1 by blast
      with \<open>t1 @ [ev a] \<in> \<D> P\<close> have \<open>t1 @ ev a # t2 \<in> S_left\<close>
        by (simp add: S_left_def)
           (metis D_imp_front_tickFree append_Cons append_Nil assms(2, 4)
                  event.simps(3) front_tickFree_append tickFree_Nil
                  front_tickFree_implies_tickFree tickFree_Cons)
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
    using "***" by fastforce

  fix s
  assume assm: \<open>s \<in> min_elems (\<D> (P \<Theta> a \<in> A. Q a))\<close>
  from set_mp[OF "*", OF this] 
  consider \<open>s \<in> min_elems (\<D> P)\<close> \<open>set s \<inter> ev ` A = {}\<close>
    | \<open>\<exists>t1 a t2.
       s = t1 @ ev a # t2 \<and> set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> t2 \<in> min_elems (\<D> (Q a)) \<and>
       (t1 @ [ev a] \<in> min_elems (\<D> P) \<or> t1 @ [ev a] \<in> \<T> P \<and> t1 @ [ev a] \<notin> \<D> P)\<close>
    using "****" by (simp add: "**") blast 
  thus \<open>s \<in> \<T> (P' \<Theta> a \<in> A. Q' a)\<close>
  proof cases
    show \<open>s \<in> min_elems (\<D> P) \<Longrightarrow> set s \<inter> ev ` A = {} \<Longrightarrow> s \<in> \<T> (Throw P' A Q')\<close>
      by (drule set_mp[OF le_approx3[OF that(1)]], simp add: T_Throw)
  next
    assume \<open>\<exists>t1 a t2.
            s = t1 @ ev a # t2 \<and> set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> t2 \<in> min_elems (\<D> (Q a)) \<and>
            (t1 @ [ev a] \<in> min_elems (\<D> P) \<or> t1 @ [ev a] \<in> \<T> P \<and> t1 @ [ev a] \<notin> \<D> P)\<close>
    then obtain t1 a t2
      where ***** : \<open>s = t1 @ ev a # t2\<close> \<open>set t1 \<inter> ev ` A = {}\<close>
                    \<open>a \<in> A\<close> \<open>t2 \<in> min_elems (\<D> (Q a))\<close>
                    \<open>t1 @ [ev a] \<in> min_elems (\<D> P) \<or> 
                     t1 @ [ev a] \<in> \<T> P \<and> t1 @ [ev a] \<notin> \<D> P\<close> by blast
    have \<open>t1 @ [ev a] \<in> \<T> P' \<and> t2 \<in> \<T> (Q' a)\<close>
      by (meson "*****"(3, 4, 5) le_approx2T le_approx3 subsetD that)
    with "*****" show \<open>s \<in> \<T> (Throw P' A Q')\<close>
      by (simp add: T_Throw) blast
  qed
qed


lemma mono_right_Throw_F :
  \<open>\<forall>a \<in> A. Q a \<sqsubseteq>\<^sub>F Q' a \<Longrightarrow> P \<Theta> a \<in> A. Q a \<sqsubseteq>\<^sub>F P \<Theta> a \<in> A. Q' a\<close>
  unfolding failure_refine_def
  by (simp add: F_Throw subset_iff disjoint_iff) blast

lemma mono_right_Throw_T : 
  \<open>\<forall>a \<in> A. Q a \<sqsubseteq>\<^sub>T Q' a \<Longrightarrow> P \<Theta> a \<in> A. Q a \<sqsubseteq>\<^sub>T P \<Theta> a \<in> A. Q' a\<close>
  unfolding trace_refine_def
  by (simp add: T_Throw subset_iff disjoint_iff) blast

lemma mono_right_Throw_D: 
  \<open>\<forall>a \<in> A. Q a \<sqsubseteq>\<^sub>D Q' a \<Longrightarrow> P \<Theta> a \<in> A. Q a \<sqsubseteq>\<^sub>D P \<Theta> a \<in> A. Q' a\<close>
  unfolding divergence_refine_def
  by (simp add: D_Throw subset_iff disjoint_iff) blast

lemma mono_Throw_FD : \<open>P \<sqsubseteq>\<^sub>F\<^sub>D P' \<Longrightarrow> \<forall>a \<in> A. Q a \<sqsubseteq>\<^sub>F\<^sub>D Q' a \<Longrightarrow>
                       P \<Theta> a \<in> A. Q a \<sqsubseteq>\<^sub>F\<^sub>D P' \<Theta> a \<in> A. Q' a\<close>
  apply (rule trans_FD[of _ \<open>P' \<Theta> a \<in> A. Q a\<close>])
  subgoal by (simp add: failure_divergence_refine_def 
                    le_ref_def F_Throw D_Throw subset_iff; safe;
          metis [[metis_verbose = false]] T_F no_Trace_implies_no_Failure)
  by (meson leFD_imp_leD leFD_imp_leF leF_leD_imp_leFD 
            mono_right_Throw_D mono_right_Throw_F)

lemma mono_Throw_DT : \<open>P \<sqsubseteq>\<^sub>D\<^sub>T P' \<Longrightarrow> \<forall>a \<in> A. Q a \<sqsubseteq>\<^sub>D\<^sub>T Q' a \<Longrightarrow>
                       P \<Theta> a \<in> A. Q a \<sqsubseteq>\<^sub>D\<^sub>T P' \<Theta> a \<in> A. Q' a\<close>
  apply (rule trans_DT[of _ \<open>P' \<Theta> a \<in> A. Q a\<close>])
  subgoal by (simp add: trace_divergence_refine_def trace_refine_def 
                   divergence_refine_def D_Throw T_Throw subset_iff, blast)
  by (simp add: mono_right_Throw_D mono_right_Throw_T trace_divergence_refine_def)



subsection \<open>Properties\<close>

lemma Throw_STOP: \<open>STOP \<Theta> a \<in> A. Q a = STOP\<close>
  by (auto simp add: STOP_iff_T T_Throw T_STOP D_STOP) 

lemma Throw_SKIP: \<open>SKIP \<Theta> a \<in> A. Q a = SKIP\<close>
  by (auto simp add: Process_eq_spec F_Throw F_SKIP D_Throw D_SKIP T_SKIP)

lemma Throw_BOT: \<open>\<bottom> \<Theta> a \<in> A. Q a = \<bottom>\<close>
  by (simp add: BOT_iff_D D_Throw D_UU)

lemma Throw_is_BOT_iff: \<open>P \<Theta> a \<in> A. Q a = \<bottom> \<longleftrightarrow> P = \<bottom>\<close>
  by (simp add: BOT_iff_D D_Throw) 


lemma Throw_empty_set: \<open>P \<Theta> a \<in> {}. Q a = P\<close>
  by (auto simp add: Process_eq_spec F_Throw D_Throw 
                     D_expand[symmetric] is_processT7_S is_processT8_S)


lemma Throw_Ndet:
  \<open>P \<sqinter> P' \<Theta> a \<in> A. Q a = (P \<Theta> a \<in> A. Q a) \<sqinter> (P' \<Theta> a \<in> A. Q a)\<close>
  \<open>P \<Theta> a \<in> A. Q a \<sqinter> Q' a = (P \<Theta> a \<in> A. Q a) \<sqinter> (P \<Theta> a \<in> A. Q' a)\<close>
  by (simp add: Process_eq_spec F_Throw F_Ndet D_Throw D_Ndet T_Ndet,
      safe, simp_all; blast)+

lemma Throw_Det:
  \<open>P \<box> P' \<Theta> a \<in> A. Q a = (P \<Theta> a \<in> A. Q a) \<box> (P' \<Theta> a \<in> A. Q a)\<close>
  \<open>P \<Theta> a \<in> A. Q a \<sqinter> Q' a = (P \<Theta> a \<in> A. Q a) \<box> (P \<Theta> a \<in> A. Q' a)\<close>
proof -
  show \<open>Throw (P \<box> P') A Q = Throw P A Q \<box> Throw P' A Q\<close> (is \<open>?lhs = ?rhs\<close>)
  proof (subst Process_eq_spec_optimized, safe)
    show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close> for s
      by (auto simp add: D_Det T_Det D_Throw)
  next
    show \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ?lhs\<close> for s
      by (simp add: D_Det T_Det D_Throw) blast
  next
    fix s X
    assume same_div: \<open>\<D> ?lhs = \<D> ?rhs\<close>
    assume \<open>(s, X) \<in> \<F> ?lhs\<close>
    hence \<open>(s, X) \<in> \<F> (P \<box> P') \<and> set s \<inter> ev ` A = {} \<or> s \<in> \<D> ?lhs \<or>
           (\<exists>t1 a t2. s = t1 @ ev a # t2 \<and> t1 @ [ev a] \<in> \<T> (P \<box> P') \<and> 
                      set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> (t2, X) \<in> \<F> (Q a))\<close>
      by (simp add: F_Throw D_Throw) blast
    thus \<open>(s, X) \<in> \<F> ?rhs\<close>
      apply (elim disjE exE)
      subgoal by (cases s, auto simp add: F_Det F_Throw T_Throw D_Throw)[1]
      subgoal by (use D_F same_div in blast)
      by (auto simp add: F_Det T_Det F_Throw T_Throw D_Throw)
  next
    show \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for s X
      apply (simp add: F_Det, elim disjE conjE)
      by (auto simp add: F_Det D_Det T_Det F_Throw D_Throw 
                         T_Throw D_T is_processT7_S subset_iff)
         (simp_all add: Cons_eq_append_conv)
  qed
next
  show \<open>P \<Theta> a \<in> A. Q a \<sqinter> Q' a = Throw P A Q \<box> Throw P A Q'\<close> (is \<open>?lhs Q Q' = ?rhs\<close>)
  proof (subst Process_eq_spec_optimized, safe)
    show \<open>s \<in> \<D> (?lhs Q Q') \<Longrightarrow> s \<in> \<D> ?rhs\<close> for s
      by (auto simp add: D_Det D_Throw D_Ndet)
  next
    show \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> (?lhs Q Q')\<close> for s
      by (simp add: D_Det D_Throw D_Ndet) blast
  next
    fix s X
    assume same_div: \<open>\<D> (?lhs Q Q') = \<D> ?rhs\<close>
    assume \<open>(s, X) \<in> \<F> (?lhs Q Q')\<close>
    hence \<open>(s, X) \<in> \<F> P \<and> set s \<inter> ev ` A = {} \<or> s \<in> \<D> (?lhs Q Q') \<or>
           (\<exists>t1 a t2. s = t1 @ ev a # t2 \<and> t1 @ [ev a] \<in> \<T> P \<and> 
                      set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> (t2, X) \<in> \<F> (Q a \<sqinter> Q' a))\<close>
      by (simp add: F_Throw D_Throw) blast
    thus \<open>(s, X) \<in> \<F> ?rhs\<close>
      apply (elim disjE exE)
      subgoal by (solves \<open>simp add: F_Det F_Throw\<close>)
      subgoal by (use D_F same_div in blast)
      by (auto simp add: F_Det F_Ndet F_Throw)
  next
    show \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> (?lhs Q Q')\<close> for s X
    proof (cases s)
      show \<open>s = [] \<Longrightarrow> (s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> (?lhs Q Q')\<close>
        by (auto simp add: F_Det F_Throw D_Throw T_Throw 
                           is_processT6_S2 Cons_eq_append_conv)
    next
      fix a s'
      have * : \<open>(a # s', X) \<in> \<F> (Throw P A Q) \<Longrightarrow>
                (a # s', X) \<in> \<F> (?lhs Q Q')\<close> for Q Q'
        by (auto simp add: F_Throw F_Det F_Ndet)
      show \<open>s = a # s' \<Longrightarrow> (s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> (?lhs Q Q')\<close>
        apply (simp add: F_Det, elim disjE)
        subgoal by (erule "*")
        by (subst Ndet_commute) (erule "*")
    qed
  qed
qed

lemma Throw_GlobalNdet:
  \<open>(\<sqinter>a \<in> A. P a) \<Theta> b \<in> B. Q b = \<sqinter>a \<in> A. (P a \<Theta> b \<in> B. Q b)\<close>
  \<open>P' \<Theta> a \<in> A. (\<sqinter>b \<in> B. Q' a b) = 
   (if B = {} then P' \<Theta> A STOP else \<sqinter>b \<in> B. (P' \<Theta> a \<in> A. Q' a b))\<close>                
  by (simp add: Process_eq_spec F_Throw D_Throw 
                F_GlobalNdet D_GlobalNdet T_GlobalNdet, safe, simp_all; blast)
     (simp add: Process_eq_spec F_Throw D_Throw 
                 F_GlobalNdet D_GlobalNdet T_GlobalNdet F_STOP D_STOP; blast)


lemma Throw_disjoint_events: \<open>A \<inter> events_of P = {} \<Longrightarrow> P \<Theta> a \<in> A. Q a = P\<close>
proof (subst Process_eq_spec_optimized, safe)
  show \<open>A \<inter> events_of P = {} \<Longrightarrow> s \<in> \<D> (Throw P A Q) \<Longrightarrow> s \<in> \<D> P\<close> for s
    by (simp add: D_Throw disjoint_iff events_of_def)
       (meson in_set_conv_decomp is_processT7_S)
next
  show \<open>A \<inter> events_of P = {} \<Longrightarrow> s \<in> \<D> P \<Longrightarrow> s \<in> \<D> (Throw P A Q)\<close> for s
    by (simp add: D_Throw disjoint_iff events_of_def image_iff)
       (metis (no_types, lifting) D_T append_Nil2 butlast_snoc front_tickFree_mono
              front_tickFree_butlast process_charn nonTickFree_n_frontTickFree)
next
  show \<open>A \<inter> events_of P = {} \<Longrightarrow> (s, X) \<in> \<F> (Throw P A Q) \<Longrightarrow> (s, X) \<in> \<F> P\<close> for s X
    by (simp add: F_Throw disjoint_iff events_of_def)
       (meson in_set_conv_decomp process_charn)
next
  show \<open>A \<inter> events_of P = {} \<Longrightarrow> (s, X) \<in> \<F> P \<Longrightarrow> (s, X) \<in> \<F> (Throw P A Q)\<close> for s X
    by (simp add: F_Throw disjoint_iff events_of_def image_iff) (metis F_T)
qed


lemma events_Throw:
  \<open>events_of (P \<Theta> a \<in> A. Q a) \<subseteq> events_of P \<union> (\<Union>a \<in> (A \<inter> events_of P). events_of (Q a))\<close>
proof (intro subsetI)
  fix e
  assume \<open>e \<in> events_of (P \<Theta> a \<in> A. Q a)\<close>
  then obtain s where * : \<open>ev e \<in> set s\<close> \<open>s \<in> \<T> (P \<Theta> a \<in> A. Q a)\<close>
    by (simp add: events_of_def) blast
  from "*"(2) consider \<open>s \<in> \<T> P\<close> \<open>set s \<inter> ev ` A = {}\<close>
    | \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<D> P \<and> tickFree t1 \<and>
               set t1 \<inter> ev ` A = {} \<and> front_tickFree t2\<close>
    | \<open>\<exists>t1 a t2. s = t1 @ ev a # t2 \<and> t1 @ [ev a] \<in> \<T> P \<and>
                 set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> t2 \<in> \<T> (Q a)\<close>
    by (simp add: T_Throw) blast
  thus \<open>e \<in> events_of P \<union> (\<Union>a \<in> (A \<inter> events_of P). events_of (Q a))\<close>
  proof cases
    from "*"(1) show \<open>s \<in> \<T> P \<Longrightarrow> set s \<inter> ev ` A = {} \<Longrightarrow>
                      e \<in> events_of P \<union> (\<Union>a\<in>A \<inter> events_of P. events_of (Q a))\<close>
      by (simp add: events_of_def) blast
  next
    show \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<D> P \<and> tickFree t1 \<and>
                  set t1 \<inter> ev ` A = {} \<and> front_tickFree t2 \<Longrightarrow>
          e \<in> events_of P \<union> (\<Union>a \<in> (A \<inter> events_of P). events_of (Q a))\<close>
      by (metis UNIV_I UnI1 empty_iff events_div)
  next
    assume \<open>\<exists>t1 a t2. s = t1 @ ev a # t2 \<and> t1 @ [ev a] \<in> \<T> P \<and>
                      set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> t2 \<in> \<T> (Q a)\<close>
    then obtain t1 a t2
      where ** : \<open>s = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close>
                 \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>t2 \<in> \<T> (Q a)\<close> by blast
    from "*"(1) "**"(1) have \<open>ev e \<in> set (t1 @ [ev a]) \<or> ev e \<in> set t2\<close> by simp
    thus \<open>e \<in> events_of P \<union> (\<Union>a \<in> (A \<inter> events_of P). events_of (Q a))\<close>
    proof (elim disjE)
      show \<open>ev e \<in> set (t1 @ [ev a]) \<Longrightarrow>
            e \<in> events_of P \<union> (\<Union>a\<in>A \<inter> events_of P. events_of (Q a))\<close>
        unfolding events_of_def using "**"(2) by blast
    next
      show \<open>ev e \<in> set t2 \<Longrightarrow> e \<in> events_of P \<union> (\<Union>a\<in>A \<inter> events_of P. events_of (Q a))\<close>
        unfolding events_of_def using "**"(2, 4, 5) mem_Collect_eq by fastforce
    qed
  qed
qed



subsection \<open>Key Property\<close>

lemma Throw_Mprefix: 
  \<open>(\<box>a \<in> A \<rightarrow> P a) \<Theta> b \<in> B. Q b =
    \<box>a \<in> A \<rightarrow> (if a \<in> B then Q a else P a \<Theta> b \<in> B. Q b)\<close>
  (is \<open>?lhs = ?rhs\<close>)
proof (subst Process_eq_spec_optimized, safe)
  fix s
  assume \<open>s \<in> \<D> ?lhs\<close>
  then consider \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<D> (Mprefix A P) \<and> tickFree t1 \<and>
                         set t1 \<inter> ev ` B = {} \<and> front_tickFree t2\<close>
  | \<open>\<exists>t1 b t2. s = t1 @ ev b # t2 \<and> t1 @ [ev b] \<in> \<T> (Mprefix A P) \<and>
               set t1 \<inter> ev ` B = {} \<and> b \<in> B \<and> t2 \<in> \<D> (Q b)\<close>
    by (simp add: D_Throw) blast
  thus \<open>s \<in> \<D> ?rhs\<close>
  proof cases
    assume \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<D> (Mprefix A P) \<and> tickFree t1 \<and>
                    set t1 \<inter> ev ` B = {} \<and> front_tickFree t2\<close>
    then obtain t1 t2
      where * : \<open>s = t1 @ t2\<close> \<open>t1 \<in> \<D> (Mprefix A P)\<close> \<open>tickFree t1\<close> 
                \<open>set t1 \<inter> ev ` B = {}\<close> \<open>front_tickFree t2\<close> by blast
    from "*"(2) obtain a t1' where ** : \<open>t1 = ev a # t1'\<close> \<open>a \<in> A\<close> \<open>t1' \<in> \<D> (P a)\<close>
      by (simp add: D_Mprefix) (metis event.inject image_iff list.collapse)
    from "*"(4) "**"(1) have *** : \<open>a \<notin> B\<close> by (simp add: image_iff)
    have \<open>t1' @ t2 \<in> \<D> (Throw (P a) B Q)\<close>
      using "*"(3, 4, 5) "**"(1, 3) by (auto simp add: D_Throw)
    with "***" show \<open>s \<in> \<D> ?rhs\<close>
      by (simp add: D_Mprefix "*"(1) "**"(1, 2))
  next
    assume \<open>\<exists>t1 b t2. s = t1 @ ev b # t2 \<and> t1 @ [ev b] \<in> \<T> (Mprefix A P) \<and>
                      set t1 \<inter> ev ` B = {} \<and> b \<in> B \<and> t2 \<in> \<D> (Q b)\<close>
    then obtain t1 b t2
      where * : \<open>s = t1 @ ev b # t2\<close> \<open>t1 @ [ev b] \<in> \<T> (Mprefix A P)\<close>
                \<open>set t1 \<inter> ev ` B = {}\<close> \<open>b \<in> B\<close> \<open>t2 \<in> \<D> (Q b)\<close> by blast
    show \<open>s \<in> \<D> ?rhs\<close>
    proof (cases \<open>t1\<close>)
      from "*"(2) show \<open>t1 = [] \<Longrightarrow> s \<in> \<D> ?rhs\<close>
        by (simp add: D_Mprefix T_Mprefix "*"(1, 4, 5))
    next
      fix a t1'
      assume \<open>t1 = a # t1'\<close>
      then obtain a' where \<open>t1 = ev a' # t1'\<close> (* a = ev a' *)
        by (metis "*"(2) append_single_T_imp_tickFree event.exhaust tickFree_Cons)
      with "*"(2, 3, 4, 5) show \<open>s \<in> \<D> ?rhs\<close>
        by (auto simp add: "*"(1) D_Mprefix T_Mprefix D_Throw)
    qed
  qed
next
  fix s
  assume \<open>s \<in> \<D> ?rhs\<close>
  then obtain a s' where * : \<open>a \<in> A\<close> \<open>s = ev a # s'\<close>
                             \<open>s' \<in> \<D> (if a \<in> B then Q a else Throw (P a) B Q)\<close> 
    by (simp add: D_Mprefix) (metis event.inject image_iff list.collapse)
  show \<open>s \<in> \<D> ?lhs\<close>
  proof (cases \<open>a \<in> B\<close>)
    assume \<open>a \<in> B\<close>
    hence ** :  \<open>[] @ [ev a] \<in> \<T> (Mprefix A P) \<and> set [] \<inter> ev ` B = {} \<and> s' \<in> \<D> (Q a)\<close>
      using "*"(3) by (simp add: T_Mprefix Nil_elem_T "*"(1))
    show \<open>s \<in> \<D> ?lhs\<close> 
      by (simp add: D_Throw) (metis "*"(2) "**" \<open>a \<in> B\<close> append_Nil)
  next
    assume \<open>a \<notin> B\<close>
    with "*"(2, 3)
    consider \<open>\<exists>t1 t2. s = ev a # t1 @ t2 \<and> t1 \<in> \<D> (P a) \<and> tickFree t1 \<and>
                      set t1 \<inter> ev ` B = {} \<and> front_tickFree t2\<close>
      | \<open>\<exists>t1 b t2. s = ev a # t1 @ ev b # t2 \<and> t1 @ [ev b] \<in> \<T> (P a) \<and>
                   set t1 \<inter> ev ` B = {} \<and> b \<in> B \<and> t2 \<in> \<D> (Q b)\<close>
      by (simp add: D_Throw) blast
    thus \<open>s \<in> \<D> ?lhs\<close>
    proof cases
      assume \<open>\<exists>t1 t2. s = ev a # t1 @ t2 \<and> t1 \<in> \<D> (P a) \<and> tickFree t1 \<and>
                      set t1 \<inter> ev ` B = {} \<and> front_tickFree t2\<close>
      then obtain t1 t2
        where ** : \<open>s = ev a # t1 @ t2\<close> \<open>t1 \<in> \<D> (P a)\<close> \<open>tickFree t1\<close>
                   \<open>set t1 \<inter> ev ` B = {}\<close> \<open>front_tickFree t2\<close> by blast
      have *** : \<open>ev a # t1 \<in> \<D> (Mprefix A P) \<and> tickFree (ev a # t1) \<and>
                  set (ev a # t1) \<inter> ev ` B = {}\<close>
        by (simp add: D_Mprefix image_iff "*"(1) "**"(2, 3, 4) \<open>a \<notin> B\<close>)
      show \<open>s \<in> \<D> ?lhs\<close>
        by (simp add: D_Throw) (metis "**"(1, 5) "***" append_Cons)
    next
      assume \<open>\<exists>t1 b t2. s = ev a # t1 @ ev b # t2 \<and> t1 @ [ev b] \<in> \<T> (P a) \<and>
                        set t1 \<inter> ev ` B = {} \<and> b \<in> B \<and> t2 \<in> \<D> (Q b)\<close>
      then obtain t1 b t2
        where ** : \<open>s = ev a # t1 @ ev b # t2\<close> \<open>t1 @ [ev b] \<in> \<T> (P a)\<close>
                   \<open>set t1 \<inter> ev ` B = {}\<close> \<open>b \<in> B\<close> \<open>t2 \<in> \<D> (Q b)\<close> by blast
      have *** : \<open>(ev a # t1) @ [ev b] \<in> \<T> (Mprefix A P) \<and> set (ev a # t1) \<inter> ev ` B = {}\<close>
        by (simp add: T_Mprefix image_iff "*"(1) "**"(2, 3) \<open>a \<notin> B\<close>)
      show \<open>s \<in> \<D> ?lhs\<close>
        by (simp add: D_Throw) (metis "**"(1, 4, 5) "***" append_Cons)
    qed
  qed
next
  fix s X
  assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
  assume \<open>(s, X) \<in> \<F> ?lhs\<close>
  then consider \<open>(s, X) \<in> \<F> (Mprefix A P)\<close> \<open>set s \<inter> ev ` B = {}\<close>
      | \<open>s \<in> \<D> ?lhs\<close>
      | \<open>\<exists>t1 b t2. s = t1 @ ev b # t2 \<and> t1 @ [ev b] \<in> \<T> (Mprefix A P) \<and> 
                   set t1 \<inter> ev ` B = {} \<and> b \<in> B \<and> (t2, X) \<in> \<F> (Q b)\<close>
    by (simp add: F_Throw D_Throw) blast
  thus \<open>(s, X) \<in> \<F> ?rhs\<close>
  proof cases
    show \<open>(s, X) \<in> \<F> (Mprefix A P) \<Longrightarrow> set s \<inter> ev ` B = {} \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
      by (simp add: F_Mprefix F_Throw)
         (metis disjoint_iff hd_in_set imageI list.set_sel(2))
  next
    show \<open>s \<in> \<D> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
      using same_div D_F by blast
  next
    assume  \<open>\<exists>t1 b t2. s = t1 @ ev b # t2 \<and> t1 @ [ev b] \<in> \<T> (Mprefix A P) \<and> 
                       set t1 \<inter> ev ` B = {} \<and> b \<in> B \<and> (t2, X) \<in> \<F> (Q b)\<close>
    then obtain t1 b t2
      where * : \<open>s = t1 @ ev b # t2\<close> \<open>t1 @ [ev b] \<in> \<T> (Mprefix A P)\<close>
                \<open>set t1 \<inter> ev ` B = {}\<close> \<open>b \<in> B\<close> \<open>(t2, X) \<in> \<F> (Q b)\<close> by blast
    show \<open>(s, X) \<in> \<F> ?rhs\<close>
    proof (cases t1) 
      from "*"(2) show \<open>t1 = [] \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
        by (auto simp add: F_Mprefix T_Mprefix F_Throw "*"(1, 4, 5))
    next
      fix a t1'
      assume \<open>t1 = a # t1'\<close>
      then obtain a' where \<open>t1 = ev a' # t1'\<close> (* a = ev a' *)
        by (metis "*"(2) append_single_T_imp_tickFree event.exhaust tickFree_Cons)
      with "*"(2, 3, 5) show \<open>(s, X) \<in> \<F> ?rhs\<close>
        by (auto simp add: F_Mprefix T_Mprefix F_Throw "*"(1, 4))
    qed
  qed
next
  show \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for s X
  proof (cases s)
    show \<open>s = [] \<Longrightarrow> (s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
      by (simp add: F_Mprefix F_Throw)
  next
    fix a s'
    assume assms : \<open>s = a # s'\<close> \<open>(s, X) \<in> \<F> ?rhs\<close>
    from assms(2) obtain a'
      where * : \<open>a' \<in> A\<close> \<open>s = ev a' # s'\<close>
                \<open>(s', X) \<in> \<F> (if a' \<in> B then Q a' else Throw (P a') B Q)\<close>
      by (simp add: assms(1) F_Mprefix) blast
    show \<open>(s, X) \<in> \<F> ?lhs\<close>
    proof (cases \<open>a' \<in> B\<close>) 
      assume \<open>a' \<in> B\<close>
      hence ** : \<open>[] @ [ev a'] \<in> \<T> (Mprefix A P) \<and>
                 set [] \<inter> ev ` B = {} \<and> (s', X) \<in> \<F> (Q a')\<close>
        using "*"(3) by (simp add: T_Mprefix Nil_elem_T "*"(1))
      show \<open>(s, X) \<in> \<F> ?lhs\<close>
        by (simp add: F_Throw) (metis "*"(2) "**" \<open>a' \<in> B\<close> append_Nil)
    next
      assume \<open>a' \<notin> B\<close>
      then consider  \<open>(s', X) \<in> \<F> (P a')\<close> \<open>set s' \<inter> ev ` B = {}\<close>
        | \<open>\<exists>t1 t2. s' = t1 @ t2 \<and> t1 \<in> \<D> (P a') \<and> tickFree t1 \<and>
                      set t1 \<inter> ev ` B = {} \<and> front_tickFree t2\<close>
        | \<open>\<exists>t1 b t2. s' = t1 @ ev b # t2 \<and> t1 @ [ev b] \<in> \<T> (P a') \<and>
                        set t1 \<inter> ev ` B = {} \<and> b \<in> B \<and> (t2, X) \<in> \<F> (Q b)\<close>
        using "*"(3) by (simp add: F_Throw D_Throw) blast
      thus \<open>(s, X) \<in> \<F> ?lhs\<close>
      proof cases
        show \<open>(s', X) \<in> \<F> (P a') \<Longrightarrow> set s' \<inter> ev ` B = {} \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
          by (simp add: F_Mprefix F_Throw "*"(1, 2) \<open>a' \<notin> B\<close> image_iff)
      next
        assume \<open>\<exists>t1 t2. s' = t1 @ t2 \<and> t1 \<in> \<D> (P a') \<and> tickFree t1 \<and>
                        set t1 \<inter> ev ` B = {} \<and> front_tickFree t2\<close>
        then obtain t1 t2
          where ** : \<open>s' = t1 @ t2\<close> \<open>t1 \<in> \<D> (P a')\<close> \<open>tickFree t1\<close>
                     \<open>set t1 \<inter> ev ` B = {}\<close> \<open>front_tickFree t2\<close> by blast
        have *** : \<open>s = (ev a' # t1) @ t2 \<and> ev a' # t1 \<in> \<D> (Mprefix A P) \<and>
                    tickFree (ev a' # t1) \<and> set (ev a' # t1) \<inter> ev ` B = {}\<close>
          by (simp add: D_Mprefix \<open>a' \<notin> B\<close> image_iff "*"(1, 2) "**"(1, 2, 3, 4))
        show \<open>(s, X) \<in> \<F> ?lhs\<close>
          by (simp add: F_Throw F_Mprefix) (metis "**"(5) "***")
      next
        assume \<open>\<exists>t1 b t2. s' = t1 @ ev b # t2 \<and> t1 @ [ev b] \<in> \<T> (P a') \<and>
                          set t1 \<inter> ev ` B = {} \<and> b \<in> B \<and> (t2, X) \<in> \<F> (Q b)\<close>
        then obtain t1 b t2
          where ** : \<open>s' = t1 @ ev b # t2\<close> \<open>t1 @ [ev b] \<in> \<T> (P a')\<close>
                     \<open>set t1 \<inter> ev ` B = {}\<close> \<open>b \<in> B\<close> \<open>(t2, X) \<in> \<F> (Q b)\<close> by blast
        have *** : \<open>s = (ev a' # t1) @ ev b # t2 \<and> set (ev a' # t1) \<inter> ev ` B = {} \<and>
                    (ev a' # t1) @ [ev b] \<in> \<T> (Mprefix A P)\<close>
          by (simp add: T_Mprefix \<open>a' \<notin> B\<close> image_iff "*"(1, 2) "**"(1, 2, 3))
        show \<open>(s, X) \<in> \<F> ?lhs\<close>
          by (simp add: F_Throw F_Mprefix) (metis "**"(4, 5) "***")
      qed
    qed
  qed
qed


corollary Throw_prefix: \<open>(a \<rightarrow> P) \<Theta> b \<in> B. Q b =
                         (a \<rightarrow> (if a \<in> B then Q a else (P \<Theta> b \<in> B. Q b)))\<close>
  unfolding write0_def by (auto simp add: Throw_Mprefix intro: mono_Mprefix_eq)

corollary Throw_Mndetprefix:
  \<open>(\<sqinter>a \<in> A \<rightarrow> P a) \<Theta> b \<in> B. Q b =
   \<sqinter>a \<in> A \<rightarrow> (if a \<in> B then Q a else P a \<Theta> b \<in> B. Q b)\<close>
  apply (subst Mndetprefix_GlobalNdet)
  apply (simp add: Throw_GlobalNdet(1) Throw_prefix)
  apply (subst Mndetprefix_GlobalNdet[symmetric])
  by simp


\<comment> \<open>We may prove some results about deadlock freeness as corollaries\<close>
   
  


subsection \<open>Continuity\<close>

lemma chain_left_Throw: \<open>chain Y \<Longrightarrow> chain (\<lambda>i. Y i \<Theta> a \<in> A. Q a)\<close>
  by (simp add: chain_def)

lemma chain_right_Throw: \<open>chain Y \<Longrightarrow> chain (\<lambda>i. P \<Theta> a \<in> A. Y i a)\<close>
  by (simp add: chain_def fun_belowD)


lemma cont_left_prem_Throw :
  \<open>(\<Squnion> i. Y i) \<Theta> a \<in> A. Q a = (\<Squnion> i. Y i \<Theta> a \<in> A. Q a)\<close>
  (is \<open>?lhs = ?rhs\<close>) if chain : \<open>chain Y\<close>
proof (subst Process_eq_spec, safe)
 show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close> for s
   by (auto simp add: limproc_is_thelub chain
                      chain_left_Throw D_Throw T_LUB D_LUB)
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
    by (simp add: limproc_is_thelub D_LUB chain_left_Throw chain)
  hence \<open>\<forall>i. S i \<noteq> {}\<close>
    by (simp add: S_def D_Throw)
       (metis ftF front_tickFree_mono list.distinct(1))
  moreover have \<open>finite (S 0)\<close>
    unfolding S_def
    apply (rule finite_subset[of _ \<open>{t1. \<exists>t2. s = t1 @ t2}\<close>], blast)
    by (metis prefixes_fin)
  moreover have \<open>\<forall>i. S (Suc i) \<subseteq> S i\<close>
    unfolding S_def apply (intro allI Un_mono subsetI; simp)
    by (metis in_mono le_approx1 po_class.chainE chain)
       (metis le_approx_lemma_T po_class.chain_def subset_eq chain)
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
      by (simp add: S_def) (meson D_T front_tickFree_single is_processT7_S)
    with "*" "**"(1, 3, 4) show \<open>s \<in> \<D> ?lhs\<close>
      by (simp add: S_def D_Throw limproc_is_thelub chain T_LUB) blast
  next
    case False
    with "*" have \<open>\<forall>i. \<exists>t2. s = t1 @ t2 \<and> t1 \<in> \<D> (Y i) \<and> front_tickFree t2\<close>
      by (simp add: S_def) blast
    hence \<open>\<exists>t2. s = t1 @ t2 \<and> (\<forall>i. t1 \<in> \<D> (Y i)) \<and> front_tickFree t2\<close> by blast
    with "*" show \<open>s \<in> \<D> ?lhs\<close>
      by (simp add: S_def D_Throw limproc_is_thelub chain D_LUB) blast
  qed
next
  show \<open>(s, X) \<in> \<F> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for s X
    by (auto simp add: limproc_is_thelub chain chain_left_Throw 
                       F_Throw F_LUB T_LUB D_LUB)
next
  fix s X
  define S
    where \<open>S i \<equiv> {t1. s = t1 \<and> (t1, X) \<in> \<F> (Y i) \<and> set t1 \<inter> ev ` A = {}} \<union>
                 {t1. \<exists>t2. s = t1 @ t2 \<and> t1 \<in> \<D> (Y i) \<and> tickFree t1 \<and>
                           set t1 \<inter> ev ` A = {} \<and> front_tickFree t2} \<union>
                 {t1. \<exists>a t2. s = t1 @ ev a # t2 \<and> t1 @ [ev a] \<in> \<T> (Y i) \<and>
                             set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> (t2, X) \<in> \<F> (Q a)}\<close> for i
  assume \<open>(s, X) \<in> \<F> ?rhs\<close>
  hence ftF: \<open>front_tickFree s\<close> using is_processT2 by blast
  from \<open>(s, X) \<in> \<F> ?rhs\<close> have \<open>(s, X) \<in> \<F> (Y i \<Theta> a \<in> A. Q a)\<close> for i
    by (simp add: limproc_is_thelub F_LUB chain_left_Throw chain)

  hence \<open>\<forall>i. S i \<noteq> {}\<close> by (simp add: S_def F_Throw, safe; simp, blast)
  moreover have \<open>finite (S 0)\<close>
    unfolding S_def
    apply (intro finite_UnI)
    apply (all \<open>rule finite_subset[of _ \<open>{t1. \<exists>t2. s = t1 @ t2}\<close>], blast\<close>)
    by (metis prefixes_fin)+
  moreover have \<open>\<forall>i. S (Suc i) \<subseteq> S i\<close>
    unfolding S_def apply (intro allI Un_mono subsetI; simp)
    subgoal by (meson is_processT8 po_class.chainE proc_ord2a chain)
    subgoal by (metis in_mono le_approx1 po_class.chainE chain)
    by (metis le_approx_lemma_T po_class.chain_def subset_eq chain)
  ultimately have \<open>(\<Inter>i. S i) \<noteq> {}\<close>
    by (rule Inter_nonempty_finite_chained_sets)
  then obtain t1 where * : \<open>\<forall>i. t1 \<in> S i\<close> 
    by (meson INT_iff ex_in_conv iso_tuple_UNIV_I)
  show \<open>(s, X) \<in> \<F> ?lhs\<close>
  proof (cases \<open>\<exists>j a t2. s = t1 @ ev a # t2 \<and> t1 @ [ev a] \<in> \<T> (Y j) \<and>
                         a \<in> A \<and> (t2, X) \<in> \<F> (Q a)\<close>)
    case True1 : True
    then obtain j a t2 where ** : \<open>s = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> (Y j)\<close>
                                  \<open>a \<in> A\<close> \<open>(t2, X) \<in> \<F> (Q a)\<close> by blast
    from "*" "**"(1) have \<open>\<forall>i. t1 @ [ev a] \<in> \<T> (Y i)\<close>
      by (simp add: S_def) (meson D_T front_tickFree_single is_processT7)
    with "*" "**"(1, 3, 4) show \<open>(s, X) \<in> \<F> ?lhs\<close>
      by (simp add: S_def F_Throw limproc_is_thelub chain T_LUB) blast
  next
    case False1 : False
    show \<open>(s, X) \<in> \<F> ?lhs\<close>
    proof (cases \<open>\<forall>i. t1 \<in> \<D> (Y i)\<close>)
      case True2 : True
      with "*" show \<open>(s, X) \<in> \<F> ?lhs\<close>
        by (simp add: S_def F_Throw limproc_is_thelub chain)
           (metis D_LUB_2 append_Nil2 front_tickFree_mono ftF process_charn chain)
    next
      case False2 : False
      then obtain j where \<open>t1 \<notin> \<D> (Y j)\<close> by blast
      with False1 "*" have ** : \<open>s = t1 \<and> (t1, X) \<in> \<F> (Y j) \<and> set t1 \<inter> ev ` A = {}\<close>
        by (simp add: S_def) blast
      with "*" D_F have \<open>\<forall>i. (t1, X) \<in> \<F> (Y i)\<close> by (auto simp add: S_def) 
      with "**" show \<open>(s, X) \<in> \<F> ?lhs\<close>
        by (simp add: F_Throw limproc_is_thelub F_LUB chain)
    qed
  qed
qed
 

lemma cont_right_prem_Throw : 
  \<open>P \<Theta> a \<in> A. (\<Squnion> i. Y i a) = (\<Squnion> i. P \<Theta> a \<in> A. Y i a)\<close>
  (is \<open>?lhs = ?rhs\<close>) if chain : \<open>chain Y\<close>
proof (subst Process_eq_spec, safe)
  show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close> for s
    by (simp add: limproc_is_thelub chain chain_right_Throw 
                       ch2ch_fun[OF chain] D_Throw D_LUB) blast
next
  fix s
  assume \<open>s \<in> \<D> ?rhs\<close>
  define S
    where \<open>S i \<equiv> {t1. \<exists>t2. s = t1 @ t2 \<and> t1 \<in> \<D> P \<and> tickFree t1 \<and>
                           set t1 \<inter> ev ` A = {} \<and> front_tickFree t2} \<union>
                 {t1. \<exists>a t2. s = t1 @ ev a # t2 \<and> t1 @ [ev a] \<in> \<T> P \<and>
                             set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> t2 \<in> \<D> (Y i a)}\<close> for i
  assume \<open>s \<in> \<D> ?rhs\<close>
  hence \<open>s \<in> \<D> (P \<Theta> a \<in> A. Y i a)\<close> for i
    by (simp add: limproc_is_thelub D_LUB chain_right_Throw chain)
  hence \<open>\<forall>i. S i \<noteq> {}\<close> by (simp add: S_def D_Throw) metis
  moreover have \<open>finite (S 0)\<close>
    unfolding S_def
    apply (rule finite_subset[of _ \<open>{t1. \<exists>t2. s = t1 @ t2}\<close>], blast)
    by (metis prefixes_fin)
  moreover have \<open>\<forall>i. S (Suc i) \<subseteq> S i\<close>
    unfolding S_def apply (intro allI Un_mono subsetI; simp)
    by (metis fun_belowD le_approx1 po_class.chainE subset_iff chain)
  ultimately have \<open>(\<Inter>i. S i) \<noteq> {}\<close>
    by (rule Inter_nonempty_finite_chained_sets)
  then obtain t1 where \<open>\<forall>i. t1 \<in> S i\<close> 
    by (meson INT_iff ex_in_conv iso_tuple_UNIV_I)
  then consider \<open>t1 \<in> \<D> P\<close> \<open>tickFree t1\<close>
                \<open>set t1 \<inter> ev ` A = {}\<close> \<open>\<exists>t2. s = t1 @ t2 \<and> front_tickFree t2\<close>
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
      by (simp add: D_Throw limproc_is_thelub chain ch2ch_fun D_LUB) blast
  qed
next
  show \<open>(s, X) \<in> \<F> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for s X
    by (simp add: limproc_is_thelub chain chain_right_Throw
                  ch2ch_fun[OF chain] F_Throw F_LUB T_LUB D_LUB) blast
next
  fix s X
  define S
    where \<open>S i \<equiv> {t1. s = t1 \<and> (t1, X) \<in> \<F> P \<and> set t1 \<inter> ev ` A = {}} \<union>
                 {t1. \<exists>t2. s = t1 @ t2 \<and> t1 \<in> \<D> P \<and> tickFree t1 \<and>
                           set t1 \<inter> ev ` A = {} \<and> front_tickFree t2} \<union>
                 {t1. \<exists>a t2. s = t1 @ ev a # t2 \<and> t1 @ [ev a] \<in> \<T> P \<and>
                             set t1 \<inter> ev ` A = {} \<and> a \<in> A \<and> (t2, X) \<in> \<F> (Y i a)}\<close> for i
  assume \<open>(s, X) \<in> \<F> ?rhs\<close>
  hence \<open>(s, X) \<in> \<F> (P \<Theta> a \<in> A. Y i a)\<close> for i
    by (simp add: limproc_is_thelub F_LUB chain_right_Throw chain)
  hence \<open>\<forall>i. S i \<noteq> {}\<close> by (simp add: S_def F_Throw, safe; simp, blast)
  moreover have \<open>finite (S 0)\<close>
    unfolding S_def
    apply (intro finite_UnI)
    apply (all \<open>rule finite_subset[of _ \<open>{t1. \<exists>t2. s = t1 @ t2}\<close>], blast\<close>)
    by (metis prefixes_fin)+
  moreover have \<open>\<forall>i. S (Suc i) \<subseteq> S i\<close>
    unfolding S_def apply (intro allI Un_mono subsetI; simp)
    by (metis NF_ND fun_below_iff po_class.chain_def proc_ord2a chain)
  ultimately have \<open>(\<Inter>i. S i) \<noteq> {}\<close>
    by (rule Inter_nonempty_finite_chained_sets)
  then obtain t1 where \<open>\<forall>i. t1 \<in> S i\<close>
    by (meson INT_iff ex_in_conv iso_tuple_UNIV_I)
  then consider \<open>s = t1 \<and> (t1, X) \<in> \<F> P\<close> \<open>set t1 \<inter> ev ` A = {}\<close>
    | \<open>\<exists>t2. s = t1 @ t2 \<and> t1 \<in> \<D> P \<and> tickFree t1 \<and> 
            set t1 \<inter> ev ` A = {} \<and> front_tickFree t2\<close>
    | \<open>set t1 \<inter> ev ` A = {}\<close> 
      \<open>\<forall>i. \<exists>a t2. s = t1 @ ev a # t2 \<and> t1 @ [ev a] \<in> \<T> P \<and> a \<in> A \<and> (t2, X) \<in> \<F> (Y i a)\<close>
    by (simp add: S_def) blast
  thus \<open>(s, X) \<in> \<F> ?lhs\<close>
  proof cases
    show \<open>s = t1 \<and> (t1, X) \<in> \<F> P \<Longrightarrow> set t1 \<inter> ev ` A = {} \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
      by (simp add: F_Throw)
  next
    show \<open>\<exists>t2. s = t1 @ t2 \<and> t1 \<in> \<D> P \<and> tickFree t1 \<and> 
               set t1 \<inter> ev ` A = {} \<and> front_tickFree t2 \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
      by (simp add: F_Throw) blast
  next
    assume assms: \<open>set t1 \<inter> ev ` A = {}\<close>
                  \<open>\<forall>i. \<exists>a t2. s = t1 @ ev a # t2 \<and> t1 @ [ev a] \<in> \<T> P \<and>
                              a \<in> A \<and> (t2, X) \<in> \<F> (Y i a)\<close>
    from this(2) obtain a t2
      where * : \<open>s = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close> \<open>a \<in> A\<close> by blast
    with assms(2) have \<open>\<forall>i. (t2, X) \<in> \<F> (Y i a)\<close> by blast
    with "*"(1, 2, 3) assms(1) show \<open>(s, X) \<in> \<F> ?lhs\<close>
      by (simp add: F_Throw limproc_is_thelub ch2ch_fun chain F_LUB) blast
  qed
qed


lemma Throw_cont[simp] : 
  assumes cont_f : \<open>cont f\<close> and cont_g : \<open>\<forall>a. cont (g a)\<close>
  shows \<open>cont (\<lambda>x. f x \<Theta> a \<in> A. g a x)\<close>
proof -
  have * : \<open>cont (\<lambda>y. y \<Theta> a \<in> A. g a x)\<close> for x
    by (rule contI2, rule monofunI, solves simp, simp add: cont_left_prem_Throw)
  have \<open>cont (Throw y A)\<close> for y
    by (simp add: contI2 cont_right_prem_Throw fun_belowD lub_fun monofunI)
  hence ** : \<open>cont (\<lambda>x. y \<Theta> a \<in> A. g a x)\<close> for y
    by (rule cont_compose) (simp add: cont_g)
  show ?thesis by (fact cont_apply[OF cont_f "*" "**"])
qed

end