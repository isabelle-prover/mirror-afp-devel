(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff, Lina Ye.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : Hiding operator
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


chapter\<open>The Hiding Operator\<close>

(*<*)
theory  Hiding
  imports Process
begin
  (*>*)

section\<open>Preliminaries : primitives and lemmas\<close>

abbreviation \<open>trace_hide t A \<equiv> filter (\<lambda>x. x \<notin> A) t\<close>

lemma Hiding_tickFree : \<open>tF (trace_hide s (ev ` A)) \<longleftrightarrow> tF s\<close>
  by (auto simp add: tickFree_def)

lemma Hiding_front_tickFree : \<open>ftF s \<Longrightarrow> ftF (trace_hide s (ev ` A))\<close>
  apply (induct s; simp add: image_iff front_tickFree_Cons_iff)
  by (metis (no_types, lifting) filter.simps(1) front_tickFree_charn)

lemma trace_hide_union: \<open>trace_hide t (A \<union> B) = trace_hide (trace_hide t A) B\<close> by simp


lemma trace_hide_ev_union [simp] :
  \<open>trace_hide t (ev ` (A \<union> B)) = trace_hide (trace_hide t (ev ` A)) (ev ` B)\<close>
  apply (fold trace_hide_union)
  apply (rule arg_cong[where f = \<open>\<lambda>S. trace_hide t S\<close>])
  by blast


abbreviation isInfHiddenRun :: \<open>[nat \<Rightarrow> ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k list, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a set] \<Rightarrow> bool\<close>
  where \<open>isInfHiddenRun f P A \<equiv> strict_mono f \<and> (\<forall>i. f i \<in> \<T> P) \<and> 
                                (\<forall>i. trace_hide (f i) (ev ` A) = trace_hide (f 0) (ev ` A))\<close>

lemma isInfHiddenRun_1 :
  \<open>isInfHiddenRun f P A \<longleftrightarrow> strict_mono f \<and> (\<forall>i. f i \<in> \<T> P) \<and>
                            (\<forall>i. \<exists>t. f i = f 0 @ t \<and> set t \<subseteq> ev ` A)\<close>
proof (intro iffI conjI; elim conjE, assumption?)
  assume * : \<open>strict_mono f\<close> \<open>\<forall>i. trace_hide (f i) (ev ` A) = trace_hide (f 0) (ev ` A)\<close>
  show \<open>\<forall>i. \<exists>t. f i = f 0 @ t \<and> set t \<subseteq> ev ` A\<close>
  proof (rule allI)
    fix i
    from "*"(1) obtain t where \<open>f i = f 0 @ t\<close>
      by (meson prefixE less_eq_nat.simps(1) strict_mono_less_eq)
    with "*"(2)[THEN spec, of i] have \<open>set t \<subseteq> ev ` A\<close>
      by simp (metis empty_filter_conv subset_code(1))
    with \<open>f i = f 0 @ t\<close> show \<open>\<exists>t. f i = f 0 @ t \<and> set t \<subseteq> ev ` A\<close> by blast
  qed
next
  assume * : \<open>\<forall>i. \<exists>t. f i = f 0 @ t \<and> set t \<subseteq> ev ` A\<close>
  show \<open>\<forall>i. trace_hide (f i) (ev ` A) = trace_hide (f 0) (ev ` A)\<close>
  proof (rule allI)
    fix i
    from "*"[rule_format, of i] show \<open>trace_hide (f i) (ev ` A) = trace_hide (f 0) (ev ` A)\<close>
      by (elim exE, simp) (meson filter_False in_mono)
  qed
qed


abbreviation div_hide :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> 'a set \<Rightarrow> ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k list set\<close>
  where \<open>div_hide P A \<equiv> {s. \<exists>t u. ftF u \<and> tF t \<and>
                                   s = trace_hide t (ev ` A) @ u \<and> 
                                   (t \<in> \<D> P \<or> (\<exists>f. isInfHiddenRun f P A \<and> t \<in> range f))}\<close>

lemma inf_hidden:
  \<open>\<exists>f. isInfHiddenRun f P A \<and> s \<in> range f\<close>
  if \<open>\<forall>t. trace_hide t (ev ` A) = trace_hide s (ev ` A) \<longrightarrow> (t, ev ` A) \<notin> \<F> P\<close> and \<open>s \<in> \<T> P\<close>
proof (rule exI)
  define f where \<open>f \<equiv> rec_nat s (\<lambda>i t. let e = SOME e. e \<in> ev ` A \<and> t @ [e] \<in> \<T> P in t @ [e])\<close>
  have \<open>strict_mono f\<close> by (simp add: f_def strict_mono_def lift_Suc_mono_less_iff)
  moreover have \<open>s \<in> range f\<close> unfolding f_def by (metis (no_types, lifting) nat.rec(1) range_eqI)
  moreover have \<open>f i \<in> \<T> P \<and> trace_hide (f i) (ev ` A) = trace_hide s (ev ` A)\<close> for i
  proof (induct i)
    show \<open>f 0 \<in> \<T> P \<and> trace_hide (f 0) (ev ` A) = trace_hide s (ev ` A)\<close>
      by (simp add: f_def that(2))
  next
    fix i
    assume hyp : \<open>f i \<in> \<T> P \<and> trace_hide (f i) (ev ` A) = trace_hide s (ev ` A)\<close>
    from is_processT5_S7[OF hyp[THEN conjunct1] that(1)[rule_format, OF hyp[THEN conjunct2]]]
    obtain e where $ : \<open>e \<in> ev ` A\<close> \<open>f i @ [e] \<in> \<T> P\<close> by blast
    have \<open>f (Suc i) = (let e = SOME e. e \<in> ev ` A \<and> f i @ [e] \<in> \<T> P in  f i @ [e])\<close>
      by (simp add: f_def)
    thus \<open>f (Suc i) \<in> \<T> P \<and> trace_hide (f (Suc i)) (ev ` A) = trace_hide s (ev ` A)\<close>
      by (simp add: hyp[THEN conjunct2]) (metis (no_types, lifting) "$" someI_ex)
  qed
  ultimately show \<open>isInfHiddenRun f P A \<and> s \<in> range f\<close> by simp
qed


lemma trace_hide_append :
  \<open>s @ t = trace_hide u (ev ` A) \<Longrightarrow>
   \<exists>s' t'. u = s' @ t' \<and> s = trace_hide s' (ev ` A) \<and> t = trace_hide t' (ev ` A)\<close>
proof (induct u arbitrary: s t)
  case Nil
  thus ?case by simp
next
  case (Cons e u)
  show ?case
  proof (cases \<open>e \<in> ev ` A\<close>)
    assume \<open>e \<in> ev ` A\<close>
    with Cons.prems have \<open>s @ t = trace_hide u (ev ` A)\<close> by simp
    with Cons.hyps obtain s' t' where 
      \<open>u = s' @ t'\<close> \<open>s = trace_hide s' (ev ` A)\<close> \<open>t = trace_hide t' (ev ` A)\<close> by blast
    hence \<open>e # u = (e # s') @ t' \<and> s = trace_hide (e # s') (ev ` A) \<and> t = trace_hide t' (ev ` A)\<close>
      by (simp add: \<open>e \<in> ev ` A\<close>)
    thus ?case by blast
  next
    assume \<open>e \<notin> ev ` A\<close>
    with Cons.prems consider \<open>s = []\<close> \<open>t \<noteq> []\<close> \<open>hd t = e\<close> \<open>[] @ tl t = trace_hide u (ev ` A)\<close>
      | \<open>s \<noteq> []\<close> \<open>hd s = e\<close> \<open>tl s @ t = trace_hide u (ev ` A)\<close> by (cases s) simp_all
    thus ?case
    proof cases
      show \<open>\<lbrakk>s = []; t \<noteq> []; hd t = e; [] @ tl t = trace_hide u (ev ` A)\<rbrakk> \<Longrightarrow> ?case\<close>
        by (drule Cons.hyps) (metis Cons.prems append_Nil filter.simps(1))
    next
      show \<open>\<lbrakk>s \<noteq> []; hd s = e; tl s @ t = trace_hide u (ev ` A)\<rbrakk> \<Longrightarrow> ?case\<close>
        by (drule Cons.hyps) (metis Cons.prems Cons_eq_appendI append_same_eq filter_append)
    qed
  qed
qed



section\<open>The Hiding Operator Definition\<close>

lift_definition Hiding  :: \<open>[('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k ,'a set] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (infixl \<open>\\<close> 69)
  is \<open>\<lambda>P A. ({(s, X). \<exists>t. s = trace_hide t (ev ` A) \<and> (t, X \<union> ev ` A) \<in> \<F> P} \<union>
             {(s, X). s \<in> div_hide P A},
             div_hide P A)\<close>
proof - 
  show \<open>?thesis P A\<close> (is \<open>is_process(?f, div_hide P A)\<close>) for P and A
  proof (unfold is_process_def FAILURES_def DIVERGENCES_def fst_conv snd_conv, intro conjI allI impI)
    from inf_hidden[of A \<open>[]\<close> P] show \<open>([], {}) \<in> ?f\<close>
      by simp (metis filter.simps(1) tickFree_Nil)
  next
    show \<open>(s, X) \<in> ?f \<Longrightarrow> ftF s\<close> for s X
      by simp (metis F_imp_front_tickFree Hiding_front_tickFree Hiding_tickFree 
          front_tickFree_append_iff tickFree_imp_front_tickFree)
  next
    show \<open>(s @ t, {}) \<in> ?f \<Longrightarrow> (s, {}) \<in> ?f\<close> for s t
    proof (induct t rule: rev_induct)
      case Nil
      then show ?case by auto
    next
      case (snoc e t)
      from snoc.prems consider u where \<open>s @ t @ [e] = trace_hide u (ev ` A)\<close> \<open>(u, ev ` A) \<in> \<F> P\<close>
        | u v where \<open>ftF v\<close> \<open>tF u\<close> \<open>s @ t @ [e] = trace_hide u (ev ` A) @ v\<close>
          \<open>u \<in> \<D> P \<or> (\<exists>f. isInfHiddenRun f P A \<and> u \<in> range f)\<close>
        by simp blast
      thus ?case
      proof cases
        fix u assume \<open>s @ t @ [e] = trace_hide u (ev ` A)\<close> \<open>(u, ev ` A) \<in> \<F> P\<close>
        from this(1) obtain u' u'' where \<open>u = u' @ u''\<close> \<open>s @ t = trace_hide u' (ev ` A)\<close>
          by (metis append_assoc trace_hide_append)
        have \<open>(s @ t, {}) \<in> ?f\<close>
        proof (cases \<open>\<exists>t. trace_hide t (ev ` A) = trace_hide u' (ev ` A) \<and> (t, ev ` A) \<in> \<F> P\<close>)
          show \<open>\<exists>t. trace_hide t (ev ` A) = trace_hide u' (ev ` A) \<and> (t, ev ` A) \<in> \<F> P \<Longrightarrow>
                    (s @ t, {}) \<in> ?f\<close>
            by (simp add: \<open>s @ t = trace_hide u' (ev ` A)\<close>) metis
        next
          assume * : \<open>\<nexists>t. trace_hide t (ev ` A) = trace_hide u' (ev ` A) \<and> (t, ev ` A) \<in> \<F> P\<close>
          from this[simplified, THEN inf_hidden] obtain f where \<open>isInfHiddenRun f P A \<and> u' \<in> range f\<close>
            using T_F_spec \<open>(u, ev ` A) \<in> \<F> P\<close> \<open>u = u' @ u''\<close> is_processT3 is_processT4_empty by blast
          hence \<open>s @ t \<in> div_hide P A\<close>
            by (simp add: \<open>s @ t = trace_hide u' (ev ` A)\<close>) 
              (metis F_imp_front_tickFree \<open>(u, ev ` A) \<in> \<F> P\<close> "*" \<open>u = u' @ u''\<close>
                append.right_neutral front_tickFree_Nil front_tickFree_append_iff)
          thus \<open>(s @ t, {}) \<in> ?f\<close> by simp
        qed
        from snoc.hyps[OF this] show \<open>(s, {}) \<in> ?f\<close> by blast
      next
        fix u v assume * : \<open>ftF v\<close> \<open>tF u\<close> \<open>s @ t @ [e] = trace_hide u (ev ` A) @ v\<close>
          \<open>u \<in> \<D> P \<or> (\<exists>f. isInfHiddenRun f P A \<and> u \<in> range f)\<close>
        show ?case
        proof (cases v rule: rev_cases)
          assume \<open>v = []\<close>
          with "*"(3) obtain u' u'' where \<open>u = u' @ u''\<close> \<open>s @ t = trace_hide u' (ev ` A)\<close>
            by simp (metis append_assoc trace_hide_append)
          from "*"(4) D_T have \<open>u \<in> \<T> P\<close> by blast
          have \<open>(s @ t, {}) \<in> ?f\<close>
          proof (cases \<open>\<exists>t. trace_hide t (ev ` A) = trace_hide u' (ev ` A) \<and> (t, ev ` A) \<in> \<F> P\<close>)
            show \<open>\<exists>t. trace_hide t (ev ` A) = trace_hide u' (ev ` A) \<and> (t, ev ` A) \<in> \<F> P \<Longrightarrow>
                      (s @ t, {}) \<in> ?f\<close>
              by (simp add: \<open>s @ t = trace_hide u' (ev ` A)\<close>) metis
          next
            assume * : \<open>\<nexists>t. trace_hide t (ev ` A) = trace_hide u' (ev ` A) \<and> (t, ev ` A) \<in> \<F> P\<close>
            from this[simplified, THEN inf_hidden] obtain f where \<open>isInfHiddenRun f P A \<and> u' \<in> range f\<close>
              by (metis T_F_spec \<open>u = u' @ u''\<close> \<open>u \<in> \<T> P\<close> is_processT3)
            hence \<open>s @ t \<in> div_hide P A\<close>
              by (simp add: \<open>s @ t = trace_hide u' (ev ` A)\<close>) 
                (metis (no_types, lifting) "*" append_Nil2 append_T_imp_tickFree
                  front_tickFree_Nil is_processT5_S7 list.distinct(1) rangeE)
            thus \<open>(s @ t, {}) \<in> ?f\<close> by simp
          qed
          from snoc.hyps[OF this] show \<open>(s, {}) \<in> ?f\<close> by blast
        next
          fix v' e'
          assume \<open>v = v' @ [e']\<close>
          with "*" front_tickFree_dw_closed have \<open>s @ t \<in> div_hide P A\<close> by auto
          hence \<open>(s @ t, {}) \<in> ?f\<close> by simp
          from snoc.hyps[OF this] show \<open>(s, {}) \<in> ?f\<close> by blast
        qed
      qed
    qed

  next
    show $ : \<open>(s, Y) \<in> ?f \<and> X \<subseteq> Y \<Longrightarrow> (s, X) \<in> ?f\<close> for s X Y
      by simp (metis is_processT4 subset_iff_psubset_eq sup.mono)
  next
    fix s X Y assume * : \<open>(s, X) \<in> ?f \<and> (\<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> ?f)\<close>
    from "*"[THEN conjunct1] consider \<open>s \<in> div_hide P A\<close> 
      | u where \<open>s = trace_hide u (ev ` A)\<close> \<open>(u, X \<union> ev ` A) \<in> \<F> P\<close> by simp blast
    thus \<open>(s, X \<union> Y) \<in> ?f\<close>
    proof cases
      show \<open>s \<in> div_hide P A \<Longrightarrow> (s, X \<union> Y) \<in> ?f\<close> by simp
    next
      fix u assume \<open>s = trace_hide u (ev ` A)\<close> \<open>(u, X \<union> ev ` A) \<in> \<F> P\<close>
      show \<open>(s, X \<union> Y) \<in> ?f\<close>
      proof (cases \<open>s \<in> div_hide P A\<close>)
        show \<open>s \<in> div_hide P A \<Longrightarrow> (s, X \<union> Y) \<in> ?f\<close> by simp
      next
        assume \<open>s \<notin> div_hide P A\<close>  
        have \<open>(u, X \<union> Y \<union> ev ` A) \<in> \<F> P\<close>
        proof (rule ccontr)
          assume \<open>(u, X \<union> Y \<union> ev ` A) \<notin> \<F> P\<close>
          hence \<open>(u, X \<union> ev ` A \<union> Y) \<notin> \<F> P\<close> by (metis sup.assoc sup_commute)
          from is_processT5_S7'[OF \<open>(u, X \<union> ev ` A) \<in> \<F> P\<close> this] obtain c
            where \<open>c \<in> Y\<close> \<open>c \<notin> X\<close> \<open>c \<notin> ev ` A\<close> \<open>u @ [c] \<in> \<T> P\<close> by blast
          show False
          proof (cases \<open>\<exists>t. trace_hide t (ev ` A) = trace_hide (u @ [c]) (ev ` A) \<and> (t, ev ` A) \<in> \<F> P\<close>)
            show \<open>\<exists>t. trace_hide t (ev ` A) = trace_hide (u @ [c]) (ev ` A) \<and> (t, ev ` A) \<in> \<F> P \<Longrightarrow> False\<close>
              using "*" \<open>c \<in> Y\<close> \<open>c \<notin> ev ` A\<close> \<open>s = trace_hide u (ev ` A)\<close> by force
          next
            assume \<open>\<nexists>t. trace_hide t (ev ` A) = trace_hide (u @ [c]) (ev ` A) \<and> (t, ev ` A) \<in> \<F> P\<close>
            hence \<open>\<forall>t. trace_hide t (ev ` A) = trace_hide (u @ [c]) (ev ` A)
                       \<longrightarrow> (t, ev ` A) \<notin> \<F> P\<close> by simp
            from inf_hidden[OF this \<open>u @ [c] \<in> \<T> P\<close>] have \<open>s @ [c] \<in> div_hide P A\<close>
              (* TODO : break this smt *)
              by (smt (verit, ccfv_threshold) Prefix_Order.strict_prefix_simps(1)
                  Prefix_Order.strict_prefix_simps(2)
                  \<open>\<nexists>t. trace_hide t (ev ` A) = trace_hide (u @ [c]) (ev ` A) \<and> (t, ev ` A) \<in> \<F> P\<close>
                  \<open>s = trace_hide u (ev ` A)\<close> \<open>s \<notin> div_hide P A\<close> \<open>u @ [c] \<in> \<T> P\<close> append_Nil2
                  append_T_imp_tickFree filter.simps(1) filter.simps(2) filter_append
                  front_tickFree_Nil is_processT5_S7 mem_Collect_eq)
            thus False using "*" \<open>c \<in> Y\<close> by blast
          qed
        qed
        thus \<open>(s, X \<union> Y) \<in> ?f\<close> by (auto simp add: \<open>s = trace_hide u (ev ` A)\<close>)
      qed
    qed
  next
    { fix s r assume \<open>s @ [\<checkmark>(r)] \<in> div_hide P A\<close>
      then obtain t u where * : \<open>ftF u\<close> \<open>tF t\<close>
        \<open>s @ [\<checkmark>(r)] = trace_hide t (ev ` A) @ u\<close>
        \<open>t \<in> \<D> P \<or> (\<exists>f. isInfHiddenRun f P A \<and> t \<in> range f)\<close> by blast
      from "*"(2, 3) have \<open>u \<noteq> []\<close>
        by (cases u; cases t rule: rev_cases; simp split: if_split_asm)
          (metis Hiding_tickFree non_tickFree_tick tickFree_append_iff)
      with "*"(2, 3) have \<open>s = trace_hide t (ev ` A) @ butlast u\<close>
        by (cases u rule: rev_cases; simp)
      moreover from "*"(1)front_tickFree_iff_tickFree_butlast tickFree_imp_front_tickFree
      have \<open>ftF (butlast u)\<close> by blast
      ultimately show \<open>s \<in> div_hide P A\<close> using "*"(2, 4) by auto
    } note local_is_processT9 = this

    fix s r X assume \<open>(s @ [\<checkmark>(r)], {}) \<in> ?f\<close>
    then consider \<open>s @ [\<checkmark>(r)] \<in> div_hide P A\<close> 
      | u where \<open>s @ [\<checkmark>(r)] = trace_hide u (ev ` A)\<close> \<open>(u, ev ` A) \<in> \<F> P\<close> by simp blast
    thus \<open>(s, X - {tick r}) \<in> ?f\<close>
    proof cases
      assume \<open>s @ [\<checkmark>(r)] \<in> div_hide P A\<close>
      with local_is_processT9 have \<open>s \<in> div_hide P A\<close> by blast
      thus \<open>(s, X - {tick r}) \<in> ?f\<close> by simp
    next
      fix u assume \<open>s @ [\<checkmark>(r)] = trace_hide u (ev ` A)\<close> \<open>(u, ev ` A) \<in> \<F> P\<close>
      from this(1) obtain u' where \<open>u = u' @ [\<checkmark>(r)]\<close> \<open>s = trace_hide u' (ev ` A)\<close>
        by (cases u rule: rev_cases; simp split: if_split_asm)
          (metis F_imp_front_tickFree Hiding_tickFree \<open>(u, ev ` A) \<in> \<F> P\<close> tickFree_append_iff
            front_tickFree_iff_tickFree_butlast non_tickFree_tick snoc_eq_iff_butlast)
      have \<open>X - {\<checkmark>(r)} \<union> ev ` A = X \<union> ev ` A - {\<checkmark>(r)}\<close> by auto
      with is_processT6_TR[OF \<open>(u, ev ` A) \<in> \<F> P\<close>[THEN F_T, unfolded \<open>u = u' @ [\<checkmark>(r)]\<close>]]
      have \<open>(u', X - {\<checkmark>(r)} \<union> ev ` A) \<in> \<F> P\<close> by presburger
      thus \<open>(s, X - {tick r}) \<in> ?f\<close> by (auto simp add: \<open>s = trace_hide u' (ev ` A)\<close>)
    qed
  next
    fix s t :: \<open>('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> assume * : \<open>s \<in> div_hide P A \<and> tF s \<and> ftF t\<close>
    from "*"[THEN conjunct1] obtain u v
      where ** : \<open>ftF v\<close> \<open>tF u\<close> \<open>s = trace_hide u (ev ` A) @ v\<close>
        \<open>u \<in> \<D> P \<or> (\<exists>f. isInfHiddenRun f P A \<and> u \<in> range f)\<close> by blast
    from "**"(3) have \<open>s @ t = trace_hide u (ev ` A) @ v @ t\<close> by simp
    moreover from "*" "**"(3) front_tickFree_append have \<open>ftF (v @ t)\<close> by auto
    ultimately show \<open>s @ t \<in> div_hide P A\<close> using "**"(2) "**"(4) by blast
  next
    show \<open>s \<in> div_hide P A \<Longrightarrow> (s, X) \<in> ?f\<close> for s X by simp
  qed
qed



section\<open>Projections\<close>

lemma F_Hiding: \<open>\<F> (P \ A) = {(s, X). \<exists>t. s = trace_hide t (ev ` A) \<and> (t, X \<union> ev ` A) \<in> \<F> P} \<union>
                             {(s, X). s \<in> div_hide P A}\<close>
  by (simp add: Failures.rep_eq Hiding.rep_eq FAILURES_def)

lemma D_Hiding: \<open>\<D> (P \ A) = div_hide P A\<close>
  by (simp add: Divergences.rep_eq Hiding.rep_eq DIVERGENCES_def)

lemma T_Hiding: \<open>\<T> (P \ A) = {trace_hide t (ev ` A) |t. (t, ev ` A) \<in> \<F> P} \<union> div_hide P A\<close>
  by (auto simp add: Traces.rep_eq TRACES_def Failures.rep_eq[symmetric] F_Hiding)
    (metis is_processT4 sup_ge2, metis sup_bot_left)

lemma Hiding_empty: \<open>P \ {} = P\<close>
  by (auto simp add: Process_eq_spec D_Hiding F_Hiding strict_mono_eq
      intro: is_processT7 is_processT8)
    (metis append.right_neutral front_tickFree_append_iff
      list.distinct(1) nonTickFree_n_frontTickFree process_charn)


lemma mem_D_imp_mem_D_Hiding: \<open>trace_hide t (ev ` A) \<in> \<D> (P \ A)\<close> if \<open>t \<in> \<D> P\<close>
proof (cases \<open>tF t\<close>)
  assume \<open>tF t\<close>
  with \<open>t \<in> \<D> P\<close> show \<open>trace_hide t (ev ` A) \<in> \<D> (P \ A)\<close>
    by (simp add: D_Hiding) (use front_tickFree_Nil in blast)
next
  assume \<open>\<not> tF t\<close>
  with \<open>t \<in> \<D> P\<close> obtain t' r where \<open>t = t' @ [\<checkmark>(r)]\<close> \<open>tF t'\<close> \<open>t' \<in> \<D> P\<close>
    by (metis D_imp_front_tickFree butlast_snoc is_processT9
        front_tickFree_iff_tickFree_butlast nonTickFree_n_frontTickFree)
  thus \<open>trace_hide t (ev ` A) \<in> \<D> (P \ A)\<close>
    by (simp add: D_Hiding) (use front_tickFree_single in blast)
qed

lemma mem_T_imp_mem_T_Hiding: \<open>trace_hide t (ev ` A) \<in> \<T> (P \ A)\<close> if \<open>t \<in> \<T> P\<close>
proof (cases \<open>\<exists>t'. trace_hide t (ev ` A) = trace_hide t' (ev ` A) \<and> (t', ev ` A) \<in> \<F> P\<close>)
  show \<open>\<exists>t'. trace_hide t (ev ` A) = trace_hide t' (ev ` A) \<and> (t', ev ` A) \<in> \<F> P
        \<Longrightarrow> trace_hide t (ev ` A) \<in> \<T> (P \ A)\<close> by (simp add: T_Hiding)
next
  assume \<open>\<nexists>t'. trace_hide t (ev ` A) = trace_hide t' (ev ` A) \<and> (t', ev ` A) \<in> \<F> P\<close>
  with inf_hidden[of A, OF _ \<open>t \<in> \<T> P\<close>] obtain f
    where \<open>isInfHiddenRun f P A\<close> \<open>t \<in> range f\<close> \<open>tF t\<close>
    by (metis T_nonTickFree_imp_decomp \<open>t \<in> \<T> P\<close> tick_T_F)
  thus \<open>trace_hide t (ev ` A) \<in> \<T> (P \ A)\<close>
    by (simp add: T_Hiding) (use front_tickFree_Nil in blast)
qed



section\<open>Continuity Rule\<close>

lemma mono_Hiding : \<open>(P \ A) \<sqsubseteq> (Q \ A)\<close> if \<open>(P::('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<sqsubseteq> Q\<close>
proof (unfold le_approx_def, intro conjI allI impI subsetI)
  from le_approx1[OF \<open>P \<sqsubseteq> Q\<close>] le_approx_lemma_T[OF \<open>P \<sqsubseteq> Q\<close>]
  show \<open>s \<in> \<D> (Q \ A) \<Longrightarrow> s \<in> \<D> (P \ A)\<close> for s
    by (simp add: D_Hiding) blast
next
  { fix s t X
    assume assms : \<open>s \<notin> \<D> (P \ A)\<close> \<open>s = trace_hide t (ev ` A)\<close>
    have \<open>t \<notin> \<D> P\<close>
    proof (cases \<open>ftF t\<close>)
      from D_imp_front_tickFree show \<open>\<not> ftF t \<Longrightarrow> t \<notin> \<D> P\<close> by blast
    next
      assume \<open>ftF t\<close>
      show \<open>t \<notin> \<D> P\<close>
      proof (cases \<open>tF t\<close>)
        from \<open>s \<notin> \<D> (P \ A)\<close> show \<open>tF t \<Longrightarrow> t \<notin> \<D> P\<close>
          by (simp add: assms(2) D_Hiding)
      next
        assume \<open>\<not> tF t\<close>
        then obtain t' r where \<open>t = t' @ [tick r]\<close>
          by (meson \<open>ftF t\<close> nonTickFree_n_frontTickFree process_charn)
        with \<open>s \<notin> \<D> (P \ A)\<close> show \<open>t \<notin> \<D> P\<close>
          by (simp add: assms(2) D_Hiding image_iff)
            (metis front_tickFree_append_iff list.distinct(1) process_charn)
      qed
    qed
  } note * = this

  fix s
  assume \<open>s \<notin> \<D> (P \ A)\<close>
  show \<open>\<R>\<^sub>a (P \ A) s = \<R>\<^sub>a (Q \ A) s\<close>
  proof (intro subset_antisym subsetI)
    fix X
    assume \<open>X \<in> \<R>\<^sub>a (P \ A) s\<close>
    with le_approx1[OF \<open>P \<sqsubseteq> Q\<close>] le_approx_lemma_T[OF \<open>P \<sqsubseteq> Q\<close>] \<open>s \<notin> \<D> (P \ A)\<close>
    obtain t where $ : \<open>s = trace_hide t (ev ` A)\<close> \<open>(t, X \<union> ev ` A) \<in> \<F> P\<close>
      by (simp add: Refusals_after_def F_Hiding D_Hiding) blast
    from "*"[OF \<open>s \<notin> \<D> (P \ A)\<close> \<open>s = trace_hide t (ev ` A)\<close>] have \<open>t \<notin> \<D> P\<close> .
    from le_approx2[OF \<open>P \<sqsubseteq> Q\<close> this] "$"
    show \<open>X \<in> \<R>\<^sub>a (Q \ A) s\<close> by (simp add: Refusals_after_def F_Hiding) blast
  next
    fix X
    assume \<open>X \<in> \<R>\<^sub>a (Q \ A) s\<close>
    with le_approx1[OF \<open>P \<sqsubseteq> Q\<close>] le_approx_lemma_T[OF \<open>P \<sqsubseteq> Q\<close>] \<open>s \<notin> \<D> (P \ A)\<close>
    obtain t where $ : \<open>s = trace_hide t (ev ` A)\<close> \<open>(t, X \<union> ev ` A) \<in> \<F> Q\<close>
      by (simp add: Refusals_after_def F_Hiding D_Hiding) blast
    from "*"[OF \<open>s \<notin> \<D> (P \ A)\<close> \<open>s = trace_hide t (ev ` A)\<close>] have \<open>t \<notin> \<D> P\<close> .
    from le_approx2[OF \<open>P \<sqsubseteq> Q\<close> this] "$"
    show \<open>X \<in> \<R>\<^sub>a (P \ A) s\<close> by (simp add: Refusals_after_def F_Hiding) blast
  qed
next
  fix s
  assume \<open>s \<in> min_elems (\<D> (P \ A))\<close>

  { fix t 
    assume assms : \<open>t \<in> \<D> P\<close> \<open>s = trace_hide t (ev ` A)\<close> \<open>tF t\<close>
    from assms(1) obtain t' t'' where \<open>t = t' @ t''\<close> and \<open>t' \<in> min_elems (\<D> P)\<close>
      by (meson min_elems_charn)
    with assms(3) elem_min_elems tickFree_append_iff
    have \<open>trace_hide t' (ev ` A) \<in> \<D> (P \ A)\<close>
      by (simp add: D_Hiding) (use front_tickFree_Nil in blast)
    from filter_append[of \<open>(\<lambda>x. x \<notin> ev ` A)\<close> t' t'', folded \<open>t = t' @ t''\<close>]
    have \<open>trace_hide t (ev ` A) = trace_hide t' (ev ` A) @ trace_hide t'' (ev ` A)\<close> .
    hence \<open>s = trace_hide t' (ev ` A)\<close>
      by (metis (no_types, lifting) assms(2) \<open>s \<in> min_elems (\<D> (P \ A))\<close>
          min_elems_no \<open>trace_hide t' (ev ` A) \<in> \<D> (P \ A)\<close> less_eq_list_def prefix_def)
    have \<open>s \<in> \<T> (Q \ A)\<close>
    proof (cases \<open>\<forall>v. trace_hide v (ev ` A) = trace_hide t' (ev ` A) \<longrightarrow> (v, ev ` A) \<notin> \<F> Q\<close>)
      assume \<open>\<forall>v. trace_hide v (ev ` A) = trace_hide t' (ev ` A) \<longrightarrow> (v, ev ` A) \<notin> \<F> Q\<close>
      from inf_hidden[OF this] have \<open>\<exists>f. isInfHiddenRun f Q A \<and> t' \<in> range f\<close>
        by (meson \<open>t' \<in> min_elems (\<D> P)\<close> in_mono le_approx_def that)
      thus \<open>s \<in> \<T> (Q \ A)\<close>
        by (simp add: T_Hiding)
          (use assms(3) \<open>s = trace_hide t' (ev ` A)\<close> \<open>t = t' @ t''\<close>
            front_tickFree_Nil tickFree_append_iff in blast)
    next
      show \<open>\<not> (\<forall>v. trace_hide v (ev ` A) = trace_hide t' (ev ` A)
                   \<longrightarrow> (v, ev ` A) \<notin> \<F> Q) \<Longrightarrow> s \<in> \<T> (Q \ A)\<close>
        by (simp add: T_Hiding) (metis \<open>s = trace_hide t' (ev ` A)\<close>)
    qed
  } note $ = this

  from elem_min_elems[OF \<open>s \<in> min_elems (\<D> (P \ A))\<close>] have \<open>s \<in> \<D> (P \ A)\<close> .
  then obtain t u
    where * : \<open>ftF u\<close> \<open>tF t\<close> \<open>s = trace_hide t (ev ` A) @ u\<close>
      \<open>t \<in> \<D> P \<or> (\<exists>f. isInfHiddenRun f P A \<and> t \<in> range f)\<close>
    by (simp add: D_Hiding) blast
  have \<open>u = []\<close>
  proof (rule ccontr)
    assume \<open>u \<noteq> []\<close>
    have \<open>ftF (butlast u)\<close> \<open>butlast s = trace_hide t (ev ` A) @ butlast u\<close>
      by (use "*"(1) front_tickFree_iff_tickFree_butlast tickFree_imp_front_tickFree in blast)
        (simp add: "*"(3) \<open>u \<noteq> []\<close> butlast_append)
    with "*"(2, 4) have \<open>butlast s \<in> \<D> (P \ A)\<close> by (simp add: D_Hiding) blast
    from min_elems_no[OF \<open>s \<in> min_elems (\<D> (P \ A))\<close> this] "*"(3) \<open>u \<noteq> []\<close>
    show False by (metis Nil_is_append_conv append_butlast_last_id less_self nless_le)
  qed

  from "*"(4) show \<open>s \<in> \<T> (Q \ A)\<close>
  proof (elim disjE exE)
    show \<open>t \<in> \<D> P \<Longrightarrow> s \<in> \<T> (Q \ A)\<close> using "$" "*"(2, 3) \<open>u = []\<close> by blast
  next
    fix f
    assume assm : \<open>isInfHiddenRun f P A \<and> t \<in> range f\<close>
    show \<open>s \<in> \<T> (Q \ A)\<close>
    proof (cases \<open>\<forall>i. f i \<in> \<T> Q\<close>)
      from "*"(1, 2, 3) assm show \<open>\<forall>i. f i \<in> \<T> Q \<Longrightarrow> s \<in> \<T> (Q \ A)\<close>
        by (simp add: T_Hiding) blast
    next
      assume \<open>\<not> (\<forall>i. f i \<in> \<T> Q)\<close>
      then obtain i where \<open>f i \<notin> \<T> Q\<close>  by blast
      with assm le_approx2T \<open>P \<sqsubseteq> Q\<close> have \<open>f i \<in> \<D> P\<close> by blast
      moreover have \<open>s = trace_hide (f i) (ev ` A)\<close>
        by (metis "*"(3) \<open>u = []\<close> append.right_neutral assm rangeE)
      moreover have \<open>tF (f i)\<close>
        by (metis "*"(2) "*"(3) Hiding_tickFree \<open>u = []\<close> append.right_neutral calculation(2))
      ultimately show \<open>s \<in> \<T> (Q \ A)\<close> using "$" by blast
    qed
  qed
qed


lemma chain_Hiding : \<open>chain Y \<Longrightarrow> chain (\<lambda> i. Y i \ A)\<close>
  by (simp add: chain_def mono_Hiding)

lemma KoenigLemma: 
  \<open>\<exists>(f::nat \<Rightarrow> 'a list). strict_mono f \<and> range f \<subseteq> {t. \<exists>t'\<in>Tr. t \<le> t'}\<close>
  if * : \<open>infinite (Tr::'a list set)\<close> and ** : \<open>\<forall>i. finite{t. \<exists>t'\<in>Tr. t = take i t'}\<close>
proof -
  define Tr' where \<open>Tr' = {t. \<exists>t'\<in>Tr. t \<le> t'}\<close> (* prefix closure *)
  have a : \<open>infinite Tr'\<close> by (rule infinite_super[OF _ "*"]) (unfold Tr'_def, blast)
  have b : \<open>finite {t \<in> Tr'. length t = i}\<close> for i
    by (rule finite_subset[OF _ "**"[THEN spec, of i]])
      (unfold Tr'_def, simp add: subset_iff, metis prefixE append_eq_conv_conj)
  have c : \<open>\<exists>e. infinite {t' \<in> Tr'. t @ [e] < t'}\<close> if \<open>infinite {t' \<in> Tr'. t < t'}\<close> for t
  proof (rule ccontr)
    assume \<open>\<nexists>e. infinite {t' \<in> Tr'. t @ [e] < t'}\<close>
    define E where \<open>E \<equiv> {e |e. t @ [e] \<in> Tr'}\<close>
    have \<open>finite E\<close>
      by (rule inj_on_finite[OF _ _ b[of \<open>Suc (length t)\<close>], of \<open>\<lambda>e. t @ [e]\<close>])
        (simp_all add: inj_on_def E_def image_Collect_subsetI)
    hence \<open>finite {t @ [e] |e. e \<in> E}\<close> by simp
    have \<open>{t' \<in> Tr'. t < t'} = {t @ [e] |e. e \<in> E} \<union> (\<Union>e\<in>E. {t' \<in> Tr'. t @ [e] < t'})\<close>
      by (auto simp add: E_def Tr'_def less_list_def less_eq_list_def prefix_def)+
        (metis append_Cons append_self_conv2 neq_Nil_conv self_append_conv)
    with \<open>\<nexists>e. infinite {t' \<in> Tr'. t @ [e] < t'}\<close> \<open>infinite {t' \<in> Tr'. t < t'}\<close> \<open>finite E\<close>
    show False by auto
  qed

  define f where \<open>f \<equiv> rec_nat [] (\<lambda>i t. let e = SOME e. infinite {t' \<in> Tr'. t @ [e] < t'} in t @ [e])\<close>
  hence \<open>strict_mono f\<close> by (simp add: lift_Suc_mono_less strict_monoI)
  moreover have \<open>f n \<in> Tr' \<and> infinite {t' \<in> Tr'. f n < t'}\<close> for n
  proof (induct n)
    show \<open>f 0 \<in> Tr' \<and> infinite {t' \<in> Tr'. f 0 < t'}\<close>
    proof (rule conjI)
      show \<open>f 0 \<in> Tr'\<close> by (simp add: f_def Tr'_def "*" not_finite_existsD)
    next
      show \<open>infinite {t' \<in> Tr'. f 0 < t'}\<close>
        by (rule infinite_super[of \<open>Tr' - {f 0}\<close>])
          (simp add: a Tr'_def f_def subset_iff less_list_def, simp add: a)
    qed
  next
    fix n assume hyp : \<open>f n \<in> Tr' \<and> infinite {t' \<in> Tr'. f n < t'}\<close>
    have \<open>f (Suc n) = (let e = SOME e. infinite {t' \<in> Tr'. f n @ [e] < t'} in f n @ [e])\<close>
      by (simp add: f_def)
    with c[of \<open>f n\<close>] obtain e
      where $ : \<open>f (Suc n) = f n @ [e] \<and> infinite {t' \<in> Tr'. f n @ [e] < t'}\<close>
      by (metis (no_types, lifting) hyp someI_ex)
    then obtain i where \<open>i \<in> Tr' \<and> f (Suc n) < i\<close> using not_finite_existsD by auto 
    with dual_order.trans order_less_imp_le have \<open>f (Suc n) \<in> Tr'\<close>
      unfolding Tr'_def by fastforce
    thus \<open>f (Suc n) \<in> Tr' \<and> infinite {t' \<in> Tr'. f (Suc n) < t'}\<close> by (simp add: "$")
  qed
  ultimately show \<open>\<exists>(f::nat \<Rightarrow> 'a list). strict_mono f \<and> range f \<subseteq> Tr'\<close> by blast
qed

(* 
lemma isInfHiddenRun_chain :
 \<open>chain Y \<Longrightarrow> isInfHiddenRun f (Y (Suc i)) A \<Longrightarrow> isInfHiddenRun f (Y i) A\<close>
  using D_T le_approx2T chain_def by blast
 *)


(* TODO: redo this proof properly *)
lemma div_Hiding_lub :  
  \<open>finite (A::'a set) \<Longrightarrow> chain Y \<Longrightarrow> \<D> (\<Squnion> i. (Y i \ A)) \<subseteq> \<D> ((\<Squnion> i. Y i) \ A)\<close>
  for Y :: \<open>nat \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof (auto simp add:limproc_is_thelub chain_Hiding D_Hiding T_Hiding D_LUB T_LUB, goal_cases)
  case (1 x)
  { fix xa t u f
    assume a:"ftF u \<and> tF t \<and> x = trace_hide t (ev ` A) @ u \<and>
              isInfHiddenRun f (Y xa) A \<and> (\<forall> i. f i \<notin> \<D> (Y xa)) \<and> t \<in> range f"
    hence "\<forall>i n. f i \<in> \<T> (Y n)" using "1"(2) D_T chain_lemma le_approx2T by blast
    with a have ?case by blast
  } note aa=this 
  { fix xa t u f j
    assume a:"ftF u \<and> tF t \<and> x = trace_hide t (ev ` A) @ u \<and> 
              isInfHiddenRun f (Y xa) A \<and> (f j \<in> \<D> (Y xa)) \<and> t \<in> range f"
    hence "\<exists>t u. ftF u \<and> tF t \<and> x = trace_hide t (ev ` A) @ u \<and> t \<in> \<D> (Y xa)"
      apply(rule_tac x="f j" in exI, rule_tac x=u in exI) 
      by (metis Hiding_tickFree rangeE)
  } note bb=this
  have cc: "\<forall>xa. \<exists>t u. ftF u \<and> tF t \<and> x = trace_hide t (ev ` A) @ u \<and> t \<in> \<D>(Y xa)
           \<Longrightarrow> ?case" (is "\<forall>xa. \<exists>t. ?S t xa \<Longrightarrow> ?case")
  proof -
    assume dd:"\<forall>xa. \<exists>t u. ftF u \<and> tF t \<and> x = trace_hide t (ev ` A) @ u \<and> t \<in> \<D>(Y xa)"
      (is "\<forall>xa. \<exists>t. ?S t xa")
    define f :: \<open>nat \<Rightarrow> ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k list\<close> where "f = (\<lambda>n. SOME t. ?S t n)"
    thus ?case 
    proof (cases "finite(range f)")
      case True
      obtain t where gg:"infinite (f -` {t})" using f_def True inf_img_fin_dom by blast 
      then obtain k where "f k = t" using finite_nat_set_iff_bounded_le by blast
      then obtain u where uu:"ftF u \<and> x = trace_hide t (ev ` A) @ u \<and> tF t"
        using f_def dd[rule_format, of k] some_eq_ex[of "\<lambda>t. ?S t k"] by blast
      { fix m
        from gg obtain n where gg:"n \<ge> m \<and> n \<in> (f -` {t})"
          by (meson finite_nat_set_iff_bounded_le nat_le_linear)
        hence "t \<in> \<D> (Y n)" using f_def dd[rule_format, of n] some_eq_ex[of "\<lambda>t. ?S t n"] by auto
        with gg 1(2) have "t \<in> \<D> (Y m)" by (meson contra_subsetD le_approx_def po_class.chain_mono)
      }
      with gg uu show ?thesis by blast
    next
      case False
      { fix t
        assume "t \<in> range f"
        then obtain k where "f k = t" using finite_nat_set_iff_bounded_le by blast
        then obtain u where uu:"ftF u \<and> x = trace_hide t (ev ` A) @ u \<and> tF t"
          using f_def dd[rule_format, of k] some_eq_ex[of "\<lambda>t. ?S t k"] by blast
        hence "set t \<subseteq> set x \<union> (ev ` A)" by auto
      } note ee=this
      { fix i
        have "finite {(take i t)|t. t \<in> range f}" 
        proof(induct i, simp)
          case (Suc i)
          have ff:"{take (Suc i) t|t. t \<in> range f} \<subseteq> {(take i t)|t. t \<in> range f} \<union>
                        (\<Union>e\<in>(set x \<union> (ev ` A)). {(take i t)@[e]|t. t \<in> range f})" (is "?AA \<subseteq> ?BB")
          proof
            fix t
            assume "t \<in> ?AA"
            then obtain t' where hh:"t' \<in> range f \<and> t = take (Suc i) t'" 
              using finite_nat_set_iff_bounded_le by blast
            with ee[of t'] show "t \<in> ?BB"
            proof(cases "length t' > i")
              case True
              hence ii:"take (Suc i) t' = take i t' @ [t'!i]" by (simp add: take_Suc_conv_app_nth)
              with ee[of t'] have "t'!i \<in> set x \<union> (ev ` A)" 
                by (meson True contra_subsetD hh nth_mem)
              with ii hh show ?thesis by blast
            next
              case False
              hence "take (Suc i) t' = take i t'" by fastforce
              with hh show ?thesis by auto
            qed
          qed
          { fix e 
            have "{x @ [e] |x. \<exists>t. x = take i t \<and> t \<in> range f} = {take i t' @ [e] |t'. t' \<in> range f}"
              by auto
            hence "finite({(take i t') @ [e] |t'. t'\<in>range f})"
              using finite_image_set[of _ "\<lambda>t. t@[e]", OF Suc] by auto 
          } note gg=this
          have "finite(set x \<union> (ev ` A))" using 1(1) by simp
          with ff gg Suc show ?case by (metis (no_types, lifting) finite_UN finite_Un finite_subset)
        qed
      } note ff=this
      hence "\<forall>i. {take i t |t. t \<in> range f} = {t. \<exists>t'. t = take i (f t')}" by auto
      with KoenigLemma[of "range f", OF False] ff
      obtain f' where gg:"strict_mono (f':: nat \<Rightarrow> ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k list) \<and> 
                                            range f' \<subseteq> {t. \<exists>t'\<in>range f. t \<le> t'}" by auto
      { fix n
        define M where "M = {m. f' n \<le> f m }"
        assume "finite M"
        hence l1:"finite {length (f m)|m. m \<in> M}" by simp
        obtain lm where l2:"lm = Max {length (f m)|m. m \<in> M}" by blast
        { fix k
          have "length (f' k) \<ge> k" 
            by(induct k, simp, metis (full_types) gg lessI less_length_mono linorder_not_le 
                not_less_eq_eq order_trans strict_mono_def)
        }
        with gg obtain m where r1:"length (f' m) > lm" by (meson lessI less_le_trans)
        from gg obtain r where r2:"f' (max m n) \<le> f r" by blast
        with gg have r3: "r \<in> M" 
          by (metis (no_types, lifting) M_def max.bounded_iff mem_Collect_eq order_refl 
              order_trans strict_mono_less_eq)
        with l1 l2 have f1:"length (f r) \<le> lm" using Max_ge by blast
        from r1 r2 have f2:"length (f r) > lm"
          by (meson dual_order.strict_trans1 gg le_length_mono max.bounded_iff order_refl 
              strict_mono_less_eq) 
        from f1 f2 have False by simp
      } note ii=this
      { fix i n
        from ii obtain m where jj:"m \<ge> n \<and> f m \<ge> f' i" 
          by (metis finite_nat_set_iff_bounded_le mem_Collect_eq nat_le_linear)
        have kk: "(f m) \<in> \<D> (Y m)" using f_def dd[rule_format, of m] some_eq_ex[of "\<lambda>t. ?S t m"] by auto 
        with jj gg have "(f' i) \<in> \<T> (Y m)" by (meson D_T is_processT3_TR)
        with jj 1(2) have  "(f' i) \<in> \<T> (Y n)" using D_T le_approx2T po_class.chain_mono by blast
      } note jj=this
      from gg have kk:"mono (\<lambda>n. trace_hide (f' n) (ev ` A))" 
        unfolding strict_mono_def mono_def
        by (metis (no_types, lifting) filter_append gg less_eq_list_def prefix_def mono_def strict_mono_mono)
      { fix n
        from gg obtain k r where "f k = f' n @ r"
          by (metis (lifting) ii less_eq_list_def prefix_def not_finite_existsD)
        hence "trace_hide (f' n) (ev ` A) \<le> x" 
          using f_def dd[rule_format, of k] some_eq_ex[of "\<lambda>t. ?S t k"]
          by (metis (no_types, lifting) prefixI prefix_prefix filter_append)
      } note ll=this
      { assume llll:"\<forall>m. \<exists>n. trace_hide (f' n) (ev ` A) > trace_hide (f' m) (ev ` A)"
        hence lll:"\<forall>m. \<exists>n. length (trace_hide (f' n) (ev ` A)) > length (trace_hide (f' m) (ev ` A))"
          using less_length_mono by blast
        define ff where lll':"ff = rec_nat (length (trace_hide (f' 0) (ev ` A))) 
                (\<lambda>i t. (let n = SOME n. (length (trace_hide (f' n) (ev ` A))) > t 
                         in length (trace_hide (f' n) (ev ` A))))"
        { fix n
          from lll' lll[rule_format, of n] have "ff (Suc n) > ff n" 
            apply simp apply (cases n)
             apply (metis (no_types, lifting) old.nat.simps(6) someI_ex)
            by (metis (no_types, lifting) llll less_length_mono old.nat.simps(7) someI_ex)
        } note lll''=this
        with lll'' have "strict_mono ff" by (simp add: lll'' lift_Suc_mono_less strict_monoI)
        hence lll''':"infinite(range ff)" using finite_imageD strict_mono_imp_inj_on by auto
        from lll lll' have "range ff \<subseteq> range (\<lambda>n. length (trace_hide (f' n) (ev ` A)))" 
          by (auto, metis (mono_tags, lifting) old.nat.exhaust old.nat.simps(6) old.nat.simps(7) range_eqI)
        with lll''' have "infinite (range (\<lambda>n. length (trace_hide (f' n) (ev ` A))))"
          using finite_subset by auto
        hence "\<exists>m. length (trace_hide (f' m) (ev ` A)) > length x"
          using finite_nat_set_iff_bounded_le by (metis (no_types, lifting) not_less rangeE)
        with ll have False using le_length_mono not_less by blast
      }
      then obtain m where mm:"\<forall>n. trace_hide (f' n) (ev ` A) \<le> trace_hide (f' m) (ev ` A)"
        by (metis (no_types, lifting) dual_order.eq_iff le_same_imp_eq_or_less ll order.strict_implies_order)
      with gg obtain k where nn:"f k \<ge> f' m" by blast
      then obtain u where oo:"ftF u \<and> x = trace_hide (f' m) (ev ` A) @ u \<and> tF (f' m)"
        using f_def dd[rule_format, of k] some_eq_ex[of "\<lambda>t. ?S t k"] 

        apply (auto simp add: prefix_def tickFree_def disjoint_iff)
        by (smt (z3) Prefix_Order.prefixE append.assoc disjoint_iff filter_append filter_is_subset front_tickFree_append subset_iff tickFree_append_iff tickFree_def)
          (*  proof -
          fix t :: "('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k list" and u :: "('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k list" and ua :: "('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k list"
          assume a1: "\<forall>x. x \<in> range tick \<longrightarrow> x \<notin> set (SOME x. \<exists>u. ftF u \<and> (\<forall>xa. xa \<in> range tick \<longrightarrow> xa \<notin> set x) \<and> trace_hide t (ev ` A) @ ua = trace_hide x (ev ` A) @ u \<and> x \<in> \<D> (Y k))"
          assume a2: "\<And>u. ftF u \<and> trace_hide t (ev ` A) @ ua = trace_hide (f' m) (ev ` A) @ u \<and> (\<forall>x. x \<in> range tick \<longrightarrow> x \<notin> set (f' m)) \<Longrightarrow> thesis"
          assume a3: "trace_hide t (ev ` A) @ ua = trace_hide (SOME x. \<exists>u. ftF u \<and> (\<forall>xa. xa \<in> range tick \<longrightarrow> xa \<notin> set x) \<and> trace_hide t (ev ` A) @ ua = trace_hide x (ev ` A) @ u \<and> x \<in> \<D> (Y k)) (ev ` A) @ u"
          assume a4: "f' m \<le> (SOME ta. \<exists>u. ftF u \<and> (\<forall>x. x \<in> range tick \<longrightarrow> x \<notin> set ta) \<and> trace_hide t (ev ` A) @ ua = trace_hide ta (ev ` A) @ u \<and> ta \<in> \<D> (Y k))"
          assume a5: "ftF u"
          obtain ee :: "('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set \<Rightarrow> ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k set \<Rightarrow> ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k" where
            f6: "\<forall>E Ea. (E \<inter> Ea \<noteq> {} \<or> (\<forall>e. e \<notin> E \<or> e \<notin> Ea)) \<and> (E \<inter> Ea = {} \<or> ee Ea E \<in> E \<and> ee Ea E \<in> Ea)"
            by (metis (no_types) disjoint_iff)
          obtain ees :: "('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k list \<Rightarrow> ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k list \<Rightarrow> ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k list" where
            "\<forall>x0 x1. (\<exists>v2. x0 = x1 @ v2) = (x0 = x1 @ ees x0 x1)"
            by moura
          then have f7: "\<forall>es esa. \<not> es \<le> esa \<or> esa = es @ ees esa es"
            by (meson Prefix_Order.prefixE)
          have "{e \<in> set (SOME es. \<exists>esa. ftF esa \<and> (\<forall>e. e \<in> range tick \<longrightarrow> e \<notin> set es) \<and> trace_hide t (ev ` A) @ ua = trace_hide es (ev ` A) @ esa \<and> es \<in> \<D> (Y k)). e \<notin> ev ` A} \<subseteq> set (SOME es. \<exists>esa. ftF esa \<and> (\<forall>e. e \<in> range tick \<longrightarrow> e \<notin> set es) \<and> trace_hide t (ev ` A) @ ua = trace_hide es (ev ` A) @ esa \<and> es \<in> \<D> (Y k))"
            by blast
          then have f8: "range tick \<inter> {e \<in> set (SOME es. \<exists>esa. ftF esa \<and> (\<forall>e. e \<in> range tick \<longrightarrow> e \<notin> set es) \<and> trace_hide t (ev ` A) @ ua = trace_hide es (ev ` A) @ esa \<and> es \<in> \<D> (Y k)). e \<notin> ev ` A} = {}"
            using f6 a1 by (meson subset_iff)
          have "trace_hide (f' m) (ev ` A) @ trace_hide (ees (SOME es. \<exists>esa. ftF esa \<and> (\<forall>e. e \<in> range tick \<longrightarrow> e \<notin> set es) \<and> trace_hide t (ev ` A) @ ua = trace_hide es (ev ` A) @ esa \<and> es \<in> \<D> (Y k)) (f' m)) (ev ` A) = trace_hide (SOME es. \<exists>esa. ftF esa \<and> (\<forall>e. e \<in> range tick \<longrightarrow> e \<notin> set es) \<and> trace_hide t (ev ` A) @ ua = trace_hide es (ev ` A) @ esa \<and> es \<in> \<D> (Y k)) (ev ` A)"
            using f7 a4 by (metis (no_types, lifting) filter_append)
          then have f9: "tF (trace_hide (f' m) (ev ` A) @ trace_hide (ees (SOME es. \<exists>esa. ftF esa \<and> (\<forall>e. e \<in> range tick \<longrightarrow> e \<notin> set es) \<and> trace_hide t (ev ` A) @ ua = trace_hide es (ev ` A) @ esa \<and> es \<in> \<D> (Y k)) (f' m)) (ev ` A))"
            using f8 by (simp add: tickFree_def)
          have "tF (f' m)"
            using f7 f6 a4 a1 by (metis (no_types, lifting) tickFree_append_iff tickFree_def)
          then have f10: "\<exists>es. ftF es \<and> trace_hide t (ev ` A) @ ua = trace_hide (f' m) (ev ` A) @ es \<and> (v1_5 \<notin> range tick \<or> v1_5 \<notin> set (f' m))"
            using f9 f7 f6 a5 a4 a3
            by (smt (z3) append.assoc filter_append front_tickFree_append tickFree_append_iff tickFree_def)
          obtain eea :: "('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k" where
            "(\<exists>v1. v1 \<in> range tick \<and> v1 \<in> set (f' m)) = (eea \<in> range tick \<and> eea \<in> set (f' m))"
            by moura
          then show ?thesis
            using f10 a2 by (metis \<open>tF (f' m)\<close> disjoint_iff tickFree_def)
        qed *)
      show ?thesis
        apply(rule_tac x="f' m" in exI, rule_tac x=u in exI)
        apply(simp add:oo, rule disjI2, rule_tac x="\<lambda>n. f' (n + m)" in exI)
        using gg jj kk mm apply (auto simp add: strict_mono_def dual_order.antisym mono_def)
        by (metis plus_nat.add_0 rangeI)
    qed
  qed
  show ?case 
  proof (cases "\<exists> xa t u f. ftF u \<and> tF t \<and> (\<forall> i. f i \<notin> \<D> (Y xa)) \<and> t \<in> range f \<and>
                            x = trace_hide t (ev ` A) @ u \<and> isInfHiddenRun f (Y xa) A")
    case True
    then show ?thesis using aa by blast
  next
    case False
    have dd:"\<forall>xa. \<exists>t u. ftF u \<and> tF t \<and> x = trace_hide t (ev ` A) @ u \<and>
             (t \<in> \<D> (Y xa) \<or> (\<exists>f. isInfHiddenRun f (Y xa) A \<and> (\<exists>i. f i \<in> \<D> (Y xa)) \<and> t \<in> range f))" 
      (is "\<forall>xa. ?dd xa")
    proof (rule_tac allI)
      fix xa
      from 1(3) obtain t u where 
        "ftF u \<and> tF t \<and> x = trace_hide t (ev ` A) @ u \<and>
              (t \<in> \<D> (Y xa) \<or> (\<exists>f. isInfHiddenRun f (Y xa) A \<and> t \<in> range f))" 
        by blast
      thus "?dd xa"
        apply(rule_tac x=t in exI, rule_tac x=u in exI, intro conjI, simp_all, elim conjE disjE, simp_all)
        using 1(1) False D_T chain_lemma le_approx2T by blast
    qed
    hence ee:"\<forall>xa. \<exists>t u. ftF u \<and> tF t \<and> x = trace_hide t (ev ` A) @ u \<and> t \<in> \<D>(Y xa)"
      using bb by blast
    with cc show ?thesis by simp
  qed
qed

lemma Cont_Hiding_prem : \<open>(\<Squnion> i. Y i) \ A = (\<Squnion> i. (Y i \ A))\<close> if \<open>finite A\<close> \<open>chain Y\<close>
proof (subst Process_eq_spec_optimized, safe)
  show \<open>s \<in> \<D> ((\<Squnion> i. Y i) \ A) \<Longrightarrow> s \<in> \<D> (\<Squnion> i. (Y i \ A))\<close> for s
    by (simp add: limproc_is_thelub chain_Hiding \<open>chain Y\<close> D_Hiding D_LUB T_LUB) blast
next
  show \<open>s \<in> \<D> (\<Squnion> i. (Y i \ A)) \<Longrightarrow> s \<in> \<D> ((\<Squnion> i. Y i) \ A)\<close> for s
    using div_Hiding_lub[OF \<open>finite A\<close> \<open>chain Y\<close>] by auto
next
  show \<open>(s, X) \<in> \<F> ((\<Squnion> i. Y i) \ A) \<Longrightarrow> (s, X) \<in> \<F> (\<Squnion> i. (Y i \ A))\<close> for s X
    by (simp add: limproc_is_thelub chain_Hiding \<open>chain Y\<close> F_Hiding F_LUB D_LUB T_LUB) blast
next
  assume same_div : \<open>\<D> ((\<Squnion> i. Y i) \ A) = \<D> (\<Squnion> i. (Y i \ A))\<close>
  fix s X assume \<open>(s, X) \<in> \<F> (\<Squnion> i. (Y i \ A))\<close>
  show \<open>(s, X) \<in> \<F> ((\<Squnion> i. Y i) \ A)\<close>
  proof (cases \<open>s \<in> \<D> (\<Squnion> i. (Y i \ A))\<close>)
    show \<open>s \<in> \<D> (\<Squnion>i. Y i \ A) \<Longrightarrow> (s, X) \<in> \<F> ((\<Squnion>i. Y i) \ A)\<close>
      by (simp add: is_processT8 same_div)
  next
    assume \<open>s \<notin> \<D> (\<Squnion>i. Y i \ A)\<close>
    then obtain j where \<open>s \<notin> \<D> (Y j \ A)\<close>
      by (auto simp add: limproc_is_thelub chain_Hiding \<open>chain Y\<close> D_LUB)
    moreover from \<open>(s, X) \<in> \<F> (\<Squnion> i. (Y i \ A))\<close> have \<open>(s, X) \<in> \<F> (Y j \ A)\<close>
      by (simp add: limproc_is_thelub chain_Hiding \<open>chain Y\<close> F_LUB)
    ultimately show \<open>(s, X) \<in> \<F> ((\<Squnion>i. Y i) \ A)\<close>
      by (fact le_approx2[OF mono_Hiding[OF is_ub_thelub[OF \<open>chain Y\<close>]], THEN iffD2])
  qed
qed



lemma Hiding_cont[simp]:  \<open>cont (\<lambda>a. f a \ A)\<close> if \<open>finite A\<close> and \<open>cont f\<close>
proof (rule cont_compose[where f = f])
  show \<open>cont (\<lambda>a. a \ A)\<close>
  proof (rule contI2)
    show \<open>monofun (\<lambda>a. a \ A)\<close> by (simp add: mono_Hiding monofunI)
  next
    show \<open>chain Y \<Longrightarrow> (\<Squnion>i. Y i) \ A \<sqsubseteq> (\<Squnion>i. Y i \ A)\<close>
      for Y :: \<open>nat \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
      by (simp add: Cont_Hiding_prem[OF \<open>finite A\<close>])
  qed
next
  from \<open>cont f\<close> show \<open>cont f\<close> .
qed



(* TODO : move this *)


lemma length_strict_mono: \<open>strict_mono f \<Longrightarrow> i + length (f 0) \<le> length (f i)\<close>
  for f :: \<open>nat \<Rightarrow> 'a list\<close>
  by (induct i)
    (simp_all add: Suc_le_eq less_length_mono order_le_less_trans strict_mono_Suc_iff)


lemma mono_trace_hide: \<open>a \<le> b \<Longrightarrow> trace_hide a (ev ` A) \<le> trace_hide b (ev ` A)\<close>
  by (metis prefixE prefixI filter_append)

lemma mono_constant: 
  assumes "mono (f::nat \<Rightarrow> ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k list)" and "\<forall>i. f i \<le> a"
  shows "\<exists>i. \<forall>j\<ge>i. f j = f i"
proof -
  from assms(2) have "\<forall>i. length (f i) \<le> length a"
    by (simp add: le_length_mono)
  hence aa:"finite {length (f i)|i. True}" 
    using finite_nat_set_iff_bounded_le by auto
  define lm where l2:"lm = Max {length (f i)|i. True}"
  with aa obtain im where "length (f im) = lm" using Max_in by fastforce
  with l2 assms(1) show ?thesis
    apply (intro exI[of _ im], intro impI allI)
    by (metis (mono_tags, lifting) Max_ge aa antisym le_length_mono le_neq_trans less_length_mono 
        mem_Collect_eq mono_def order_less_irrefl)
qed

text \<open>We can actually optimize the divergences of the \<^const>\<open>Hiding\<close> operator.\<close>

lemma mono_take : \<open>s \<le> t \<Longrightarrow> take n s \<le> take n t\<close>
  unfolding less_eq_list_def prefix_def by auto

lemma shift_isInfHiddenRun : \<open>\<exists>f. isInfHiddenRun f P A \<and> t = f 0\<close>
  if \<open>isInfHiddenRun f P A \<and> t \<in> range f\<close>
proof -
  from that obtain i where \<open>t = f i\<close> by blast
  hence \<open>t = f (i + 0)\<close> by simp
  moreover have \<open>isInfHiddenRun (\<lambda>j. f (i + j)) P A\<close>
    by (metis add_Suc_right strict_mono_Suc_iff that)
  ultimately show \<open>\<exists>f. isInfHiddenRun f P A \<and> t = f 0\<close> by blast
qed

lemma uniformize_length_isInfHiddenRun :
  assumes * : \<open>isInfHiddenRun f P A\<close> \<open>t = f 0\<close>
  defines \<open>g \<equiv> \<lambda>i. take (i + length t) (f i)\<close>
  shows \<open>isInfHiddenRun g P A \<and> (\<forall>i. length (g i) = i + length t) \<and> t = g 0\<close>
proof (intro conjI allI)
  show \<open>strict_mono g\<close>
  proof (unfold strict_mono_Suc_iff, rule allI)
    fix i
    from "*"(1) have \<open>strict_mono f\<close> by blast
    from length_strict_mono[of f \<open>Suc i\<close>, OF \<open>strict_mono f\<close>]
    have $ : \<open>take (i + length (f 0)) (f (Suc i)) < take ((Suc i) + length (f 0)) (f (Suc i))\<close>
      by (simp add: take_Suc_conv_app_nth)
    from \<open>strict_mono f\<close>[THEN strict_monoD, of i \<open>Suc i\<close>, simplified]
    obtain u where \<open>f (Suc i) = f i @ u\<close> by (meson strict_prefixE')
    with length_strict_mono[of f i, OF \<open>strict_mono f\<close>]
    have \<open>take (i + length (f 0)) (f i) = take (i + length (f 0)) (f (Suc i))\<close> by simp
    with "$" "*"(2) show \<open>g i < g (Suc i)\<close> unfolding g_def by presburger
  qed
next
  show \<open>g i \<in> \<T> P\<close> for i unfolding g_def
    by (metis "*"(1) prefixI append_take_drop_id is_processT3_TR)
next
  show \<open>trace_hide (g i) (ev ` A) = trace_hide (g 0) (ev ` A)\<close> for i
  proof (rule order_antisym)
    have \<open>f 0 \<le> f i\<close> by (simp add: "*"(1) strict_mono_less_eq)
    hence \<open>f 0 \<le> take (i + length t) (f i)\<close>
      by (metis "*"(2) prefixE prefixI le_add2 take_all_iff take_append)
    from mono_trace_hide[OF this]
    show \<open>trace_hide (g i) (ev ` A) \<le> trace_hide (g 0) (ev ` A)\<close>
      unfolding g_def
      by (metis "*" prefixI append_take_drop_id filter_append le_add2 take_all_iff)
  next
    have $ : \<open>take (i + length (f 0)) (f i) \<le> f i\<close> by (metis prefixI append_take_drop_id)
    have \<open>take (length t) (f 0) \<le> take (i + length t) (f 0)\<close>
      \<open>take (i + length t) (f 0) \<le> take (i + length t) (f i)\<close>
      by (simp add: "*"(2))
        (meson "*"(1) le_add2 le_add_same_cancel2 mono_take strict_mono_less_eq)
    from order_trans[OF this] have \<open>g 0 \<le> g i\<close> unfolding g_def by simp
    thus \<open>trace_hide (g 0) (ev ` A) \<le> trace_hide (g i) (ev ` A)\<close> by (fact mono_trace_hide)
  qed
next
  show \<open>length (g i) = i + length t\<close> for i by (simp add: "*" g_def length_strict_mono)
next
  show \<open>t = g 0\<close> by (simp add: "*"(2) g_def)
qed


abbreviation isInfHiddenRun_optimized ::
  \<open>[nat \<Rightarrow> ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k list, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a set, ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close>
  where \<open>isInfHiddenRun_optimized f P A t \<equiv>
         strict_mono f \<and> (\<forall>i. f i \<in> \<T> P) \<and> (\<forall>i. f i \<notin> \<D> P) \<and> 
         (\<forall>i. trace_hide (f i) (ev ` A) = trace_hide (f 0) (ev ` A)) \<and>
         (\<forall>i. length (f i) = i + length t) \<and> t = f 0\<close>

abbreviation div_hide_optimized :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> 'a set \<Rightarrow> ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k list set\<close>
  where \<open>div_hide_optimized P A \<equiv>
         {s. \<exists>t u. ftF u \<and> tF t \<and>
                   s = trace_hide t (ev ` A) @ u \<and> 
                   (t \<in> \<D> P \<or> (\<exists>f. isInfHiddenRun_optimized f P A t))}\<close>


lemma D_Hiding_optimized : \<open>\<D> (P \ A) = div_hide_optimized P A\<close>
proof (unfold D_Hiding, intro subset_antisym subsetI)
  show \<open>s \<in> div_hide_optimized P A \<Longrightarrow> s \<in> div_hide P A\<close> for s by blast
next
  fix s assume \<open>s \<in> div_hide P A\<close>
  then obtain t u
    where * : \<open>ftF u\<close> \<open>tF t\<close> \<open>s = trace_hide t (ev ` A) @ u\<close>
      \<open>t \<in> \<D> P \<or> (\<exists>f. isInfHiddenRun f P A \<and> t \<in> range f)\<close> by blast
  from "*"(4) show \<open>s \<in> div_hide_optimized P A\<close>
  proof (elim disjE exE)
    from "*"(1, 2, 3) show \<open>t \<in> \<D> P \<Longrightarrow> s \<in> div_hide_optimized P A\<close> by blast
  next
    fix f assume \<open>isInfHiddenRun f P A \<and> t \<in> range f\<close>
    with shift_isInfHiddenRun obtain f where ** : \<open>isInfHiddenRun f P A \<and> t = f 0\<close> by blast
    show \<open>s \<in> div_hide_optimized P A\<close>
    proof (cases \<open>\<exists>i. f i \<in> \<D> P\<close>)
      assume \<open>\<exists>i. f i \<in> \<D> P\<close>
      then obtain i where \<open>f i \<in> \<D> P\<close> ..
      have \<open>trace_hide t (ev ` A) = trace_hide (f i) (ev ` A)\<close> by (metis "**")
      moreover from calculation have \<open>tF (f i)\<close> by (metis "*"(2) Hiding_tickFree)
      ultimately show \<open>s \<in> div_hide_optimized P A\<close>
        using "*"(1, 3) \<open>f i \<in> \<D> P\<close> by blast
    next
      assume \<open>\<nexists>i. f i \<in> \<D> P\<close>
      from "**" uniformize_length_isInfHiddenRun[of f P A t]
      have \<open>isInfHiddenRun (\<lambda>i. take (i + length t) (f i)) P A \<and>
            (\<forall>i. length (take (i + length t) (f i)) = i + length t) \<and>
            t = take (0 + length t) (f 0)\<close> by blast
      moreover from \<open>\<nexists>i. f i \<in> \<D> P\<close> have \<open>\<forall>i. take (i + length t) (f i) \<notin> \<D> P\<close>
        by (metis "**" append_Nil2 append_take_drop_id
            front_tickFree_nonempty_append_imp is_processT2_TR is_processT7)
      ultimately show \<open>s \<in> div_hide_optimized P A\<close> using "*"(1, 2, 3) by blast
    qed
  qed
qed


lemma T_Hiding_optimized :
  \<open>\<T> (P \ A) = {trace_hide t (ev ` A) |t. (t, ev ` A) \<in> \<F> P} \<union> div_hide_optimized P A\<close>
  by (unfold T_Hiding, fold D_Hiding, unfold D_Hiding_optimized) (fact refl)



text \<open>
Actually, \<^term>\<open>f i\<close> can be rewritten as \<^term>\<open>t @ map x [0..<i]\<close>
where \<^term>\<open>x\<close> is the sequence such that \<^term>\<open>f (Suc i) = f i @ [x i]\<close>.\<close>

definition seqRun :: \<open>[('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, nat \<Rightarrow> ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> nat \<Rightarrow> ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where \<open>seqRun t x i \<equiv> t @ map x [0..<i]\<close>

lemma seqRun_is_rec_nat : \<open>seqRun t x = rec_nat t (\<lambda>i t. t @ [x i])\<close>
proof (rule ext)
  show \<open>seqRun t x i = rec_nat t (\<lambda>i t. t @ [x i]) i\<close> for i
    by (induct i) (simp_all add: seqRun_def)
qed


lemma seqRun_0    [simp] : \<open>seqRun t x 0 = t\<close>
  and seqRun_Suc  [simp] : \<open>seqRun t x (Suc i) = seqRun t x i @ [x i]\<close>
  and seqRun_Nil  [simp] : \<open>seqRun [] x i = map x [0..<i]\<close>
  and seqRun_Cons [simp] : \<open>seqRun (a # t) x i = a # seqRun t x i\<close>
  by (simp_all add: seqRun_def)

lemma strict_mono_seqRun [simp] : \<open>strict_mono (seqRun t x)\<close>
  by (simp add: strict_mono_Suc_iff)

lemma length_seqRun [simp] : \<open>length (seqRun t x i) = i + length t\<close>
  by (simp add: seqRun_def)

lemma t_le_seqRun [simp] : \<open>t \<le> seqRun t x i\<close> by (simp add: seqRun_def)

lemma take_t_le_seqRun [simp] : \<open>take i t \<le> seqRun t x j\<close>
  by (induct t, simp_all add: seqRun_def less_eq_list_def prefix_def)
    (metis append.assoc append_Cons append_take_drop_id)

lemma nth_seqRun :
  \<open>j < i + length t \<Longrightarrow>
   seqRun t x i ! j = (if j < length t then t ! j else x (j - length t))\<close>
  by (simp add: seqRun_def nth_append)

lemma take_seqRun [simp] :
  \<open>take j (seqRun t x i) = (if j \<le> length t then take j t else seqRun t x (min i (j - length t)))\<close>
  by (simp add: seqRun_def min_def take_map)


lemma seqRun_eq_iff [simp] : \<open>seqRun t x i = seqRun t x j \<longleftrightarrow> i = j\<close>
  by (metis add_right_cancel length_seqRun)

lemma seqRun_le_iff [simp] : \<open>seqRun t x i \<le> seqRun t x j \<longleftrightarrow> i \<le> j\<close>
  by (simp add: strict_mono_less_eq)

lemma seqRun_less_iff [simp] : \<open>seqRun t x i < seqRun t x j \<longleftrightarrow> i < j\<close>
  by (simp add: strict_mono_less)

lemma trace_hide_is_Nil_iff : \<open>trace_hide s A = [] \<longleftrightarrow> set s \<subseteq> A\<close>
  by (simp add: filter_empty_conv subset_code(1))

lemma trace_hide_seqRun_eq_iff :
  \<open>trace_hide (seqRun t x i) A = trace_hide t A \<longleftrightarrow> (\<forall>j<i. x j \<in> A)\<close>
  by (simp add: seqRun_def trace_hide_is_Nil_iff subset_iff image_iff)
    (use atLeastLessThan_iff in blast)


abbreviation isInfHidden_seqRun ::
  \<open>[nat \<Rightarrow> ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a set, ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close>
  where \<open>isInfHidden_seqRun x P A t \<equiv> \<forall>i. seqRun t x i \<in> \<T> P \<and> x i \<in> ev ` A\<close>

abbreviation isInfHidden_seqRun_strong ::
  \<open>[nat \<Rightarrow> ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, 'a set, ('a, 'r) trace\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k] \<Rightarrow> bool\<close>
  where \<open>isInfHidden_seqRun_strong x P A t \<equiv>
         \<forall>i. seqRun t x i \<in> \<T> P \<and> seqRun t x i \<notin> \<D> P \<and> x i \<in> ev ` A\<close>



abbreviation div_hide_seqRun :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> 'a set \<Rightarrow> ('a, 'r) event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k list set\<close>
  where \<open>div_hide_seqRun P A \<equiv>
         {s. \<exists>t u. ftF u \<and> tF t \<and> s = trace_hide t (ev ` A) @ u \<and> 
                   (t \<in> \<D> P \<or> (\<exists>x. isInfHidden_seqRun x P A t))}\<close>

lemma D_Hiding_seqRun : \<open>\<D> (P \ A) = div_hide_seqRun P A\<close>
proof (intro subset_antisym subsetI)
  fix s assume \<open>s \<in> \<D> (P \ A)\<close>
  then obtain t u
    where * : \<open>ftF u\<close> \<open>tF t\<close> \<open>s = trace_hide t (ev ` A) @ u\<close>
      \<open>t \<in> \<D> P \<or> (\<exists>f. isInfHiddenRun_optimized f P A t)\<close>
    unfolding D_Hiding_optimized by blast
  show \<open>s \<in> div_hide_seqRun P A\<close>
  proof (clarify, intro exI conjI)
    show \<open>ftF u\<close> \<open>tF t\<close>
      \<open>s = trace_hide t (ev ` A) @ u\<close> by (fact "*"(1, 2, 3))+
  next
    from "*"(4) show \<open>t \<in> \<D> P \<or> (\<exists>x. isInfHidden_seqRun x P A t)\<close>
    proof (elim disjE exE)
      show \<open>t \<in> \<D> P \<Longrightarrow> t \<in> \<D> P \<or> (\<exists>x. isInfHidden_seqRun x P A t)\<close> ..
    next
      fix f assume $ : \<open>isInfHiddenRun_optimized f P A t\<close>
      define x where \<open>x i \<equiv> f (Suc i) ! (i + length t)\<close> for i
      have $$ : \<open>seqRun t x i = f i\<close> for i
      proof (induct i)
        show \<open>seqRun t x 0 = f 0\<close> by (simp add: "$")
      next
        fix i assume \<open>seqRun t x i = f i\<close>
        from "$" have \<open>length (f (Suc i)) = Suc i + length t\<close>
          \<open>length (f i) = i + length t\<close> \<open>f i \<le> f (Suc i)\<close>
          by (blast, blast, simp add: strict_mono_less_eq)
        then obtain y where \<open>f (Suc i) = f i @ [y]\<close>
          by (simp add: less_eq_list_def prefix_def)
            (metis append_eq_append_conv length_Suc_conv_rev)
        with \<open>length (f i) = i + length t\<close> have \<open>f (Suc i) = f i @ [x i]\<close>
          unfolding x_def by (metis nth_append_length)
        thus \<open>seqRun t x (Suc i) = f (Suc i)\<close> by (simp add: \<open>seqRun t x i = f i\<close>)
      qed
      have \<open>isInfHidden_seqRun x P A t\<close>
      proof (intro allI conjI)
        from "$" "$$" show \<open>seqRun t x i \<in> \<T> P\<close> for i by presburger+
      next
        from trace_hide_seqRun_eq_iff[of \<open>ev ` A\<close> t x, unfolded "$$"] "$"
        show \<open>x i \<in> ev ` A\<close> for i by blast
      qed
      thus \<open>t \<in> \<D> P \<or> (\<exists>x. isInfHidden_seqRun x P A t)\<close> by blast
    qed
  qed
next
  fix s assume \<open>s \<in> div_hide_seqRun P A\<close>
  then obtain t u
    where * : \<open>ftF u\<close> \<open>tF t\<close> \<open>s = trace_hide t (ev ` A) @ u\<close>
      \<open>t \<in> \<D> P \<or> (\<exists>x. isInfHidden_seqRun x P A t)\<close> by blast

  show \<open>s \<in> \<D> (P \ A)\<close>
  proof (unfold D_Hiding_optimized)
    from "*"(4) show \<open>s \<in> div_hide_optimized P A\<close>
    proof (elim disjE exE)
      from "*"(1, 2, 3) show \<open>t \<in> \<D> P \<Longrightarrow> s \<in> div_hide_optimized P A\<close> by blast
    next
      fix x assume $ : \<open>isInfHidden_seqRun x P A t\<close>
      show \<open>s \<in> div_hide_optimized P A\<close>
      proof (cases \<open>\<exists>i. seqRun t x i \<in> \<D> P\<close>)
        assume \<open>\<exists>i. seqRun t x i \<in> \<D> P\<close>
        then obtain i where \<open>seqRun t x i \<in> \<D> P\<close> ..
        show \<open>s \<in> div_hide_optimized P A\<close>
        proof (clarify, intro exI conjI)
          show \<open>ftF u\<close> by (fact "*"(1))
        next
          show \<open>tF (seqRun t x i)\<close>
            by (metis "$" append_T_imp_tickFree length_Cons n_not_Suc_n seqRun_Suc)
        next
          show \<open>s = trace_hide (seqRun t x i) (ev ` A) @ u\<close>
            by (metis "$" "*"(3) trace_hide_seqRun_eq_iff)
        next
          from \<open>seqRun t x i \<in> \<D> P\<close> 
          show \<open>seqRun t x i \<in> \<D> P \<or> (\<exists>f. isInfHiddenRun_optimized f P A (seqRun t x i))\<close> ..
        qed
      next
        assume \<open>\<nexists>i. seqRun t x i \<in> \<D> P\<close>
        hence \<open>isInfHiddenRun_optimized (seqRun t x) P A t\<close>
          by (simp add: trace_hide_seqRun_eq_iff "$")
        with "*"(1, 2, 3) show \<open>s \<in> div_hide_optimized P A\<close> by blast
      qed
    qed
  qed
qed


lemma T_Hiding_seqRun :
  \<open>\<T> (P \ A) = {trace_hide t (ev ` A) |t. (t, ev ` A) \<in> \<F> P} \<union> div_hide_seqRun P A\<close>
  by (unfold T_Hiding, fold D_Hiding_seqRun D_Hiding) (fact refl)

lemma F_Hiding_seqRun :
  \<open>\<F> (P \ A) =
   {(s, X). \<exists>t. s = trace_hide t (ev ` A) \<and> (t, X \<union> ev ` A) \<in> \<F> P} \<union>
   {(s, X). s \<in> div_hide_seqRun P A}\<close>
  by (unfold F_Hiding, fold D_Hiding_seqRun D_Hiding) (fact refl)


lemma D_Hiding_seqRunI :
  \<open>\<lbrakk>ftF u; tF t; s = trace_hide t (ev ` A) @ u;
    t \<in> \<D> P \<or> (\<exists>x. isInfHidden_seqRun x P A t)\<rbrakk> \<Longrightarrow> s \<in> \<D> (P \ A)\<close>
  unfolding D_Hiding_seqRun by blast

lemma D_Hiding_seqRunE :
  assumes \<open>s \<in> \<D> (P \ A)\<close>
  obtains t u where \<open>ftF u\<close> \<open>tF t\<close> \<open>s = trace_hide t (ev ` A) @ u\<close>
    \<open>t \<in> \<D> P \<or> (\<exists>x. isInfHidden_seqRun_strong x P A t)\<close>
proof -
  from \<open>s \<in> \<D> (P \ A)\<close> obtain t u
    where * : \<open>ftF u\<close> \<open>tF t\<close> \<open>s = trace_hide t (ev ` A) @ u\<close>
      \<open>t \<in> \<D> P \<or> (\<exists>x. isInfHidden_seqRun x P A t)\<close> unfolding D_Hiding_seqRun by blast
  from "*"(4) show thesis
  proof (elim disjE exE)
    from "*"(1, 2, 3) that show \<open>t \<in> \<D> P \<Longrightarrow> thesis\<close> by blast
  next
    fix x assume $ : \<open>isInfHidden_seqRun x P A t\<close>
    show thesis
    proof (cases \<open>\<exists>i. seqRun t x i \<in> \<D> P\<close>)
      assume \<open>\<exists>i. seqRun t x i \<in> \<D> P\<close>
      then obtain i where \<open>seqRun t x i \<in> \<D> P\<close> ..
      show thesis
      proof (rule that)
        show \<open>ftF u\<close> by (fact "*"(1))
      next
        show \<open>tF (seqRun t x i)\<close>
          by (metis "$" append_T_imp_tickFree neq_Nil_conv seqRun_Suc)
      next
        show \<open>s = trace_hide (seqRun t x i) (ev ` A) @ u\<close>
          by (simp add: "*"(3)) (metis "$" trace_hide_seqRun_eq_iff)
      next
        from \<open>seqRun t x i \<in> \<D> P\<close>
        show \<open>seqRun t x i \<in> \<D> P \<or>
              (\<exists>y. isInfHidden_seqRun_strong y P A (seqRun t x i))\<close> ..
      qed
    next
      from "*"(1, 2, 3) "$" that show \<open>\<nexists>i. seqRun t x i \<in> \<D> P \<Longrightarrow> thesis\<close> by blast
    qed
  qed
qed


lemma T_Hiding_seqRunE :
  assumes \<open>s \<in> \<T> (P \ A)\<close>
  obtains t where \<open>s = trace_hide t (ev ` A)\<close> \<open>(t, ev ` A) \<in> \<F> P\<close>
  | t u where \<open>ftF u\<close> \<open>tF t\<close> \<open>s = trace_hide t (ev ` A) @ u\<close>
    \<open>t \<in> \<D> P \<or> (\<exists>x. isInfHidden_seqRun_strong x P A t)\<close>
proof (cases \<open>s \<in> \<D> (P \ A)\<close>)
  assume \<open>s \<notin> \<D> (P \ A)\<close>
  with \<open>s \<in> \<T> (P \ A)\<close> have \<open>s \<in> {trace_hide t (ev ` A) |t. (t, ev ` A) \<in> \<F> P}\<close>
    unfolding D_Hiding T_Hiding by blast
  with that(1) show thesis by blast
qed (elim D_Hiding_seqRunE, presburger)


lemma butlast_seqRun : \<open>butlast (seqRun t x i) = (case i of 0 \<Rightarrow> butlast t
                                                      | Suc j \<Rightarrow> seqRun t x j)\<close>
  by (cases i) simp_all


lemma isInfHidden_seqRun_imp_tickFree : \<open>isInfHidden_seqRun x P A t \<Longrightarrow> tF t\<close>
  by (metis append_T_imp_tickFree not_Cons_self2 seqRun_0 seqRun_Suc)

lemma tickFree_seqRun_iff : \<open>tF (seqRun t x i) \<longleftrightarrow> tF t \<and> (\<forall>j<i. is_ev (x j))\<close>
  by (induct i; simp) (metis less_Suc_eq)

lemma front_tickFree_seqRun_iff :
  \<open>ftF (seqRun t x i) \<longleftrightarrow> (case i of 0 \<Rightarrow> ftF t | Suc j \<Rightarrow> tF t \<and> (\<forall>k<j. is_ev (x k)))\<close>
  by (cases i) (simp_all add: front_tickFree_iff_tickFree_butlast tickFree_seqRun_iff)


lemmas Hiding_seqRun_projs = F_Hiding_seqRun D_Hiding_seqRun T_Hiding_seqRun

(*<*)
end
  (*>*)