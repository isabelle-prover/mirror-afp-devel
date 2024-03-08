(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : HOL-CSP_OpSem - Operational semantics for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Burkhart Wolff
 *
 * This file       : New laws
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

chapter\<open> Bonus: powerful new Laws \<close>

theory  NewLaws
  imports Interrupt Sliding Throw
begin


(*<*)
hide_const R
text \<open>We need to hide this because we want to be allowed to use the letter R in our lemmas.
      We can still access this notion via the notation \<^term>\<open>\<R> P\<close>.
      In further versions of \<^theory>\<open>HOL-CSP.Process\<close>, R will be renamed in Refusals 
      and we will remove this paragraph.\<close>
(*>*)

section \<open>Powerful Results about \<^const>\<open>Renaming\<close>\<close>

text \<open>In this section we will provide laws about the \<^const>\<open>Renaming\<close> operator.
      In the first subsection we will give slight generalizations of previous results,
      but in the other we prove some very powerful theorems.\<close>

subsection \<open>Some Generalizations\<close>

text \<open>For \<^const>\<open>Renaming\<close>, we can obtain generalizations of the following results:

      @{thm Renaming_Mprefix[no_vars] Renaming_Mndetprefix[no_vars]}\<close>

lemma Renaming_Mprefix:
  \<open>Renaming (\<box>a \<in> A \<rightarrow> P a) f = 
   \<box>y \<in> f ` A \<rightarrow> \<sqinter>a \<in> {x \<in> A. y = f x}. Renaming (P a) f\<close> (is \<open>?lhs = ?rhs\<close>)
proof (subst Process_eq_spec_optimized, safe)
  show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close> for s
    by (auto simp add: D_Renaming D_Mprefix D_GlobalNdet hd_map_EvExt)
       (use list.map_sel(2) tickFree_tl in blast)
next
  fix s
  assume \<open>s \<in> \<D> ?rhs\<close>
  then obtain a s' where * : \<open>a \<in> A\<close> \<open>s = EvExt f (ev a) # s'\<close>
                             \<open>s' \<in> \<D> (Renaming (P a) f)\<close>
    by (simp add: D_Mprefix EvExt_def D_GlobalNdet split: if_split_asm)
       (metis list.collapse)
  from "*"(3) obtain s1 s2 
    where ** : \<open>tickFree s1\<close> \<open>front_tickFree s2\<close> 
               \<open>s' = map (EvExt f) s1 @ s2\<close> \<open>s1 \<in> \<D> (P a)\<close>
    by (simp add: D_Renaming) blast
  have *** : \<open>tickFree (ev a # s1) \<and> 
              s = EvExt f (ev a) # map (EvExt f) s1 @ s2 \<and> ev a # s1 \<in> \<D> (Mprefix A P)\<close>
    by (simp add: D_Mprefix "*"(1, 2) "**"(1, 3, 4))
  show \<open>s \<in> \<D> ?lhs\<close>
    by (simp add: D_Renaming )
       (metis "**"(2) "***" append_Cons list.simps(9))
next
  fix s X
  assume same_div: \<open>\<D> ?lhs = \<D> ?rhs\<close>
  assume \<open>(s, X) \<in> \<F> ?lhs\<close>
  then consider \<open>s \<in> \<D> ?lhs\<close>
    | \<open>\<exists>t. (t, EvExt f -` X) \<in> \<F> (Mprefix A P) \<and> s = map (EvExt f) t\<close>
    by (simp add: F_Renaming D_Renaming) blast
  thus \<open>(s, X) \<in> \<F> ?rhs\<close>
  proof cases
    from D_F same_div show \<open>s \<in> \<D> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> by blast
  next
    assume \<open>\<exists>t. (t, EvExt f -` X) \<in> \<F> (Mprefix A P) \<and> s = map (EvExt f) t\<close>
    then obtain t where * : \<open>(t, EvExt f -` X) \<in> \<F> (Mprefix A P)\<close> 
                            \<open>s = map (EvExt f) t\<close> by blast
    show \<open>(s, X) \<in> \<F> ?rhs\<close>
    proof (cases \<open>t = []\<close>)
      from "*" show \<open>t = [] \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
        by (simp add: F_Mprefix disjoint_iff_not_equal)
           (metis ev_elem_anteced1)
    next
      assume \<open>t \<noteq> []\<close>
      with "*"(1) obtain a t'
        where ** : \<open>a \<in> A\<close> \<open>t = ev a # t'\<close> \<open>(t', EvExt f -` X) \<in> \<F> (P a)\<close>
        by (simp add: F_Mprefix) (metis event.inject imageE list.exhaust_sel)
      have *** : \<open>s \<noteq> [] \<and> hd s \<in> ev ` f ` A\<close>
        using "*"(2) "**"(1, 2) hd_map_EvExt by fastforce
      with "**" have \<open>ev (f a) = hd s \<and> 
                     (tl s, X) \<in> \<F> (\<sqinter>a \<in> {x \<in> A. f a = f x}. Renaming (P a) f)\<close>
        by (simp add: F_GlobalNdet "*"(2) F_Renaming)
           (metis (no_types, opaque_lifting) \<open>t \<noteq> []\<close> hd_map hd_map_EvExt list.sel(1))
      with "***" show \<open>(s, X) \<in> \<F> ?rhs\<close> by (simp add: F_Mprefix) blast
    qed
  qed
next
  show \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for s X
  proof (cases s)
    show \<open>s = [] \<Longrightarrow> (s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
      by (simp add: F_Mprefix F_Renaming disjoint_iff_not_equal)
         (metis ev_elem_anteced1)
  next
    fix b s'
    assume \<open>s = b # s'\<close> \<open>(s, X) \<in> \<F> ?rhs\<close>
    then obtain a
      where * : \<open>a \<in> A\<close> \<open>s = (EvExt f) (ev a) # s'\<close> (* \<open>b = ev (f a)\<close> *)
                \<open>(s', X) \<in> \<F> (\<sqinter>a \<in> {x \<in> A. f a = f x}. Renaming (P a) f)\<close>
      by (auto simp add: F_Mprefix EvExt_def)
    from "*"(1, 3) obtain a'
      where ** : \<open>a' \<in> A\<close> \<open>f a' = f a\<close> \<open>(s', X) \<in> \<F> (Renaming (P a') f)\<close>
      by (auto simp add: F_GlobalNdet split: if_split_asm)
    from "**"(3) consider 
      \<open>\<exists>t. (t, EvExt f -` X) \<in> \<F> (P a') \<and> s' = map (EvExt f) t\<close>
      | \<open>\<exists>s1 s2. tickFree s1 \<and> front_tickFree s2 \<and> 
                 s' = map (EvExt f) s1 @ s2 \<and> s1 \<in> \<D> (P a')\<close>
      by (simp add: F_Renaming) blast
    thus \<open>(s, X) \<in> \<F> ?lhs\<close>
    proof cases
      assume \<open>\<exists>t. (t, EvExt f -` X) \<in> \<F> (P a') \<and> s' = map (EvExt f) t\<close>
      then obtain t where *** : \<open>(t, EvExt f -` X) \<in> \<F> (P a')\<close>
                                \<open>s' = map (EvExt f) t\<close> by blast
      have **** : \<open>(ev a' # t, EvExt f -` X) \<in> \<F> (Mprefix A P) \<and> 
                   s = map (EvExt f) (ev a' # t)\<close>
        by (simp add: F_Mprefix "*"(2) "**"(1) "***"(1, 2))
           (metis "**"(2) ev_elem_anteced1 vimage_singleton_eq)
      show \<open>(s, X) \<in> \<F> ?lhs\<close>
        apply (simp add: F_Renaming)
        using "****" by blast
    next
      assume \<open>\<exists>s1 s2. tickFree s1 \<and> front_tickFree s2 \<and> 
                      s' = map (EvExt f) s1 @ s2 \<and> s1 \<in> \<D> (P a')\<close>
      then obtain s1 s2
        where *** : \<open>tickFree s1\<close> \<open>front_tickFree s2\<close> 
                    \<open>s' = map (EvExt f) s1 @ s2\<close> \<open>s1 \<in> \<D> (P a')\<close> by blast
      have \<open>tickFree (ev a' # s1) \<and> 
            s = EvExt f (ev a') # map (EvExt f) s1 @ s2 \<and> 
            ev a' # s1 \<in> \<D> (Mprefix A P)\<close>
        by (simp add: "*"(2) "**"(1) "***" D_Mprefix) 
           (metis "**"(2) ev_elem_anteced1 vimage_singleton_eq)
      thus \<open>(s, X) \<in> \<F> ?lhs\<close> by (auto simp add: "***"(2) F_Renaming)   
    qed
  qed
qed


lemma Renaming_Mprefix_Sliding:
  \<open>Renaming ((\<box>a \<in> A \<rightarrow> P a) \<rhd> Q) f = 
   (\<box>y \<in> f ` A \<rightarrow> \<sqinter>a \<in> {x \<in> A. y = f x}. Renaming (P a) f) \<rhd> Renaming Q f\<close>
  unfolding Sliding_def
  by (simp add: Renaming_Ndet Renaming_Det Renaming_Mprefix)


lemma Renaming_GlobalNdet:
  \<open>Renaming (\<sqinter>a \<in> A. P a) f = \<sqinter>b \<in> f ` A. \<sqinter>a \<in> {a \<in> A. b = f a}. Renaming (P a) f\<close>
  by (simp add: Process_eq_spec F_Renaming
                F_GlobalNdet D_Renaming D_GlobalNdet) blast


lemma Renaming_Mndetprefix:
  \<open>Renaming (\<sqinter>a \<in> A \<rightarrow> P a) f = 
   \<sqinter>y \<in> f ` A \<rightarrow> \<sqinter>a \<in> {x \<in> A. y = f x}. Renaming (P a) f\<close> (is \<open>?lhs = ?rhs\<close>)
  apply (subst (1 2) Mndetprefix_GlobalNdet)
  apply (simp add: Renaming_GlobalNdet Renaming_prefix)
  apply (intro mono_GlobalNdet_eq ballI)
  apply (subst write0_GlobalNdet[symmetric], blast)
  by (simp add: mono_GlobalNdet_eq) 



subsection \<open>\<^const>\<open>Renaming\<close> and \<^const>\<open>Hiding\<close>\<close>

text \<open>When \<^term>\<open>f\<close> is one to one, \<^term>\<open>Renaming (P \ S) f\<close> will behave like we expect it to do.\<close>

lemma strict_mono_map: \<open>strict_mono g \<Longrightarrow> strict_mono (\<lambda>i. map f (g i))\<close>
  unfolding strict_mono_def less_list_def le_list_def
  by (metis list.map_disc_iff map_append self_append_conv)


lemma trace_hide_map_EvExt :
  \<open>inj_on (EvExt f) (set s \<union> ev ` S) \<Longrightarrow>
   trace_hide (map (EvExt f) s) (ev ` f ` S) = 
   map (EvExt f) (trace_hide s (ev ` S))\<close>
proof (induct s)
  case Nil
  show ?case by simp
next
  case (Cons a s)
  hence * : \<open>trace_hide (map (EvExt f) s) (ev ` f ` S) = 
             map (EvExt f) (trace_hide s (ev ` S))\<close> by fastforce
  from Cons.prems[unfolded inj_on_def, rule_format, of a, simplified] show ?case
    apply (simp add: "*")
    apply (simp add: image_iff split: event.split)
    by (metis ev_elem_anteced1 singletonI vimage_singleton_eq)
qed
  

lemma inj_on_EvExt_iff: \<open>inj_on (EvExt f) (insert tick (ev ` S)) \<longleftrightarrow> inj_on f S\<close>
  unfolding inj_on_def EvExt_def by (auto split: event.split)

lemma inj_on_EvExt_set_T:
  \<open>inj_on f (events_of P) \<Longrightarrow> s \<in> \<T> P \<Longrightarrow> inj_on (EvExt f) (insert tick (set s))\<close>
  unfolding inj_on_def EvExt_def events_of_def by (auto split: event.split)


theorem bij_Renaming_Hiding: \<open>Renaming (P \ S) f = Renaming P f \ f ` S\<close>
  (is \<open>?lhs = ?rhs\<close>) if bij_f: \<open>bij f\<close>
proof (subst Process_eq_spec_optimized, safe)
  fix s
  assume \<open>s \<in> \<D> ?lhs\<close>
  then obtain s1 s2 where * : \<open>tickFree s1\<close> \<open>front_tickFree s2\<close>
                              \<open>s = map (EvExt f) s1 @ s2\<close> \<open>s1 \<in> \<D> (P \ S)\<close>
    by (simp add: D_Renaming) blast
  from "*"(4) obtain t u
    where ** : \<open>front_tickFree u\<close> \<open>tickFree t\<close> \<open>s1 = trace_hide t (ev ` S) @ u\<close>
               \<open>t \<in> \<D> P \<or> (\<exists>g. isInfHiddenRun g P S \<and> t \<in> range g)\<close>
    by (simp add: D_Hiding) blast
  from "**"(4) show \<open>s \<in> \<D> ?rhs\<close>
  proof (elim disjE)
    assume \<open>t \<in> \<D> P\<close>
    hence \<open>front_tickFree (map (EvExt f) u @ s2) \<and> tickFree (map (EvExt f) t) \<and>
           s = trace_hide (map (EvExt f) t) (ev ` f ` S) @ map (EvExt f) u @ s2 \<and>
           map (EvExt f) t \<in> \<D> (Renaming P f)\<close>
      apply (simp add: "*"(3) "**"(2, 3) EvExt_tF, intro conjI)
      subgoal using "*"(1, 2) "**"(3) EvExt_tF front_tickFree_append tickFree_append by blast
      subgoal by (rule trace_hide_map_EvExt[symmetric];
              use bij_f in \<open>unfold bij_def inj_on_def EvExt_def, auto split: event.split\<close>)
      using "**"(2) D_Renaming front_tickFree_Nil by blast
    thus \<open>s \<in> \<D> ?rhs\<close> by (simp add: D_Hiding) blast
  next
    assume \<open>\<exists>g. isInfHiddenRun g P S \<and> t \<in> range g\<close>
    then obtain g where \<open>isInfHiddenRun g P S\<close> \<open>t \<in> range g\<close> by blast
    hence \<open>front_tickFree (map (EvExt f) u @ s2) \<and>
           tickFree (map (EvExt f) t) \<and>
           s = trace_hide (map (EvExt f) t) (ev ` f ` S) @ map (EvExt f) u @ s2 \<and>
           isInfHiddenRun (\<lambda>i. map (EvExt f) (g i)) (Renaming P f) (f ` S) \<and> 
           map (EvExt f) t \<in> range (\<lambda>i. map (EvExt f) (g i))\<close>
      apply (simp add: "*"(3) "**"(2, 3) EvExt_tF, intro conjI)
      subgoal using "*"(1, 2) "**"(3) EvExt_tF front_tickFree_append tickFree_append by blast
      subgoal by (rule trace_hide_map_EvExt[symmetric];
                 use bij_f in \<open>unfold bij_def inj_on_def EvExt_def, auto split: event.split\<close>)
      subgoal using strict_mono_map by blast
      subgoal by (solves \<open>auto simp add: T_Renaming\<close>)
      subgoal apply (subst (1 2) trace_hide_map_EvExt)
        by (use bij_f in \<open>unfold bij_def inj_on_def EvExt_def, auto split: event.split\<close>) metis
      subgoal by blast
      done
    thus \<open>s \<in> \<D> ?rhs\<close> by (simp add: D_Hiding) blast
  qed
next
  fix s
  assume \<open>s \<in> \<D> ?rhs\<close>
  then obtain t u
    where * : \<open>front_tickFree u\<close> \<open>tickFree t\<close> \<open>s = trace_hide t (ev ` f ` S) @ u\<close>
              \<open>t \<in> \<D> (Renaming P f) \<or> 
               (\<exists>g. isInfHiddenRun g (Renaming P f) (f ` S) \<and> t \<in> range g)\<close>
    by (simp add: D_Hiding) blast
  from "*"(4) show \<open>s \<in> \<D> ?lhs\<close>
  proof (elim disjE)
    assume \<open>t \<in> \<D> (Renaming P f)\<close>
    then obtain t1 t2 where ** : \<open>tickFree t1\<close> \<open>front_tickFree t2\<close> 
                                 \<open>t = map (EvExt f) t1 @ t2\<close> \<open>t1 \<in> \<D> P\<close>
      by (simp add: D_Renaming) blast
    have \<open>tickFree (trace_hide t1 (ev ` S)) \<and> 
          front_tickFree (trace_hide t2 (ev ` f ` S) @ u) \<and>
          trace_hide (map (EvExt f) t1) (ev ` f ` S) @ trace_hide t2 (ev ` f ` S) @ u =
          map (EvExt f) (trace_hide t1 (ev ` S)) @ trace_hide t2 (ev ` f ` S) @ u \<and>
          trace_hide t1 (ev ` S) \<in> \<D> (P \ S)\<close>
      apply (simp, intro conjI)
      subgoal using "**"(1) Hiding_tickFree by blast
      subgoal using "*"(1, 2) "**"(3) Hiding_tickFree front_tickFree_append tickFree_append by blast
      subgoal by (rule trace_hide_map_EvExt;
              use bij_f in \<open>unfold bij_def inj_on_def EvExt_def, simp split: event.split\<close>)
      subgoal using "**"(4) elemDIselemHD by blast
      done
    thus \<open>s \<in> \<D> ?lhs\<close> by (simp add: D_Renaming "*"(3) "**"(3)) blast
  next
    have inv_S: \<open>S = inv f ` f ` S\<close> by (simp add: bij_is_inj bij_f)
    have inj_inv_f: \<open>inj (inv f)\<close> 
      by (simp add: bij_imp_bij_inv bij_is_inj bij_f)
    have ** : \<open>map (EvExt (inv f) \<circ> EvExt f) v = v\<close> for v
        by (induct v, unfold EvExt_def, auto split: event.split)
           (metis bij_inv_eq_iff bij_f)
    assume \<open>\<exists>g. isInfHiddenRun g (Renaming P f) (f ` S) \<and> t \<in> range g\<close>
    then obtain g
      where *** : \<open>isInfHiddenRun g (Renaming P f) (f ` S)\<close> \<open>t \<in> range g\<close> by blast
    then consider \<open>\<exists>t1. t1 \<in> \<T> P \<and> t = map (EvExt f) t1\<close>
      | \<open>\<exists>t1 t2. tickFree t1 \<and> front_tickFree t2 \<and> 
                 t = map (EvExt f) t1 @ t2 \<and> t1 \<in> \<D> P\<close>
      by (simp add: T_Renaming) blast
    thus \<open>s \<in> \<D> ?lhs\<close>
    proof cases
      assume \<open>\<exists>t1. t1 \<in> \<T> P \<and> t = map (EvExt f) t1\<close>
      then obtain t1 where **** : \<open>t1 \<in> \<T> P\<close> \<open>t = map (EvExt f) t1\<close> by blast
      have ***** : \<open>t1 = map (EvExt (inv f)) t\<close> by (simp add: "****"(2) "**")
      have ****** : \<open>trace_hide t1 (ev ` S) = trace_hide t1 (ev ` S) \<and>
                     isInfHiddenRun (\<lambda>i. map (EvExt (inv f)) (g i)) P S \<and> 
                     t1 \<in> range (\<lambda>i. map (EvExt (inv f)) (g i))\<close>
        apply (simp add: "***"(1) strict_mono_map, intro conjI)
        subgoal apply (subst Renaming_inv[where f = f, symmetric])
           apply (solves \<open>simp add: bij_is_inj bij_f\<close>)
          using "***"(1) by (subst T_Renaming, blast)
        subgoal apply (subst (1 2) inv_S, subst (1 2) trace_hide_map_EvExt)
          by (use bij_f in \<open>unfold bij_def inj_on_def EvExt_def, 
                                auto simp add: inj_eq inj_inv_f split: event.split\<close>)
              (metis "***"(1))
        subgoal using "***"(2) "*****" by blast
        done
      have \<open>tickFree (trace_hide t1 (ev ` S)) \<and> front_tickFree t1 \<and>
            trace_hide (map (EvExt f) t1) (ev ` f ` S) @ u = 
            map (EvExt f) (trace_hide t1 (ev ` S)) @ u \<and> 
            trace_hide t1 (ev ` S) \<in> \<D> (P \ S)\<close>
        apply (simp, intro conjI)
        subgoal using "*"(2) "****"(2) EvExt_tF Hiding_tickFree by blast

        subgoal using "****"(1) is_processT2_TR by blast
        apply (rule trace_hide_map_EvExt,
                use bij_f in \<open>unfold bij_def inj_on_def EvExt_def, auto split: event.split\<close>)[1]
        apply (simp add: D_Renaming D_Hiding)
        using "*"(2) "*****" "******" EvExt_tF front_tickFree_Nil by blast
      with "*"(1) show \<open>s \<in> \<D> ?lhs\<close> by (simp add: D_Renaming "*"(3) "****"(2)) blast
    next
      assume \<open>\<exists>t1 t2. tickFree t1 \<and> front_tickFree t2 \<and> 
                      t = map (EvExt f) t1 @ t2 \<and> t1 \<in> \<D> P\<close>
      then obtain t1 t2
        where **** : \<open>tickFree t1\<close> \<open>front_tickFree t2\<close>
                     \<open>t = map (EvExt f) t1 @ t2\<close> \<open>t1 \<in> \<D> P\<close> by blast
      have \<open>tickFree (trace_hide t1 (ev ` S)) \<and>
            front_tickFree (trace_hide t2 (ev ` f ` S) @ u) \<and>
            trace_hide (map (EvExt f) t1) (ev ` f ` S) @ trace_hide t2 (ev ` f ` S) @ u =
            map (EvExt f) (trace_hide t1 (ev ` S)) @ trace_hide t2 (ev ` f ` S) @ u \<and>
            trace_hide t1 (ev ` S) \<in> \<D> (P \ S)\<close>
        apply (simp, intro conjI)
        subgoal using "****"(1) Hiding_tickFree by blast
        subgoal using "*"(1, 2) "****"(3) Hiding_tickFree front_tickFree_append tickFree_append by blast
        subgoal by (rule trace_hide_map_EvExt;
                use bij_f in \<open>unfold bij_def inj_on_def EvExt_def, simp split: event.split\<close>)
        subgoal using "****"(4) elemDIselemHD by blast
        done
      thus \<open>s \<in> \<D> ?lhs\<close> by (simp add: D_Renaming "*"(3) "****"(3)) blast
    qed
  qed
next
  fix s X
  assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
  assume \<open>(s, X) \<in> \<F> ?lhs\<close>
  then consider \<open>s \<in> \<D> ?lhs\<close>
    | \<open>\<exists>s1. (s1, EvExt f -` X) \<in> \<F> (P \ S) \<and> s = map (EvExt f) s1\<close>
    by (simp add: F_Renaming D_Renaming) blast
  thus \<open>(s, X) \<in> \<F> ?rhs\<close>
  proof cases
    from D_F same_div show \<open>s \<in> \<D> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> by blast
  next
    assume \<open>\<exists>s1. (s1, EvExt f -` X) \<in> \<F> (P \ S) \<and> s = map (EvExt f) s1\<close>
    then obtain s1 where * : \<open>(s1, EvExt f -` X) \<in> \<F> (P \ S)\<close>
                             \<open>s = map (EvExt f) s1\<close> by blast
    from this(1) consider \<open>s1 \<in> \<D> (P \ S)\<close>
      | \<open>\<exists>t. s1 = trace_hide t (ev ` S) \<and> (t, EvExt f -` X \<union> ev ` S) \<in> \<F> P\<close>
      by (simp add: F_Hiding D_Hiding) blast
    thus \<open>(s, X) \<in> \<F> ?rhs\<close>
    proof cases
      assume \<open>s1 \<in> \<D> (P \ S)\<close>
      then obtain t u
        where ** : \<open>front_tickFree u\<close> \<open>tickFree t\<close> \<open>s1 = trace_hide t (ev ` S) @ u\<close>
                   \<open>t \<in> \<D> P \<or> (\<exists>g. isInfHiddenRun g P S \<and> t \<in> range g)\<close>
        by (simp add: D_Hiding) blast
      have *** : \<open>front_tickFree (map (EvExt f) u) \<and> tickFree (map (EvExt f) t) \<and>
                  map (EvExt f) (trace_hide t (ev ` S)) @ map (EvExt f) u = 
                  trace_hide (map (EvExt f) t) (ev ` f ` S) @ (map (EvExt f) u)\<close>
        by (simp add: EvExt_ftF EvExt_tF "**"(1, 2))
           (rule trace_hide_map_EvExt[symmetric];
            use bij_f in \<open>unfold bij_def inj_on_def EvExt_def, simp split: event.split\<close>)
      from "**"(4) show \<open>(s, X) \<in> \<F> ?rhs\<close>
      proof (elim disjE)
        assume \<open>t \<in> \<D> P\<close>
        hence $ : \<open>map (EvExt f) t \<in> \<D> (Renaming P f)\<close>
          apply (simp add: D_Renaming)
          using "**"(2) front_tickFree_Nil by blast
        show \<open>(s, X) \<in> \<F> ?rhs\<close>
          by (simp add: F_Hiding) (metis "$" "*"(2) "**"(3) "***" map_append)
      next
        assume \<open>\<exists>g. isInfHiddenRun g P S \<and> t \<in> range g\<close>
        then obtain g where \<open>isInfHiddenRun g P S\<close> \<open>t \<in> range g\<close> by blast
        hence $ : \<open>isInfHiddenRun (\<lambda>i. map (EvExt f) (g i)) (Renaming P f) (f ` S) \<and> 
                   map (EvExt f) t \<in> range (\<lambda>i. map (EvExt f) (g i))\<close>
          apply (subst (1 2) trace_hide_map_EvExt,
                 (use bij_f in \<open>unfold bij_def inj_on_def EvExt_def, auto split: event.split\<close>)[2])
          by (simp add: strict_mono_map T_Renaming image_iff) (metis (mono_tags, lifting))
        show \<open>(s, X) \<in> \<F> ?rhs\<close>
          by (simp add: F_Hiding) 
             (metis (mono_tags, lifting) "$" "*"(2) "**"(3) "***" map_append)
      qed
    next
      assume \<open>\<exists>t. s1 = trace_hide t (ev ` S) \<and> (t, EvExt f -` X \<union> ev ` S) \<in> \<F> P\<close>
      then obtain t where ** : \<open>s1 = trace_hide t (ev ` S)\<close> 
                               \<open>(t, EvExt f -` X \<union> ev ` S) \<in> \<F> P\<close> by blast
      have *** : \<open>EvExt f -` X \<union> EvExt f -` ev ` f ` S = EvExt f -` X \<union> ev ` S\<close>
        by (use bij_f in \<open>unfold bij_def inj_on_def EvExt_def, auto simp add: image_iff split: event.split\<close>)
           (metis (no_types, opaque_lifting) event.distinct(1) event.exhaust event.simps(4, 5) o_apply)
      have \<open>map (EvExt f) (trace_hide t (ev ` S)) = 
            trace_hide (map (EvExt f) t) (ev ` f ` S) \<and>
            (map (EvExt f) t, X \<union> ev ` f ` S) \<in> \<F> (Renaming P f)\<close>
        apply (intro conjI)
         apply (rule trace_hide_map_EvExt[symmetric];
                use bij_f in \<open>unfold bij_def inj_on_def EvExt_def, simp split: event.split\<close>)
        apply (simp add: F_Renaming)
        using "**"(2) "***" by auto
      show \<open>(s, X) \<in> \<F> ?rhs\<close>
        apply (simp add: F_Hiding "*"(2) "**"(1))
        using \<open>?this\<close> by blast
    qed
  qed
next
  fix s X
  assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
  assume \<open>(s, X) \<in> \<F> ?rhs\<close>
  then consider \<open>s \<in> \<D> ?rhs\<close>
    | \<open>\<exists>t. s = trace_hide t (ev ` f ` S) \<and> 
           (t, X \<union> ev ` f ` S) \<in> \<F> (Renaming P f)\<close>
    by (simp add: F_Hiding D_Hiding) blast
  thus \<open>(s, X) \<in> \<F> ?lhs\<close>
  proof cases
    from D_F same_div show \<open>s \<in> \<D> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> by blast
  next
    assume \<open>\<exists>t. s = trace_hide t (ev ` f ` S) \<and>
                (t, X \<union> ev ` f ` S) \<in> \<F> (Renaming P f)\<close>
    then obtain t
      where * : \<open>s = trace_hide t (ev ` f ` S)\<close>
                \<open>(t, X \<union> ev ` f ` S) \<in> \<F> (Renaming P f)\<close> by blast
    have ** : \<open>EvExt f -` X \<union> EvExt f -` ev ` f ` S = EvExt f -` X \<union> ev ` S\<close>
        by (use bij_f in \<open>unfold bij_def inj_on_def EvExt_def, auto simp add: image_iff split: event.split\<close>)
           (metis (no_types, opaque_lifting) event.distinct(1) event.exhaust event.simps(4, 5) o_apply)
    have \<open>(\<exists>s1. (s1, EvExt f -` X \<union> EvExt f -` ev ` f ` S) \<in> \<F> P \<and> t = map (EvExt f) s1) \<or> 
          (\<exists>s1 s2. tickFree s1 \<and> front_tickFree s2 \<and> t = map (EvExt f) s1 @ s2 \<and> s1 \<in> \<D> P)\<close>
      using "*"(2) by (simp add: F_Renaming)
    thus \<open>(s, X) \<in> \<F> ?lhs\<close>
    proof (elim disjE exE conjE)
      fix s1
      assume \<open>(s1, EvExt f -` X \<union> EvExt f -` ev ` f ` S) \<in> \<F> P\<close> \<open>t = map (EvExt f) s1\<close>
      hence \<open>(trace_hide s1 (ev ` S), EvExt f -` X) \<in> \<F> (P \ S) \<and>
             s = map (EvExt f) (trace_hide s1 (ev ` S))\<close>
        apply (simp add: "*"(1) F_Hiding "**", intro conjI)
         apply blast
        by (rule trace_hide_map_EvExt;
            use bij_f in \<open>unfold bij_def inj_on_def EvExt_def, simp split: event.split\<close>)
      show \<open>(s, X) \<in> \<F> ?lhs\<close>
        apply (simp add: F_Renaming)
        using \<open>?this\<close> by blast
    next
      fix s1 s2
      assume \<open>tickFree s1\<close> \<open>front_tickFree s2\<close> \<open>t = map (EvExt f) s1 @ s2\<close> \<open>s1 \<in> \<D> P\<close>
      hence \<open>tickFree (trace_hide s1 (ev ` S)) \<and> 
             front_tickFree (trace_hide s2 (ev ` f ` S)) \<and> 
             s = map (EvExt f) (trace_hide s1 (ev ` S)) @ trace_hide s2 (ev ` f ` S) \<and> 
             trace_hide s1 (ev ` S) \<in> \<D> (P \ S)\<close>
        apply (simp add: F_Renaming "*"(1), intro conjI)
        subgoal using Hiding_tickFree by blast
        subgoal using Hiding_fronttickFree by blast
         apply (rule trace_hide_map_EvExt;
                use bij_f in \<open>unfold bij_def inj_on_def EvExt_def, simp split: event.split\<close>)
        using elemDIselemHD by blast
      show \<open>(s, X) \<in> \<F> ?lhs\<close>
        apply (simp add: F_Renaming)
        using \<open>?this\<close> by blast
    qed
  qed
qed



subsection \<open>\<^const>\<open>Renaming\<close> and \<^const>\<open>Sync\<close>\<close>

text \<open>Idem for the synchronization: when \<^term>\<open>f\<close> is one to one, 
      \<^term>\<open>Renaming (P \<lbrakk>S\<rbrakk> Q)\<close> will behave as expected.\<close>

lemma exists_map_antecedent_if_subset_range:
  \<open>set u \<subseteq> range f \<Longrightarrow> \<exists>t. u = map f t\<close>
  \<comment> \<open>In particular, when \<^term>\<open>f\<close> is surjective or bijective.\<close>
proof (induct u)
  show \<open>\<exists>t. [] = map f t\<close> by simp
next
  fix a u
  assume prem : \<open>set (a # u) \<subseteq> range f\<close>
     and  hyp : \<open>set u \<subseteq> range f \<Longrightarrow> \<exists>t. u = map f t\<close>
  then obtain t where * : \<open>u = map f t\<close> 
    by (meson set_subset_Cons subset_trans)
  from prem obtain x where ** : \<open>f x = a\<close> by auto
  show \<open>\<exists>t. a # u = map f t\<close>
  proof (intro exI)
    show \<open>a # u = map f (x # t)\<close> by (simp add: "*" "**")
  qed
qed


lemma bij_map_setinterleaving_iff_setinterleaving :
  \<open>map f r setinterleaves ((map f t, map f u), f ` S) \<longleftrightarrow>
   r setinterleaves ((t, u), S)\<close> if bij_f : \<open>bij f\<close>
proof (induct \<open>(t, S, u)\<close> arbitrary: t u r rule: setinterleaving.induct)
  case 1
  thus ?case by simp
next
  case (2 y u)
  show ?case
  proof (cases \<open>y \<in> S\<close>)
    show \<open>y \<in> S \<Longrightarrow> ?case\<close> by simp
  next
    assume \<open>y \<notin> S\<close>
    hence \<open>f y \<notin> f ` S\<close> by (metis bij_betw_imp_inj_on inj_image_mem_iff bij_f)
    with "2.hyps"[OF \<open>y \<notin> S\<close>, of \<open>tl r\<close>] show ?case
      by (cases r; simp add: \<open>y \<notin> S\<close>) (metis bij_pointE bij_f)
  qed
next
  case (3 x t)
  show ?case
  proof (cases \<open>x \<in> S\<close>)
    show \<open>x \<in> S \<Longrightarrow> ?case\<close> by simp
  next
    assume \<open>x \<notin> S\<close>
    hence \<open>f x \<notin> f ` S\<close> by (metis bij_betw_imp_inj_on inj_image_mem_iff bij_f)
    with "3.hyps"[OF \<open>x \<notin> S\<close>, of \<open>tl r\<close>] show ?case
      by (cases r; simp add: \<open>x \<notin> S\<close>) (metis bij_pointE bij_f)
  qed
next
  case (4 x t y u)
  have  * : \<open>x \<noteq> y \<Longrightarrow> f x \<noteq> f y\<close> by (metis bij_pointE bij_f)
  have ** : \<open>f z \<in> f ` S \<longleftrightarrow> z \<in> S\<close> for z
    by (meson bij_betw_def inj_image_mem_iff bij_f)
  show ?case
  proof (cases \<open>x \<in> S\<close>; cases \<open>y \<in> S\<close>)
    from "4.hyps"(1)[of \<open>tl r\<close>] show \<open>x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> ?case\<close>
      by (cases r; simp add: "*") (metis bij_pointE bij_f)
  next
    from "4.hyps"(2)[of \<open>tl r\<close>] show \<open>x \<in> S \<Longrightarrow> y \<notin> S \<Longrightarrow> ?case\<close>
      by (cases r; simp add: "**") (metis bij_pointE bij_f)
  next
    from "4.hyps"(5)[of \<open>tl r\<close>] show \<open>x \<notin> S \<Longrightarrow> y \<in> S \<Longrightarrow> ?case\<close>
      by (cases r; simp add: "**") (metis bij_pointE bij_f)
  next
    from "4.hyps"(3, 4)[of \<open>tl r\<close>] show \<open>x \<notin> S \<Longrightarrow> y \<notin> S \<Longrightarrow> ?case\<close>
      by (cases r; simp add: "**") (metis bij_pointE bij_f)
  qed
qed


theorem bij_Renaming_Sync:
  \<open>Renaming (P \<lbrakk>S\<rbrakk> Q) f = Renaming P f \<lbrakk>f ` S\<rbrakk> Renaming Q f\<close>
  (is \<open>?lhs P Q = ?rhs P Q\<close>) if bij_f: \<open>bij f\<close>
proof -
  \<comment> \<open>Three intermediate results.\<close>
  have bij_EvExt_f : \<open>bij (EvExt f)\<close>
  proof (unfold bij_iff EvExt_def, intro allI ex1I)
    show \<open>(case (EvExt (inv f)) e of ev x \<Rightarrow> (ev \<circ> f) x | tick \<Rightarrow> tick) = e\<close> for e
      by (simp add: EvExt_def split: event.split)
         (meson bij_inv_eq_iff bij_f)
  next
    show \<open>(case e' of ev x \<Rightarrow> (ev \<circ> f) x | tick \<Rightarrow> tick) = e \<Longrightarrow>
          e' = EvExt (inv f) e\<close> for e e'
      by (simp add: EvExt_def split: event.splits)
         (metis bij_inv_eq_iff event.inject event.simps(3) bij_f)
  qed
  have EvExt_inv_f_is_inv_EvExt_f : \<open>inv (EvExt f) = EvExt (inv f)\<close>
  proof -
    have \<open>EvExt (inv f) \<circ> EvExt f = id\<close>
      by (rule ext, simp add: EvExt_def split: event.split)
         (meson bij_betw_imp_inj_on inv_f_eq bij_f)
    thus \<open>inv (EvExt f) = EvExt (inv f)\<close>  
      by (metis EvExt_comp EvExt_id bij_betw_def inv_unique_comp surj_iff that)
  qed
  have sets_S_eq : \<open>(EvExt f) ` (insert tick (ev ` S)) = insert tick (ev ` f ` S)\<close>
    unfolding EvExt_def image_def by auto

  show \<open>?lhs P Q = ?rhs P Q\<close>
  proof (subst Process_eq_spec_optimized, safe)
    fix s
    assume \<open>s \<in> \<D> (?lhs P Q)\<close>
    then obtain s1 s2 where * : \<open>tickFree s1\<close> \<open>front_tickFree s2\<close>
                                \<open>s = map (EvExt f) s1 @ s2\<close> \<open>s1 \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
      by (simp add: D_Renaming) blast
    from "*"(4) obtain t u r v 
      where ** : \<open>front_tickFree v\<close> \<open>tickFree r \<or> v = []\<close> 
                 \<open>s1 = r @ v\<close> \<open>r setinterleaves ((t, u), insert tick (ev ` S))\<close>
                 \<open>t \<in> \<D> P \<and> u \<in> \<T> Q \<or> t \<in> \<D> Q \<and> u \<in> \<T> P\<close> 
      by (simp add: D_Sync) blast
    { fix t u P Q
      assume assms : \<open>r setinterleaves ((t, u), insert tick (ev ` S))\<close> 
                     \<open>t \<in> \<D> P\<close> \<open>u \<in> \<T> Q\<close>
      have \<open>map (EvExt f) r setinterleaves 
            ((map (EvExt f) t, map (EvExt f) u), insert tick (ev ` f ` S))\<close>
        by (metis assms(1) bij_EvExt_f 
                  bij_map_setinterleaving_iff_setinterleaving sets_S_eq)
      moreover have \<open>map (EvExt f) t \<in> \<D> (Renaming P f)\<close>
        apply (cases \<open>tickFree t\<close>; simp add: D_Renaming)
        using assms(2) front_tickFree_Nil apply blast
        by (metis (no_types, lifting) assms(2) butlast_snoc front_tickFree_butlast
                                      front_tickFree_single map_EvExt_tick map_append 
                                      nonTickFree_n_frontTickFree process_charn)
      moreover have \<open>map (EvExt f) u \<in> \<T> (Renaming Q f)\<close>
        using assms(3) by (simp add: T_Renaming) blast
      ultimately have \<open>s \<in> \<D> (?rhs P Q)\<close>
        by (simp add: D_Sync "*"(3) "**"(3))
           (metis "*"(1, 2) "**"(3) EvExt_tF front_tickFree_append tickFree_append)
    } note *** = this

    from "**"(4, 5) "***" show \<open>s \<in> \<D> (?rhs P Q)\<close>
      apply (elim disjE)
      using "**"(4) "***" apply blast
      using "**"(4) "***" by (subst Sync_commute) blast
  next
    fix s
    assume \<open>s \<in> \<D> (?rhs P Q)\<close>
    then obtain t u r v
      where * : \<open>front_tickFree v\<close> \<open>tickFree r \<or> v = []\<close> \<open>s = r @ v\<close> 
                \<open>r setinterleaves ((t, u), insert tick (ev ` f ` S))\<close>
                \<open>t \<in> \<D> (Renaming P f) \<and> u \<in> \<T> (Renaming Q f) \<or>
                 t \<in> \<D> (Renaming Q f) \<and> u \<in> \<T> (Renaming P f)\<close>
      by (simp add: D_Sync) blast

    { fix t u P Q
      assume assms : \<open>r setinterleaves ((t, u), insert tick (ev ` f ` S))\<close> 
                     \<open>t \<in> \<D> (Renaming P f)\<close> \<open>u \<in> \<T> (Renaming Q f)\<close>
      have ** : \<open>(map (inv (EvExt f)) r) setinterleaves
                 ((map (inv (EvExt f)) t, map (inv (EvExt f)) u), insert tick (ev ` S))\<close>
        by (metis (no_types) assms(1) bij_EvExt_f bij_betw_imp_inj_on
                             bij_betw_inv_into  image_inv_f_f sets_S_eq
                             bij_map_setinterleaving_iff_setinterleaving)
      have \<open>map (EvExt (inv f)) t \<in> \<D> (Renaming (Renaming P f) (inv f))\<close>
        by (subst D_Renaming, simp)
           (metis EvExt_ftF append.right_neutral assms(2) front_tickFree_implies_tickFree 
                  front_tickFree_single map_append nonTickFree_n_frontTickFree process_charn)
      hence *** : \<open>map (inv (EvExt f)) t \<in> \<D> P\<close>
        by (simp add: Renaming_inv bij_is_inj bij_f EvExt_inv_f_is_inv_EvExt_f)
      have \<open>map (EvExt (inv f)) u \<in> \<T> (Renaming (Renaming Q f) (inv f))\<close>
        using assms(3) by (subst T_Renaming, simp) blast
      hence **** : \<open>map (inv (EvExt f)) u \<in> \<T> Q\<close>
        by (simp add: Renaming_inv bij_is_inj bij_f EvExt_inv_f_is_inv_EvExt_f)
      have ***** : \<open>map (EvExt f \<circ> inv (EvExt f)) r = r\<close>
        by (metis bij_EvExt_f bij_betw_imp_surj list.map_id surj_iff)
      have \<open>s \<in> \<D> (?lhs P Q)\<close>
      proof (cases \<open>tickFree r\<close>)
        assume \<open>tickFree r\<close>
        have $ : \<open>r @ v = map (EvExt f) (map (inv (EvExt f)) r) @ v\<close>
          by (simp add: "*****")
        show \<open>s \<in> \<D> (?lhs P Q)\<close>
          apply (simp add: D_Renaming D_Sync "*"(3))
          by (metis "$" "*"(1) "**" "***" "****" EvExt_tF \<open>tickFree r\<close> 
                    append.right_neutral append_same_eq front_tickFree_Nil)
      next
        assume \<open>\<not> tickFree r\<close>
        then obtain r' where $ : \<open>r = r' @ [tick]\<close> \<open>tickFree r'\<close>
          by (metis D_imp_front_tickFree assms front_tickFree_implies_tickFree ftf_Sync
                    is_processT2_TR nonTickFree_n_frontTickFree)
        then obtain t' u'
          where $$ : \<open>t = t' @ [tick]\<close> \<open>u = u' @ [tick]\<close>
          using SyncWithTick_imp_NTF D_T assms by blast
        hence $$$ : \<open>(map (inv (EvExt f)) r') setinterleaves
                     ((map (inv (EvExt f)) t', map (inv (EvExt f)) u'),
                      insert tick (ev ` S))\<close>
          by (metis "$"(1) assms(1) bij_EvExt_f bij_betw_imp_inj_on 
                    bij_betw_inv_into bij_map_setinterleaving_iff_setinterleaving
                    butlast_snoc ftf_Sync32 image_inv_f_f sets_S_eq)
        from "***" $$(1) have *** : \<open>map (inv (EvExt f)) t' \<in> \<D> P\<close> 
          by simp (metis EvExt_inv_f_is_inv_EvExt_f is_processT9 tick_eq_EvExt)
        from "****" $$(2) have **** : \<open>map (inv (EvExt f)) u' \<in> \<T> Q\<close>
          using is_processT3_ST by simp blast
        have $$$$ : \<open>r = map (EvExt f) (map (inv (EvExt f)) r') @ [tick]\<close>
          using "$" "*****" by auto
        show \<open>s \<in> \<D> (?lhs P Q)\<close>
          by (simp add: D_Renaming D_Sync "*"(3) "$$$")
             (metis "$"(1) "$"(2) "$$$" "$$$$" "*"(2) "***" "****" EvExt_tF \<open>\<not> tickFree r\<close>
                    append.right_neutral append_same_eq front_tickFree_Nil front_tickFree_single)
      qed
    } note ** = this
    show \<open>s \<in> \<D> (?lhs P Q)\<close> by (metis "*"(4, 5) "**" Sync_commute)
  next
    fix s X
    assume same_div : \<open>\<D> (?lhs P Q) = \<D> (?rhs P Q)\<close>
    assume \<open>(s, X) \<in> \<F> (?lhs P Q)\<close>
    then consider \<open>s \<in> \<D> (?lhs P Q)\<close>
      | \<open>\<exists>s1. (s1, EvExt f -` X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q) \<and> s = map (EvExt f) s1\<close>
      by (simp add: F_Renaming D_Renaming) blast
    thus \<open>(s, X) \<in> \<F> (?rhs P Q)\<close>
    proof cases
      from same_div D_F show \<open>s \<in> \<D> (?lhs P Q) \<Longrightarrow> (s, X) \<in> \<F> (?rhs P Q)\<close> by blast
    next
      assume \<open>\<exists>s1. (s1, EvExt f -` X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q) \<and> s = map (EvExt f) s1\<close>
      then obtain s1 where * : \<open>(s1, EvExt f -` X) \<in> \<F> (P \<lbrakk>S\<rbrakk> Q)\<close> 
                               \<open>s = map (EvExt f) s1\<close> by blast
      from "*"(1) consider \<open>s1 \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
        | \<open>\<exists>t_P t_Q X_P X_Q. 
           (t_P, X_P) \<in> \<F> P \<and> (t_Q, X_Q) \<in> \<F> Q \<and>
           s1 setinterleaves ((t_P, t_Q), insert tick (ev ` S)) \<and>
           EvExt f -` X = (X_P \<union> X_Q) \<inter> insert tick (ev ` S) \<union> X_P \<inter> X_Q\<close>
        by (simp add: F_Sync D_Sync) blast
      thus \<open>(s, X) \<in> \<F> (?rhs P Q)\<close>
      proof cases
        assume \<open>s1 \<in> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
        hence \<open>s \<in> \<D> (?lhs P Q)\<close>
          apply (cases \<open>tickFree s1\<close>; simp add: D_Renaming "*"(2)) 
          using front_tickFree_Nil apply blast
          by (metis (no_types, lifting) EvExt_ftF butlast_snoc front_tickFree_butlast
                    front_tickFree_single map_butlast nonTickFree_n_frontTickFree process_charn)
        with same_div D_F show \<open>(s, X) \<in> \<F> (?rhs P Q)\<close> by blast
      next
        assume \<open>\<exists>t_P t_Q X_P X_Q. 
                (t_P, X_P) \<in> \<F> P \<and> (t_Q, X_Q) \<in> \<F> Q \<and>
                s1 setinterleaves ((t_P, t_Q), insert tick (ev ` S)) \<and>
                EvExt f -` X = (X_P \<union> X_Q) \<inter> insert tick (ev ` S) \<union> X_P \<inter> X_Q\<close>
        then obtain t_P t_Q X_P X_Q
          where ** : \<open>(t_P, X_P) \<in> \<F> P\<close> \<open>(t_Q, X_Q) \<in> \<F> Q\<close>
                     \<open>s1 setinterleaves ((t_P, t_Q), insert tick (ev ` S))\<close>
                     \<open>EvExt f -` X = (X_P \<union> X_Q) \<inter> insert tick (ev ` S) \<union> X_P \<inter> X_Q\<close> by blast
        have \<open>(map (EvExt f) t_P, (EvExt f) ` X_P) \<in> \<F> (Renaming P f)\<close>
          by (simp add: F_Renaming)
             (metis "**"(1) bij_EvExt_f bij_betw_imp_inj_on inj_vimage_image_eq)
        moreover have \<open>(map (EvExt f) t_Q, (EvExt f) ` X_Q) \<in> \<F> (Renaming Q f)\<close>
          by (simp add: F_Renaming)
             (metis "**"(2) bij_EvExt_f bij_betw_imp_inj_on inj_vimage_image_eq)
        moreover have \<open>s setinterleaves ((map (EvExt f) t_P, map (EvExt f) t_Q),
                                         insert tick (ev ` f ` S))\<close>
          by (metis "*"(2) "**"(3) bij_EvExt_f sets_S_eq
                    bij_map_setinterleaving_iff_setinterleaving)
        moreover have \<open>X = ((EvExt f) ` X_P \<union> (EvExt f) ` X_Q) \<inter> insert tick (ev ` f ` S) \<union>
                           (EvExt f) ` X_P \<inter> (EvExt f) ` X_Q\<close>
          by (metis "**"(4) bij_EvExt_f bij_betw_def image_Int image_Un 
                    image_vimage_eq inf_top.right_neutral sets_S_eq)
        ultimately show \<open>(s, X) \<in> \<F> (?rhs P Q)\<close>
          by (simp add: F_Sync) blast
      qed
    qed
  next
    fix s X
    assume same_div : \<open>\<D> (?lhs P Q) = \<D> (?rhs P Q)\<close>
    assume \<open>(s, X) \<in> \<F> (?rhs P Q)\<close>
    then consider \<open>s \<in> \<D> (?rhs P Q)\<close>
      | \<open>\<exists>t_P t_Q X_P X_Q.
         (t_P, X_P) \<in> \<F> (Renaming P f) \<and> (t_Q, X_Q) \<in> \<F> (Renaming Q f) \<and>
         s setinterleaves ((t_P, t_Q), insert tick (ev ` f ` S)) \<and>
         X = (X_P \<union> X_Q) \<inter> insert tick (ev ` f ` S) \<union> X_P \<inter> X_Q\<close>
      by (simp add: F_Sync D_Sync) blast
    thus \<open>(s, X) \<in> \<F> (?lhs P Q)\<close>
    proof cases
      from same_div D_F show \<open>s \<in> \<D> (?rhs P Q) \<Longrightarrow> (s, X) \<in> \<F> (?lhs P Q)\<close> by blast
    next
      assume \<open>\<exists>t_P t_Q X_P X_Q.
              (t_P, X_P) \<in> \<F> (Renaming P f) \<and> (t_Q, X_Q) \<in> \<F> (Renaming Q f) \<and>
              s setinterleaves ((t_P, t_Q), insert tick (ev ` f ` S)) \<and>
              X = (X_P \<union> X_Q) \<inter> insert tick (ev ` f ` S) \<union> X_P \<inter> X_Q\<close>
      then obtain t_P t_Q X_P X_Q
        where * : \<open>(t_P, X_P) \<in> \<F> (Renaming P f)\<close> \<open>(t_Q, X_Q) \<in> \<F> (Renaming Q f)\<close>
                  \<open>s setinterleaves ((t_P, t_Q), insert tick (ev ` f ` S))\<close>
                  \<open>X = (X_P \<union> X_Q) \<inter> insert tick (ev ` f ` S) \<union> X_P \<inter> X_Q\<close> by blast
      from "*"(1, 2) consider \<open>t_P \<in> \<D> (Renaming P f) \<or> t_Q \<in> \<D> (Renaming Q f)\<close>
        | \<open>\<exists>t_P1 t_Q1. (t_P1, EvExt f -` X_P) \<in> \<F> P \<and> t_P = map (EvExt f) t_P1 \<and>
                       (t_Q1, EvExt f -` X_Q) \<in> \<F> Q \<and> t_Q = map (EvExt f) t_Q1\<close>
        by (simp add: F_Renaming D_Renaming) blast
      thus \<open>(s, X) \<in> \<F> (?lhs P Q)\<close>
      proof cases
        assume \<open>t_P \<in> \<D> (Renaming P f) \<or> t_Q \<in> \<D> (Renaming Q f)\<close>
        hence \<open>s \<in> \<D> (?rhs P Q)\<close>
          apply (simp add: D_Sync)
          using "*"(1, 2, 3) F_T Sync.sym front_tickFree_Nil by blast
        with same_div D_F show \<open>(s, X) \<in> \<F> (?lhs P Q)\<close> by blast
      next
        assume \<open>\<exists>t_P1 t_Q1. (t_P1, EvExt f -` X_P) \<in> \<F> P \<and> t_P = map (EvExt f) t_P1 \<and>
                            (t_Q1, EvExt f -` X_Q) \<in> \<F> Q \<and> t_Q = map (EvExt f) t_Q1\<close>
        then obtain t_P1 t_Q1
          where ** : \<open>(t_P1, EvExt f -` X_P) \<in> \<F> P\<close> \<open>t_P = map (EvExt f) t_P1\<close>
                     \<open>(t_Q1, EvExt f -` X_Q) \<in> \<F> Q\<close> \<open>t_Q = map (EvExt f) t_Q1\<close> by blast
        from "**"(2, 4) have *** : \<open>t_P1 = map (inv (EvExt f)) t_P\<close>
                                   \<open>t_Q1 = map (inv (EvExt f)) t_Q\<close>
          by (simp, metis bij_EvExt_f bij_betw_imp_inj_on inv_o_cancel list.map_id)+
        have **** : \<open>map (EvExt f) (map (inv (EvExt f)) s) = s\<close>
          by (metis bij_EvExt_f bij_betw_imp_surj list.map_comp list.map_id surj_iff)
        from bij_map_setinterleaving_iff_setinterleaving
                [of \<open>inv (EvExt f)\<close> s t_P \<open>insert tick (ev ` f ` S)\<close> t_Q, simplified "*"(3)]
        have \<open>map (inv (EvExt f)) s setinterleaves ((t_P1, t_Q1), insert tick (ev ` S))\<close>
          by (metis "***" bij_EvExt_f bij_betw_imp_inj_on
                    bij_betw_inv_into image_inv_f_f sets_S_eq)
        moreover have \<open>EvExt f -` X = (EvExt f -` X_P \<union> EvExt f -` X_Q) \<inter> insert tick (ev ` S) \<union> 
                      EvExt f -` X_P \<inter> EvExt f -` X_Q\<close>
          by (metis "*"(4) bij_EvExt_f bij_betw_imp_inj_on
                    inj_vimage_image_eq sets_S_eq vimage_Int vimage_Un)
        ultimately show \<open>(s, X) \<in> \<F> (?lhs P Q)\<close>
          by (simp add: F_Renaming F_Sync)
             (metis "**"(1, 3) "****")
      qed
    qed
  qed
qed


section \<open>\<^const>\<open>Hiding\<close> and \<^const>\<open>Mprefix\<close>\<close>

text \<open>We already have a way to distribute the \<^const>\<open>Hiding\<close> operator on the
      \<^const>\<open>Mprefix\<close> operator with @{thm Hiding_Mprefix_distr[of S A]}.
      But this is only usable when \<^term>\<open>A \<inter> S = {}\<close>. With the \<^const>\<open>Sliding\<close>
      operator, we can now handle the case \<^term>\<open>A \<inter> S \<noteq> {}\<close>.\<close>


subsection \<open>Two intermediate Results\<close>

lemma D_Hiding_Mprefix_dir2:
  assumes \<open>s \<in> \<D> (\<box>a \<in> A - S \<rightarrow> (P a \ S))\<close>
  shows \<open>s \<in> \<D> (\<box>a \<in> A \<rightarrow> P a \ S)\<close>
proof -
  from assms obtain a s'
    where * : \<open>a \<in> A\<close> \<open>a \<notin> S\<close> \<open>s = ev a # s'\<close> \<open>s' \<in> \<D> (P a \ S)\<close>
    by (auto simp add: D_Mprefix) (metis list.collapse)
  from "*"(4) obtain t u 
    where ** : \<open>front_tickFree u\<close> \<open>tickFree t\<close> \<open>s' = trace_hide t (ev ` S) @ u\<close>
               \<open>t \<in> \<D> (P a) \<or> (\<exists> f. isInfHiddenRun f (P a) S \<and> t \<in> range f)\<close>
    by (simp add: D_Hiding) blast
  from "**"(4) show \<open>s \<in> \<D> (\<box>a \<in> A \<rightarrow> P a \ S)\<close>
  proof (elim disjE)
    assume \<open>t \<in> \<D> (P a)\<close>
    hence \<open>tickFree (ev a # t) \<and> s = trace_hide (ev a # t) (ev ` S) @ u \<and>
           ev a # t \<in> \<D> (Mprefix A P)\<close>
      by (simp add: "*"(1, 2, 3) "**"(2, 3) image_iff[of \<open>ev a\<close>] D_Mprefix)
    show \<open>s \<in> \<D> (Mprefix A P \ S)\<close>
      apply (simp add: D_Hiding)
      using "**"(1) \<open>?this\<close> by blast
  next
    assume \<open>\<exists>f. isInfHiddenRun f (P a) S \<and> t \<in> range f\<close>
    then obtain f where *** : \<open>isInfHiddenRun f (P a) S\<close> \<open>t \<in> range f\<close> by blast
    hence \<open>tickFree (ev a # t) \<and> s = trace_hide (ev a # t) (ev ` S) @ u \<and>
           isInfHiddenRun (\<lambda>i. ev a # f i) (Mprefix A P) S \<and> 
           ev a # t \<in> range (\<lambda>i. ev a # f i)\<close>
      by (auto simp add: "*"(1, 2, 3) "**"(2, 3) image_iff[of \<open>ev a\<close>] 
                         T_Mprefix less_cons strict_mono_Suc_iff)
    show \<open>s \<in> \<D> (Mprefix A P \ S)\<close>
      apply (simp add: D_Hiding)
      using "**"(1) \<open>?this\<close> by blast
  qed
qed


lemma F_Hiding_Mprefix_dir2: 
  assumes \<open>s \<noteq> []\<close> and \<open>(s, X) \<in> \<F> (\<box>a \<in> A - S \<rightarrow> (P a \ S))\<close>
  shows \<open>(s, X) \<in> \<F> (\<box>a \<in> A \<rightarrow> P a \ S)\<close>
proof -
  from assms obtain a s'
    where * : \<open>a \<in> A\<close> \<open>a \<notin> S\<close> \<open>s = ev a # s'\<close> \<open>(s', X) \<in> \<F> (P a \ S)\<close>
    by (auto simp add: F_Mprefix) (metis list.collapse)
  from "*"(4) consider \<open>s' \<in> \<D> (P a \ S)\<close>
    | \<open>\<exists>t. s' = trace_hide t (ev ` S) \<and> (t, X \<union> ev ` S) \<in> \<F> (P a)\<close>
    by (simp add: F_Hiding D_Hiding) blast
  thus \<open>(s, X) \<in> \<F> (Mprefix A P \ S)\<close>
  proof cases
    assume \<open>s' \<in> \<D> (P a \ S)\<close>
    then obtain t u
      where ** : \<open>front_tickFree u\<close> \<open>tickFree t\<close> 
                 \<open>s' = trace_hide t (ev ` S) @ u\<close> 
                 \<open>t \<in> \<D> (P a) \<or> (\<exists> f. isInfHiddenRun f (P a) S \<and> t \<in> range f)\<close>
      by (simp add: D_Hiding) blast
    from "**"(4) show \<open>(s, X) \<in> \<F> (Mprefix A P \ S)\<close>
    proof (elim disjE)
      assume \<open>t \<in> \<D> (P a)\<close>
      hence \<open>tickFree (ev a # t) \<and> s = trace_hide (ev a # t) (ev ` S) @ u \<and>
             ev a # t \<in> \<D> (Mprefix A P)\<close>
        by (simp add: "*"(1, 2, 3) "**"(2, 3) D_Mprefix image_iff[of \<open>ev a\<close>])
      show \<open>(s, X) \<in> \<F> (Mprefix A P \ S)\<close>
        apply (simp add: F_Hiding)
        using "**"(1) \<open>?this\<close> by blast
    next
      assume \<open>\<exists>f. isInfHiddenRun f (P a) S \<and> t \<in> range f\<close>
      then obtain f where \<open>isInfHiddenRun f (P a) S\<close> \<open>t \<in> range f\<close> by blast
      hence \<open>tickFree (ev a # t) \<and> s = trace_hide (ev a # t) (ev ` S) @ u \<and>
             (isInfHiddenRun (\<lambda>i. ev a # f i) (Mprefix A P) S \<and> 
             ev a # t \<in> range (\<lambda>i. ev a # f i))\<close>
        by (auto simp add: "*"(1, 2, 3) "**"(2, 3) less_cons monotone_on_def T_Mprefix)
      show \<open>(s, X) \<in> \<F> (Mprefix A P \ S)\<close>
        apply (simp add: F_Hiding)
        using "**"(1) \<open>?this\<close> by blast
    qed
  next
    assume \<open>\<exists>t. s' = trace_hide t (ev ` S) \<and> (t, X \<union> ev ` S) \<in> \<F> (P a)\<close>
    then obtain t where ** : \<open>s' = trace_hide t (ev ` S)\<close>
                             \<open>(t, X \<union> ev ` S) \<in> \<F> (P a)\<close> by blast
    have \<open>s = trace_hide (ev a # t) (ev ` S) \<and> (ev a # t, X \<union> ev ` S) \<in> \<F> (Mprefix A P)\<close>
      by (simp add: "*"(1, 2, 3) "**" F_Mprefix image_iff)
    show \<open>(s, X) \<in> \<F> (Mprefix A P \ S)\<close>
      apply (simp add: F_Hiding)
      using \<open>?this\<close> by blast
  qed
qed



subsection \<open>\<^const>\<open>Hiding\<close> and \<^const>\<open>Mprefix\<close> for disjoint Sets\<close>

text \<open>Now we can give a more readable proof of the following result 
      (already proven in \<^theory>\<open>HOL-CSP.CSP_Laws\<close>).\<close>

theorem Hiding_Mprefix_disjoint: 
  \<open>\<box>a \<in> A \<rightarrow> P a \ S = \<box>a \<in> A \<rightarrow> (P a \ S)\<close> 
  (is \<open>?lhs = ?rhs\<close>) if disjoint: \<open>A \<inter> S = {}\<close>
proof (subst Process_eq_spec_optimized, safe)
  fix s
  assume \<open>s \<in> \<D> ?lhs\<close>
  then obtain t u 
    where * : \<open>front_tickFree u\<close> \<open>tickFree t\<close> \<open>s = trace_hide t (ev ` S) @ u\<close>
              \<open>t \<in> \<D> (Mprefix A P) \<or> 
               (\<exists> f. isInfHiddenRun f (Mprefix A P) S \<and> t \<in> range f)\<close>
  by (simp add: D_Hiding) blast
  from "*"(4) show \<open>s \<in> \<D> ?rhs\<close>
  proof (elim disjE)
    assume \<open>t \<in> \<D> (Mprefix A P)\<close>
    then obtain a t' where ** : \<open>a \<in> A\<close> \<open>a \<notin> S\<close> \<open>t = ev a # t'\<close> \<open>t' \<in> \<D> (P a)\<close>
      by (auto simp add: D_Mprefix) 
         (metis list.exhaust_sel disjoint_iff disjoint)
    have \<open>front_tickFree u \<and> tickFree t' \<and>
          trace_hide t' (ev ` S) @ u = trace_hide t' (ev ` S) @ u \<and> t' \<in> \<D> (P a)\<close>
      apply (simp add: "*"(1) "**"(4))
      using "*"(2) "**"(3) tickFree_Cons by blast
    show \<open>s \<in> \<D> ?rhs\<close>
      apply (simp add: D_Mprefix "*"(3) "**"(1, 2, 3) image_iff[of \<open>ev _\<close>] D_Hiding)
      using \<open>?this\<close> by blast
  next
    assume \<open>\<exists> f. isInfHiddenRun f (Mprefix A P) S \<and> t \<in> range f\<close>
    then obtain f where ** : \<open>isInfHiddenRun f (Mprefix A P) S\<close>
                             \<open>t \<in> range f\<close> by blast
    from "**"(1) T_Mprefix obtain a
      where *** : \<open>a \<in> A\<close> \<open>a \<notin> S\<close> \<open>f (Suc 0) \<noteq> []\<close> \<open>hd (f (Suc 0)) = ev a\<close>
      by (simp add: T_Mprefix) 
         (metis disjoint_iff disjoint nil_less strict_mono_Suc_iff)
    from "**"(1)[THEN conjunct2, THEN conjunct2, rule_format, of 1]
         "**"(1)[simplified isInfHiddenRun_1] "***"(1, 4) disjoint
    have **** : \<open>f j \<noteq> [] \<and> hd (f j) = ev a\<close> for j
      using "**"(1)[THEN conjunct2, THEN conjunct1, rule_format, of j]
      apply (cases \<open>f 1\<close>; simp add: T_Mprefix "***"(3) split: if_split_asm)
      by (metis Nil_is_append_conv filter.simps(1)
                hd_append2 list.distinct(1) list.sel(1)) blast
    then obtain t' where \<open>t = ev a # t'\<close>
      by (metis "**"(2) list.exhaust_sel rangeE)
    hence \<open>tickFree t' \<and> trace_hide t' (ev ` S) @ u = trace_hide t' (ev ` S) @ u \<and>
           isInfHiddenRun (\<lambda>i. tl (f i)) (P a) S \<and> t' \<in> range (\<lambda>i. tl (f i))\<close>
      apply (simp, intro conjI)
      subgoal using "*"(2) tickFree_Cons by blast
      subgoal by (meson "**"(1) "****" less_tail strict_mono_Suc_iff)
      subgoal using "**"(1) by (simp add: T_Mprefix "****") 
      subgoal by (metis (no_types, lifting) "**"(1) "****" filter.simps(2) list.exhaust_sel list.sel(3))
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
    | \<open>\<exists>t. s = trace_hide t (ev ` S) \<and> (t, X \<union> ev ` S) \<in> \<F> (Mprefix A P)\<close>
    by (simp add: F_Hiding D_Hiding) blast
  thus \<open>(s, X) \<in> \<F> ?rhs\<close>
  proof cases
    from same_div D_F show \<open>s \<in> \<D> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> by blast
  next
    assume \<open>\<exists>t. s = trace_hide t (ev ` S) \<and> (t, X \<union> ev ` S) \<in> \<F> (Mprefix A P)\<close>
    then obtain t where * : \<open>s = trace_hide t (ev ` S)\<close>
                            \<open>(t, X \<union> ev ` S) \<in> \<F> (Mprefix A P)\<close> by blast
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
            metis event.inject filter.simps(1) imageE)
    by (simp add: Diff_triv F_Hiding_Mprefix_dir2)
qed


text \<open>And we obtain a similar result when adding a \<^const>\<open>Sliding\<close> in the expression.\<close>

theorem Hiding_Mprefix_Sliding_disjoint:
  \<open>((\<box>a \<in> A \<rightarrow> P a) \<rhd> Q) \ S = (\<box>a \<in> A \<rightarrow> (P a \ S)) \<rhd> (Q \ S)\<close>
  if disjoint: \<open>A \<inter> S = {}\<close>
proof (subst Hiding_Mprefix_disjoint[OF disjoint, symmetric])
  show \<open>((\<box>a \<in> A \<rightarrow> P a) \<rhd> Q) \ S = (\<box>a \<in> A \<rightarrow> P a \ S) \<rhd> (Q \ S)\<close>
   (is \<open>?lhs = ?rhs\<close>)
  proof (subst Process_eq_spec_optimized, safe)
    fix s
    assume \<open>s \<in> \<D> ?lhs\<close>
    hence \<open>s \<in> \<D> (Mprefix A P \<sqinter> Q \ S)\<close>
      by (simp add: D_Hiding D_Sliding D_Ndet T_Sliding T_Ndet)
    thus \<open>s \<in> \<D> ?rhs\<close>
      by (rule set_rev_mp)
         (simp add: D_Ndet D_Sliding Hiding_Ndet subsetI)
  next
    fix s
    assume \<open>s \<in> \<D> ?rhs\<close>
    hence \<open>s \<in> \<D> (Q \ S) \<or> s \<in> \<D> (\<box>a \<in> A \<rightarrow> P a \ S)\<close>
      by (simp add: Hiding_Mprefix_disjoint[OF disjoint]
                    D_Ndet D_Sliding) blast
    thus \<open>s \<in> \<D> ?lhs\<close>
      by (auto simp add: D_Hiding D_Sliding T_Sliding)
  next
    fix s X
    assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
    assume \<open>(s, X) \<in> \<F> ?lhs\<close>
    then consider \<open>s \<in> \<D> ?lhs\<close>
      |\<open>\<exists>t. s = trace_hide t (ev ` S) \<and> (t, X \<union> ev ` S) \<in> \<F> (Mprefix A P \<rhd> Q)\<close>
      by (simp add: F_Hiding D_Hiding) blast
    thus \<open>(s, X) \<in> \<F> ?rhs\<close>
    proof cases
      from same_div D_F show \<open>s \<in> \<D> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> by blast
    next
      assume \<open>\<exists>t. s = trace_hide t (ev ` S) \<and>
                  (t, X \<union> ev ` S) \<in> \<F> (Mprefix A P \<rhd> Q)\<close>
      then obtain t
        where * : \<open>s = trace_hide t (ev ` S)\<close>
                  \<open>(t, X \<union> ev ` S) \<in> \<F> (Mprefix A P \<rhd> Q)\<close> by blast
      from "*"(2) consider \<open>(t, X \<union> ev ` S) \<in> \<F> Q\<close>
        | \<open>t \<noteq> []\<close> \<open>(t, X \<union> ev ` S) \<in> \<F> (Mprefix A P)\<close>
        by (simp add: F_Sliding D_Mprefix) blast
      thus \<open>(s, X) \<in> \<F> ?rhs\<close>
      proof cases
        have \<open>(t, X \<union> ev ` S) \<in> \<F> Q \<Longrightarrow> (s, X) \<in> \<F> (Q \ S)\<close>
          by (auto simp add: F_Hiding "*"(1))
        thus \<open>(t, X \<union> ev ` S) \<in> \<F> Q \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
          by (simp add: F_Ndet F_Sliding "*"(1))
      next
        assume assms : \<open>t \<noteq> []\<close> \<open>(t, X \<union> ev ` S) \<in> \<F> (Mprefix A P)\<close>
        with disjoint have \<open>trace_hide t (ev ` S) \<noteq> []\<close>
          by (cases t, auto simp add: F_Mprefix)
        also have \<open>(s, X) \<in> \<F> (Mprefix A P \ S)\<close>
          using assms by (auto simp: F_Hiding "*"(1))
        ultimately show \<open>(s, X) \<in> \<F> ?rhs\<close>
          by (simp add: F_Sliding "*"(1))
      qed
    qed
  next
    have * : \<open>t \<in> \<T> (Mprefix A P) \<Longrightarrow> trace_hide t (ev ` S) = [] \<longleftrightarrow> t = []\<close> for t
      using disjoint by (cases t, auto simp add: T_Mprefix)
    have ** : \<open>[] \<notin> \<D> (Mprefix A P \ S)\<close>
      apply (rule ccontr, simp add: D_Hiding)
      by (metis (mono_tags, lifting) "*" NT_ND Nil_Nin_D_Mprefix  
                UNIV_I f_inv_into_f lessI nless_le strict_mono_on_eqD)
    fix s X
    assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
    assume \<open>(s, X) \<in> \<F> ?rhs\<close>
    with ** consider \<open>(s, X) \<in> \<F> (Q \ S)\<close>
      | \<open>s \<noteq> []\<close> \<open>(s, X) \<in> \<F> (Mprefix A P \ S)\<close>
      by (simp add: Hiding_Mprefix_disjoint[OF disjoint] F_Sliding D_Mprefix) blast
    thus \<open>(s, X) \<in> \<F> ?lhs\<close>
    proof cases
      assume \<open>(s, X) \<in> \<F> (Q \ S)\<close>
      then consider \<open>s \<in> \<D> (Q \ S)\<close>
        | \<open>\<exists>t. s = trace_hide t (ev ` S) \<and> (t, X \<union> ev ` S) \<in> \<F> Q\<close>
        by (simp add: F_Hiding D_Hiding) blast
      thus \<open>(s, X) \<in> \<F> ?lhs\<close>
      proof cases
        assume \<open>s \<in> \<D> (Q \ S)\<close>
        hence \<open>s \<in> \<D> ?rhs\<close> by (simp add: D_Ndet D_Sliding)
        with same_div D_F show \<open>(s, X) \<in> \<F> ?lhs\<close> by blast
      next
        assume \<open>\<exists>t. s = trace_hide t (ev ` S) \<and> (t, X \<union> ev ` S) \<in> \<F> Q\<close>
        thus \<open>(s, X) \<in> \<F> ?lhs\<close>
          by (simp add: F_Hiding F_Sliding) blast
      qed
    next
      assume assms : \<open>s \<noteq> []\<close> \<open>(s, X) \<in> \<F> (Mprefix A P \ S)\<close>
      then consider \<open>s \<in> \<D> (Mprefix A P \ S)\<close>
        | \<open>\<exists>t. t \<noteq> [] \<and> s = trace_hide t (ev ` S) \<and> (t, X \<union> ev ` S) \<in> \<F> (Mprefix A P)\<close>
        by (simp add: F_Hiding D_Hiding) (metis filter.simps(1))
      thus \<open>(s, X) \<in> \<F> ?lhs\<close>
      proof cases
        assume \<open>s \<in> \<D> (Mprefix A P \ S)\<close>
        hence \<open>s \<in> \<D> ?rhs\<close> by (simp add: D_Ndet D_Sliding)
        with same_div D_F show \<open>(s, X) \<in> \<F> ?lhs\<close> by blast
      next
        show \<open>\<exists>t. t \<noteq> [] \<and> s = trace_hide t (ev ` S) \<and>
                  (t, X \<union> ev ` S) \<in> \<F> (Mprefix A P) \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
          by (auto simp add: F_Sliding F_Hiding)
      qed
    qed
  qed
qed




subsection \<open>\<^const>\<open>Hiding\<close> and \<^const>\<open>Mprefix\<close> for non-disjoint Sets\<close>

text \<open>Finally the new version, when \<^term>\<open>A \<inter> S \<noteq> {}\<close>.\<close>

theorem Hiding_Mprefix_non_disjoint:
\<comment> \<open>Rework this proof\<close>
  \<open>\<box>a \<in> A \<rightarrow> P a \ S = (\<box>a \<in> A - S \<rightarrow> (P a \ S)) \<rhd> (\<sqinter>a \<in> A \<inter> S. (P a \ S))\<close>
  (is \<open>?lhs = ?rhs\<close>) if non_disjoint: \<open>A \<inter> S \<noteq> {}\<close>
proof (subst Process_eq_spec_optimized, safe)
  fix s
  assume \<open>s \<in> \<D> ?lhs\<close>
  then obtain t u 
    where * : \<open>front_tickFree u\<close> \<open>tickFree t\<close> \<open>s = trace_hide t (ev ` S) @ u\<close>
              \<open>t \<in> \<D> (Mprefix A P) \<or> 
               (\<exists> f. isInfHiddenRun f (Mprefix A P) S \<and> t \<in> range f)\<close>
    by (simp add: D_Hiding) blast
  from "*"(4) show \<open>s \<in> \<D> ?rhs\<close>
  proof (elim disjE)
    assume \<open>t \<in> \<D> (Mprefix A P)\<close>
    then obtain a t' where ** : \<open>a \<in> A\<close> \<open>t = ev a # t'\<close> \<open>t' \<in> \<D> (P a)\<close>
      by (simp add: D_Mprefix) 
         (metis event.inject image_iff list.exhaust_sel)
    have \<open>tickFree t' \<and>
          (if a \<in> S then s else tl s) = trace_hide t' (ev ` S) @ u \<and>
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
        by (simp add: T_Mprefix) blast
      have **** : \<open>0 < j \<Longrightarrow> f j \<noteq> [] \<and> hd (f j) = ev a\<close> for j
      proof (induct j rule: nat_induct_non_zero)
        from "***"(2, 3) show \<open>f 1 \<noteq> [] \<and> hd (f 1) = ev a\<close> by blast
      next
        case (Suc j)
        have \<open>j < Suc j\<close> by simp
        from "**"(1)[THEN conjunct1, THEN strict_monoD, OF this]
        obtain v where \<open>f (Suc j) = f j @ v\<close>
          by (metis le_list_def order_less_imp_le)
        thus ?case by (simp add: Suc.hyps(2))
      qed
      from "***"(1) have *****: \<open>a \<in> A \<inter> S\<close>
        by simp (metis (no_types, lifting) "**"(1) "***"(2, 3)
                       \<open>f 0 = []\<close> empty_filter_conv event.inject
                       filter.simps(1) image_iff list.set_sel(1))
      have \<open>(if i = 0 \<and> t = [] then [] else tl (f (Suc i))) \<in> \<T> (P a)\<close> for i
      proof -
        from "**"(1) "****"[of \<open>Suc i\<close>] have \<open>tl (f (Suc i)) \<in> \<T> (P a)\<close>
          by (simp add: T_Mprefix) (metis event.inject)
        thus \<open>(if i = 0 \<and> t = [] then [] else tl (f (Suc i))) \<in> \<T> (P a)\<close>
          by (simp add: Nil_elem_T)
      qed
      hence ****** :
        \<open>front_tickFree u \<and> tickFree (tl t) \<and>
         s = trace_hide (tl t) (ev ` S) @ u \<and>
         isInfHiddenRun (\<lambda>i. if i = 0 \<and> t = [] then [] else tl (f (Suc i))) (P a) S \<and> 
         tl t \<in> range (\<lambda>i. if i = 0 \<and> t = [] then [] else tl (f (Suc i)))\<close>
        apply (intro conjI)
        subgoal by (solves \<open>simp add: "*"(1)\<close>)
        subgoal by (metis "*"(2) list.sel(2) tickFree_tl)
        subgoal by (metis "*"(3) "**"(1) \<open>f 0 = []\<close> \<open>t = f k\<close> empty_filter_conv
              filter.simps(1) list.sel(2) list.set_sel(2))
        subgoal by (simp add: monotone_on_def,
              metis "**"(1) Suc_less_eq less_list_def less_tail monotoneD
              nil_le nil_less zero_less_Suc)
        subgoal by blast
        subgoal by (simp, metis "**"(1) "****" \<open>f 0 = []\<close> empty_filter_conv
              filter.simps(1) list.set_sel(2) zero_less_Suc)
        by (simp add: image_iff,
            metis Suc_pred \<open>f 0 = []\<close> \<open>t = f k\<close> bot_nat_0.not_eq_extremum)
      have \<open>a \<in> A \<inter> S \<and> s \<in> \<D> (P a \ S)\<close>
        apply (simp add: D_Hiding "*****"[simplified])
        using ****** by blast
      hence \<open>s \<in> \<D> (\<sqinter>a \<in> A \<inter> S. (P a \ S))\<close> by (simp add: D_GlobalNdet) blast
      thus \<open>s \<in> \<D> ?rhs\<close> by (simp add: D_Sliding)
    next
      assume \<open>f 0 \<noteq> []\<close>
      with "**"(1)[THEN conjunct2, THEN conjunct1, rule_format, of 0]
      obtain a where *** : \<open>a \<in> A\<close> \<open>f 0 \<noteq> []\<close> \<open>hd (f 0) = ev a\<close>
        by (simp add: T_Mprefix) blast
      have **** : \<open>f j \<noteq> [] \<and> hd (f j) = ev a\<close> for j
      proof (induct j)
        from "***"(2, 3) show \<open>f 0 \<noteq> [] \<and> hd (f 0) = ev a\<close> by blast
      next
        case (Suc j)
        have \<open>j < Suc j\<close> by simp
        from "**"(1)[THEN conjunct1, THEN strict_monoD, OF this]
        obtain v where \<open>f (Suc j) = f j @ v\<close>
          by (metis le_list_def order_less_imp_le)
        thus ?case by (simp add: Suc.hyps(1))
      qed
      show \<open>s \<in> \<D> ?rhs\<close>
      proof (cases \<open>a \<in> S\<close>)
        assume \<open>a \<in> S\<close>
        hence \<open>a \<in> A \<inter> S\<close> by (simp add: "***"(1))
        have \<open>tickFree (tl t) \<and> s = trace_hide (tl t) (ev ` S) @ u \<and>
              isInfHiddenRun (\<lambda>i. tl (f i)) (P a) S \<and> tl t \<in> range (\<lambda>i. tl (f i))\<close>
          apply (simp add: "*"(3), intro conjI)
          subgoal by (metis "*"(2) list.sel(2) tickFree_tl)
          subgoal by (cases t; simp; metis "****" \<open>a \<in> S\<close> \<open>t = f k\<close> image_iff list.sel(1))
          subgoal by (meson "**"(1) "****" less_tail strict_mono_Suc_iff)
          subgoal using "**"(1) by (simp add: T_Mprefix "****")
          subgoal by (metis (no_types, lifting) "**"(1) "****" filter.simps(2) list.exhaust_sel list.sel(3))
          using "**"(2) by blast
        have \<open>s \<in> \<D> (\<sqinter>a \<in> A \<inter> S. (P a \ S))\<close>
          apply (simp add: D_GlobalNdet D_Hiding)
          using "*"(1) \<open>a \<in> A \<inter> S\<close> \<open>?this\<close> by blast
        thus \<open>s \<in> \<D> ?rhs\<close> by (simp add: D_Sliding)
      next
        assume \<open>a \<notin> S\<close>
        have \<open>tickFree (tl t) \<and> 
              trace_hide (tl t) (ev ` S) @ u = trace_hide (tl t) (ev ` S) @ u \<and>
              isInfHiddenRun (\<lambda>i. tl (f i)) (P a) S \<and> tl t \<in> range (\<lambda>i. tl (f i))\<close>
          apply (simp add: "*"(3), intro conjI)
          subgoal by (metis "*"(2) list.sel(2) tickFree_tl)
          subgoal by (meson "**"(1) "****" less_tail strict_mono_Suc_iff)
          subgoal using "**"(1) by (simp add: T_Mprefix "****")
          subgoal by (metis (no_types, lifting) "**"(1) "****" filter.simps(2) list.exhaust_sel list.sel(3))
          using "**"(2) by blast
        from \<open>a \<notin> S\<close> have \<open>s \<in> \<D> (\<box>a\<in>A - S \<rightarrow> (P a \ S))\<close>
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
  then consider \<open>s \<in> \<D> (\<box>a \<in> A - S \<rightarrow> (P a \ S))\<close> 
    | \<open>s \<in> \<D> (\<sqinter>a \<in> A \<inter> S. (P a \ S))\<close> by (simp add: D_Sliding) blast
  thus \<open>s \<in> \<D> ?lhs\<close>
  proof cases
    show \<open>s \<in> \<D> (\<box>a \<in> A - S \<rightarrow> (P a \ S)) \<Longrightarrow> s \<in> \<D> ?lhs\<close>
      by (rule D_Hiding_Mprefix_dir2)
  next
    assume \<open>s \<in> \<D> (\<sqinter>a \<in> A \<inter> S. (P a \ S))\<close>
    then obtain a where * : \<open>a \<in> A\<close> \<open>a \<in> S\<close> \<open>s \<in> \<D> (P a \ S)\<close>
      by (simp add: D_GlobalNdet)
         (metis (no_types, lifting) IntD1 IntD2 UN_iff empty_iff)
    from "*"(3) obtain t u 
       where ** : \<open>front_tickFree u\<close> \<open>tickFree t\<close> \<open>s = trace_hide t (ev ` S) @ u\<close>
                 \<open>t \<in> \<D> (P a) \<or> (\<exists> f. isInfHiddenRun f (P a) S \<and> t \<in> range f)\<close>
      by (simp add: D_Hiding) blast
    from "**"(4) show \<open>s \<in> \<D> ?lhs\<close>
    proof (elim disjE)
      assume \<open>t \<in> \<D> (P a)\<close>
      hence $ : \<open>tickFree (ev a # t) \<and> ev a # t \<in> \<D> (Mprefix A P) \<and>
                 s = trace_hide (ev a # t) (ev ` S) @ u\<close>
        by (simp add: "*"(1, 2) "**"(2, 3) D_Mprefix)
      show \<open>s \<in> \<D> ?lhs\<close>
        apply (simp add: D_Hiding)
        using "$" "**"(1) by blast
    next
      assume \<open>\<exists>f. isInfHiddenRun f (P a) S \<and> t \<in> range f\<close>
      then obtain f where \<open>isInfHiddenRun f (P a) S\<close> \<open>t \<in> range f\<close> by blast
      hence $ : \<open>tickFree (ev a # t) \<and> 
                 s = trace_hide (ev a # t) (ev ` S) @ u \<and>
                 isInfHiddenRun (\<lambda>i. ev a # f i) (Mprefix A P) S \<and> 
                 ev a # t \<in> range (\<lambda>i. ev a # f i)\<close>
        by (auto simp add: "*"(1, 2) "**"(2, 3) less_cons monotone_on_def T_Mprefix)
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
    | \<open>\<exists>t. s = trace_hide t (ev ` S) \<and> (t, X \<union> ev ` S) \<in> \<F> (Mprefix A P)\<close>
    by (simp add: F_Hiding D_Hiding) blast
  thus \<open>(s, X) \<in> \<F> ?rhs\<close>
  proof cases
    from D_F same_div show \<open>s \<in> \<D> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> by blast
  next
    assume \<open>\<exists>t. s = trace_hide t (ev ` S) \<and> (t, X \<union> ev ` S) \<in> \<F> (Mprefix A P)\<close>
    then obtain t where * : \<open>s = trace_hide t (ev ` S)\<close>
                            \<open>(t, X \<union> ev ` S) \<in> \<F> (Mprefix A P)\<close> by blast
    from "*"(2) consider \<open>t = []\<close> \<open>(X \<union> ev ` S) \<inter> ev ` A = {}\<close>
      | \<open>\<exists>a t'. a \<in> A \<and> t = ev a # t' \<and> (t', X \<union> ev ` S) \<in> \<F> (P a)\<close>
      by (simp add: F_Mprefix) (metis event.inject image_iff list.collapse)
    thus \<open>(s, X) \<in> \<F> ?rhs\<close>
    proof cases
      show \<open>t = [] \<Longrightarrow> (X \<union> ev ` S) \<inter> ev ` A = {} \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
        using "*"(1) by (auto simp add: F_Sliding F_GlobalNdet)
    next
      assume \<open>\<exists>a t'. a \<in> A \<and> t = ev a # t' \<and> (t', X \<union> ev ` S) \<in> \<F> (P a)\<close>
      then obtain a t' where ** : \<open>a \<in> A\<close> \<open>t = ev a # t'\<close>
                                  \<open>(t', X \<union> ev ` S) \<in> \<F> (P a)\<close> by blast
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
  then consider \<open>(s, X) \<in> \<F> (\<sqinter>a \<in> A \<inter> S. (P a \ S))\<close>
    | \<open>s \<noteq> []\<close> \<open>(s, X) \<in> \<F> (\<box>a \<in> A - S \<rightarrow> (P a \ S))\<close>
    by (auto simp add: F_Sliding)
  thus \<open>(s, X) \<in> \<F> ?lhs\<close>
  proof cases
    assume \<open>(s, X) \<in> \<F> (\<sqinter>a \<in> A \<inter> S. (P a \ S))\<close>
    then obtain a where * : \<open>a \<in> A\<close> \<open>a \<in> S\<close> \<open>(s, X) \<in> \<F> (P a \ S)\<close>
      by (simp add: F_GlobalNdet non_disjoint) blast
    from "*"(3) consider \<open>s \<in> \<D> (P a \ S)\<close>
      | \<open>\<exists>t. s = trace_hide t (ev ` S) \<and> (t, X \<union> ev ` S) \<in> \<F> (P a)\<close>
      by (simp add: F_Hiding D_Hiding) blast
    thus \<open>(s, X) \<in> \<F> ?lhs\<close>
    proof cases
      assume \<open>s \<in> \<D> (P a \ S)\<close>
      then obtain t u
        where ** : \<open>front_tickFree u\<close> \<open>tickFree t\<close> 
                   \<open>s = trace_hide t (ev ` S) @ u\<close> 
                   \<open>t \<in> \<D> (P a) \<or> (\<exists> f. isInfHiddenRun f (P a) S \<and> t \<in> range f)\<close>
        by (simp add: D_Hiding) blast
      from "**"(4) show \<open>(s, X) \<in> \<F> ?lhs\<close>
      proof (elim disjE)
        assume \<open>t \<in> \<D> (P a)\<close>
        hence $ : \<open>tickFree (ev a # t) \<and> s = trace_hide (ev a # t) (ev ` S) @ u \<and> 
                   ev a # t \<in> \<D> (Mprefix A P)\<close>
          by (simp add: D_Mprefix "*"(1, 2) "**"(2, 3) image_iff[of \<open>ev a\<close>])
        show \<open>(s, X) \<in> \<F> ?lhs\<close>
          apply (simp add: F_Hiding)
          using "$" "**"(1) by blast
      next
        assume \<open>\<exists>f. isInfHiddenRun f (P a) S \<and> t \<in> range f\<close>
        then obtain f where \<open>isInfHiddenRun f (P a) S\<close> \<open>t \<in> range f\<close> by blast
        hence $ : \<open>tickFree (ev a # t) \<and> s = trace_hide (ev a # t) (ev ` S) @ u \<and>
                   isInfHiddenRun (\<lambda>i. ev a # f i) (Mprefix A P) S \<and> 
                   ev a # t \<in> range (\<lambda>i. ev a # f i)\<close>
          by (simp add: T_Mprefix "*"(1, 2) "**"(2, 3) 
                        image_iff[of \<open>ev a\<close>] less_cons monotone_on_def) blast
        show \<open>(s, X) \<in> \<F> ?lhs\<close>
          apply (simp add: F_Hiding)
          using "$" "**"(1) by blast
      qed
    next
      assume \<open>\<exists>t. s = trace_hide t (ev ` S) \<and> (t, X \<union> ev ` S) \<in> \<F> (P a)\<close>
      then obtain t where \<open>s = trace_hide t (ev ` S)\<close>
                          \<open>(t, X \<union> ev ` S) \<in> \<F> (P a)\<close> by blast
      hence \<open>s = trace_hide (ev a # t) (ev ` S) \<and> 
             (ev a # t, X \<union> ev ` S) \<in> \<F> (Mprefix A P)\<close>
        by (simp add: "*"(1, 2) F_Mprefix)
      show \<open>(s, X) \<in> \<F> ?lhs\<close>
        apply (simp add: F_Hiding, rule disjI1)
        using \<open>?this\<close> by blast
    qed
  next
    show \<open>s \<noteq> [] \<Longrightarrow> (s, X) \<in> \<F> (\<box>a\<in>A - S \<rightarrow> (P a \ S)) \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
      by (rule F_Hiding_Mprefix_dir2)
  qed
qed

\<comment> \<open>Just a small lemma to understand why the nonempty hypothesis is necessary.\<close>
lemma \<open>\<exists>A P S. A \<inter> S = {} \<and> 
               \<box>a \<in> A::nat set \<rightarrow> P a \ S \<noteq> 
               (\<box>a \<in> A - S \<rightarrow> (P a \ S)) \<rhd> (\<sqinter>a \<in> A \<inter> S. (P a \ S))\<close>
proof (intro exI)
  show \<open>{0} \<inter> {Suc 0} = {} \<and> 
        \<box>a \<in> {0}::nat set \<rightarrow> SKIP \ {Suc 0} \<noteq> 
        (\<box>a \<in> {0} - {Suc 0} \<rightarrow> (SKIP \ {Suc 0})) \<rhd> (\<sqinter>a \<in> {0} \<inter> {Suc 0}. (SKIP \ {Suc 0}))\<close>
    apply (simp add: write0_def[symmetric] no_Hiding_write0 Hiding_set_SKIP)
    by (simp add: Process_eq_spec write0_def
                  F_Mprefix F_Sliding F_STOP set_eq_iff) blast
qed


text \<open>And we obtain a similar result when adding a \<^const>\<open>Sliding\<close> in the expression.\<close>

lemma Hiding_Mprefix_Sliding_non_disjoint:
  \<open>((\<box>a \<in> A \<rightarrow> P a) \<rhd> Q) \ S = (\<box>a \<in> A - S \<rightarrow> (P a \ S)) \<rhd> 
                                (Q \ S) \<sqinter> (\<sqinter>a \<in> A \<inter> S. (P a \ S))\<close>
  if non_disjoint: \<open>A \<inter> S \<noteq> {}\<close>
proof (subst Sliding_Ndet(2),
       subst Hiding_Mprefix_non_disjoint[OF non_disjoint, symmetric])
  show \<open>Mprefix A P \<rhd> Q \ S =
        ((\<box>a \<in> A - S \<rightarrow> (P a \ S)) \<rhd> (Q \ S)) \<sqinter> (\<box>a \<in> A \<rightarrow> P a \ S)\<close>
   (is \<open>?lhs = ?rhs\<close>)
  proof (subst Process_eq_spec_optimized, safe)
    fix s
    assume \<open>s \<in> \<D> ?lhs\<close>
    hence \<open>s \<in> \<D> (Mprefix A P \<sqinter> Q \ S)\<close>
      by (simp add: D_Hiding D_Sliding D_Ndet T_Sliding T_Ndet)
    thus \<open>s \<in> \<D> ?rhs\<close>
      by (rule set_rev_mp)
         (simp add: D_Ndet D_Sliding Hiding_Ndet subsetI)
  next
    fix s
    assume \<open>s \<in> \<D> ?rhs\<close>
    hence \<open>s \<in> \<D> (Q \ S) \<or> s \<in> \<D> (\<box>a \<in> A \<rightarrow> P a \ S)\<close>
      by (simp add: Hiding_Mprefix_non_disjoint[OF non_disjoint]
                    D_Ndet D_Sliding) blast
    thus \<open>s \<in> \<D> ?lhs\<close>
      by (auto simp add: D_Hiding D_Sliding T_Sliding)
  next
    fix s X
    assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
    assume \<open>(s, X) \<in> \<F> ?lhs\<close>
    then consider \<open>s \<in> \<D> ?lhs\<close>
      |\<open>\<exists>t. s = trace_hide t (ev ` S) \<and> (t, X \<union> ev ` S) \<in> \<F> (Mprefix A P \<rhd> Q)\<close>
      by (simp add: F_Hiding D_Hiding) blast
    thus \<open>(s, X) \<in> \<F> ?rhs\<close>
    proof cases
      from same_div D_F show \<open>s \<in> \<D> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> by blast
    next
      assume \<open>\<exists>t. s = trace_hide t (ev ` S) \<and>
                  (t, X \<union> ev ` S) \<in> \<F> (Mprefix A P \<rhd> Q)\<close>
      then obtain t
        where * : \<open>s = trace_hide t (ev ` S)\<close>
                  \<open>(t, X \<union> ev ` S) \<in> \<F> (Mprefix A P \<rhd> Q)\<close> by blast
      from "*"(2) consider \<open>(t, X \<union> ev ` S) \<in> \<F> Q\<close>
        | \<open>(t, X \<union> ev ` S) \<in> \<F> (Mprefix A P)\<close>
        by (simp add: F_Sliding D_Mprefix) blast
      thus \<open>(s, X) \<in> \<F> ?rhs\<close>
      proof cases
        have \<open>(t, X \<union> ev ` S) \<in> \<F> Q \<Longrightarrow> (s, X) \<in> \<F> (Q \ S)\<close>
          by (auto simp add: F_Hiding "*"(1))
        thus \<open>(t, X \<union> ev ` S) \<in> \<F> Q \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
          by (simp add: F_Ndet F_Sliding "*"(1))
      next
        assume \<open>(t, X \<union> ev ` S) \<in> \<F> (Mprefix A P)\<close>
        hence \<open>(s, X) \<in> \<F> (Mprefix A P \ S)\<close> by (auto simp: F_Hiding "*"(1))
        thus \<open>(s, X) \<in> \<F> ?rhs\<close> by (simp add: F_Ndet "*"(1))
      qed
    qed
  next
    fix s X
    have * : \<open>s \<noteq> [] \<Longrightarrow> (s, X) \<in> \<F> (\<box>a \<in> A - S \<rightarrow> (P a \ S)) \<Longrightarrow> 
                          (s, X) \<in> \<F> (\<box>a \<in> A \<rightarrow> P a \ S)\<close>
      by (simp add: Hiding_Mprefix_non_disjoint[OF non_disjoint] F_Sliding)
    assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
    assume \<open>(s, X) \<in> \<F> ?rhs\<close>
    with "*" consider \<open>(s, X) \<in> \<F> (Q \ S)\<close> | \<open>(s, X) \<in> \<F> (Mprefix A P \ S)\<close>
      by (auto simp add: F_Ndet F_Sliding)
    thus \<open>(s, X) \<in> \<F> ?lhs\<close>
    proof cases
      assume \<open>(s, X) \<in> \<F> (Q \ S)\<close>
      then consider \<open>s \<in> \<D> (Q \ S)\<close>
        | \<open>\<exists>t. s = trace_hide t (ev ` S) \<and> (t, X \<union> ev ` S) \<in> \<F> Q\<close>
        by (simp add: F_Hiding D_Hiding) blast
      thus \<open>(s, X) \<in> \<F> ?lhs\<close>
      proof cases
        assume \<open>s \<in> \<D> (Q \ S)\<close>
        hence \<open>s \<in> \<D> ?rhs\<close> by (simp add: D_Ndet D_Sliding)
        with same_div D_F show \<open>(s, X) \<in> \<F> ?lhs\<close> by blast
      next
        assume \<open>\<exists>t. s = trace_hide t (ev ` S) \<and> (t, X \<union> ev ` S) \<in> \<F> Q\<close>
        thus \<open>(s, X) \<in> \<F> ?lhs\<close>
          by (simp add: F_Hiding F_Sliding) blast
      qed
    next
      assume \<open>(s, X) \<in> \<F> (Mprefix A P \ S)\<close>
      then consider \<open>s \<in> \<D> (Mprefix A P \ S)\<close>
        | \<open>\<exists>t. s = trace_hide t (ev ` S) \<and> (t, X \<union> ev ` S) \<in> \<F> (Mprefix A P)\<close>
        by (simp add: F_Hiding D_Hiding) blast
      thus \<open>(s, X) \<in> \<F> ?lhs\<close>
      proof cases
        assume \<open>s \<in> \<D> (Mprefix A P \ S)\<close>
        hence \<open>s \<in> \<D> ?rhs\<close> by (simp add: D_Ndet D_Sliding)
        with same_div D_F show \<open>(s, X) \<in> \<F> ?lhs\<close> by blast
      next
        assume \<open>\<exists>t. s = trace_hide t (ev ` S) \<and> (t, X \<union> ev ` S) \<in> \<F> (Mprefix A P)\<close>
        then obtain t where * : \<open>s = trace_hide t (ev ` S)\<close>
                                \<open>(t, X \<union> ev ` S) \<in> \<F> (Mprefix A P)\<close> by blast
        from "*"(2) non_disjoint have \<open>t \<noteq> []\<close> by (simp add: F_Mprefix) blast
        with "*" show \<open>(s, X) \<in> \<F> ?lhs\<close>
          by (simp add: F_Hiding F_Sliding) blast
      qed
    qed
  qed
qed
       


section \<open>\<^const>\<open>Sliding\<close> behaviour\<close>

text \<open>We already proved several laws for the \<^const>\<open>Sliding\<close> operator.
      Here we give other results in the same spirit as
      @{thm [source] Hiding_Mprefix_Sliding_disjoint} and
      @{thm [source] Hiding_Mprefix_Sliding_non_disjoint}.\<close>

lemma Mprefix_Sliding_Mprefix_Sliding:
  \<open>(\<box>a \<in> A \<rightarrow> P a) \<rhd> (\<box>b \<in> B \<rightarrow> Q b) \<rhd> R =
   (\<box> x \<in> A \<union> B \<rightarrow> (if x \<in> A \<inter> B then P x \<sqinter> Q x else if x \<in> A then P x else Q x)) \<rhd> R\<close>
  (is \<open>(\<box>a \<in> A \<rightarrow> P a) \<rhd> (\<box>b \<in> B \<rightarrow> Q b) \<rhd> R = ?term \<rhd> R\<close>)
proof (subst Sliding_def, subst Mprefix_Det_distr)
  have \<open>Mprefix B Q \<sqinter> (Mprefix A P \<box> Mprefix B Q) \<rhd> R = Mprefix A P \<box> Mprefix B Q \<rhd> R\<close>
    by (metis Det_STOP Ndet_commute Ndet_distrib Sliding_STOP_Det Sliding_assoc Sliding_def) 
  thus \<open>?term \<sqinter> Mprefix B Q \<rhd> R = ?term \<rhd> R\<close>
    by (simp add: Mprefix_Det_distr Ndet_commute)
qed


lemma Mprefix_Sliding_Seq: 
  \<open>((\<box>a \<in> A \<rightarrow> P a) \<rhd> P') \<^bold>; Q = (\<box>a \<in> A \<rightarrow> P a \<^bold>; Q) \<rhd> (P' \<^bold>; Q)\<close>
proof (subst Mprefix_Seq[symmetric])
  show \<open>((\<box>a \<in> A \<rightarrow> P a) \<rhd> P') \<^bold>; Q = 
        ((\<box>a \<in> A \<rightarrow> P a) \<^bold>; Q) \<rhd> (P' \<^bold>; Q)\<close> (is \<open>?lhs = ?rhs\<close>)
  proof (subst Process_eq_spec, safe)
    show \<open>s \<in> \<D> ?lhs \<Longrightarrow> s \<in> \<D> ?rhs\<close> for s
      by (auto simp add: D_Sliding D_Seq T_Sliding)
  next
    show \<open>s \<in> \<D> ?rhs \<Longrightarrow> s \<in> \<D> ?lhs\<close> for s
      by (auto simp add: D_Sliding D_Seq T_Sliding)
  next
    show \<open>(s, X) \<in> \<F> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> for s X
      apply (simp add: F_Seq, elim disjE exE)
        apply (solves \<open>auto simp add: F_Sliding F_Seq D_Mprefix\<close>)
       apply (solves \<open>auto simp add: F_Sliding T_Sliding F_Seq\<close>)
      by (solves \<open>auto simp add: D_Sliding D_Seq F_Sliding F_Seq\<close>)
  next
    show \<open>(s, X) \<in> \<F> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> for s X
      apply (simp add: F_Sliding, elim disjE)
        apply (solves \<open>auto simp add: F_Seq D_Sliding F_Sliding T_Sliding\<close>)
       apply (solves \<open>auto simp add: F_Seq D_Sliding F_Sliding T_Sliding\<close>)
      by (simp add: D_Seq D_Mprefix T_Seq T_Mprefix)
         (metis append_is_Nil_conv event.simps(3) hd_append list.sel(1))
  qed
qed



lemma Throw_Sliding :
  \<open>(\<box>a \<in> A \<rightarrow> P a) \<rhd> P' \<Theta> b \<in> B. Q b = 
   (\<box>a \<in> A \<rightarrow> (if a \<in> B then Q a else (P a \<Theta> b \<in> B. Q b))) \<rhd> (P' \<Theta> b \<in> B. Q b)\<close>
  (is \<open>?lhs = ?rhs\<close>)
proof (subst Process_eq_spec_optimized, safe)
  fix s
  assume \<open>s \<in> \<D> ?lhs\<close>
  then consider \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<D> (Mprefix A P \<rhd> P') \<and>
                         tickFree t1 \<and> set t1 \<inter> ev ` B = {} \<and> front_tickFree t2\<close>
    | \<open>\<exists>t1 b t2. s = t1 @ ev b # t2 \<and> t1 @ [ev b] \<in> \<T> (Mprefix A P \<rhd> P') \<and>
                 set t1 \<inter> ev ` B = {} \<and> b \<in> B \<and> t2 \<in> \<D> (Q b)\<close>
    by (simp add: D_Throw) blast
  thus \<open>s \<in> \<D> ?rhs\<close>
  proof cases
    assume \<open>\<exists>t1 t2. s = t1 @ t2 \<and> t1 \<in> \<D> (Mprefix A P \<rhd> P') \<and>
                    tickFree t1 \<and> set t1 \<inter> ev ` B = {} \<and> front_tickFree t2\<close>
    then obtain t1 t2
      where * : \<open>s = t1 @ t2\<close> \<open>t1 \<in> \<D> (Mprefix A P \<rhd> P')\<close> \<open>tickFree t1\<close>
                \<open>set t1 \<inter> ev ` B = {}\<close> \<open>front_tickFree t2\<close> by blast
    from "*"(2) consider \<open>t1 \<in> \<D> (Mprefix A P)\<close> | \<open>t1 \<in> \<D> P'\<close>
      by (simp add: D_Sliding) blast
    thus \<open>s \<in> \<D> ?rhs\<close>
    proof cases
      assume \<open>t1 \<in> \<D> (Mprefix A P)\<close>
      then obtain a t1' where \<open>t1 = ev a # t1'\<close> \<open>a \<in> A\<close> \<open>t1' \<in> \<D> (P a)\<close>
        by (simp add: D_Mprefix image_iff)
           (metis event.inject list.collapse)
      with "*"(1, 3, 4, 5) show \<open>s \<in> \<D> ?rhs\<close>
        by (simp add: D_Sliding D_Mprefix D_Throw) (metis image_eqI)
    next
      from "*"(1, 3, 4, 5)  show \<open>t1 \<in> \<D> P' \<Longrightarrow> s \<in> \<D> ?rhs\<close>
        by (simp add: D_Sliding D_Throw) blast
    qed
  next
    assume \<open>\<exists>t1 b t2. s = t1 @ ev b # t2 \<and> t1 @ [ev b] \<in> \<T> (Mprefix A P \<rhd> P') \<and>
                      set t1 \<inter> ev ` B = {} \<and> b \<in> B \<and> t2 \<in> \<D> (Q b)\<close>
    then obtain t1 b t2
      where * : \<open>s = t1 @ ev b # t2\<close> \<open>t1 @ [ev b] \<in> \<T> (Mprefix A P \<rhd> P')\<close>
                \<open>set t1 \<inter> ev ` B = {}\<close> \<open>b \<in> B\<close> \<open>t2 \<in> \<D> (Q b)\<close> by blast
    from "*"(2) consider \<open>t1 @ [ev b] \<in> \<T> (Mprefix A P)\<close> | \<open>t1 @ [ev b] \<in> \<T> P'\<close>
      by (simp add: T_Sliding) blast
    thus \<open>s \<in> \<D> ?rhs\<close>
    proof cases
      assume \<open>t1 @ [ev b] \<in> \<T> (Mprefix A P)\<close>
      then obtain a t1'
        where \<open>t1 @ [ev b] = ev a # t1'\<close> \<open>a \<in> A\<close> \<open>t1' \<in> \<T> (P a)\<close>
        by (simp add: T_Mprefix)
           (metis list.exhaust_sel snoc_eq_iff_butlast)
      with "*"(1, 3, 4, 5) show \<open>s \<in> \<D> ?rhs\<close>
        by (cases t1; simp add: "*"(1) D_Sliding D_Mprefix D_Throw)
           (metis image_eqI)
    next
      from "*"(1, 3, 4, 5) show \<open>t1 @ [ev b] \<in> \<T> P' \<Longrightarrow> s \<in> \<D> ?rhs\<close>
        by (simp add: D_Sliding D_Mprefix D_Throw) blast
    qed
  qed
next
  fix s
  assume \<open>s \<in> \<D> ?rhs\<close>
  then consider \<open>s \<in> \<D> (Throw P' B Q)\<close>
    | \<open>s \<in> \<D> (\<box>a\<in>A \<rightarrow> (if a \<in> B then Q a else Throw (P a) B Q))\<close>
    by (simp add: D_Sliding) blast
  thus \<open>s \<in> \<D> ?lhs\<close>
  proof cases
    show \<open>s \<in> \<D> (Throw P' B Q) \<Longrightarrow> s \<in> \<D> ?lhs\<close>
      by (simp add: D_Throw D_Sliding T_Sliding) blast
  next
    assume \<open>s \<in> \<D> (\<box>a\<in>A \<rightarrow> (if a \<in> B then Q a else Throw (P a) B Q))\<close>
    then obtain a s' 
      where * : \<open>s = ev a # s'\<close> \<open>a \<in> A\<close>
                \<open>s' \<in> \<D> (if a \<in> B then Q a else Throw (P a) B Q)\<close>
      by (cases s; simp add: D_Mprefix) blast
    show \<open>s \<in> \<D> ?lhs\<close>
    proof (cases \<open>a \<in> B\<close>)
      from "*" show \<open>a \<in> B \<Longrightarrow> s \<in> \<D> ?lhs\<close>
        by (simp add: D_Throw T_Sliding T_Mprefix disjoint_iff)
           (metis Nil_elem_T emptyE empty_set list.sel(1, 3) self_append_conv2)
    next
      assume \<open>a \<notin> B\<close>
      with "*"(3) consider 
        \<open>\<exists>t1 t2. s' = t1 @ t2 \<and> t1 \<in> \<D> (P a) \<and> tickFree t1 \<and>
                 set t1 \<inter> ev ` B = {} \<and> front_tickFree t2\<close>
        | \<open>\<exists>t1 b t2. s' = t1 @ ev b # t2 \<and> t1 @ [ev b] \<in> \<T> (P a) \<and>
                     set t1 \<inter> ev ` B = {} \<and> b \<in> B \<and> t2 \<in> \<D> (Q b)\<close>
        by (simp add: D_Throw) blast
      thus \<open>s \<in> \<D> ?lhs\<close>
      proof cases
        assume \<open>\<exists>t1 t2. s' = t1 @ t2 \<and> t1 \<in> \<D> (P a) \<and> tickFree t1 \<and>
                        set t1 \<inter> ev ` B = {} \<and> front_tickFree t2\<close>
        then obtain t1 t2
          where ** : \<open>s' = t1 @ t2\<close> \<open>t1 \<in> \<D> (P a)\<close> \<open>tickFree t1\<close>
                     \<open>set t1 \<inter> ev ` B = {}\<close> \<open>front_tickFree t2\<close>
          by blast
        have *** : \<open>s = (ev a # t1) @ t2 \<and> set (ev a # t1) \<inter> ev ` B = {}\<close>
          by (simp add: "*"(1) "**"(1, 4) image_iff \<open>a \<notin> B\<close>)
        from "*" "**"(1, 2, 3, 5) show \<open>s \<in> \<D> ?lhs\<close>
          by (simp add: D_Throw D_Sliding D_Mprefix image_iff)
             (metis "***" event.distinct(1) list.discI list.sel(1, 3) tickFree_Cons)
      next
        assume \<open>\<exists>t1 b t2. s' = t1 @ ev b # t2 \<and> t1 @ [ev b] \<in> \<T> (P a) \<and>
                          set t1 \<inter> ev ` B = {} \<and> b \<in> B \<and> t2 \<in> \<D> (Q b)\<close>
        then obtain t1 b t2
          where ** : \<open>s' = t1 @ ev b # t2\<close> \<open>t1 @ [ev b] \<in> \<T> (P a)\<close>
                     \<open>set t1 \<inter> ev ` B = {}\<close> \<open>b \<in> B\<close> \<open>t2 \<in> \<D> (Q b)\<close> by blast
        have *** : \<open>s = (ev a # t1 @ [ev b]) @ t2 \<and> set (ev a # t1) \<inter> ev ` B = {}\<close>
          by (simp add: "*"(1) "**"(1, 3) image_iff \<open>a \<notin> B\<close>)
        from "*" "**"(1, 2, 4, 5) show \<open>s \<in> \<D> ?lhs\<close>
          by (simp add: D_Throw T_Sliding T_Mprefix)
             (metis "***" Cons_eq_appendI list.sel(1, 3))
      qed
    qed
  qed
next
  fix s X
  assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
  assume \<open>(s, X) \<in> \<F> ?lhs\<close>
  then consider \<open>s \<in> \<D> ?lhs\<close>
    | \<open>(s, X) \<in> \<F> (Mprefix A P \<rhd> P')\<close> \<open>set s \<inter> ev ` B = {}\<close>
    | \<open>\<exists>t1 b t2. s = t1 @ ev b # t2 \<and> t1 @ [ev b] \<in> \<T> (Mprefix A P \<rhd> P') \<and>
                 set t1 \<inter> ev ` B = {} \<and> b \<in> B \<and> (t2, X) \<in> \<F> (Q b)\<close>
    by (simp add: F_Throw D_Throw) blast
  thus \<open>(s, X) \<in> \<F> ?rhs\<close>
  proof cases
    from same_div D_F show \<open>s \<in> \<D> ?lhs \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close> by blast
  next
    show \<open>(s, X) \<in> \<F> (Mprefix A P \<rhd> P') \<Longrightarrow> set s \<inter> ev ` B = {} \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
      by (cases s; simp add: F_Sliding F_Mprefix F_Throw) blast
  next
    assume \<open>\<exists>t1 b t2. s = t1 @ ev b # t2 \<and> t1 @ [ev b] \<in> \<T> (Mprefix A P \<rhd> P') \<and>
                      set t1 \<inter> ev ` B = {} \<and> b \<in> B \<and> (t2, X) \<in> \<F> (Q b)\<close>
    then obtain t1 b t2 
      where * : \<open>s = t1 @ ev b # t2\<close> \<open>t1 @ [ev b] \<in> \<T> (Mprefix A P \<rhd> P')\<close>
                \<open>set t1 \<inter> ev ` B = {}\<close> \<open>b \<in> B\<close> \<open>(t2, X) \<in> \<F> (Q b)\<close> by blast
    from "*"(2) consider \<open>t1 @ [ev b] \<in> \<T> (Mprefix A P)\<close> | \<open>t1 @ [ev b] \<in> \<T> P'\<close>
      by (simp add: T_Sliding) blast
    thus \<open>(s, X) \<in> \<F> ?rhs\<close>
    proof cases
      assume \<open>t1 @ [ev b] \<in> \<T> (Mprefix A P)\<close>
      then obtain a t1'
        where \<open>t1 @ [ev b] = ev a # t1'\<close> \<open>a \<in> A\<close> \<open>t1' \<in> \<T> (P a)\<close>
        by (simp add: T_Mprefix)
           (metis list.exhaust_sel snoc_eq_iff_butlast)
      with "*"(1, 3, 4, 5) show \<open>(s, X) \<in> \<F> ?rhs\<close>
        by (cases t1; simp add: "*"(1) F_Sliding F_Mprefix F_Throw) blast
    next
      from "*"(1, 3, 4, 5) show \<open>t1 @ [ev b] \<in> \<T> P' \<Longrightarrow> (s, X) \<in> \<F> ?rhs\<close>
        by (simp add: F_Sliding F_Mprefix F_Throw) blast
    qed
  qed
next
  fix s X
  assume same_div : \<open>\<D> ?lhs = \<D> ?rhs\<close>
  assume \<open>(s, X) \<in> \<F> ?rhs\<close>
  then consider \<open>s \<in> \<D> ?rhs\<close> | \<open>(s, X) \<in> \<F> (Throw P' B Q)\<close>
    | \<open>s \<noteq> []\<close> \<open>(s, X) \<in> \<F> (\<box>a \<in> A \<rightarrow> (if a \<in> B then Q a else Throw (P a) B Q))\<close>
    by (simp add: F_Sliding D_Sliding) blast
  thus \<open>(s, X) \<in> \<F> ?lhs\<close>
  proof cases
    from same_div D_F show \<open>s \<in> \<D> ?rhs \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close> by blast
  next
    show \<open>(s, X) \<in> \<F> (Throw P' B Q) \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
      by (simp add: F_Throw F_Sliding D_Sliding T_Sliding) blast
  next
    assume \<open>s \<noteq> []\<close> \<open>(s, X) \<in> \<F> (\<box>a \<in> A \<rightarrow> (if a \<in> B then Q a else Throw (P a) B Q))\<close>
    then obtain a s'
      where * : \<open>s = ev a # s'\<close> \<open>a \<in> A\<close> 
                \<open>(s', X) \<in> \<F> (if a \<in> B then Q a else Throw (P a) B Q)\<close>
      by (simp add: F_Mprefix image_iff) (metis event.inject list.collapse)
    show \<open>(s, X) \<in> \<F> ?lhs\<close>
    proof (cases \<open>a \<in> B\<close>)
      assume \<open>a \<in> B\<close>
      have \<open>[ev a] \<in> \<T> (Mprefix A P \<rhd> P')\<close>
        by (simp add: T_Sliding T_Mprefix "*"(2) Nil_elem_T)
        
      with "*"(1, 3) \<open>a \<in> B\<close> show \<open>(s, X) \<in> \<F> ?lhs\<close>
        by (simp add: F_Throw) (metis append_Nil empty_set inf_bot_left)
    next
      assume \<open>a \<notin> B\<close>
      with "*"(3) consider \<open>s' \<in> \<D> (Throw (P a) B Q)\<close>
        | \<open>(s', X) \<in> \<F> (P a)\<close> \<open>set s' \<inter> ev ` B = {}\<close>
        | \<open>\<exists>t1 b t2. s' = t1 @ ev b # t2 \<and> t1 @ [ev b] \<in> \<T> (P a) \<and> 
                     set t1 \<inter> ev ` B = {} \<and> b \<in> B \<and> (t2, X) \<in> \<F> (Q b)\<close>
        by (simp add: F_Throw D_Throw) blast
      thus \<open>(s, X) \<in> \<F> ?lhs\<close>
      proof cases
        assume \<open>s' \<in> \<D> (Throw (P a) B Q)\<close>
        hence \<open>s \<in> \<D> ?rhs\<close> by (simp add: "*"(1, 2) D_Sliding D_Mprefix \<open>a \<notin> B\<close>)
        with same_div D_F show \<open>(s, X) \<in> \<F> ?lhs\<close> by blast
      next
        show \<open>(s', X) \<in> \<F> (P a) \<Longrightarrow> set s' \<inter> ev ` B = {} \<Longrightarrow> (s, X) \<in> \<F> ?lhs\<close>
          using "*"(1, 2) \<open>a \<notin> B\<close> by (simp add: F_Throw F_Sliding F_Mprefix) blast
      next
        assume \<open>\<exists>t1 b t2. s' = t1 @ ev b # t2 \<and> t1 @ [ev b] \<in> \<T> (P a) \<and> 
                          set t1 \<inter> ev ` B = {} \<and> b \<in> B \<and> (t2, X) \<in> \<F> (Q b)\<close>
        then obtain t1 b t2
          where ** : \<open>s' = t1 @ ev b # t2\<close> \<open>t1 @ [ev b] \<in> \<T> (P a)\<close>
                     \<open>set t1 \<inter> ev ` B = {}\<close> \<open>b \<in> B\<close> \<open>(t2, X) \<in> \<F> (Q b)\<close> by blast
        from "**" have *** : \<open>(ev a # t1) @ [ev b] \<in> \<T> (Mprefix A P) \<and> 
                              set (ev a # t1) \<inter> ev ` B = {}\<close>
          by (simp add: T_Mprefix "*"(2) image_iff \<open>a \<notin> B\<close>)
        from "*"(1) "**"(1, 4, 5) "**"(5) show \<open>(s, X) \<in> \<F> ?lhs\<close>
          by (simp add: F_Throw T_Sliding) (metis "***" Cons_eq_appendI)
      qed
    qed
  qed
qed



end 
