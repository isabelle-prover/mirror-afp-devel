(*<*)
\<comment>\<open> ******************************************************************** 
 * Project         : HOL-CSP - A Shallow Embedding of CSP in  Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Benoît Ballenghien.
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

section\<open> The Renaming Operator \<close>

theory  Renaming
  imports Process
begin

subsection\<open>Some preliminaries\<close>

definition EvExt where \<open>EvExt f x \<equiv> case_event (ev o f) tick x\<close>


term \<open>f -` B\<close> (* instead of defining our own antecedent function *)

definition finitary :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> bool\<close> 
  where \<open>finitary f \<equiv> \<forall>x. finite(f -` {x})\<close>



text \<open>We start with some simple results.\<close>

lemma \<open>f -` {} = {}\<close> by simp

lemma \<open>X \<subseteq> Y \<Longrightarrow> f -` X \<subseteq> f -` Y\<close> by (rule vimage_mono)

lemma \<open>f -`(X \<union> Y) = f -` X \<union> f -` Y\<close> by (rule vimage_Un)


lemma EvExt_id: \<open>EvExt id = id\<close>
  unfolding id_def EvExt_def by (metis comp_apply event.exhaust event.simps(4, 5))

lemma EvExt_eq_tick: \<open>EvExt f a = tick \<longleftrightarrow> a = tick\<close>
  by (metis EvExt_def comp_apply event.exhaust event.simps(3, 4, 5))

lemma tick_eq_EvExt: \<open>tick = EvExt f a \<longleftrightarrow> a = tick\<close>
  by (metis EvExt_eq_tick)

lemma EvExt_ev1: \<open>EvExt f b = ev a \<longleftrightarrow> (\<exists>c. b = ev c \<and> EvExt f (ev c) = ev a)\<close>
  by (metis event.exhaust event.simps(3) tick_eq_EvExt)

lemma EvExt_tF: \<open>tickFree (map (EvExt f) s) \<longleftrightarrow> tickFree s\<close> 
  unfolding tickFree_def by (auto simp add: tick_eq_EvExt image_iff)

lemma inj_EvExt: \<open>inj EvExt\<close>
  unfolding inj_on_def EvExt_def
  by auto (metis comp_eq_dest_lhs event.simps(4, 5) ext)




lemma EvExt_ftF: \<open>front_tickFree (map (EvExt f) s) \<longleftrightarrow> front_tickFree s\<close> 
  unfolding front_tickFree_def by safe (metis (no_types, opaque_lifting) EvExt_tF map_tl rev_map)+
 

lemma map_EvExt_tick: \<open>[tick] = map (EvExt f) t \<longleftrightarrow> t = [tick]\<close>
  using tick_eq_EvExt by fastforce


lemma anteced_EvExt_diff_tick: \<open>EvExt f -` (X - {tick}) = EvExt f -` X - {tick}\<close>
  by (rule subset_antisym) (simp_all add: EvExt_eq_tick subset_Diff_insert subset_vimage_iff)
  


lemma   ev_elem_anteced1: \<open>ev a \<in> EvExt f -` A \<longleftrightarrow> ev (f a) \<in> A\<close>
  and tick_elem_anteced1: \<open>tick \<in> EvExt f -` A \<longleftrightarrow> tick \<in> A\<close>
  unfolding EvExt_def by simp_all
  

lemma hd_map_EvExt: \<open>t \<noteq> [] \<Longrightarrow> hd t = ev a \<Longrightarrow> hd (map (EvExt f) t) = ev (f a)\<close>
  and tl_map_EvExt: \<open>t \<noteq> [] \<Longrightarrow> tl (map (EvExt f) t) = map (EvExt f) (tl t)\<close>
  unfolding EvExt_def by (simp_all add:  list.map_sel(1) map_tl)



subsection\<open>The Renaming Operator Definition\<close>

lift_definition Renaming :: \<open>['a process, 'a \<Rightarrow> 'b] \<Rightarrow> 'b process\<close>
  is \<open>\<lambda>P f. ({(s, R). \<exists> s1. (s1, (EvExt f) -` R) \<in> \<F> P \<and> s = map (EvExt f) s1} \<union>
             {(s ,R). \<exists> s1 s2. tickFree s1 \<and> front_tickFree s2 \<and> s = (map (EvExt f) s1) @ s2 \<and> s1 \<in> \<D> P},
             {t. \<exists> s1 s2. tickFree s1 \<and> front_tickFree s2 \<and> t = (map (EvExt f) s1) @ s2 \<and> s1 \<in> \<D> P})\<close>
proof -
  show "is_process ({(s, R). \<exists> s1. (s1, (EvExt f) -` R) \<in> \<F> P \<and> s = map (EvExt f) s1} \<union>
              {(s ,R). \<exists> s1 s2.   tickFree s1 \<and> front_tickFree s2 
                                \<and> s = (map (EvExt (f :: 'a \<Rightarrow> 'b)) s1) @ s2 \<and> s1 \<in> \<D> P},
              {t.      \<exists> s1 s2. tickFree s1 \<and> front_tickFree s2 
                                \<and> t = (map (EvExt f) s1) @ s2 \<and> s1 \<in> \<D> P})"
              (is "is_process(?f, ?d)") for P f
unfolding is_process_def FAILURES_def DIVERGENCES_def
  proof (simp only: fst_conv snd_conv, intro conjI allI impI)
    show \<open>([], {}) \<in> ?f\<close>
      by (simp add: process_charn)
  next
    show \<open>(s, X) \<in> ?f \<Longrightarrow> front_tickFree s\<close> for s X
      by (auto simp add: EvExt_ftF is_processT2 EvExt_tF front_tickFree_append)
  next
    show \<open>(s @ t, {}) \<in> ?f \<Longrightarrow> (s, {}) \<in> ?f\<close> for s t
    proof (induct t rule: rev_induct, simp, auto,
           metis (no_types, lifting) is_processT3_SR map_eq_append_conv, goal_cases)
      case (1 x t s1 s2)
      show ?case
      proof (rule "1"(1), auto)
        assume a1: \<open>\<forall>s1. tickFree s1 \<longrightarrow> 
                           (\<forall>s2. s @ t = map (EvExt f) s1 @ s2 \<longrightarrow> front_tickFree s2 \<longrightarrow> s1 \<notin> \<D> P)\<close>
        have \<open>(if s2 = [] then butlast s1 else s1) \<notin> \<D> P\<close>
          apply (rule a1[rule_format, of _ \<open>butlast s2\<close>])
          using "1"(3, 4, 5) apply (auto simp add: tickFree_def front_tickFree_def 
                                              intro: in_set_butlastD)
             apply ((metis append_assoc butlast_snoc map_butlast)+)[2]
           apply (metis append_assoc butlast_append butlast_snoc)
          by (metis butlast_rev list.set_sel(2) rev_is_Nil_conv rev_rev_ident)
        with \<open>s1 \<in> \<D> P\<close> have \<open>s2 = []\<close> by presburger
        with "1"(5, 6) show \<open>\<exists>s1. (s1, {}) \<in> \<F> P \<and> s @ t = map (EvExt f) s1\<close>
          apply (rule_tac x = \<open>butlast s1\<close> in exI, intro conjI)
          by (metis append_butlast_last_id butlast.simps(1) process_charn)
             (metis butlast_append map_butlast snoc_eq_iff_butlast)
      qed
    qed
  next
    show \<open>(s, Y) \<in> ?f \<and> X \<subseteq> Y \<Longrightarrow> (s, X) \<in> ?f\<close> for s X Y
      apply (induct s rule: rev_induct, simp_all)
      by (meson is_processT4 vimage_mono)
         (metis process_charn vimage_mono)
  next
    show \<open>(s, X) \<in> ?f \<and> (\<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> ?f) \<Longrightarrow> (s, X \<union> Y) \<in> ?f\<close> for s X Y
      by auto (metis (no_types, lifting) is_processT5 list.simps(8, 9) map_append vimageE)
  next
    show \<open>(s @ [tick], {}) \<in> ?f \<Longrightarrow> (s, X - {tick}) \<in> ?f\<close> for s X
      apply auto
      by (metis (no_types, lifting) anteced_EvExt_diff_tick is_processT6 map_EvExt_tick 
                                    map_eq_append_conv)
         (metis EvExt_tF append.assoc butlast_snoc front_tickFree_charn non_tickFree_tick
                tickFree_Nil tickFree_append tickFree_implies_front_tickFree)
  next
    show \<open>s \<in> ?d \<and> tickFree s \<and> front_tickFree t \<Longrightarrow> s @ t \<in> ?d\<close> for s t
      using front_tickFree_append by safe auto
  next
    show \<open>s \<in> ?d \<Longrightarrow> (s, X) \<in> ?f\<close> for s X by blast
      
  next
    show \<open>s @ [tick] \<in> ?d \<Longrightarrow> s \<in> ?d\<close> for s
      apply (induct s, auto)
      by (metis EvExt_tF Nil_is_map_conv hd_append2 list.exhaust_sel list.sel(1) tickFree_Cons)
         (metis Cons_eq_appendI EvExt_tF append.assoc butlast_snoc front_tickFree_charn 
                non_tickFree_tick tickFree_Nil tickFree_append tickFree_implies_front_tickFree)
  qed
qed


text \<open>Some syntaxic sugar\<close>

syntax
  "_Renaming"  :: \<open>'a process \<Rightarrow> updbinds \<Rightarrow> 'a process\<close> (\<open>_\<lbrakk>_\<rbrakk>\<close> [100, 100]) (*see the values we need, at least 51*)
translations
  "_Renaming P updates" \<rightleftharpoons> "CONST Renaming P (_Update (CONST id) updates)"


text \<open>Now we can write \<^term>\<open>P\<lbrakk>a := b\<rbrakk>\<close>. But like in \<^theory>\<open>HOL.Fun\<close>, we can write this kind of
      expression with as many updates we want: \<^term>\<open>P\<lbrakk>a := b, c := d, e := f, g := h\<rbrakk>\<close>.
      By construction we also inherit all the results about \<^const>\<open>fun_upd\<close>, for example
      @{thm fun_upd_other fun_upd_upd fun_upd_twist}.\<close>

lemma \<open>P\<lbrakk>x := y, x := z\<rbrakk> = P\<lbrakk>x := z\<rbrakk>\<close> by simp

lemma \<open>a \<noteq> c \<Longrightarrow> P\<lbrakk>a := b, c := d\<rbrakk> = P\<lbrakk>c := d, a := b\<rbrakk>\<close> by (simp add: fun_upd_twist)




subsection\<open>The Projections\<close>

lemma F_Renaming: \<open>\<F> (Renaming P f) = 
  {(s, R). \<exists>s1. (s1, EvExt f -` R) \<in> \<F> P \<and> s = map (EvExt f) s1} \<union>
  {(s, R). \<exists>s1 s2. tickFree s1 \<and> front_tickFree s2 \<and> s = map (EvExt f) s1 @ s2 \<and> s1 \<in> \<D> P}\<close>
  by (simp add: Failures.rep_eq FAILURES_def Renaming.rep_eq)

lemma D_Renaming: \<open>\<D> (Renaming P f) = {t. \<exists>s1 s2. tickFree s1 \<and> front_tickFree s2 \<and> 
                                                   t = map (EvExt f) s1 @ s2 \<and> s1 \<in> \<D> P}\<close>
  by (simp add: Divergences.rep_eq DIVERGENCES_def Renaming.rep_eq)

lemma T_Renaming: \<open>\<T> (Renaming P f) = 
  {t. \<exists> t1. t1 \<in> \<T> P \<and> t = map (EvExt f) t1} \<union> 
  {t.\<exists> t1 t2. tickFree t1 \<and> front_tickFree t2 \<and> t = map (EvExt f) t1 @ t2 \<and> t1 \<in> \<D> P}\<close>
  apply (subst Traces.rep_eq, auto simp add: TRACES_def Failures.rep_eq[symmetric] F_Renaming)
  by (use F_T in blast) (metis T_F vimage_empty)



subsection\<open>Continuity Rule\<close>

subsubsection \<open>Monotonicity of \<^const>\<open>Renaming\<close>.\<close>

lemma mono_Renaming[simp] : \<open>P \<sqsubseteq> Q \<Longrightarrow> (Renaming P f) \<sqsubseteq> (Renaming Q f)\<close>
proof (subst le_approx_def, intro conjI)
  show \<open>P \<sqsubseteq> Q \<Longrightarrow> \<D> (Renaming Q f) \<subseteq> \<D> (Renaming P f)\<close>
    unfolding D_Renaming using le_approx1 by blast
next 
  show \<open>P \<sqsubseteq> Q \<Longrightarrow> \<forall>s. s \<notin> \<D> (Renaming P f) \<longrightarrow> \<R>\<^sub>a (Renaming P f) s = \<R>\<^sub>a (Renaming Q f) s\<close>
    apply (auto simp add: Ra_def D_Renaming F_Renaming)
      apply (metis EvExt_ftF append.right_neutral front_tickFree_charn front_tickFree_single
                   le_approx2 map_append process_charn tickFree_Cons tickFree_Nil tickFree_append)
    using le_approx_lemma_F by blast (metis le_approx_def subset_eq)
next
  show \<open>P \<sqsubseteq> Q \<Longrightarrow> min_elems (\<D> (Renaming P f)) \<subseteq> \<T> (Renaming Q f)\<close>
  proof (unfold min_elems_def, auto simp add: D_Renaming T_Renaming, goal_cases)
    case (1 s1 s2)
    obtain t2 where f1: \<open>map (EvExt f) t2 = s2\<close>
      by (metis "1"(3, 4, 5, 6) front_tickFree_charn less_append map_is_Nil_conv nil_less2)
    with "1" show ?case 
      apply (rule_tac x = \<open>s1 @ t2\<close> in exI, simp)
      apply (rule le_approx3[simplified subset_iff, OF "1"(1), rule_format])
      apply (induct s2 rule: rev_induct, induct s1 rule: rev_induct, auto)
        apply (simp add: Nil_min_elems)
       apply (metis "1"(5) append.right_neutral f1 less_self list.simps(8) min_elems3)
      by (metis append.assoc front_tickFree_dw_closed less_self)
  qed
qed

  


lemma \<open>{ev c |c. f c = a} = ev`{c . f c = a}\<close> by (rule setcompr_eq_image)


lemma vimage_EvExt_subset_vimage: \<open>EvExt f -` (ev ` A) \<subseteq> insert tick (ev ` (f -` A))\<close>
  and vimage_subset_vimage_EvExt: \<open>(ev ` (f -` A)) \<subseteq> (EvExt f -` (ev ` A)) - {tick}\<close>
  unfolding EvExt_def by auto (metis comp_apply event.exhaust event.simps(4) image_iff vimage_eq)



subsubsection \<open>Some useful results about \<^const>\<open>finitary\<close>, and preliminaries lemmas for continuity.\<close>

lemma inj_imp_finitary[simp] : \<open>inj f \<Longrightarrow> finitary f\<close> by (simp add: finitary_def finite_vimageI)

lemma finitary_comp_iff : \<open>finitary g \<Longrightarrow> finitary (g o f) \<longleftrightarrow> finitary f\<close>
proof (unfold finitary_def, intro iffI allI;
       (subst vimage_comp[symmetric] | subst (asm) vimage_comp[symmetric]))
  have f1: \<open>f -` g -` {x} = (\<Union>y \<in> g -` {x}. f -` {y})\<close> for x by blast
  show \<open>finite (f -` g -` {x})\<close> if  \<open>\<forall>x. finite (f -` {x})\<close> and \<open>\<forall>x. finite (g -` {x})\<close> for x
    apply (subst f1, subst finite_UN)
    by (rule that(2)[unfolded finitary_def, rule_format])
       (intro ballI that(1)[rule_format])
qed (metis finite_Un insert_absorb vimage_insert vimage_singleton_eq)



lemma finitary_updated_iff[simp] : \<open>finitary (f (a := b)) \<longleftrightarrow> finitary f\<close>
proof (unfold fun_upd_def finitary_def vimage_def, intro iffI allI)
  show \<open>finite {x. (if x = a then b else f x) \<in> {y}}\<close> if \<open>\<forall>y. finite {x. f x \<in> {y}}\<close> for y
    apply (rule finite_subset[of _ \<open>{x. x = a} \<union> {x. f x \<in> {y}}\<close>], (auto)[1])
    apply (rule finite_UnI)
    by simp (fact that[rule_format]) 
next
  show \<open>finite {x. f x \<in> {y}}\<close> if \<open>\<forall>y. finite {x. (if x = a then b else f x) \<in> {y}}\<close> for y
    apply (rule finite_subset[of _ \<open>{x. x = a \<and> f x \<in> {y}} \<union> {x. x \<noteq> a \<and> f x \<in> {y}}\<close>], (auto)[1])
    apply (rule finite_UnI)
    using that[rule_format, of y] by (simp_all add: Collect_mono rev_finite_subset)
qed

text \<open>By declaring this simp, we automatically obtain this kind of result.\<close>

lemma \<open>finitary f \<longleftrightarrow> finitary (f (a := b, c := d, e:= g, h := i))\<close> by simp
    


lemma Cont_RenH2: \<open>finitary (EvExt f) \<longleftrightarrow> finitary f\<close>
proof -
  have inj_ev: \<open>inj ev\<close> by (simp add: inj_def)
  show \<open>finitary (EvExt f) \<longleftrightarrow> finitary f\<close>
    apply (subst finitary_comp_iff[of ev f, symmetric], simp add: inj_ev)
  proof (intro iffI; subst finitary_def, intro allI)
    have inj_ev: \<open>inj ev\<close> by (simp add: inj_def)
    show \<open>finite ((ev \<circ> f) -` {x})\<close> if \<open>finitary (EvExt f)\<close> for x
      apply (fold vimage_comp)
    proof (cases \<open>x = tick\<close>, (insert finite.simps)[1], blast) 
      assume \<open>x \<noteq> tick\<close>
      with subset_singletonD[OF inj_vimage_singleton[OF inj_ev, of x]] obtain y 
        where f1: \<open>ev -` {x} = {y}\<close> by auto (metis empty_iff event.exhaust vimage_singleton_eq)
      have f2: \<open>(f -` {y}) = ev -` ev ` f -` {y}\<close> by (simp add: inj_ev inj_vimage_image_eq)
      show \<open>finite (f -` ev -` {x})\<close> 
        apply (subst f1, subst f2)
        apply (rule finite_vimageI[OF _ inj_ev]) 
        apply (rule finite_subset[OF vimage_subset_vimage_EvExt])
        apply (rule finite_Diff)
        using finitary_def that by fastforce
    qed
  next
    show \<open>finite (EvExt f -` {x})\<close> if \<open>finitary (ev \<circ> f)\<close> for x
    proof (cases \<open>x = tick\<close>,
           metis Diff_cancel anteced_EvExt_diff_tick finite.emptyI infinite_remove vimage_empty)
      assume \<open>x \<noteq> tick\<close>
      with subset_singletonD[OF inj_vimage_singleton[OF inj_ev, of x]] obtain y 
        where f1: \<open>{x} = ev ` {y}\<close> using event.exhaust by auto
      show \<open>finite (EvExt f -` {x})\<close>
        apply (subst f1)
        apply (rule finite_subset[OF vimage_EvExt_subset_vimage])
        apply (subst finite_insert)
        apply (rule finite_imageI)
        by (fact finitary_comp_iff[OF inj_imp_finitary[OF inj_ev], of f, 
                                   simplified that, simplified, unfolded finitary_def, rule_format])
    qed
  qed 
qed



lemma Cont_RenH3:
  \<open>{s1 @ t1 |s1 t1. (\<exists> b. s1 = [b] & f b = a) \<and> list = map f t1} = 
   (\<Union> b \<in> f -`{a}. (\<lambda>t. b # t) ` {t. list = map f t})\<close>
  by auto (metis append_Cons append_Nil)


lemma Cont_RenH4: \<open>finitary f \<longleftrightarrow> (\<forall>s. finite {t. s = map f t})\<close>
proof (unfold finitary_def, intro iffI allI)
  show \<open>finite {t. s = map f t}\<close> if \<open>\<forall>x. finite (f -` {x})\<close>for s
  proof (induct s, simp)
    case (Cons a s)
    have \<open>{t. a # s = map f t} = (\<Union>b \<in> f -` {a}. {b # t |t. s = map f t})\<close>
      by (subst Cons_eq_map_conv) blast
    thus ?case by (simp add: finite_UN[OF that[rule_format]] local.Cons)
  qed
next
  have map1: \<open>[a] = map f s = (\<exists>b. s = [b] \<and> f b = a)\<close> for a s by fastforce
  show \<open>finite (f -` {x}) \<close> if \<open>\<forall>s. finite {t. s = map f t}\<close> for x
    by (simp add: vimage_def)
       (fact finite_vimageI[OF that[rule_format, of \<open>[x]\<close>, simplified map1], 
                            of \<open>\<lambda>x. [x]\<close>, unfolded inj_on_def, simplified])
qed



lemma Cont_RenH5: \<open>finitary f \<Longrightarrow> finite (\<Union>t \<in> {t. t \<le> s}. {s. t=map (EvExt f) s})\<close>
  apply (rule finite_UN_I)
  unfolding le_list_def
    apply (induct s rule: rev_induct, simp)
   apply (subgoal_tac \<open>{t. \<exists>r. t @ r = xs @ [x]} = insert (xs @ [x]) {t. \<exists>r. t @ r = xs}\<close>, auto)
   apply (metis butlast_append butlast_snoc self_append_conv)
  using Cont_RenH2 Cont_RenH4 by blast



lemma Cont_RenH6: \<open>{t. \<exists> t2. tickFree t \<and> front_tickFree t2 \<and> x = map (EvExt f) t @ t2} 
                   \<subseteq> {y. \<exists>xa. xa \<in> {t. t <= x} \<and> y \<in> {s. xa = map (EvExt f) s}}\<close>
  by (auto simp add: le_list_def)



lemma Cont_RenH7: \<open>finite {t. \<exists>t2. tickFree t \<and> front_tickFree t2 \<and> s = map (EvExt f) t @ t2}\<close>
  if \<open>finitary f\<close>
proof -
  have f1: \<open>{y. map (EvExt f) y \<le> s} = (\<Union>z \<in> {z. z \<le> s}. {y. z = map (EvExt f) y})\<close> by fast
  show ?thesis
    apply (rule finite_subset[OF Cont_RenH6])
    apply (simp add: f1)
    apply (rule finite_UN_I)
     apply (induct s rule: rev_induct, simp)
     apply (subgoal_tac \<open>{z. z \<le> xs @ [x]} = insert (xs @ [x]) {z. z \<le> xs}\<close>, auto)
      apply (metis append_eq_first_pref_spec append_self_conv le_list_def)
     apply (meson le_list_def order_trans)
    using Cont_RenH2 Cont_RenH4 that by blast
qed


lemma chain_Renaming: \<open>chain Y \<Longrightarrow> chain (\<lambda>i. Renaming (Y i) f)\<close>
  by (simp add: chain_def) 



text \<open>A key lemma for the continuity.\<close>

lemma Inter_nonempty_finite_chained_sets:
  \<open>\<forall>i. S i \<noteq> {} \<Longrightarrow> finite (S 0) \<Longrightarrow> \<forall>i. S (Suc i) \<subseteq> S i \<Longrightarrow> (\<Inter>i. S i) \<noteq> {}\<close>
proof (induct \<open>card (S 0)\<close> arbitrary: S rule: nat_less_induct)
  case 1
  show ?case
  proof (cases \<open>\<forall>i. S i = S 0\<close>)
    case True
    thus ?thesis by (metis "1.prems"(1) INT_iff ex_in_conv)
  next 
    case False
    have f1: \<open>i \<le> j \<Longrightarrow> S j \<subseteq> S i\<close> for i j by (simp add: "1.prems"(3) lift_Suc_antimono_le)
    with False obtain j m where f2: \<open>m < card (S 0)\<close> and f3: \<open>m = card (S j)\<close>
      by (metis "1.prems"(2) psubsetI psubset_card_mono zero_le)
    define T where \<open>T i \<equiv> S (i + j)\<close> for i
    have f4: \<open>m = card (T 0)\<close> unfolding T_def by (simp add: f3)
    from f1 have f5: \<open>(\<Inter>i. S i) = (\<Inter>i. T i)\<close> unfolding T_def by (auto intro: le_add1)
    show ?thesis
      apply (subst f5)
      apply (rule "1.hyps"[rule_format, OF f2, of T, OF f4], unfold T_def)
      by (simp_all add: "1.prems"(1, 3) lift_Suc_antimono_le)
         (metis "1.prems"(2) add_0 f1 finite_subset le_add1)
  qed
qed



subsubsection \<open>Finally, continuity !\<close>

lemma Cont_Renaming_prem:
  \<open>(\<Squnion> i. Renaming (Y i) f) = (Renaming (\<Squnion> i. Y i) f)\<close> if finitary: \<open>finitary f\<close> 
   and chain: \<open>chain Y\<close>
proof (subst Process_eq_spec, safe, goal_cases)
  show \<open>s \<in> \<D> (\<Squnion>i. Renaming (Y i) f) \<Longrightarrow> s \<in> \<D> (Renaming (Lub Y) f)\<close> for s
  proof (simp add: limproc_is_thelub chain chain_Renaming D_Renaming D_LUB)
    assume a1: \<open>\<forall>i. \<exists>s1.    tickFree s1 
                         \<and> (\<exists>s2. front_tickFree s2 
                                  \<and> s = map (EvExt f) s1 @ s2 \<and> s1 \<in> \<D> (Y i))\<close>
    define S where \<open>S i \<equiv> {s1. \<exists>t2.   tickFree s1 \<and> front_tickFree t2 
                                    \<and> s = map (EvExt f) s1 @ t2 \<and> s1 \<in> \<D> (Y i)}\<close> for i

    have \<open>(\<Inter>i. S i) \<noteq> {}\<close> 
      apply (rule Inter_nonempty_finite_chained_sets, unfold S_def)
        apply (insert a1, blast)[1]
       apply (rule finite_subset[OF _ Cont_RenH7[OF finitary, of s]], blast)
      using chain unfolding chain_def le_approx_def by blast
    then obtain s1 where f5: \<open>s1 \<in> (\<Inter>i. S i)\<close> by blast
    
    thus \<open>\<exists>s1. tickFree s1 \<and> (\<exists>s2.   front_tickFree s2 
                                   \<and> s = map (EvExt f) s1 @ s2 
                                   \<and> (\<forall>i. s1 \<in> \<D> (Y i)))\<close>
      by (rule_tac x = s1 in exI, unfold S_def) auto
  qed
next
  show \<open>s \<in> \<D> (Renaming (Lub Y) f) \<Longrightarrow> s \<in> \<D> (\<Squnion>i. Renaming (Y i) f)\<close> for s
    by (auto simp add: limproc_is_thelub chain chain_Renaming D_Renaming D_LUB)
next
  show \<open>(s, X) \<in> \<F> (\<Squnion>i. Renaming (Y i) f) \<Longrightarrow> (s, X) \<in> \<F> (Renaming (Lub Y) f)\<close> for s X
  proof (auto simp add: limproc_is_thelub chain chain_Renaming F_Renaming D_LUB F_LUB)
    assume a1: \<open>\<forall>i. (\<exists>s1. (s1, EvExt f -` X) \<in> \<F> (Y i) \<and> s = map (EvExt f) s1) \<or>
                    (\<exists>s1. tickFree s1 \<and> 
                          (\<exists>s2.   front_tickFree s2 
                                \<and> s = map (EvExt f) s1 @ s2 
                                \<and> s1 \<in> \<D> (Y i)))\<close>
       and a2: \<open>\<forall>s1. tickFree s1 \<longrightarrow> 
                     (\<forall>s2. s = map (EvExt f) s1 @ s2
                             \<longrightarrow> front_tickFree s2
                             \<longrightarrow> (\<exists>i. s1 \<notin> \<D> (Y i)))\<close>
    define S where \<open>S i \<equiv> {s1. (s1, EvExt f -` X) \<in> \<F> (Y i) \<and> s = map (EvExt f) s1} \<union>
                           {s1. \<exists>t2. tickFree s1 
                                     \<and> front_tickFree t2 
                                     \<and> s = map (EvExt f) s1 @ t2 
                                     \<and> s1 \<in> \<D> (Y i)}\<close> for i

    have \<open>s1 \<in> (\<Inter>i. S i) \<Longrightarrow> (\<forall>i. (s1, EvExt f -` X) \<in> \<F> (Y i) \<and> s = map (EvExt f) s1) 
                              \<or> tickFree s1 \<and> (\<exists>s2.    front_tickFree s2 
                                                     \<and> s = map (EvExt f) s1 @ s2 
                                                     \<and> (\<forall>i. s1 \<in> \<D> (Y i)))\<close> for s1
      unfolding S_def by auto (meson NF_ND)
    hence f1: \<open>s1 \<in> (\<Inter>i. S i) \<Longrightarrow> (\<forall>i. (s1, EvExt f -` X) \<in> \<F>(Y i) \<and> s = map(EvExt f) s1)\<close> for s1
      by (meson a2)
    have \<open>(\<Inter>i. S i) \<noteq> {}\<close>
      apply (rule Inter_nonempty_finite_chained_sets, unfold S_def)
        apply (insert a1, blast)[1]
       apply (subst finite_Un, intro conjI)
        apply (rule finite_subset[of _ \<open>{s1. s = map (EvExt f) s1}\<close>], blast)
        apply (insert Cont_RenH2 Cont_RenH4 finitary, blast)[1]
       apply (rule finite_subset[OF _ Cont_RenH7[OF finitary, of s]], blast)
      using NF_ND chain po_class.chainE proc_ord2a chain le_approx_def by safe blast+

    then obtain s1 where \<open>s1 \<in> (\<Inter>i. S i)\<close> by blast
    thus \<open>\<exists>s1. (\<forall>x. (s1, EvExt f -` X) \<in> \<F> (Y x)) \<and> s = map (EvExt f) s1\<close> 
      using f1 by (rule_tac x = s1 in exI) blast
  qed
next
  show \<open>(s, X) \<in> \<F> (Renaming (Lub Y) f) \<Longrightarrow> (s, X) \<in> \<F> (\<Squnion>i. Renaming (Y i) f)\<close> for s X
    by (auto simp add: limproc_is_thelub chain chain_Renaming F_Renaming D_LUB F_LUB)  
qed
 

lemma Renaming_cont[simp] : \<open>cont P \<Longrightarrow> finitary f \<Longrightarrow> cont (\<lambda>x. (Renaming (P x) f))\<close>
  by (rule contI2)
     (simp add: cont2monofunE monofunI, simp add: Cont_Renaming_prem ch2ch_cont cont2contlubE)


lemma RenamingF_cont : \<open>cont P \<Longrightarrow> cont (\<lambda>x. (P x)\<lbrakk>a := b\<rbrakk>)\<close>
  (* by simp *)
  by (simp only: Renaming_cont finitary_updated_iff inj_imp_finitary inj_on_id)


lemma \<open>cont P \<Longrightarrow> cont (\<lambda>x. (P x)\<lbrakk>a := b, c := d, e := f, g := a\<rbrakk>)\<close>
  (* by simp *)
  apply (erule Renaming_cont)
  apply (simp only: finitary_updated_iff)
  apply (rule inj_imp_finitary)
  by (rule inj_on_id)
  
 



subsection \<open>Some nice properties\<close>


lemma EvExt_comp: \<open>EvExt (g \<circ> f) = EvExt g \<circ> EvExt f\<close>
  unfolding EvExt_def by (rule ext, auto) (metis comp_apply event.exhaust event.simps(4, 5))



lemma Renaming_comp : \<open>Renaming P (g o f) = Renaming (Renaming P f) g\<close>
proof (subst Process_eq_spec, intro conjI subset_antisym)
  show \<open>\<F> (Renaming P (g \<circ> f)) \<subseteq> \<F> (Renaming (Renaming P f) g)\<close>
    apply (simp add: F_Renaming D_Renaming subset_iff, safe)
    by (metis (no_types, opaque_lifting) EvExt_comp list.map_comp set.compositionality)
       (metis (no_types, opaque_lifting) EvExt_comp EvExt_tF append.right_neutral 
                                         front_tickFree_Nil list.map_comp)
next
  show \<open>\<F> (Renaming (Renaming P f) g) \<subseteq> \<F> (Renaming P (g \<circ> f))\<close>
    apply (auto simp add: F_Renaming D_Renaming EvExt_comp EvExt_ftF EvExt_tF front_tickFree_append)
    by (metis (no_types, opaque_lifting) EvExt_comp list.map_comp set.compositionality)
next
  show \<open>\<D> (Renaming P (g \<circ> f)) \<subseteq> \<D> (Renaming (Renaming P f) g)\<close>
    apply (simp add: D_Renaming subset_iff, safe)
    by (metis (no_types, opaque_lifting) EvExt_comp EvExt_tF append.right_neutral 
                                         front_tickFree_Nil list.map_comp)
next
  show \<open>\<D> (Renaming (Renaming P f) g) \<subseteq> \<D> (Renaming P (g \<circ> f))\<close>
    apply (auto simp add: D_Renaming subset_iff)
    by (metis EvExt_comp EvExt_tF front_tickFree_append)
qed




lemma Renaming_id: \<open>Renaming P id = P\<close>
  by (subst Process_eq_spec, auto simp add: F_Renaming D_Renaming EvExt_id 
                                            is_processT7_S is_processT8_S)
     (metis append.right_neutral front_tickFree_mono list.distinct(1) 
            nonTickFree_n_frontTickFree process_charn)
  

lemma Renaming_inv: \<open>Renaming (Renaming P f) (inv f) = P\<close> if \<open>inj f\<close>
  apply (subst Renaming_comp[symmetric])
  apply (subst inv_o_cancel[OF that])
  by (fact Renaming_id)


end

