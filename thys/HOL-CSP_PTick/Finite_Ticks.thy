(***********************************************************************************
 * Copyright (c) 2025 Université Paris-Saclay
 *
 * Author: Benoît Ballenghien, Université Paris-Saclay,
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

chapter \<open>Finite Ticks Predicate\<close>


(*<*)
theory Finite_Ticks
  imports "HOL-CSPM"
begin
  (*>*)



section \<open>Definitions\<close>

text \<open>Due to our generalization, the generalized sequential composition
      will require this additional assumption for continuity.
      Intuitively, having an infinite number of possible terminations after
      a given trace will lead to a infinite branching preventing continuity,
      to a certain extent like what happens with global non deterministic choice.\<close>


definition finite_all_ticks :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close>
  where \<open>finite_all_ticks P \<equiv> \<forall>t \<in> \<T> P. finite {r. t @ [\<checkmark>(r)] \<in> \<T> P}\<close>

lemma finite_all_ticksI : \<open>(\<And>t. t \<in> \<T> P \<Longrightarrow> finite {r. t @ [\<checkmark>(r)] \<in> \<T> P}) \<Longrightarrow> finite_all_ticks P\<close>
  by (simp add: finite_all_ticks_def)

lemma finite_all_ticksD : \<open>finite_all_ticks P \<Longrightarrow> finite {r. t @ [\<checkmark>(r)] \<in> \<T> P}\<close>
  by (simp add: finite_all_ticks_def)
    (meson is_processT3_TR_append not_finite_existsD)


text \<open>Actually, when a \<^const>\<open>tick\<close> only appears in divergences, it will not matter
      for continuity. We therefore introduce the modified predicate, which is much more useful.\<close>

definition finite_ticks :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> bool\<close> (\<open>\<bbbF>\<^sub>\<checkmark>'(_')\<close>)
  where \<open>\<bbbF>\<^sub>\<checkmark>(P) \<equiv> \<forall>t \<in> \<T> P. finite {r. t @ [\<checkmark>(r)] \<in> \<T> P - \<D> P}\<close>

lemma finite_ticksI :
  \<open>(\<And>t. t \<in> \<T> P \<Longrightarrow> t \<notin> \<D> P \<Longrightarrow> finite {r. t @ [\<checkmark>(r)] \<in> \<T> P}) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(P)\<close>
  by (simp add: finite_ticks_def)
    (metis (mono_tags, lifting) Collect_cong append_T_imp_tickFree front_tickFree_Cons_iff
      is_processT7 is_processT9 not_Cons_self2 not_finite_existsD)

lemma finite_ticksD :
  \<open>\<bbbF>\<^sub>\<checkmark>(P) \<Longrightarrow> t \<notin> \<D> P \<Longrightarrow> finite {r. t @ [\<checkmark>(r)] \<in> \<T> P}\<close>
  by (simp add: finite_ticks_def)
    (metis (lifting) Collect_cong is_processT3_TR_append
      is_processT9 not_finite_existsD)


lemma finite_all_ticks_imp_finite_ticks [simp] : \<open>finite_all_ticks P \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(P)\<close>
  by (simp add: finite_all_ticksD finite_ticksI)

lemma finite_all_ticks_is_finite_ticks_or_finite_UNIV :
  \<open>finite_all_ticks P \<longleftrightarrow> (if \<D> P = {} then \<bbbF>\<^sub>\<checkmark>(P) else finite (UNIV :: 'r set))\<close>
  \<comment>\<open>This is justifying why \<^const>\<open>finite_all_ticks\<close> is not really interesting.\<close>
  for P :: \<open>('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
proof (rule iffI)
  show \<open>if \<D> P = {} then \<bbbF>\<^sub>\<checkmark>(P) else finite (UNIV :: 'r set)\<close>
    if \<open>finite_all_ticks P\<close>
  proof (split if_split, intro conjI impI)
    from \<open>finite_all_ticks P\<close> show \<open>\<D> P = {} \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(P)\<close>
      by (simp add: finite_ticksI finite_all_ticksD)
  next
    assume \<open>\<D> P \<noteq> {}\<close>
    with nonempty_divE obtain t where \<open>tF t\<close> \<open>t \<in> \<D> P\<close> by blast
    hence \<open>t @ [\<checkmark>(r)] \<in> \<D> P\<close> for r by (simp add: is_processT7)
    with \<open>finite_all_ticks P\<close> show \<open>finite (UNIV :: 'r set)\<close>
      by (metis (mono_tags, lifting) Collect_cong D_T UNIV_I \<open>t \<in> \<D> P\<close>
          finite_all_ticks_def mem_Collect_eq top_set_def)
  qed
next
  show \<open>if \<D> P = {} then \<bbbF>\<^sub>\<checkmark>(P) else finite (UNIV :: 'r set) \<Longrightarrow> finite_all_ticks P\<close>
    by (simp add: finite_ticksD finite_all_ticks_def split: if_split_asm)
      (meson rev_finite_subset subset_UNIV)
qed



text \<open>We also introduce the concept that a function can preserve \<^const>\<open>finite_ticks\<close>.
      Unfortunately, we will not succeed in proving continuity under this condition
      for generalized sequential composition.\<close>

definition finite_ticks_fun :: \<open>(('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Rightarrow> ('b, 's) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k) \<Rightarrow> bool\<close> (\<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>'(_')\<close>)
  where \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f) \<equiv> \<forall>P. \<bbbF>\<^sub>\<checkmark>(P) \<longrightarrow> \<bbbF>\<^sub>\<checkmark>(f P)\<close>

lemma finite_ticks_funI: \<open>(\<And>P. \<bbbF>\<^sub>\<checkmark>(P) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(f P)) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f)\<close>
  by (simp add: finite_ticks_fun_def)

lemma finite_ticks_funD: \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(P) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(f P)\<close>
  by (simp add: finite_ticks_fun_def)



section \<open>Properties\<close>

named_theorems finite_ticks_simps
named_theorems finite_ticks_fun_simps

subsection \<open>Constant Processes\<close>

lemma finite_ticks_BOT [finite_ticks_simps] : \<open>\<bbbF>\<^sub>\<checkmark>(\<bottom>)\<close>
  by (simp add: finite_ticks_def BOT_projs)

lemma finite_ticks_fun_BOT [finite_ticks_fun_simps] : \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<bottom>)\<close>
  by (simp add: finite_ticks_fun_def finite_ticks_BOT)

lemma finite_ticks_SKIP [finite_ticks_simps] : \<open>\<bbbF>\<^sub>\<checkmark>(SKIP r)\<close>
  by (simp add: finite_ticks_def SKIP_projs)

lemma finite_ticks_STOP [finite_ticks_simps] : \<open>\<bbbF>\<^sub>\<checkmark>(STOP)\<close>
  by (simp add: finite_ticks_def T_STOP)

lemma finite_ticks_SKIPS_iff [finite_ticks_simps] : \<open>\<bbbF>\<^sub>\<checkmark>(SKIPS R) \<longleftrightarrow> finite R\<close>
  by (auto simp add: finite_ticks_def SKIPS_projs)


subsection \<open>Other properties\<close>

lemma finite_strict_ticks_of_imp_finite_ticks [finite_ticks_simps] :
  \<open>finite \<^bold>\<checkmark>\<^bold>s(P) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(P)\<close>
  by (metis (mono_tags, lifting) finite_subset finite_ticksI
      is_processT9 mem_Collect_eq strict_ticks_of_memI subsetI)

lemma finite_strict_ticks_of_image_imp_finite_ticks_fun [finite_ticks_fun_simps] :
  \<open>(\<And>x. finite \<^bold>\<checkmark>\<^bold>s(f x)) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f)\<close>
  by (simp add: finite_strict_ticks_of_imp_finite_ticks finite_ticks_funI)


lemma anti_mono_finite_ticks [finite_ticks_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>(P)\<close> if \<open>P \<sqsubseteq> Q\<close> \<open>\<bbbF>\<^sub>\<checkmark>(Q)\<close>
proof (rule finite_ticksI)
  fix t assume \<open>t \<in> \<T> P\<close> \<open>t \<notin> \<D> P\<close>
  have \<open>{r. t @ [\<checkmark>(r)] \<in> \<T> P} = {r. t @ [\<checkmark>(r)] \<in> \<T> Q}\<close>
    by (meson \<open>t \<notin> \<D> P\<close> is_processT9 le_approx2T \<open>P \<sqsubseteq> Q\<close>)
  also have \<open>finite \<dots>\<close>
  proof (rule \<open>\<bbbF>\<^sub>\<checkmark>(Q)\<close>[THEN finite_ticksD])
    from \<open>t \<notin> \<D> P\<close> le_approx1 \<open>P \<sqsubseteq> Q\<close> show \<open>t \<notin> \<D> (Q)\<close> by blast
  qed
  finally show \<open>finite {r. t @ [\<checkmark>(r)] \<in> \<T> P}\<close> .
qed

lemma anti_mono_finite_ticks_fun [finite_ticks_fun_simps] :
  \<open>f \<sqsubseteq> g \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(g) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f)\<close>
  by (metis anti_mono_finite_ticks finite_ticks_fun_def fun_below_iff)


lemma finite_ticks_LUB_iff [finite_ticks_fun_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>(\<Squnion>i. Y i) \<longleftrightarrow> (\<forall>i. \<bbbF>\<^sub>\<checkmark>(Y i))\<close> if \<open>chain Y\<close>
proof safe
  from anti_mono_finite_ticks is_ub_thelub \<open>chain Y\<close>
  show \<open>\<bbbF>\<^sub>\<checkmark>(\<Squnion>i. Y i) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(Y i)\<close> for i by blast
next
  show \<open>\<bbbF>\<^sub>\<checkmark>(\<Squnion>i. Y i)\<close> if \<open>\<forall>i. \<bbbF>\<^sub>\<checkmark>(Y i)\<close>
  proof (rule finite_ticksI)
    fix t assume \<open>t \<in> \<T> (\<Squnion>i. Y i)\<close> \<open>t \<notin> \<D> (\<Squnion>i. Y i)\<close>
    from \<open>t \<notin> \<D> (\<Squnion>i. Y i)\<close> obtain j where \<open>t \<notin> \<D> (Y j)\<close>
      by (metis D_LUB_2 \<open>chain Y\<close> limproc_is_thelub)
    have \<open>{r. t @ [\<checkmark>(r)] \<in> \<T> (\<Squnion>i. Y i)} = {r. t @ [\<checkmark>(r)] \<in> \<T> (Y j)}\<close>
      by (meson \<open>chain Y\<close> \<open>t \<notin> \<D> (Y j)\<close> is_processT9 is_ub_thelub le_approx2T)
    also have \<open>finite \<dots>\<close>
      by (fact \<open>\<forall>i. \<bbbF>\<^sub>\<checkmark>(Y i)\<close>[THEN spec, THEN finite_ticksD, OF \<open>t \<notin> \<D> (Y j)\<close>])
    finally show \<open>finite {r. t @ [\<checkmark>(r)] \<in> \<T> (\<Squnion>i. Y i)}\<close> .
  qed
qed


lemma adm_finite_ticks [finite_ticks_simps] : \<open>adm (\<lambda>P. \<bbbF>\<^sub>\<checkmark>(P))\<close>
  by (rule admI) (simp add: finite_ticks_LUB_iff)

lemma finite_ticks_fix [finite_ticks_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>(\<mu> X. f X)\<close> if \<open>cont f\<close> and \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f)\<close>
proof (induct rule: fix_ind)
  show \<open>adm finite_ticks\<close> by (fact adm_finite_ticks)
next
  show \<open>\<bbbF>\<^sub>\<checkmark>(\<bottom>)\<close> by (fact finite_ticks_BOT)
next
  show \<open>\<bbbF>\<^sub>\<checkmark>((\<Lambda> X. f X)\<cdot>X)\<close> if \<open>\<bbbF>\<^sub>\<checkmark>(X)\<close> for X
    by (simp add: \<open>cont f\<close>) (fact finite_ticks_funD[OF \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f)\<close> \<open>\<bbbF>\<^sub>\<checkmark>(X)\<close>])
qed



lemma adm_finite_ticks_fun [finite_ticks_fun_simps] : \<open>adm (\<lambda>f. \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f))\<close>
  by (simp add: admI ch2ch_fun finite_ticks_LUB_iff finite_ticks_fun_def lub_fun)

lemma finite_ticks_fun_fix [finite_ticks_fun_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<mu> X. f X)\<close> if \<open>cont f\<close> and \<open>\<And>x. \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(x) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f x)\<close>
proof (induct f rule: cont_fix_ind)
  from \<open>cont f\<close> show \<open>cont f\<close> .
next
  from adm_finite_ticks_fun show \<open>adm (\<lambda>f. \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f))\<close> .
next
  from finite_ticks_fun_BOT show \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<bottom>)\<close> .
next
  from \<open>\<And>y. \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(y) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f y)\<close> show \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(x) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f x)\<close> for x .
qed


lemma finite_ticks_fun_id [finite_ticks_fun_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(id)\<close> \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. x)\<close>
  by (simp_all add: finite_ticks_funI)

lemma finite_ticks_fun_const_iff [finite_ticks_fun_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. P) \<longleftrightarrow> \<bbbF>\<^sub>\<checkmark>(P)\<close>
  by (meson finite_ticks_STOP finite_ticks_fun_def)

lemma finite_ticks_fun_comp [finite_ticks_fun_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(g) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. g (f x))\<close>
  by (simp add: finite_ticks_fun_def)



section \<open>Laws\<close>

subsection \<open>Laws of \<^term>\<open>\<bbbF>\<^sub>\<checkmark>(P)\<close>\<close>

lemma finite_ticks_Ndet [finite_ticks_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>(P \<sqinter> Q)\<close> if \<open>\<bbbF>\<^sub>\<checkmark>(P)\<close> \<open>\<bbbF>\<^sub>\<checkmark>(Q)\<close>
proof (rule finite_ticksI)
  fix t assume \<open>t \<in> \<T> (P \<sqinter> Q)\<close> \<open>t \<notin> \<D> (P \<sqinter> Q)\<close>
  from \<open>t \<in> \<T> (P \<sqinter> Q)\<close>
  have \<open>t \<in> \<T> P \<and> t \<in> \<T> Q \<or> t \<in> \<T> P \<and> (\<forall>r. t @ [\<checkmark>(r)] \<notin> \<T> Q) \<or> (\<forall>r. t @ [\<checkmark>(r)] \<notin> \<T> P) \<and> t \<in> \<T> Q\<close>
    unfolding T_Ndet by (metis Un_iff is_processT3_TR_append)
  with \<open>\<bbbF>\<^sub>\<checkmark>(P)\<close> \<open>\<bbbF>\<^sub>\<checkmark>(Q)\<close> \<open>t \<notin> \<D> (P \<sqinter> Q)\<close> show \<open>finite {r. t @ [\<checkmark>(r)] \<in> \<T> (P \<sqinter> Q)}\<close>
    by (auto simp add: Ndet_projs dest: finite_ticksD)
qed


lemma finite_ticks_Det [finite_ticks_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>(P \<box> Q)\<close> if \<open>\<bbbF>\<^sub>\<checkmark>(P)\<close> \<open>\<bbbF>\<^sub>\<checkmark>(Q)\<close>
proof -
  have \<open>\<bbbF>\<^sub>\<checkmark>(P \<box> Q) = \<bbbF>\<^sub>\<checkmark>(P \<sqinter> Q)\<close> by (simp add: finite_ticks_def Det_projs Ndet_projs)
  with \<open>\<bbbF>\<^sub>\<checkmark>(P)\<close> \<open>\<bbbF>\<^sub>\<checkmark>(Q)\<close> show \<open>\<bbbF>\<^sub>\<checkmark>(P \<box> Q)\<close> by (simp add: finite_ticks_Ndet)
qed


lemma finite_ticks_Sliding [finite_ticks_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>(P) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(Q) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(P \<rhd> Q)\<close>
  by (simp add: Sliding_def finite_ticks_Ndet finite_ticks_Det)


lemma finite_ticks_Interrupt [finite_ticks_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>(P \<triangle> Q)\<close> if \<open>\<bbbF>\<^sub>\<checkmark>(P)\<close> \<open>\<bbbF>\<^sub>\<checkmark>(Q)\<close>
proof (cases \<open>Q = \<bottom>\<close>)
  show \<open>Q = \<bottom> \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(P \<triangle> Q)\<close> by (simp add: finite_ticks_BOT)
next
  show \<open>\<bbbF>\<^sub>\<checkmark>(P \<triangle> Q)\<close> if \<open>Q \<noteq> \<bottom>\<close>
  proof (rule finite_ticksI)
    fix t assume \<open>t \<in> \<T> (P \<triangle> Q)\<close> \<open>t \<notin> \<D> (P \<triangle> Q)\<close>
    have \<open>{r. t @ [\<checkmark>(r)] \<in> \<T> (P \<triangle> Q)} \<subseteq>
          {r. t @ [\<checkmark>(r)] \<in> \<T> P} \<union>
          (\<Union>u \<in> {u. \<exists>v. t = u @ v \<and> u \<in> \<T> P}. {r. drop (length u) t @ [\<checkmark>(r)] \<in> \<T> Q})\<close>
      by (simp add: subset_iff T_Interrupt)
        (metis Prefix_Order.prefix_length_le Prefix_Order.same_prefix_nil
          append_eq_append_conv_if append_eq_first_pref_spec butlast_append butlast_snoc)
    moreover have \<open>finite \<dots>\<close>
    proof (rule finite_UnI)
      from D_Interrupt \<open>t \<notin> \<D> (P \<triangle> Q)\<close> have \<open>t \<notin> \<D> P\<close> by blast
      thus \<open>finite {r. t @ [\<checkmark>(r)] \<in> \<T> P}\<close> by (simp add: finite_ticksD \<open>\<bbbF>\<^sub>\<checkmark>(P)\<close>)
    next
      show \<open>finite (\<Union>u\<in>{u. \<exists>v. t = u @ v \<and> u \<in> \<T> P}. {r. drop (length u) t @ [\<checkmark>(r)] \<in> \<T> Q})\<close>
      proof (rule finite_UN_I)
        show \<open>finite {u. \<exists>v. t = u @ v \<and> u \<in> \<T> P}\<close> by (prove_finite_subset_of_prefixes t)
      next
        fix u assume \<open>u \<in> {u. \<exists>v. t = u @ v \<and> u \<in> \<T> P}\<close>
        then obtain v where \<open>u \<in> \<T> P\<close> \<open>t = u @ v\<close> by blast
        with \<open>t \<in> \<T> (P \<triangle> Q)\<close> append_T_imp_tickFree consider \<open>tF u\<close> | \<open>v = []\<close> by blast
        thus \<open>finite {r. drop (length u) t @ [\<checkmark>(r)] \<in> \<T> Q}\<close>
        proof cases
          assume \<open>tF u\<close>
          with \<open>u \<in> \<T> P\<close> \<open>t \<notin> \<D> (P \<triangle> Q)\<close> have \<open>v \<notin> \<D> Q\<close>
            by (simp add: D_Interrupt \<open>t = u @ v\<close>)
          thus \<open>tF u \<Longrightarrow> finite {r. drop (length u) t @ [\<checkmark>(r)] \<in> \<T> Q}\<close>
            by (simp add: \<open>t = u @ v\<close> finite_ticksD \<open>\<bbbF>\<^sub>\<checkmark>(Q)\<close>)
        next
          from BOT_iff_Nil_D \<open>Q \<noteq> \<bottom>\<close> have \<open>[] \<notin> \<D> Q\<close> by blast
          with \<open>\<bbbF>\<^sub>\<checkmark>(Q)\<close> finite_ticksD have \<open>finite {r. [\<checkmark>(r)] \<in> \<T> Q}\<close> by force
          thus \<open>v = [] \<Longrightarrow> finite {r. drop (length u) t @ [\<checkmark>(r)] \<in> \<T> Q}\<close>
            by (simp add: \<open>t = u @ v\<close>)
        qed
      qed
    qed
    ultimately show \<open>finite {r. t @ [\<checkmark>(r)] \<in> \<T> (P \<triangle> Q)}\<close> by (fact finite_subset)
  qed
qed


lemma finite_ticks_Throw [finite_ticks_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>(P \<Theta> a\<in>A. Q a)\<close> if \<open>\<bbbF>\<^sub>\<checkmark>(P)\<close> \<open>\<And>a. a \<in> A \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(Q a)\<close>
proof (rule finite_ticksI)
  fix t assume \<open>t \<in> \<T> (P \<Theta> a\<in>A. Q a)\<close> \<open>t \<notin> \<D> (P \<Theta> a\<in>A. Q a)\<close>
  then consider \<open>t \<in> \<T> P\<close> \<open>set t \<inter> ev ` A = {}\<close>
    | t1 a t2 where \<open>t = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close>
      \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>t2 \<in> \<T> (Q a)\<close>
    unfolding Throw_projs by blast
  thus \<open>finite {r. t @ [\<checkmark>(r)] \<in> \<T> (P \<Theta> a\<in>A. Q a)}\<close>
  proof cases
    assume \<open>t \<in> \<T> P\<close> \<open>set t \<inter> ev ` A = {}\<close>
    hence \<open>{r. t @ [\<checkmark>(r)] \<in> \<T> (P \<Theta> a\<in>A. Q a)} \<subseteq> {r. t @ [\<checkmark>(r)] \<in> \<T> P}\<close>
      by (auto simp add: T_Throw D_T is_processT7 disjoint_iff image_iff)
        (metis (no_types) butlast.simps(2) butlast_append butlast_snoc in_set_conv_decomp)
    moreover have \<open>finite \<dots>\<close>
    proof (rule \<open>\<bbbF>\<^sub>\<checkmark>(P)\<close>[THEN finite_ticksD])
      from \<open>set t \<inter> ev ` A = {}\<close>
      have \<open>t \<in> \<D> P \<Longrightarrow> (if tF t then t else butlast t) \<in> \<D> (P \<Theta> a\<in>A. Q a)\<close>
        by (cases t rule: rev_cases, simp_all add: D_Throw)
          (metis D_imp_front_tickFree \<open>set t \<inter> ev ` A = {}\<close> append.right_neutral butlast_snoc
            div_butlast_when_non_tickFree_iff front_tickFree_Nil front_tickFree_nonempty_append_imp
            not_Cons_self2 not_is_ev tickFree_Cons_iff tickFree_append_iff)
      with \<open>t \<notin> \<D> (P \<Theta> a\<in>A. Q a)\<close> D_imp_front_tickFree div_butlast_when_non_tickFree_iff
      show \<open>t \<notin> \<D> P\<close> by blast
    qed
    ultimately show \<open>finite {r. t @ [\<checkmark>(r)] \<in> \<T> (P \<Theta> a\<in>A. Q a)}\<close> by (fact finite_subset)
  next
    fix t1 a t2 assume * : \<open>t = t1 @ ev a # t2\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close>
      \<open>set t1 \<inter> ev ` A = {}\<close> \<open>a \<in> A\<close> \<open>t2 \<in> \<T> (Q a)\<close>
    from \<open>t \<notin> \<D> (P \<Theta> a\<in>A. Q a)\<close>
    have \<open>t \<notin> {t1 @ t2 |t1 t2. t1 \<in> \<D> P \<and> tF t1 \<and> set t1 \<inter> ev ` A = {} \<and> ftF t2}\<close>
      by (simp add: D_Throw UnI1)

    with "*" have \<open>{r. t @ [\<checkmark>(r)] \<in> \<T> (P \<Theta> a\<in>A. Q a)} = {r. t2 @ [\<checkmark>(r)] \<in> \<T> (Q a)}\<close>
      by (simp add: T_Throw, safe)
        (metis Cons_eq_appendI append_assoc butlast_snoc front_tickFree_charn
          non_tickFree_tick tickFree_Nil tickFree_append_iff tickFree_imp_front_tickFree,
          solves \<open>simp add: Throw_T_third_clause_breaker\<close>, metis)
    also have \<open>finite \<dots>\<close>
    proof (rule \<open>\<And>a. a \<in> A \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(Q a)\<close>[THEN finite_ticksD, OF \<open>a \<in> A\<close>])
      from \<open>t \<notin> \<D> (P \<Theta> a\<in>A. Q a)\<close> \<open>t1 @ [ev a] \<in> \<T> P\<close> \<open>set t1 \<inter> ev ` A = {}\<close>
      show \<open>t2 \<notin> \<D> (Q a)\<close> by (auto simp add: D_Throw \<open>t = t1 @ ev a # t2\<close> \<open>a \<in> A\<close>)
    qed
    finally show \<open>finite {r. t @ [\<checkmark>(r)] \<in> \<T> (P \<Theta> a\<in>A. Q a)}\<close> .
  qed
qed


lemma finite_ticks_Renaming [finite_ticks_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>(Renaming P f g)\<close> if \<open>finitary f\<close> \<open>finitary g\<close> \<open>\<bbbF>\<^sub>\<checkmark>(P)\<close>
proof (rule finite_ticksI)
  fix t assume \<open>t \<notin> \<D> (Renaming P f g)\<close>
  hence \<open>{s. t @ [\<checkmark>(s)] \<in> \<T> (Renaming P f g)} \<subseteq>
         (\<Union>u\<in>{u. t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u \<and> u \<in> \<T> P}. {g r |r. u @ [\<checkmark>(r)] \<in> \<T> P})\<close>
    by (auto simp add: subset_iff Renaming_projs append_eq_map_conv tick_eq_map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_iff)
      (use is_processT3_TR_append in blast,
        metis append_Nil butlast_append event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k.disc(2) front_tickFree_iff_tickFree_butlast
        map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree snoc_eq_iff_butlast tickFree_butlast)
  moreover have \<open>finite \<dots>\<close>
  proof (rule finite_UN_I)
    have \<open>finitary (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)\<close> by (simp add: Cont_RenH2 \<open>finitary f\<close> \<open>finitary g\<close>)
    have \<open>{u. t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u \<and> u \<in> \<T> P} \<subseteq> {u. t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u}\<close> by blast
    moreover from Cont_RenH4 \<open>finitary (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g)\<close> have \<open>finite \<dots>\<close> by blast
    ultimately show \<open>finite {u. t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u \<and> u \<in> \<T> P}\<close> by (fact finite_subset)
  next
    fix u assume \<open>u \<in> {u. t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u \<and> u \<in> \<T> P}\<close>
    hence \<open>t = map (map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k f g) u\<close> \<open>u \<in> \<T> P\<close> by simp_all
    with \<open>t \<notin> \<D> (Renaming P f g)\<close> have \<open>u \<notin> \<D> P\<close>
      by (simp add: D_Renaming)
        (metis (no_types, opaque_lifting) D_imp_front_tickFree append_Nil append_Nil2
          div_butlast_when_non_tickFree_iff front_tickFree_charn map_butlast
          map_event\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k_tickFree snoc_eq_iff_butlast tickFree_Nil)
    thus \<open>finite {g r |r. u @ [\<checkmark>(r)] \<in> \<T> P}\<close>
      by (simp add: finite_ticksD \<open>\<bbbF>\<^sub>\<checkmark>(P)\<close>)
  qed
  ultimately show \<open>finite {r. t @ [\<checkmark>(r)] \<in> \<T> (Renaming P f g)}\<close> by (fact finite_subset)
qed


lemma finite_ticks_Seq [finite_ticks_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>(P \<^bold>; Q)\<close> if \<open>\<bbbF>\<^sub>\<checkmark>(Q)\<close>
proof (cases \<open>Q = \<bottom>\<close>)
  from not_finite_existsD show \<open>Q = \<bottom> \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(P \<^bold>; Q)\<close>
    by (auto simp add: finite_ticks_def Seq_projs BOT_projs)
next
  show \<open>\<bbbF>\<^sub>\<checkmark>(P \<^bold>; Q)\<close> if \<open>Q \<noteq> \<bottom>\<close>
  proof (rule finite_ticksI)
    fix t assume \<open>t \<notin> \<D> (P \<^bold>; Q)\<close>
    hence \<open>{r. t @ [\<checkmark>(r)] \<in> \<T> (P \<^bold>; Q)} \<subseteq>
           (\<Union>u \<in> {u. \<exists>v r. t = u @ v \<and> u @ [\<checkmark>(r)] \<in> \<T> P}. {r. drop (length u) t @ [\<checkmark>(r)] \<in> \<T> Q})\<close>
      by (auto simp add: Seq_projs intro: is_processT9)
        (metis (no_types, opaque_lifting) T_imp_front_tickFree append_butlast_last_id
          append_eq_conv_conj butlast_append butlast_snoc front_tickFree_nonempty_append_imp
          last_appendR list.distinct(1) non_tickFree_tick tickFree_append_iff)
    moreover have \<open>finite \<dots>\<close>
    proof (rule finite_UN_I)
      show \<open>finite {u. \<exists>v r. t = u @ v \<and> u @ [\<checkmark>(r)] \<in> \<T> P}\<close>
        by (prove_finite_subset_of_prefixes t)
    next
      fix u assume \<open>u \<in> {u. \<exists>v r. t = u @ v \<and> u @ [\<checkmark>(r)] \<in> \<T> P}\<close>
      then obtain v r where \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>t = u @ v\<close> by blast
      with append_T_imp_tickFree consider \<open>tF u\<close> | \<open>v = []\<close> by blast
      thus \<open>finite {r. drop (length u) t @ [\<checkmark>(r)] \<in> \<T> Q}\<close>
      proof cases
        assume \<open>tF u\<close>
        with \<open>u @ [\<checkmark>(r)] \<in> \<T> P\<close> \<open>t \<notin> \<D> (P \<^bold>; Q)\<close> have \<open>v \<notin> \<D> Q\<close>
          by (auto simp add: D_Seq \<open>t = u @ v\<close>)
        thus \<open>tF u \<Longrightarrow> finite {r. drop (length u) t @ [\<checkmark>(r)] \<in> \<T> Q}\<close>
          by (simp add: \<open>t = u @ v\<close> finite_ticksD \<open>\<bbbF>\<^sub>\<checkmark>(Q)\<close>)
      next
        from BOT_iff_Nil_D \<open>Q \<noteq> \<bottom>\<close> have \<open>[] \<notin> \<D> Q\<close> by blast
        with \<open>\<bbbF>\<^sub>\<checkmark>(Q)\<close> finite_ticksD have \<open>finite {r. [\<checkmark>(r)] \<in> \<T> Q}\<close> by force
        thus \<open>v = [] \<Longrightarrow> finite {r. drop (length u) t @ [\<checkmark>(r)] \<in> \<T> Q}\<close>
          by (simp add: \<open>t = u @ v\<close>)
      qed
    qed
    ultimately show \<open>finite {r. t @ [\<checkmark>(r)] \<in> \<T> (P \<^bold>; Q)}\<close> by (fact finite_subset)
  qed
qed



lemma finite_ticks_Sync [finite_ticks_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>(P \<lbrakk>S\<rbrakk> Q)\<close> if \<open>\<bbbF>\<^sub>\<checkmark>(P) \<or> \<bbbF>\<^sub>\<checkmark>(Q)\<close>
proof (rule finite_ticksI)
  fix t assume \<open>t \<notin> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
  have \<open>{r. t @ [\<checkmark>(r)] \<in> \<T> (P \<lbrakk>S\<rbrakk> Q)} \<subseteq>
        (\<Union>(t_P, t_Q)\<in>{(t_P, t_Q). t setinterleaves ((t_P, t_Q), range tick \<union> ev ` S)}.
                      {r. t_P @ [\<checkmark>(r)] \<in> \<T> P \<and> t_P \<notin> \<D> P \<and> t_Q @ [\<checkmark>(r)] \<in> \<T> Q \<and> t_Q \<notin> \<D> Q})\<close>
    (is \<open>_ \<subseteq> ?rhs\<close>)
  proof (rule subsetI)
    fix r assume \<open>r \<in> {r. t @ [\<checkmark>(r)] \<in> \<T> (P \<lbrakk>S\<rbrakk> Q)}\<close>
    hence \<open>t @ [\<checkmark>(r)] \<in> \<T> (P \<lbrakk>S\<rbrakk> Q)\<close> ..
    moreover from \<open>t \<notin> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close> have \<open>t @ [\<checkmark>(r)] \<notin> \<D> (P \<lbrakk>S\<rbrakk> Q)\<close>
      by (meson is_processT9)
    ultimately obtain t_P t_Q where \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close> \<open>t_P \<notin> \<D> P\<close> \<open>t_Q \<notin> \<D> Q\<close>
      \<open>(t @ [\<checkmark>(r)]) setinterleaves ((t_P, t_Q), range tick \<union> ev ` S)\<close>
      by (simp add: Sync_projs)
        (metis (no_types, lifting) append.right_neutral front_tickFree_Nil setinterleaving_sym)
    from this(1-4) SyncWithTick_imp_NTF[OF this(5)] show \<open>r \<in> ?rhs\<close>
      by simp (metis T_imp_front_tickFree front_tickFree_append_iff is_processT7 not_Cons_self2)
  qed
  moreover have \<open>finite \<dots>\<close>
  proof (rule finite_UN_I, safe)
    show \<open>finite {(t_P, t_Q). t setinterleaves ((t_P, t_Q), range tick \<union> ev ` S)}\<close>
      by (fact finite_interleaves)
  next
    from \<open>\<bbbF>\<^sub>\<checkmark>(P) \<or> \<bbbF>\<^sub>\<checkmark>(Q)\<close> finite_ticksD 
    show \<open>finite {r. t_P @ [\<checkmark>(r)] \<in> \<T> P \<and> t_P \<notin> \<D> P \<and>
                     t_Q @ [\<checkmark>(r)] \<in> \<T> Q \<and> t_Q \<notin> \<D> Q}\<close> for t_P t_Q by fastforce
  qed
  ultimately show \<open>finite {r. t @ [\<checkmark>(r)] \<in> \<T> (P \<lbrakk>S\<rbrakk> Q)}\<close> by (fact finite_subset)
qed

corollary \<open>\<bbbF>\<^sub>\<checkmark>(P) \<or> \<bbbF>\<^sub>\<checkmark>(Q) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(P ||  Q)\<close>
  and \<open>\<bbbF>\<^sub>\<checkmark>(P) \<or> \<bbbF>\<^sub>\<checkmark>(Q) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(P ||| Q)\<close>
  by (fact finite_ticks_Sync)+

(* 
lemma finite_ticks_Hiding [finite_ticks_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>(P \ S)\<close> if \<open>finite S\<close> and \<open>\<bbbF>\<^sub>\<checkmark>(P)\<close>
  \<comment> \<open>Probably complicated proof.\<close>
  oops
 *)


lemma finite_ticks_GlobalNdet [finite_ticks_simps] :
  \<open>finite A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(P a)) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(\<sqinter>a\<in>A. P a)\<close>
  \<comment>\<open>We can't expect \<^term>\<open>infinite A\<close> here, see @{thm finite_ticks_SKIPS_iff[no_vars]}.\<close>
  by (induct A rule: induct_subset_empty_single)
    (simp_all add: GlobalNdet_distrib_unit finite_ticks_Ndet finite_ticks_STOP)

lemma finite_ticks_GlobalDet [finite_ticks_simps] :
  \<open>finite A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(P a)) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(\<box>a\<in>A. P a)\<close>
  by (induct A rule: finite_induct)
    (simp_all add: GlobalDet_distrib_unit_bis finite_ticks_Det finite_ticks_STOP)

lemma \<open>L = [] \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(SEQ l\<in>@L. P l)\<close> by (simp add: finite_ticks_SKIP)

lemma finite_ticks_MultiSeq_nonempty [finite_ticks_simps] :
  \<open>L \<noteq> [] \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(P (last L)) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(SEQ l\<in>@L. P l)\<close>
  by (induct L rule: rev_induct) (simp_all add: finite_ticks_Seq)

lemma finite_ticks_MultiSync [finite_ticks_simps] :
  \<open>(\<And>m. m \<in># M \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(P m)) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk> m\<in>#M. P m)\<close>
  by (induct M rule: induct_subset_mset_empty_single)
    (simp_all add: finite_ticks_Sync finite_ticks_STOP)

corollary \<open>(\<And>m. m \<in># M \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(P m)) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(\<^bold>|\<^bold>|  m\<in>#M. P m)\<close>
  and \<open>(\<And>m. m \<in># M \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(P m)) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(\<^bold>|\<^bold>|\<^bold>| m\<in>#M. P m)\<close>
  by (fact finite_ticks_MultiSync)+


lemma finite_ticks_Mprefix_iff [finite_ticks_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>(\<box>a\<in>A \<rightarrow> P a) \<longleftrightarrow> (\<forall>a\<in>A. \<bbbF>\<^sub>\<checkmark>(P a))\<close>
proof (safe intro!: finite_ticksI)
  fix t a assume \<open>\<bbbF>\<^sub>\<checkmark>(\<box>a\<in>A \<rightarrow> P a)\<close> \<open>a \<in> A\<close> \<open>t \<in> \<T> (P a)\<close> \<open>t \<notin> \<D> (P a)\<close>
  have \<open>{r. t @ [\<checkmark>(r)] \<in> \<T> (P a)} = {r. (ev a # t) @ [\<checkmark>(r)] \<in> \<T> (\<box>a\<in>A \<rightarrow> P a)}\<close>
    by (auto simp add: \<open>a \<in> A\<close> T_Mprefix)
  also have \<open>finite \<dots>\<close>
    by (rule \<open>\<bbbF>\<^sub>\<checkmark>(\<box>a\<in>A \<rightarrow> P a)\<close>[THEN finite_ticksD])
      (simp add: D_Mprefix \<open>t \<notin> \<D> (P a)\<close>)
  finally show \<open>finite {r. t @ [\<checkmark>(r)] \<in> \<T> (P a)}\<close> .
next
  fix t assume \<open>\<forall>a\<in>A. \<bbbF>\<^sub>\<checkmark>(P a)\<close> \<open>t \<in> \<T> (\<box>a\<in>A \<rightarrow> P a)\<close> \<open>t \<notin> \<D> (\<box>a\<in>A \<rightarrow> P a)\<close>
  from \<open>t \<in> \<T> (\<box>a\<in>A \<rightarrow> P a)\<close> consider \<open>t = []\<close> | u a where \<open>a \<in> A\<close> \<open>t = ev a # u\<close>
    by (auto simp add: T_Mprefix)
  thus \<open>finite {r. t @ [\<checkmark>(r)] \<in> \<T> (\<box>a\<in>A \<rightarrow> P a)}\<close>
  proof cases
    show \<open>t = [] \<Longrightarrow> finite {r. t @ [\<checkmark>(r)] \<in> \<T> (\<box>a\<in>A \<rightarrow> P a)}\<close> by (simp add: T_Mprefix)
  next
    fix u a assume \<open>a \<in> A\<close> \<open>t = ev a # u\<close>
    hence \<open>{r. t @ [\<checkmark>(r)] \<in> \<T> (\<box>a\<in>A \<rightarrow> P a)} = {r. u @ [\<checkmark>(r)] \<in> \<T> (P a)}\<close>
      by (simp add: set_eq_iff T_Mprefix)
    also have \<open>finite \<dots>\<close>
      by (rule \<open>\<forall>a\<in>A. \<bbbF>\<^sub>\<checkmark>(P a)\<close>[THEN bspec, OF \<open>a \<in> A\<close>, THEN finite_ticksD])
        (use \<open>t \<notin> \<D> (\<box>a\<in>A \<rightarrow> P a)\<close> in \<open>simp add: \<open>t = ev a # u\<close> D_Mprefix \<open>a \<in> A\<close>\<close>)
    finally show \<open>finite {r. t @ [\<checkmark>(r)] \<in> \<T> (\<box>a\<in>A \<rightarrow> P a)}\<close> .
  qed
qed

lemma finite_ticks_Mndetprefix_iff [finite_ticks_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>(\<sqinter>a\<in>A \<rightarrow> P a) \<longleftrightarrow> (\<forall>a\<in>A. \<bbbF>\<^sub>\<checkmark>(P a))\<close>
proof -
  have \<open>\<bbbF>\<^sub>\<checkmark>(\<sqinter>a\<in>A \<rightarrow> P a) \<longleftrightarrow> \<bbbF>\<^sub>\<checkmark>(\<box>a\<in>A \<rightarrow> P a)\<close>
    by (simp add: finite_ticks_def Mndetprefix_projs Mprefix_projs)
  thus \<open>\<bbbF>\<^sub>\<checkmark>(\<sqinter>a\<in>A \<rightarrow> P a) \<longleftrightarrow> (\<forall>a\<in>A. \<bbbF>\<^sub>\<checkmark>(P a))\<close> by (simp add: finite_ticks_Mprefix_iff)
qed

lemma finite_ticks_write0_iff [finite_ticks_simps] : \<open>\<bbbF>\<^sub>\<checkmark>(a \<rightarrow> P) \<longleftrightarrow> \<bbbF>\<^sub>\<checkmark>(P)\<close>
  by (simp add: write0_def finite_ticks_Mprefix_iff)

lemma finite_ticks_write_iff [finite_ticks_simps] : \<open>\<bbbF>\<^sub>\<checkmark>(c\<^bold>!a \<rightarrow> P) \<longleftrightarrow> \<bbbF>\<^sub>\<checkmark>(P)\<close>
  by (simp add: write_def finite_ticks_Mprefix_iff)

lemma finite_ticks_read_iff :
  \<open>\<bbbF>\<^sub>\<checkmark>(c\<^bold>?a\<in>A \<rightarrow> P a) \<longleftrightarrow> (\<forall>b\<in>c ` A. \<bbbF>\<^sub>\<checkmark>(P (inv_into A c b)))\<close>
  by (simp add: read_def finite_ticks_Mprefix_iff)

lemma finite_ticks_inj_on_read_iff [finite_ticks_simps] :
  \<open>inj_on c A \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(c\<^bold>?a\<in>A \<rightarrow> P a) \<longleftrightarrow> (\<forall>a\<in>A. \<bbbF>\<^sub>\<checkmark>(P a))\<close>
  by (simp add: read_def finite_ticks_Mprefix_iff)

lemma finite_ticks_ndet_write_iff :
  \<open>\<bbbF>\<^sub>\<checkmark>(c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) \<longleftrightarrow> (\<forall>b\<in>c ` A. \<bbbF>\<^sub>\<checkmark>(P (inv_into A c b)))\<close>
  by (simp add: ndet_write_def finite_ticks_Mndetprefix_iff)

lemma finite_ticks_inj_on_ndet_write_iff [finite_ticks_simps] :
  \<open>inj_on c A \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>(c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) \<longleftrightarrow> (\<forall>a\<in>A. \<bbbF>\<^sub>\<checkmark>(P a))\<close>
  by (simp add: ndet_write_def finite_ticks_Mndetprefix_iff)



subsection \<open>Laws of \<^term>\<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f)\<close>\<close>

lemma finite_ticks_fun_Det [finite_ticks_fun_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(g) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. f x \<box> g x)\<close>
  by (simp add: finite_ticks_Det finite_ticks_fun_def)

lemma finite_ticks_fun_Ndet [finite_ticks_fun_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(g) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. f x \<sqinter> g x)\<close>
  by (simp add: finite_ticks_Ndet finite_ticks_fun_def)

lemma finite_ticks_fun_Sliding [finite_ticks_fun_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(g) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. f x \<rhd> g x)\<close>
  by (simp add: finite_ticks_Sliding finite_ticks_fun_def)

lemma finite_ticks_fun_Interrupt [finite_ticks_fun_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(g) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. f x \<triangle> g x)\<close>
  by (simp add: finite_ticks_Interrupt finite_ticks_fun_def)

lemma finite_ticks_fun_Throw [finite_ticks_fun_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f) \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(g a)) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. f x \<Theta> a\<in>A. g a x)\<close>
  by (simp add: finite_ticks_Throw finite_ticks_fun_def)

lemma finite_ticks_fun_Renaming [finite_ticks_fun_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(P) \<Longrightarrow> finitary f \<Longrightarrow> finitary g \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. Renaming (P x) f g)\<close>
  by (simp add: finite_ticks_Renaming finite_ticks_fun_def)

lemma finite_ticks_fun_RenamingF [finite_ticks_fun_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(P) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. (P x) \<lbrakk>a := b\<rbrakk> \<lbrakk>c := d\<rbrakk>)\<close>
  by (simp add: finite_ticks_fun_Renaming)

lemma finite_ticks_fun_Seq [finite_ticks_fun_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(g) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. f x \<^bold>; g x)\<close>
  by (simp add: finite_ticks_Seq finite_ticks_fun_def)

lemma finite_ticks_fun_Sync [finite_ticks_fun_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(g) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. f x \<lbrakk>S\<rbrakk> g x)\<close>
  by (simp add: finite_ticks_Sync finite_ticks_fun_def)

corollary \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(g) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. f x ||  g x)\<close>
  and \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(g) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. f x ||| g x)\<close>
  by (fact finite_ticks_fun_Sync)+


(* lemma finite_ticks_fun_Hiding [finite_ticks_fun_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. f x \ S)\<close>
  by (simp add: finite_ticks_Hiding finite_ticks_fun_def)
 *)


lemma finite_ticks_fun_GlobalNdet [finite_ticks_fun_simps] :
  \<open>finite A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f a)) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. \<sqinter>a\<in>A. f a x)\<close>
  by (simp add: finite_ticks_GlobalNdet finite_ticks_fun_def)

lemma finite_ticks_fun_GlobalDet :
  \<open>finite A \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f a)) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. \<box>a\<in>A. f a x)\<close>
  by (simp add: finite_ticks_GlobalDet finite_ticks_fun_def)

lemma finite_ticks_fun_MultiSeq [finite_ticks_fun_simps] :
  \<open>L = [] \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. SEQ l\<in>@L. f l x)\<close>
  \<open>L \<noteq> [] \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f (last L)) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. SEQ l\<in>@L. f l x)\<close>
  by (simp_all add: finite_ticks_MultiSeq_nonempty finite_ticks_fun_def finite_ticks_SKIP)

lemma finite_ticks_fun_MultiSync [finite_ticks_fun_simps] :
  \<open>(\<And>m. m \<in># M \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f m)) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. \<^bold>\<lbrakk>S\<^bold>\<rbrakk> m\<in>#M. f m x)\<close>
  by (simp add: finite_ticks_MultiSync finite_ticks_fun_def)

corollary \<open>(\<And>m. m \<in># M \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f m)) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. \<^bold>|\<^bold>|  m\<in>#M. f m x)\<close>
  and \<open>(\<And>m. m \<in># M \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f m)) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. \<^bold>|\<^bold>|\<^bold>| m\<in>#M. f m x)\<close>
  by (fact finite_ticks_fun_MultiSync)+


lemma finite_ticks_fun_Mprefix_iff :
  \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. \<box>a\<in>A \<rightarrow> f a x) \<longleftrightarrow> (\<forall>a \<in> A. \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f a))\<close>
  by (auto simp add: finite_ticks_fun_def finite_ticks_Mprefix_iff)

lemma finite_ticks_fun_Mprefix [finite_ticks_fun_simps] :
  \<open>(\<And>a. a \<in> A \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f a)) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. \<box>a\<in>A \<rightarrow> f a x)\<close>
  by (simp add: finite_ticks_fun_Mprefix_iff)

lemma finite_ticks_fun_Mndetprefix_iff [finite_ticks_fun_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. \<sqinter>a\<in>A \<rightarrow> f a x) \<longleftrightarrow> (\<forall>a \<in> A. \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f a))\<close>
  by (auto simp add: finite_ticks_fun_def finite_ticks_Mndetprefix_iff)

lemma finite_ticks_fun_Mndetprefix [finite_ticks_fun_simps] :
  \<open>(\<And>a. a \<in> A \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f a)) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. \<sqinter>a\<in>A \<rightarrow> f a x)\<close>
  by (simp add: finite_ticks_fun_Mndetprefix_iff)

lemma finite_ticks_fun_write0_iff [finite_ticks_fun_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. a \<rightarrow> f x) \<longleftrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f)\<close>
  by (simp add: write0_def finite_ticks_fun_Mprefix_iff)

lemma finite_ticks_fun_write_iff [finite_ticks_fun_simps] :
  \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. c\<^bold>!a \<rightarrow> f x) \<longleftrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f)\<close>
  by (simp add: write_def finite_ticks_fun_Mprefix_iff)

lemma finite_ticks_fun_read_iff :
  \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. c\<^bold>?a\<in>A \<rightarrow> f a x) \<longleftrightarrow> (\<forall>b\<in>c ` A. \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f (inv_into A c b)))\<close>
  by (simp add: read_def finite_ticks_fun_Mprefix_iff)

lemma finite_ticks_fun_read [finite_ticks_fun_simps] :
  \<open>(\<And>a. a \<in> A \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. f a x)) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. c\<^bold>?a\<in>A \<rightarrow> f a x)\<close>
  by (simp add: read_def o_def inv_into_into finite_ticks_fun_Mprefix_iff)

lemma finite_ticks_fun_ndet_write_iff :
  \<open>\<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. c\<^bold>!\<^bold>!a\<in>A \<rightarrow> f a x) \<longleftrightarrow> (\<forall>b\<in>c ` A. \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(f (inv_into A c b)))\<close>
  by (simp add: ndet_write_def finite_ticks_fun_Mndetprefix_iff)

lemma finite_ticks_fun_ndet_write [finite_ticks_fun_simps] :
  \<open>(\<And>a. a \<in> A \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. f a x)) \<Longrightarrow> \<bbbF>\<^sub>\<checkmark>\<^sub>\<Rightarrow>(\<lambda>x. c\<^bold>!\<^bold>!a\<in>A \<rightarrow> f a x)\<close>
  by (simp add: ndet_write_def o_def inv_into_into finite_ticks_fun_Mndetprefix_iff)



(*<*)
end
  (*>*)