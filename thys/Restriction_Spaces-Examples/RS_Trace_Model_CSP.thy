(***********************************************************************************
 * Copyright (c) 2025 Université Paris-Saclay
 *
 * Author: Benoît Ballenghien, Université Paris-Saclay,
           CNRS, ENS Paris-Saclay, LMF
 * Author: Benjamin Puyobro, Université Paris-Saclay,
           IRT SystemX, CNRS, ENS Paris-Saclay, LMF
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


section \<open>Trace Model of CSP\<close>

(*<*)
theory RS_Trace_Model_CSP
  imports Restriction_Spaces "HOL-Library.Prefix_Order"
begin 
  (*>*)

text \<open>
In the AFP one can already find \<^verbatim>\<open>HOL-CSP\<close>, a shallow embedding of the failure-divergence
model of denotational semantics proposed by Hoare, Roscoe and Brookes in the eighties.
Here, we simplify the example by restraining ourselves to a trace model.\<close>

subsection \<open>Prerequisites\<close>

datatype 'a event = ev (of_ev : 'a) | tick (\<open>\<checkmark>\<close>)

type_synonym 'a trace = \<open>'a event list\<close>


definition tickFree :: \<open>'a trace \<Rightarrow> bool\<close> (\<open>tF\<close>)
  where \<open>tickFree t \<equiv> \<checkmark> \<notin> set t\<close>

definition front_tickFree :: \<open>'a trace \<Rightarrow> bool\<close> (\<open>ftF\<close>)
  where \<open>front_tickFree s \<equiv> s = [] \<or> tickFree (tl (rev s))\<close>


lemma tickFree_Nil        [simp] : \<open>tF []\<close>
  and tickFree_Cons_iff   [simp] : \<open>tF (a # t) \<longleftrightarrow> a \<noteq> \<checkmark> \<and> tF t\<close>
  and tickFree_append_iff [simp] : \<open>tF (s @ t) \<longleftrightarrow> tF s    \<and> tF t\<close>
  and tickFree_rev_iff    [simp] : \<open>tF (rev t) \<longleftrightarrow> tF t\<close>
  and non_tickFree_tick   [simp] : \<open>\<not> tF [\<checkmark>]\<close>
  by (auto simp add: tickFree_def)

lemma tickFree_iff_is_map_ev : \<open>tF t \<longleftrightarrow> (\<exists>u. t = map ev u)\<close>
  by (metis event.collapse event.distinct(1) ex_map_conv tickFree_def)

lemma front_tickFree_Nil   [simp] : \<open>ftF []\<close>
  and front_tickFree_single[simp] : \<open>ftF [a]\<close>
  by (simp_all add: front_tickFree_def)


lemma tickFree_tl : \<open>tF s \<Longrightarrow> tF (tl s)\<close>
  by (cases s) simp_all

lemma non_tickFree_imp_not_Nil: \<open>\<not> tF s \<Longrightarrow> s \<noteq> []\<close>
  using tickFree_Nil by blast

lemma tickFree_butlast: \<open>tF s \<longleftrightarrow> tF (butlast s) \<and> (s \<noteq> [] \<longrightarrow> last s \<noteq> \<checkmark>)\<close>
  by (induct s) simp_all

lemma front_tickFree_iff_tickFree_butlast: \<open>ftF s \<longleftrightarrow> tF (butlast s)\<close>
  by (induct s) (auto simp add: front_tickFree_def)

lemma front_tickFree_Cons_iff: \<open>ftF (a # s) \<longleftrightarrow> s = [] \<or> a \<noteq> \<checkmark> \<and> ftF s\<close>
  by (simp add: front_tickFree_iff_tickFree_butlast)

lemma front_tickFree_append_iff:
  \<open>ftF (s @ t) \<longleftrightarrow> (if t = [] then ftF s else tF s \<and> ftF t)\<close>
  by (simp add: butlast_append front_tickFree_iff_tickFree_butlast)

lemma tickFree_imp_front_tickFree [simp] : \<open>tF s \<Longrightarrow> ftF s\<close>
  by (simp add: front_tickFree_def tickFree_tl)

lemma front_tickFree_charn: \<open>ftF s \<longleftrightarrow> s = [] \<or> (\<exists>a t. s = t @ [a] \<and> tF t)\<close>
  by (cases s rule: rev_cases) (simp_all add: front_tickFree_def)


lemma nonTickFree_n_frontTickFree: \<open>\<not> tF s \<Longrightarrow> ftF s \<Longrightarrow> \<exists>t r. s = t @ [\<checkmark>]\<close>
  by (metis front_tickFree_charn tickFree_Cons_iff
      tickFree_Nil tickFree_append_iff)

lemma front_tickFree_dw_closed : \<open>ftF (s @ t) \<Longrightarrow> ftF s\<close>
  by (metis front_tickFree_append_iff tickFree_imp_front_tickFree)

lemma front_tickFree_append: \<open>tF s \<Longrightarrow> ftF t \<Longrightarrow> ftF (s @ t)\<close>
  by (simp add: front_tickFree_append_iff)

lemma tickFree_imp_front_tickFree_snoc: \<open>tF s \<Longrightarrow> ftF (s @ [a])\<close>
  by (simp add: front_tickFree_append)

lemma front_tickFree_nonempty_append_imp: \<open>ftF (t @ r) \<Longrightarrow> r \<noteq> [] \<Longrightarrow> tF t \<and> ftF r\<close>
  by (simp add: front_tickFree_append_iff)

lemma tickFree_map_ev [simp] : \<open>tF (map ev t)\<close>
  by (induct t) simp_all

lemma tickFree_map_ev_comp [simp] : \<open>tF (map (ev \<circ> f) t)\<close>
  by (metis list.map_comp tickFree_map_ev)

lemma front_tickFree_map_map_event_iff :
  \<open>ftF (map (map_event f) t) \<longleftrightarrow> ftF t\<close>
  by (induct t) (simp_all add: front_tickFree_Cons_iff)




definition is_process :: \<open>'a trace set \<Rightarrow> bool\<close>
  where \<open>is_process T \<equiv> [] \<in> T \<and> (\<forall>t. t \<in> T \<longrightarrow> ftF t) \<and> (\<forall>t u. t @ u \<in> T \<longrightarrow> t \<in> T)\<close>

typedef 'a process = \<open>{T :: 'a trace set. is_process T}\<close>
  morphisms Traces to_process
proof (rule exI)
  show \<open>{[]} \<in> {T. is_process T}\<close>
    by (simp add: is_process_def front_tickFree_def)
qed

setup_lifting type_definition_process


notation Traces (\<open>\<T>\<close>)

lemma is_process_inv :
  \<open>[] \<in> \<T> P \<and> (\<forall>t. t \<in> \<T> P \<longrightarrow> ftF t) \<and> (\<forall>t u. t @ u \<in> \<T> P \<longrightarrow> t \<in> \<T> P)\<close>
  by (metis is_process_def mem_Collect_eq to_process_cases to_process_inverse)

lemma Nil_elem_T       : \<open>[] \<in> \<T> P\<close>
  and front_tickFree_T : \<open>t \<in> \<T> P \<Longrightarrow> ftF t\<close>
  and T_dw_closed      : \<open>t @ u \<in> \<T> P \<Longrightarrow> t \<in> \<T> P\<close>
  by (simp_all add: is_process_inv)


lemma process_eq_spec : \<open>P = Q \<longleftrightarrow> \<T> P = \<T> Q\<close>
  by transfer simp



subsection \<open>First Processes\<close>

lift_definition BOT :: \<open>'a process\<close> is \<open>{t. ftF t}\<close>
  by (auto simp add: is_process_def front_tickFree_append_iff)

lemma T_BOT : \<open>\<T> BOT = {t. ftF t}\<close>
  by (simp add: BOT.rep_eq)


lift_definition SKIP :: \<open>'a process\<close> is \<open>{[], [\<checkmark>]}\<close>
  by (simp add: is_process_def append_eq_Cons_conv)

lemma T_SKIP : \<open>\<T> SKIP = {[], [\<checkmark>]}\<close>
  by (simp add: SKIP.rep_eq)


lift_definition STOP :: \<open>'a process\<close> is \<open>{[]}\<close>
  by (simp add: is_process_def)

lemma T_STOP : \<open>\<T> STOP = {[]}\<close>
  by (simp add: STOP.rep_eq)


lift_definition Sup_processes ::
  \<open>(nat \<Rightarrow> 'a process) \<Rightarrow> 'a process\<close> is \<open>\<lambda>\<sigma>. \<Inter>i. \<T> (\<sigma> i)\<close>
proof -
  show \<open>is_process (\<Inter>i. \<T> (\<sigma> i))\<close> for \<sigma> :: \<open>nat \<Rightarrow> 'a process\<close>
  proof (unfold is_process_def, intro conjI allI impI)
    show \<open>[] \<in> (\<Inter>i. \<T> (\<sigma> i))\<close> by (simp add: Nil_elem_T)
  next
    show \<open>t \<in> (\<Inter>i. \<T> (\<sigma> i)) \<Longrightarrow> ftF t\<close> for t
      by (auto intro: front_tickFree_T)
  next
    show \<open>t @ u \<in> (\<Inter>i. \<T> (\<sigma> i)) \<Longrightarrow> t \<in> (\<Inter>i. \<T> (\<sigma> i))\<close> for t u
      by (auto intro: T_dw_closed)
  qed
qed

lemma T_Sup_processes : \<open>\<T> (Sup_processes \<sigma>) = (\<Inter>i. \<T> (\<sigma> i))\<close>
  by (simp add: Sup_processes.rep_eq)



subsection \<open>Instantiations\<close>

instantiation process :: (type) order
begin

definition less_eq_process :: \<open>'a process \<Rightarrow> 'a process \<Rightarrow> bool\<close>
  where \<open>P \<le> Q \<equiv> \<T> Q \<subseteq> \<T> P\<close>

definition less_process :: \<open>'a process \<Rightarrow> 'a process \<Rightarrow> bool\<close>
  where \<open>P < Q \<equiv> \<T> Q \<subset> \<T> P\<close>

instance
  by intro_classes
    (auto simp add: less_eq_process_def less_process_def process_eq_spec)

end


instantiation process :: (type) order_restriction_space
begin

lift_definition restriction_process :: \<open>'a process \<Rightarrow> nat \<Rightarrow> 'a process\<close>
  is \<open>\<lambda>P n. \<T> P \<union> {t @ u |t u. t \<in> \<T> P \<and> length t = n \<and> tF t \<and> ftF u}\<close>
proof -
  show \<open>?thesis P n\<close> (is \<open>is_process ?t\<close>) for P n
  proof (unfold is_process_def, intro conjI allI impI)
    show \<open>[] \<in> ?t\<close> by (simp add: Nil_elem_T)
  next
    show \<open>t \<in> ?t \<Longrightarrow> ftF t\<close> for t
      by (auto simp add: front_tickFree_append_iff front_tickFree_T)
  next
    fix t u assume \<open>t @ u \<in> ?t\<close>
    then consider \<open>t @ u \<in> \<T> P\<close>
      | (@) t' u' where \<open>t @ u = t' @ u'\<close> \<open>t' \<in> \<T> P\<close>
        \<open>length t' = n\<close> \<open>tF t'\<close> \<open>ftF u'\<close> by blast
    thus \<open>t \<in> ?t\<close>
    proof cases
      from T_dw_closed show \<open>t @ u \<in> \<T> P \<Longrightarrow> t \<in> ?t\<close> by blast
    next
      case @
      show \<open>t \<in> ?t\<close>
      proof (cases \<open>length t \<le> length t'\<close>)
        assume \<open>length t \<le> length t'\<close>
        with "@"(1) obtain t'' where \<open>t' = t @ t''\<close>
          by (metis append_eq_append_conv_if append_eq_conv_conj)
        with "@"(2) T_dw_closed show \<open>t \<in> ?t\<close> by blast
      next
        assume \<open>\<not> length t \<le> length t'\<close>
        hence \<open>length t' \<le> length t\<close> by simp
        with "@"(1,4,5) \<open>\<not> length t \<le> length t'\<close>
        obtain t'' where \<open>t = t' @ t''\<close> \<open>ftF t''\<close>
          by (metis append_eq_conv_conj drop_eq_Nil front_tickFree_append
              front_tickFree_dw_closed front_tickFree_nonempty_append_imp
              take_all_iff take_append)
        with "@"(2,3,4) show \<open>t \<in> ?t\<close> by blast
      qed
    qed
  qed
qed

lemma T_restriction_process :
  \<open>\<T> (P \<down> n) = \<T> P \<union> {t @ u |t u. t \<in> \<T> P \<and> length t = n \<and> tF t \<and> ftF u}\<close>
  by (simp add: restriction_process.rep_eq)


lemma restriction_process_0 [simp] : \<open>P \<down> 0 = BOT\<close>
  by transfer (auto simp add: front_tickFree_T Nil_elem_T)

lemma T_restriction_processE :
  \<open>t \<in> \<T> (P \<down> n) \<Longrightarrow>
   (t \<in> \<T> P \<Longrightarrow> length t \<le> n \<Longrightarrow> thesis) \<Longrightarrow>
   (\<And>u v. t = u @ v \<Longrightarrow> u \<in> \<T> P \<Longrightarrow> length u = n \<Longrightarrow> tF u \<Longrightarrow> ftF v \<Longrightarrow> thesis) \<Longrightarrow>
   thesis\<close>
  by (simp add: T_restriction_process)
    (metis (no_types) T_dw_closed append_take_drop_id drop_eq_Nil
      front_tickFree_T front_tickFree_nonempty_append_imp length_take min_def)


instance
proof intro_classes
  show \<open>P \<down> 0 \<le> Q \<down> 0\<close> for P Q :: \<open>'a process\<close> by simp
next
  show \<open>P \<down> n \<down> m = P \<down> min n m\<close> for P :: \<open>'a process\<close> and n m
  proof (subst process_eq_spec, intro subset_antisym subsetI)
    show \<open>t \<in> \<T> (P \<down> n \<down> m) \<Longrightarrow> t \<in> \<T> (P \<down> min n m)\<close> for t
      by (elim T_restriction_processE)
        (auto simp add: T_restriction_process intro: front_tickFree_append)
  next
    show \<open>t \<in> \<T> (P \<down> min n m) \<Longrightarrow> t \<in> \<T> (P \<down> n \<down> m)\<close> for t
      by (elim T_restriction_processE)
        (auto simp add: T_restriction_process min_def split: if_split_asm)
  qed
next
  show \<open>P \<le> Q \<Longrightarrow> P \<down> n \<le> Q \<down> n\<close> for P Q :: \<open>'a process\<close> and n
    by (auto simp add: less_eq_process_def T_restriction_process)
next
  fix P Q :: \<open>'a process\<close> assume \<open>\<not> P \<le> Q\<close>
  then obtain t where \<open>t \<in> \<T> Q\<close> \<open>t \<notin> \<T> P\<close>
    unfolding less_eq_process_def by blast
  hence \<open>t \<in> \<T> (Q \<down> Suc (length t)) \<and> t \<notin> \<T> (P \<down> Suc (length t))\<close>
    by (auto simp add: T_restriction_process) 
  hence \<open>\<not> P \<down> Suc (length t) \<le> Q \<down> Suc (length t)\<close>
    unfolding less_eq_process_def by blast
  thus \<open>\<exists>n. \<not> P \<down> n \<le> Q \<down> n\<close> ..
qed


text \<open>Of course, we recover the structure of \<^class>\<open>restriction_space\<close>.\<close>

lemma \<open>OFCLASS ('a process, restriction_space_class)\<close>
  by intro_classes

end


lemma restricted_Sup_processes_is :
  \<open>(\<lambda>n. Sup_processes \<sigma> \<down> n) = \<sigma>\<close> if \<open>restriction_chain \<sigma>\<close>
proof (subst (2) restricted_restriction_chain_is
    [OF \<open>restriction_chain \<sigma>\<close>, symmetric], rule ext)
  fix n
  have \<open>length t \<le> n \<Longrightarrow> t \<in> \<T> (\<sigma> n) \<longleftrightarrow> (\<forall>i. t \<in> \<T> (\<sigma> i))\<close> for t n
  proof safe
    show \<open>t \<in> \<T> (\<sigma> i)\<close> if \<open>length t \<le> n\<close> \<open>t \<in> \<T> (\<sigma> n)\<close> for i
    proof (cases \<open>i \<le> n\<close>)
      from restriction_chain_def_ter[THEN iffD1, OF \<open>restriction_chain \<sigma>\<close>]
      show \<open>i \<le> n \<Longrightarrow> t \<in> \<T> (\<sigma> i)\<close>
        by (metis (lifting) \<open>t \<in> \<T> (\<sigma> n)\<close> T_restriction_process Un_iff)
    next
      from \<open>length t \<le> n\<close> \<open>t \<in> \<T> (\<sigma> n)\<close> show \<open>\<not> i \<le> n \<Longrightarrow> t \<in> \<T> (\<sigma> i)\<close>
        by (induct n, simp_all add: Nil_elem_T)
          (metis (no_types) T_restriction_processE
            append_eq_conv_conj linorder_linear take_all_iff
            restriction_chain_def_ter[THEN iffD1, OF \<open>restriction_chain \<sigma>\<close>])
    qed
  next
    show \<open>\<forall>i. t \<in> \<T> (\<sigma> i) \<Longrightarrow> t \<in> \<T> (\<sigma> n)\<close> by simp
  qed
  hence * : \<open>length t \<le> n \<Longrightarrow> t \<in> \<T> (\<sigma> n) \<longleftrightarrow> t \<in> \<T> (Sup_processes \<sigma>)\<close> for t n
    by (simp add: T_Sup_processes)

  show \<open>Sup_processes \<sigma> \<down> n = \<sigma> n \<down> n\<close> for n
  proof (subst process_eq_spec, intro subset_antisym subsetI)
    show \<open>t \<in> \<T> (Sup_processes \<sigma> \<down> n) \<Longrightarrow> t \<in> \<T> (\<sigma> n \<down> n)\<close> for t
    proof (elim T_restriction_processE)
      show \<open>t \<in> \<T> (Sup_processes \<sigma>) \<Longrightarrow> length t \<le> n \<Longrightarrow> t \<in> \<T> (\<sigma> n \<down> n)\<close>
        by (simp add: "*" T_restriction_process)
    next
      show \<open>\<lbrakk>t = u @ v; u \<in> \<T> (Sup_processes \<sigma>); length u = n; tF u; ftF v\<rbrakk>
            \<Longrightarrow> t \<in> \<T> (\<sigma> n \<down> n)\<close> for u v
        by (auto simp add: "*" T_restriction_process)
    qed
  next
    from "*" show \<open>t \<in> \<T> (\<sigma> n \<down> n) \<Longrightarrow> t \<in> \<T> (Sup_processes \<sigma> \<down> n)\<close> for t
      by (elim T_restriction_processE)
        (auto simp add: T_restriction_process)
  qed
qed


instance process :: (type) complete_restriction_space 
proof intro_classes
  show \<open>restriction_convergent \<sigma>\<close> if \<open>restriction_chain \<sigma>\<close>
    for \<sigma> :: \<open>nat \<Rightarrow> 'a process\<close>
  proof (rule restriction_convergentI)
    have \<open>\<sigma> = (\<lambda>n. Sup_processes \<sigma> \<down> n)\<close>
      by (simp add: restricted_Sup_processes_is \<open>restriction_chain \<sigma>\<close>)
    moreover have \<open>(\<lambda>n. Sup_processes \<sigma> \<down> n) \<midarrow>\<down>\<rightarrow> Sup_processes \<sigma>\<close>
      by (fact restriction_tendsto_restrictions)
    ultimately show \<open>\<sigma> \<midarrow>\<down>\<rightarrow> Sup_processes \<sigma>\<close> by simp
  qed
qed



subsection \<open>Operators\<close>

lift_definition Choice :: \<open>'a process \<Rightarrow> 'a process \<Rightarrow> 'a process\<close> (infixl \<open>\<box>\<close> 82)
  is \<open>\<lambda>P Q. \<T> P \<union> \<T> Q\<close>
  by (auto simp add: is_process_def Nil_elem_T front_tickFree_T intro: T_dw_closed)

lemma T_Choice : \<open>\<T> (P \<box> Q) = \<T> P \<union> \<T> Q\<close>
  by (simp add: Choice.rep_eq)


lift_definition GlobalChoice :: \<open>['b set, 'b \<Rightarrow> 'a process] \<Rightarrow> 'a process\<close>
  is \<open>\<lambda>A P. if A = {} then {[]} else \<Union>a\<in>A. \<T> (P a)\<close>
  by (auto simp add: is_process_def Nil_elem_T front_tickFree_T intro: T_dw_closed)

syntax "_GlobalChoice" :: \<open>[pttrn, 'b set, 'a process] \<Rightarrow> 'a process\<close>
  (\<open>(3\<box>((_)/\<in>(_))./ (_))\<close> [78,78,77] 77)
syntax_consts "_GlobalChoice" \<rightleftharpoons> GlobalChoice
translations  "\<box> a \<in> A. P" \<rightleftharpoons> "CONST GlobalChoice A (\<lambda>a. P)"

lemma T_GlobalChoice : \<open>\<T> (\<box>a \<in> A. P a) = (if A = {} then {[]} else \<Union>a\<in>A. \<T> (P a))\<close>
  by (simp add: GlobalChoice.rep_eq)


lift_definition Seq :: \<open>'a process \<Rightarrow> 'a process \<Rightarrow> 'a process\<close> (infixl \<open>\<^bold>;\<close> 74)
  is \<open>\<lambda>P Q. {t \<in> \<T> P. tF t} \<union> {t @ u |t u. t @ [\<checkmark>] \<in> \<T> P \<and> u \<in> \<T> Q}\<close>
  by (auto simp add: is_process_def Nil_elem_T append_eq_append_conv2 intro: T_dw_closed)
    (metis front_tickFree_T front_tickFree_append_iff
      front_tickFree_dw_closed not_Cons_self,
      meson front_tickFree_append_iff is_process_inv snoc_eq_iff_butlast)

lemma T_Seq : \<open>\<T> (P \<^bold>; Q) = {t \<in> \<T> P. tF t} \<union> {t @ u |t u. t @ [\<checkmark>] \<in> \<T> P \<and> u \<in> \<T> Q}\<close>
  by (simp add: Seq.rep_eq)


lift_definition Renaming :: \<open>['a process, 'a \<Rightarrow> 'b] \<Rightarrow> 'b process\<close>
  is \<open>\<lambda>P f. {map (map_event f) u |u. u \<in> \<T> P}\<close>
  by (auto simp add: is_process_def Nil_elem_T front_tickFree_map_map_event_iff
      front_tickFree_T append_eq_map_conv intro: T_dw_closed)

lemma T_Renaming : \<open>\<T> (Renaming P f) = {map (map_event f) u |u. u \<in> \<T> P}\<close>
  by (simp add: Renaming.rep_eq)


lift_definition Mprefix :: \<open>['a set, 'a \<Rightarrow> 'a process] \<Rightarrow> 'a process\<close>
  is \<open>\<lambda>A P. insert [] {ev a # t |a t. a \<in> A \<and> t \<in> \<T> (P a)}\<close>
  by (auto simp add: is_process_def front_tickFree_Cons_iff
      front_tickFree_T append_eq_Cons_conv intro: T_dw_closed)

syntax "_Mprefix" :: \<open>[pttrn, 'a set, 'a process] \<Rightarrow> 'a process\<close>	
  (\<open>(3\<box>((_)/\<in>(_))/ \<rightarrow> (_))\<close> [78,78,77] 77)
syntax_consts "_Mprefix" \<rightleftharpoons> Mprefix
translations "\<box>a\<in>A \<rightarrow> P" \<rightleftharpoons> "CONST Mprefix A (\<lambda>a. P)"

lemma T_Mprefix : \<open>\<T> (\<box>a \<in> A \<rightarrow> P a) = insert [] {ev a # t |a t. a \<in> A \<and> t \<in> \<T> (P a)}\<close>
  by (simp add: Mprefix.rep_eq)






fun setinterleaving :: \<open>'a trace \<times> 'a set \<times> 'a trace \<Rightarrow> 'a trace set\<close>
  where Nil_setinterleaving_Nil : \<open>setinterleaving ([], A, []) = {[]}\<close>

|     ev_setinterleaving_Nil :
  \<open>setinterleaving (ev a # u, A, []) =
         (if a \<in> A then {} else {ev a # t| t. t \<in> setinterleaving (u, A, [])})\<close>
|     tick_setinterleaving_Nil : \<open>setinterleaving (\<checkmark> # u, A, []) = {}\<close>

|     Nil_setinterleaving_ev :
  \<open>setinterleaving ([], A, ev b # v) =
         (if b \<in> A then {} else {ev b # t| t. t \<in> setinterleaving ([], A, v)})\<close>
|     Nil_setinterleaving_tick  : \<open>setinterleaving ([], A, \<checkmark> # v) = {}\<close>

|     ev_setinterleaving_ev : 
  \<open>setinterleaving (ev a # u, A, ev b # v) =
         (  if a \<in> A
          then   if b \<in> A 
                then   if a = b
                     then {ev a # t |t. t \<in> setinterleaving (u, A, v)}
                     else {}
                else {ev b # t |t. t \<in> setinterleaving (ev a # u, A, v)}
           else   if b \<in> A then {ev a # t |t. t \<in> setinterleaving (u, A, ev b # v)}
                else {ev a # t |t. t \<in> setinterleaving (u, A, ev b # v)} \<union>
                     {ev b # t |t. t \<in> setinterleaving (ev a # u, A, v)})\<close>
|     ev_setinterleaving_tick :
  \<open>setinterleaving (ev a # u, A, \<checkmark> # v) =
         (if a \<in> A then {} else {ev a # t |t. t \<in> setinterleaving (u, A, \<checkmark> # v)})\<close>
|     tick_setinterleaving_ev :
  \<open>setinterleaving (\<checkmark> # u, A, ev b # v) =
         (if b \<in> A then {} else {ev b # t |t. t \<in> setinterleaving (\<checkmark> # u, A, v)})\<close>
|     tick_setinterleaving_tick :
  \<open>setinterleaving (\<checkmark> # u, A, \<checkmark> # v) = {\<checkmark> # t |t. t \<in> setinterleaving (u, A, v)}\<close>


lemmas setinterleaving_induct
  [case_names Nil_setinterleaving_Nil ev_setinterleaving_Nil tick_setinterleaving_Nil
    Nil_setinterleaving_ev Nil_setinterleaving_tick ev_setinterleaving_ev
    ev_setinterleaving_tick tick_setinterleaving_ev tick_setinterleaving_tick] =
  setinterleaving.induct



lemma Cons_setinterleaving_Nil :
  \<open>setinterleaving (e # u, A, []) =
   (case e of ev a \<Rightarrow> (  if a \<in> A then {}
                       else {ev a # t |t. t \<in> setinterleaving (u, A, [])})
            | \<checkmark> \<Rightarrow> {})\<close>
  by (cases e) simp_all

lemma Nil_setinterleaving_Cons :
  \<open>setinterleaving ([], A, e # v) =
   (case e of ev a \<Rightarrow> (  if a \<in> A then {}
                       else {ev a # t |t. t \<in> setinterleaving ([], A, v)})
            | \<checkmark> \<Rightarrow> {})\<close>
  by (cases e) simp_all

lemma Cons_setinterleaving_Cons :
  \<open>setinterleaving (e # u, A, f # v) =
   (case e of ev a \<Rightarrow>
    (case f of ev b \<Rightarrow> 
       if a \<in> A
     then   if b \<in> A 
           then   if a = b
                then {ev a # t |t. t \<in> setinterleaving (u, A, v)}
                else {}
           else {ev b # t |t. t \<in> setinterleaving (ev a # u, A, v)}
      else   if b \<in> A then {ev a # t |t. t \<in> setinterleaving (u, A, ev b # v)}
           else {ev a # t |t. t \<in> setinterleaving (u, A, ev b # v)} \<union>
                {ev b # t |t. t \<in> setinterleaving (ev a # u, A, v)}
             | \<checkmark> \<Rightarrow>   if a \<in> A then {}
                    else {ev a # t |t. t \<in> setinterleaving (u, A, \<checkmark> # v)})
            | \<checkmark> \<Rightarrow>
    (case f of ev b \<Rightarrow>   if b \<in> A then {}
                       else {ev b # t| t. t \<in> setinterleaving (\<checkmark> # u, A, v)}
             | \<checkmark> \<Rightarrow> {\<checkmark> # t |t. t \<in> setinterleaving (u, A, v)}))\<close>
  by (cases e; cases f) simp_all


lemmas setinterleaving_simps =
  Cons_setinterleaving_Nil Nil_setinterleaving_Cons Cons_setinterleaving_Cons 



abbreviation setinterleaves ::
  \<open>['a trace, 'a trace, 'a trace, 'a set] \<Rightarrow> bool\<close>
  (\<open>(_ /(setinterleaves)/ '(()'(_, _')(), _'))\<close> [63,0,0,0] 64)
  where \<open>t setinterleaves ((u, v), A) \<equiv> t \<in> setinterleaving (u, A, v)\<close>




lemma tickFree_setinterleaves_iff :
  \<open>t setinterleaves ((u, v), A) \<Longrightarrow> tF t \<longleftrightarrow> tF u \<and> tF v\<close>
  by (induct \<open>(u, A, v)\<close> arbitrary: t u v rule: setinterleaving_induct)
    (auto split: if_split_asm)

lemma setinterleaves_tickFree_imp :
  \<open>tF u \<or> tF v \<Longrightarrow> t setinterleaves ((u, v), A) \<Longrightarrow> tF t \<and> tF u \<and> tF v\<close>
  by (elim disjE; induct \<open>(u, A, v)\<close> arbitrary: t u v rule: setinterleaving_induct)
    (auto split: if_split_asm)



lemma setinterleaves_NilL_iff :
  \<open>t setinterleaves (([], v), A) \<longleftrightarrow>
   tF v \<and> set v \<inter> ev ` A = {} \<and> t = map ev (map of_ev v)\<close>
  by (induct \<open>([] :: 'a trace, A, v)\<close> arbitrary: t v rule: setinterleaving_induct)
    (auto split: if_split_asm)

lemma setinterleaves_NilR_iff :
  \<open>t setinterleaves ((u, []), A) \<longleftrightarrow>
   tF u \<and> set u \<inter> ev ` A = {} \<and> t = map ev (map of_ev u)\<close>
  by (induct \<open>(u, A, [] :: 'a trace)\<close>
      arbitrary: t u rule: setinterleaving_induct)
    (auto split: if_split_asm)

lemma Nil_setinterleaves :
  \<open>[] setinterleaves ((u, v), A) \<Longrightarrow> u = [] \<and> v = []\<close>
  by (induct \<open>(u, A, v)\<close> arbitrary: u v rule: setinterleaving_induct)
    (simp_all split: if_split_asm)


lemma front_tickFree_setinterleaves_iff :
  \<open>t setinterleaves ((u, v), A) \<Longrightarrow> ftF t \<longleftrightarrow> ftF u \<and> ftF v\<close>
proof (induct \<open>(u, A, v)\<close> arbitrary: t u v rule: setinterleaving_induct)
  case (tick_setinterleaving_tick u v) thus ?case
    by (simp add: split: if_split_asm)
      (metis Nil_setinterleaves Nil_setinterleaving_Nil front_tickFree_Cons_iff singletonD)
qed (simp add: setinterleaves_NilL_iff setinterleaves_NilR_iff split: if_split_asm;
    metis event.simps(3) front_tickFree_Cons_iff front_tickFree_Nil)+


lemma setinterleaves_snoc_notinL :
  \<open>t setinterleaves ((u, v), A) \<Longrightarrow> a \<notin> A \<Longrightarrow>
   t @ [ev a] setinterleaves ((u @ [ev a], v), A)\<close>
  by (induct \<open>(u, A, v)\<close> arbitrary: t u v rule: setinterleaving_induct)
    (auto split: if_split_asm)

lemma setinterleaves_snoc_notinR :
  \<open>t setinterleaves ((u, v), A) \<Longrightarrow> a \<notin> A \<Longrightarrow>
   t @ [ev a] setinterleaves ((u, v @ [ev a]), A)\<close>
  by (induct \<open>(u, A, v)\<close> arbitrary: t u v rule: setinterleaving_induct)
    (auto split: if_split_asm)

lemma setinterleaves_snoc_inside :
  \<open>t setinterleaves ((u, v), A) \<Longrightarrow> a \<in> A \<Longrightarrow>
   t @ [ev a] setinterleaves ((u @ [ev a], v @ [ev a]), A)\<close>
  by (induct \<open>(u, A, v)\<close> arbitrary: t u v rule: setinterleaving_induct)
    (auto split: if_split_asm)


lemma setinterleaves_snoc_tick :
  \<open>t setinterleaves ((u, v), A) \<Longrightarrow> t @ [\<checkmark>] setinterleaves ((u @ [\<checkmark>], v @ [\<checkmark>]), A)\<close>
  by (induct \<open>(u, A, v)\<close> arbitrary: t u v rule: setinterleaving_induct)
    (auto split: if_split_asm)


lemma Cons_tick_setinterleavesE :
  \<open>\<checkmark> # t setinterleaves ((u, v), A) \<Longrightarrow>
   (\<And>u' v' r s. \<lbrakk>u = \<checkmark> # u'; v = \<checkmark> # v'; t setinterleaves ((u', v'), A)\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
  by (induct \<open>(u, A, v)\<close> arbitrary: t u v rule: setinterleaving_induct)
    (simp_all split: if_split_asm)

lemma Cons_ev_setinterleavesE :
  \<open>ev a # t setinterleaves ((u, v), A) \<Longrightarrow>
   (\<And>u'. a \<notin> A \<Longrightarrow> u = ev a # u' \<Longrightarrow> t setinterleaves ((u', v), A) \<Longrightarrow> thesis) \<Longrightarrow>
   (\<And>v'. a \<notin> A \<Longrightarrow> v = ev a # v' \<Longrightarrow> t setinterleaves ((u, v'), A) \<Longrightarrow> thesis) \<Longrightarrow>
   (\<And>u' v'. a \<in> A \<Longrightarrow> u = ev a # u' \<Longrightarrow> v = ev a # v' \<Longrightarrow>
             t setinterleaves ((u', v'), A) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
proof (induct \<open>(u, A, v)\<close> arbitrary: u v t rule: setinterleaving_induct)
  case Nil_setinterleaving_Nil thus ?case by simp
next
  case (ev_setinterleaving_Nil b u)
  from ev_setinterleaving_Nil.prems(1) show ?case
    by (simp add: ev_setinterleaving_Nil.prems(2) split: if_split_asm)
next
  case (tick_setinterleaving_Nil r u) thus ?case by simp
next
  case (Nil_setinterleaving_ev c v)
  from Nil_setinterleaving_ev.prems(1) show ?case
    by (simp add: Nil_setinterleaving_ev.prems(3) split: if_split_asm)
next
  case (Nil_setinterleaving_tick s v) thus ?case by simp
next
  case (ev_setinterleaving_ev b u c v)
  from ev_setinterleaving_ev.prems(1) show ?case
    by (simp add: ev_setinterleaving_ev.prems(2, 3, 4) split: if_split_asm)
      (use ev_setinterleaving_ev.prems(2, 3) in presburger)
next
  case (ev_setinterleaving_tick b u s v)
  from ev_setinterleaving_tick.prems(1) show ?case
    by (simp add: ev_setinterleaving_tick.prems(2) split: if_split_asm)
next
  case (tick_setinterleaving_ev r u c v)
  from tick_setinterleaving_ev.prems(1) show ?case
    by (simp add: tick_setinterleaving_ev.prems(3) split: if_split_asm)
next
  case (tick_setinterleaving_tick u v) thus ?case by simp
qed


lemma rev_setinterleaves_rev_rev_iff :
  \<open>rev t setinterleaves ((rev u, rev v), A)
   \<longleftrightarrow> t setinterleaves ((u, v), A)\<close>
proof (rule iffI)
  show \<open>t setinterleaves ((u, v), A) \<Longrightarrow>
        rev t setinterleaves ((rev u, rev v), A)\<close> for t u v
    by (induct \<open>(u, A, v)\<close> arbitrary: t u v rule: setinterleaving_induct)
      (auto simp add: setinterleaves_snoc_notinL setinterleaves_snoc_notinR
        setinterleaves_snoc_inside setinterleaves_snoc_tick split: if_split_asm)
  from this[of \<open>rev t\<close> \<open>rev u\<close> \<open>rev v\<close>, simplified]
  show \<open>rev t setinterleaves ((rev u, rev v), A) \<Longrightarrow>
        t setinterleaves ((u, v), A)\<close> .
qed


lemma setinterleaves_preserves_ev_notin_set :
  \<open>\<lbrakk>ev a \<notin> set u; ev a \<notin> set v; t setinterleaves ((u, v), A)\<rbrakk> \<Longrightarrow> ev a \<notin> set t\<close>
  by (induct \<open>(u, A, v)\<close> arbitrary: t u v rule: setinterleaving_induct)
    (auto split: if_split_asm)



lemma setinterleaves_preserves_ev_inside_set :
  \<open>\<lbrakk>ev a \<in> set u; ev a \<in> set v; t setinterleaves ((u, v), A)\<rbrakk> \<Longrightarrow> ev a \<in> set t\<close>
proof (induct \<open>(u, A, v)\<close> arbitrary: t u v rule: setinterleaving_induct)
  case Nil_setinterleaving_Nil
  then show ?case by simp
next
  case (ev_setinterleaving_Nil a u)
  then show ?case by simp
next
  case (tick_setinterleaving_Nil u)
  then show ?case by simp
next
  case (Nil_setinterleaving_ev b v)
  then show ?case by simp
next
  case (Nil_setinterleaving_tick v)
  then show ?case by simp
next
  case (ev_setinterleaving_ev a u b v)
  from ev_setinterleaving_ev.prems show ?case
    by (simp_all split: if_split_asm)
      (insert ev_setinterleaving_ev.hyps; metis list.set_intros(1,2))+
next
  case (ev_setinterleaving_tick a u v)
  then show ?case by (auto split: if_split_asm)
next
  case (tick_setinterleaving_ev u b v)
  then show ?case by (auto split: if_split_asm)
next
  case (tick_setinterleaving_tick u v)
  then show ?case by auto
qed


lemma ev_notin_both_sets_imp_empty_setinterleaving :
  \<open>\<lbrakk>ev a \<in> set u \<and> ev a \<notin> set v \<or> ev a \<notin> set u \<and> ev a \<in> set v; a \<in> A\<rbrakk> \<Longrightarrow>
   setinterleaving (u, A, v) = {}\<close>
  by (induct \<open>(u, A, v)\<close> arbitrary: u v rule: setinterleaving_induct)
    (simp_all, safe, auto)


lemma append_setinterleaves_imp :
  \<open>t setinterleaves ((u, v), A) \<Longrightarrow> t' \<le> t \<Longrightarrow>
   \<exists>u' \<le> u. \<exists>v' \<le> v. t' setinterleaves ((u', v'), A)\<close>
proof (induct \<open>(u, A, v)\<close> arbitrary: t u v t' rule: setinterleaving_induct)
  case Nil_setinterleaving_Nil thus ?case by auto
next
  case (ev_setinterleaving_Nil a u)
  from ev_setinterleaving_Nil.prems
  obtain w w' where \<open>a \<notin> A\<close> \<open>t = ev a # w\<close> \<open>t' = [] \<or> t' = ev a # w'\<close>
    \<open>w' \<le> w\<close> \<open>w setinterleaves ((u, []), A)\<close>
    by (simp split: if_split_asm) (metis (no_types) Prefix_Order.prefix_Cons Nil_prefix)
  from \<open>t' = [] \<or> t' = ev a # w'\<close> show ?case
  proof (elim disjE)
    show \<open>t' = [] \<Longrightarrow> ?case\<close> by auto
  next
    assume \<open>t' = ev a # w'\<close>
    from ev_setinterleaving_Nil.hyps[OF \<open>a \<notin> A\<close> \<open>w setinterleaves ((u, []), A)\<close> \<open>w' \<le> w\<close>]
    obtain u' v' where \<open>u' \<le> u \<and> v' \<le> [] \<and> w' setinterleaves ((u', v'), A)\<close> by blast
    hence \<open>ev a # u' \<le> ev a # u \<and> v' \<le> [] \<and> t' setinterleaves ((ev a # u', v'), A)\<close>
      by (auto simp add: \<open>a \<notin> A\<close> \<open>t' = ev a # w'\<close>)
    thus ?case by blast
  qed
next
  case (tick_setinterleaving_Nil r u) thus ?case by simp
next
  case (Nil_setinterleaving_ev b v)
  from Nil_setinterleaving_ev.prems
  obtain w w' where \<open>b \<notin> A\<close> \<open>t = ev b # w\<close> \<open>t' = [] \<or> t' = ev b # w'\<close>
    \<open>w' \<le> w\<close> \<open>w setinterleaves (([], v), A)\<close>
    by (simp split: if_split_asm) (metis (no_types) Prefix_Order.prefix_Cons Nil_prefix)
  from \<open>t' = [] \<or> t' = ev b # w'\<close> show ?case
  proof (elim disjE)
    show \<open>t' = [] \<Longrightarrow> ?case\<close> by auto
  next
    assume \<open>t' = ev b # w'\<close>
    from Nil_setinterleaving_ev.hyps[OF \<open>b \<notin> A\<close> \<open>w setinterleaves (([], v), A)\<close> \<open>w' \<le> w\<close>]
    obtain u' v' where \<open>u' \<le> [] \<and> v' \<le> v \<and> w' setinterleaves ((u', v'), A)\<close> by blast
    hence \<open>u' \<le> [] \<and> ev b # v' \<le> ev b # v \<and> t' setinterleaves ((u', ev b # v'), A)\<close>
      by (auto simp add: \<open>b \<notin> A\<close> \<open>t' = ev b # w'\<close>)
    thus ?case by blast
  qed
next
  case (Nil_setinterleaving_tick s v) thus ?case by simp
next
  case (ev_setinterleaving_ev a u b v)
  from ev_setinterleaving_ev.prems
  consider \<open>t' = []\<close>
    |      (both_in)   w w' where \<open>a \<in> A\<close> \<open>b \<in> A\<close> \<open>a = b\<close> \<open>t = ev a # w\<close> \<open>t' = ev a # w'\<close>
      \<open>w setinterleaves ((u, v), A)\<close> \<open>w' \<le> w\<close>
    |      (inR_mvL)   w w' where \<open>a \<notin> A\<close> \<open>b \<in> A\<close> \<open>t = ev a # w\<close> \<open>t' = ev a # w'\<close>
      \<open>w setinterleaves ((u, ev b # v), A)\<close> \<open>w' \<le> w\<close>
    |      (inL_mvR)   w w' where \<open>a \<in> A\<close> \<open>b \<notin> A\<close> \<open>t = ev b # w\<close> \<open>t' = ev b # w'\<close>
      \<open>w setinterleaves ((ev a # u, v), A)\<close> \<open>w' \<le> w\<close>
    |      (notin_mvL) w w' where \<open>a \<notin> A\<close> \<open>b \<notin> A\<close> \<open>t = ev a # w\<close> \<open>t' = ev a # w'\<close>
      \<open>w setinterleaves ((u, ev b # v), A)\<close> \<open>w' \<le> w\<close>
    |      (notin_mvR) w w' where \<open>a \<notin> A\<close> \<open>b \<notin> A\<close> \<open>t = ev b # w\<close> \<open>t' = ev b # w'\<close>
      \<open>w setinterleaves ((ev a # u, v), A)\<close> \<open>w' \<le> w\<close>
    by (cases t') (auto split: if_split_asm)
  thus ?case
  proof cases
    from Nil_setinterleaving_Nil show \<open>t' = [] \<Longrightarrow> ?thesis\<close> by blast
  next
    case both_in
    from ev_setinterleaving_ev(1)[OF both_in(1-3, 6-7)]
    obtain u' v' where \<open>u' \<le> u \<and> v' \<le> v \<and> w' setinterleaves ((u', v'), A)\<close> by blast
    hence \<open>ev a # u' \<le> ev a # u \<and> ev b # v' \<le> ev b # v \<and> t' setinterleaves ((ev a # u', ev b # v'), A)\<close>
      by (auto simp add: both_in(2, 3) \<open>t' = ev a # w'\<close>)
    thus ?thesis by blast
  next
    case inR_mvL
    from ev_setinterleaving_ev(3)[OF inR_mvL(1, 2, 5, 6)]
    obtain u' v' where \<open>u' \<le> u \<and> v' \<le> ev b # v \<and> w' setinterleaves ((u', v'), A)\<close> by blast
    hence \<open>ev a # u' \<le> ev a # u \<and> v' \<le> ev b # v \<and> t' setinterleaves ((ev a # u', v'), A)\<close>
      by (cases v') (auto simp add: inR_mvL(1, 4))
    thus ?thesis by blast
  next
    case inL_mvR
    from ev_setinterleaving_ev(2)[OF inL_mvR(1, 2, 5, 6)]
    obtain u' v' where \<open>u' \<le> ev a # u \<and> v' \<le> v \<and> w' setinterleaves ((u', v'), A)\<close> by blast
    hence \<open>u' \<le> ev a # u \<and> ev b # v' \<le> ev b # v \<and> t' setinterleaves ((u', ev b # v'), A)\<close>
      by (cases u') (auto simp add: inL_mvR(2, 4))
    thus ?thesis by blast
  next
    case notin_mvL
    from ev_setinterleaving_ev(4)[OF notin_mvL(1, 2, 5, 6)]
    obtain u' v' where \<open>u' \<le> u \<and> v' \<le> ev b # v \<and> w' setinterleaves ((u', v'), A)\<close> by blast
    hence \<open>ev a # u' \<le> ev a # u \<and> v' \<le> ev b # v \<and> t' setinterleaves ((ev a # u', v'), A)\<close>
      by (cases v') (auto simp add: notin_mvL(1, 4))
    thus ?thesis by blast
  next
    case notin_mvR
    from ev_setinterleaving_ev(5)[OF notin_mvR(1, 2, 5, 6)]
    obtain u' v' where \<open>u' \<le> ev a # u \<and> v' \<le> v \<and> w' setinterleaves ((u', v'), A)\<close> by blast
    hence \<open>u' \<le> ev a # u \<and> ev b # v' \<le> ev b # v \<and> t' setinterleaves ((u', ev b # v'), A)\<close>
      by (cases u') (auto simp add: notin_mvR(2, 4))
    thus ?thesis by blast
  qed
next
  case (ev_setinterleaving_tick a u v)
  from ev_setinterleaving_tick.prems
  obtain w w' where \<open>a \<notin> A\<close> \<open>t = ev a # w\<close> \<open>t' = [] \<or> t' = ev a # w'\<close>
    \<open>w' \<le> w\<close> \<open>w setinterleaves ((u, \<checkmark> # v), A)\<close>
    by (simp split: if_split_asm) (metis (no_types) Prefix_Order.prefix_Cons Nil_prefix)
  from \<open>t' = [] \<or> t' = ev a # w'\<close> show ?case
  proof (elim disjE)
    from Nil_setinterleaving_Nil show \<open>t' = [] \<Longrightarrow> ?case\<close> by blast
  next
    assume \<open>t' = ev a # w'\<close>
    from ev_setinterleaving_tick.hyps[OF \<open>a \<notin> A\<close> \<open>w setinterleaves ((u, \<checkmark> # v), A)\<close> \<open>w' \<le> w\<close>]
    obtain u' v' where \<open>u' \<le> u \<and> v' \<le> \<checkmark> # v \<and> w' setinterleaves ((u', v'), A)\<close> by blast
    hence \<open>ev a # u' \<le> ev a # u \<and> v' \<le> \<checkmark> # v \<and> t' setinterleaves ((ev a # u', v'), A)\<close>
      by (cases v') (simp_all add: \<open>a \<notin> A\<close> \<open>t' = ev a # w'\<close>)
    thus ?case by blast
  qed
next
  case (tick_setinterleaving_ev u b v)
  from tick_setinterleaving_ev.prems
  obtain w w' where \<open>b \<notin> A\<close> \<open>t = ev b # w\<close> \<open>t' = [] \<or> t' = ev b # w'\<close>
    \<open>w' \<le> w\<close> \<open>w setinterleaves ((\<checkmark> # u, v), A)\<close>
    by (simp split: if_split_asm) (metis (no_types) Prefix_Order.prefix_Cons Nil_prefix)
  from \<open>t' = [] \<or> t' = ev b # w'\<close> show ?case
  proof (elim disjE)
    from Nil_setinterleaving_Nil show \<open>t' = [] \<Longrightarrow> ?case\<close> by blast
  next
    assume \<open>t' = ev b # w'\<close>
    from tick_setinterleaving_ev.hyps[OF \<open>b \<notin> A\<close> \<open>w setinterleaves ((\<checkmark> # u, v), A)\<close> \<open>w' \<le> w\<close>]
    obtain u' v' where \<open>u' \<le> \<checkmark> # u \<and> v' \<le> v \<and> w' setinterleaves ((u', v'), A)\<close> by blast
    hence \<open>u' \<le> \<checkmark> # u \<and> ev b # v' \<le> ev b # v \<and> t' setinterleaves ((u', ev b # v'), A)\<close>
      by (cases u') (simp_all add: \<open>b \<notin> A\<close> \<open>t' = ev b # w'\<close>)
    thus ?case by blast
  qed
next
  case (tick_setinterleaving_tick u v)
  from tick_setinterleaving_tick.prems obtain w w'
    where \<open>t = \<checkmark> # w\<close> \<open>t' = [] \<or> t' = \<checkmark> # w'\<close>
      \<open>w' \<le> w\<close> \<open>w setinterleaves ((u, v), A)\<close>
    by (cases t') (auto split: option.split_asm)
  from \<open>t' = [] \<or> t' = \<checkmark> # w'\<close> show ?case
  proof (elim disjE)
    from Nil_setinterleaving_Nil show \<open>t' = [] \<Longrightarrow> ?case\<close> by blast
  next
    assume \<open>t' = \<checkmark> # w'\<close>
    from tick_setinterleaving_tick.hyps
      [OF \<open>w setinterleaves ((u, v), A)\<close> \<open>w' \<le> w\<close>]
    obtain u' v' where \<open>u' \<le> u \<and> v' \<le> v \<and> w' setinterleaves ((u', v'), A)\<close> by blast
    hence \<open>\<checkmark> # u' \<le> \<checkmark> # u \<and> \<checkmark> # v' \<le> \<checkmark> # v \<and>
           t' setinterleaves ((\<checkmark> # u', \<checkmark> # v'), A)\<close>
      by (simp add: \<open>t' = \<checkmark> # w'\<close>)
    thus ?case by blast
  qed
qed



lift_definition Sync :: \<open>'a process \<Rightarrow> 'a set \<Rightarrow> 'a process \<Rightarrow> 'a process\<close>
  (\<open>(3(_ \<lbrakk>_\<rbrakk>/ _))\<close> [70, 0, 71] 70)
  is \<open>\<lambda>P A Q. {t. \<exists>t_P t_Q. t_P \<in> \<T> P \<and> t_Q \<in> \<T> Q \<and> t setinterleaves ((t_P, t_Q), A)}\<close>
proof -
  show \<open>?thesis P A Q\<close> (is \<open>is_process ?t\<close>) for P A Q
  proof (unfold is_process_def, intro conjI allI impI)
    from Nil_elem_T Nil_setinterleaving_Nil show \<open>[] \<in> ?t\<close> by blast
  next
    fix t assume \<open>t \<in> ?t\<close>
    then obtain t_P t_Q where \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close>
      \<open>t setinterleaves ((t_P, t_Q), A)\<close> by blast
    from \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close> front_tickFree_T
    have \<open>ftF t_P\<close> \<open>ftF t_Q\<close> by auto
    with \<open>t setinterleaves ((t_P, t_Q), A)\<close>
    show \<open>ftF t\<close> by (simp add: front_tickFree_setinterleaves_iff)
  next
    fix t u assume \<open>t @ u \<in> ?t\<close>
    then obtain t_P t_Q where \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close>
      \<open>t @ u setinterleaves ((t_P, t_Q), A)\<close> by blast
    from this(3) obtain t_P' t_P'' t_Q' t_Q''
      where \<open>t_P = t_P' @ t_P''\<close> \<open>t_Q = t_Q' @ t_Q''\<close>
        \<open>t setinterleaves ((t_P', t_Q'), A)\<close>
      by (meson Prefix_Order.prefixE Prefix_Order.prefixI append_setinterleaves_imp)
    from \<open>t_P \<in> \<T> P\<close> \<open>t_Q \<in> \<T> Q\<close> this(1, 2) have \<open>t_P' \<in> \<T> P\<close> \<open>t_Q' \<in> \<T> Q\<close>
      by (auto intro: T_dw_closed)
    with \<open>t setinterleaves ((t_P', t_Q'), A)\<close> show \<open>t \<in> ?t\<close> by blast
  qed
qed

lemma T_Sync :
  \<open>\<T> (P \<lbrakk>A\<rbrakk> Q) = {t. \<exists>t_P t_Q. t_P \<in> \<T> P \<and> t_Q \<in> \<T> Q \<and> t setinterleaves ((t_P, t_Q), A)}\<close>
  by (simp add: Sync.rep_eq)


lift_definition Interrupt :: \<open>'a process \<Rightarrow> 'a process \<Rightarrow> 'a process\<close> (infixl \<open>\<triangle>\<close> 81)
  is \<open>\<lambda>P Q. \<T> P \<union> {t @ u |t u. t \<in> \<T> P \<and> tF t \<and> u \<in> \<T> Q}\<close>
proof -
  show \<open>?thesis P Q\<close> (is \<open>is_process ?t\<close>) for P Q
  proof (unfold is_process_def, intro conjI allI impI)
    show \<open>[] \<in> ?t\<close> by (simp add: Nil_elem_T)
  next
    show \<open>t \<in> ?t \<Longrightarrow> ftF t\<close> for t
      by (auto simp add: front_tickFree_append_iff intro: front_tickFree_T)
  next
    show \<open>t @ u \<in> ?t \<Longrightarrow> t \<in> ?t\<close> for t u
      by (auto simp add: append_eq_append_conv2 intro: T_dw_closed)
  qed
qed





subsection \<open>Constructiveness\<close>

lemma restriction_process_Mprefix :
  \<open>\<box>a \<in> A \<rightarrow> P a \<down> n = (case n of 0 \<Rightarrow> BOT | Suc m \<Rightarrow> \<box>a\<in>A \<rightarrow> (P a \<down> m))\<close>
  by (auto simp add: process_eq_spec T_restriction_process T_Mprefix T_BOT
      Nil_elem_T nat.case_eq_if front_tickFree_Cons_iff front_tickFree_T)
    (metis Cons_eq_append_conv Suc_length_conv event.distinct(1) length_greater_0_conv
      list.size(3) nat.exhaust_sel tickFree_Cons_iff)


lemma constructive_Mprefix [simp] :
  \<open>constructive (\<lambda>b. \<box>a\<in>A \<rightarrow> f a b)\<close> if \<open>\<And>a. a \<in> A \<Longrightarrow> non_destructive (f a)\<close>
proof -
  have \<open>\<box>a\<in>A \<rightarrow> f a b = \<box>a\<in>A \<rightarrow> (if a \<in> A then f a b else STOP)\<close> for b
    by (auto simp add: process_eq_spec T_Mprefix)
  moreover have \<open>constructive (\<lambda>b. \<box>a\<in>A \<rightarrow> (if a \<in> A then f a b else STOP))\<close>
  proof (rule constructive_comp_non_destructive[of \<open>\<lambda>P. \<box>a\<in>A \<rightarrow> P a\<close>])
    show \<open>constructive (\<lambda>P. \<box>a\<in>A \<rightarrow> P a)\<close>
      by (rule constructiveI) (simp add: restriction_process_Mprefix restriction_fun_def)
  next
    show \<open>non_destructive (\<lambda>b a. if a \<in> A then f a b else STOP)\<close>
      by (simp add: non_destructive_fun_iff, intro allI non_destructive_if_then_else)
        (simp_all add: \<open>\<And>a. a \<in> A \<Longrightarrow> non_destructive (f a)\<close> non_destructiveI)
  qed
  ultimately show \<open>constructive (\<lambda>b. \<box>a\<in>A \<rightarrow> f a b)\<close> by simp
qed






subsection \<open>Non Destructiveness\<close>

lemma non_destructive_Choice [simp] :
  \<open>non_destructive (\<lambda>x. f x \<box> g x)\<close>
  if \<open>non_destructive f\<close> \<open>non_destructive g\<close>
  for f g :: \<open>'a :: restriction \<Rightarrow> 'b process\<close>
proof -
  have * : \<open>non_destructive (\<lambda>(P, Q). P \<box> Q :: 'b process)\<close>
  proof (rule order_non_destructiveI, clarify)
    fix P Q P' Q' :: \<open>'b process\<close> and n
    assume \<open>(P, Q) \<down> n = (P', Q') \<down> n\<close>
    hence \<open>P \<down> n = P' \<down> n\<close> \<open>Q \<down> n = Q' \<down> n\<close>
      by (simp_all add: restriction_prod_def)
    show \<open>P \<box> Q \<down> n \<le> P' \<box> Q' \<down> n\<close>
    proof (unfold less_eq_process_def, rule subsetI)
      show \<open>t \<in> \<T> (P' \<box> Q' \<down> n) \<Longrightarrow> t \<in> \<T> (P \<box> Q \<down> n)\<close> for t
      proof (elim T_restriction_processE)
        show \<open>t \<in> \<T> (P' \<box> Q') \<Longrightarrow> length t \<le> n \<Longrightarrow> t \<in> \<T> (P \<box> Q \<down> n)\<close>
          by (simp add: T_restriction_process T_Choice)
            (metis (lifting) T_restriction_process T_restriction_processE
              Un_iff \<open>P \<down> n = P' \<down> n\<close> \<open>Q \<down> n = Q' \<down> n\<close>)
      next
        show \<open>\<lbrakk>t = u @ v; u \<in> \<T> (P' \<box> Q'); length u = n; tF u; ftF v\<rbrakk>
              \<Longrightarrow> t \<in> \<T> (P \<box> Q \<down> n)\<close> for u v
          by (simp add: T_restriction_process T_Choice)
            (metis (lifting) T_restriction_process T_restriction_processE Un_iff
              \<open>P \<down> n = P' \<down> n\<close> \<open>Q \<down> n = Q' \<down> n\<close> append.right_neutral append_eq_conv_conj)
      qed
    qed
  qed
  have ** : \<open>non_destructive (\<lambda>x. (f x, g x))\<close>
    by (fact non_destructive_prod_codomain[OF that])
  from non_destructive_comp_non_destructive[OF * **, simplified]
  show \<open>non_destructive (\<lambda>x. f x \<box> g x)\<close> .
qed


lemma restriction_process_GlobalChoice :
  \<open>\<box>a \<in> A. P a \<down> n = (if A = {} then case n of 0 \<Rightarrow> BOT | Suc m \<Rightarrow> STOP else \<box>a \<in> A. (P a \<down> n))\<close>
  by (auto simp add: process_eq_spec T_restriction_process T_GlobalChoice T_BOT T_STOP
      split: nat.split)


lemma non_destructive_GlobalChoice [simp] :
  \<open>non_destructive (\<lambda>b. \<box>a\<in>A. f a b)\<close> if \<open>\<And>a. a \<in> A \<Longrightarrow> non_destructive (f a)\<close>
proof -
  have \<open>\<box>a\<in>A. f a b = \<box>a\<in>A. (if a \<in> A then f a b else STOP)\<close> for b
    by (auto simp add: process_eq_spec T_GlobalChoice)
  moreover have \<open>non_destructive (\<lambda>b. \<box>a\<in>A. (if a \<in> A then f a b else STOP))\<close>
  proof (rule non_destructive_comp_non_destructive[of \<open>\<lambda>P. \<box>a\<in>A. P a\<close>])
    show \<open>non_destructive (\<lambda>P. \<box>a\<in>A. P a)\<close>
      by (rule non_destructiveI) (simp add: restriction_process_GlobalChoice restriction_fun_def)
  next
    show \<open>non_destructive (\<lambda>b a. if a \<in> A then f a b else STOP)\<close>
      by (simp add: non_destructive_fun_iff, intro allI non_destructive_if_then_else)
        (simp_all add: \<open>\<And>a. a \<in> A \<Longrightarrow> non_destructive (f a)\<close> non_destructiveI)
  qed
  ultimately show \<open>non_destructive (\<lambda>b. \<box>a\<in>A. f a b)\<close> by simp
qed



subsection \<open>Examples\<close>

notepad begin
  fix A B :: \<open>'b \<Rightarrow> 'a set\<close>
  define P :: \<open>'b \<Rightarrow> 'a process\<close>
    where \<open>P \<equiv> \<upsilon> X. (\<lambda>s. \<box> a \<in> A s \<rightarrow> X s \<box> (\<box> b \<in> B s \<rightarrow> X s))\<close> (is \<open>P \<equiv> \<upsilon> X. ?f X\<close>)
  have \<open>P = ?f P\<close>
    by (unfold P_def, subst restriction_fix_eq) simp_all

end


lemma \<open>constructive (\<lambda>X \<sigma>. \<box> e \<in> f \<sigma> \<rightarrow> \<box> \<sigma>' \<in> g \<sigma> e. X \<sigma>')\<close>
  by simp



lemma length_le_T_restriction_process_iff_T :
  \<open>length t \<le> n \<Longrightarrow> t \<in> \<T> (P \<down> n) \<longleftrightarrow> t \<in> \<T> P\<close>
  by (auto simp add: T_restriction_process)



lemma restriction_adm_notin_T [simp] : \<open>adm\<^sub>\<down> (\<lambda>a. t \<notin> \<T> a)\<close>
proof (rule restriction_admI)
  fix \<sigma> and \<Sigma> assume \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> \<open>\<And>n. t \<notin> \<T> (\<sigma> n)\<close>
  from \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> obtain n0 where \<open>\<forall>k\<ge>n0. \<Sigma> \<down> length t = \<sigma> k \<down> length t\<close>
    by (blast dest: restriction_tendstoD)
  hence \<open>\<forall>k\<ge>n0. \<T> (\<Sigma> \<down> length t) = \<T> (\<sigma> k \<down> length t)\<close> by simp
  hence \<open>\<forall>k\<ge>n0. t \<in> \<T> \<Sigma> \<longleftrightarrow> t \<in> \<T> (\<sigma> k)\<close>
    by (metis dual_order.refl length_le_T_restriction_process_iff_T)
  with \<open>\<And>n. t \<notin> \<T> (\<sigma> n)\<close> show \<open>t \<notin> \<T> \<Sigma>\<close> by blast
qed


lemma restriction_adm_in_T [simp] : \<open>adm\<^sub>\<down> (\<lambda>a. t \<in> \<T> a)\<close>
proof (rule restriction_admI)
  fix \<sigma> and \<Sigma> assume \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> \<open>\<And>n. t \<in> \<T> (\<sigma> n)\<close>
  from \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> obtain n0 where \<open>\<forall>k\<ge>n0. \<Sigma> \<down> length t = \<sigma> k \<down> length t\<close>
    by (blast dest: restriction_tendstoD)
  hence \<open>\<forall>k\<ge>n0. \<T> (\<Sigma> \<down> length t) = \<T> (\<sigma> k \<down> length t)\<close> by simp
  hence \<open>\<forall>k\<ge>n0. t \<in> \<T> \<Sigma> \<longleftrightarrow> t \<in> \<T> (\<sigma> k)\<close>
    by (metis dual_order.refl length_le_T_restriction_process_iff_T)
  with \<open>\<And>n. t \<in> \<T> (\<sigma> n)\<close> show \<open>t \<in> \<T> \<Sigma>\<close> by blast
qed


(*<*)
end
  (*>*)