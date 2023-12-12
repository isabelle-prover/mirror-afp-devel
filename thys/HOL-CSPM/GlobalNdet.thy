(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSPM - Architectural operators for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff
 *
 * This file       : Global non-deterministic choice
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


chapter\<open> The Global Non-Deterministic Choice \<close>
theory GlobalNdet                                               
  imports MultiNdet
begin 


section\<open> General Non-Deterministic Choice Definition\<close>

text\<open> This is an experimental definition of a generalized non-deterministic choice  \<^term>\<open>a \<sqinter> b\<close>
for an arbitrary set. The present version is "totalised" for the case of \<^term>\<open>A = {}\<close> by
\<^const>\<open>STOP\<close>, which is not the neutral element of the \<^const>\<open>Ndet\<close> operator (because
there is no neutral element for \<^const>\<open>Ndet\<close>).\<close>

lemma \<open>\<nexists>P. \<forall>Q. (P :: '\<alpha> process) \<sqinter> Q = Q\<close>
proof -
  { fix P :: \<open>'\<alpha> process\<close>
    assume * : \<open>\<forall>Q. P \<sqinter> Q = Q\<close>
    hence \<open>P = STOP\<close>
      by (erule_tac x = STOP in allE) (simp add: Ndet_is_STOP_iff)
    with * have False
      by (erule_tac x = SKIP in allE) 
         (metis mono_Ndet_FD_right Ndet_commute 
                SKIP_FD_iff SKIP_Neq_STOP idem_FD)
  }
  thus ?thesis by blast
qed



lift_definition GlobalNdet :: \<open>['\<alpha> set, '\<alpha> \<Rightarrow> '\<beta> process] \<Rightarrow> '\<beta> process\<close>
  is   \<open>\<lambda>A P.   if A = {} 
              then ({(s, X). s = []}, {})
              else (\<Union>a\<in>A. \<F> (P a), \<Union>a\<in>A. \<D> (P a))\<close>
proof -
  show \<open>?thesis A P\<close>
   (is \<open>is_process (  if A = {} then ({(s, X). s = []}, {}) else (?f, ?d))\<close>) for A P
  proof (split if_split, intro conjI impI)
    show \<open>is_process ({(s, X). s = []}, {})\<close>
      by (simp add: is_process_REP_STOP)
  next
    show \<open>is_process (\<Union>a\<in>A. \<F> (P a), \<Union>a\<in>A. \<D> (P a))\<close> if nonempty: \<open>A \<noteq> {}\<close>
      unfolding is_process_def FAILURES_def DIVERGENCES_def fst_conv snd_conv
    proof (intro conjI allI impI)
      show \<open>([], {}) \<in> ?f\<close> using is_processT1 nonempty by blast
    next
      show \<open>(s, X) \<in> ?f \<Longrightarrow> front_tickFree s\<close> for s X
        using is_processT2 by blast
    next
      show \<open>(s @ t, {}) \<in> ?f \<Longrightarrow> (s, {}) \<in> ?f\<close> for s t
        using is_processT3 by blast
    next
      show \<open>(s, Y) \<in> ?f \<and> X \<subseteq> Y \<Longrightarrow> (s, X) \<in> ?f\<close> for s X Y
        using is_processT4 by blast
    next
      show \<open>(s, X) \<in> ?f \<and> (\<forall>c. c \<in> Y \<longrightarrow> (s @ [c], {}) \<notin> ?f) \<Longrightarrow> (s, X \<union> Y) \<in> ?f\<close> for s X Y
        using is_processT5 by simp blast
    next
      show \<open>(s @ [tick], {}) \<in> ?f \<Longrightarrow> (s, X - {tick}) \<in> ?f\<close> for s X
        using is_processT6 by blast
    next
      show \<open>s \<in> ?d \<and> tickFree s \<and> front_tickFree t \<Longrightarrow> s @ t \<in> ?d\<close> for s t
        using is_processT7 by blast
    next
      show \<open>s \<in> ?d \<Longrightarrow> (s, X) \<in> ?f\<close> for s X 
        using is_processT8 by blast
    next
      show \<open>s @ [tick] \<in> ?d \<Longrightarrow> s \<in> ?d\<close> for s
        using is_processT9 by blast
    qed
  qed
qed
  
  


syntax  "_GlobalNdet" :: \<open>[pttrn,'a set,'b process] \<Rightarrow> 'b process\<close> (\<open>(3\<sqinter> _\<in>_. / _)\<close> 76)
translations  "\<sqinter> p \<in> A. P " \<rightleftharpoons> "CONST GlobalNdet A (\<lambda>p. P)"

text\<open>Note that the global non-deterministic choice @{term [eta_contract = false] \<open>\<sqinter> p \<in> A. P p\<close>}
     is different from the multi-non-deterministic prefix
     @{term [eta_contract = false] \<open>\<sqinter> p \<in> A \<rightarrow> P p\<close>} which guarantees continuity 
     even when \<^term>\<open>A\<close> is \<^const>\<open>infinite\<close> due to the fact that it communicates
     its choice via an internal prefix operator.

     It is also subtly different from the multi-non-deterministic choice
     @{term [eta_contract = false] \<open>\<Sqinter> p \<in> A. P p\<close>} 
     which is only defined when \<^term>\<open>A\<close> is \<^const>\<open>finite\<close>.\<close>

lemma empty_GlobalNdet[simp] : \<open>GlobalNdet {} P = STOP\<close>
  by (simp add: GlobalNdet.abs_eq STOP_def)



section \<open>The Projections\<close>

lemma F_GlobalNdet:
  \<open>\<F> (\<sqinter> x \<in> A. P x) = (if A = {} then {(s, X). s = []} else (\<Union> x\<in>A. \<F> (P x)))\<close>
  by (simp add: Failures_def FAILURES_def GlobalNdet.rep_eq)

lemma D_GlobalNdet:
  \<open>\<D> (\<sqinter> x \<in> A. P x) = (if A = {} then {} else (\<Union> x\<in>A. \<D> (P x)))\<close>
  by (simp add: Divergences_def DIVERGENCES_def GlobalNdet.rep_eq)

lemma T_GlobalNdet:
  \<open>\<T> (\<sqinter> x \<in> A. P x) = (if A = {} then {[]} else (\<Union> x\<in>A. \<T> (P x)))\<close>
  by (auto simp add: Traces_def TRACES_def Failures_def[symmetric] 
                     F_GlobalNdet intro: F_T T_F)
 

lemma mono_GlobalNdet_eq:
  \<open>\<forall>x \<in> A. P x = Q x \<Longrightarrow> GlobalNdet A P = GlobalNdet A Q\<close>
  by (subst Process_eq_spec, simp add: F_GlobalNdet D_GlobalNdet)

lemma mono_GlobalNdet_eq2:
  \<open>\<forall>x \<in> A. P (f x) = Q x \<Longrightarrow> GlobalNdet (f ` A) P = GlobalNdet A Q\<close>
  by (subst Process_eq_spec, simp add: F_GlobalNdet D_GlobalNdet)




section \<open>Factorization of \<^const>\<open>Ndet\<close> in front of \<^const>\<open>GlobalNdet\<close>\<close>

lemma GlobalNdet_factorization_union:
  \<open>\<lbrakk>A \<noteq> {}; B \<noteq> {}\<rbrakk> \<Longrightarrow>
   (\<sqinter> p \<in> A. P p) \<sqinter> (\<sqinter> p \<in> B. P p) = (\<sqinter> p \<in> A \<union> B . P p)\<close>
  by (subst Process_eq_spec) (simp add: F_GlobalNdet D_GlobalNdet F_Ndet D_Ndet)
 



section \<open>\<^term>\<open>\<bottom>\<close> Absorbance\<close>

lemma GlobalNdet_BOT_absorb: \<open>P a = \<bottom> \<Longrightarrow> a \<in> A \<Longrightarrow> (\<sqinter> x \<in> A. P x) = \<bottom>\<close>
  using is_processT2
  by (subst Process_eq_spec)
     (auto simp add: F_GlobalNdet D_GlobalNdet F_UU D_UU D_imp_front_tickFree)


lemma GlobalNdet_is_BOT_iff: \<open>(\<sqinter> x \<in> A. P x) = \<bottom> \<longleftrightarrow> (\<exists>a \<in> A. P a = \<bottom>)\<close>
  by (simp add: BOT_iff_D D_GlobalNdet)
  


section \<open>First Properties\<close>

lemma GlobalNdet_id: \<open>A \<noteq> {} \<Longrightarrow> (\<sqinter> p \<in> A. P) = P\<close>
  by (subst Process_eq_spec) (simp add: F_GlobalNdet D_GlobalNdet)


lemma GlobalNdet_STOP_id: \<open>(\<sqinter> p \<in> A. STOP) = STOP\<close>
  by (cases \<open>A = {}\<close>) (simp_all add: GlobalNdet_id)


lemma GlobalNdet_unit[simp] : \<open>(\<sqinter> x \<in> {a}. P x) = P a\<close> 
  by(auto simp : Process_eq_spec F_GlobalNdet D_GlobalNdet)


lemma GlobalNdet_distrib_unit:
  \<open>A - {a} \<noteq> {} \<Longrightarrow> (\<sqinter> x \<in> insert a A. P x) = P a \<sqinter> (\<sqinter> x \<in> A - {a}. P x)\<close>
  by (metis GlobalNdet_factorization_union GlobalNdet_unit 
            empty_not_insert insert_Diff_single insert_is_Un)



section \<open>Behaviour of \<^const>\<open>GlobalNdet\<close> with \<^const>\<open>Ndet\<close>\<close>

lemma GlobalNdet_Ndet:
  \<open>(\<sqinter> a \<in> A. P a) \<sqinter> (\<sqinter> a \<in> A. Q a) = \<sqinter> a \<in> A. P a \<sqinter> Q a\<close>
  by (auto simp add: Process_eq_spec F_GlobalNdet D_GlobalNdet F_Ndet D_Ndet)



section \<open>Commutativity\<close>

lemma GlobalNdet_sets_commute:
  \<open>(\<sqinter> a \<in> A. \<sqinter> b \<in> B. P a b) = \<sqinter> b \<in> B. \<sqinter> a \<in> A. P a b\<close>
  by (auto simp add: Process_eq_spec F_GlobalNdet D_GlobalNdet 
                     F_Ndet D_Ndet F_STOP D_STOP)



section \<open>Behaviour with Injectivity\<close>

lemma inj_on_mapping_over_GlobalNdet: 
  \<open>inj_on f A \<Longrightarrow> (\<sqinter> x \<in> A. P x) = \<sqinter> x \<in> f ` A. P (inv_into A f x)\<close>
  by (simp add: Process_eq_spec F_GlobalNdet D_GlobalNdet
                F_Ndet D_Ndet F_STOP D_STOP)






section \<open>Cartesian Product Results\<close>

lemma GlobalNdet_cartprod_\<sigma>s_set_\<sigma>s_set:
  \<open>(\<sqinter> (s, t) \<in> A \<times> B. P (s @ t)) = \<sqinter> u \<in> {s @ t |s t. (s, t) \<in> A \<times> B}. P u\<close>
  apply (subst Process_eq_spec, simp add: F_GlobalNdet D_GlobalNdet)
  by safe auto


lemma GlobalNdet_cartprod_s_set_\<sigma>s_set:
  \<open>(\<sqinter> (s, t) \<in> A \<times> B. P (s # t)) = \<sqinter> u \<in> {s # t |s t. (s, t) \<in> A \<times> B}. P u\<close>
  apply (subst Process_eq_spec, simp add: F_GlobalNdet D_GlobalNdet)
  by safe auto


lemma GlobalNdet_cartprod_s_set_s_set:
  \<open>(\<sqinter> (s, t) \<in> A \<times> B. P [s, t]) = \<sqinter> u \<in> {[s, t] |s t. (s, t) \<in> A \<times> B}. P u\<close>
  apply (subst Process_eq_spec, simp add: F_GlobalNdet D_GlobalNdet)
  by safe auto


lemma GlobalNdet_cartprod: \<open>(\<sqinter>(s, t) \<in> A \<times> B. P s t) = \<sqinter>s \<in> A. \<sqinter>t \<in> B. P s t\<close>
  apply (subst Process_eq_spec, simp add: F_GlobalNdet D_GlobalNdet)
  by safe auto
  

  
section \<open>Link with \<^const>\<open>MultiNdet\<close>\<close>

text \<open>This operator is in fact an extension of \<^const>\<open>MultiNdet\<close> to arbitrary sets:
      when \<^term>\<open>A\<close> is \<^const>\<open>finite\<close>, we have
      @{term [eta_contract = false] \<open>(\<sqinter>a \<in> A. P a) = \<Sqinter>a \<in> A. P a\<close>}.\<close>

lemma finite_GlobalNdet_is_MultiNdet:
  \<open>finite A \<Longrightarrow> (\<sqinter> p \<in> A. P p) = \<Sqinter> p \<in> A. P p\<close>
  by (simp add: Process_eq_spec F_GlobalNdet F_MultiNdet D_GlobalNdet D_MultiNdet)


text \<open>We obtain immediately the continuity when \<^term>\<open>A\<close> is \<^const>\<open>finite\<close>
      (and this is a necessary hypothesis for continuity).\<close>

lemma GlobalNdet_cont[simp]:
  \<open>\<lbrakk>finite A; \<forall>x. cont (f x)\<rbrakk> \<Longrightarrow> cont (\<lambda>y. (\<sqinter> z \<in> A. (f z y)))\<close>
  by (simp add: finite_GlobalNdet_is_MultiNdet) 
                                    


section \<open>Link with \<^const>\<open>Mndetprefix\<close>\<close>

text \<open>This is a trick to make proof of \<^const>\<open>Mndetprefix\<close> using
      \<^const>\<open>GlobalNdet\<close> as it has an easier denotational definition.\<close>

lemma Mndetprefix_GlobalNdet: \<open>\<sqinter> x \<in> A \<rightarrow> P x = \<sqinter> x \<in> A. (x \<rightarrow> P x)\<close>
  apply (cases \<open>A = {}\<close>, simp)
  by (subst Process_eq_spec_optimized) 
     (simp_all add: F_Mndetprefix D_Mndetprefix F_GlobalNdet D_GlobalNdet)
  
lemma write0_GlobalNdet:
  \<open>A \<noteq> {} \<Longrightarrow> (\<sqinter> x\<in>A. (a \<rightarrow> P x)) = (a \<rightarrow> (\<sqinter> x\<in>A. P x))\<close>
  by (auto simp add: Process_eq_spec write0_def 
                     F_GlobalNdet D_GlobalNdet F_Mprefix D_Mprefix)


section \<open>Properties\<close>

lemma GlobalNdet_Det:
  \<open>A \<noteq> {} \<Longrightarrow> (\<sqinter> a \<in> A. P a) \<box> Q = \<sqinter> a \<in> A. P a \<box> Q\<close>
  by (auto simp add: Process_eq_spec F_GlobalNdet D_GlobalNdet
                     F_Det D_Det Un_def T_GlobalNdet) 

lemma Mndetprefix_STOP: \<open>A \<subseteq> C \<Longrightarrow> (\<sqinter> a \<in> A \<rightarrow> P a) \<lbrakk>C\<rbrakk> STOP = STOP\<close>
proof (subst STOP_iff_T, intro subset_antisym subsetI)
  show \<open>s \<in> {[]} \<Longrightarrow> s \<in> \<T> (Mndetprefix A P \<lbrakk>C\<rbrakk> STOP)\<close> for s
    by (simp add: Nil_elem_T)
next
  show \<open>A \<subseteq> C \<Longrightarrow> s \<in> \<T> (Mndetprefix A P \<lbrakk>C\<rbrakk> STOP) \<Longrightarrow> s \<in> {[]}\<close> for s
    by (auto simp add: STOP_iff_T T_Sync T_Mndetprefix D_Mndetprefix
                       T_STOP D_STOP write0_def T_Mprefix D_Mprefix subset_iff
                split: if_split_asm) 
       (metis Sync.sym emptyLeftNonSync hd_in_set imageI insert_iff)+
qed


lemma GlobalNdet_Sync_distr:
  \<open>A \<noteq> {} \<Longrightarrow> (\<sqinter> x \<in> A. P x) \<lbrakk> C \<rbrakk> Q = \<sqinter> x \<in> A. (P x \<lbrakk> C \<rbrakk> Q)\<close>
  apply (auto simp: Process_eq_spec T_GlobalNdet
                    F_GlobalNdet D_GlobalNdet D_Sync F_Sync) \<comment> \<open>takes some seconds\<close>
  using front_tickFree_Nil by blast+ 

lemma Mndetprefix_Mprefix_Sync_distr:
  \<open>\<lbrakk>A \<subseteq> B; B \<subseteq> C\<rbrakk> \<Longrightarrow> (\<sqinter> a \<in> A \<rightarrow> P a) \<lbrakk> C \<rbrakk> (\<box> b \<in> B \<rightarrow> Q b) =
                      \<sqinter> a \<in> A \<rightarrow> (P a \<lbrakk> C \<rbrakk> Q a)\<close>
  \<comment> \<open>does not hold in general when \<^term>\<open>A \<subseteq> C\<close>\<close>
  apply (cases \<open>A = {}\<close>, simp,
         metis (no_types, lifting) Mprefix_STOP Mprefix_Sync_distr_subset
                                   empty_subsetI inf_bot_left)
  apply (cases \<open>B = {}\<close>, simp add: Mprefix_STOP Mndetprefix_STOP)
  apply (subst Mndetprefix_GlobalNdet, subst GlobalNdet_Sync_distr, assumption)
  apply (subst Mndetprefix_GlobalNdet, subst Mprefix_singl[symmetric]) 
  apply (unfold write0_def, rule mono_GlobalNdet_eq[rule_format])
  apply (subst Mprefix_Sync_distr_subset[of _ C B P Q], blast, blast)
  by (metis (no_types, lifting) in_mono inf_le1 insert_disjoint(1)
                                Mprefix_singl subset_singletonD)


corollary Mndetprefix_Mprefix_Par_distr:
  \<open>A \<subseteq> B \<Longrightarrow> ((\<sqinter> a \<in> A \<rightarrow> P a) || (\<box> b \<in> B \<rightarrow> Q b)) = \<sqinter> a \<in> A \<rightarrow> P a || Q a\<close>
  by (simp add: Mndetprefix_Mprefix_Sync_distr)


lemma Mndetprefix_Sync_Det_distr:
  \<open>(\<sqinter> a \<in> A \<rightarrow> (P a \<lbrakk> C \<rbrakk> (\<sqinter> b \<in> B \<rightarrow> Q b))) \<box>
   (\<sqinter> b \<in> B \<rightarrow> ((\<sqinter> a \<in> A \<rightarrow> P a) \<lbrakk> C \<rbrakk> Q b))
   \<sqsubseteq>\<^sub>F\<^sub>D (\<sqinter> a \<in> A \<rightarrow> P a) \<lbrakk> C \<rbrakk> (\<sqinter> b \<in> B \<rightarrow> Q b)\<close>
  if set_hyps : \<open>A \<noteq> {}\<close> \<open>B \<noteq> {}\<close> \<open>A \<inter> C = {}\<close> \<open>B \<inter> C = {}\<close>
   \<comment> \<open>both surprising: equality does not hold + deterministic choice\<close>
proof -
  have mono_GlobalNdet_FD:
    \<open>\<And>P Q A. \<forall>x \<in> A. P x \<sqsubseteq>\<^sub>F\<^sub>D Q x \<Longrightarrow> GlobalNdet A P \<sqsubseteq>\<^sub>F\<^sub>D GlobalNdet A Q\<close>
    by (auto simp: failure_divergence_refine_def le_ref_def F_GlobalNdet D_GlobalNdet)

  have * : \<open>a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow>
           (\<sqinter>b \<in> B.  (a \<rightarrow> (P a \<lbrakk>C\<rbrakk> (b \<rightarrow> Q b)))) \<box>
           (\<sqinter>a \<in> A.  (b \<rightarrow> ((a \<rightarrow> P a) \<lbrakk>C\<rbrakk> Q b))) \<sqsubseteq>\<^sub>F\<^sub>D
           (a \<rightarrow> P a) \<lbrakk>C\<rbrakk> (b \<rightarrow> Q b)\<close> for a b
    apply (subst Mprefix_Sync_distr_indep[of \<open>{a}\<close> C \<open>{b}\<close>, unfolded Mprefix_singl])
    using that(3) 
      apply (simp add: disjoint_iff; fail)
    using that(4) 
     apply (simp add: disjoint_iff; fail)
    apply (rule mono_Det_FD)
    unfolding failure_divergence_refine_def le_ref_def
    by (auto simp add: D_GlobalNdet F_GlobalNdet)

  have \<open>(\<sqinter>a \<in> A. \<sqinter>b \<in> B. (a \<rightarrow> (P a \<lbrakk>C\<rbrakk> (b \<rightarrow> Q b)))) \<box>
        (\<sqinter>b \<in> B. \<sqinter>a \<in> A. (b \<rightarrow> ((a \<rightarrow> P a) \<lbrakk>C\<rbrakk> Q b))) \<sqsubseteq>\<^sub>F\<^sub>D
        \<sqinter>b \<in> B. \<sqinter>a \<in> A.  ((a \<rightarrow> P a) \<lbrakk>C\<rbrakk> (b \<rightarrow> Q b))\<close>
    apply (subst Det_commute, subst GlobalNdet_Det, simp add: set_hyps(2))
    apply (subst Det_commute, subst GlobalNdet_Det, simp add: set_hyps(1))
    apply (intro ballI impI mono_GlobalNdet_FD) 
    using "*" by blast

  thus ?thesis
    apply (simp add: Mndetprefix_GlobalNdet GlobalNdet_Sync_distr)
    apply (subst (1 2 3) Sync_commute, simp add: GlobalNdet_Sync_distr set_hyps(2))
    apply (subst (1 2 3) Sync_commute, simp add: GlobalNdet_Sync_distr set_hyps(1))
    by (simp add: set_hyps(1, 2) write0_GlobalNdet)
qed





lemma GlobalNdet_Mprefix_distr:
  \<open>A \<noteq> {} \<Longrightarrow> (\<sqinter> a \<in> A. \<box> b \<in> B \<rightarrow> P a b) = \<box> b \<in> B \<rightarrow> (\<sqinter> a \<in> A. P a b)\<close>
  by (auto simp add: Process_eq_spec F_GlobalNdet D_GlobalNdet F_Mprefix D_Mprefix)



lemma GlobalNdet_Det_distrib:
  \<open>(\<sqinter> a \<in> A. P a \<box> Q a) = (\<sqinter> a \<in> A. P a) \<box> (\<sqinter> a \<in> A. Q a)\<close>
  if \<open>\<exists>Q' b. \<forall>a. Q a = (b \<rightarrow> Q' a)\<close>
proof -
  from that obtain b Q' where \<open>\<forall>a. (Q a = (b \<rightarrow> Q' a))\<close> by blast
  thus ?thesis
    apply (cases \<open>A = {}\<close>, simp add: Det_STOP)
    apply (simp add: Process_eq_spec F_Det D_Det write0_def
                     F_GlobalNdet D_GlobalNdet T_GlobalNdet, safe)
    by (auto simp add: F_Mprefix D_Mprefix T_Mprefix)
qed



end

