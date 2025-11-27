(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSPM - Architectural operators for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff.
 *
 * This file       : Laws for architectural operators
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

chapter \<open>CSPM Laws\<close>

(*<*)
theory Read_Write_CSPM_Laws
  imports Step_CSPM_Laws_Extended
begin
  (*>*)


subsection \<open>The Throw Operator\<close>

lemma Throw_read :
  \<open>inj_on c A \<Longrightarrow> (c\<^bold>?a \<in> A \<rightarrow> P a) \<Theta> a \<in> B. Q a =
                  c\<^bold>?a \<in> A \<rightarrow> (if c a \<in> B then Q (c a) else P a \<Theta> a \<in> B. Q a)\<close>
  by (auto simp add: read_def Throw_Mprefix intro: mono_Mprefix_eq)

lemma Throw_ndet_write :
  \<open>inj_on c A \<Longrightarrow> (c\<^bold>!\<^bold>!a \<in> A \<rightarrow> P a) \<Theta> a \<in> B. Q a =
                  c\<^bold>!\<^bold>!a \<in> A \<rightarrow> (if c a \<in> B then Q (c a) else P a \<Theta> a \<in> B. Q a)\<close>
  by (auto simp add: ndet_write_def Throw_Mndetprefix intro: mono_Mndetprefix_eq)

lemma Throw_write :
  \<open>(c\<^bold>!a \<rightarrow> P) \<Theta> a \<in> B. Q a = c\<^bold>!a \<rightarrow> (if c a \<in> B then Q (c a) else P \<Theta> a \<in> B. Q a)\<close>
  by (auto simp add: write_def Throw_Mprefix intro: mono_Mprefix_eq)

lemma Throw_write0 :
  \<open>(a \<rightarrow> P) \<Theta> a \<in> B. Q a = a \<rightarrow> (if a \<in> B then Q a else P \<Theta> a \<in> B. Q a)\<close>
  by (auto simp add: write0_def Throw_Mprefix intro: mono_Mprefix_eq)



subsection \<open>The Interrupt Operator\<close>

lemma Interrupt_read :
  \<open>(c\<^bold>?a \<in> A \<rightarrow> P a) \<triangle> Q = Q \<box> (c\<^bold>?a \<in> A \<rightarrow> P a \<triangle> Q)\<close>
  by (auto simp add: read_def Interrupt_Mprefix
      intro!: mono_Mprefix_eq arg_cong[where f = \<open>\<lambda>P. Q \<box> P\<close>])

lemma Interrupt_ndet_write :
  \<open>(c\<^bold>!\<^bold>!a \<in> A \<rightarrow> P a) \<triangle> Q = Q \<box> (c\<^bold>!\<^bold>!a \<in> A \<rightarrow> P a \<triangle> Q)\<close>
  by (auto simp add: ndet_write_def Interrupt_Mndetprefix
      intro!: mono_Mndetprefix_eq arg_cong[where f = \<open>\<lambda>P. Q \<box> P\<close>])

lemma Interrupt_write : \<open>(c\<^bold>!a \<rightarrow> P) \<triangle> Q = Q \<box> (c\<^bold>!a \<rightarrow> P \<triangle> Q)\<close>
  by (auto simp add: write_def Interrupt_Mprefix intro: mono_Mprefix_eq)

lemma Interrupt_write0 : \<open>(a \<rightarrow> P) \<triangle> Q = Q \<box> (a \<rightarrow> P \<triangle> Q)\<close>
  by (auto simp add: write0_def Interrupt_Mprefix intro: mono_Mprefix_eq)



subsection \<open>Global Deterministic Choice\<close>

lemma GlobalDet_read :  
  \<open>\<box>a \<in> A. c\<^bold>?b \<in> B a \<rightarrow> P a b = c\<^bold>?b \<in> (\<Union>a\<in>A. B a) \<rightarrow> \<sqinter>a\<in>{a \<in> A. b \<in> B a}. P a b\<close>
  if \<open>inj_on c (\<Union>a\<in>A. B a)\<close>
proof -
  have * : \<open>a \<in> A \<Longrightarrow> b \<in> B a \<Longrightarrow>
            {a \<in> A. inv_into (\<Union> (B ` A)) c (c b) \<in> B a} = {a \<in> A. c b \<in> c ` B a}\<close> for a b
    by (metis (no_types, opaque_lifting) SUP_upper UN_iff
        inj_on_image_mem_iff inv_into_f_eq \<open>inj_on c (\<Union>a\<in>A. B a)\<close>)
  have \<open>\<box>a \<in> A. c\<^bold>?b \<in> B a \<rightarrow> P a b =
        \<box>b\<in>(\<Union>x\<in>A. c ` B x) \<rightarrow> \<sqinter>a\<in>{a \<in> A. b \<in> c ` B a}. P a (inv_into (B a) c b)\<close>
    by (simp add: read_def GlobalDet_Mprefix)
  also have \<open>(\<Union>x\<in>A. c ` B x) = c ` (\<Union>a\<in>A. B a)\<close> by blast
  finally show \<open>\<box>a \<in> A. c\<^bold>?b \<in> B a \<rightarrow> P a b = c\<^bold>?b \<in> (\<Union>a\<in>A. B a) \<rightarrow> \<sqinter>a\<in>{a \<in> A. b \<in> B a}. P a b\<close>
    apply (auto simp add: read_def "*" intro!: mono_Mprefix_eq mono_GlobalNdet_eq)
    by (metis (lifting) UN_I UN_upper inj_on_subset inv_into_f_eq that)
qed


lemma GlobalDet_write :  
  \<open>\<box>a \<in> A. c\<^bold>!(b a) \<rightarrow> P a = c\<^bold>?x \<in> b ` A \<rightarrow> \<sqinter>a\<in>{a \<in> A. x = b a}. P a\<close> if \<open>inj_on c (b ` A)\<close>
proof -
  from \<open>inj_on c (b ` A)\<close> have * : \<open>x \<in> A \<Longrightarrow> {a \<in> A. inv_into (b ` A) c (c (b x)) = b a} =
                                              {a \<in> A. c (b x) = c (b a)}\<close> for x
    by (auto simp add: inj_on_eq_iff)
  have \<open>\<box>a \<in> A. c\<^bold>!(b a) \<rightarrow> P a = \<box>x\<in>(\<Union>a\<in>A. {c (b a)}) \<rightarrow> GlobalNdet {a \<in> A. x = c (b a)} P\<close>
    by (simp add: write_def GlobalDet_Mprefix)
  also have \<open>(\<Union>a\<in>A. {c (b a)}) = c ` b ` A\<close> by blast
  finally show \<open>\<box>a \<in> A. c\<^bold>!(b a) \<rightarrow> P a = c\<^bold>?x \<in> b ` A \<rightarrow> \<sqinter>a\<in>{a \<in> A. x = b a}. P a\<close>
    by (auto simp add: read_def "*" intro: mono_Mprefix_eq)
qed


lemma GlobalDet_write0 :  
  \<open>\<box>a\<in>A. b a \<rightarrow> P a = \<box>x \<in> (b ` A) \<rightarrow> \<sqinter>a \<in> {a \<in> A. x = b a}. P a\<close>
  by (auto simp add: GlobalDet_write[where c = \<open>\<lambda>x. x\<close>, simplified write_is_write0] read_def
      intro!: mono_Mprefix_eq) (metis (lifting) f_inv_into_f image_eqI)



subsection \<open>Multiple Synchronization Product\<close>

lemma MultiSync_read_subset :
  \<open>(\<^bold>\<lbrakk>S\<^bold>\<rbrakk> m \<in># M. c\<^bold>?a \<in> A m \<rightarrow> P m a) = (if M = {#} then STOP else
   c\<^bold>?a \<in> (\<Inter>m \<in> set_mset M. A m) \<rightarrow> (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> m \<in># M. P m a))\<close> (is \<open>?lhs = ?rhs\<close>)
  if \<open>inj_on c (\<Union>m \<in> set_mset M. A m)\<close> \<open>\<And>m. m \<in># M \<Longrightarrow> c ` A m \<subseteq> S\<close>
proof -
  have * : \<open>M \<noteq> {#} \<Longrightarrow> (\<Inter>m\<in>set_mset M. c ` A m) = c ` \<Inter> (A ` set_mset M)\<close>
    by (metis SUP_upper image_INT multiset_nonemptyE that(1))
  have \<open>?lhs = (if M = {#} then STOP else
                \<box>a\<in>(\<Inter>m\<in>set_mset M. c ` A m) \<rightarrow> \<^bold>\<lbrakk>S\<^bold>\<rbrakk> m\<in>#M. (P m \<circ> inv_into (A m) c) a)\<close>
    by (simp add: read_def MultiSync_Mprefix_subset that(2))
  also have \<open>\<dots> = ?rhs\<close>
    apply (auto simp add: read_def "*" intro!: mono_Mprefix_eq mono_MultiSync_eq) 
    by (metis (full_types) INF_lower2 INT_I UN_upper inj_on_subset inv_into_f_f that(1))
  finally show \<open>?lhs = ?rhs\<close> .
qed

lemmas MultiPar_read_subset = MultiSync_read_subset[where S = UNIV, simplified]


lemma MultiSync_read_indep :
  \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk> m \<in># mset_set M. c\<^bold>?a \<in> (A m) \<rightarrow> P m a =
   c\<^bold>?a \<in> (\<Union>m \<in> M. A m) \<rightarrow> \<sqinter>m \<in> {m \<in> M. a \<in> A m}. (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> n \<in># mset_set M. (if n = m then P m a else c\<^bold>?b \<in> (A n) \<rightarrow> P n b))\<close>
  (is \<open>?lhs = ?rhs\<close>) if \<open>inj_on c (\<Union>m \<in> M. A m)\<close> \<open>finite M\<close> \<open>\<And>m. m \<in> M \<Longrightarrow> c ` A m \<inter> S = {}\<close>
proof -
  have * : \<open>(\<Union>x\<in>M. c ` A x) = c ` \<Union> (A ` M)\<close> by auto
  have ** : \<open>m \<in> M \<Longrightarrow> a \<in> A m \<Longrightarrow> {m \<in> M. c a \<in> c ` A m} = {m \<in> M. inv_into (\<Union> (A ` M)) c (c a) \<in> A m}\<close> for a m
    by (auto simp add: image_iff) (metis UN_I inv_into_f_f that(1))+
  have \<open>?lhs = \<box>a\<in>(\<Union>x\<in>M. c ` A x)
       \<rightarrow> \<sqinter>m\<in>{m \<in> M. a \<in> c ` A m}.
             \<^bold>\<lbrakk>S\<^bold>\<rbrakk> n\<in>#mset_set M. (if n = m then (P m \<circ> inv_into (A m) c) a else Mprefix (c ` A n) (P n \<circ> inv_into (A n) c))\<close>
    by (simp add: read_def MultiSync_Mprefix_indep that(2, 3))
  also have \<open>\<dots> = ?rhs\<close>
    by (auto simp add: read_def "*" "**" intro!: mono_Mprefix_eq mono_GlobalNdet_eq mono_MultiSync_eq)
      (metis UN_upper UnionI imageI inj_on_subset inv_into_f_eq that(1))
  finally show \<open>?lhs = ?rhs\<close> .
qed

lemmas MultiInter_read_indep = MultiSync_read_indep[where S = \<open>{}\<close>, simplified]


lemma inv_into_eq_inv_into :
  \<open>inj_on f A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> C \<subseteq> A \<Longrightarrow> a \<in> B \<Longrightarrow> a \<in> C \<Longrightarrow>
   inv_into B f (f a) = inv_into C f (f a)\<close>
  by (metis inj_on_subset inv_into_f_f)



lemma MultiSync_ndet_write_subset :
  \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk> m \<in># M. c\<^bold>!\<^bold>!a \<in> A m \<rightarrow> P m a = (if M = {#} then STOP else
      if \<exists>a. \<forall>m m'. m \<in># M \<longrightarrow> m' \<in># M - {#m#} \<longrightarrow> A m = {a} \<and> A m' = {a}
    then  c\<^bold>!\<^bold>!a \<in> (\<Inter>m \<in> set_mset M. A m) \<rightarrow> (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> m \<in># M. P m a)
    else (c\<^bold>!\<^bold>!a \<in> (\<Inter>m \<in> set_mset M. A m) \<rightarrow> (\<^bold>\<lbrakk>S\<^bold>\<rbrakk> m \<in># M. P m a)) \<sqinter> STOP)\<close>
  (is \<open>?lhs M = (if M = {#} then STOP else if ?cond M then ?rhs M else ?rhs M \<sqinter> STOP)\<close>)
  if \<open>inj_on c (\<Union>m \<in> set_mset M. A m)\<close> \<open>\<And>m. m \<in># M \<Longrightarrow> c ` A m \<subseteq> S\<close>
proof (induct M rule: induct_subset_mset_empty_single)
  case 1 show ?case by simp
next
  case (2 m) show ?case by simp
next
  case (3 M' m)
  from "3"(1-3) that(2) have subset_props : \<open>A m \<subseteq> (\<Union>m \<in> set_mset M. A m)\<close>
    \<open>\<Inter> (A ` set_mset M') \<subseteq> (\<Union>m \<in> set_mset M. A m)\<close>
    \<open>\<Inter> (A ` set_mset (add_mset m M')) \<subseteq> (\<Union>m \<in> set_mset M. A m)\<close>
    \<open>c ` (\<Union>m \<in> set_mset M. A m) \<subseteq> S\<close>
    by auto (meson mset_subset_eqD multiset_nonemptyE)
  note inj_props = subset_props(1, 2)[THEN inj_on_subset[OF that(1)]]
  
  have $ : \<open>c ` A m = c ` \<Inter> (A ` set_mset M') \<longleftrightarrow> A m = \<Inter> (A ` set_mset M')\<close>
    by (simp only: inj_on_image_eq_iff[OF that(1) subset_props(1, 2)])
  have $$ : \<open>c ` (A m \<inter> \<Inter> (A ` set_mset M')) = c ` A m \<inter> c ` (\<Inter> (A ` set_mset M'))\<close>
    by (fact inj_on_image_Int[OF that(1) subset_props(1, 2)])
  from "3"(1, 2)
  have * : \<open>ndet_write c (A m) (P m) \<lbrakk>S\<rbrakk> ?rhs M' =
            (if \<exists>a. A m = {a} \<and> \<Inter> (A ` set_mset M') = {a}
             then c\<^bold>!(THE a. \<Inter> (A ` set_mset M') = {a}) \<rightarrow>
                  (P m (THE a. A m = {a}) \<lbrakk>S\<rbrakk>
                   \<^bold>\<lbrakk>S\<^bold>\<rbrakk> m\<in>#M'. P m (THE a. \<Inter> (A ` set_mset M') = {a}))
             else (c\<^bold>!\<^bold>!x\<in>(\<Inter> (A ` set_mset (add_mset m M'))) \<rightarrow> \<^bold>\<lbrakk>S\<^bold>\<rbrakk> m\<in>#add_mset m M'. P m x) \<sqinter> STOP)\<close>
    unfolding ndet_write_Sync_ndet_write_subset
              [OF subset_props(1, 2)[THEN image_mono, THEN subset_trans[OF _ subset_props(4)]]]
    by (auto simp add: "3"(3) write_is_write0 ndet_write_def "$$"
           intro!: arg_cong[where f = \<open>\<lambda>P. P \<sqinter> STOP\<close>] mono_Mndetprefix_eq
                   arg_cong2[where f = \<open>\<lambda>P Q. P \<lbrakk>S\<rbrakk> Q\<close>] mono_MultiSync_eq arg_cong[where f = \<open>\<lambda>a. P _ a\<close>]
                   inv_into_eq_inv_into[OF that(1) subset_props(1, 3), simplified]
                   inv_into_eq_inv_into[OF that(1) subset_props(2, 3), simplified])
      (metis "$" empty_is_image image_insert inj_props(1) inv_into_image_cancel subset_iff,
       ((metis INT_I inv_into_f_f subset_iff subset_props(1, 2) that(1))+)[2],
        metis UN_I inj_onD mset_subset_eqD that(1))
  have ** : \<open>?cond (add_mset m M') \<longleftrightarrow>
             (if size M' = 1 then \<exists>a. A m = {a} \<and> A (THE m. M' = {#m#}) = {a}
              else ?cond M' \<and> (\<exists>a. A m = {a} \<and> \<Inter> (A ` set_mset M') = {a}))\<close>
    by (cases M', auto simp add: "3"(3) split: if_split_asm)
      (metis Int_absorb all_not_in_conv insertI1 set_mset_eq_empty_iff singletonD)
  from "3.hyps"(1) that(2) have *** : \<open>ndet_write c (A m) (P m) \<lbrakk>S\<rbrakk> STOP = STOP\<close>
    by (auto simp add: ndet_write_Sync_STOP inj_props(1) ndet_write_is_STOP_iff Ndet_is_STOP_iff Int_absorb2)
  have \<open>?lhs (add_mset m M') = ndet_write c (A m) (P m) \<lbrakk>S\<rbrakk> \<^bold>\<lbrakk>S\<^bold>\<rbrakk> m'\<in># M'. ndet_write c (A m') (P m')\<close>
    by (simp add: "3"(3))
  also have \<open>\<dots> = ndet_write c (A m) (P m) \<lbrakk>S\<rbrakk>
                  (if ?cond M' then ?rhs M' else ?rhs M' \<sqinter> STOP)\<close>
    by (simp add: "3"(3, 4))
  also have \<open>\<dots> = (if ?cond (add_mset m M') then ?rhs (add_mset m M')
                   else ?rhs (add_mset m M') \<sqinter> STOP)\<close> (is \<open>?lhs' m M' = ?rhs' m M'\<close>)
  proof (split if_split, intro conjI impI)
    show \<open>?cond (add_mset m M') \<Longrightarrow> ?lhs' m M' = ?rhs (add_mset m M')\<close>
      unfolding "**"
      by (cases M', auto simp add: "3"(3) write_Sync_write split: if_split_asm)
        (metis "3.hyps"(1) image_insert insert_subset that(2))+
  next
    show \<open>\<not> ?cond (add_mset m M') \<Longrightarrow> ?lhs' m M' = ?rhs (add_mset m M') \<sqinter> STOP\<close>
      unfolding "**"
      by (cases \<open>size M' = 1\<close>, simp_all add: "*")
        (cases M', auto simp add: "*" "***" ndet_write_Sync_STOP Sync_distrib_Ndet_left
                        write_Sync_STOP "3"(3) write_Sync_write_subset Ndet_aci(1-4))
  qed
  also have \<open>\<dots> = (  if add_mset m M' = {#} then STOP 
                   else   if ?cond (add_mset m M') then ?rhs (add_mset m M')
                        else ?rhs (add_mset m M')  \<sqinter> STOP)\<close> by simp
  finally show ?case .
qed

lemmas MultiPar_ndet_write_subset = MultiSync_ndet_write_subset[where S = UNIV, simplified]


(*<*)
end
  (*>*)
