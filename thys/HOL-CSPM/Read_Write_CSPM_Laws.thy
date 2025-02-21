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
    by (auto simp add: read_def "*" intro!: mono_Mprefix_eq mono_GlobalNdet_eq)
      (metis (lifting) SUP_upper UN_I inv_into_f_eq subset_inj_on \<open>inj_on c (\<Union>a\<in>A. B a)\<close>)
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

(* TODO: add read laws  *)




(*<*)
end
  (*>*)