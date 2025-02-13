(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff, Lina Ye.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : Support for read and write operations
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

section\<open>Read and Write Laws\<close>

(*<*)
theory Read_Write_CSP_Laws
  imports Step_CSP_Laws_Extended
begin
  (*>*)


subsection \<open>Projections\<close>

subsubsection \<open>\<^const>\<open>read\<close>\<close>

lemma F_read :
  \<open>\<F> (c\<^bold>?a\<in>A \<rightarrow> P a) = {([], X) |X. X \<inter> ev ` c ` A = {}} \<union>
                      {(ev a # s, X) |a s X. a \<in> c ` A \<and> (s, X) \<in> \<F> ((P \<circ> inv_into A c) a)}\<close>
  by (simp add: read_def F_Mprefix)

lemma F_read_inj_on :
  \<open>inj_on c A \<Longrightarrow>
   \<F> (c\<^bold>?a\<in>A \<rightarrow> P a) = {([], X) |X. X \<inter> ev ` c ` A = {}} \<union>
                      {(ev (c a) # s, X) |a s X. a \<in> A \<and> (s, X) \<in> \<F> (P a)}\<close>
  by (auto simp add: F_read)


lemma D_read :
  \<open>\<D> (c\<^bold>?a\<in>A \<rightarrow> P a) = {ev a # s |a s. a \<in> c ` A \<and> s \<in> \<D> ((P \<circ> inv_into A c) a)}\<close>
  by (simp add: read_def D_Mprefix)

lemma D_read_inj_on :
  \<open>inj_on c A \<Longrightarrow> \<D> (c\<^bold>?a\<in>A \<rightarrow> P a) = {ev (c a) # s |a s. a \<in> A \<and> s \<in> \<D> (P a)}\<close>
  by (auto simp add: D_read)


lemma T_read :
  \<open>\<T> (c\<^bold>?a\<in>A \<rightarrow> P a) = insert [] {ev a # s |a s. a \<in> c ` A \<and> s \<in> \<T> ((P \<circ> inv_into A c) a)}\<close>
  by (simp add: read_def T_Mprefix)

lemma T_read_inj_on :
  \<open>inj_on c A \<Longrightarrow> \<T> (c\<^bold>?a\<in>A \<rightarrow> P a) = insert [] {ev (c a) # s |a s. a \<in> A \<and> s \<in> \<T> (P a)}\<close>
  by (auto simp add: T_read)


lemmas read_projs = F_read D_read T_read
  and read_inj_on_projs = F_read_inj_on D_read_inj_on T_read_inj_on



subsubsection \<open>\<^const>\<open>ndet_write\<close>\<close>

lemma F_ndet_write :
  \<open>\<F> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) =
   (  if A = {} then {(s, X). s = []}
    else {([], X) |X. \<exists>a\<in>A. ev (c a) \<notin> X} \<union>
         {(ev a # s, X) |a s X. a \<in> c ` A \<and> (s, X) \<in> \<F> ((P \<circ> inv_into A c) a)})\<close>
  by (simp add: ndet_write_def F_Mndetprefix')

lemma F_ndet_write_inj_on :
  \<open>inj_on c A \<Longrightarrow>
   \<F> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) =
   (  if A = {} then {(s, X). s = []}
    else {([], X) |X. \<exists>a\<in>A. ev (c a) \<notin> X} \<union>
         {(ev (c a) # s, X) |a s X. a \<in> A \<and> (s, X) \<in> \<F> (P a)})\<close>
  by (auto simp add: F_ndet_write)


lemma D_ndet_write :
  \<open>\<D> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) = {ev a # s |a s. a \<in> c ` A \<and> s \<in> \<D> ((P \<circ> inv_into A c) a)}\<close>
  by (simp add: ndet_write_def D_Mndetprefix')

lemma D_ndet_write_inj_on :
  \<open>inj_on c A \<Longrightarrow> \<D> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) = {ev (c a) # s |a s. a \<in> A \<and> s \<in> \<D> (P a)}\<close>
  by (auto simp add: D_ndet_write)


lemma T_ndet_write :
  \<open>\<T> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) = insert [] {ev a # s |a s. a \<in> c ` A \<and> s \<in> \<T> ((P \<circ> inv_into A c) a)}\<close>
  by (simp add: ndet_write_def T_Mndetprefix')

lemma T_ndet_write_inj_on :
  \<open>inj_on c A \<Longrightarrow> \<T> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) = insert [] {ev (c a) # s |a s. a \<in> A \<and> s \<in> \<T> (P a)}\<close>
  by (auto simp add: T_ndet_write)


lemmas ndet_write_projs = F_ndet_write D_ndet_write T_ndet_write
  and ndet_write_inj_on_projs = F_ndet_write_inj_on D_ndet_write_inj_on T_ndet_write_inj_on



subsubsection \<open>\<^const>\<open>write\<close> and \<^const>\<open>write0\<close>\<close>

lemma F_write :
  \<open>\<F> (c\<^bold>!a \<rightarrow> P) = {([], X) |X. ev (c a) \<notin> X} \<union> {(ev (c a) # s, X) |s X. (s, X) \<in> \<F> P}\<close>
  by (simp add: write_def F_Mprefix)

lemma F_write0 :
  \<open>\<F> (a \<rightarrow> P) = {([], X) |X. ev a \<notin> X} \<union> {(ev a # s, X) |s X. (s, X) \<in> \<F> P}\<close>
  by (simp add: write0_def F_Mprefix)


lemma D_write : \<open>\<D> (c\<^bold>!a \<rightarrow> P) = {ev (c a) # s |s. s \<in> \<D> P}\<close>
  by (simp add: write_def D_Mprefix)

lemma D_write0 : \<open>\<D> (a \<rightarrow> P) = {ev a # s |s. s \<in> \<D> P}\<close>
  by (simp add: write0_def D_Mprefix)


lemma T_write : \<open>\<T> (c\<^bold>!a \<rightarrow> P) = insert [] {ev (c a) # s |s. s \<in> \<T> P}\<close>
  by (simp add: write_def T_Mprefix)

lemma T_write0 : \<open>\<T> (a \<rightarrow> P) = insert [] {ev a # s |s. s \<in> \<T> P}\<close>
  by (simp add: write0_def T_Mprefix)


lemmas write_projs = F_write D_write T_write
  and write0_projs = F_write0 D_write0 T_write0




subsection \<open>Equality with Constant Process\<close>

subsubsection \<open>\<^const>\<open>STOP\<close>\<close>

lemma read_is_STOP_iff : \<open>c\<^bold>?a\<in>A \<rightarrow> P a = STOP \<longleftrightarrow> A = {}\<close>
  by (simp add: read_def Mprefix_is_STOP_iff)

lemma read_empty [simp] : \<open>c\<^bold>?a\<in>{} \<rightarrow> P a = STOP\<close> by (simp add: read_def)

lemma ndet_write_is_STOP_iff : \<open>c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a = STOP \<longleftrightarrow> A = {}\<close>
  by (simp add: ndet_write_def Mndetprefix_is_STOP_iff)

lemma ndet_write_empty [simp] : \<open>c\<^bold>!\<^bold>!a\<in>{} \<rightarrow> P a = STOP\<close> by (simp add: ndet_write_def)

lemma write0_neq_STOP [simp] : \<open>a \<rightarrow> P \<noteq> STOP\<close> by (simp add: write0_def Mprefix_is_STOP_iff)

lemma write_neq_STOP [simp] : \<open>c\<^bold>!a \<rightarrow> P \<noteq> STOP\<close> by (simp add: write_is_write0)



subsubsection \<open>\<^const>\<open>SKIP\<close>\<close>

lemma read_neq_SKIP [simp] : \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<noteq> SKIP r\<close> by (simp add: read_def)

lemma ndet_write_neq_SKIP [simp] : \<open>c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<noteq> SKIP r\<close> by (simp add: ndet_write_def)

lemma write0_neq_SKIP [simp] : \<open>a \<rightarrow> P \<noteq> SKIP r\<close> by (simp add: write0_def)

lemma write_neq_SKIP [simp] : \<open>c\<^bold>!a \<rightarrow> P \<noteq> SKIP r\<close> by (simp add: write_is_write0)



subsubsection \<open>\<^term>\<open>\<bottom>\<close>\<close>

lemma read_neq_BOT [simp] : \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<noteq> \<bottom>\<close> by (simp add: read_def)

lemma ndet_write_neq_BOT [simp] : \<open>c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<noteq> \<bottom>\<close> by (simp add: ndet_write_def)

lemma write0_neq_BOT [simp] : \<open>a \<rightarrow> P \<noteq> \<bottom>\<close> by (simp add: write0_def)

lemma write_neq_BOT [simp] : \<open>c\<^bold>!a \<rightarrow> P \<noteq> \<bottom>\<close> by (simp add: write_is_write0)




subsection \<open>Extensions of Step-Laws\<close>

subsubsection \<open>Monotony for equality\<close>

lemma mono_read_eq :
  \<open>(\<And>a. a \<in> A \<Longrightarrow> P a = Q a) \<Longrightarrow> read c A P = read c A Q\<close>
  by (auto simp add: read_def inv_into_into intro!: mono_Mprefix_eq)

lemma mono_ndet_write_eq :
  \<open>(\<And>a. a \<in> A \<Longrightarrow> P a = Q a) \<Longrightarrow> ndet_write c A P = ndet_write c A Q\<close>
  by (auto simp add: ndet_write_def inv_into_into intro!: mono_Mndetprefix_eq)


subsubsection \<open>\<^const>\<open>Det\<close> and \<^const>\<open>Ndet\<close>\<close>

lemma read_Ndet_read :
  \<open>(c\<^bold>?a\<in>A \<rightarrow> P a) \<sqinter> (c\<^bold>?b\<in>B \<rightarrow> Q b) =
   (c\<^bold>?a\<in>(A - B) \<rightarrow> P a) \<sqinter> (c\<^bold>?b\<in>(B - A) \<rightarrow> Q b) \<box> (c\<^bold>?x\<in>(A \<inter> B) \<rightarrow> P x \<sqinter> Q x)\<close>
  (is \<open>?lhs = ?rhs\<close>) if \<open>inj_on c (A \<union> B)\<close>
proof -
  have   * : \<open>c ` A - c ` B = c ` (A - B)\<close>
    by (metis Diff_subset inj_on_image_set_diff le_supI1 sup.cobounded2 \<open>inj_on c (A \<union> B)\<close>)
  have  ** : \<open>c ` B - c ` A = c ` (B - A)\<close>
    by (metis Diff_subset Un_upper1 inj_on_image_set_diff le_supI2 \<open>inj_on c (A \<union> B)\<close>)
  have *** : \<open>c ` A \<inter> c ` B = c ` (A \<inter> B)\<close>
    by (metis inf_sup_ord(3) inj_on_image_Int sup_ge2 \<open>inj_on c (A \<union> B)\<close>)
  from \<open>inj_on c (A \<union> B)\<close> have \<open>inj_on c (A - B)\<close> by (simp add: inj_on_Un inj_on_diff)
  with \<open>inj_on c (A \<union> B)\<close> have   $ : \<open>a \<in> A - B \<Longrightarrow> inv_into A c (c a) = inv_into (A - B) c (c a)\<close> for a
    by (auto simp add: inj_on_Un)
  from \<open>inj_on c (A \<union> B)\<close> have \<open>inj_on c (B - A)\<close> by (simp add: inj_on_Un inj_on_diff)
  with \<open>inj_on c (A \<union> B)\<close> have  $$ : \<open>b \<in> B - A \<Longrightarrow> inv_into B c (c b) = inv_into (B - A) c (c b)\<close> for b
    by (auto simp add: inj_on_Un)
  have $$$ : \<open>inv_into A c (c a) = inv_into (A \<inter> B) c (c a)\<close>
    \<open>inv_into B c (c a) = inv_into (A \<inter> B) c (c a)\<close> if \<open>a \<in> A \<inter> B\<close> for a
    using \<open>a \<in> A \<inter> B\<close> \<open>inj_on c (A \<union> B)\<close> by (auto simp add: inj_on_Un inj_on_Int)
  show \<open>?lhs = ?rhs\<close>
    by (unfold read_def, subst Mprefix_Ndet_Mprefix)
      (auto simp add: "*" "**" "***" "$" "$$" "$$$"
        intro!: mono_Mprefix_eq arg_cong[where f = P] arg_cong2[where f = \<open>(\<box>)\<close>]
        arg_cong2[where f = \<open>(\<sqinter>)\<close>])
qed

lemma read_Det_read :
  \<open>(c\<^bold>?a\<in>A \<rightarrow> P a) \<box> (c\<^bold>?b\<in>B \<rightarrow> Q b) =
   c\<^bold>?a\<in>(A \<union> B) \<rightarrow> (if a \<in> A \<inter> B then P a \<sqinter> Q a else if a \<in> A then P a else Q a)\<close>
  (is \<open>?lhs = ?rhs\<close>) if \<open>inj_on c (A \<union> B)\<close>
proof -
  have * : \<open>c ` A \<union> c ` B = c ` (A \<union> B)\<close> by blast
  from \<open>inj_on c (A \<union> B)\<close>
  have $ : \<open>a \<in> A \<Longrightarrow> inv_into A c (c a) = inv_into (A \<union> B) c (c a)\<close>
    \<open>b \<in> B \<Longrightarrow> inv_into B c (c b) = inv_into (A \<union> B) c (c b)\<close> for a b
    by (simp_all add: inj_on_Un)
  from \<open>inj_on c (A \<union> B)\<close> show \<open>?lhs = ?rhs\<close>
    by (auto simp add: read_def Mprefix_Det_Mprefix "*" "$"
        intro!: mono_Mprefix_eq) (metis Un_iff inj_onD)+
qed


lemma ndet_write_Det_ndet_write :
  \<open>(c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) \<box> (c\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b) =
   (  if A = {} then (c\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b)
    else   if B = {} then (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a)
         else \<sqinter>a\<in>A. \<sqinter>b\<in>B. (if a = b then c\<^bold>!a \<rightarrow> P a \<sqinter> Q a else (c\<^bold>!a \<rightarrow> P a) \<box> (c\<^bold>!b \<rightarrow> Q b)))\<close>
  if \<open>inj_on c (A \<union> B)\<close>
proof -
  have * : \<open>a \<in> A \<Longrightarrow> inv_into A c (c a) = inv_into (A \<union> B) c (c a)\<close>
    \<open>b \<in> B \<Longrightarrow> inv_into B c (c b) = inv_into (A \<union> B) c (c b)\<close> for a b
    using \<open>inj_on c (A \<union> B)\<close> by (auto simp add: inj_on_Un)
  from \<open>inj_on c (A \<union> B)\<close> show ?thesis
    by (auto simp add: ndet_write_def Mndetprefix_Det_Mndetprefix "*" write_is_write0 inj_on_eq_iff
        split: if_split_asm intro!: mono_GlobalNdet_eq2)
qed

lemma ndet_write_Ndet_ndet_write :
  \<open>(c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) \<sqinter> (c\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b) =
   (  if A = B then (c\<^bold>!\<^bold>!b\<in>B \<rightarrow> P b \<sqinter> Q b)
    else   if A \<subseteq> B
         then (c\<^bold>!\<^bold>!b\<in>(B - A) \<rightarrow> Q b) \<sqinter> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<sqinter> Q a)
         else   if B \<subseteq> A
              then (c\<^bold>!\<^bold>!a\<in>(A - B) \<rightarrow> P a) \<sqinter> (c\<^bold>!\<^bold>!b\<in>B \<rightarrow> P b \<sqinter> Q b)
              else (c\<^bold>!\<^bold>!a\<in>(A - B) \<rightarrow> P a) \<sqinter> (c\<^bold>!\<^bold>!b\<in>(B - A) \<rightarrow> Q b) \<sqinter> (c\<^bold>!\<^bold>!a\<in>(A \<inter> B) \<rightarrow> P a \<sqinter> Q a))\<close>
  if \<open>A \<inter> B \<noteq> {}\<close> \<open>inj_on c (A \<union> B)\<close>
proof -
  have * : \<open>a \<in> A \<Longrightarrow> inv_into A c (c a) = inv_into (A \<union> B) c (c a)\<close>
    \<open>b \<in> B \<Longrightarrow> inv_into B c (c b) = inv_into (A \<union> B) c (c b)\<close>
    \<open>a \<in> A - B \<Longrightarrow> inv_into (A - B) c (c a) = inv_into A c (c a)\<close>
    \<open>b \<in> B - A \<Longrightarrow> inv_into (B - A) c (c b) = inv_into B c (c b)\<close>
    \<open>x \<in> A \<inter> B \<Longrightarrow> inv_into (A \<union> B) c (c x) = inv_into (A \<inter> B) c (c x)\<close> for a b x
    using \<open>inj_on c (A \<union> B)\<close> by (auto simp add: inj_on_Un inj_on_diff inj_on_Int)
  from \<open>inj_on c (A \<union> B)\<close> have $ : \<open>c ` A \<subseteq> c ` B \<longleftrightarrow> A \<subseteq> B\<close> \<open>c ` B \<subseteq> c ` A \<longleftrightarrow> B \<subseteq> A\<close>
    by (auto simp add: inj_on_eq_iff)
  hence $$ : \<open>c ` A = c ` B \<longleftrightarrow> A = B\<close> by blast
  from \<open>inj_on c (A \<union> B)\<close> 
  have $$$ : \<open>c ` A - c ` B = c ` (A - B)\<close> \<open>c ` B - c ` A = c ` (B - A)\<close> \<open>c ` A \<inter> c ` B = c ` (A \<inter> B)\<close>
    by (auto simp add: inj_on_eq_iff)
  from \<open>A \<inter> B \<noteq> {}\<close> have \<open>c ` A \<inter> c ` B \<noteq> {}\<close> by blast
  show ?thesis
    by (auto simp add: Mndetprefix_Ndet_Mndetprefix[OF \<open>c ` A \<inter> c ` B \<noteq> {}\<close>]
        "$" "$$" "$$$" "*" comp_def ndet_write_def
        intro!: mono_Mndetprefix_eq arg_cong2[where f = \<open>(\<sqinter>)\<close>])
qed



lemma write0_Ndet_write0 : \<open>(a \<rightarrow> P) \<sqinter> (a \<rightarrow> Q) = a \<rightarrow> P \<sqinter> Q\<close>
  by (auto simp: Process_eq_spec write0_def D_Ndet F_Ndet F_Mprefix D_Mprefix Un_def)

lemma write0_Det_write0_is_write0_Ndet_write0 : \<open>(a \<rightarrow> P) \<box> (a \<rightarrow> Q) = (a \<rightarrow> P) \<sqinter> (a \<rightarrow> Q)\<close>
  by (simp add: write0_def Mprefix_Det_Mprefix) (simp add: Mprefix_singl write0_Ndet_write0)

lemma write_Ndet_write : \<open>(c\<^bold>!a \<rightarrow> P) \<sqinter> (c\<^bold>!a \<rightarrow> Q) = c\<^bold>!a \<rightarrow> P \<sqinter> Q\<close>
  by (simp add: write0_Ndet_write0 write_is_write0)

lemma write_Det_write_is_write_Ndet_write: \<open>(c\<^bold>!a \<rightarrow> P) \<box> (c\<^bold>!a \<rightarrow> Q) = (c\<^bold>!a \<rightarrow> P) \<sqinter> (c\<^bold>!a \<rightarrow> Q)\<close>
  by (simp add: write0_Det_write0_is_write0_Ndet_write0 write_is_write0)



lemma write_Ndet_read :
  \<open>(c\<^bold>!a \<rightarrow> P) \<sqinter> (c\<^bold>?b\<in>B \<rightarrow> Q b) =
   (if a \<in> B then STOP else c\<^bold>!a \<rightarrow> P) \<sqinter> (c\<^bold>?b\<in>(B - {a}) \<rightarrow> Q b) \<box> (if a \<in> B then c\<^bold>!a \<rightarrow> P \<sqinter> Q a else STOP)\<close>
  if \<open>inj_on c ({a} \<union> B)\<close>
  by (subst read_Ndet_read[OF \<open>inj_on c ({a} \<union> B)\<close>, simplified])
    (auto simp add: insert_Diff_if intro: arg_cong2[where f = \<open>(\<box>)\<close>] arg_cong2[where f = \<open>(\<sqinter>)\<close>])

lemma read_Ndet_write :
  \<open>inj_on c (A \<union> {b}) \<Longrightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a) \<sqinter> (c\<^bold>!b \<rightarrow> Q) =
   (if b \<in> A then STOP else c\<^bold>!b \<rightarrow> Q) \<sqinter> (c\<^bold>?a\<in>(A - {b}) \<rightarrow> P a) \<box> (if b \<in> A then c\<^bold>!b \<rightarrow> P b \<sqinter> Q else STOP)\<close>
  by (subst Ndet_commute, subst write_Ndet_read) (simp_all add: Ndet_commute)

lemma write0_Ndet_read :
  \<open>(a \<rightarrow> P) \<sqinter> (id\<^bold>?b\<in>B \<rightarrow> Q b) =
   (if a \<in> B then STOP else a \<rightarrow> P) \<sqinter> (id\<^bold>?b\<in>(B - {a}) \<rightarrow> Q b) \<box> (if a \<in> B then a \<rightarrow> P \<sqinter> Q a else STOP)\<close>
  by (subst write_Ndet_read[where c = id, unfolded write_is_write0, simplified]) simp

lemma read_Ndet_write0 :
  \<open>(id\<^bold>?a\<in>A \<rightarrow> P a) \<sqinter> (b \<rightarrow> Q) =
   (if b \<in> A then STOP else b \<rightarrow> Q) \<sqinter> (id\<^bold>?a\<in>(A - {b}) \<rightarrow> P a) \<box> (if b \<in> A then b \<rightarrow> P b \<sqinter> Q else STOP)\<close>
  by (subst read_Ndet_write[where c = id, unfolded write_is_write0, simplified]) simp 


lemma write_Det_read :
  \<open>inj_on c (insert a B) \<Longrightarrow> (c\<^bold>!a \<rightarrow> P) \<box> (c\<^bold>?b\<in>B \<rightarrow> Q b) =
   c\<^bold>?b\<in>(insert a B) \<rightarrow> (if b = a \<and> a \<in> B then P \<sqinter> Q a else if b = a then P else Q b)\<close>
  by (subst read_Det_read[where A = \<open>{a}\<close>, simplified]) (auto intro: mono_read_eq)

lemma read_Det_write :
  \<open>inj_on c (insert b A) \<Longrightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a) \<box> (c\<^bold>!b \<rightarrow> Q) =
   c\<^bold>?a\<in>(insert b A) \<rightarrow> (if a = b \<and> b \<in> A then P a \<sqinter> Q else if a = b then Q else P a)\<close>
  by (subst read_Det_read[where B = \<open>{b}\<close>, simplified]) (auto intro: mono_read_eq)

lemma write0_Det_read :
  \<open>(a \<rightarrow> P) \<box> (id\<^bold>?b\<in>B \<rightarrow> Q b) =
   id\<^bold>?b\<in>(insert a B) \<rightarrow> (if b = a \<and> a \<in> B then P \<sqinter> Q a else if b = a then P else Q b)\<close>
  by (subst write_Det_read[where c = id, unfolded write_is_write0, simplified]) simp

lemma read_Det_write0 :
  \<open>(id\<^bold>?a\<in>A \<rightarrow> P a) \<box> (b \<rightarrow> Q) =
   id\<^bold>?a\<in>(insert b A) \<rightarrow> (if a = b \<and> b \<in> A then P a \<sqinter> Q else if a = b then Q else P a)\<close>
  by (subst read_Det_write[where c = id, unfolded write_is_write0, simplified]) simp


(* TODO: really useful ? and do we want versions for ndet_write and write/write0 ? *)



subsubsection \<open> @{const [source] \<open>Sliding\<close>} \<close>

lemma write0_Sliding_write0 :
  \<open>(a \<rightarrow> P) \<rhd> (b \<rightarrow> Q) =
   (\<box>x \<in> {a, b} \<rightarrow> (if a = b then P \<sqinter> Q else if x = a then P else Q)) \<sqinter>
   (b \<rightarrow> (if a = b then P \<sqinter> Q else Q))\<close>
  by (auto simp add: Process_eq_spec write0_def
      Sliding_projs Ndet_projs Mprefix_projs)

lemma write_Sliding_write :
  \<open>(c\<^bold>!a \<rightarrow> P) \<rhd> (d\<^bold>!b \<rightarrow> Q) =
   (\<box>x \<in> {c a, d b} \<rightarrow> (if c a = d b then P \<sqinter> Q else if x = c a then P else Q)) \<sqinter>
   (d\<^bold>!b \<rightarrow> (if c a = d b then P \<sqinter> Q else Q))\<close>
  by (simp add: write_is_write0 write0_Sliding_write0)

lemma write0_Sliding_write :
  \<open>(a \<rightarrow> P) \<rhd> (d\<^bold>!b \<rightarrow> Q) =
   (\<box>x \<in> {a, d b} \<rightarrow> (if a = d b then P \<sqinter> Q else if x = a then P else Q)) \<sqinter>
   (d\<^bold>!b \<rightarrow> (if a = d b then P \<sqinter> Q else Q))\<close>
  by (simp add: write_is_write0 write0_Sliding_write0)

lemma write_Sliding_write0 :
  \<open>(c\<^bold>!a \<rightarrow> P) \<rhd> (b \<rightarrow> Q) =
   (\<box>x \<in> {c a, b} \<rightarrow> (if c a = b then P \<sqinter> Q else if x = c a then P else Q)) \<sqinter>
   (b \<rightarrow> (if c a = b then P \<sqinter> Q else Q))\<close>
  by (simp add: write_is_write0 write0_Sliding_write0)



lemma read_Sliding_superset_read :
  \<comment> \<open>Not really interesting without the additional assumptions.\<close>
  \<open>A \<subseteq> B \<Longrightarrow> inj_on c B \<Longrightarrow>
   (c\<^bold>?a\<in>A \<rightarrow> P a) \<rhd> (c\<^bold>?b\<in>B \<rightarrow> Q b) = c\<^bold>?b\<in>B \<rightarrow> (if b \<in> A then P b \<sqinter> Q b else Q b)\<close>
  by (unfold read_def, subst Mprefix_Sliding_superset_Mprefix)
    (auto simp add: inj_on_eq_iff subset_iff intro!: mono_Mprefix_eq, metis inj_on_subset inv_into_f_f subset_eq)

lemma read_Sliding_same_set_read :
  \<open>inj_on c A \<Longrightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a) \<rhd> (c\<^bold>?a\<in>A \<rightarrow> Q a) = c\<^bold>?a\<in>A \<rightarrow> P a \<sqinter> Q a\<close>
  by (unfold read_def Mprefix_Sliding_same_set_Mprefix)
    (auto simp add: inj_on_eq_iff subset_iff intro: mono_Mprefix_eq)

lemma ndet_write_Sliding_superset_ndet_write :
  \<open>A \<subseteq> B \<Longrightarrow> inj_on c B \<Longrightarrow>
   (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) \<rhd> (c\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b) = c\<^bold>!\<^bold>!b\<in>B \<rightarrow> (if b \<in> A then P b \<sqinter> Q b else Q b)\<close>
  by (unfold ndet_write_def, subst Mndetprefix_Sliding_superset_Mndetprefix)
    (auto simp add: inj_on_eq_iff subset_iff intro!: mono_Mndetprefix_eq, metis inj_on_subset inv_into_f_f subset_eq)

lemma ndet_write_Sliding_same_set_ndet_write :
  \<open>inj_on c A \<Longrightarrow> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) \<rhd> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> Q a) = c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<sqinter> Q a\<close>
  by (unfold ndet_write_def Mndetprefix_Sliding_same_set_Mndetprefix)
    (auto simp add: inj_on_eq_iff subset_iff intro: mono_Mndetprefix_eq)


lemma write_Sliding_superset_read :
  \<open>a \<in> B \<Longrightarrow> inj_on c B \<Longrightarrow>
   (c\<^bold>!a \<rightarrow> P) \<rhd> (c\<^bold>?b\<in>B \<rightarrow> Q b) = c\<^bold>?b\<in>B \<rightarrow> (if b = a then P \<sqinter> Q b else Q b)\<close>
  by (subst read_Sliding_superset_read[where A = \<open>{a}\<close>, simplified]) simp_all

lemma write0_Sliding_superset_read :
  \<open>a \<in> B \<Longrightarrow> (a \<rightarrow> P) \<rhd> (id\<^bold>?b\<in>B \<rightarrow> Q b) = id\<^bold>?b\<in>B \<rightarrow> (if b = a then P \<sqinter> Q b else Q b)\<close>
  by (subst read_Sliding_superset_read
      [where A = \<open>{a}\<close> and c = id, simplified, unfolded write_is_write0, simplified]) simp_all

lemma write_Sliding_superset_ndet_write :
  \<open>a \<in> B \<Longrightarrow> inj_on c B \<Longrightarrow>
   (c\<^bold>!a \<rightarrow> P) \<rhd> (c\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b) = c\<^bold>!\<^bold>!b\<in>B \<rightarrow> (if b = a then P \<sqinter> Q b else Q b)\<close>
  by (subst ndet_write_Sliding_superset_ndet_write[where A = \<open>{a}\<close>, simplified]) simp_all

lemma write0_Sliding_superset_ndet_write :
  \<open>a \<in> B \<Longrightarrow> (a \<rightarrow> P) \<rhd> (id\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b) = id\<^bold>!\<^bold>!b\<in>B \<rightarrow> (if b = a then P \<sqinter> Q b else Q b)\<close>
  by (subst ndet_write_Sliding_superset_ndet_write
      [where A = \<open>{a}\<close> and c = id, simplified, unfolded write_is_write0, simplified]) simp_all



subsubsection \<open> @{const [source] \<open>Seq\<close>} \<close>

lemma read_Seq : \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<^bold>; Q = c\<^bold>?a\<in>A \<rightarrow> (P a \<^bold>; Q)\<close>
  by (simp add: read_def Mprefix_Seq comp_def)

lemma write0_Seq : \<open>a \<rightarrow> P \<^bold>; Q = a \<rightarrow> (P \<^bold>; Q)\<close>
  by (simp add: write0_def Mprefix_Seq)

lemma ndet_write_Seq : \<open>c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<^bold>; Q = c\<^bold>!\<^bold>!a\<in>A \<rightarrow> (P a \<^bold>; Q)\<close>
  by (simp add: ndet_write_is_GlobalNdet_write0 Seq_distrib_GlobalNdet_right write0_Seq)

lemma write_Seq : \<open>c\<^bold>!a \<rightarrow> P \<^bold>; Q = c\<^bold>!a \<rightarrow> (P \<^bold>; Q)\<close>
  by (simp add: write0_Seq write_is_write0)



subsubsection \<open> \<^const>\<open>Renaming\<close> \<close>

lemma Renaming_read :
  \<open>Renaming (c\<^bold>?a\<in>A \<rightarrow> P a) f g = (f \<circ> c)\<^bold>?a\<in>A \<rightarrow> Renaming (P a) f g\<close>
  if \<open>inj_on c A\<close> and \<open>inj_on f (c ` A)\<close>
proof -
  have \<open>f ` c ` A = (f \<circ> c) ` A\<close> by auto
  have \<open>inj_on (f \<circ> c) A\<close> by (simp add: comp_inj_on \<open>inj_on c A\<close> \<open>inj_on f (c ` A)\<close>)
  have * : \<open>y \<in> (\<lambda>x. f (c x)) ` A \<Longrightarrow> {x \<in> c ` A. y = f x} = {inv_into (c ` A) f y}\<close> for y
    using \<open>inj_on f (c ` A)\<close> by auto
  show \<open>Renaming (c\<^bold>?a\<in>A \<rightarrow> P a) f g = (f \<circ> c)\<^bold>?a\<in>A \<rightarrow> Renaming (P a) f g\<close>
  proof (unfold read_def Renaming_Mprefix \<open>f ` c ` A = (f \<circ> c) ` A\<close>, rule mono_Mprefix_eq)
    from \<open>inj_on (f \<circ> c) A\<close>
    show \<open>a \<in> (f \<circ> c) ` A \<Longrightarrow>
          \<sqinter>a\<in>{x \<in> c ` A. a = f x}. Renaming ((P \<circ> inv_into A c) a) f g =
          ((\<lambda>a. Renaming (P a) f g) \<circ> inv_into A (f \<circ> c)) a\<close> for a
      by (auto simp add: "*" inv_into_f_eq \<open>inj_on c A\<close> \<open>inj_on f (c ` A)\<close>
          intro: arg_cong[where f = \<open>\<lambda>a. Renaming (P a) f g\<close>])
  qed
qed

lemma Renaming_write :
  \<open>Renaming (c\<^bold>!a \<rightarrow> P) f g = (f \<circ> c)\<^bold>!a \<rightarrow> Renaming P f g\<close>
  by (fact Renaming_read[where A = \<open>{a}\<close>, simplified])

lemma Renaming_write0 :
  \<open>Renaming (a \<rightarrow> P) f g = f a \<rightarrow> Renaming P f g\<close>
  by (fact Renaming_write[where c = id, unfolded write_is_write0, simplified])

lemma Renaming_ndet_write :
  \<open>Renaming (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) f g = (f \<circ> c)\<^bold>!\<^bold>!a\<in>A \<rightarrow> Renaming (P a) f g\<close>
  if \<open>inj_on c A\<close> and \<open>inj_on f (c ` A)\<close>
proof -
  have \<open>inj_on (f \<circ> c) A\<close> by (simp add: comp_inj_on \<open>inj_on c A\<close> \<open>inj_on f (c ` A)\<close>)
  have \<open>(\<lambda>x. f (c x)) ` A = f ` (c ` A)\<close> by auto
  show \<open>Renaming (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) f g = (f \<circ> c)\<^bold>!\<^bold>!a\<in>A \<rightarrow> Renaming (P a) f g\<close>
    by (simp add: \<open>?this\<close> ndet_write_is_GlobalNdet_write0 Renaming_distrib_GlobalNdet Renaming_write0, rule sym)
      (use \<open>inj_on (f \<circ> c) A\<close> \<open>inj_on c A\<close> in
        \<open>auto simp add: inv_into_f_eq
                 intro: mono_GlobalNdet_eq2 arg_cong[where f = \<open>\<lambda>a. _ \<rightarrow> Renaming (P a) f g\<close>]\<close>)
qed



subsubsection \<open> \<^const>\<open>Hiding\<close> \<close>

lemma Hiding_read_disjoint :
  \<open>c ` A \<inter> S = {} \<Longrightarrow> c\<^bold>?a\<in>A \<rightarrow> P a \ S = c\<^bold>?a\<in>A \<rightarrow> (P a \ S)\<close>
  by (unfold read_def, subst Hiding_Mprefix_disjoint)
    (auto simp add: disjoint_iff image_iff intro: mono_Mprefix_eq)

lemma \<open>A \<subseteq> B \<Longrightarrow> a \<in> A \<Longrightarrow> (inv_into A c) a = (inv_into B c) a\<close>
  oops \<comment> \<open>Not provable, therefore we need the injectivity for the non disjoint case.\<close>

lemma Hiding_read_non_disjoint :
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \ S = (c\<^bold>?a\<in>(A - c -` S) \<rightarrow> (P a \ S)) \<rhd> (\<sqinter>a\<in>(A \<inter> c -` S). (P a \ S))\<close>
  if \<open>inj_on c A\<close> and \<open>c ` A \<inter> S \<noteq> {}\<close>
proof -
  have * : \<open>(P \<circ> inv_into A c) x = (P \<circ> inv_into (A - c -` S) c) x\<close>
    if \<open>x \<in> c ` (A - c -` S)\<close> for x
  proof -
    from \<open>x \<in> c ` (A - c -` S)\<close> obtain a where \<open>a \<in> A - c -` S\<close> \<open>x = c a\<close> by blast
    from \<open>a \<in> A - c -` S\<close> have \<open>a \<in> A\<close> by blast
    from \<open>inj_on c A\<close> inj_on_subset have \<open>inj_on c (A - c -` S)\<close> by force
    from \<open>a \<in> A - c -` S\<close> \<open>x = c a\<close> \<open>inj_on c (A - c -` S)\<close>
    have \<open>(inv_into (A - c -` S) c) x = a\<close> by simp
    moreover from \<open>a \<in> A\<close> \<open>x = c a\<close> \<open>inj_on c A\<close> have \<open>(inv_into A c) x = a\<close> by simp
    ultimately show \<open>(P \<circ> inv_into A c) x = (P \<circ> inv_into (A - c -` S) c) x\<close> by simp
  qed
  have ** : \<open>c ` (A - c -` S) = c ` A - S\<close> by blast
  have *** : \<open>c ` A \<inter> S = c ` (A \<inter> (c -` S))\<close> by blast
  have \<open>(c\<^bold>?a\<in>A \<rightarrow> P a) \ S = (c\<^bold>?a\<in>(A - c -` S) \<rightarrow> (P a \ S)) \<rhd>
                             (\<sqinter>a\<in>(c ` A \<inter> S). (P (inv_into A c a) \ S))\<close>
  proof (unfold read_def comp_def, subst Hiding_Mprefix_non_disjoint,
      use \<open>c ` A \<inter> S \<noteq> {}\<close> in blast, rule arg_cong[where f = \<open>\<lambda>P. P \<rhd> _\<close>])
    show \<open>\<box>a\<in>(c ` A - S) \<rightarrow> (P (inv_into A c a) \ S) =
          \<box>x\<in>c ` (A - c -` S) \<rightarrow> (P (inv_into (A - c -` S) c x) \ S)\<close>
      by (use "*" in \<open>force simp add: "**" intro : mono_Mprefix_eq\<close>)
  qed
  also have \<open>(\<sqinter>a\<in>(c ` A \<inter> S). (P (inv_into A c a) \ S)) = \<sqinter>a\<in>(A \<inter> c -` S). (P a \ S)\<close>
    by (subst "***", rule mono_GlobalNdet_eq2) (simp add: \<open>inj_on c A\<close>)
  finally show \<open>(c\<^bold>?a\<in>A \<rightarrow> P a) \ S =
                (c\<^bold>?a\<in>(A - c -` S) \<rightarrow> (P a \ S)) \<rhd> (\<sqinter>a\<in>(A \<inter> c -` S). (P a \ S))\<close> .
qed

lemma Hiding_read_subset :
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \ S = \<sqinter>a\<in>(c ` A \<inter> S). (P (inv_into A c a) \ S)\<close>
  if \<open>inj_on c A\<close> and \<open>c ` A \<subseteq> S\<close>
proof (cases \<open>A = {}\<close>)
  show \<open>A = {} \<Longrightarrow> c\<^bold>?a\<in>A \<rightarrow> P a \ S = \<sqinter>a\<in>(c ` A \<inter> S). (P (inv_into A c a) \ S)\<close>
    by (auto simp add: Process_eq_spec GlobalNdet_projs F_Hiding_seqRun D_Hiding_seqRun read_def Mprefix_projs)
next
  assume \<open>A \<noteq> {}\<close>
  with \<open>c ` A \<subseteq> S\<close> have \<open>c ` A \<inter> S \<noteq> {}\<close> \<open>c ` A - S = {}\<close> by auto
  show \<open>c\<^bold>?a\<in>A \<rightarrow> P a \ S = \<sqinter>a\<in>(c ` A \<inter> S). (P (inv_into A c a) \ S)\<close>
    by (simp add: read_def Hiding_Mprefix_non_disjoint[OF \<open>c ` A \<inter> S \<noteq> {}\<close>] \<open>c ` A - S = {}\<close>
        Process_eq_spec Sliding_projs GlobalNdet_projs Mprefix_projs)
qed



lemma Hiding_ndet_write_disjoint :
  \<open>c ` A \<inter> S = {} \<Longrightarrow> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) \ S = (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> (P a \ S))\<close>
  by (unfold ndet_write_def, subst Hiding_Mndetprefix_disjoint)
    (auto simp add: disjoint_iff image_iff intro: mono_Mndetprefix_eq)

lemma Hiding_ndet_write_subset :
  \<open>c ` A \<subseteq> S \<Longrightarrow> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) \ S = \<sqinter>a\<in>c ` A. (P (inv_into A c a) \ S)\<close>
  by (unfold ndet_write_def, subst Hiding_Mndetprefix_subset)
    (auto simp add: disjoint_iff image_iff intro: mono_GlobalNdet_eq)

lemma Hiding_ndet_write_subset_bis :
  \<comment> \<open>With the injectivity...\<close>
  \<open>inj_on c A \<Longrightarrow> c ` A \<subseteq> S \<Longrightarrow> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) \ S = \<sqinter>a\<in>A. (P a \ S)\<close>
  by (simp add: Hiding_ndet_write_subset mono_GlobalNdet_eq2)

lemma \<open>A \<subseteq> B \<Longrightarrow> a \<in> A \<Longrightarrow> (inv_into A c) a = (inv_into B c) a\<close>
  oops \<comment> \<open>Not provable, therefore we need the injectivity for the non disjoint case.\<close>

lemma Hiding_ndet_write_non_disjoint_not_subset :
  \<open>(c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) \ S =
   (c\<^bold>!\<^bold>!a\<in>(A - c -` S) \<rightarrow> (P a \ S)) \<sqinter> (\<sqinter>a\<in>(A \<inter> c -` S). (P a \ S))\<close>
  if \<open>inj_on c A\<close> and \<open>c ` A \<inter> S \<noteq> {}\<close> and \<open>\<not> c ` A \<subseteq> S\<close>
proof -
  have * : \<open>(P \<circ> inv_into A c) x = (P \<circ> inv_into (A - c -` S) c) x\<close>
    if \<open>x \<in> c ` (A - c -` S)\<close> for x
  proof -
    from \<open>x \<in> c ` (A - c -` S)\<close> obtain a where \<open>a \<in> A - c -` S\<close> \<open>x = c a\<close> by blast
    from \<open>a \<in> A - c -` S\<close> have \<open>a \<in> A\<close> by blast
    from \<open>inj_on c A\<close> inj_on_subset have \<open>inj_on c (A - c -` S)\<close> by force
    from \<open>a \<in> A - c -` S\<close> \<open>x = c a\<close> \<open>inj_on c (A - c -` S)\<close>
    have \<open>(inv_into (A - c -` S) c) x = a\<close> by simp
    moreover from \<open>a \<in> A\<close> \<open>x = c a\<close> \<open>inj_on c A\<close> have \<open>(inv_into A c) x = a\<close> by simp
    ultimately show \<open>(P \<circ> inv_into A c) x = (P \<circ> inv_into (A - c -` S) c) x\<close> by simp
  qed
  have ** : \<open>c ` (A - c -` S) = c ` A - S\<close> by blast
  have *** : \<open>c ` A \<inter> S = c ` (A \<inter> c -` S)\<close> by blast
  have \<open>(c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) \ S = (c\<^bold>!\<^bold>!a\<in>(A - c -` S) \<rightarrow> (P a \ S)) \<sqinter>
                              (\<sqinter>a\<in>(c ` A \<inter> S). (P (inv_into A c a) \ S))\<close>
  proof (unfold ndet_write_def comp_def
      Hiding_Mndetprefix_non_disjoint_not_subset
      [OF \<open>c ` A \<inter> S \<noteq> {}\<close> \<open>\<not> c ` A \<subseteq> S\<close>])
    show \<open>(\<sqinter>a\<in>(c ` A - S) \<rightarrow> (P (inv_into A c a) \ S)) \<sqinter>
          (\<sqinter>a\<in>(c ` A \<inter> S). (P (inv_into A c a) \ S)) =
          (\<sqinter>x\<in>c ` (A - c -` S) \<rightarrow> (P (inv_into (A - c -` S) c x) \ S)) \<sqinter>
          (\<sqinter>a\<in>(c ` A \<inter> S). (P (inv_into A c a) \ S))\<close>
      by (rule arg_cong[where f = \<open>\<lambda>P. P \<sqinter> _\<close>])
        (use "*" in \<open>force simp add: "**" intro : mono_Mndetprefix_eq\<close>)
  qed
  also have \<open>(\<sqinter>a\<in>(c ` A \<inter> S). (P (inv_into A c a) \ S)) = \<sqinter>a\<in>(A \<inter> c -` S). (P a \ S)\<close>
    by (auto simp add: "***" \<open>inj_on c A\<close> intro: mono_GlobalNdet_eq2)
  finally show \<open>c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \ S =
                (c\<^bold>!\<^bold>!a\<in>(A - c -` S) \<rightarrow> (P a \ S)) \<sqinter> (\<sqinter>a\<in>(A \<inter> c -` S). (P a \ S))\<close> .
qed



lemma Hiding_write0_disjoint :
  \<open>a \<notin> S \<Longrightarrow> a \<rightarrow> P \ S = a \<rightarrow> (P \ S)\<close>
  by (simp add: write0_def Hiding_Mprefix_disjoint)

lemma Hiding_write0_non_disjoint :
  \<open>a \<in> S \<Longrightarrow> a \<rightarrow> P \ S = P \ S\<close>
  by (simp add: write0_def Hiding_Mprefix_non_disjoint)

lemma Hiding_write_disjoint :
  \<open>c a \<notin> S \<Longrightarrow> c\<^bold>!a \<rightarrow> P \ S = c\<^bold>!a \<rightarrow> (P \ S)\<close>
  by (simp add: Hiding_write0_disjoint write_is_write0)

lemma Hiding_write_subset :
  \<open>c a \<in> S \<Longrightarrow> c\<^bold>!a \<rightarrow> P \ S = P \ S\<close>
  by (simp add: Hiding_write0_non_disjoint write_is_write0)





subsubsection \<open> \<^const>\<open>Sync\<close> \<close>

paragraph \<open> \<^const>\<open>read\<close> \<close>

lemma read_Sync_read : 
  \<comment> \<open>This is the general case.\<close>
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b =
   (c\<^bold>?a\<in>(A - c -` S) \<rightarrow> (P a \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b)) \<box>
   (d\<^bold>?b\<in>(B - d -` S) \<rightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> Q b)) \<box>
   (\<box>x\<in>(c ` A \<inter> d ` B \<inter> S) \<rightarrow> (P (inv_into A c x) \<lbrakk>S\<rbrakk> Q (inv_into B d x)))\<close>
  (is \<open>?lhs = ?rhs1 \<box> ?rhs2 \<box> ?rhs3\<close>)
  if \<open>c ` A \<inter> S = {} \<or> c ` A \<subseteq> S \<or> inj_on c A\<close>
    \<open>d ` B \<inter> S = {} \<or> d ` B \<subseteq> S \<or> inj_on d B\<close>
    \<comment> \<open>Assumptions may seem strange, but the motivation is that when \<^term>\<open>A - c -` S \<noteq> {}\<close>
     (which is equivalent to \<^term>\<open>\<not> c ` A \<subseteq> S\<close>), we need to ensure that 
     \<^term>\<open>inv_into (A - c -` S) c\<close> is equal to \<^term>\<open>inv_into A c\<close>.
     This requires \<^term>\<open>A - c -` S = A\<close> (which is equivalent to \<^term>\<open>c ` A \<inter> S = {}\<close>)
     or \<^term>\<open>inj_on c A\<close>. We need obviously a similar assumption for \<^term>\<open>B\<close>.\<close>
proof -
  have * : \<open>\<And>e X. e ` (X - e -` S) = e ` X - S\<close> by auto
  have \<open>?lhs = (\<box>a\<in>(c ` A - S) \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk> (\<box>x\<in>d ` B \<rightarrow> Q (inv_into B d x)))) \<box>
               (\<box>b\<in>(d ` B - S) \<rightarrow> ((\<box>x\<in>c ` A \<rightarrow> P (inv_into A c x)) \<lbrakk>S\<rbrakk> Q (inv_into B d b))) \<box>
               (\<box>x\<in>(c ` A \<inter> d ` B \<inter> S) \<rightarrow> (P (inv_into A c x) \<lbrakk>S\<rbrakk> Q (inv_into B d x)))\<close>
    (is \<open>?lhs = ?rhs1' \<box> ?rhs2' \<box> ?rhs3\<close>)
    by (simp add: read_def Mprefix_Sync_Mprefix comp_def)
  also from that(1) have \<open>?rhs1' = ?rhs1\<close>
  proof (elim disjE)
    assume \<open>c ` A \<inter> S = {}\<close>
    hence \<open>A - c -` S = A \<and> c ` A - S = c ` A\<close> by fast
    thus \<open>?rhs1' = ?rhs1\<close> by (simp add: read_def comp_def)
  next
    assume \<open>c ` A \<subseteq> S\<close>
    hence \<open>A - c -` S = {} \<and> c ` A - S = {}\<close> by fast
    show \<open>?rhs1' = ?rhs1\<close> by (simp add: \<open>?this\<close>)
  next
    assume \<open>inj_on c A\<close>
    hence \<open>inj_on c (A - c -` S)\<close> by (simp add: inj_on_diff)
    with \<open>inj_on c A\<close> show \<open>?rhs1' = ?rhs1\<close>
      by (auto simp add: read_def comp_def "*" intro: mono_Mprefix_eq)
  qed
  also from that(2) have \<open>?rhs2' = ?rhs2\<close>
  proof (elim disjE)
    assume \<open>d ` B \<inter> S = {}\<close>
    hence \<open>B - d -` S = B \<and> d ` B - S = d ` B\<close> by fast
    thus \<open>?rhs2' = ?rhs2\<close> by (simp add: read_def comp_def)
  next
    assume \<open>d ` B \<subseteq> S\<close>
    hence \<open>B - d -` S = {} \<and> d ` B - S = {}\<close> by fast
    show \<open>?rhs2' = ?rhs2\<close> by (simp add: \<open>?this\<close>)
  next
    assume \<open>inj_on d B\<close>
    hence \<open>inj_on d (B - d -` S)\<close> by (simp add: inj_on_diff)
    with \<open>inj_on d B\<close> show \<open>?rhs2' = ?rhs2\<close>
      by (auto simp add: read_def comp_def "*" intro: mono_Mprefix_eq)
  qed
  finally show \<open>?lhs = ?rhs1 \<box> ?rhs2 \<box> ?rhs3\<close> .
qed


paragraph \<open>Enforce read\<close>

\<comment> \<open>With stronger assumptions, we can fully rewrite the right hand side with \<^const>\<open>read\<close>.\<close>
\<comment> \<open>Remember that now, channels \<^term>\<open>c\<close> and \<^term>\<open>d\<close> must have the same type.
   This was not the case on the previous lemma.\<close>
lemma read_Sync_read_forced_read_left : 
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b =
   (c\<^bold>?a\<in>(A - c -` S) \<rightarrow> (P a \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b)) \<box>
   (d\<^bold>?b\<in>(B - d -` S) \<rightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> Q b)) \<box>
   (c\<^bold>?x\<in>(A \<inter> c -` (d ` B \<inter> S)) \<rightarrow> (P x \<lbrakk>S\<rbrakk> Q x))\<close>
  (is \<open>?lhs = ?rhs1 \<box> ?rhs2 \<box> ?rhs3\<close>)
  if \<open>c ` A \<inter> S = {} \<or> inj_on c A\<close>
    \<open>d ` B \<inter> S = {} \<or> inj_on d B\<close>
    \<open>\<And>a b. a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> c a = d b \<Longrightarrow> d b \<in> S \<Longrightarrow> a = b\<close>
proof -
  let ?rhs3' = \<open>(\<box>x\<in>(c ` A \<inter> d ` B \<inter> S) \<rightarrow> (P (inv_into A c x) \<lbrakk>S\<rbrakk> Q (inv_into B d x)))\<close>
  have  * : \<open>c ` (A \<inter> c -` (d ` B \<inter> S)) = c ` A \<inter> d ` B \<inter> S\<close> by blast
  have ** : \<open>c ` (A \<inter> c -` d ` B) = c ` A \<inter> d ` B\<close> by blast
  from that(1, 2) consider \<open>c ` A \<inter> S = {} \<or> d ` B \<inter> S = {}\<close>
    | \<open>inj_on c A\<close> \<open>inj_on d B\<close> by blast
  hence \<open>?rhs3' = ?rhs3\<close>
  proof cases
    assume \<open>c ` A \<inter> S = {} \<or> d ` B \<inter> S = {}\<close>
    hence \<open>c ` A \<inter> d ` B \<inter> S = {} \<and> A \<inter> c -` (d ` B \<inter> S) = {}\<close> by blast
    thus \<open>?rhs3' = ?rhs3\<close> by simp
  next
    assume \<open>inj_on c A\<close> \<open>inj_on d B\<close>
    show \<open>?rhs3' = ?rhs3\<close>
    proof (unfold read_def "*" comp_def,
        intro mono_Mprefix_eq arg_cong2[where f = \<open>\<lambda>P Q. P \<lbrakk>S\<rbrakk> Q\<close>])
      fix x assume \<open>x \<in> c ` A \<inter> d ` B \<inter> S\<close>
      moreover from \<open>inj_on c A\<close> inj_on_Int
      have \<open>inj_on c A \<and> inj_on c (A \<inter> c -` (d ` B \<inter> S))\<close> by blast
      ultimately show \<open>P (inv_into A c x) = P (inv_into (A \<inter> c -` (d ` B \<inter> S)) c x)\<close>
        by (simp add: image_iff, elim conjE bexE, simp)
    next
      fix x assume $ : \<open>x \<in> c ` A \<inter> d ` B \<inter> S\<close>
      then obtain a b where $$ : \<open>x = c a\<close> \<open>a \<in> A\<close> \<open>x = d b\<close> \<open>b \<in> B\<close> by blast
      from \<open>inj_on c A\<close> inj_on_Int have $$$ : \<open>inj_on c (A \<inter> c -` (d ` B \<inter> S))\<close> by blast
      have \<open>inv_into B d x = b\<close> by (simp add: "$$"(3, 4) \<open>inj_on d B\<close>)
      also have \<open>b = a\<close> by (metis "$" "$$" Int_iff that(3))
      also have \<open>a = inv_into (A \<inter> c -` (d ` B \<inter> S)) c x\<close>
        by (metis "$" "$$"(1, 2) "$$$" "*" Int_lower1
            \<open>inj_on c A\<close> inj_on_image_mem_iff inv_into_f_eq)
      finally have \<open>inv_into B d x = inv_into (A \<inter> c -` (d ` B \<inter> S)) c x\<close> .
      thus \<open>Q (inv_into B d x) = Q (inv_into (A \<inter> c -` (d ` B \<inter> S)) c x)\<close> by simp
    qed
  qed
  moreover have \<open>?lhs = ?rhs1 \<box> ?rhs2 \<box> ?rhs3'\<close>
    using that(1, 2) by (subst read_Sync_read) auto
  ultimately show \<open>?lhs = ?rhs1 \<box> ?rhs2 \<box> ?rhs3\<close> by argo
qed


lemma read_Sync_read_forced_read_right:
  \<open>\<lbrakk>c ` A \<inter> S = {} \<or> inj_on c A; d ` B \<inter> S = {} \<or> inj_on d B;
    \<And>a b. a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> c a = d b \<Longrightarrow> d b \<in> S \<Longrightarrow> a = b\<rbrakk> \<Longrightarrow>
   c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b =
   (c\<^bold>?a\<in>(A - c -` S) \<rightarrow> (P a \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b)) \<box>
   (d\<^bold>?b\<in>(B - d -` S) \<rightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> Q b)) \<box>
   (d\<^bold>?x\<in>(B \<inter> d -` (c ` A \<inter> S)) \<rightarrow> (P x \<lbrakk>S\<rbrakk> Q x))\<close>
  by (subst Sync_commute, subst Det_commute, subst read_Sync_read_forced_read_left)
    (blast, blast, metis, auto simp add: Sync_commute intro: arg_cong2[where f = \<open>(\<box>)\<close>])


paragraph \<open>Special Cases\<close>

lemma read_Sync_read_subset : 
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b =
   \<box>x\<in>(c ` A \<inter> d ` B) \<rightarrow> (P (inv_into A c x) \<lbrakk>S\<rbrakk> Q (inv_into B d x))\<close>
  if \<open>c ` A \<subseteq> S\<close> \<open>d ` B \<subseteq> S\<close>
proof -
  from that have * : \<open>A - c -` S = {}\<close> \<open>B - d -` S = {}\<close> by auto
  from that(1) have ** : \<open>c ` A \<inter> d ` B \<inter> S = c ` A \<inter> d ` B\<close> by blast
  show ?thesis by (subst read_Sync_read)
      (use that in \<open>simp_all add: "*" "**"\<close>)
qed

lemma read_Sync_read_subset_forced_read_left : 
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b = c\<^bold>?x\<in>(A \<inter> c -` d ` B) \<rightarrow> (P x \<lbrakk>S\<rbrakk> Q x)\<close>
  if \<open>c ` A \<subseteq> S\<close> \<open>d ` B \<subseteq> S\<close> \<open>inj_on c A\<close> \<open>inj_on d B\<close>
    \<open>\<And>a b. a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> c a = d b \<Longrightarrow> d b \<in> S \<Longrightarrow> a = b\<close>
proof -
  from that have * : \<open>A - c -` S = {}\<close> \<open>B - d -` S = {}\<close> by auto
  from that(1) have ** : \<open>A \<inter> (c -` d ` B \<inter> c -` S) = A \<inter> c -` d ` B\<close> by blast
  show ?thesis by (subst read_Sync_read_forced_read_left)
      (use that(3, 4, 5) in \<open>simp_all add: "*" "**"\<close>)
qed

lemma read_Sync_read_subset_forced_read_right : 
  \<open>\<lbrakk>c ` A \<subseteq> S; d ` B \<subseteq> S; inj_on c A; inj_on d B;
    \<And>a b. a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> c a = d b \<Longrightarrow> d b \<in> S \<Longrightarrow> a = b\<rbrakk> \<Longrightarrow>
   c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b = d\<^bold>?x\<in>(B \<inter> d -` c ` A) \<rightarrow> (P x \<lbrakk>S\<rbrakk> Q x)\<close>
  by (subst Sync_commute, subst read_Sync_read_subset_forced_read_left)
    (simp_all add: Sync_commute, metis)


lemma read_Sync_read_indep : 
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b =
   (c\<^bold>?a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk> (d\<^bold>?b\<in>B \<rightarrow> Q b))) \<box> (d\<^bold>?b\<in>B \<rightarrow> ((c\<^bold>?a\<in>A \<rightarrow> P a) \<lbrakk>S\<rbrakk> Q b))\<close>
  if \<open>c ` A \<inter> S = {}\<close> \<open>d ` B \<inter> S = {}\<close>
proof -
  from that have * : \<open>A - c -` S = A\<close> \<open>B - d -` S = B\<close> by auto
  from that(1) have ** : \<open>c ` A \<inter> d ` B \<inter> S = {}\<close> by blast
  show ?thesis by (subst read_Sync_read) (use that in \<open>simp_all add: "*" "**"\<close>)
qed

lemma read_Sync_read_left : 
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b = c\<^bold>?a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk> (d\<^bold>?b\<in>B \<rightarrow> Q b))\<close>
  if \<open>c ` A \<inter> S = {}\<close> \<open>d ` B \<subseteq> S\<close>
proof -
  from that(1) have * : \<open>A - c -` S = A\<close> \<open>c ` A \<inter> d ` B \<inter> S = {}\<close> by auto
  from that(2) have ** : \<open>B - d -` S = {}\<close> by blast
  show ?thesis by (subst read_Sync_read)
      (use that in \<open>simp_all add: "*" "**"\<close>)
qed

lemma read_Sync_read_right :
  \<open>c ` A \<subseteq> S \<Longrightarrow> d ` B \<inter> S = {} \<Longrightarrow>
   c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b = d\<^bold>?b\<in>B \<rightarrow> ((c\<^bold>?a\<in>A \<rightarrow> P a) \<lbrakk>S\<rbrakk> Q b)\<close>
  by (subst Sync_commute, subst read_Sync_read_left)
    (simp_all add: Sync_commute)


corollary read_Par_read :
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a || d\<^bold>?b\<in>B \<rightarrow> Q b =
   \<box>x\<in>(c ` A \<inter> d ` B) \<rightarrow> (P (inv_into A c x) || Q (inv_into B d x))\<close>
  by (simp add: read_Sync_read_subset)

corollary read_Par_read_forced_read_left :
  \<open>\<lbrakk>inj_on c A; inj_on d B; \<And>a b. a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> c a = d b \<Longrightarrow> a = b\<rbrakk> \<Longrightarrow>
   c\<^bold>?a\<in>A \<rightarrow> P a || d\<^bold>?b\<in>B \<rightarrow> Q b = c\<^bold>?x\<in>(A \<inter> c -` d ` B) \<rightarrow> (P x || Q x)\<close>
  by (subst read_Sync_read_forced_read_left) simp_all

corollary read_Par_read_forced_read_right :
  \<open>\<lbrakk>inj_on c A; inj_on d B; \<And>a b. a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> c a = d b \<Longrightarrow> a = b\<rbrakk> \<Longrightarrow>
   c\<^bold>?a\<in>A \<rightarrow> P a || d\<^bold>?b\<in>B \<rightarrow> Q b = d\<^bold>?x\<in>(B \<inter> d -` c ` A) \<rightarrow> (P x || Q x)\<close>
  by (subst read_Sync_read_forced_read_right) simp_all


corollary read_Inter_read :
  \<open>\<lbrakk>inj_on c A; inj_on d B; \<And>a b. a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> c a = d b \<Longrightarrow> a = b\<rbrakk> \<Longrightarrow>
   c\<^bold>?a\<in>A \<rightarrow> P a ||| d\<^bold>?b\<in>B \<rightarrow> Q b =
   (c\<^bold>?a\<in>A \<rightarrow> (P a ||| d\<^bold>?b\<in>B \<rightarrow> Q b)) \<box> (d\<^bold>?b\<in>B \<rightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a ||| Q b))\<close>
  by (simp add: read_Sync_read)



paragraph \<open>Same channel\<close>

text \<open>Some results can be rewritten when we have the same channel.\<close>


lemma read_Sync_read_forced_read_same_chan : 
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> c\<^bold>?b\<in>B \<rightarrow> Q b =
   (c\<^bold>?a\<in>(A - c -` S) \<rightarrow> (P a \<lbrakk>S\<rbrakk> c\<^bold>?b\<in>B \<rightarrow> Q b)) \<box>
   (c\<^bold>?b\<in>(B - c -` S) \<rightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> Q b)) \<box>
   (c\<^bold>?x\<in>(A \<inter> B \<inter> c -` S) \<rightarrow> (P x \<lbrakk>S\<rbrakk> Q x))\<close>
  (is \<open>?lhs = ?rhs1 \<box> ?rhs2 \<box> ?rhs3\<close>)
  if \<open>c ` A \<inter> S = {} \<or> inj_on c A\<close> \<open>c ` B \<inter> S = {} \<or> inj_on c B\<close>
    \<open>\<And>a b. a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> c a = c b \<Longrightarrow> c b \<in> S \<Longrightarrow> a = b\<close>
proof -
  \<comment> \<open>Actually, the third assumption is equivalent to the following
     (we of course do not use that(3) in the proof of equivalence).\<close>
  from that(1, 2)
  have \<open>inj_on c ((A \<union> B) \<inter> c -` S) \<longleftrightarrow>
        (\<forall>a b. a \<in> A \<longrightarrow> b \<in> B \<longrightarrow> c a = c b \<longrightarrow> c b \<in> S \<longrightarrow> a = b)\<close>
    by (elim disjE, simp_all add: inj_on_def)
      ((auto)[3], metis Int_iff Un_iff vimageE vimageI)

  from that(3) have * : \<open>A \<inter> (c -` c ` B \<inter> c -` S) = A \<inter> B \<inter> c -` S\<close> by auto blast
  show ?thesis by (simp add: read_Sync_read_forced_read_left that "*")
qed

lemma read_Sync_read_forced_read_same_chan_weaker :
  \<comment> \<open>Easier with a stronger assumption.\<close>
  \<open>inj_on c (A \<union> B) \<Longrightarrow>
   c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> c\<^bold>?b\<in>B \<rightarrow> Q b =
   (c\<^bold>?a\<in>(A - c -` S) \<rightarrow> (P a \<lbrakk>S\<rbrakk> c\<^bold>?b\<in>B \<rightarrow> Q b)) \<box>
   (c\<^bold>?b\<in>(B - c -` S) \<rightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> Q b)) \<box>
   (c\<^bold>?x\<in>(A \<inter> B \<inter> c -` S) \<rightarrow> (P x \<lbrakk>S\<rbrakk> Q x))\<close>
  by (rule read_Sync_read_forced_read_same_chan)
    (simp_all add: inj_on_Un, metis Un_iff inj_onD inj_on_Un)


lemma read_Sync_read_subset_forced_read_same_chan :
  \<comment> \<open>In the subset case, the assumption \<^term>\<open>inj_on c (A \<union> B)\<close> is equivalent.
      The result is not weaker anymore.\<close>
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> c\<^bold>?b\<in>B \<rightarrow> Q b = c\<^bold>?x\<in>(A \<inter> B) \<rightarrow> (P x \<lbrakk>S\<rbrakk> Q x)\<close>
  if \<open>c ` A \<subseteq> S\<close> \<open>c ` B \<subseteq> S\<close> \<open>inj_on c (A \<union> B)\<close>
proof -
  from that(3) have \<open>A \<inter> c -` c ` B = A \<inter> B\<close> by (auto simp add: inj_on_def)
  with that(3) show ?thesis
    by (subst read_Sync_read_subset_forced_read_left)
      (simp_all add: that(1, 2) inj_on_Un, meson Un_iff inj_on_contraD that(3))
qed



paragraph \<open>\<^const>\<open>read\<close> and \<^const>\<open>ndet_write\<close>.\<close>

lemma ndet_write_Sync_read :
  \<open>c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b =
   (  if A = {} then STOP \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b
    else \<sqinter>a\<in>c ` A. (if a \<in> S then STOP else a \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b)) \<box>
                   (\<box>b\<in>(d ` B - S) \<rightarrow> (a \<rightarrow> P (inv_into A c a) \<lbrakk>S\<rbrakk> Q (inv_into B d b))) \<box>
                   (if a \<in> d ` B \<inter> S then a \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk> Q (inv_into B d a)) else STOP))\<close>
  by (auto simp add: ndet_write_def read_def Mndetprefix_Sync_Mprefix
      intro: mono_GlobalNdet_eq arg_cong2[where f = \<open>(\<box>)\<close>])

lemma read_Sync_ndet_write :
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b =
   (  if B = {} then c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> STOP
    else \<sqinter>b\<in>d ` B. (if b \<in> S then STOP else b \<rightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> Q (inv_into B d b))) \<box>
                   (\<box>a\<in>(c ` A - S) \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk> b \<rightarrow> Q (inv_into B d b))) \<box>
                   (if b \<in> c ` A \<inter> S then b \<rightarrow> (P (inv_into A c b) \<lbrakk>S\<rbrakk> Q (inv_into B d b)) else STOP))\<close>
  by (auto simp add: ndet_write_def read_def Mprefix_Sync_Mndetprefix
      intro: mono_GlobalNdet_eq arg_cong2[where f = \<open>(\<box>)\<close>])


lemma ndet_write_Sync_read_subset :
  \<open>c ` A \<subseteq> S \<Longrightarrow> d ` B \<subseteq> S \<Longrightarrow>
   c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b =
   (  if c ` A \<subseteq> d ` B then \<sqinter>a\<in>c ` A \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk> Q (inv_into B d a))
    else (\<sqinter>a\<in>(c ` A \<inter> d ` B) \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk> Q (inv_into B d a))) \<sqinter> STOP)\<close>
  by (simp add: read_def ndet_write_def Mndetprefix_Sync_Mprefix_subset)

lemma read_Sync_ndet_write_subset :
  \<open>c ` A \<subseteq> S \<Longrightarrow> d ` B \<subseteq> S \<Longrightarrow>
   c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b =
   (  if d ` B \<subseteq> c ` A then \<sqinter>b\<in>d ` B \<rightarrow> (P (inv_into A c b) \<lbrakk>S\<rbrakk> Q (inv_into B d b))
    else (\<sqinter>b\<in>(c ` A \<inter> d ` B) \<rightarrow> (P (inv_into A c b) \<lbrakk>S\<rbrakk> Q (inv_into B d b))) \<sqinter> STOP)\<close>
  by (simp add: read_def ndet_write_def Mprefix_Sync_Mndetprefix_subset)


\<comment> \<open>If we have the same injective channel, it's better.\<close>
lemma ndet_write_Sync_read_subset_same_chan:
  \<open>c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> c\<^bold>?b\<in>B \<rightarrow> Q b =
   (if A \<subseteq> B then c\<^bold>!\<^bold>!a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk> Q a) else (c\<^bold>!\<^bold>!a\<in>(A \<inter> B) \<rightarrow> (P a \<lbrakk>S\<rbrakk> Q a)) \<sqinter> STOP)\<close>
  if \<open>c ` A \<subseteq> S\<close> \<open>c ` B \<subseteq> S\<close> \<open>inj_on c (A \<union> B)\<close>
proof -
  from \<open>inj_on c (A \<union> B)\<close> have  * : \<open>c ` A \<subseteq> c ` B \<longleftrightarrow> A \<subseteq> B\<close>
    by (auto simp add: inj_on_eq_iff)
  from \<open>inj_on c (A \<union> B)\<close> have ** : \<open>c ` A \<inter> c ` B = c ` (A \<inter> B)\<close>
    by (auto simp add: inj_on_Un)
  from \<open>inj_on c (A \<union> B)\<close> show ?thesis
    by (unfold ndet_write_Sync_read_subset[OF \<open>c ` A \<subseteq> S\<close> \<open>c ` B \<subseteq> S\<close>] "*" "**")
      (auto simp add: ndet_write_def inj_on_Un inj_on_Int
        intro!: mono_Mndetprefix_eq arg_cong2[where f = \<open>(\<sqinter>)\<close>])
qed

lemma read_Sync_ndet_write_subset_same_chan:
  \<open>c ` A \<subseteq> S \<Longrightarrow> c ` B \<subseteq> S \<Longrightarrow> inj_on c (A \<union> B) \<Longrightarrow>
   c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> c\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b =
   (if B \<subseteq> A then c\<^bold>!\<^bold>!b\<in>B \<rightarrow> (P b \<lbrakk>S\<rbrakk> Q b) else (c\<^bold>!\<^bold>!b\<in>(A \<inter> B) \<rightarrow> (P b \<lbrakk>S\<rbrakk> Q b)) \<sqinter> STOP)\<close>
  by (subst (1 2 3) Sync_commute)
    (simp add: Int_commute Un_commute ndet_write_Sync_read_subset_same_chan)


lemma ndet_write_Sync_read_indep :
  \<open>c ` A \<inter> S = {} \<Longrightarrow> d ` B \<inter> S = {} \<Longrightarrow>
   c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b =
   (  if A = {} then d\<^bold>?b\<in>B \<rightarrow>  (STOP \<lbrakk>S\<rbrakk> Q b)
    else \<sqinter>a\<in>c ` A. (a \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b)) \<box>
                   (d\<^bold>?b\<in>B \<rightarrow> (a \<rightarrow> P (inv_into A c a) \<lbrakk>S\<rbrakk> Q b)))\<close>
  by (auto simp add: ndet_write_def read_def Mndetprefix_Sync_Mprefix_indep comp_def
      intro: mono_GlobalNdet_eq arg_cong2[where f = \<open>(\<box>)\<close>])

lemma read_Sync_ndet_write_indep :
  \<open>c ` A \<inter> S = {} \<Longrightarrow> d ` B \<inter> S = {} \<Longrightarrow>
   c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b =
   (  if B = {} then c\<^bold>?a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk> STOP)
    else \<sqinter>b\<in>d ` B. (b \<rightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> Q (inv_into B d b))) \<box>
                   (c\<^bold>?a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk> b \<rightarrow> Q (inv_into B d b))))\<close>
  by (auto simp add: ndet_write_def read_def Mprefix_Sync_Mndetprefix_indep comp_def
      intro: mono_GlobalNdet_eq arg_cong2[where f = \<open>(\<box>)\<close>])


lemma ndet_write_Sync_read_left :
  \<open>c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b = c\<^bold>!\<^bold>!a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b)\<close>
  (is \<open>?lhs = ?rhs\<close>) if \<open>c ` A \<inter> S = {}\<close> \<open>d ` B \<subseteq> S\<close>
proof -
  from that have \<open>?lhs = (  if A = {} then STOP \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b
                          else c\<^bold>!\<^bold>!a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b))\<close>
    by (auto simp add: ndet_write_def read_def Mndetprefix_Sync_Mprefix_left comp_def
        intro: mono_GlobalNdet_eq arg_cong2[where f = \<open>(\<box>)\<close>])
  also have \<open>\<dots> = ?rhs\<close> by (simp add: read_def ndet_write_def Mprefix_is_STOP_iff
        STOP_Sync_Mprefix that(2))
  finally show \<open>?lhs = ?rhs\<close> .
qed

lemma read_Sync_ndet_write_left :
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b = c\<^bold>?a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b)\<close>
  (is \<open>?lhs = ?rhs\<close>) if \<open>c ` A \<inter> S = {}\<close> \<open>d ` B \<subseteq> S\<close>
proof -
  from that have \<open>?lhs = (if B = {} then (c\<^bold>?a\<in>A \<rightarrow> P a) \<lbrakk>S\<rbrakk> STOP else ?rhs)\<close>
    by (auto simp add: ndet_write_def read_def Mprefix_Sync_Mndetprefix_left comp_def
        intro: mono_GlobalNdet_eq arg_cong2[where f = \<open>(\<box>)\<close>])
  also have \<open>\<dots> = ?rhs\<close>
    by (simp add: read_def comp_def)
      (use Mprefix_Sync_Mprefix_left that(1) in force)
  finally show \<open>?lhs = ?rhs\<close> .
qed


lemma ndet_write_Sync_read_right :
  \<open>c ` A \<subseteq> S \<Longrightarrow> d ` B \<inter> S = {} \<Longrightarrow>
   c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b = d\<^bold>?b\<in>B \<rightarrow> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> Q b)\<close>
  by (subst (1 2) Sync_commute) (simp add: read_Sync_ndet_write_left)

lemma read_Sync_ndet_write_right :
  \<open>c ` A \<subseteq> S \<Longrightarrow> d ` B \<inter> S = {} \<Longrightarrow>
   c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b = d\<^bold>!\<^bold>!b\<in>B \<rightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> Q b)\<close>
  by (subst (1 2) Sync_commute) (simp add: ndet_write_Sync_read_left)



paragraph \<open>\<^const>\<open>read\<close> and \<^const>\<open>write\<close>.\<close>

lemma write_Sync_read :
  \<open>c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b =
   (if c a \<in> S then STOP else c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b)) \<box>
   (\<box>b\<in>(d ` B - S) \<rightarrow> (c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> Q (inv_into B d b))) \<box>
   (if c a \<in> d ` B \<inter> S then c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk> Q (inv_into B d (c a))) else STOP)\<close>
  by (subst ndet_write_Sync_read[where A = \<open>{a}\<close>, simplified])
    (simp add: write_is_write0 image_iff)

lemma read_Sync_write :
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q =
   (if d b \<in> S then STOP else d\<^bold>!b \<rightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> Q)) \<box>
   (\<box>a\<in>(c ` A - S) \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q)) \<box>
   (if d b \<in> c ` A \<inter> S then d\<^bold>!b \<rightarrow> (P (inv_into A c (d b)) \<lbrakk>S\<rbrakk> Q) else STOP)\<close>
  by (subst read_Sync_ndet_write[where B = \<open>{b}\<close>, simplified])
    (simp add: write_is_write0 image_iff)


lemma write_Sync_read_subset :
  \<open>c a \<in> S \<Longrightarrow> d ` B \<subseteq> S \<Longrightarrow>
   c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b =
   (if c a \<in> d ` B then c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk> Q (inv_into B d (c a))) else STOP)\<close>
  by (simp add: write_Sync_read)
    (metis Det_STOP Det_commute Diff_eq_empty_iff Mprefix_empty)

lemma read_Sync_write_subset :
  \<open>c ` A \<subseteq> S \<Longrightarrow> d b \<in> S \<Longrightarrow>
   c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q =
   (if d b \<in> c ` A then d\<^bold>!b \<rightarrow> (P (inv_into A c (d b)) \<lbrakk>S\<rbrakk> Q) else STOP)\<close>
  by (metis Sync_commute write_Sync_read_subset)


\<comment> \<open>If we have the same injective channel, it's better.\<close>
lemma write_Sync_read_subset_same_chan:
  \<open>c a \<in> S \<Longrightarrow> c ` B \<subseteq> S \<Longrightarrow> inj_on c (insert a B) \<Longrightarrow>
   c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> c\<^bold>?b\<in>B \<rightarrow> Q b = (if a \<in> B then c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk> Q a) else STOP)\<close>
  by (subst ndet_write_Sync_read_subset_same_chan[where A = \<open>{a}\<close>, simplified]) simp_all

lemma read_Sync_write_subset_same_chan:
  \<open>c ` A \<subseteq> S \<Longrightarrow> c b \<in> S \<Longrightarrow> inj_on c (insert b A) \<Longrightarrow>
   c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> c\<^bold>!b \<rightarrow> Q = (if b \<in> A then c\<^bold>!b \<rightarrow> (P b \<lbrakk>S\<rbrakk> Q) else STOP)\<close>
  by (metis Sync_commute write_Sync_read_subset_same_chan)


lemma write_Sync_read_indep :
  \<open>c a \<notin> S \<Longrightarrow> d ` B \<inter> S = {} \<Longrightarrow>
   c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b =
   (c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b)) \<box> (d\<^bold>?b\<in>B \<rightarrow> (c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> Q b))\<close>
  by (subst ndet_write_Sync_read_indep[where A = \<open>{a}\<close>, simplified])
    (simp_all add: write_is_write0)

lemma read_Sync_write_indep :
  \<open>c ` A \<inter> S = {} \<Longrightarrow> d b \<notin> S \<Longrightarrow>
   c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q =
   (d\<^bold>!b \<rightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> Q)) \<box> (c\<^bold>?a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q))\<close>
  by (subst read_Sync_ndet_write_indep[where B = \<open>{b}\<close>, simplified])
    (simp_all add: write_is_write0)


lemma write_Sync_read_left :
  \<open>c a \<notin> S \<Longrightarrow> d ` B \<subseteq> S \<Longrightarrow>
   c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b = c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b)\<close>
  by (subst ndet_write_Sync_read_left[where A = \<open>{a}\<close>, simplified]) simp_all

lemma read_Sync_write_left :
  \<open>c ` A \<inter> S = {} \<Longrightarrow> d b \<in> S \<Longrightarrow>
   c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q = c\<^bold>?a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q)\<close>
  by (subst read_Sync_ndet_write_left[where B = \<open>{b}\<close>, simplified]) simp_all


lemma write_Sync_read_right :
  \<open>c a \<in> S \<Longrightarrow> d ` B \<inter> S = {} \<Longrightarrow>
   c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b = d\<^bold>?b\<in>B \<rightarrow> (c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> Q b)\<close>
  by (subst (1 2) Sync_commute) (simp add: read_Sync_write_left)

lemma read_Sync_write_right :
  \<open>c ` A \<subseteq> S \<Longrightarrow> d b \<notin> S \<Longrightarrow>
   c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q = d\<^bold>!b \<rightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> Q)\<close>
  by (subst (1 2) Sync_commute) (simp add: write_Sync_read_left)



paragraph \<open>\<^const>\<open>ndet_write\<close> and \<^const>\<open>ndet_write\<close>\<close>

lemma ndet_write_Sync_ndet_write :
  \<open>c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b =
   (  if A = {} then   if d ` B \<inter> S = {} then d\<^bold>!\<^bold>!b\<in>B \<rightarrow> (STOP \<lbrakk>S\<rbrakk> Q b)
                     else (\<sqinter>x\<in>d ` (B - d -` S) \<rightarrow> (STOP \<lbrakk>S\<rbrakk> Q (inv_into B d x))) \<sqinter> STOP
    else   if B = {} then   if c ` A \<inter> S = {} then c\<^bold>!\<^bold>!a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk> STOP)
                          else (\<sqinter>x\<in>c ` (A - c -` S) \<rightarrow> (P (inv_into A c x) \<lbrakk>S\<rbrakk> STOP)) \<sqinter> STOP
         else \<sqinter>b\<in>d ` B. \<sqinter>a\<in>c ` A.
              (if a \<in> S then STOP else a \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk> b \<rightarrow> Q (inv_into B d b))) \<box>
              (if b \<in> S then STOP else b \<rightarrow> (a \<rightarrow> P (inv_into A c a) \<lbrakk>S\<rbrakk> Q (inv_into B d b))) \<box>
              (if a = b \<and> b \<in> S then b \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk> Q (inv_into B d b)) else STOP))\<close>
  (is \<open>?lhs = (  if A = {} then if d ` B \<inter> S = {} then ?mv_right else ?mv_right' \<sqinter> STOP
               else   if B = {} then if c ` A \<inter> S = {} then ?mv_left else ?mv_left' \<sqinter> STOP
                    else ?huge_mess)\<close>)
proof (split if_split, intro conjI impI)
  have \<open>d ` (B - d -` S) = d ` B - S\<close> by blast
  thus \<open>A = {} \<Longrightarrow> ?lhs = (if d ` B \<inter> S = {} then ?mv_right else ?mv_right' \<sqinter> STOP)\<close>
    by (auto simp add: ndet_write_def STOP_Sync_Mndetprefix comp_def
        intro: mono_Mndetprefix_eq)
next
  show \<open>?lhs = (if B = {} then if c ` A \<inter> S = {} then ?mv_left else ?mv_left' \<sqinter> STOP else ?huge_mess)\<close> if \<open>A \<noteq> {}\<close>
  proof (split if_split, intro conjI impI)
    have \<open>c ` (A - c -` S) = c ` A - S\<close> by blast
    thus \<open>B = {} \<Longrightarrow> ?lhs = (if c ` A \<inter> S = {} then ?mv_left else ?mv_left' \<sqinter> STOP)\<close>
      by (auto simp add: ndet_write_def Mndetprefix_Sync_STOP comp_def
          intro: mono_Mndetprefix_eq)
  next
    assume \<open>B \<noteq> {}\<close>
    have \<open>?lhs = (\<sqinter>b\<in>d ` B. \<sqinter>a\<in>c ` A. (a \<rightarrow> P (inv_into A c a) \<lbrakk>S\<rbrakk> (b \<rightarrow> Q (inv_into B d b))))\<close>
      by (simp add: ndet_write_def Mndetprefix_GlobalNdet \<open>A \<noteq> {}\<close> \<open>B \<noteq> {}\<close>
          Sync_distrib_GlobalNdet_left Sync_distrib_GlobalNdet_right)
    also have \<open>\<dots> = ?huge_mess\<close>
      by (auto simp add: write0_def Mprefix_Sync_Mprefix Diff_triv Mprefix_is_STOP_iff disjoint_iff
          intro!: mono_GlobalNdet_eq arg_cong2[where f = \<open>(\<box>)\<close>])
    finally show \<open>?lhs = ?huge_mess\<close> .
  qed
qed


lemma ndet_write_Sync_ndet_write_subset :
  \<open>c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b =
   (  if \<exists>b. c ` A = {b} \<and> d ` B = {b}
    then (THE b. d ` B = {b}) \<rightarrow> (P (inv_into A c (THE a. c ` A = {a})) \<lbrakk>S\<rbrakk> Q (inv_into B d (THE b. d ` B = {b})))
    else (\<sqinter>x\<in>(c ` A \<inter> d ` B) \<rightarrow> (P (inv_into A c x) \<lbrakk>S\<rbrakk> Q (inv_into B d x))) \<sqinter> STOP)\<close>
  (is \<open>?lhs = (if ?cond then ?rhs1 else ?rhs2)\<close>) if \<open>c ` A \<subseteq> S\<close> \<open>d ` B \<subseteq> S\<close>
proof (split if_split, intro conjI impI)
  show \<open>?cond \<Longrightarrow> ?lhs = ?rhs1\<close>
    by (elim exE, simp add: ndet_write_is_GlobalNdet_write0 write0_def)
      (subst Mprefix_Sync_Mprefix_subset, use \<open>c ` A \<subseteq> S\<close> in simp_all)
next
  assume \<open>\<not> ?cond\<close>
  let ?term = \<open>\<lambda>a b. (b \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk> Q (inv_into B d b)))\<close>
  have \<open>?lhs = \<sqinter>b\<in>d ` B. \<sqinter>a\<in>c ` A. (if a = b then ?term a b else STOP)\<close>
    (is \<open>?lhs = \<sqinter>b\<in>d ` B. \<sqinter>a\<in>c ` A. ?rhs' b a\<close>)
  proof (cases \<open>A = {} \<or> B = {}\<close>)
    from \<open>c ` A \<subseteq> S\<close> \<open>d ` B \<subseteq> S\<close> show \<open>A = {} \<or> B = {} \<Longrightarrow> ?lhs = (\<sqinter>b\<in>d ` B. \<sqinter>a\<in>c ` A. ?rhs' b a)\<close>
      by (elim disjE) (simp_all add: ndet_write_def Mndetprefix_Sync_STOP STOP_Sync_Mndetprefix
          Int_absorb2 Mndetprefix_is_STOP_iff Ndet_is_STOP_iff)
  next
    show \<open>\<not> (A = {} \<or> B = {}) \<Longrightarrow> ?lhs = (\<sqinter>b\<in>d ` B. \<sqinter>a\<in>c ` A. ?rhs' b a)\<close>
      by (simp add: ndet_write_Sync_ndet_write)
        (intro mono_GlobalNdet_eq, use \<open>c ` A \<subseteq> S\<close> \<open>d ` B \<subseteq> S\<close> in auto)
  qed

  also have \<open>(\<sqinter>b\<in>d ` B. \<sqinter>a\<in>c ` A. ?rhs' b a) = ?rhs2\<close>
  proof (cases \<open>d ` B \<inter> c ` A = {}\<close>)
    assume \<open>d ` B \<inter> c ` A = {}\<close>
    hence \<open>c ` A \<inter> d ` B = {}\<close> by blast
    hence \<open>(\<sqinter>b\<in>d ` B. \<sqinter>a\<in>c ` A. ?rhs' b a) = STOP\<close> by (auto simp add: GlobalNdet_is_STOP_iff)
    thus \<open>(\<sqinter>b\<in>d ` B. \<sqinter>a\<in>c ` A. ?rhs' b a) = ?rhs2\<close>
      by (auto simp add: \<open>c ` A \<inter> d ` B = {}\<close>)
  next
    show \<open>(\<sqinter>b\<in>d ` B. \<sqinter>a\<in>c ` A. ?rhs' b a) = ?rhs2\<close> if \<open>d ` B \<inter> c ` A \<noteq> {}\<close>
    proof (cases \<open>d ` B - c ` A = {}\<close>)
      assume \<open>d ` B - c ` A = {}\<close>
      hence \<open>c ` A \<inter> d ` B = d ` B\<close> by blast
      have \<open>(\<sqinter>a\<in>c ` A. ?rhs' b a) = (if c ` A = {b} then ?term b b else ?term b b \<sqinter> STOP)\<close>
        (is \<open>(\<sqinter>a\<in>c ` A. ?rhs' b a) = ?rhs'' b\<close>) if \<open>b \<in> d ` B\<close> for b
      proof (cases \<open>c ` A \<inter> {b} = {}\<close>)
        from \<open>d ` B - c ` A = {}\<close> \<open>b \<in> d ` B\<close>
        show \<open>c ` A \<inter> {b} = {} \<Longrightarrow> (\<sqinter>a\<in>c ` A. ?rhs' b a) = ?rhs'' b\<close> by auto
      next
        show \<open>(\<sqinter>a\<in>c ` A. ?rhs' b a) = ?rhs'' b\<close> if \<open>c ` A \<inter> {b} \<noteq> {}\<close>
        proof (cases \<open>c ` A - {b} = {}\<close>)
          show \<open>c ` A - {b} = {} \<Longrightarrow> (\<sqinter>a\<in>c ` A. ?rhs' b a) = ?rhs'' b\<close>
            using \<open>c ` A \<inter> {b} \<noteq> {}\<close> by auto
        next
          show \<open>(\<sqinter>a\<in>c ` A. ?rhs' b a) = ?rhs'' b\<close> if \<open>c ` A - {b} \<noteq> {}\<close>
            using \<open>c ` A - {b} \<noteq> {}\<close> \<open>c ` A \<inter> {b} \<noteq> {}\<close>
            by (auto simp add: GlobalNdet_is_STOP_iff
                simp flip: GlobalNdet_factorization_union
                [OF \<open>c ` A \<inter> {b} \<noteq> {}\<close> \<open>c ` A - {b} \<noteq> {}\<close>, unfolded Int_Diff_Un]
                intro: arg_cong2[where f = \<open>(\<sqinter>)\<close>])
        qed
      qed
      hence \<open>(\<sqinter>b \<in> d ` B. \<sqinter>a\<in>c ` A. ?rhs' b a) = \<sqinter>b \<in> d ` B. ?rhs'' b\<close>
        by (fact mono_GlobalNdet_eq)
      also have \<open>(\<sqinter>b \<in> d ` B. ?rhs'' b) = ?rhs2\<close>
      proof -
        from \<open>\<not> ?cond\<close> have \<open>(\<sqinter>b \<in> d ` B. ?rhs'' b) = \<sqinter>b \<in> d ` B. ?term b b \<sqinter> STOP\<close>
          by (metis Diff_eq_empty_iff Int_commute \<open>c ` A \<inter> d ` B = d ` B\<close>
              \<open>d ` B - c ` A = {}\<close> subset_singleton_iff \<open>d ` B \<inter> c ` A \<noteq> {}\<close>)
        also have \<open>\<dots> = (\<sqinter>b \<in> d ` B. ?term b b) \<sqinter> STOP\<close>
          by (simp add: Process_eq_spec Ndet_projs GlobalNdet_projs STOP_projs)
        finally show \<open>(\<sqinter>b \<in> d ` B. ?rhs'' b) = ?rhs2\<close>
          by (simp add: Mndetprefix_GlobalNdet \<open>c ` A \<inter> d ` B = d ` B\<close>)
      qed
      finally show \<open>(\<sqinter>b \<in> d ` B. \<sqinter>a\<in>c ` A. ?rhs' b a) = ?rhs2\<close> .
    next
      assume \<open>d ` B - c ` A \<noteq> {}\<close>
      have \<open>\<sqinter>a\<in>c ` A. (if a = b then ?term a b else STOP) =
            (if b \<in> c ` A then if c ` A = {b} then ?term b b else (?term b b) \<sqinter> STOP else STOP)\<close>
        if \<open>b \<in> d ` B\<close> for b
      proof (split if_split, intro conjI impI)
        show \<open>\<sqinter>a\<in>c ` A. (if a = b then ?term a b else STOP) =
              (if c ` A = {b} then ?term b b else (?term b b) \<sqinter> STOP)\<close> if \<open>b \<in> c ` A\<close>
        proof (split if_split, intro conjI impI)
          show \<open>c ` A = {b} \<Longrightarrow> \<sqinter>a\<in>c ` A. (if a = b then ?term a b else STOP) = ?term b b\<close> by simp
        next
          assume \<open>c ` A \<noteq> {b}\<close>
          with \<open>b \<in> c ` A\<close> have \<open>insert b (c ` A) = c ` A\<close> \<open>c ` A - {b} \<noteq> {}\<close> by auto
          show \<open>c ` A \<noteq> {b} \<Longrightarrow> \<sqinter>a\<in>c ` A. (if a = b then ?term a b else STOP) = ?term b b \<sqinter> STOP\<close>
            by (auto simp add: GlobalNdet_is_STOP_iff intro!: arg_cong2[where f = \<open>(\<sqinter>)\<close>]
                simp flip: GlobalNdet_factorization_union
                [of \<open>{b}\<close>, OF _ \<open>c ` A - {b} \<noteq> {}\<close>, simplified, unfolded \<open>insert b (c ` A) = c ` A\<close>])
        qed
      next
        show \<open>b \<notin> c ` A \<Longrightarrow> \<sqinter>a\<in>c ` A. (if a = b then ?term a b else STOP) = STOP\<close>
          by (auto simp add: GlobalNdet_is_STOP_iff)
      qed

      hence \<open>\<sqinter>b \<in> d ` B. \<sqinter>a\<in>c ` A. ?rhs' b a =
             \<sqinter>b \<in> d ` B. (if b \<in> c ` A then if c ` A = {b} then ?term b b else (?term b b) \<sqinter> STOP else STOP)\<close>
        by (fact mono_GlobalNdet_eq)
      also from \<open>d ` B - c ` A \<noteq> {}\<close> have \<open>\<dots> = (\<sqinter>b \<in> d ` B. (if b \<in> c ` A then ?term b b else STOP)) \<sqinter> STOP\<close>
        by (simp add: Process_eq_spec GlobalNdet_projs, safe)
          (simp_all add: GlobalNdet_projs STOP_projs Ndet_projs split: if_split_asm, auto)
      also have \<open>\<dots> = ?rhs2\<close>
      proof (fold GlobalNdet_factorization_union
          [OF \<open>d ` B \<inter> c ` A \<noteq> {}\<close> \<open>d ` B - c ` A \<noteq> {}\<close>, unfolded Int_Diff_Un])
        have \<open>\<sqinter>b\<in>(d ` B \<inter> c ` A). (if b \<in> c ` A then ?term b b else STOP) =
              \<sqinter>b\<in>(d ` B \<inter> c ` A). ?term b b\<close> by (auto intro: mono_GlobalNdet_eq)
        moreover have \<open>\<sqinter>b\<in>(d ` B - c ` A). (if b \<in> c ` A then ?term b b else STOP) = STOP\<close>
          by (simp add: GlobalNdet_is_STOP_iff)
        ultimately show \<open>(\<sqinter>b\<in>(d ` B \<inter> c ` A). (if b \<in> c ` A then ?term b b else STOP)) \<sqinter>
                         (\<sqinter>b\<in>(d ` B - c ` A). (if b \<in> c ` A then ?term b b else STOP)) \<sqinter> STOP = ?rhs2\<close>
          by (metis Mndetprefix_GlobalNdet Int_commute Ndet_assoc Ndet_id)
      qed
      finally show \<open>(\<sqinter>b \<in> d ` B. \<sqinter>a\<in>c ` A. ?rhs' b a) = ?rhs2\<close> .
    qed
  qed
  finally show \<open>?lhs = ?rhs2\<close> .
qed


lemma ndet_write_Sync_ndet_write_indep :
  \<open>c ` A \<inter> S = {} \<Longrightarrow> d ` B \<inter> S = {} \<Longrightarrow>
   c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b =
   (  if A = {} then d\<^bold>!\<^bold>!b\<in>B \<rightarrow> (STOP \<lbrakk>S\<rbrakk> Q b)
    else   if B = {} then c\<^bold>!\<^bold>!a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk> STOP)
         else \<sqinter>b\<in>d ` B. \<sqinter>a\<in>c ` A.
              ((a \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk> b \<rightarrow> Q (inv_into B d b)))) \<box>
              ((b \<rightarrow> (a \<rightarrow> P (inv_into A c a) \<lbrakk>S\<rbrakk> Q (inv_into B d b)))))\<close>
  by (auto simp add: ndet_write_Sync_ndet_write disjoint_iff intro!: mono_GlobalNdet_eq)


lemma ndet_write_Sync_ndet_write_left :
  \<open>c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b = c\<^bold>!\<^bold>!a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b)\<close>
  (is \<open>?lhs = ?rhs\<close>) if \<open>c ` A \<inter> S = {}\<close> \<open>d ` B \<subseteq> S\<close>
proof -
  let ?rhs' = \<open>\<sqinter>b\<in>d ` B. \<sqinter>a\<in>c ` A. a \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk> b \<rightarrow> Q (inv_into B d b))\<close>
  have \<open>?lhs = (  if A = {} then   if d ` B \<inter> S = {} then d\<^bold>!\<^bold>!b\<in>B \<rightarrow> (STOP \<lbrakk>S\<rbrakk> Q b)
                                 else (\<sqinter>x\<in>d ` (B - d -` S) \<rightarrow> (STOP \<lbrakk>S\<rbrakk> Q (inv_into B d x))) \<sqinter> STOP
                else   if B = {} then   if c ` A \<inter> S = {} then c\<^bold>!\<^bold>!a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk> STOP)
                                      else (\<sqinter>x\<in>c ` (A - c -` S) \<rightarrow> (P (inv_into A c x) \<lbrakk>S\<rbrakk> STOP)) \<sqinter> STOP
                     else \<sqinter>b\<in>d ` B. \<sqinter>a\<in>c ` A.
                          (if a \<in> S then STOP else (a \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk> b \<rightarrow> Q (inv_into B d b)))) \<box>
                          (if b \<in> S then STOP else (b \<rightarrow> (a \<rightarrow> P (inv_into A c a) \<lbrakk>S\<rbrakk> Q (inv_into B d b)))) \<box>
                          (if a = b \<and> b \<in> S then b \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk> Q (inv_into B d b)) else STOP))\<close>
    (is \<open>?lhs = (if A = {} then ?rhs1 else if B = {} then ?rhs2 else ?rhs3)\<close>)
    by (fact ndet_write_Sync_ndet_write)
  also from \<open>d ` B \<subseteq> S\<close> have \<open>?rhs1 = STOP\<close>
    by (auto simp add: Ndet_is_STOP_iff ndet_write_def Mndetprefix_GlobalNdet GlobalNdet_is_STOP_iff)
  also from \<open>c ` A \<inter> S = {}\<close> have \<open>?rhs2 = c\<^bold>!\<^bold>!a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk> STOP)\<close> by presburger
  also from \<open>c ` A \<inter> S = {}\<close> \<open>d ` B \<subseteq> S\<close>
  have \<open>?rhs3 = \<sqinter>b\<in>d ` B. \<sqinter>a\<in>c ` A. a \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk> b \<rightarrow> Q (inv_into B d b))\<close>
    by (intro mono_GlobalNdet_eq) auto
  finally have \<open>?lhs = (  if A = {} then STOP
                        else   if B = {} then c\<^bold>!\<^bold>!a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk> STOP)
                             else ?rhs')\<close> .
  moreover have \<open>B \<noteq> {} \<Longrightarrow> ?rhs' = \<sqinter>a\<in>c ` A. a \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk> \<sqinter>b\<in>d ` B. b \<rightarrow> Q (inv_into B d b))\<close>
    by (subst GlobalNdet_sets_commute)
      (simp add: Sync_distrib_GlobalNdet_left write0_GlobalNdet)
  moreover have \<open>\<dots> = c\<^bold>!\<^bold>!a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b)\<close>
    by (simp add: ndet_write_is_GlobalNdet_write0)
  ultimately show \<open>?lhs = ?rhs\<close> by simp
qed


lemma ndet_write_Sync_ndet_write_right :
  \<open>c ` A \<subseteq> S \<Longrightarrow> d ` B \<inter> S = {} \<Longrightarrow>
   c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b = d\<^bold>!\<^bold>!b\<in>B \<rightarrow> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> Q b)\<close>
  by (subst (1 2) Sync_commute) (simp add: ndet_write_Sync_ndet_write_left)




paragraph \<open>\<^const>\<open>ndet_write\<close> and \<^const>\<open>write\<close>\<close>

lemma write_Sync_ndet_write :
  \<open>c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b =
   (  if B = {} then c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> STOP
    else \<sqinter>b\<in>d ` B. (if b \<in> S then STOP else b \<rightarrow> (c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> Q (inv_into B d b))) \<box>
                   (if c a \<in> S then STOP else c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk> b \<rightarrow> Q (inv_into B d b))) \<box>
                   (if b = c a \<and> c a \<in> S then c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk> Q (inv_into B d (c a))) else STOP))\<close>
  by (subst read_Sync_ndet_write[where A = \<open>{a}\<close>, simplified],
      auto simp add: write_def Mprefix_singl split: if_split_asm
      intro!: mono_GlobalNdet_eq arg_cong2[where f = \<open>(\<box>)\<close>] mono_Mprefix_eq)
    (simp add: insert_Diff_if write0_def)

lemma ndet_write_Sync_write :
  \<open>c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q =
   (  if A = {} then STOP \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q
    else \<sqinter>a\<in>c ` A. (if a \<in> S then STOP else a \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q)) \<box>
                   (if d b \<in> S then STOP else d\<^bold>!b \<rightarrow> (a \<rightarrow> P (inv_into A c a) \<lbrakk>S\<rbrakk> Q)) \<box>
                   (if a = d b \<and> d b \<in> S then d\<^bold>!b \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk> Q) else STOP))\<close>
  by (subst (1 2 3 4 5) Sync_commute)
    (auto simp add: write_Sync_ndet_write intro: mono_GlobalNdet_eq)


lemma write_Sync_ndet_write_subset :
  \<open>c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b =
   (  if c a \<notin> d ` B then STOP else if d ` B = {c a} then c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk> Q (inv_into B d (c a)))
    else (c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk> Q (inv_into B d (c a)))) \<sqinter> STOP)\<close> if \<open>c a \<in> S\<close> \<open>d ` B \<subseteq> S\<close>
proof (subst read_Sync_ndet_write_subset[where A = \<open>{a}\<close>, simplified])
  from \<open>c a \<in> S\<close> show \<open>c a \<in> S\<close> .
next
  from \<open>d ` B \<subseteq> S\<close> show \<open>d ` B \<subseteq> S\<close> .
next
  show \<open>(  if d ` B \<subseteq> {c a} then \<sqinter>b\<in>d ` B \<rightarrow> (P \<lbrakk>S\<rbrakk> Q (inv_into B d b))
         else (\<sqinter>b\<in>(c ` {a} \<inter> d ` B) \<rightarrow> (P \<lbrakk>S\<rbrakk> Q (inv_into B d b))) \<sqinter> STOP) =
        (  if c a \<notin> d ` B then STOP else if d ` B = {c a} then c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk> Q (inv_into B d (c a)))
         else (c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk> Q (inv_into B d (c a)))) \<sqinter> STOP)\<close>
    (is \<open>?lhs = (if c a \<notin> d ` B then STOP else if d ` B = {c a} then ?rhs else ?rhs \<sqinter> STOP)\<close>)
  proof (split if_split, intro conjI impI)
    show \<open>c a \<notin> d ` B \<Longrightarrow> ?lhs = STOP\<close>
      by (auto simp add: GlobalNdet_is_STOP_iff image_subset_iff image_iff)
  next
    show \<open>\<not> c a \<notin> d ` B \<Longrightarrow> ?lhs = (if d ` B = {c a} then ?rhs else ?rhs \<sqinter> STOP)\<close>
      by (auto simp add: image_subset_iff Ndet_is_STOP_iff write_is_write0)
  qed
qed

lemma ndet_write_Sync_write_subset :
  \<open>c ` A \<subseteq> S \<Longrightarrow> d b \<in> S \<Longrightarrow>
   (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a) \<lbrakk>S\<rbrakk> (d\<^bold>!b \<rightarrow> Q) =
   (  if d b \<notin> c ` A then STOP else if c ` A = {d b} then d\<^bold>!b \<rightarrow> (P (inv_into A c (d b)) \<lbrakk>S\<rbrakk> Q)
    else (d\<^bold>!b \<rightarrow> (P (inv_into A c (d b)) \<lbrakk>S\<rbrakk> Q)) \<sqinter> STOP)\<close>
  by (subst (1 2 3) Sync_commute) (simp add: write_Sync_ndet_write_subset)


lemma write_Sync_ndet_write_indep :
  \<open>c a \<notin> S \<Longrightarrow> d ` B \<inter> S = {} \<Longrightarrow>
   c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b =
   (  if B = {} then c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk> STOP)
    else \<sqinter>b\<in>d ` B. (c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk> b \<rightarrow> Q (inv_into B d b))) \<box>
                   (b \<rightarrow> (c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> Q (inv_into B d b))))\<close>
  by (subst ndet_write_Sync_ndet_write_indep[where A = \<open>{a}\<close>, simplified])
    (auto simp add: write_is_write0 intro: mono_GlobalNdet_eq)

lemma ndet_write_Sync_write_indep :
  \<open>c ` A \<inter> S = {} \<Longrightarrow> d b \<notin> S \<Longrightarrow>
   c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q =
   (  if A = {} then d\<^bold>!b \<rightarrow> (STOP \<lbrakk>S\<rbrakk> Q)
    else \<sqinter>a\<in>c ` A. (a \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q)) \<box>
                   (d\<^bold>!b \<rightarrow> (a \<rightarrow> P (inv_into A c a) \<lbrakk>S\<rbrakk> Q)))\<close>
  by (subst (1 2 3 4) Sync_commute, subst Det_commute)
    (simp add: write_Sync_ndet_write_indep)


lemma write_Sync_ndet_write_left :
  \<open>c a \<notin> S \<Longrightarrow> d ` B \<subseteq> S \<Longrightarrow> c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b = c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b)\<close>
  by (subst ndet_write_Sync_ndet_write_left[where A = \<open>{a}\<close>, simplified]) simp_all

lemma ndet_write_Sync_write_left :
  \<open>c ` A \<inter> S = {} \<Longrightarrow> d b \<in> S \<Longrightarrow> c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q = c\<^bold>!\<^bold>!a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q)\<close>
  by (subst ndet_write_Sync_ndet_write_left[where B = \<open>{b}\<close>, simplified]) simp_all


lemma write_Sync_ndet_write_right :
  \<open>c a \<in> S \<Longrightarrow> d ` B \<inter> S = {} \<Longrightarrow> c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b = d\<^bold>!\<^bold>!b\<in>B \<rightarrow> (c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> Q b)\<close>
  by (subst ndet_write_Sync_ndet_write_right[where A = \<open>{a}\<close>, simplified]) simp_all

lemma ndet_write_Sync_write_right :
  \<open>c ` A \<subseteq> S \<Longrightarrow> d b \<notin> S \<Longrightarrow> c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q = d\<^bold>!b \<rightarrow> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> Q)\<close>
  by (subst ndet_write_Sync_ndet_write_right[where B = \<open>{b}\<close>, simplified]) simp_all



paragraph \<open>\<^const>\<open>write\<close> and \<^const>\<open>write\<close>\<close>

lemma write_Sync_write :
  \<open>c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q =
   (if d b \<in> S then STOP else d\<^bold>!b \<rightarrow> (c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> Q)) \<box>
   (if c a \<in> S then STOP else c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q)) \<box>
   (if c a = d b \<and> d b \<in> S then c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk> Q) else STOP)\<close>
  by (subst read_Sync_read[where A = \<open>{a}\<close> and B = \<open>{b}\<close>, simplified])
    (simp add: write_def insert_Diff_if Det_commute Int_insert_right)

lemma write_Inter_write :
  \<open>c\<^bold>!a \<rightarrow> P ||| d\<^bold>!b \<rightarrow> Q = (c\<^bold>!a \<rightarrow> (P ||| d\<^bold>!b \<rightarrow> Q)) \<box> (d\<^bold>!b \<rightarrow> (c\<^bold>!a \<rightarrow> P ||| Q))\<close>
  by (simp add: write_Sync_write Det_commute)

lemma write_Par_write :
  \<open>c\<^bold>!a \<rightarrow> P || d\<^bold>!b \<rightarrow> Q = (if c a = d b then c\<^bold>!a \<rightarrow> (P || Q) else STOP)\<close>
  by (simp add: write_Sync_write)


lemma write_Sync_write_subset :
  \<open>c a \<in> S \<Longrightarrow> d b \<in> S \<Longrightarrow>
   c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q = (if c a = d b then c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk> Q) else STOP)\<close>
  by (simp add: write_Sync_write)

lemma write_Sync_write_indep :
  \<open>c a \<notin> S \<Longrightarrow> d b \<notin> S \<Longrightarrow>
   c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q = (c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q)) \<box> (d\<^bold>!b \<rightarrow> (c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> Q))\<close>
  by (simp add: Det_commute write_Sync_write)


lemma write_Sync_write_left :
  \<open>c a \<notin> S \<Longrightarrow> d b \<in> S \<Longrightarrow> c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q = c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q)\<close>
  by (auto simp add: write_Sync_write)


lemma write_Sync_write_right :
  \<open>c a \<in> S \<Longrightarrow> d b \<notin> S \<Longrightarrow> c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q = d\<^bold>!b \<rightarrow> (c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> Q)\<close>
  by (auto simp add: write_Sync_write)




paragraph \<open>\<^const>\<open>read\<close> and \<^const>\<open>write0\<close>.\<close>

lemma write0_Sync_read :
  \<open>a \<rightarrow> P \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b =
   (if a \<in> S then STOP else a \<rightarrow> (P \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b)) \<box>
   (\<box>b\<in>(d ` B - S) \<rightarrow> (a \<rightarrow> P \<lbrakk>S\<rbrakk> Q (inv_into B d b))) \<box>
   (if a \<in> d ` B \<inter> S then a \<rightarrow> (P \<lbrakk>S\<rbrakk> Q (inv_into B d a)) else STOP)\<close>
  by (simp add: write_Sync_read[where c = id, unfolded write_is_write0, simplified])

lemma read_Sync_write0 :
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> b \<rightarrow> Q =
   (if b \<in> S then STOP else b \<rightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> Q)) \<box>
   (\<box>a\<in>(c ` A - S) \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk> b \<rightarrow> Q)) \<box>
   (if b \<in> c ` A \<inter> S then b \<rightarrow> (P (inv_into A c b) \<lbrakk>S\<rbrakk> Q) else STOP)\<close>
  by (simp add: read_Sync_write[where d = id, unfolded write_is_write0, simplified])

lemma write0_Sync_read_subset :
  \<open>a \<in> S \<Longrightarrow> d ` B \<subseteq> S \<Longrightarrow>
   a \<rightarrow> P \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b =
   (if a \<in> d ` B then a \<rightarrow> (P \<lbrakk>S\<rbrakk> Q (inv_into B d a)) else STOP)\<close>
  by (simp add: write_Sync_read_subset[where c = id, unfolded write_is_write0, simplified])

lemma read_Sync_write0_subset :
  \<open>c ` A \<subseteq> S \<Longrightarrow> b \<in> S \<Longrightarrow>
   c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> b \<rightarrow> Q =
   (if b \<in> c ` A then b \<rightarrow> (P (inv_into A c b) \<lbrakk>S\<rbrakk> Q) else STOP)\<close>
  by (simp add: read_Sync_write_subset[where d = \<open>\<lambda>x. x\<close>, unfolded write_is_write0])

lemma write0_Sync_read_subset_same_chan:
  \<open>a \<in> S \<Longrightarrow> B \<subseteq> S \<Longrightarrow>
   a \<rightarrow> P \<lbrakk>S\<rbrakk> id\<^bold>?b\<in>B \<rightarrow> Q b = (if a \<in> B then a \<rightarrow> (P \<lbrakk>S\<rbrakk> Q a) else STOP)\<close>
  by (simp add: write_Sync_read_subset_same_chan
      [where c = id, unfolded write_is_write0, simplified])

lemma read_Sync_write0_subset_same_chan:
  \<open>A \<subseteq> S \<Longrightarrow> b \<in> S \<Longrightarrow>
   id\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> b \<rightarrow> Q = (if b \<in> A then b \<rightarrow> (P b \<lbrakk>S\<rbrakk> Q) else STOP)\<close>
  by (simp add: read_Sync_write_subset_same_chan
      [where c = id, unfolded write_is_write0, simplified])

lemma write0_Sync_read_indep :
  \<open>a \<notin> S \<Longrightarrow> d ` B \<inter> S = {} \<Longrightarrow>
   a \<rightarrow> P \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b =
   (a \<rightarrow> (P \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b)) \<box> (d\<^bold>?b\<in>B \<rightarrow> (a \<rightarrow> P \<lbrakk>S\<rbrakk> Q b))\<close>
  by (simp add: write_Sync_read_indep[where c = id, unfolded write_is_write0, simplified])

lemma read_Sync_write0_indep :
  \<open>c ` A \<inter> S = {} \<Longrightarrow> b \<notin> S \<Longrightarrow>
   c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> b \<rightarrow> Q =
   (b \<rightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> Q)) \<box> (c\<^bold>?a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk> b \<rightarrow> Q))\<close>
  by (simp add: read_Sync_write_indep[where d = id, unfolded write_is_write0, simplified])

lemma write0_Sync_read_left :
  \<open>a \<notin> S \<Longrightarrow> d ` B \<subseteq> S \<Longrightarrow> a \<rightarrow> P \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b = a \<rightarrow> (P \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b)\<close>
  by (simp add: write_Sync_read_left[where c = id, unfolded write_is_write0, simplified])

lemma read_Sync_write0_left :
  \<open>c ` A \<inter> S = {} \<Longrightarrow> b \<in> S \<Longrightarrow> c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> b \<rightarrow> Q = c\<^bold>?a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk> b \<rightarrow> Q)\<close>
  by (simp add: read_Sync_write_left[where d = id, unfolded write_is_write0, simplified])

lemma write0_Sync_read_right :
  \<open>a \<in> S \<Longrightarrow> d ` B \<inter> S = {} \<Longrightarrow> a \<rightarrow> P \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b = d\<^bold>?b\<in>B \<rightarrow> (a \<rightarrow> P \<lbrakk>S\<rbrakk> Q b)\<close>
  by (simp add: write_Sync_read_right[where c = id, unfolded write_is_write0, simplified])

lemma read_Sync_write0_right :
  \<open>c ` A \<subseteq> S \<Longrightarrow> b \<notin> S \<Longrightarrow> c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> b \<rightarrow> Q = b \<rightarrow> (c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> Q)\<close>
  by (simp add: read_Sync_write_right[where d = id, unfolded write_is_write0, simplified])



paragraph \<open>\<^const>\<open>ndet_write\<close> and \<^const>\<open>write0\<close>\<close>

lemma write0_Sync_ndet_write :
  \<open>a \<rightarrow> P \<lbrakk>S\<rbrakk> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b =
   (  if B = {} then a \<rightarrow> P \<lbrakk>S\<rbrakk> STOP
    else \<sqinter>b\<in>d ` B. (if b \<in> S then STOP else b \<rightarrow> (a \<rightarrow> P \<lbrakk>S\<rbrakk> Q (inv_into B d b))) \<box>
                   (if a \<in> S then STOP else a \<rightarrow> (P \<lbrakk>S\<rbrakk> b \<rightarrow> Q (inv_into B d b))) \<box>
                   (if b = a \<and> a \<in> S then a \<rightarrow> (P \<lbrakk>S\<rbrakk> Q (inv_into B d a)) else STOP))\<close>
  by (simp add: write_Sync_ndet_write[where c = \<open>\<lambda>x. x\<close>, unfolded write_is_write0, simplified])

lemma ndet_write_Sync_write0 :
  \<open>c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> b \<rightarrow> Q =
   (  if A = {} then STOP \<lbrakk>S\<rbrakk> b \<rightarrow> Q
    else \<sqinter>a\<in>c ` A. (if a \<in> S then STOP else a \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk> b \<rightarrow> Q)) \<box>
                   (if b \<in> S then STOP else b \<rightarrow> (a \<rightarrow> P (inv_into A c a) \<lbrakk>S\<rbrakk> Q)) \<box>
                   (if a = b \<and> b \<in> S then b \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk> Q) else STOP))\<close>
  by (simp add: ndet_write_Sync_write[where d = \<open>\<lambda>x. x\<close>, unfolded write_is_write0, simplified])

lemma write0_Sync_ndet_write_subset :
  \<open>a \<in> S \<Longrightarrow> d ` B \<subseteq> S \<Longrightarrow>
   a \<rightarrow> P \<lbrakk>S\<rbrakk> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b =
   (  if a \<notin> d ` B then STOP else if d ` B = {a} then a \<rightarrow> (P \<lbrakk>S\<rbrakk> Q (inv_into B d a))
    else (a \<rightarrow> (P \<lbrakk>S\<rbrakk> Q (inv_into B d a))) \<sqinter> STOP)\<close>
  by (simp add: write_Sync_ndet_write_subset[where c = id, unfolded write_is_write0, simplified])

lemma ndet_write_Sync_write0_subset :
  \<open>c ` A \<subseteq> S \<Longrightarrow> b \<in> S \<Longrightarrow>
   c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> b \<rightarrow> Q =
   (  if b \<notin> c ` A then STOP else if c ` A = {b} then b \<rightarrow> (P (inv_into A c b) \<lbrakk>S\<rbrakk> Q)
    else (b \<rightarrow> (P (inv_into A c b) \<lbrakk>S\<rbrakk> Q)) \<sqinter> STOP)\<close>
  by (simp add: ndet_write_Sync_write_subset[where d = id, unfolded write_is_write0, simplified])

lemma write0_Sync_ndet_write_indep :
  \<open>a \<notin> S \<Longrightarrow> d ` B \<inter> S = {} \<Longrightarrow>
   a \<rightarrow> P \<lbrakk>S\<rbrakk> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b =
   (  if B = {} then a \<rightarrow> (P \<lbrakk>S\<rbrakk> STOP)
    else \<sqinter>b\<in>d ` B. (a \<rightarrow> (P \<lbrakk>S\<rbrakk> b \<rightarrow> Q (inv_into B d b))) \<box>
                   (b \<rightarrow> (a \<rightarrow> P \<lbrakk>S\<rbrakk> Q (inv_into B d b))))\<close>
  by (simp add: write_Sync_ndet_write_indep[where c = id, unfolded write_is_write0, simplified])

lemma ndet_write_Sync_write0_indep :
  \<open>c ` A \<inter> S = {} \<Longrightarrow> b \<notin> S \<Longrightarrow>
   c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> b \<rightarrow> Q =
   (  if A = {} then b \<rightarrow> (STOP \<lbrakk>S\<rbrakk> Q)
    else \<sqinter>a\<in>c ` A. (a \<rightarrow> (P (inv_into A c a) \<lbrakk>S\<rbrakk> b \<rightarrow> Q)) \<box>
                   (b \<rightarrow> (a \<rightarrow> P (inv_into A c a) \<lbrakk>S\<rbrakk> Q)))\<close>
  by (simp add: ndet_write_Sync_write_indep[where d = id, unfolded write_is_write0, simplified])

lemma write0_Sync_ndet_write_left :
  \<open>a \<notin> S \<Longrightarrow> d ` B \<subseteq> S \<Longrightarrow> a \<rightarrow> P \<lbrakk>S\<rbrakk> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b = a \<rightarrow> (P \<lbrakk>S\<rbrakk> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b)\<close>
  by (simp add: write_Sync_ndet_write_left[where c = id, unfolded write_is_write0, simplified])

lemma ndet_write_Sync_write0_left :
  \<open>c ` A \<inter> S = {} \<Longrightarrow> b \<in> S \<Longrightarrow> c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> b \<rightarrow> Q = c\<^bold>!\<^bold>!a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk> b \<rightarrow> Q)\<close>
  by (simp add: ndet_write_Sync_write_left[where d = id, unfolded write_is_write0, simplified])

lemma write_Sync_ndet_write0_right :
  \<open>a \<in> S \<Longrightarrow> d ` B \<inter> S = {} \<Longrightarrow> a \<rightarrow> P \<lbrakk>S\<rbrakk> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b = d\<^bold>!\<^bold>!b\<in>B \<rightarrow> (a \<rightarrow> P \<lbrakk>S\<rbrakk> Q b)\<close>
  by (simp add: write_Sync_ndet_write_right[where c = id, unfolded write_is_write0, simplified])

lemma ndet_write_Sync_write0_right :
  \<open>c ` A \<subseteq> S \<Longrightarrow> b \<notin> S \<Longrightarrow> c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> b \<rightarrow> Q = b \<rightarrow> (c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> Q)\<close>
  by (simp add: ndet_write_Sync_write_right[where d = id, unfolded write_is_write0, simplified])



paragraph \<open>\<^const>\<open>write0\<close> and \<^const>\<open>write0\<close>\<close>

lemma write0_Sync_write0 :
  \<open>a \<rightarrow> P \<lbrakk>S\<rbrakk> b \<rightarrow> Q =
   (if b \<in> S then STOP else b \<rightarrow> (a \<rightarrow> P \<lbrakk>S\<rbrakk> Q)) \<box>
   (if a \<in> S then STOP else a \<rightarrow> (P \<lbrakk>S\<rbrakk> b \<rightarrow> Q)) \<box>
   (if a = b \<and> b \<in> S then a \<rightarrow> (P \<lbrakk>S\<rbrakk> Q) else STOP)\<close>
  by (simp add: write_Sync_write[where c = id and d = id, unfolded write_is_write0, simplified])

lemma write0_Sync_write0_bis :
  \<open>(a \<rightarrow> P) \<lbrakk>S\<rbrakk> (b \<rightarrow> Q) =
   (  if a \<in> S
    then   if b \<in> S
         then   if a = b
              then a \<rightarrow> (P \<lbrakk>S\<rbrakk> Q)
              else STOP
         else (b \<rightarrow> ((a \<rightarrow> P) \<lbrakk>S\<rbrakk> Q))
    else   if b \<in> S
         then a \<rightarrow> (P \<lbrakk>S\<rbrakk> (b \<rightarrow> Q))
    else (a \<rightarrow> (P \<lbrakk>S\<rbrakk> (b \<rightarrow> Q))) \<box> (b \<rightarrow> ((a \<rightarrow> P) \<lbrakk>S\<rbrakk> Q)))\<close>
  by (cases \<open>a \<in> S\<close>; cases \<open>b \<in> S\<close>) (auto simp add: write0_Sync_write0 Det_commute)

lemma write0_Inter_write0 :
  \<open>a \<rightarrow> P ||| b \<rightarrow> Q = (a \<rightarrow> (P ||| b \<rightarrow> Q)) \<box> (b \<rightarrow> (a \<rightarrow> P ||| Q))\<close>
  by (simp add: write0_Sync_write0 Det_commute)

lemma write0_Par_write0 :
  \<open>a \<rightarrow> P || b \<rightarrow> Q = (if a = b then a \<rightarrow> (P || Q) else STOP)\<close>
  by (simp add: write0_Sync_write0)



lemma write0_Sync_write0_subset :
  \<open>a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> a \<rightarrow> P \<lbrakk>S\<rbrakk> b \<rightarrow> Q = (if a = b then a \<rightarrow> (P \<lbrakk>S\<rbrakk> Q) else STOP)\<close>
  by (simp add: write_Sync_write_subset[where c = id and d = id, unfolded write_is_write0, simplified])

lemma write0_Sync_write0_indep :
  \<open>a \<notin> S \<Longrightarrow> b \<notin> S \<Longrightarrow> a \<rightarrow> P \<lbrakk>S\<rbrakk> b \<rightarrow> Q = (a \<rightarrow> (P \<lbrakk>S\<rbrakk> b \<rightarrow> Q)) \<box> (b \<rightarrow> (a \<rightarrow> P \<lbrakk>S\<rbrakk> Q))\<close>
  by (simp add: write_Sync_write_indep[where c = id and d = id, unfolded write_is_write0, simplified])

lemma write0_Sync_write0_left :
  \<open>a \<notin> S \<Longrightarrow> b \<in> S \<Longrightarrow> a \<rightarrow> P \<lbrakk>S\<rbrakk> b \<rightarrow> Q = a \<rightarrow> (P \<lbrakk>S\<rbrakk> b \<rightarrow> Q)\<close>
  by (simp add: write_Sync_write_left[where c = id and d = id, unfolded write_is_write0, simplified])

lemma write0_Sync_write0_right :
  \<open>a \<in> S \<Longrightarrow> b \<notin> S \<Longrightarrow> a \<rightarrow> P \<lbrakk>S\<rbrakk> b \<rightarrow> Q = b \<rightarrow> (a \<rightarrow> P \<lbrakk>S\<rbrakk> Q)\<close>
  by (simp add: write_Sync_write_right[where c = id and d = id, unfolded write_is_write0, simplified]) 


paragraph \<open>\<^const>\<open>write\<close> and \<^const>\<open>write0\<close>\<close>

lemma write0_Sync_write :
  \<open>a \<rightarrow> P \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q =
   (if d b \<in> S then STOP else d\<^bold>!b \<rightarrow> (a \<rightarrow> P \<lbrakk>S\<rbrakk> Q)) \<box>
   (if a \<in> S then STOP else a \<rightarrow> (P \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q)) \<box>
   (if a = d b \<and> d b \<in> S then a \<rightarrow> (P \<lbrakk>S\<rbrakk> Q) else STOP)\<close>
  by (simp add: write0_Sync_write0 write_is_write0)

lemma write_Sync_write0 :
  \<open>c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> b \<rightarrow> Q =
   (if b \<in> S then STOP else b \<rightarrow> (c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> Q)) \<box>
   (if c a \<in> S then STOP else c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk> b \<rightarrow> Q)) \<box>
   (if c a = b \<and> b \<in> S then c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk> Q) else STOP)\<close>
  by (simp add: write0_Sync_write0 write_is_write0)


lemma write0_Sync_write_subset :
  \<open>a \<in> S \<Longrightarrow> d b \<in> S \<Longrightarrow>
   a \<rightarrow> P \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q = (if a = d b then a \<rightarrow> (P \<lbrakk>S\<rbrakk> Q) else STOP)\<close>
  by (simp add: write0_Sync_write)

lemma write_Sync_write0_subset :
  \<open>c a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow>
   c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> b \<rightarrow> Q = (if c a = b then c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk> Q) else STOP)\<close>
  by (simp add: write_Sync_write0)


lemma write0_Sync_write_indep :
  \<open>a \<notin> S \<Longrightarrow> d b \<notin> S \<Longrightarrow>
   a \<rightarrow> P \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q = (a \<rightarrow> (P \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q)) \<box> (d\<^bold>!b \<rightarrow> (a \<rightarrow> P \<lbrakk>S\<rbrakk> Q))\<close>
  by (simp add: Det_commute write0_Sync_write)

lemma write_Sync_write0_indep :
  \<open>c a \<notin> S \<Longrightarrow> b \<notin> S \<Longrightarrow>
   c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> b \<rightarrow> Q = (c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk> b \<rightarrow> Q)) \<box> (b \<rightarrow> (c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> Q))\<close>
  by (simp add: Det_commute write_Sync_write0)


lemma write0_Sync_write_left :
  \<open>a \<notin> S \<Longrightarrow> d b \<in> S \<Longrightarrow> a \<rightarrow> P \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q = a \<rightarrow> (P \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q)\<close>
  by (simp add: write0_Sync_write0_left write_is_write0)

lemma write_Sync_write0_left :
  \<open>c a \<notin> S \<Longrightarrow> b \<in> S \<Longrightarrow> c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> b \<rightarrow> Q = c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk> b \<rightarrow> Q)\<close>
  by (simp add: write0_Sync_write0_left write_is_write0)


lemma write0_Sync_write_right :
  \<open>a \<in> S \<Longrightarrow> d b \<notin> S \<Longrightarrow> a \<rightarrow> P \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q = d\<^bold>!b \<rightarrow> (a \<rightarrow> P \<lbrakk>S\<rbrakk> Q)\<close>
  by (simp add: write0_Sync_write0_right write_is_write0)

lemma write_Sync_write0_right :
  \<open>c a \<in> S \<Longrightarrow> b \<notin> S \<Longrightarrow> c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> b \<rightarrow> Q = b \<rightarrow> (c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> Q)\<close>
  by (simp add: Sync_commute write0_Sync_write_left)



subsection \<open>\<^const>\<open>Sync\<close>, \<^const>\<open>SKIP\<close> and \<^const>\<open>STOP\<close>\<close>

subsubsection \<open>\<^const>\<open>SKIP\<close>\<close>

text \<open>Without injectivity, the result is a trivial corollary of
      @{thm read_def} and @{thm Mprefix_Sync_SKIP}.\<close>

lemma read_Sync_SKIP :
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> SKIP r = c\<^bold>?a\<in>(A - c -` S) \<rightarrow> (P a \<lbrakk>S\<rbrakk> SKIP r)\<close> if \<open>inj_on c A\<close>
proof -
  have \<open>c ` (A - c -` S) = c ` A - S\<close> by blast
  show \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> SKIP r = c\<^bold>?a\<in>(A - c -` S) \<rightarrow> (P a \<lbrakk>S\<rbrakk> SKIP r)\<close>
    by (auto simp add: read_def Mprefix_Sync_SKIP \<open>?this\<close> inj_on_diff \<open>inj_on c A\<close>
        intro: mono_Mprefix_eq)
qed

lemma SKIP_Sync_read :
  \<open>inj_on d B \<Longrightarrow> SKIP r \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b = d\<^bold>?b\<in>(B - d -` S) \<rightarrow> (SKIP r \<lbrakk>S\<rbrakk> Q b)\<close>
  by (subst (1 2) Sync_commute) (simp add: read_Sync_SKIP)


corollary write_Sync_SKIP :
  \<open>c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> SKIP r = (if c a \<in> S then STOP else c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk> SKIP r))\<close>
  and SKIP_Sync_write :
  \<open>SKIP r \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q = (if d b \<in> S then STOP else d\<^bold>!b \<rightarrow> (SKIP r \<lbrakk>S\<rbrakk> Q))\<close>
  by (simp_all add: write_def Mprefix_Sync_SKIP SKIP_Sync_Mprefix Diff_triv)

corollary write0_Sync_SKIP :
  \<open>a \<rightarrow> P \<lbrakk>S\<rbrakk> SKIP r = (if a \<in> S then STOP else a \<rightarrow> (P \<lbrakk>S\<rbrakk> SKIP r))\<close>
  and SKIP_Sync_write0 :
  \<open>SKIP r \<lbrakk>S\<rbrakk> b \<rightarrow> Q = (if b \<in> S then STOP else b \<rightarrow> (SKIP r \<lbrakk>S\<rbrakk> Q))\<close>
  by (simp_all add: write0_def Mprefix_Sync_SKIP SKIP_Sync_Mprefix Diff_triv)


lemma ndet_write_Sync_SKIP :
  \<open>c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> SKIP r =
   (  if c ` A \<inter> S = {} then c\<^bold>!\<^bold>!a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk> SKIP r)
    else (c\<^bold>!\<^bold>!a\<in>(A - c -` S) \<rightarrow> (P a \<lbrakk>S\<rbrakk> SKIP r)) \<sqinter> STOP)\<close>
  (is \<open>?lhs = (if c ` A \<inter> S = {} then ?rhs1 else ?rhs2 \<sqinter> STOP)\<close>) if \<open>inj_on c A\<close>
proof (split if_split, intro conjI impI)
  assume \<open>c ` A \<inter> S = {}\<close>
  hence \<open>A - c -` S = A\<close> by blast
  from \<open>c ` A \<inter> S = {}\<close> show \<open>?lhs = ?rhs1\<close>
    by (auto simp add: \<open>?this\<close> ndet_write_is_GlobalNdet_write0 disjoint_iff
        Sync_distrib_GlobalNdet_right write0_Sync_SKIP
        intro!: mono_GlobalNdet_eq split: if_split_asm)
next
  show \<open>?lhs = ?rhs2 \<sqinter> STOP\<close> if \<open>c ` A \<inter> S \<noteq> {}\<close>
  proof (cases \<open>c ` A - S = {}\<close>)
    assume \<open>c ` A - S = {}\<close>
    hence \<open>A - c -` S = {}\<close> by blast
    from \<open>c ` A - S = {}\<close> show \<open>?lhs = ?rhs2 \<sqinter> STOP\<close>
      by (auto simp add: ndet_write_is_GlobalNdet_write0 GlobalNdet_is_STOP_iff
          \<open>?this\<close> Sync_distrib_GlobalNdet_right write0_Sync_SKIP)
  next
    have \<open>c ` (A - c -` S) = c ` A - S\<close> by blast
    show \<open>?lhs = ?rhs2 \<sqinter> STOP\<close> if \<open>c ` A - S \<noteq> {}\<close>
      by (subst Ndet_commute, unfold ndet_write_is_GlobalNdet_write0 Sync_distrib_GlobalNdet_right)
        (auto simp add: GlobalNdet_is_STOP_iff write0_Sync_SKIP
          \<open>?this\<close> \<open>inj_on c A\<close> inj_on_diff
          simp flip: GlobalNdet_factorization_union
          [OF \<open>c ` A \<inter> S \<noteq> {}\<close> \<open>c ` A - S \<noteq> {}\<close>, unfolded Int_Diff_Un]
          intro!: arg_cong2[where f = \<open>(\<sqinter>)\<close>] mono_GlobalNdet_eq)
  qed
qed

corollary SKIP_Sync_ndet_write :
  \<open>inj_on d B \<Longrightarrow>
   SKIP r \<lbrakk>S\<rbrakk> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b =
   (  if d ` B \<inter> S = {} then d\<^bold>!\<^bold>!b\<in>B \<rightarrow> (SKIP r \<lbrakk>S\<rbrakk> Q b)
    else (d\<^bold>!\<^bold>!b\<in>(B - d -` S) \<rightarrow> (SKIP r \<lbrakk>S\<rbrakk> Q b)) \<sqinter> STOP)\<close>
  by (subst (1 2 3) Sync_commute) (simp add: ndet_write_Sync_SKIP)


subsubsection \<open>\<^const>\<open>STOP\<close>\<close>

text \<open>Without injectivity, the result is a trivial corollary of
      @{thm read_def} and @{thm Mprefix_Sync_SKIP}.\<close>

lemma read_Sync_STOP :
  \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> STOP = c\<^bold>?a\<in>(A - c -` S) \<rightarrow> (P a \<lbrakk>S\<rbrakk> STOP)\<close> if \<open>inj_on c A\<close>
proof -
  have \<open>c ` (A - c -` S) = c ` A - S\<close> by blast
  show \<open>c\<^bold>?a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> STOP = c\<^bold>?a\<in>(A - c -` S) \<rightarrow> (P a \<lbrakk>S\<rbrakk> STOP)\<close>
    by (auto simp add: \<open>?this\<close> read_def Mprefix_Sync_STOP inj_on_diff \<open>inj_on c A\<close>
        intro: mono_Mprefix_eq)
qed

lemma STOP_Sync_read :
  \<open>inj_on d B \<Longrightarrow> STOP \<lbrakk>S\<rbrakk> d\<^bold>?b\<in>B \<rightarrow> Q b = d\<^bold>?b\<in>(B - d -` S) \<rightarrow> (STOP \<lbrakk>S\<rbrakk> Q b)\<close>
  by (subst (1 2) Sync_commute) (simp add: read_Sync_STOP)


corollary write_Sync_STOP :
  \<open>c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> STOP = (if c a \<in> S then STOP else c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk> STOP))\<close>
  and STOP_Sync_write :
  \<open>STOP \<lbrakk>S\<rbrakk> d\<^bold>!b \<rightarrow> Q = (if d b \<in> S then STOP else d\<^bold>!b \<rightarrow> (STOP \<lbrakk>S\<rbrakk> Q))\<close>
  by (simp_all add: write_def Mprefix_Sync_STOP STOP_Sync_Mprefix Diff_triv)

corollary write0_Sync_STOP :
  \<open>a \<rightarrow> P \<lbrakk>S\<rbrakk> STOP = (if a \<in> S then STOP else a \<rightarrow> (P \<lbrakk>S\<rbrakk> STOP))\<close>
  and STOP_Sync_write0 :
  \<open>STOP \<lbrakk>S\<rbrakk> b \<rightarrow> Q = (if b \<in> S then STOP else b \<rightarrow> (STOP \<lbrakk>S\<rbrakk> Q))\<close>
  by (simp_all add: write0_def Mprefix_Sync_STOP STOP_Sync_Mprefix Diff_triv)


lemma ndet_write_Sync_STOP :
  \<open>c\<^bold>!\<^bold>!a\<in>A \<rightarrow> P a \<lbrakk>S\<rbrakk> STOP =
   (  if c ` A \<inter> S = {} then c\<^bold>!\<^bold>!a\<in>A \<rightarrow> (P a \<lbrakk>S\<rbrakk> STOP)
    else (c\<^bold>!\<^bold>!a\<in>(A - c -` S) \<rightarrow> (P a \<lbrakk>S\<rbrakk> STOP)) \<sqinter> STOP)\<close>
  (is \<open>?lhs = (if c ` A \<inter> S = {} then ?rhs1 else ?rhs2 \<sqinter> STOP)\<close>) if \<open>inj_on c A\<close>
proof (split if_split, intro conjI impI)
  assume \<open>c ` A \<inter> S = {}\<close>
  hence \<open>A - c -` S = A\<close> by blast
  from \<open>c ` A \<inter> S = {}\<close> show \<open>?lhs = ?rhs1\<close>
    by (auto simp add: \<open>?this\<close> ndet_write_is_GlobalNdet_write0 disjoint_iff
        Sync_distrib_GlobalNdet_right write0_Sync_STOP
        intro!: mono_GlobalNdet_eq split: if_split_asm)
next
  show \<open>?lhs = ?rhs2 \<sqinter> STOP\<close> if \<open>c ` A \<inter> S \<noteq> {}\<close>
  proof (cases \<open>c ` A - S = {}\<close>)
    assume \<open>c ` A - S = {}\<close>
    hence \<open>A - c -` S = {}\<close> by blast
    from \<open>c ` A - S = {}\<close> show \<open>?lhs = ?rhs2 \<sqinter> STOP\<close>
      by (auto simp add: ndet_write_is_GlobalNdet_write0 GlobalNdet_is_STOP_iff
          \<open>?this\<close> Sync_distrib_GlobalNdet_right write0_Sync_STOP)
  next
    have \<open>c ` (A - c -` S) = c ` A - S\<close> by blast
    show \<open>?lhs = ?rhs2 \<sqinter> STOP\<close> if \<open>c ` A - S \<noteq> {}\<close>
      by (subst Ndet_commute, unfold ndet_write_is_GlobalNdet_write0 Sync_distrib_GlobalNdet_right)
        (auto simp add: GlobalNdet_is_STOP_iff write0_Sync_STOP
          \<open>?this\<close> \<open>inj_on c A\<close> inj_on_diff
          simp flip: GlobalNdet_factorization_union
          [OF \<open>c ` A \<inter> S \<noteq> {}\<close> \<open>c ` A - S \<noteq> {}\<close>, unfolded Int_Diff_Un]
          intro!: arg_cong2[where f = \<open>(\<sqinter>)\<close>] mono_GlobalNdet_eq)
  qed
qed

corollary STOP_Sync_ndet_write :
  \<open>inj_on d B \<Longrightarrow>
   STOP \<lbrakk>S\<rbrakk> d\<^bold>!\<^bold>!b\<in>B \<rightarrow> Q b =
   (  if d ` B \<inter> S = {} then d\<^bold>!\<^bold>!b\<in>B \<rightarrow> (STOP \<lbrakk>S\<rbrakk> Q b)
    else (d\<^bold>!\<^bold>!b\<in>(B - d -` S) \<rightarrow> (STOP \<lbrakk>S\<rbrakk> Q b)) \<sqinter> STOP)\<close>
  by (subst (1 2 3) Sync_commute) (simp add: ndet_write_Sync_STOP)




(*<*)
end
  (*>*)