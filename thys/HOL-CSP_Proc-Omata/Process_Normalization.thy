(***********************************************************************************
 * Copyright (c) 2025 Université Paris-Saclay
 *
 * Author: Benoît Ballenghien, Université Paris-Saclay,
 *         CNRS, ENS Paris-Saclay, LMF
 * Author: Burkhart Wolff, Université Paris-Saclay,
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


chapter \<open>ProcOmata: Functional Automata embedded into CSP Processes\<close>

(*<*)
theory Process_Normalization
  imports "HOL-CSP_PTick"
begin
  (*>*)


text \<open>
We will often have to perform induction on both the list of automata
and the list of states, provided that they have the same length.\<close>

lemma induct_2_lists012 [consumes 1, case_names Nil single Cons] : 
  \<open>\<lbrakk>length xs = length ys; P [] []; \<And>x1 y1. P [x1] [y1];
    \<And>x1 x2 xs y1 y2 ys. length xs = length ys \<Longrightarrow> P xs ys \<Longrightarrow>
                         P (x2 # xs) (y2 # ys) \<Longrightarrow> P (x1 # x2 # xs) (y1 # y2 # ys)\<rbrakk>
   \<Longrightarrow> P xs ys\<close>
  by (induct xs arbitrary: ys rule: induct_list012)
    (auto simp add: Suc_length_conv length_Suc_conv)

lemma nat_induct_012 [case_names 0 1 2 Suc]:
  \<open>\<lbrakk>P 0; P (Suc 0); P (Suc (Suc 0)); \<And>k. Suc (Suc 0) \<le> k \<Longrightarrow> P k \<Longrightarrow> P (Suc k)\<rbrakk> \<Longrightarrow> P n\<close>
  by (metis One_nat_def Suc_1 less_2_cases_iff linorder_not_le nat_induct)



text \<open>
The following results will be moved to \<^session>\<open>Restriction_Spaces\<close> in the future.
\<close>

lemma restriction_shift_iterated :
  \<open>restriction_shift (f ^^ k) (int k * m)\<close>
  if \<open>restriction_shift f m\<close> for f :: \<open>'a \<Rightarrow> 'a :: restriction_space\<close>
proof (induct k)
  show \<open>restriction_shift (f ^^ 0) (int 0 * m)\<close>
    by (simp add: restriction_shiftI)
next
  fix k assume * : \<open>restriction_shift (f ^^ k) (int k * m)\<close>
  have \<open>restriction_shift (f ^^ Suc k) (int (Suc k) * m) \<longleftrightarrow>
        restriction_shift (\<lambda>x. f ((f ^^ k) x)) (int k * m + m)\<close>
    by (simp add: comp_def distrib_left mult.commute add.commute)
  also have \<dots> by (fact restriction_shift_comp_restriction_shift[OF that "*"])
  finally show \<open>restriction_shift (f ^^ Suc k) (int (Suc k) * m)\<close> .
qed

lemma non_destructive_iterated :
  \<open>non_destructive f \<Longrightarrow> non_destructive (f ^^ k)\<close>
  for f :: \<open>'a \<Rightarrow> 'a :: restriction_space\<close>
  by (metis mult.commute mult_zero_left non_destructive_def non_destructive_on_def
      restriction_shift_def restriction_shift_iterated)

lemma constructive_iterated :
  \<open>constructive (f ^^ k)\<close> if \<open>0 < k\<close> \<open>constructive f\<close>
for f :: \<open>'a \<Rightarrow> 'a :: restriction_space\<close>
proof -
  from \<open>constructive f\<close> have \<open>restriction_shift f 1\<close>
    unfolding constructive_def constructive_on_def restriction_shift_def by blast
  with restriction_shift_iterated
  have \<open>restriction_shift (f ^^ k) (int k * 1)\<close> .
  hence \<open>restriction_shift (f ^^ k) (int k)\<close> by simp
  with \<open>0 < k\<close> show \<open>constructive (f ^^ k)\<close>
    by (metis One_nat_def constructive_def constructive_on_def
        less_eq_Suc_le nat_int_comparison(3) of_nat_1_eq_iff
        restriction_shift_def restriction_shift_imp_restriction_shift_le )
qed


lemma restriction_fix_unique_iterated :
  \<open>\<lbrakk>0 < k; constructive f; (f ^^ k) x = x\<rbrakk> \<Longrightarrow> (\<upsilon> x. f x) = x\<close>
  by (metis constructive_iterated funpow_swap1 restriction_fix_unique)


lemma restriction_fix_iterated :
  \<open>0 < k \<Longrightarrow> constructive f \<Longrightarrow> (\<upsilon> x. (f ^^ k) x) = (\<upsilon> x. f x)\<close>
  by (metis constructive_iterated restriction_fix_eq restriction_fix_unique_iterated)



corollary restriction_fix_ind_iterated
  [consumes 1, case_names constructive adm base step]:
  \<open>P (\<upsilon> x. f x)\<close> if \<open>0 < k\<close> \<open>constructive f\<close> \<open>adm\<^sub>\<down> P\<close> \<open>P x\<close> \<open>\<And>x. P x \<Longrightarrow> P ((f ^^ k) x)\<close>
proof -
  from constructive_iterated that(1, 2) have \<open>constructive (f ^^ k)\<close> .
  from restriction_fix_ind[OF this that(3-5)] have \<open>P (\<upsilon> x. (f ^^ k) x)\<close> .
  also from restriction_fix_iterated that(1, 2) have \<open>(\<upsilon> x. (f ^^ k) x) = (\<upsilon> x. f x)\<close> .
  finally show \<open>P (\<upsilon> x. f x)\<close> .
qed




section \<open>Definitions\<close>


subsection \<open>Non-deterministic and deterministic Automata\<close>

unbundle option_type_syntax

type_synonym ('\<sigma>, 'a) enabl  = \<open>'\<sigma> \<Rightarrow> 'a set\<close>
type_synonym ('\<sigma>, 'a, '\<sigma>') trans = \<open>'\<sigma> \<Rightarrow> 'a \<Rightarrow> '\<sigma>'\<close>
type_synonym ('\<sigma>, 'a) trans\<^sub>d  = \<open>('\<sigma>, 'a, '\<sigma> option) trans\<close>
type_synonym ('\<sigma>, 'a) trans\<^sub>n\<^sub>d = \<open>('\<sigma>, 'a, '\<sigma> set) trans\<close>

record ('\<sigma>, 'a, '\<sigma>', 'r) A =
  \<tau> :: \<open>('\<sigma>, 'a, '\<sigma>') trans\<close>
  \<omega> :: \<open>'\<sigma> \<Rightarrow> 'r\<close>

type_synonym ('\<sigma>, 'a, 'r) A\<^sub>d = \<open>('\<sigma>, 'a, '\<sigma> option, 'r option) A\<close>
type_synonym ('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>d_scheme = \<open>('\<sigma>, 'a, '\<sigma> option, 'r option, '\<alpha>) A_scheme\<close>
type_synonym ('\<sigma>, 'a, 'r) A\<^sub>n\<^sub>d = \<open>('\<sigma>, 'a, '\<sigma> set, 'r set) A\<close>
type_synonym ('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme = \<open>('\<sigma>, 'a, '\<sigma> set, 'r set, '\<alpha>) A_scheme\<close>



subsection \<open>Enableness\<close>

consts \<epsilon> :: \<open>('\<sigma>, 'a, '\<sigma>', 'r', '\<alpha>) A_scheme \<Rightarrow> ('\<sigma>, 'a) enabl\<close>
overloading
  \<epsilon>\<^sub>d \<equiv> \<open>\<epsilon> :: ('\<sigma>, 'a, '\<sigma> option, 'r', '\<alpha>) A_scheme \<Rightarrow> ('\<sigma>, 'a) enabl\<close>
  \<epsilon>\<^sub>n\<^sub>d \<equiv> \<open>\<epsilon> :: ('\<sigma>, 'a, '\<sigma> set, 'r', '\<alpha>) A_scheme \<Rightarrow> ('\<sigma>, 'a) enabl\<close>
begin
fun \<epsilon>\<^sub>d :: \<open>('\<sigma>, 'a, '\<sigma> option, 'r', '\<alpha>) A_scheme \<Rightarrow> ('\<sigma>, 'a) enabl\<close>
  where \<open>\<epsilon>\<^sub>d A \<sigma> = {a. \<tau> A \<sigma> a \<noteq> \<diamond>}\<close>
fun \<epsilon>\<^sub>n\<^sub>d :: \<open>('\<sigma>, 'a, '\<sigma> set, 'r', '\<alpha>) A_scheme \<Rightarrow> ('\<sigma>, 'a) enabl\<close>
  where \<open>\<epsilon>\<^sub>n\<^sub>d A \<sigma> = {a. \<tau> A \<sigma> a \<noteq> {}}\<close>
end

lemmas \<epsilon>_simps[simp del] = \<epsilon>\<^sub>d.simps \<epsilon>\<^sub>n\<^sub>d.simps


subsection \<open>States allowing Termination\<close>

consts \<rho> :: \<open>('\<sigma>, 'a, '\<sigma>', 'r', '\<alpha>) A_scheme \<Rightarrow> '\<sigma> set\<close>
overloading
  \<rho>\<^sub>d \<equiv> \<open>\<rho> :: ('\<sigma>, 'a, '\<sigma>', 'r option, '\<alpha>) A_scheme \<Rightarrow> '\<sigma> set\<close>
  \<rho>\<^sub>n\<^sub>d \<equiv> \<open>\<rho> :: ('\<sigma>, 'a, '\<sigma>', 'r set, '\<alpha>) A_scheme \<Rightarrow> '\<sigma> set\<close>
begin
fun \<rho>\<^sub>d :: \<open>('\<sigma>, 'a, '\<sigma>', 'r option, '\<alpha>) A_scheme \<Rightarrow> '\<sigma> set\<close>
  where \<open>\<rho>\<^sub>d A = {\<sigma>. \<omega> A \<sigma> \<noteq> \<diamond>}\<close>
fun \<rho>\<^sub>n\<^sub>d :: \<open>('\<sigma>, 'a, '\<sigma>', 'r set, '\<alpha>) A_scheme \<Rightarrow> '\<sigma> set\<close>
  where \<open>\<rho>\<^sub>n\<^sub>d A = {\<sigma>. \<omega> A \<sigma> \<noteq> {}}\<close>
end

lemmas \<rho>_simps[simp del] = \<rho>\<^sub>d.simps \<rho>\<^sub>n\<^sub>d.simps


subsection \<open>Reachability\<close>

inductive_set \<R>\<^sub>d :: \<open>('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>d_scheme \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma> set\<close>
  for A :: \<open>('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>d_scheme\<close> and \<sigma> :: '\<sigma>
  where init : \<open>\<sigma>  \<in> \<R>\<^sub>d A \<sigma>\<close>
  |     step : \<open>\<sigma>' \<in> \<R>\<^sub>d A \<sigma> \<Longrightarrow> \<lfloor>\<sigma>''\<rfloor> = \<tau> A \<sigma>' a \<Longrightarrow> \<sigma>'' \<in> \<R>\<^sub>d A \<sigma>\<close>

inductive_set \<R>\<^sub>n\<^sub>d :: \<open>('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma> set\<close>
  for A :: \<open>('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme\<close> and \<sigma> :: '\<sigma>
  where init : \<open>\<sigma>  \<in> \<R>\<^sub>n\<^sub>d A \<sigma>\<close>
  |     step : \<open>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma> \<Longrightarrow> \<sigma>'' \<in> \<tau> A \<sigma>' a \<Longrightarrow> \<sigma>'' \<in> \<R>\<^sub>n\<^sub>d A \<sigma>\<close>


lemma \<R>\<^sub>d_trans: \<open>\<sigma>'' \<in> \<R>\<^sub>d A \<sigma>' \<Longrightarrow> \<sigma>' \<in> \<R>\<^sub>d A \<sigma> \<Longrightarrow> \<sigma>'' \<in> \<R>\<^sub>d A \<sigma>\<close>
  by (induct rule: \<R>\<^sub>d.induct, simp add: \<R>\<^sub>d.init) (meson \<R>\<^sub>d.step)

lemma \<R>\<^sub>n\<^sub>d_trans: \<open>\<sigma>'' \<in> \<R>\<^sub>n\<^sub>d A \<sigma>' \<Longrightarrow> \<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma> \<Longrightarrow> \<sigma>'' \<in> \<R>\<^sub>n\<^sub>d A \<sigma>\<close>
  by (induct rule: \<R>\<^sub>n\<^sub>d.induct, simp add: \<R>\<^sub>n\<^sub>d.init) (meson \<R>\<^sub>n\<^sub>d.step)



subsection \<open>Morphisms\<close>

text \<open>
Our morphisms are defined considering that,
except from \<^const>\<open>\<tau>\<close>, the fields remain unchanged.\<close>

definition from_det_to_ndet ::
  \<open>('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>d_scheme \<Rightarrow> ('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme\<close>
  where \<open>from_det_to_ndet A \<equiv>
         \<lparr>\<tau> = \<lambda>\<sigma> a. case \<tau> A \<sigma> a of \<lfloor>\<sigma>'\<rfloor> \<Rightarrow> {\<sigma>'} | \<diamond> \<Rightarrow> {},
          \<omega> = \<lambda>\<sigma>. case \<omega> A \<sigma> of \<lfloor>r\<rfloor> \<Rightarrow> {r} | \<diamond> \<Rightarrow> {}, \<dots> = more A\<rparr>\<close>
definition from_ndet_to_det ::
  \<open>('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme \<Rightarrow> ('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>d_scheme\<close>
  where \<open>from_ndet_to_det A \<equiv>
         \<lparr>\<tau> = \<lambda>\<sigma> a. if \<tau> A \<sigma> a = {} then \<diamond> else \<lfloor>THE \<sigma>'. \<sigma>' \<in> \<tau> A \<sigma> a\<rfloor>,
          \<omega> = \<lambda>\<sigma>. if \<omega> A \<sigma> = {} then \<diamond> else \<lfloor>THE r. r \<in> \<omega> A \<sigma>\<rfloor>, \<dots> = more A\<rparr>\<close>

definition from_\<sigma>_to_\<sigma>s\<^sub>d ::
  \<open>('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>d_scheme \<Rightarrow> ('\<sigma> list, 'a, 'r, '\<alpha>) A\<^sub>d_scheme\<close>
  where \<open>from_\<sigma>_to_\<sigma>s\<^sub>d A \<equiv>
         \<lparr>\<tau> = \<lambda>\<sigma>s a. case \<tau> A (hd \<sigma>s) a of \<lfloor>\<sigma>'\<rfloor> \<Rightarrow> \<lfloor>[\<sigma>']\<rfloor> | \<diamond> \<Rightarrow> \<diamond>,
          \<omega> = \<lambda>\<sigma>s. \<omega> A (hd \<sigma>s), \<dots> = more A\<rparr>\<close>
definition from_\<sigma>_to_\<sigma>s\<^sub>n\<^sub>d ::
  \<open>('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme \<Rightarrow> ('\<sigma> list, 'a, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme\<close>
  where \<open>from_\<sigma>_to_\<sigma>s\<^sub>n\<^sub>d A \<equiv>
         \<lparr>\<tau> = \<lambda>\<sigma>s a. {[\<sigma>'] |\<sigma>'. \<sigma>' \<in> \<tau> A (hd \<sigma>s) a},
          \<omega> = \<lambda>\<sigma>s. \<omega> A (hd \<sigma>s), \<dots> = more A\<rparr>\<close>

definition from_\<sigma>s_to_\<sigma>\<^sub>d ::
  \<open>('\<sigma> list, 'a, 'r, '\<alpha>) A\<^sub>d_scheme \<Rightarrow> ('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>d_scheme\<close>
  where \<open>from_\<sigma>s_to_\<sigma>\<^sub>d A \<equiv>
         \<lparr>\<tau> = \<lambda>\<sigma> a. case \<tau> A [\<sigma>] a of \<lfloor>\<sigma>s'\<rfloor> \<Rightarrow> \<lfloor>hd \<sigma>s'\<rfloor> | \<diamond> \<Rightarrow> \<diamond>,
          \<omega> = \<lambda>\<sigma>. \<omega> A [\<sigma>], \<dots> = more A\<rparr>\<close>
definition from_\<sigma>s_to_\<sigma>\<^sub>n\<^sub>d ::
  \<open>('\<sigma> list, 'a, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme \<Rightarrow> ('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme\<close>
  where \<open>from_\<sigma>s_to_\<sigma>\<^sub>n\<^sub>d A \<equiv>
         \<lparr>\<tau> = \<lambda>\<sigma> a. {hd \<sigma>s' |\<sigma>s'. \<sigma>s' \<in> \<tau> A [\<sigma>] a},
          \<omega> = \<lambda>\<sigma>. \<omega> A [\<sigma>], \<dots> = more A\<rparr>\<close>

definition from_singl_to_list\<^sub>d ::
  \<open>('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>d_scheme \<Rightarrow> ('\<sigma> list, 'a, 'r list, '\<alpha>) A\<^sub>d_scheme\<close>
  where \<open>from_singl_to_list\<^sub>d A \<equiv>
         \<lparr>\<tau> = \<lambda>\<sigma>s a. case \<tau> A (hd \<sigma>s) a of \<lfloor>\<sigma>'\<rfloor> \<Rightarrow> \<lfloor>[\<sigma>']\<rfloor> | \<diamond> \<Rightarrow> \<diamond>,
          \<omega> = \<lambda>\<sigma>s. case \<omega> A (hd \<sigma>s) of \<lfloor>r\<rfloor> \<Rightarrow> \<lfloor>[r]\<rfloor> | \<diamond> \<Rightarrow> \<diamond>, \<dots> = more A\<rparr>\<close>
definition from_singl_to_list\<^sub>n\<^sub>d ::
  \<open>('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme \<Rightarrow> ('\<sigma> list, 'a, 'r list, '\<alpha>) A\<^sub>n\<^sub>d_scheme\<close>
  where \<open>from_singl_to_list\<^sub>n\<^sub>d A \<equiv>
         \<lparr>\<tau> = \<lambda>\<sigma>s a. {[\<sigma>'] |\<sigma>'. \<sigma>' \<in> \<tau> A (hd \<sigma>s) a},
          \<omega> = \<lambda>\<sigma>s. {[r] |r. r \<in> \<omega> A (hd \<sigma>s)}, \<dots> = more A\<rparr>\<close>

definition from_list_to_singl\<^sub>d ::
  \<open>('\<sigma> list, 'a, 'r list, '\<alpha>) A\<^sub>d_scheme \<Rightarrow> ('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>d_scheme\<close>
  where \<open>from_list_to_singl\<^sub>d A \<equiv>
         \<lparr>\<tau> = \<lambda>\<sigma> a. case \<tau> A [\<sigma>] a of \<lfloor>\<sigma>s'\<rfloor> \<Rightarrow> \<lfloor>hd \<sigma>s'\<rfloor> | \<diamond> \<Rightarrow> \<diamond>,
          \<omega> = \<lambda>\<sigma>. case \<omega> A [\<sigma>] of \<lfloor>rs\<rfloor> \<Rightarrow> \<lfloor>hd rs\<rfloor> | \<diamond> \<Rightarrow> \<diamond>, \<dots> = more A\<rparr>\<close>
definition from_list_to_singl\<^sub>n\<^sub>d ::
  \<open>('\<sigma> list, 'a, 'r list, '\<alpha>) A\<^sub>n\<^sub>d_scheme \<Rightarrow> ('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme\<close>
  where \<open>from_list_to_singl\<^sub>n\<^sub>d A \<equiv>
         \<lparr>\<tau> = \<lambda>\<sigma> a. {hd \<sigma>s' |\<sigma>s'. \<sigma>s' \<in> \<tau> A [\<sigma>] a},
          \<omega> = \<lambda>\<sigma>. {hd rs |rs. rs \<in> \<omega> A [\<sigma>]}, \<dots> = more A\<rparr>\<close>

lemmas det_ndet_conv_defs  = from_det_to_ndet_def from_ndet_to_det_def
  and      \<sigma>_\<sigma>s_conv_defs  = from_\<sigma>_to_\<sigma>s\<^sub>d_def from_\<sigma>_to_\<sigma>s\<^sub>n\<^sub>d_def
  from_\<sigma>s_to_\<sigma>\<^sub>d_def from_\<sigma>s_to_\<sigma>\<^sub>n\<^sub>d_def
  and singl_list_conv_defs = from_singl_to_list\<^sub>d_def from_singl_to_list\<^sub>n\<^sub>d_def
  from_list_to_singl\<^sub>d_def from_list_to_singl\<^sub>n\<^sub>d_def


bundle functional_automata_morphisms_syntax begin

notation from_det_to_ndet (\<open>\<llangle>_\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<close> [0])
notation from_ndet_to_det (\<open>\<llangle>_\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<close> [0])
notation from_\<sigma>_to_\<sigma>s\<^sub>d (\<open>\<^sub>d\<llangle>_\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<close> [0])
notation from_\<sigma>_to_\<sigma>s\<^sub>n\<^sub>d (\<open>\<^sub>n\<^sub>d\<llangle>_\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<close> [0])
notation from_\<sigma>s_to_\<sigma>\<^sub>d (\<open>\<^sub>d\<llangle>_\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma>\<close> [0])
notation from_\<sigma>s_to_\<sigma>\<^sub>n\<^sub>d (\<open>\<^sub>n\<^sub>d\<llangle>_\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma>\<close> [0])
notation from_singl_to_list\<^sub>d (\<open>\<^sub>d\<llangle>_\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<close> [0])
notation from_singl_to_list\<^sub>n\<^sub>d (\<open>\<^sub>n\<^sub>d\<llangle>_\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<close> [0])
notation from_list_to_singl\<^sub>d (\<open>\<^sub>d\<llangle>_\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<close> [0])
notation from_list_to_singl\<^sub>n\<^sub>d (\<open>\<^sub>n\<^sub>d\<llangle>_\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<close> [0])

end


unbundle functional_automata_morphisms_syntax


lemma morphisms_A_scheme_more_simps [simp] :
  \<open>more \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d = more A\<close> \<open>more \<llangle>B\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d = more B\<close>
  \<open>more \<^sub>d\<llangle>C\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s = more C\<close> \<open>more \<^sub>n\<^sub>d\<llangle>D\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s = more D\<close>
  \<open>more \<^sub>d\<llangle>E\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma> = more E\<close> \<open>more \<^sub>n\<^sub>d\<llangle>F\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma> = more F\<close>
  \<open>more \<^sub>d\<llangle>G\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t = more G\<close> \<open>more \<^sub>n\<^sub>d\<llangle>H\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t = more H\<close>
  \<open>more \<^sub>d\<llangle>I\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l = more I\<close> \<open>more \<^sub>n\<^sub>d\<llangle>J\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l = more J\<close>
  by (simp_all add: det_ndet_conv_defs \<sigma>_\<sigma>s_conv_defs singl_list_conv_defs)


subsection \<open>Generic update Functions\<close>

definition update_both  where \<open>update_both  A\<^sub>0 A\<^sub>1 \<sigma>\<^sub>0 \<sigma>\<^sub>1 e f \<equiv> f (\<tau> A\<^sub>0 \<sigma>\<^sub>0 e) (\<tau> A\<^sub>1 \<sigma>\<^sub>1 e)\<close>

definition update_left  where \<open>update_left  A\<^sub>0 \<sigma>\<^sub>0 \<sigma>\<^sub>1 e f g  \<equiv> f (\<tau> A\<^sub>0 \<sigma>\<^sub>0 e) (g \<sigma>\<^sub>1)\<close>

definition update_right where \<open>update_right A\<^sub>1 \<sigma>\<^sub>0 \<sigma>\<^sub>1 e f g  \<equiv> f (g \<sigma>\<^sub>0) (\<tau> A\<^sub>1 \<sigma>\<^sub>1 e)\<close>

lemmas update_defs[simp] = update_both_def update_left_def update_right_def

abbreviation f_up_set where \<open>f_up_set f B C \<equiv> {f s t| s t. (s, t) \<in> B \<times> C}\<close>

abbreviation f_up_opt where \<open>f_up_opt f s t \<equiv> case s of \<diamond> \<Rightarrow> \<diamond> | \<lfloor>s'\<rfloor> \<Rightarrow> map_option (f s') t\<close>





subsection \<open>Assumptions on Automata\<close>

(*required hypothesis when we will need continuity*)
definition finite_trans :: \<open>('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme \<Rightarrow> bool\<close>
  where \<open>finite_trans A \<equiv> \<forall>\<sigma> a. finite (\<tau> A \<sigma> a)\<close>

lemma finite_trans_morphisms_simps[simp]: 
  \<open>finite_trans \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<close>
  \<open>finite_trans B \<Longrightarrow> finite_trans \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<close>
  \<open>finite_trans C \<Longrightarrow> finite_trans \<^sub>n\<^sub>d\<llangle>C\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma>\<close>
  \<open>finite_trans D \<Longrightarrow> finite_trans \<^sub>n\<^sub>d\<llangle>D\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<close>
  \<open>finite_trans E \<Longrightarrow> finite_trans \<^sub>n\<^sub>d\<llangle>E\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<close>                       
  unfolding det_ndet_conv_defs \<sigma>_\<sigma>s_conv_defs singl_list_conv_defs finite_trans_def
  by (simp_all add: option.case_eq_if)


definition at_most_1_elem :: \<open>('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme \<Rightarrow> bool\<close>
  where \<open>at_most_1_elem A \<equiv>
         (\<forall>\<sigma> a. \<tau> A \<sigma> a = {} \<or> (\<exists>\<sigma>'. \<tau> A \<sigma> a = {\<sigma>'})) \<and>
         (\<forall>\<sigma>. \<omega> A \<sigma> = {} \<or> (\<exists>r. \<omega> A \<sigma> = {r}))\<close>

lemma at_most_1_elem_def_bis :
  \<open>at_most_1_elem A \<longleftrightarrow> (\<forall>\<sigma> a. \<exists>\<sigma>'. \<tau> A \<sigma> a \<subseteq> {\<sigma>'}) \<and> (\<forall>\<sigma>. \<exists>r. \<omega> A \<sigma> \<subseteq> {r})\<close>
  by (auto simp add: at_most_1_elem_def subset_iff)
    (((metis empty_iff singleton_iff)+)[2],
      ((metis equals0D is_singletonI' is_singleton_some_elem)+)[2])

lemma at_most_1_elemI :
  \<open>\<lbrakk>\<And>\<sigma> a. \<tau> A \<sigma> a = {} \<or> (\<exists>\<sigma>'. \<tau> A \<sigma> a = {\<sigma>'});
    \<And>\<sigma>. \<omega> A \<sigma> = {} \<or> (\<exists>r. \<omega> A \<sigma> = {r})\<rbrakk> \<Longrightarrow> at_most_1_elem A\<close>
  by (simp add: at_most_1_elem_def)

lemma at_most_1_elemE :
  \<open>\<lbrakk>\<tau> A \<sigma> a = {} \<Longrightarrow> thesis; \<And>\<sigma>'. \<tau> A \<sigma> a = {\<sigma>'} \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis\<close>
  \<open>\<lbrakk>\<omega> A \<sigma> = {} \<Longrightarrow> thesis; \<And>r. \<omega> A \<sigma> = {r} \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis\<close>
  if \<open>at_most_1_elem A\<close>
  by (meson at_most_1_elem_def \<open>at_most_1_elem A\<close>)+



definition at_most_1_elem_trans :: \<open>('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme \<Rightarrow> bool\<close>
  where \<open>at_most_1_elem_trans A \<equiv> \<forall>\<sigma> a. \<tau> A \<sigma> a = {} \<or> (\<exists>\<sigma>'. \<tau> A \<sigma> a = {\<sigma>'})\<close>

lemma at_most_1_elem_trans_def_bis :
  \<open>at_most_1_elem_trans A \<longleftrightarrow> (\<forall>\<sigma> a. \<exists>\<sigma>'. \<tau> A \<sigma> a \<subseteq> {\<sigma>'})\<close>
  by (auto simp add: at_most_1_elem_trans_def subset_iff)
    (metis empty_iff singleton_iff,
      metis equals0D is_singletonI' is_singleton_some_elem)

lemma at_most_1_elem_transI :
  \<open>\<lbrakk>\<And>\<sigma> a. \<tau> A \<sigma> a = {} \<or> (\<exists>\<sigma>'. \<tau> A \<sigma> a = {\<sigma>'})\<rbrakk> \<Longrightarrow> at_most_1_elem_trans A\<close>
  by (simp add: at_most_1_elem_trans_def)

lemma at_most_1_elem_transE :
  \<open>\<lbrakk>\<tau> A \<sigma> a = {} \<Longrightarrow> thesis; \<And>\<sigma>'. \<tau> A \<sigma> a = {\<sigma>'} \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis\<close>
  if \<open>at_most_1_elem_trans A\<close>
  by (meson at_most_1_elem_trans_def \<open>at_most_1_elem_trans A\<close>)+

lemma at_most_1_elem_imp_at_most_1_elem_trans :
  \<open>at_most_1_elem A \<Longrightarrow> at_most_1_elem_trans A\<close>
  by (simp add: at_most_1_elem_def at_most_1_elem_trans_def)



definition length_1_trans\<^sub>d :: \<open>('\<sigma> list, 'a, 'r, '\<alpha>) A\<^sub>d_scheme \<Rightarrow> bool\<close>
  where \<open>length_1_trans\<^sub>d A \<equiv>
         \<forall>\<sigma>s a. case \<tau> A \<sigma>s a of \<diamond> \<Rightarrow> True | \<lfloor>\<sigma>s'\<rfloor> \<Rightarrow> length \<sigma>s' = Suc 0\<close>

lemma length_1_trans\<^sub>dI :
  \<open>\<lbrakk>\<And>\<sigma>s a \<sigma>s'. \<tau> A \<sigma>s a = \<lfloor>\<sigma>s'\<rfloor> \<Longrightarrow> length \<sigma>s' = Suc 0\<rbrakk> \<Longrightarrow> length_1_trans\<^sub>d A\<close>
  by (simp add: length_1_trans\<^sub>d_def split: option.split)

lemma length_1_trans\<^sub>dE :
  \<open>\<lbrakk>length_1_trans\<^sub>d A; \<tau> A \<sigma>s a = \<lfloor>\<sigma>s'\<rfloor>; \<And>\<sigma>. \<sigma>s' = [\<sigma>] \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis\<close>
  by (simp add: length_1_trans\<^sub>d_def split: option.split_asm)
    (metis (no_types) length_0_conv length_Suc_conv)


definition length_1_trans\<^sub>n\<^sub>d :: \<open>('\<sigma> list, 'a, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme \<Rightarrow> bool\<close>
  where \<open>length_1_trans\<^sub>n\<^sub>d A \<equiv> \<forall>\<sigma>s a. \<forall>\<sigma>s' \<in> \<tau> A \<sigma>s a. length \<sigma>s' = Suc 0\<close>

lemma length_1_trans\<^sub>n\<^sub>dI :
  \<open>\<lbrakk>\<And>\<sigma>s a \<sigma>s'. \<sigma>s' \<in> \<tau> A \<sigma>s a \<Longrightarrow> length \<sigma>s' = Suc 0\<rbrakk> \<Longrightarrow> length_1_trans\<^sub>n\<^sub>d A\<close>
  by (simp add: length_1_trans\<^sub>n\<^sub>d_def split: option.split)

lemma length_1_trans\<^sub>n\<^sub>dE :
  \<open>\<lbrakk>length_1_trans\<^sub>n\<^sub>d A; \<sigma>s' \<in> \<tau> A \<sigma>s a; \<And>\<sigma>. \<sigma>s' = [\<sigma>] \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis\<close>
  by (simp add: length_1_trans\<^sub>n\<^sub>d_def split: option.split_asm)
    (metis (no_types) length_0_conv length_Suc_conv)


definition length_1\<^sub>d :: \<open>('\<sigma> list, 'a, 'r list, '\<alpha>) A\<^sub>d_scheme \<Rightarrow> bool\<close>
  where \<open>length_1\<^sub>d A \<equiv>
         (\<forall>\<sigma>s a. case \<tau> A \<sigma>s a of \<diamond> \<Rightarrow> True | \<lfloor>\<sigma>s'\<rfloor> \<Rightarrow> length \<sigma>s' = Suc 0) \<and>
         (\<forall>\<sigma>s. case \<omega> A \<sigma>s of \<diamond> \<Rightarrow> True | \<lfloor>rs\<rfloor> \<Rightarrow> length rs = Suc 0)\<close>

lemma length_1\<^sub>dI :
  \<open>\<lbrakk>\<And>\<sigma>s a \<sigma>s'. \<tau> A \<sigma>s a = \<lfloor>\<sigma>s'\<rfloor> \<Longrightarrow> length \<sigma>s' = Suc 0;
    \<And>\<sigma>s rs. \<omega> A \<sigma>s = \<lfloor>rs\<rfloor> \<Longrightarrow> length rs = Suc 0\<rbrakk> \<Longrightarrow> length_1\<^sub>d A\<close>
  by (simp add: length_1\<^sub>d_def split: option.split)

lemma length_1\<^sub>dE :
  \<open>\<lbrakk>length_1\<^sub>d A; \<tau> A \<sigma>s a = \<lfloor>\<sigma>s'\<rfloor>; \<And>\<sigma>. \<sigma>s' = [\<sigma>] \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis\<close>
  \<open>\<lbrakk>length_1\<^sub>d A; \<omega> A \<sigma>s = \<lfloor>rs\<rfloor>; \<And>r. rs = [r] \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis\<close>
  by (simp add: length_1\<^sub>d_def split: option.split_asm,
      metis (no_types) length_0_conv length_Suc_conv)+


definition length_1\<^sub>n\<^sub>d :: \<open>('\<sigma> list, 'a, 'r list, '\<alpha>) A\<^sub>n\<^sub>d_scheme \<Rightarrow> bool\<close>
  where \<open>length_1\<^sub>n\<^sub>d A \<equiv> (\<forall>\<sigma>s a. \<forall>\<sigma>s' \<in> \<tau> A \<sigma>s a. length \<sigma>s' = Suc 0) \<and>
                        (\<forall>\<sigma>s. \<forall>rs \<in> \<omega> A \<sigma>s. length rs = Suc 0)\<close>

lemma length_1\<^sub>n\<^sub>dI :
  \<open>\<lbrakk>\<And>\<sigma>s a \<sigma>s'. \<sigma>s' \<in> \<tau> A \<sigma>s a \<Longrightarrow> length \<sigma>s' = Suc 0;
    \<And>\<sigma>s rs. rs \<in> \<omega> A \<sigma>s \<Longrightarrow> length rs = Suc 0\<rbrakk> \<Longrightarrow> length_1\<^sub>n\<^sub>d A\<close>
  by (simp add: length_1\<^sub>n\<^sub>d_def split: option.split)

lemma length_1\<^sub>n\<^sub>dE :
  \<open>\<lbrakk>length_1\<^sub>n\<^sub>d A; \<sigma>s' \<in> \<tau> A \<sigma>s a; \<And>\<sigma>. \<sigma>s' = [\<sigma>] \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis\<close>
  \<open>\<lbrakk>length_1\<^sub>n\<^sub>d A; rs \<in> \<omega> A \<sigma>s; \<And>r. rs = [r] \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis\<close>
  by (simp add: length_1\<^sub>n\<^sub>d_def split: option.split_asm,
      metis (no_types) length_0_conv length_Suc_conv)+

(* abbreviation card_trans_le1 :: \<open>('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme \<Rightarrow> bool\<close>
  where \<open>card_trans_le1 A \<equiv> \<forall>s e. card (\<tau> A s e) \<le> Suc 0\<close>

lemma finite_trans_conj_card_trans_le1_is:
  \<open>finite_trans A \<and> card_trans_le1 A \<longleftrightarrow> (\<forall>s e.  \<tau> A s e = {} \<or> (\<exists>!t. \<tau> A s e = {t}))\<close>
  by (auto, metis card_1_singleton_iff card_mono empty_subsetI insert_subset le_antisym,
      metis finite.simps, metis card_1_singleton_iff card_eq_0_iff le_eq_less_or_eq less_Suc_eq_le)

lemma finite_trans_imp_card_trans_le1_is:
  \<open>finite_trans A \<Longrightarrow> card_trans_le1 A \<longleftrightarrow> (\<forall>s e.  \<tau> A s e = {} \<or> (\<exists>!t. \<tau> A s e = {t}))\<close>
  by (simp add: finite_trans_conj_card_trans_le1_is[symmetric]) *)


(*when this hypothesis is not verified, the product of two deterministic automata can become non deterministic*)
definition indep_enabl :: \<open>('\<sigma>\<^sub>0, 'a, 'r\<^sub>0, '\<alpha>) A\<^sub>d_scheme \<Rightarrow> '\<sigma>\<^sub>0 \<Rightarrow> 'a set \<Rightarrow> ('\<sigma>\<^sub>1, 'a, 'r\<^sub>1, '\<beta>) A\<^sub>d_scheme \<Rightarrow> '\<sigma>\<^sub>1 \<Rightarrow> bool\<close>
  where \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>\<^sub>1 \<equiv> \<forall>t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 \<sigma>\<^sub>0. \<forall>t\<^sub>1 \<in> \<R>\<^sub>d A\<^sub>1 \<sigma>\<^sub>1. \<epsilon> A\<^sub>0 t\<^sub>0 \<inter> \<epsilon> A\<^sub>1 t\<^sub>1 \<subseteq> E\<close>

lemma indep_enablI :
  \<open>(\<And>t\<^sub>0 t\<^sub>1. t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 \<sigma>\<^sub>0 \<Longrightarrow> t\<^sub>1 \<in> \<R>\<^sub>d A\<^sub>1 \<sigma>\<^sub>1 \<Longrightarrow> \<epsilon> A\<^sub>0 t\<^sub>0 \<inter> \<epsilon> A\<^sub>1 t\<^sub>1 \<subseteq> E)
   \<Longrightarrow> indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>\<^sub>1\<close>
  and indep_enablD :
  \<open>\<lbrakk>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>\<^sub>1; t\<^sub>0 \<in> \<R>\<^sub>d A\<^sub>0 \<sigma>\<^sub>0; t\<^sub>1 \<in> \<R>\<^sub>d A\<^sub>1 \<sigma>\<^sub>1\<rbrakk> \<Longrightarrow> \<epsilon> A\<^sub>0 t\<^sub>0 \<inter> \<epsilon> A\<^sub>1 t\<^sub>1 \<subseteq> E\<close>
  by (simp_all add: indep_enabl_def)


definition \<rho>_disjoint_\<epsilon> :: \<open>('\<sigma>, 'a, '\<sigma>', 'r', '\<alpha>) A_scheme \<Rightarrow> bool\<close>
  where \<open>\<rho>_disjoint_\<epsilon> A \<equiv> \<forall>\<sigma> \<in> \<rho> A. \<epsilon> A \<sigma> = {}\<close>

lemma \<rho>_disjoint_\<epsilon>I : \<open>(\<And>\<sigma>. \<sigma> \<in> \<rho> A \<Longrightarrow> \<epsilon> A \<sigma> = {}) \<Longrightarrow> \<rho>_disjoint_\<epsilon> A\<close>
  and \<rho>_disjoint_\<epsilon>D : \<open>\<rho>_disjoint_\<epsilon> A \<Longrightarrow> \<sigma> \<in> \<rho> A \<Longrightarrow> \<epsilon> A \<sigma> = {}\<close>
  by (simp_all add: \<rho>_disjoint_\<epsilon>_def)



definition at_most_1_elem_term :: \<open>('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme \<Rightarrow> bool\<close>
  where \<open>at_most_1_elem_term A \<equiv> \<forall>\<sigma>. \<omega> A \<sigma> = {} \<or> (\<exists>r. \<omega> A \<sigma> = {r})\<close>

lemma at_most_1_elem_term_def_bis :
  \<open>at_most_1_elem_term A \<longleftrightarrow> (\<forall>\<sigma>. \<exists>r. \<omega> A \<sigma> \<subseteq> {r})\<close>
  by (auto simp add: at_most_1_elem_term_def subset_iff)
    (metis empty_iff singleton_iff,
      metis equals0D is_singletonI' is_singleton_some_elem)

lemma at_most_1_elem_termI :
  \<open>\<lbrakk>\<And>\<sigma>. \<omega> A \<sigma> = {} \<or> (\<exists>r. \<omega> A \<sigma> = {r})\<rbrakk> \<Longrightarrow> at_most_1_elem_term A\<close>
  by (simp add: at_most_1_elem_term_def)

lemma at_most_1_elem_termE :
  \<open>\<lbrakk>\<omega> A \<sigma> = {} \<Longrightarrow> thesis; \<And>r. \<omega> A \<sigma> = {r} \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis\<close>
  if \<open>at_most_1_elem_term A\<close>
  by (meson at_most_1_elem_term_def \<open>at_most_1_elem_term A\<close>)+

lemma at_most_1_elem_imp_at_most_1_elem_term :
  \<open>at_most_1_elem A \<Longrightarrow> at_most_1_elem_term A\<close>
  by (simp add: at_most_1_elem_def at_most_1_elem_term_def)




section \<open>First Properties\<close>

subsection \<open>\<^const>\<open>\<epsilon>\<close>, \<^const>\<open>\<rho>\<close> and \<^const>\<open>\<omega>\<close> first equalities\<close>

lemma base_trans_\<epsilon>[simp]:
  \<open>\<epsilon> (\<lparr>\<tau> = \<lambda>\<sigma> a. \<diamond>, \<omega> = \<lambda>\<sigma>. \<diamond>, \<dots> = some\<rparr> :: ('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>d_scheme) \<sigma> = {}\<close>
  \<open>\<epsilon> (\<lparr>\<tau> = \<lambda>\<sigma> a. {}, \<omega> = \<lambda>\<sigma>. {}, \<dots> = some\<rparr> :: ('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme) \<sigma> = {}\<close>
  by (simp_all add: \<epsilon>_simps)

lemma base_trans_\<rho>[simp]:
  \<open>\<rho> (\<lparr>\<tau> = \<lambda>\<sigma> a. \<diamond>, \<omega> = \<lambda>\<sigma>. \<diamond>, \<dots> = some\<rparr> :: ('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>d_scheme) = {}\<close>
  \<open>\<rho> (\<lparr>\<tau> = \<lambda>\<sigma> a. {}, \<omega> = \<lambda>\<sigma>. {}, \<dots> = some\<rparr> :: ('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme) = {}\<close>
  by (simp_all add: \<rho>_simps)


lemma \<sigma>_\<sigma>s_conv_\<epsilon>[simp]:
  \<open>\<epsilon> \<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s \<sigma>s = \<epsilon> A (hd \<sigma>s)\<close> \<open>\<epsilon> \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s \<sigma>s = \<epsilon> B (hd \<sigma>s)\<close>
  \<open>\<epsilon> \<^sub>d\<llangle>C\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma> \<sigma> = \<epsilon> C [\<sigma>]\<close> \<open>\<epsilon> \<^sub>n\<^sub>d\<llangle>D\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma> \<sigma> = \<epsilon> D [\<sigma>]\<close>
  by (simp_all add: \<sigma>_\<sigma>s_conv_defs \<epsilon>_simps option.case_eq_if)

lemma \<sigma>_\<sigma>s_conv_\<rho>[simp]:
  \<open>\<rho> \<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s = {\<sigma>s. hd \<sigma>s \<in> \<rho> A}\<close> \<open>\<rho> \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s = {\<sigma>s. hd \<sigma>s \<in> \<rho> B}\<close>
  \<open>\<rho> \<^sub>d\<llangle>C\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma> = {\<sigma>. [\<sigma>] \<in> \<rho> C}\<close> \<open>\<rho> \<^sub>n\<^sub>d\<llangle>D\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma> = {\<sigma>. [\<sigma>] \<in> \<rho> D}\<close>
  by (simp_all add: \<sigma>_\<sigma>s_conv_defs \<rho>_simps option.case_eq_if)


lemma singl_list_conv_\<epsilon>[simp]:
  \<open>\<epsilon> \<^sub>d\<llangle>A\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma>s = \<epsilon> A (hd \<sigma>s)\<close> \<open>\<epsilon> \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma>s = \<epsilon> B (hd \<sigma>s)\<close>
  \<open>\<epsilon> \<^sub>d\<llangle>C\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l \<sigma> = \<epsilon> C [\<sigma>]\<close> \<open>\<epsilon> \<^sub>n\<^sub>d\<llangle>D\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l \<sigma> = \<epsilon> D [\<sigma>]\<close>
  by (simp_all add: singl_list_conv_defs \<epsilon>_simps option.case_eq_if)

lemma singl_list_conv_\<rho>[simp]:
  \<open>\<rho> \<^sub>d\<llangle>A\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t = {\<sigma>s. hd \<sigma>s \<in> \<rho> A}\<close> \<open>\<rho> \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t = {\<sigma>s. hd \<sigma>s \<in> \<rho> B}\<close>
  \<open>\<rho> \<^sub>d\<llangle>C\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l = {\<sigma>. [\<sigma>] \<in> \<rho> C}\<close> \<open>\<rho> \<^sub>n\<^sub>d\<llangle>D\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l = {\<sigma>. [\<sigma>] \<in> \<rho> D}\<close>
  by (simp_all add: singl_list_conv_defs \<rho>_simps option.case_eq_if)


lemma det_ndet_conv_\<epsilon>[simp]: \<open>\<epsilon> \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d = \<epsilon> A\<close> \<open>\<epsilon> \<llangle>B\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d = \<epsilon> B\<close>
  by (rule ext, simp add: det_ndet_conv_defs \<epsilon>_simps option.case_eq_if)+

lemma det_ndet_conv_\<rho>[simp]: \<open>\<rho> \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d = \<rho> A\<close> \<open>\<rho> \<llangle>B\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d = \<rho> B\<close>
  by (simp_all add: det_ndet_conv_defs \<rho>_simps option.case_eq_if)

lemma \<omega>_from_det_to_ndet :
  \<open>\<omega> \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d = (\<lambda>\<sigma>. case \<omega> A \<sigma> of \<lfloor>r\<rfloor> \<Rightarrow> {r} | \<diamond> \<Rightarrow> {})\<close>
  by (auto simp add: det_ndet_conv_defs)


lemma \<epsilon>_\<omega>_useless [simp] :
  \<open>\<epsilon> (A\<lparr>\<omega> := some_\<omega>\<rparr>) = \<epsilon> A\<close> \<open>\<epsilon> (B\<lparr>\<omega> := some_\<omega>'\<rparr>) = \<epsilon> B\<close>
  for A :: \<open>('\<sigma>, 'a, '\<sigma> option, 'r option, '\<alpha>) A_scheme\<close>
    and B :: \<open>('\<sigma>, 'a, '\<sigma> set, 'r set, '\<alpha>) A_scheme\<close>
  by (rule ext, simp add: \<epsilon>_simps)+

lemma \<rho>_disjoint_\<epsilon>_updated_\<omega> [simp] :
  \<open>\<rho>_disjoint_\<epsilon> (A\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>)\<close>
  \<open>\<rho>_disjoint_\<epsilon> (B\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>)\<close>
  by (simp_all add: \<rho>_disjoint_\<epsilon>_def \<rho>_simps)

lemma \<rho>_disjoint_\<epsilon>_det_ndet_conv_iff [simp] :
  \<open>\<rho>_disjoint_\<epsilon> \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<longleftrightarrow> \<rho>_disjoint_\<epsilon> A\<close>
  \<open>\<rho>_disjoint_\<epsilon> \<llangle>B\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d \<longleftrightarrow> \<rho>_disjoint_\<epsilon> B\<close>
  by (simp_all add: \<rho>_disjoint_\<epsilon>_def)

lemma at_most_1_elem_term_updated_\<omega> [simp] :
  \<open>at_most_1_elem_term (A\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>)\<close>
  by (simp add: at_most_1_elem_term_def)

lemma at_most_1_elem_term_from_det_to_ndet [simp] :
  \<open>at_most_1_elem_term \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<close>
  by (simp add: det_ndet_conv_defs at_most_1_elem_term_def split: option.split)

lemma at_most_1_elem_term_unit [simp] :
  \<open>at_most_1_elem_term (A :: ('\<sigma>, 'a, unit, '\<alpha>) A\<^sub>n\<^sub>d_scheme)\<close>
  by (auto simp add: at_most_1_elem_term_def)



subsection \<open>Properties of our morphisms\<close>

method expand_A_scheme =
  match conclusion in \<open>A = B\<close> for A B :: \<open>('\<sigma>, 'a, '\<sigma>', 'r', '\<alpha>) A_scheme\<close> \<Rightarrow>
  \<open>cases A, cases B\<close>


lemma base_trans_det_ndet_conv:
  \<open>\<llangle>\<lparr>\<tau> = \<lambda>\<sigma> a. \<diamond>, \<omega> = \<lambda>\<sigma>. \<diamond>, \<dots> = some\<rparr>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d =
    \<lparr>\<tau> = \<lambda>\<sigma> a. {}, \<omega> = \<lambda>\<sigma>. {}, \<dots> = some\<rparr>\<close>
  \<open>\<llangle>\<lparr>\<tau> = \<lambda>\<sigma> a. {}, \<omega> = \<lambda>\<sigma>. {}, \<dots> = some\<rparr>\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d =
   \<lparr>\<tau> = \<lambda>\<sigma> a. \<diamond>, \<omega> = \<lambda>\<sigma>. \<diamond>, \<dots> = some\<rparr>\<close>
  unfolding det_ndet_conv_defs by simp_all


lemma from_det_to_ndet_\<sigma>_\<sigma>s_conv_commute:
  \<open>\<^sub>n\<^sub>d\<llangle>\<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s = \<llangle>\<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<close> \<open>\<^sub>n\<^sub>d\<llangle>\<llangle>B\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma> = \<llangle>\<^sub>d\<llangle>B\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<close>
  by (simp add: det_ndet_conv_defs \<sigma>_\<sigma>s_conv_defs, rule ext,
      auto simp add: option.case_eq_if split: if_splits)+

lemma from_det_to_ndet_singl_list_conv_commute:
  \<open>\<^sub>n\<^sub>d\<llangle>\<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t = \<llangle>\<^sub>d\<llangle>A\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<close> \<open>\<^sub>n\<^sub>d\<llangle>\<llangle>B\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l = \<llangle>\<^sub>d\<llangle>B\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<close>
  by (simp add: det_ndet_conv_defs singl_list_conv_defs,
      solves \<open>intro conjI ext, auto split: option.split\<close>)+


lemma from_ndet_to_det_\<sigma>_\<sigma>s_conv_commute:
  \<open>at_most_1_elem_trans A \<Longrightarrow> \<^sub>d\<llangle>\<llangle>A\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s = \<llangle>\<^sub>n\<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<close>
  \<open>at_most_1_elem_trans B \<Longrightarrow> \<^sub>d\<llangle>\<llangle>B\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma> = \<llangle>\<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma>\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<close>
proof -
  assume * : \<open>at_most_1_elem_trans A\<close>
  from "*" have \<open>\<tau> \<^sub>d\<llangle>\<llangle>A\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s \<sigma>s a = \<tau> \<llangle>\<^sub>n\<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d \<sigma>s a\<close> for \<sigma>s a
    by (auto simp add: det_ndet_conv_defs \<sigma>_\<sigma>s_conv_defs
        elim: at_most_1_elem_transE)
  moreover have \<open>\<omega> \<^sub>d\<llangle>\<llangle>A\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s \<sigma>s = \<omega> \<llangle>\<^sub>n\<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d \<sigma>s\<close> for \<sigma>s
    by (auto simp add: det_ndet_conv_defs \<sigma>_\<sigma>s_conv_defs)
  moreover have \<open>more \<^sub>d\<llangle>\<llangle>A\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s = more \<llangle>\<^sub>n\<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<close> by simp
  ultimately show \<open>\<^sub>d\<llangle>\<llangle>A\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s = \<llangle>\<^sub>n\<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<close> by expand_A_scheme auto
next
  assume * : \<open>at_most_1_elem_trans B\<close>
  from "*" have \<open>\<tau> \<^sub>d\<llangle>\<llangle>B\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma> \<sigma> a = \<tau> \<llangle>\<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma>\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d \<sigma> a\<close> for \<sigma> a
    by (auto simp add: det_ndet_conv_defs \<sigma>_\<sigma>s_conv_defs
        elim: at_most_1_elem_transE)
  moreover have \<open>\<omega> \<^sub>d\<llangle>\<llangle>B\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma> \<sigma> = \<omega> \<llangle>\<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma>\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d \<sigma>\<close> for \<sigma>
    by (auto simp add: det_ndet_conv_defs \<sigma>_\<sigma>s_conv_defs)
  moreover have \<open>more \<^sub>d\<llangle>\<llangle>B\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma> = more \<llangle>\<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma>\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<close> by simp
  ultimately show \<open>\<^sub>d\<llangle>\<llangle>B\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma> = \<llangle>\<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma>\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<close> by expand_A_scheme auto
qed

lemma from_ndet_to_det_singl_list_conv_commute:
  \<open>at_most_1_elem A \<Longrightarrow> \<^sub>d\<llangle>\<llangle>A\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t = \<llangle>\<^sub>n\<^sub>d\<llangle>A\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<close>
  \<open>at_most_1_elem B \<Longrightarrow> \<^sub>d\<llangle>\<llangle>B\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l = \<llangle>\<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<close>
proof -
  assume * : \<open>at_most_1_elem A\<close>
  from "*" have \<open>\<tau> \<^sub>d\<llangle>\<llangle>A\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma>s a = \<tau> \<llangle>\<^sub>n\<^sub>d\<llangle>A\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d \<sigma>s a\<close> for \<sigma>s a
    by (auto simp add: det_ndet_conv_defs singl_list_conv_defs
        elim: at_most_1_elemE(1))
  moreover from "*" have \<open>\<omega> \<^sub>d\<llangle>\<llangle>A\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma>s = \<omega> \<llangle>\<^sub>n\<^sub>d\<llangle>A\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d \<sigma>s\<close> for \<sigma>s
    by (auto simp add: det_ndet_conv_defs singl_list_conv_defs
        elim: at_most_1_elemE(2))
  moreover have \<open>more \<^sub>d\<llangle>\<llangle>A\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t = more \<llangle>\<^sub>n\<^sub>d\<llangle>A\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<close> by simp
  ultimately show \<open>\<^sub>d\<llangle>\<llangle>A\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t = \<llangle>\<^sub>n\<^sub>d\<llangle>A\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<close> by expand_A_scheme auto
next
  assume * : \<open>at_most_1_elem B\<close>
  from "*" have \<open>\<tau> \<^sub>d\<llangle>\<llangle>B\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l \<sigma> a = \<tau> \<llangle>\<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d \<sigma> a\<close> for \<sigma> a
    by (auto simp add: det_ndet_conv_defs singl_list_conv_defs
        elim: at_most_1_elemE(1))
  moreover from "*" have \<open>\<omega> \<^sub>d\<llangle>\<llangle>B\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l \<sigma> = \<omega> \<llangle>\<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d \<sigma>\<close> for \<sigma>
    by (auto simp add: det_ndet_conv_defs singl_list_conv_defs
        elim: at_most_1_elemE(2))
  moreover have \<open>more \<^sub>d\<llangle>\<llangle>B\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l = more \<llangle>\<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<close> by simp
  ultimately show \<open>\<^sub>d\<llangle>\<llangle>B\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l = \<llangle>\<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<close> by expand_A_scheme auto
qed



lemma behaviour_\<sigma>_\<sigma>s_conv:
  \<open>\<epsilon> \<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s [\<sigma>] = \<epsilon> A \<sigma>\<close>
  \<open>\<tau> \<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s [\<sigma>] a = (case \<tau> A \<sigma> a of \<diamond> \<Rightarrow> \<diamond> | \<lfloor>t\<rfloor> \<Rightarrow> \<lfloor>[t]\<rfloor>)\<close>
  \<open>\<rho> \<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s = {\<sigma>s. hd \<sigma>s \<in> \<rho> A}\<close>
  \<open>\<omega> \<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s [\<sigma>] = \<omega> A \<sigma>\<close>
  \<open>\<epsilon> \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s [\<sigma>] = \<epsilon> B \<sigma>\<close>
  \<open>\<tau> \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s [\<sigma>] a = {[\<sigma>'] |\<sigma>'. \<sigma>' \<in> \<tau> B \<sigma> a}\<close>
  \<open>\<rho> \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s = {\<sigma>s. hd \<sigma>s \<in> \<rho> B}\<close>
  \<open>\<omega> \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s [\<sigma>] = \<omega> B \<sigma>\<close>
  \<open>\<epsilon> \<^sub>d\<llangle>C\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma> \<sigma> = \<epsilon> C [\<sigma>]\<close>
  \<open>\<tau> \<^sub>d\<llangle>C\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma> \<sigma> a = (case \<tau> C [\<sigma>] a of \<diamond> \<Rightarrow> \<diamond> | \<lfloor>\<sigma>s'\<rfloor> \<Rightarrow> \<lfloor>hd \<sigma>s'\<rfloor>)\<close>
  \<open>\<rho> \<^sub>d\<llangle>C\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma> = {\<sigma>. [\<sigma>] \<in> \<rho> C}\<close>
  \<open>\<omega> \<^sub>d\<llangle>C\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma> \<sigma> = \<omega> C [\<sigma>]\<close>
  \<open>\<epsilon> \<^sub>n\<^sub>d\<llangle>D\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma> \<sigma> = \<epsilon> D [\<sigma>]\<close>
  \<open>\<tau> \<^sub>n\<^sub>d\<llangle>D\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma> \<sigma> a = {hd \<sigma>s'| \<sigma>s'. \<sigma>s' \<in> \<tau> D [\<sigma>] a}\<close>
  \<open>\<rho> \<^sub>n\<^sub>d\<llangle>D\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma> = {\<sigma>. [\<sigma>] \<in> \<rho> D}\<close> \<open>\<omega> \<^sub>n\<^sub>d\<llangle>D\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma> \<sigma> = \<omega> D [\<sigma>]\<close>
  by simp_all (simp_all add: \<sigma>_\<sigma>s_conv_defs)


lemma behaviour_singl_list_conv:
  \<open>\<epsilon> \<^sub>d\<llangle>A\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t [\<sigma>] = \<epsilon> A \<sigma>\<close>
  \<open>\<tau> \<^sub>d\<llangle>A\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t [\<sigma>] a = (case \<tau> A \<sigma> a of \<diamond> \<Rightarrow> \<diamond> | \<lfloor>t\<rfloor> \<Rightarrow> \<lfloor>[t]\<rfloor>)\<close>
  \<open>\<rho> \<^sub>d\<llangle>A\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t = {\<sigma>s. hd \<sigma>s \<in> \<rho> A}\<close>
  \<open>\<omega> \<^sub>d\<llangle>A\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t [\<sigma>] = (case \<omega> A \<sigma> of \<diamond> \<Rightarrow> \<diamond> | \<lfloor>r\<rfloor> \<Rightarrow> \<lfloor>[r]\<rfloor>)\<close>
  \<open>\<epsilon> \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t [\<sigma>] = \<epsilon> B \<sigma>\<close>
  \<open>\<tau> \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t [\<sigma>] a = {[\<sigma>'] |\<sigma>'. \<sigma>' \<in> \<tau> B \<sigma> a}\<close>
  \<open>\<rho> \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t = {\<sigma>s. hd \<sigma>s \<in> \<rho> B}\<close>
  \<open>\<omega> \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t [\<sigma>] = {[r] |r. r \<in> \<omega> B \<sigma>}\<close>
  \<open>\<epsilon> \<^sub>d\<llangle>C\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l \<sigma> = \<epsilon> C [\<sigma>]\<close>
  \<open>\<tau> \<^sub>d\<llangle>C\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l \<sigma> a = (case \<tau> C [\<sigma>] a of \<diamond> \<Rightarrow> \<diamond> | \<lfloor>\<sigma>s'\<rfloor> \<Rightarrow> \<lfloor>hd \<sigma>s'\<rfloor>)\<close>
  \<open>\<rho> \<^sub>d\<llangle>C\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l = {\<sigma>. [\<sigma>] \<in> \<rho> C}\<close>
  \<open>\<omega> \<^sub>d\<llangle>C\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l \<sigma> = (case \<omega> C [\<sigma>] of \<diamond> \<Rightarrow> \<diamond> | \<lfloor>rs\<rfloor> \<Rightarrow> \<lfloor>hd rs\<rfloor>)\<close>
  \<open>\<epsilon> \<^sub>n\<^sub>d\<llangle>D\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l \<sigma> = \<epsilon> D [\<sigma>]\<close>
  \<open>\<tau> \<^sub>n\<^sub>d\<llangle>D\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l \<sigma> a = {hd \<sigma>s'| \<sigma>s'. \<sigma>s' \<in> \<tau> D [\<sigma>] a}\<close>
  \<open>\<rho> \<^sub>n\<^sub>d\<llangle>D\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l = {\<sigma>. [\<sigma>] \<in> \<rho> D}\<close>
  \<open>\<omega> \<^sub>n\<^sub>d\<llangle>D\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l \<sigma> = {hd rs |rs. rs \<in> \<omega> D [\<sigma>]}\<close>
  by simp_all (simp_all add: singl_list_conv_defs)


lemma empty_from_det_to_ndet_is_None_trans [simp] : \<open>\<tau> \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma> a = {} \<longleftrightarrow> \<tau> A \<sigma> a = \<diamond>\<close>
  by (simp add: \<epsilon>_simps det_ndet_conv_defs option.case_eq_if)


lemma at_most_1_elem_from_det_to_ndet [simp] : \<open>at_most_1_elem \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<close>
  by (rule at_most_1_elemI)
    (simp_all add: det_ndet_conv_defs split: option.split)


lemma from_ndet_to_det_from_det_to_ndet [simp] : \<open>\<llangle>\<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d = A\<close>
  by (cases A, simp add: det_ndet_conv_defs)
    (intro conjI ext, simp_all split: option.split)

lemma from_det_to_ndet_from_ndet_to_det [simp] :
  \<open>\<llangle>\<llangle>A\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d = A\<close> if \<open>at_most_1_elem A\<close>
proof -
  from that have \<open>\<tau> \<llangle>\<llangle>A\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma> a = \<tau> A \<sigma> a\<close> for \<sigma> a
    by (auto simp add: det_ndet_conv_defs elim: at_most_1_elemE(1))
  moreover from that have \<open>\<omega> \<llangle>\<llangle>A\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma> = \<omega> A \<sigma>\<close> for \<sigma>
    by (auto simp add: det_ndet_conv_defs elim: at_most_1_elemE(2))
  moreover have \<open>more \<llangle>\<llangle>A\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d = more A\<close> by simp
  ultimately show \<open>\<llangle>\<llangle>A\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d = A\<close> by expand_A_scheme fastforce
qed


theorem bij_betw_from_det_to_ndet :
  \<open>bij_betw (\<lambda>A. \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) UNIV {A. at_most_1_elem A}\<close>
  unfolding bij_betw_iff_bijections
  by (rule exI[where x = \<open>\<lambda>A. \<llangle>A\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d\<close>]) simp

lemma bij_betw_from_ndet_to_det :
  \<open>bij_betw (\<lambda>A. \<llangle>A\<rrangle>\<^sub>n\<^sub>d\<^sub>\<leadsto>\<^sub>d) {A. at_most_1_elem A} UNIV\<close>
  unfolding bij_betw_iff_bijections
  by (rule exI[where x = \<open>\<lambda>A. \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<close>]) simp


lemma length_1_trans_from_\<sigma>_to_\<sigma>s [simp] :
  \<open>length_1_trans\<^sub>d \<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<close> \<open>length_1_trans\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<close>
  by (rule length_1_trans\<^sub>dI, solves \<open>auto simp add: \<sigma>_\<sigma>s_conv_defs split: option.split_asm\<close>)
    (rule length_1_trans\<^sub>n\<^sub>dI, solves \<open>auto simp add: \<sigma>_\<sigma>s_conv_defs split: option.split_asm\<close>)

lemma \<tau>_hd_from_\<sigma>_to_\<sigma>s_eq [simp] :
  \<open>\<tau> \<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s [hd \<sigma>s] a = \<tau> \<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s \<sigma>s a\<close>
  \<open>\<tau> \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s [hd \<sigma>s] a = \<tau> \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s \<sigma>s a\<close>
  by (simp_all add: \<sigma>_\<sigma>s_conv_defs)

lemma \<omega>_hd_from_\<sigma>_to_\<sigma>s_eq [simp] :
  \<open>\<omega> \<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s [hd \<sigma>s] = \<omega> \<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s \<sigma>s\<close>
  \<open>\<omega> \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s [hd \<sigma>s] = \<omega> \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s \<sigma>s\<close>
  by (simp_all add: \<sigma>_\<sigma>s_conv_defs)


lemma from_\<sigma>s_to_\<sigma>_from_\<sigma>_to_\<sigma>s [simp] :
  \<open>\<^sub>d\<llangle>\<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma> = A\<close> \<open>\<^sub>n\<^sub>d\<llangle>\<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma> = B\<close>
  by (cases A, simp add: \<sigma>_\<sigma>s_conv_defs, intro conjI ext;
      simp add: option.case_eq_if set_eq_iff; metis list.sel(1))
    (cases B, simp add: \<sigma>_\<sigma>s_conv_defs, intro conjI ext;
      simp add: option.case_eq_if set_eq_iff; metis list.sel(1))

lemma from_\<sigma>_to_\<sigma>s_from_\<sigma>s_to_\<sigma> [simp] :
  \<open>\<lbrakk>length_1_trans\<^sub>d A; \<And>\<sigma>s a. \<tau> A [hd \<sigma>s] a = \<tau> A \<sigma>s a;
    \<And>\<sigma>s. \<omega> A [hd \<sigma>s] = \<omega> A \<sigma>s\<rbrakk> \<Longrightarrow> \<^sub>d\<llangle>\<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma>\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s = A\<close>
  \<open>\<lbrakk>length_1_trans\<^sub>n\<^sub>d B; \<And>\<sigma>s a. \<tau> B [hd \<sigma>s] a = \<tau> B \<sigma>s a;
    \<And>\<sigma>s. \<omega> B [hd \<sigma>s] = \<omega> B \<sigma>s\<rbrakk> \<Longrightarrow> \<^sub>n\<^sub>d\<llangle>\<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma>\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s = B\<close>
proof -
  assume * : \<open>length_1_trans\<^sub>d A\<close> \<open>\<And>\<sigma>s a. \<tau> A [hd \<sigma>s] a = \<tau> A \<sigma>s a\<close>
    \<open>\<And>\<sigma>s. \<omega> A [hd \<sigma>s] = \<omega> A \<sigma>s\<close>
  from "*"(1) have \<open>\<tau> \<^sub>d\<llangle>\<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma>\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s \<sigma>s a = \<tau> A \<sigma>s a\<close> for \<sigma>s a
    by (auto simp add: \<sigma>_\<sigma>s_conv_defs "*"(2) split: option.split
        elim: length_1_trans\<^sub>dE)
  moreover have \<open>\<omega> \<^sub>d\<llangle>\<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma>\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s \<sigma>s = \<omega> A \<sigma>s\<close> for \<sigma>s
    by (simp add: \<sigma>_\<sigma>s_conv_defs "*"(3))
  moreover have \<open>more \<^sub>d\<llangle>\<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma>\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s = more A\<close> by simp
  ultimately show \<open>\<^sub>d\<llangle>\<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma>\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s = A\<close> by expand_A_scheme auto
next
  assume * : \<open>length_1_trans\<^sub>n\<^sub>d B\<close> \<open>\<And>\<sigma>s a. \<tau> B [hd \<sigma>s] a = \<tau> B \<sigma>s a\<close>
    \<open>\<And>\<sigma>s. \<omega> B [hd \<sigma>s] = \<omega> B \<sigma>s\<close>
  from "*"(1) have \<open>\<tau> \<^sub>n\<^sub>d\<llangle>\<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma>\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s \<sigma>s a = \<tau> B \<sigma>s a\<close> for \<sigma>s a
    by (auto simp add: \<sigma>_\<sigma>s_conv_defs "*"(2) elim: length_1_trans\<^sub>n\<^sub>dE)
      (metis length_1_trans\<^sub>n\<^sub>dE list.sel(1))
  moreover have \<open>\<omega> \<^sub>n\<^sub>d\<llangle>\<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma>\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s \<sigma>s = \<omega> B \<sigma>s\<close> for \<sigma>s
    by (simp add: \<sigma>_\<sigma>s_conv_defs "*"(3))
  moreover have \<open>more \<^sub>n\<^sub>d\<llangle>\<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma>\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s = more B\<close> by simp
  ultimately show \<open>\<^sub>n\<^sub>d\<llangle>\<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma>\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s = B\<close> by expand_A_scheme fastforce
qed

theorem bij_betw_from_\<sigma>_to_\<sigma>s : 
  \<open>bij_betw (\<lambda>A. \<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s) UNIV
   {A. length_1_trans\<^sub>d A \<and> (\<forall>\<sigma>s a. \<tau> A [hd \<sigma>s] a = \<tau> A \<sigma>s a) \<and> (\<forall>\<sigma>s. \<omega> A [hd \<sigma>s] = \<omega> A \<sigma>s)}\<close>
  (is \<open>bij_betw (\<lambda>A. \<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s) UNIV ?S\<^sub>d\<close>)
  \<open>bij_betw (\<lambda>B. \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s) UNIV
   {B. length_1_trans\<^sub>n\<^sub>d B \<and> (\<forall>\<sigma>s a. \<tau> B \<sigma>s a = \<tau> B [hd \<sigma>s] a) \<and> (\<forall>\<sigma>s. \<omega> B [hd \<sigma>s] = \<omega> B \<sigma>s)}\<close>
  unfolding bij_betw_iff_bijections
  by (rule exI[where x = \<open>\<lambda>A. \<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma>\<close>], simp)
    (rule exI[where x = \<open>\<lambda>A. \<^sub>n\<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma>\<close>], simp)


lemma bij_betw_from_\<sigma>s_to_\<sigma> : 
  \<open>bij_betw (\<lambda>A. \<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma>)
   {A. length_1_trans\<^sub>d A \<and> (\<forall>\<sigma>s a. \<tau> A [hd \<sigma>s] a = \<tau> A \<sigma>s a) \<and> (\<forall>\<sigma>s. \<omega> A [hd \<sigma>s] = \<omega> A \<sigma>s)} UNIV\<close>
  \<open>bij_betw (\<lambda>B. \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>\<sigma>\<^sub>s\<^sub>\<leadsto>\<^sub>\<sigma>)
   {B. length_1_trans\<^sub>n\<^sub>d B \<and> (\<forall>\<sigma>s a. \<tau> B \<sigma>s a = \<tau> B [hd \<sigma>s] a) \<and> (\<forall>\<sigma>s. \<omega> B [hd \<sigma>s] = \<omega> B \<sigma>s)} UNIV\<close>
  unfolding bij_betw_iff_bijections
  by (rule exI[where x = \<open>\<lambda>A. \<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<close>], simp)
    (rule exI[where x = \<open>\<lambda>A. \<^sub>n\<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<close>], simp)



lemma length_1_from_singl_to_list [simp] :
  \<open>length_1\<^sub>d \<^sub>d\<llangle>A\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<close> \<open>length_1\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<close>
  by (rule length_1\<^sub>dI; solves \<open>auto simp add: singl_list_conv_defs split: option.split_asm\<close>)
    (rule length_1\<^sub>n\<^sub>dI; solves \<open>auto simp add: singl_list_conv_defs split: option.split_asm\<close>)

lemma \<tau>_hd_from_singl_to_list_eq [simp] :
  \<open>\<tau> \<^sub>d\<llangle>A\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t [hd \<sigma>s] a = \<tau> \<^sub>d\<llangle>A\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma>s a\<close>
  \<open>\<tau> \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t [hd \<sigma>s] a = \<tau> \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma>s a\<close>
  by (simp_all add: singl_list_conv_defs)

lemma \<omega>_hd_from_singl_to_list_eq [simp] :
  \<open>\<omega> \<^sub>d\<llangle>A\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t [hd \<sigma>s] = \<omega> \<^sub>d\<llangle>A\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma>s\<close>
  \<open>\<omega> \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t [hd \<sigma>s] = \<omega> \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma>s\<close>
  by (simp_all add: singl_list_conv_defs)


lemma from_list_to_singl_from_singl_to_list [simp] :
  \<open>\<^sub>d\<llangle>\<^sub>d\<llangle>A\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l = A\<close> \<open>\<^sub>n\<^sub>d\<llangle>\<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l = B\<close>
  by (cases A, simp add: singl_list_conv_defs, intro conjI ext;
      simp add: option.case_eq_if set_eq_iff; metis list.sel(1))
    (cases B, simp add: singl_list_conv_defs, intro conjI ext;
      simp add: option.case_eq_if set_eq_iff; metis list.sel(1))

lemma from_singl_to_list_from_list_to_singl [simp] :
  \<open>\<lbrakk>length_1\<^sub>d A; \<And>\<sigma>s a. \<tau> A [hd \<sigma>s] a = \<tau> A \<sigma>s a;
    \<And>\<sigma>s. \<omega> A [hd \<sigma>s] = \<omega> A \<sigma>s\<rbrakk> \<Longrightarrow> \<^sub>d\<llangle>\<^sub>d\<llangle>A\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t = A\<close>
  \<open>\<lbrakk>length_1\<^sub>n\<^sub>d B; \<And>\<sigma>s a. \<tau> B [hd \<sigma>s] a = \<tau> B \<sigma>s a;
    \<And>\<sigma>s. \<omega> B [hd \<sigma>s] = \<omega> B \<sigma>s\<rbrakk> \<Longrightarrow> \<^sub>n\<^sub>d\<llangle>\<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t = B\<close>
proof -
  assume * : \<open>length_1\<^sub>d A\<close> \<open>\<And>\<sigma>s a. \<tau> A [hd \<sigma>s] a = \<tau> A \<sigma>s a\<close>
    \<open>\<And>\<sigma>s. \<omega> A [hd \<sigma>s] = \<omega> A \<sigma>s\<close>
  from "*"(1) have \<open>\<tau> \<^sub>d\<llangle>\<^sub>d\<llangle>A\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma>s a = \<tau> A \<sigma>s a\<close> for \<sigma>s a
    by (auto simp add: singl_list_conv_defs "*"(2)
        split: option.split elim: length_1\<^sub>dE(1))
  moreover from "*"(1) have \<open>\<omega> \<^sub>d\<llangle>\<^sub>d\<llangle>A\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma>s = \<omega> A \<sigma>s\<close> for \<sigma>s
    by (auto simp add: singl_list_conv_defs "*"(3)
        split: option.split elim: length_1\<^sub>dE(2))
  moreover have \<open>more \<^sub>d\<llangle>\<^sub>d\<llangle>A\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t = more A\<close> by simp
  ultimately show \<open>\<^sub>d\<llangle>\<^sub>d\<llangle>A\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t = A\<close> by expand_A_scheme auto
next
  assume * : \<open>length_1\<^sub>n\<^sub>d B\<close> \<open>\<And>\<sigma>s a. \<tau> B [hd \<sigma>s] a = \<tau> B \<sigma>s a\<close>
    \<open>\<And>\<sigma>s. \<omega> B [hd \<sigma>s] = \<omega> B \<sigma>s\<close>
  from "*"(1) have \<open>\<tau> \<^sub>n\<^sub>d\<llangle>\<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma>s a = \<tau> B \<sigma>s a\<close> for \<sigma>s a
    by (auto simp add: singl_list_conv_defs "*"(2) elim: length_1\<^sub>n\<^sub>dE(1))
      (metis length_1\<^sub>n\<^sub>dE(1) list.sel(1))
  moreover from "*"(1) have \<open>\<omega> \<^sub>n\<^sub>d\<llangle>\<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma>s = \<omega> B \<sigma>s\<close> for \<sigma>s
    by (auto simp add: singl_list_conv_defs "*"(3) elim: length_1\<^sub>n\<^sub>dE(2))
      (metis length_1\<^sub>n\<^sub>dE(2) list.sel(1))
  moreover have \<open>more \<^sub>n\<^sub>d\<llangle>\<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t = more B\<close> by simp
  ultimately show \<open>\<^sub>n\<^sub>d\<llangle>\<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t = B\<close> by expand_A_scheme fastforce
qed


theorem bij_betw_from_singl_to_list : 
  \<open>bij_betw (\<lambda>A. \<^sub>d\<llangle>A\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t) UNIV
   {A. length_1\<^sub>d A \<and> (\<forall>\<sigma>s a. \<tau> A [hd \<sigma>s] a = \<tau> A \<sigma>s a) \<and> (\<forall>\<sigma>s. \<omega> A [hd \<sigma>s] = \<omega> A \<sigma>s)}\<close>
  (is \<open>bij_betw (\<lambda>A. \<^sub>d\<llangle>A\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t) UNIV ?S\<^sub>d\<close>)
  \<open>bij_betw (\<lambda>B. \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t) UNIV
   {B. length_1\<^sub>n\<^sub>d B \<and> (\<forall>\<sigma>s a. \<tau> B \<sigma>s a = \<tau> B [hd \<sigma>s] a) \<and> (\<forall>\<sigma>s. \<omega> B [hd \<sigma>s] = \<omega> B \<sigma>s)}\<close>
  unfolding bij_betw_iff_bijections
  by (rule exI[where x = \<open>\<lambda>A. \<^sub>d\<llangle>A\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<close>], simp)
    (rule exI[where x = \<open>\<lambda>A. \<^sub>n\<^sub>d\<llangle>A\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<close>], simp)

lemma bij_betw_from_list_to_singl : 
  \<open>bij_betw (\<lambda>A. \<^sub>d\<llangle>A\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l)
   {A. length_1\<^sub>d A \<and> (\<forall>\<sigma>s a. \<tau> A [hd \<sigma>s] a = \<tau> A \<sigma>s a) \<and> (\<forall>\<sigma>s. \<omega> A [hd \<sigma>s] = \<omega> A \<sigma>s)} UNIV\<close>
  \<open>bij_betw (\<lambda>B. \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<^sub>\<leadsto>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l)
   {B. length_1\<^sub>n\<^sub>d B \<and> (\<forall>\<sigma>s a. \<tau> B \<sigma>s a = \<tau> B [hd \<sigma>s] a) \<and> (\<forall>\<sigma>s. \<omega> B [hd \<sigma>s] = \<omega> B \<sigma>s)} UNIV\<close>
  unfolding bij_betw_iff_bijections
  by (rule exI[where x = \<open>\<lambda>A. \<^sub>d\<llangle>A\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<close>], simp)
    (rule exI[where x = \<open>\<lambda>A. \<^sub>n\<^sub>d\<llangle>A\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t\<close>], simp)



subsection \<open>Reachability results (for \<^const>\<open>\<R>\<^sub>d\<close> and \<^const>\<open>\<R>\<^sub>n\<^sub>d\<close>)\<close>

lemma \<R>_base_trans[simp]: \<open>\<R>\<^sub>d  \<lparr>\<tau> = \<lambda>\<sigma> a. \<diamond>, \<omega> = \<lambda>\<sigma>. \<diamond>, \<dots> = some\<rparr> = (\<lambda>\<sigma>. {\<sigma>})\<close>
  \<open>\<R>\<^sub>n\<^sub>d \<lparr>\<tau> = \<lambda>\<sigma> a. {}, \<omega> = \<lambda>\<sigma>. {}, \<dots> = some\<rparr> = (\<lambda>\<sigma>. {\<sigma>})\<close>
  by (rule ext, safe, subst (asm) \<R>\<^sub>d.simps \<R>\<^sub>n\<^sub>d.simps, simp_all add: \<R>\<^sub>d.init \<R>\<^sub>n\<^sub>d.init)+


theorem \<R>\<^sub>n\<^sub>d_from_det_to_ndet : \<open>\<R>\<^sub>n\<^sub>d \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma> = \<R>\<^sub>d A \<sigma>\<close>
proof safe
  show \<open>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma> \<Longrightarrow> \<sigma>' \<in> \<R>\<^sub>d A \<sigma>\<close> for \<sigma>'
    by (induct rule: \<R>\<^sub>n\<^sub>d.induct, fact \<R>\<^sub>d.init, erule \<R>\<^sub>d.step)
      (simp add: from_det_to_ndet_def option.case_eq_if split: if_split_asm)
next
  show \<open>\<sigma>' \<in> \<R>\<^sub>d A \<sigma> \<Longrightarrow> \<sigma>' \<in> \<R>\<^sub>n\<^sub>d \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d \<sigma>\<close> for \<sigma>'
    by (induct rule: \<R>\<^sub>d.induct, fact \<R>\<^sub>n\<^sub>d.init)
      (metis \<R>\<^sub>n\<^sub>d.step det_ndet_conv_defs(1) option.case(2) 
        option.set_intros option.simps(15) select_convs(1))
qed


(*TODO: see where this can be useful*)
lemma bij_betw_\<R>\<^sub>n\<^sub>d_if_same_\<tau> : \<open>bij_betw f (\<R>\<^sub>n\<^sub>d B\<^sub>0 \<sigma>\<^sub>0) (\<R>\<^sub>n\<^sub>d B\<^sub>1 (f \<sigma>\<^sub>0))\<close>
  if \<open>inj_on f (\<R>\<^sub>n\<^sub>d B\<^sub>0 \<sigma>\<^sub>0)\<close> and \<open>\<And>\<sigma>\<^sub>0' a. \<sigma>\<^sub>0' \<in> \<R>\<^sub>n\<^sub>d B\<^sub>0 \<sigma>\<^sub>0 \<Longrightarrow> \<tau> B\<^sub>1 (f \<sigma>\<^sub>0') a = f ` \<tau> B\<^sub>0 \<sigma>\<^sub>0' a\<close>
proof (rule bij_betw_imageI, fact that(1), auto simp add: image_def, goal_cases)
  show \<open>s \<in> \<R>\<^sub>n\<^sub>d B\<^sub>0 \<sigma>\<^sub>0 \<Longrightarrow> f s \<in> \<R>\<^sub>n\<^sub>d B\<^sub>1 (f \<sigma>\<^sub>0)\<close> for s
    by (induct rule: \<R>\<^sub>n\<^sub>d.induct, simp add: \<R>\<^sub>n\<^sub>d.init, metis \<R>\<^sub>n\<^sub>d.step that(2) image_eqI)
next
  show \<open>s \<in> \<R>\<^sub>n\<^sub>d B\<^sub>1 (f \<sigma>\<^sub>0) \<Longrightarrow> \<exists>t \<in> \<R>\<^sub>n\<^sub>d B\<^sub>0 \<sigma>\<^sub>0. s = f t\<close> for s
    by (induct rule: \<R>\<^sub>n\<^sub>d.induct, metis \<R>\<^sub>n\<^sub>d.simps, metis (mono_tags, lifting) \<R>\<^sub>n\<^sub>d.step that(2) image_iff)
qed

lemma bij_betw_\<R>\<^sub>d_if_same_\<tau>: \<open>bij_betw f (\<R>\<^sub>d A\<^sub>0 \<sigma>\<^sub>0) (\<R>\<^sub>d A\<^sub>1 (f \<sigma>\<^sub>0))\<close>
  if \<open>inj_on f (\<R>\<^sub>d A\<^sub>0 \<sigma>\<^sub>0)\<close> and \<open>\<And>\<sigma>\<^sub>0' a. \<sigma>\<^sub>0' \<in> \<R>\<^sub>d A\<^sub>0 \<sigma>\<^sub>0 \<Longrightarrow> \<tau> A\<^sub>1 (f \<sigma>\<^sub>0') a = map_option f (\<tau> A\<^sub>0 \<sigma>\<^sub>0' a)\<close>
  by (subst (1 2) \<R>\<^sub>n\<^sub>d_from_det_to_ndet[symmetric], rule bij_betw_\<R>\<^sub>n\<^sub>d_if_same_\<tau>)
    (simp_all add: \<R>\<^sub>n\<^sub>d_from_det_to_ndet that(1),
      simp add: det_ndet_conv_defs that(2) option.case_eq_if map_option_case)

lemmas same_\<tau>_implies_same_\<R>\<^sub>n\<^sub>d = bij_betw_\<R>\<^sub>n\<^sub>d_if_same_\<tau>[where f = id, simplified bij_betw_def, simplified]
  and same_\<tau>_implies_same_\<R>\<^sub>d = bij_betw_\<R>\<^sub>d_if_same_\<tau>[where f = id, simplified bij_betw_def option.map_id, simplified]

corollary \<R>\<^sub>d_\<omega>_useless [simp] : \<open>\<R>\<^sub>d (A\<lparr>\<omega> := some_\<omega>\<rparr>) \<sigma> = \<R>\<^sub>d A \<sigma>\<close>
  by (auto intro!: same_\<tau>_implies_same_\<R>\<^sub>d)

corollary \<R>\<^sub>n\<^sub>d_\<omega>_useless [simp] : \<open>\<R>\<^sub>n\<^sub>d (A\<lparr>\<omega> := some_\<omega>\<rparr>) \<sigma> = \<R>\<^sub>n\<^sub>d A \<sigma>\<close>
  by (auto intro!: same_\<tau>_implies_same_\<R>\<^sub>n\<^sub>d)

corollary indep_enabl_\<omega>_useless [simp] :
  \<open>indep_enabl (A\<^sub>0\<lparr>\<omega> := some_\<omega>\<rparr>) \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>\<^sub>1 \<longleftrightarrow> indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>\<^sub>1\<close>
  \<open>indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E (A\<^sub>1\<lparr>\<omega> := some_\<omega>\<rparr>) \<sigma>\<^sub>1 \<longleftrightarrow> indep_enabl A\<^sub>0 \<sigma>\<^sub>0 E A\<^sub>1 \<sigma>\<^sub>1\<close>
  by (simp_all add: indep_enabl_def)


method \<R>_subset_method uses defs opt induct init simps = 
  induct rule: induct, auto simp add: init defs \<epsilon>_simps split: if_splits,
  (metis (no_types, opaque_lifting) simps)+

method \<R>\<^sub>d_subset_method uses defs opt =
  \<R>_subset_method defs: defs opt: opt induct: \<R>\<^sub>d.induct init: \<R>\<^sub>d.init simps: \<R>\<^sub>d.simps

method \<R>\<^sub>n\<^sub>d_subset_method uses defs opt =
  \<R>_subset_method defs: defs opt: opt induct: \<R>\<^sub>n\<^sub>d.induct init: \<R>\<^sub>n\<^sub>d.init simps: \<R>\<^sub>n\<^sub>d.simps


lemma \<R>\<^sub>n\<^sub>d_from_\<sigma>_to_\<sigma>s_description: \<open>\<R>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s [\<sigma>] = {[\<sigma>']| \<sigma>'. \<sigma>' \<in> \<R>\<^sub>n\<^sub>d B \<sigma>}\<close>
proof safe
  show \<open>\<sigma>s \<in> \<R>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s [\<sigma>] \<Longrightarrow> \<exists>\<sigma>'. \<sigma>s = [\<sigma>'] \<and> \<sigma>' \<in> \<R>\<^sub>n\<^sub>d B \<sigma>\<close> for \<sigma>s
    by (induct rule: \<R>\<^sub>n\<^sub>d.induct, auto simp add: \<R>\<^sub>n\<^sub>d.init behaviour_\<sigma>_\<sigma>s_conv(6), metis \<R>\<^sub>n\<^sub>d.step)
next
  show \<open>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d B \<sigma> \<Longrightarrow> [\<sigma>'] \<in> \<R>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s [\<sigma>]\<close> for \<sigma>'
    by (induct rule: \<R>\<^sub>n\<^sub>d.induct) (simp_all add: \<R>\<^sub>n\<^sub>d.init \<R>\<^sub>n\<^sub>d.step behaviour_\<sigma>_\<sigma>s_conv(6))
qed


lemma \<R>\<^sub>d_from_\<sigma>_to_\<sigma>s_description: \<open>\<R>\<^sub>d \<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s [\<sigma>] = {[\<sigma>']| \<sigma>'. \<sigma>' \<in> \<R>\<^sub>d A \<sigma>}\<close>
  by (simp add: \<R>\<^sub>n\<^sub>d_from_\<sigma>_to_\<sigma>s_description
      flip: \<R>\<^sub>n\<^sub>d_from_det_to_ndet from_det_to_ndet_\<sigma>_\<sigma>s_conv_commute(1))


lemma \<R>\<^sub>n\<^sub>d_from_singl_to_list_description: \<open>\<R>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t [\<sigma>] = {[\<sigma>']| \<sigma>'. \<sigma>' \<in> \<R>\<^sub>n\<^sub>d B \<sigma>}\<close>
proof safe
  show \<open>\<sigma>s \<in> \<R>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t [\<sigma>] \<Longrightarrow> \<exists>\<sigma>'. \<sigma>s = [\<sigma>'] \<and> \<sigma>' \<in> \<R>\<^sub>n\<^sub>d B \<sigma>\<close> for \<sigma>s
    by (induct rule: \<R>\<^sub>n\<^sub>d.induct, auto simp add: \<R>\<^sub>n\<^sub>d.init behaviour_singl_list_conv(6), metis \<R>\<^sub>n\<^sub>d.step)
next
  show \<open>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d B \<sigma> \<Longrightarrow> [\<sigma>'] \<in> \<R>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t [\<sigma>]\<close> for \<sigma>'
    by (induct rule: \<R>\<^sub>n\<^sub>d.induct) (simp_all add: \<R>\<^sub>n\<^sub>d.init \<R>\<^sub>n\<^sub>d.step behaviour_singl_list_conv(6))
qed


lemma \<R>\<^sub>d_from_singl_to_list_description: \<open>\<R>\<^sub>d \<^sub>d\<llangle>A\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t [\<sigma>] = {[\<sigma>']| \<sigma>'. \<sigma>' \<in> \<R>\<^sub>d A \<sigma>}\<close>
  by (simp add: \<R>\<^sub>n\<^sub>d_from_singl_to_list_description
      flip: \<R>\<^sub>n\<^sub>d_from_det_to_ndet from_det_to_ndet_singl_list_conv_commute(1))



lemma length_\<R>\<^sub>d_from_\<sigma>_to_\<sigma>s:
  \<open>\<sigma>s' \<in> \<R>\<^sub>d \<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s \<sigma>s \<Longrightarrow> \<sigma>s' = \<sigma>s \<or> length \<sigma>s' = 1\<close>  
  by (simp add: \<sigma>_\<sigma>s_conv_defs)
    (induct rule: \<R>\<^sub>d.induct, simp_all split: option.split_asm)

lemma length_\<R>\<^sub>n\<^sub>d_from_\<sigma>_to_\<sigma>s:
  \<open>\<sigma>s' \<in> \<R>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s \<sigma>s \<Longrightarrow> \<sigma>s' = \<sigma>s \<or> length \<sigma>s' = 1\<close>
  by (simp add: \<sigma>_\<sigma>s_conv_defs)
    (induct rule: \<R>\<^sub>n\<^sub>d.induct, auto)

lemma length_\<R>\<^sub>d_from_singl_to_list:
  \<open>\<sigma>s' \<in> \<R>\<^sub>d \<^sub>d\<llangle>A\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma>s \<Longrightarrow> \<sigma>s' = \<sigma>s \<or> length \<sigma>s' = 1\<close>
  by (simp add: singl_list_conv_defs)
    (induct rule: \<R>\<^sub>d.induct, simp_all split: option.split_asm)

lemma length_\<R>\<^sub>n\<^sub>d_from_singl_to_list:
  \<open>\<sigma>s' \<in> \<R>\<^sub>n\<^sub>d \<^sub>n\<^sub>d\<llangle>B\<rrangle>\<^sub>s\<^sub>i\<^sub>n\<^sub>g\<^sub>l\<^sub>\<hookrightarrow>\<^sub>l\<^sub>i\<^sub>s\<^sub>t \<sigma>s \<Longrightarrow> \<sigma>s' = \<sigma>s \<or> length \<sigma>s' = 1\<close>
  by (simp add: singl_list_conv_defs)
    (induct rule: \<R>\<^sub>n\<^sub>d.induct, auto)



section \<open>Normalization\<close> 

subsection \<open>Non-deterministic Case\<close>

text \<open>First version, without final state notion\<close>

abbreviation P_nd_step :: \<open>[('\<sigma>, 'a) enabl, ('\<sigma>, 'a) trans\<^sub>n\<^sub>d, '\<sigma> \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, '\<sigma>] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where \<open>P_nd_step \<epsilon>\<^sub>A \<tau>\<^sub>A X \<sigma> \<equiv> \<box> e \<in> \<epsilon>\<^sub>A \<sigma> \<rightarrow> \<sqinter> \<sigma>' \<in> \<tau>\<^sub>A \<sigma> e. X \<sigma>'\<close>

definition P_nd :: \<open>('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme \<Rightarrow> '\<sigma> \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (\<open>P\<llangle>_\<rrangle>\<^sub>n\<^sub>d\<close> 1000)
  where \<open>P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<equiv> \<upsilon> X. P_nd_step (\<epsilon> A) (\<tau> A) X\<close>


lemma P_nd_step_constructive [simp] : \<open>constructive (P_nd_step \<epsilon>\<^sub>A \<tau>\<^sub>A)\<close> by simp

lemma P_nd_step_cont [simp] : \<open>\<forall>\<sigma> a. finite (\<tau>\<^sub>A \<sigma> a) \<Longrightarrow> cont (P_nd_step \<epsilon>\<^sub>A \<tau>\<^sub>A)\<close>
  by (simp add: cont_fun)

lemma P_nd_step_constructive_bis : \<open>constructive (P_nd_step (\<epsilon> A) (\<tau> A))\<close> by simp

lemma P_nd_step_cont_bis [simp] : \<open>finite_trans A \<Longrightarrow> cont (P_nd_step (\<epsilon> A) (\<tau> A))\<close>
  by (simp add: finite_trans_def)

lemma P_nd_rec: \<open>P\<llangle>A\<rrangle>\<^sub>n\<^sub>d = (\<lambda>\<sigma>. P_nd_step (\<epsilon> A) (\<tau> A) P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>)\<close>
  by (unfold P_nd_def, rule ext, subst restriction_fix_eq, simp_all)

lemma P_nd_is_fix : \<open>finite_trans A \<Longrightarrow> P\<llangle>A\<rrangle>\<^sub>n\<^sub>d = (\<mu> X. P_nd_step (\<epsilon> A) (\<tau> A) X)\<close>
  by (simp add: P_nd_def restriction_fix_is_fix)

lemma non_destructive_imp_restriction_cont [simp] :
  \<open>non_destructive f \<Longrightarrow> restriction_cont f\<close>
  by (simp add: non_destructive_on_def)



lemma P_nd_\<omega>_useless: \<open>P\<llangle>A\<rrangle>\<^sub>n\<^sub>d = P\<llangle>A\<lparr>\<omega> := some_\<omega>\<rparr>\<rrangle>\<^sub>n\<^sub>d\<close>
  by (simp add: P_nd_def \<epsilon>_simps)

lemma P_nd_\<omega>_useless_bis : \<open>P\<llangle>A\<rrangle>\<^sub>n\<^sub>d = P\<llangle>A\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle>\<^sub>n\<^sub>d\<close>
  by (fact P_nd_\<omega>_useless)

lemma P_nd_induct [case_names adm base step] :
  \<open>adm\<^sub>\<down> P \<Longrightarrow> P \<sigma> \<Longrightarrow> (\<And>X. P X \<Longrightarrow> P (P_nd_step (\<epsilon> A) (\<tau> A) X)) \<Longrightarrow> P P\<llangle>A\<rrangle>\<^sub>n\<^sub>d\<close>
  unfolding P_nd_def
  by (rule restriction_fix_ind[OF P_nd_step_constructive_bis]) simp_all

lemma P_nd_induct_iterated [consumes 1, case_names adm base step] :
  \<open>\<lbrakk>0 < k; adm\<^sub>\<down> P; P \<sigma>; \<And>X. P X \<Longrightarrow> P ((P_nd_step (\<epsilon> A) (\<tau> A) ^^ k) X)\<rbrakk> \<Longrightarrow> P P\<llangle>A\<rrangle>\<^sub>n\<^sub>d\<close>
  unfolding P_nd_def
  by (rule restriction_fix_ind_iterated[where f = \<open>P_nd_step (\<epsilon> A) (\<tau> A)\<close>]) auto



text \<open>New version with final state notion where we just have \<^const>\<open>SKIPS\<close>.\<close>

abbreviation P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step ::
  \<open>[('\<sigma>, 'a) enabl, ('\<sigma>, 'a) trans\<^sub>n\<^sub>d, '\<sigma> \<Rightarrow> 'r set, '\<sigma> \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, '\<sigma>] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step \<epsilon>\<^sub>A \<tau>\<^sub>A \<omega>\<^sub>A X \<sigma> \<equiv> if \<omega>\<^sub>A \<sigma> = {} then P_nd_step \<epsilon>\<^sub>A \<tau>\<^sub>A X \<sigma> else SKIPS (\<omega>\<^sub>A \<sigma>)\<close>

definition P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd :: \<open>('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme \<Rightarrow> '\<sigma> \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (\<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>_\<rrangle>\<^sub>n\<^sub>d\<close> 1000)
  where \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<equiv> \<upsilon> X. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step (\<epsilon> A) (\<tau> A) (\<omega> A) X\<close>



lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step_constructive [simp] : \<open>constructive (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step \<epsilon>\<^sub>A \<tau>\<^sub>A \<omega>\<^sub>A)\<close> by auto


lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step_cont [simp] : \<open>\<forall>\<sigma> a. finite (\<tau>\<^sub>A \<sigma> a) \<Longrightarrow> cont (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step \<epsilon>\<^sub>A \<tau>\<^sub>A \<omega>\<^sub>A)\<close>
  by (simp add: cont_fun)

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step_constructive_bis : \<open>constructive (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step (\<epsilon> A) (\<tau> A) (\<omega> A))\<close> by simp

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step_cont_bis [simp] : \<open>finite_trans A \<Longrightarrow> cont (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step (\<epsilon> A) (\<tau> A) (\<omega> A))\<close>
  by (simp add: finite_trans_def)

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_rec: \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d = (\<lambda>\<sigma>. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step (\<epsilon> A) (\<tau> A) (\<omega> A) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>)\<close>
  by (unfold P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_def, rule ext, subst restriction_fix_eq, simp_all)

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_is_fix : \<open>finite_trans A \<Longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d = (\<mu> X. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step (\<epsilon> A) (\<tau> A) (\<omega> A) X)\<close>
  by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_def restriction_fix_is_fix)

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_induct [case_names adm base step] :
  \<open>adm\<^sub>\<down> P \<Longrightarrow> P \<sigma> \<Longrightarrow> (\<And>X. P X \<Longrightarrow> P (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step (\<epsilon> A) (\<tau> A) (\<omega> A) X)) \<Longrightarrow> P P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d\<close>
  unfolding P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_def
  by (rule restriction_fix_ind[OF P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step_constructive_bis]) simp_all

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_induct_iterated [consumes 1, case_names adm base step] :
  \<open>\<lbrakk>0 < k; adm\<^sub>\<down> P; P \<sigma>; \<And>X. P X \<Longrightarrow> P ((P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step (\<epsilon> A) (\<tau> A) (\<omega> A) ^^ k) X)\<rbrakk> \<Longrightarrow> P P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d\<close>
  unfolding P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_def
  by (rule restriction_fix_ind_iterated[where f = \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step (\<epsilon> A) (\<tau> A) (\<omega> A)\<close>]) auto



text \<open>Correspondence when we always have \<^term>\<open>\<omega> A \<sigma> = {}\<close>.\<close>

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_empty_\<rho> : \<open>\<rho> A = {} \<Longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d = P\<llangle>A\<rrangle>\<^sub>n\<^sub>d\<close>
  by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_def P_nd_def \<rho>_simps)

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_updated_\<omega>: \<open>P\<llangle>A\<rrangle>\<^sub>n\<^sub>d = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle>\<^sub>n\<^sub>d\<close>
  by (metis (mono_tags, lifting) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_empty_\<rho> P_nd_\<omega>_useless_bis \<rho>\<^sub>n\<^sub>d.simps
      empty_Collect_eq select_convs(2) surjective update_convs(2))

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_empty_\<rho>_inter_\<R>\<^sub>n\<^sub>d:
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma> = P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>\<close> if \<open>\<rho> A \<inter> \<R>\<^sub>n\<^sub>d A \<sigma> = {}\<close>
proof -
  have \<open>\<sigma>' \<in> \<R>\<^sub>n\<^sub>d A \<sigma> \<Longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>' = P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>'\<close> for \<sigma>'
  proof (induct A arbitrary: \<sigma>' rule: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_induct)
    case adm show ?case by simp
  next
    case base show \<open>P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>' = P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>'\<close> ..
  next
    case (step X)
    from step.prems(1) that have \<open>\<sigma>' \<notin> \<rho> A\<close> by blast
    hence \<open>\<omega> A \<sigma>' = {}\<close> by (simp add: \<rho>_simps)
    thus ?case
      by (subst P_nd_rec, auto intro!: mono_Mprefix_eq mono_GlobalNdet_eq)
        (metis (lifting) \<R>\<^sub>n\<^sub>d.simps step.hyps step.prems)
  qed
  thus \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma> = P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>\<close> by (simp add: \<R>\<^sub>n\<^sub>d.init)
qed



lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_rec_notin_\<rho>:
  \<open>\<sigma> \<notin> \<rho> A \<Longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma> = P_nd_step (\<epsilon> A) (\<tau> A) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>\<close>
  by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_rec) (simp add: \<rho>_simps)

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_rec_in_\<rho>: \<open>\<sigma> \<in> \<rho> A \<Longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma> = SKIPS (\<omega> A \<sigma>)\<close>
  by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_rec, simp add: \<rho>_simps)



subsection \<open>Deterministic Case\<close>

text \<open>First version, without final state notion.\<close>

abbreviation P_d_step :: \<open>[('\<sigma>, 'a) enabl, ('\<sigma>, 'a) trans\<^sub>d, '\<sigma> \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, '\<sigma>] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where \<open>P_d_step \<epsilon>\<^sub>A \<tau>\<^sub>A X s \<equiv> \<box> e \<in> \<epsilon>\<^sub>A s \<rightarrow> X \<lceil>\<tau>\<^sub>A s e\<rceil>\<close>

definition P_d :: \<open>('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>d_scheme \<Rightarrow> '\<sigma> \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (\<open>P\<llangle>_\<rrangle>\<^sub>d\<close> 1000)
  where \<open>P\<llangle>A\<rrangle>\<^sub>d \<equiv> \<upsilon> X. P_d_step (\<epsilon> A) (\<tau> A) X\<close>


lemma P_d_step_constructive[simp] : \<open>constructive (P_d_step \<epsilon>\<^sub>A \<tau>\<^sub>A)\<close> by simp

lemmas P_d_step_constructive_bis = P_d_step_constructive[of \<open>\<epsilon> A\<close> \<open>\<tau> A\<close>] for A

lemma P_d_step_cont[simp]: \<open>cont (P_d_step \<epsilon>\<^sub>A \<tau>\<^sub>A)\<close>
  by (simp add: cont_fun)

lemmas P_d_step_cont_bis = P_d_step_cont[of \<open>\<epsilon> A\<close> \<open>\<tau> A\<close>] for A

lemma P_d_rec: \<open>P\<llangle>A\<rrangle>\<^sub>d = (\<lambda>s. P_d_step (\<epsilon> A) (\<tau> A) P\<llangle>A\<rrangle>\<^sub>d s)\<close>
  by (unfold P_d_def, subst restriction_fix_eq) simp_all

lemma P_d_is_fix : \<open>P\<llangle>A\<rrangle>\<^sub>d = (\<mu> X. P_d_step (\<epsilon> A) (\<tau> A) X)\<close>
  by (simp add: P_d_def restriction_fix_is_fix)


lemma P_d_\<omega>_useless: \<open>P\<llangle>A\<rrangle>\<^sub>d = P\<llangle>A\<lparr>\<omega> := some_\<omega>\<rparr>\<rrangle>\<^sub>d\<close>
  by (simp add: P_d_def \<epsilon>_simps)

lemma P_d_\<omega>_useless_bis: \<open>P\<llangle>A\<rrangle>\<^sub>d = P\<llangle>A\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle>\<^sub>d\<close>
  by (fact P_d_\<omega>_useless)

lemma P_d_induct [case_names adm base step] :
  \<open>\<lbrakk>adm\<^sub>\<down> P; P \<sigma>; \<And>X. P X \<Longrightarrow> P (P_d_step (\<epsilon> A) (\<tau> A) X)\<rbrakk> \<Longrightarrow> P P\<llangle>A\<rrangle>\<^sub>d\<close>
  unfolding P_d_def
  by (rule restriction_fix_ind[OF P_d_step_constructive_bis]) simp_all

lemma P_d_induct_iterated [consumes 1, case_names adm base step] :
  \<open>\<lbrakk>0 < k; adm\<^sub>\<down> P; P \<sigma>; \<And>X. P X \<Longrightarrow> P ((P_d_step (\<epsilon> A) (\<tau> A) ^^ k) X)\<rbrakk> \<Longrightarrow> P P\<llangle>A\<rrangle>\<^sub>d\<close>
  unfolding P_d_def
  by (rule restriction_fix_ind_iterated[where f = \<open>P_d_step (\<epsilon> A) (\<tau> A)\<close>]) auto



text \<open>New version with final state notion where we just \<^const>\<open>SKIP\<close>.\<close>

abbreviation P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_step ::
  \<open>[('\<sigma>, 'a) enabl, ('\<sigma>, 'a) trans\<^sub>d, '\<sigma> \<Rightarrow> 'r option, '\<sigma> \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k, '\<sigma>] \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close>
  where \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_step \<epsilon>\<^sub>A \<tau>\<^sub>A \<omega>\<^sub>A X \<sigma> \<equiv> case \<omega>\<^sub>A \<sigma> of \<lfloor>r\<rfloor> \<Rightarrow> SKIP r | \<diamond> \<Rightarrow> P_d_step \<epsilon>\<^sub>A \<tau>\<^sub>A X \<sigma>\<close>

definition P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d :: \<open>('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>d_scheme \<Rightarrow> '\<sigma> \<Rightarrow> ('a, 'r) process\<^sub>p\<^sub>t\<^sub>i\<^sub>c\<^sub>k\<close> (\<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>_\<rrangle>\<^sub>d\<close> 1000)
  where \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<equiv> \<upsilon> X. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_step (\<epsilon> A) (\<tau> A) (\<omega> A) X\<close>

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_step_constructive[simp]: \<open>constructive (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_step \<epsilon>\<^sub>A \<tau>\<^sub>A \<S>\<^sub>F\<^sub>A)\<close>
  by (auto simp add: option.case_eq_if)

lemmas P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_step_constructive_bis = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_step_constructive[of \<open>\<epsilon> A\<close> \<open>\<tau> A\<close> \<open>\<omega> A\<close>] for A


lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_step_cont[simp]: \<open>cont (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_step \<epsilon>\<^sub>A \<tau>\<^sub>A \<S>\<^sub>F\<^sub>A)\<close>
  by (simp add: cont_fun option.case_eq_if)

lemmas P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_step_cont_bis = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_step_cont[of \<open>\<epsilon> A\<close> \<open>\<tau> A\<close> \<open>\<omega> A\<close>] for A

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_rec: \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d = (\<lambda>\<sigma>. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_step (\<epsilon> A) (\<tau> A) (\<omega> A) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>)\<close>
  by (unfold P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_def, subst restriction_fix_eq) auto

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_is_fix : \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d = (\<mu> X. P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_step (\<epsilon> A) (\<tau> A) (\<omega> A) X)\<close>
  by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_def restriction_fix_is_fix)


lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_induct [case_names adm base step] :
  \<open>adm\<^sub>\<down> P \<Longrightarrow> P \<sigma> \<Longrightarrow> (\<And>X. P X \<Longrightarrow> P (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_step (\<epsilon> A) (\<tau> A) (\<omega> A) X)) \<Longrightarrow> P P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d\<close>
  unfolding P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_def
  by (rule restriction_fix_ind[OF P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_step_constructive_bis]) simp_all

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_induct_iterated [consumes 1, case_names adm base step] :
  \<open>\<lbrakk>0 < k; adm\<^sub>\<down> P; P \<sigma>; \<And>X. P X \<Longrightarrow> P ((P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_step (\<epsilon> A) (\<tau> A) (\<omega> A) ^^ k) X)\<rbrakk> \<Longrightarrow> P P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d\<close>
  unfolding P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_def
  by (rule restriction_fix_ind_iterated[where f = \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_step (\<epsilon> A) (\<tau> A) (\<omega> A)\<close>]) auto



text \<open>Correspondence when we always have \<^term>\<open>\<omega> A \<sigma> = {}\<close>.\<close>

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_empty_\<rho> : \<open>\<rho> A = {} \<Longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d = P\<llangle>A\<rrangle>\<^sub>d\<close>
  by (simp add: \<rho>_simps P_d_def P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_def)

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_updated_\<omega>: \<open>P\<llangle>A\<rrangle>\<^sub>d = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle>\<^sub>d\<close>
  by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_empty_\<rho> P_d_\<omega>_useless \<rho>_simps)


lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_empty_\<rho>_inter_\<R>\<^sub>d:
  \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma> = P\<llangle>A\<rrangle>\<^sub>d \<sigma>\<close> if \<open>\<rho> A \<inter> \<R>\<^sub>d A \<sigma> = {}\<close>
proof -
  have \<open>\<sigma>' \<in> \<R>\<^sub>d A \<sigma> \<Longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>' = P\<llangle>A\<rrangle>\<^sub>d \<sigma>'\<close> for \<sigma>'
  proof (induct A arbitrary: \<sigma>' rule: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_induct)
    case adm show ?case by simp
  next
    case base show \<open>P\<llangle>A\<rrangle>\<^sub>d \<sigma>' = P\<llangle>A\<rrangle>\<^sub>d \<sigma>'\<close> ..
  next
    case (step X)
    from step.prems(1) that have \<open>\<sigma>' \<notin> \<rho> A\<close> by blast
    hence \<open>\<omega> A \<sigma>' = \<diamond>\<close> by (simp add: \<rho>_simps)
    thus ?case
      by (subst P_d_rec, auto intro!: mono_Mprefix_eq mono_GlobalNdet_eq)
        (subst (asm) \<epsilon>_simps, auto, metis (lifting) \<R>\<^sub>d.step step.hyps step.prems)
  qed
  thus \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma> = P\<llangle>A\<rrangle>\<^sub>d \<sigma>\<close> by (simp add: \<R>\<^sub>d.init)
qed



lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_rec_notin_\<rho>:
  \<open>\<sigma> \<notin> \<rho> A \<Longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma> = P_d_step (\<epsilon> A) (\<tau> A) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>\<close>
  by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_rec) (simp add: \<rho>_simps)

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_rec_in_\<rho>: \<open>\<sigma> \<in> \<rho> A \<Longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma> = SKIP \<lceil>\<omega> A \<sigma>\<rceil>\<close>
  by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_rec, simp add: \<rho>_simps split: option.split)



subsection \<open>Link between deterministic and non-deterministic ProcOmata\<close>

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_det_to_ndet_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d : \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>n\<^sub>d = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d\<close>
proof (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_def, rule restriction_fix_unique)
  show \<open>constructive (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step (\<epsilon> \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) (\<tau> \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) (\<omega> \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d))\<close> by simp
next
  show \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step (\<epsilon> \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) (\<tau> \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) (\<omega> \<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d\<close>
    by (subst (3) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_rec)
      (rule ext, auto simp add: from_det_to_ndet_def \<epsilon>_simps
        split: option.split intro: mono_Mprefix_eq)
qed


corollary P_nd_from_det_to_ndet_is_P_d : \<open>P\<llangle>\<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>n\<^sub>d = P\<llangle>A\<rrangle>\<^sub>d\<close>
proof -
  have \<open>P\<llangle>\<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>n\<^sub>d = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr>\<rrangle>\<^sub>n\<^sub>d\<close>
    by (fact P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_updated_\<omega>)
  also have \<open>\<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<lparr>\<omega> := \<lambda>\<sigma>. {}\<rparr> = \<llangle>A\<lparr>\<omega> := \<lambda>\<sigma>. \<diamond>\<rparr>\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<close>
    by (simp add: from_det_to_ndet_def)
  finally show \<open>P\<llangle>\<llangle>A\<rrangle>\<^sub>d\<^sub>\<hookrightarrow>\<^sub>n\<^sub>d\<rrangle>\<^sub>n\<^sub>d = P\<llangle>A\<rrangle>\<^sub>d\<close>
    by (simp add: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_updated_\<omega> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_det_to_ndet_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d)
qed



subsection \<open>Prove Equality between ProcOmata\<close>

subsubsection \<open>This is the easiest method we can think about.\<close>

lemma P_d_eqI : \<open>(\<And>\<sigma> a. \<tau> A \<sigma> a = \<tau> B \<sigma> a) \<Longrightarrow> P\<llangle>A\<rrangle>\<^sub>d = P\<llangle>B\<rrangle>\<^sub>d\<close>
  by (simp add: P_d_def \<epsilon>_simps)

lemma P_nd_eqI : \<open>(\<And>\<sigma> a. \<tau> A \<sigma> a = \<tau> B \<sigma> a) \<Longrightarrow> P\<llangle>A\<rrangle>\<^sub>n\<^sub>d = P\<llangle>B\<rrangle>\<^sub>n\<^sub>d\<close>
  by (simp add: P_nd_def \<epsilon>_simps)

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_eqI :
  \<open>(\<And>\<sigma> a. \<sigma> \<notin> \<rho> A \<Longrightarrow> \<tau> A \<sigma> a = \<tau> B \<sigma> a) \<Longrightarrow> (\<And>\<sigma>. \<omega> A \<sigma> = \<omega> B \<sigma>) \<Longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>B\<rrangle>\<^sub>d\<close>
  by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_def, rule restriction_fix_unique, simp)
    (subst (2) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_rec, auto simp add: \<epsilon>_simps \<rho>_simps split: option.split)

lemma P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_eqI :
  \<open>(\<And>\<sigma> a. \<sigma> \<notin> \<rho> A \<Longrightarrow> \<tau> A \<sigma> a = \<tau> B \<sigma> a) \<Longrightarrow> (\<And>\<sigma>. \<omega> A \<sigma> = \<omega> B \<sigma>) \<Longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>B\<rrangle>\<^sub>n\<^sub>d\<close>
  by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_def, rule restriction_fix_unique[OF P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step_constructive])
    (subst (2) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_rec, auto simp add: \<epsilon>_simps \<rho>_simps split: option.split)



subsubsection \<open>We establish now a much more powerful theorem.\<close>

theorem P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_eqI_strong:
  (* TODO: see if we can obtain better by looking at \<rho> *)
  assumes inj_on_f : \<open>inj_on f (\<R>\<^sub>n\<^sub>d A\<^sub>0 \<sigma>\<^sub>0)\<close>
    and eq_trans : \<open>\<And>\<sigma>\<^sub>0' a. \<sigma>\<^sub>0' \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 \<sigma>\<^sub>0 \<Longrightarrow> \<tau> A\<^sub>1 (f \<sigma>\<^sub>0') a = f ` (\<tau> A\<^sub>0 \<sigma>\<^sub>0' a)\<close>
    and eq_fin : \<open>\<And>\<sigma>\<^sub>0'. \<sigma>\<^sub>0' \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 \<sigma>\<^sub>0 \<Longrightarrow> \<omega> A\<^sub>1 (f \<sigma>\<^sub>0') = \<omega> A\<^sub>0 \<sigma>\<^sub>0'\<close>
  shows \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d (f \<sigma>\<^sub>0)\<close>
proof -
  have \<open>\<sigma>\<^sub>0' \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 \<sigma>\<^sub>0 \<Longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d (f \<sigma>\<^sub>0') = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0'\<close> for \<sigma>\<^sub>0'
  proof (induct A\<^sub>1 arbitrary: \<sigma>\<^sub>0' rule: P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_induct)
    case adm show ?case by simp
  next
    show \<open>\<sigma>\<^sub>0' \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 \<sigma>\<^sub>0 \<Longrightarrow> P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d (inv_into (\<R>\<^sub>n\<^sub>d A\<^sub>0 \<sigma>\<^sub>0) f (f \<sigma>\<^sub>0')) = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0'\<close> for \<sigma>\<^sub>0'
      by (simp add: inj_on_f)
  next
    case (step X)
    from step.prems eq_trans have \<open>\<epsilon> A\<^sub>0 \<sigma>\<^sub>0' = \<epsilon> A\<^sub>1 (f \<sigma>\<^sub>0')\<close>
      by (auto simp add: \<epsilon>_simps)
    moreover have \<open>\<omega> A\<^sub>1 (f \<sigma>\<^sub>0') = \<omega> A\<^sub>0 \<sigma>\<^sub>0'\<close> by (simp add: eq_fin step.prems)
    ultimately show ?case
      by (subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_rec, auto)
        (metis (mono_tags, lifting) \<R>\<^sub>n\<^sub>d.step eq_trans mono_GlobalNdet_eq2
          step.hyps step.prems)
  qed
  thus \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d (f \<sigma>\<^sub>0)\<close> by (simp add: \<R>\<^sub>n\<^sub>d.init)
qed


theorem P_nd_eqI_strong:
  \<open>\<lbrakk>inj_on f (\<R>\<^sub>n\<^sub>d A\<^sub>0 \<sigma>\<^sub>0);
    \<And>\<sigma>\<^sub>0' a. \<sigma>\<^sub>0' \<in> \<R>\<^sub>n\<^sub>d A\<^sub>0 \<sigma>\<^sub>0 \<Longrightarrow> \<tau> A\<^sub>1 (f \<sigma>\<^sub>0') a = f ` (\<tau> A\<^sub>0 \<sigma>\<^sub>0' a)\<rbrakk>
  \<Longrightarrow> P\<llangle>A\<^sub>0\<rrangle>\<^sub>n\<^sub>d \<sigma>\<^sub>0 = P\<llangle>A\<^sub>1\<rrangle>\<^sub>n\<^sub>d (f \<sigma>\<^sub>0)\<close>
  by (unfold P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_updated_\<omega>, rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_eqI_strong) simp_all


theorem P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_eqI_strong:
  assumes \<open>inj_on f (\<R>\<^sub>d A\<^sub>0 \<sigma>\<^sub>0)\<close>
    and \<open>\<And>\<sigma>\<^sub>0' a. \<sigma>\<^sub>0' \<in> \<R>\<^sub>d A\<^sub>0 \<sigma>\<^sub>0 \<Longrightarrow> \<tau> A\<^sub>1 (f \<sigma>\<^sub>0') a = map_option f (\<tau> A\<^sub>0 \<sigma>\<^sub>0' a)\<close>
    and \<open>\<And>\<sigma>\<^sub>0'. \<sigma>\<^sub>0' \<in> \<R>\<^sub>d A\<^sub>0 \<sigma>\<^sub>0 \<Longrightarrow> \<omega> A\<^sub>1 (f \<sigma>\<^sub>0') = \<omega> A\<^sub>0 \<sigma>\<^sub>0'\<close>
  shows \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<^sub>1\<rrangle>\<^sub>d (f \<sigma>\<^sub>0)\<close>
  by (fold P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_det_to_ndet_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d, rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_eqI_strong)
    (unfold \<R>\<^sub>n\<^sub>d_from_det_to_ndet,
      simp_all add: assms from_det_to_ndet_def map_option_case split: option.split)


theorem P_d_eqI_strong:
  \<open>\<lbrakk>inj_on f (\<R>\<^sub>d A\<^sub>0 \<sigma>\<^sub>0);
    \<And>\<sigma>\<^sub>0' a. \<sigma>\<^sub>0' \<in> \<R>\<^sub>d A\<^sub>0 \<sigma>\<^sub>0 \<Longrightarrow> \<tau> A\<^sub>1 (f \<sigma>\<^sub>0') a = map_option f (\<tau> A\<^sub>0 \<sigma>\<^sub>0' a)\<rbrakk>
   \<Longrightarrow> P\<llangle>A\<^sub>0\<rrangle>\<^sub>d \<sigma>\<^sub>0 = P\<llangle>A\<^sub>1\<rrangle>\<^sub>d (f \<sigma>\<^sub>0)\<close>
  by (unfold P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_updated_\<omega>, rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_eqI_strong) simp_all


lemmas P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_eqI_strong_id = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_eqI_strong[of id, simplified]
  and  P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_eqI_strong_id = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_eqI_strong
  [of id, simplified id_def option.map_ident, simplified]
  and  P_nd_eqI_strong_id = P_nd_eqI_strong[of id, simplified]
  and  P_d_eqI_strong_id = P_d_eqI_strong
  [of id, simplified id_def option.map_ident, simplified]


corollary P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_\<sigma>_to_\<sigma>s_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd : \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<^sub>n\<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<rrangle>\<^sub>n\<^sub>d [\<sigma>] = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>\<close>
  by (auto simp add: image_iff behaviour_\<sigma>_\<sigma>s_conv(6, 8)
      intro!: inj_onI P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_eqI_strong[symmetric])

corollary P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_from_\<sigma>_to_\<sigma>s_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d : \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<rrangle>\<^sub>d [\<sigma>] = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>\<close>
  by (auto simp add: image_iff behaviour_\<sigma>_\<sigma>s_conv(2, 4)
      intro!: inj_onI P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_eqI_strong[symmetric] split: option.split)

corollary P_nd_from_\<sigma>_to_\<sigma>s_is_P_nd : \<open>P\<llangle>\<^sub>n\<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<rrangle>\<^sub>n\<^sub>d [\<sigma>] = P\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>\<close>
  by (auto simp add: image_iff behaviour_\<sigma>_\<sigma>s_conv(6, 8)
      intro!: inj_onI P_nd_eqI_strong[symmetric])

corollary P_d_from_\<sigma>_to_\<sigma>s_is_P_d : \<open>P\<llangle>\<^sub>d\<llangle>A\<rrangle>\<^sub>\<sigma>\<^sub>\<hookrightarrow>\<^sub>\<sigma>\<^sub>s\<rrangle>\<^sub>d [\<sigma>] = P\<llangle>A\<rrangle>\<^sub>d \<sigma>\<close>
  by (auto simp add: image_iff behaviour_\<sigma>_\<sigma>s_conv(2, 4)
      intro!: inj_onI P_d_eqI_strong[symmetric] split: option.split)



text \<open>Behaviour of normalizations. We will use the following methods in combining theories.\<close>
  (* 
method P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_when_indep_method uses indep R_d_subset R_nd_subset trans_result defs = 
  subst P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d_is_some_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd, rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_ndI_strong_id[rule_format], simp_all,
  subst (asm) \<R>\<^sub>n\<^sub>d_is_\<R>\<^sub>d, drule set_mp[OF R_d_subset, rotated],
  (simp add: indep)?, (insert trans_result indep)[1], fastforce,
  rule arg_cong2[where f = \<open>(\<inter>)\<close>], solves simp, simp add: det_ndet_conv_defs defs

method P_when_indep_method uses indep R_d_subset trans_result = 
  subst P_d_is_some_P_nd, rule P_ndI_strong_id[rule_format], simp_all, 
  subst (asm) \<R>\<^sub>n\<^sub>d_is_\<R>\<^sub>d, drule set_mp[OF R_d_subset, rotated], (simp add: indep)?, (*for arbitrary*)
  (insert trans_result indep)[1], fastforce
 *)



(* TODO: find a better place for the things below ? *)
fun recursive_modifier_fun\<^sub>d :: \<open>[('\<sigma> \<times> 'a) \<Rightarrow> '\<sigma> option, (('\<sigma> \<times> 'a) \<times> '\<sigma> option) list] \<Rightarrow> ('\<sigma> \<times> 'a) \<Rightarrow> '\<sigma> option\<close>
  where \<open>recursive_modifier_fun\<^sub>d f [] = f\<close>
  |     \<open>recursive_modifier_fun\<^sub>d f (((s, e), t) # \<G>\<^sub>A) = recursive_modifier_fun\<^sub>d (f((s, e) := t)) \<G>\<^sub>A\<close>


abbreviation recursive_constructor_A\<^sub>d :: \<open>[(('\<sigma> \<times> 'a) \<times> '\<sigma> option) list, '\<sigma> \<Rightarrow> 'r option] \<Rightarrow> ('\<sigma>, 'a, 'r) A\<^sub>d\<close>
  where \<open>recursive_constructor_A\<^sub>d \<G>\<^sub>A \<omega>\<^sub>A \<equiv> \<lparr>\<tau> = curry (recursive_modifier_fun\<^sub>d (\<lambda>(s, e). \<diamond>) \<G>\<^sub>A), \<omega> = \<omega>\<^sub>A\<rparr>\<close>


lemma \<epsilon>_det_breaker:
  \<open>\<epsilon> (\<lparr>\<tau> = curry (g((\<sigma>'::'\<sigma>, a) \<mapsto> \<sigma>''::'\<sigma>)), \<omega> = some_\<omega>, \<dots> = some_more\<rparr> ) \<sigma> = 
   (if \<sigma> = \<sigma>' then {a} \<union> \<epsilon> \<lparr>\<tau> = curry g, \<omega> = some_\<omega>\<rparr> \<sigma>' else \<epsilon> \<lparr>\<tau> = curry g, \<omega> = some_\<omega>\<rparr> \<sigma>)\<close>
  by (auto simp add: \<epsilon>_simps split: if_splits)

method \<epsilon>_det_calc = (unfold recursive_modifier_fun\<^sub>d.simps \<epsilon>_det_breaker, simp cong: if_cong)[1]

method \<tau>_det_calc = (unfold recursive_modifier_fun\<^sub>d.simps, simp cong: if_cong)[1]







lemma bij_Renaming_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd :
  fixes A :: \<open>('\<sigma>, 'a, 'r, '\<alpha>) A\<^sub>n\<^sub>d_scheme\<close> and f :: \<open>'a \<Rightarrow> 'b\<close> and g :: \<open>'r \<Rightarrow> 's\<close>
  assumes \<open>bij f\<close>
  defines B_def : \<open>B \<equiv> \<lparr>\<tau> = \<lambda>\<sigma> b. \<tau> A \<sigma> (inv f b), \<omega> = \<lambda>\<sigma>. g ` (\<omega> A \<sigma>)\<rparr>\<close>
  shows \<open>Renaming (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) f g = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>B\<rrangle>\<^sub>n\<^sub>d \<sigma>\<close> (is \<open>?lhs \<sigma> = _\<close>)
proof (rule fun_cong[of ?lhs \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>B\<rrangle>\<^sub>n\<^sub>d\<close> \<sigma>])
  show \<open>?lhs = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>B\<rrangle>\<^sub>n\<^sub>d\<close>
  proof (rule restriction_fix_unique[OF P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step_constructive_bis[of B],
        symmetric, folded P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_def])
    show \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step (\<epsilon> B) (\<tau> B) (\<omega> B) ?lhs = ?lhs\<close>
    proof (rule ext)
      have * : \<open>\<epsilon> B \<sigma> = f ` \<epsilon> A \<sigma>\<close> for \<sigma>
        by (simp add: B_def \<epsilon>_simps image_def) (metis \<open>bij f\<close> bij_inv_eq_iff)
      have ** : \<open>inv f (f a) = a\<close> for a
        by (metis \<open>bij f\<close> bij_inv_eq_iff)
      have *** : \<open>(THE a'. f a' = f a) = a\<close> for a
        by (rule the1_equality', metis (mono_tags, lifting) Uniq_I assms(1) bij_betw_def injD, simp)
      show \<open>P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_step (\<epsilon> B) (\<tau> B) (\<omega> B) ?lhs \<sigma> = ?lhs \<sigma>\<close> for \<sigma>
        by (subst (2) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_rec, simp add: "*")
          (auto simp add: "**" "***" B_def Renaming_distrib_GlobalNdet
            Renaming_Mprefix_image_inj[OF \<open>bij f\<close>[THEN bij_is_inj]]
            intro: mono_Mprefix_eq)
    qed
  qed
qed

lemma bij_Renaming_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d :
  \<open>bij f \<Longrightarrow> Renaming (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>) f g =
             P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<lparr>\<tau> = \<lambda>\<sigma> b. \<tau> A \<sigma> (inv f b), \<omega> = \<lambda>\<sigma>. map_option g (\<omega> A \<sigma>)\<rparr>\<rrangle>\<^sub>d \<sigma>\<close>
  by (subst (1 2) P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_from_det_to_ndet_is_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d[symmetric],
      subst bij_Renaming_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd, assumption)
    (rule fun_cong[of _ _ \<sigma>], rule P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd_eqI,
      simp_all add: from_det_to_ndet_def split: option.split)


lemma RenamingTick_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd :
  \<open>RenamingTick (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>n\<^sub>d \<sigma>) g = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<lparr>\<tau> = \<tau> A, \<omega> = \<lambda>\<sigma>. g ` \<omega> A \<sigma>\<rparr>\<rrangle>\<^sub>n\<^sub>d \<sigma>\<close>
  by (simp add: bij_Renaming_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_nd)

lemma RenamingTick_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d :
  \<open>RenamingTick (P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>A\<rrangle>\<^sub>d \<sigma>) g = P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S\<llangle>\<lparr>\<tau> = \<tau> A, \<omega> = \<lambda>\<sigma>. map_option g (\<omega> A \<sigma>)\<rparr>\<rrangle>\<^sub>d \<sigma>\<close>
  by (simp add: bij_Renaming_P\<^sub>S\<^sub>K\<^sub>I\<^sub>P\<^sub>S_d)



(*<*)
end
  (*>*)