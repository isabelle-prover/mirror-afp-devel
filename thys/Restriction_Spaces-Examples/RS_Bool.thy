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


section \<open>Booleans\<close>

(*<*)
theory RS_Bool
  imports Restriction_Spaces
begin
  (*>*)

text \<open>Restriction instance for \<^typ>\<open>bool\<close>.\<close>

instantiation bool :: restriction
begin

definition restriction_bool :: \<open>bool \<Rightarrow> nat \<Rightarrow> bool\<close>
  where \<open>b \<down> n \<equiv> if n = 0 then False else b\<close>

instance by (intro_classes) (auto simp add: restriction_bool_def)
end


lemma restriction_bool_0_is_False [simp] : \<open>b \<down> 0 = False\<close>
  by (simp add: restriction_bool_def)


text \<open>Restriction space instance for \<^typ>\<open>bool\<close>.\<close>

instance bool :: restriction_space
  by intro_classes (simp_all add: restriction_bool_def gt_ex)



text \<open>Complete Restriction space instance for \<^typ>\<open>bool\<close>.\<close>

lemma restriction_tendsto_bool_iff :
  \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<longleftrightarrow> (\<exists>n. \<forall>k\<ge>n. \<sigma> k = \<Sigma>)\<close> for \<Sigma> :: bool
  unfolding restriction_tendsto_def
  by (auto simp add: restriction_bool_def)


instance bool :: complete_restriction_space
proof intro_classes
  fix \<sigma> :: \<open>nat \<Rightarrow> bool\<close> assume \<open>chain\<^sub>\<down> \<sigma>\<close>
  hence \<open>(\<forall>n>0. \<not> \<sigma> n) \<or> (\<forall>n>0. \<sigma> n)\<close>
    by (simp add: restriction_chain_def restriction_bool_def split: if_split_asm)
      (metis One_nat_def Zero_not_Suc gr0_conv_Suc nat_induct_non_zero zero_induct)
  hence \<open>\<sigma> \<midarrow>\<down>\<rightarrow> False \<or> \<sigma> \<midarrow>\<down>\<rightarrow> True\<close>
    by (metis (full_types) gt_ex order.strict_trans2 restriction_tendsto_def)
  thus \<open>convergent\<^sub>\<down> \<sigma>\<close>
    using restriction_convergentI by blast
qed



lemma restriction_cont_imp_restriction_adm :
  \<open>cont\<^sub>\<down> P \<Longrightarrow> adm\<^sub>\<down> P\<close> for P :: \<open>'a :: restriction_space \<Rightarrow> bool\<close>
  unfolding restriction_adm_def restriction_cont_on_def restriction_cont_at_def
  by (auto simp add: restriction_tendsto_bool_iff)


lemma restriction_compact_bool : \<open>compact\<^sub>\<down> (UNIV :: bool set)\<close>
  by (simp add: finite_imp_restriction_compact)

(*<*)
end
  (*>*)
