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


section \<open>Trivial Construction\<close>

(*<*)
theory RS_Any_Type
  imports Restriction_Spaces
begin 
  (*>*)


text \<open>Restriction instance for any type.\<close>

typedef 'a type' = \<open>UNIV :: 'a set\<close> by auto

instantiation type' :: (type) restriction
begin

lift_definition restriction_type' :: \<open>'a type' \<Rightarrow> nat \<Rightarrow> 'a type'\<close>
  is \<open>\<lambda>x n. if n = 0 then undefined else x\<close> .

instance by (intro_classes, transfer, simp add: min_def)

end


lemma restriction_type'_0_is_undefined [simp] :
  \<open>x \<down> 0 = undefined\<close> for x :: \<open>'a type'\<close> by transfer simp


instance type' :: (type) restriction_space
  by (intro_classes, simp, transfer, auto)


lemma restriction_tendsto_type'_iff :
  \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<longleftrightarrow> (\<exists>n0. \<forall>n\<ge>n0. \<sigma> n = \<Sigma>)\<close> for \<Sigma> :: \<open>'a type'\<close>
  by (simp add: restriction_tendsto_def, transfer, auto)


lemma restriction_chain_type'_iff :
  \<open>chain\<^sub>\<down> \<sigma> \<longleftrightarrow> \<sigma> 0 = undefined \<and> (\<forall>n\<ge>Suc 0. \<sigma> n = \<sigma> (Suc 0))\<close>
  for \<sigma> :: \<open>nat \<Rightarrow> 'a type'\<close>
  by (simp add: restriction_chain_def_ter, transfer, simp)
    (safe, (simp_all)[3], metis Suc_le_D Suc_le_eq zero_less_Suc)



instance type' :: (type) complete_restriction_space
  by intro_classes
    (auto simp add: restriction_chain_type'_iff restriction_convergent_def
      restriction_tendsto_type'_iff)

(*<*)
end
  (*>*)