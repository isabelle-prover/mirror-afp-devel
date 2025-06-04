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


section \<open>Option Type\<close>

(*<*)
theory RS_Option
  imports Restriction_Spaces
begin
  (*>*)

subsection \<open>Restriction option type\<close>

instantiation option :: (restriction) restriction
begin

definition restriction_option :: \<open>'a option \<Rightarrow> nat \<Rightarrow> 'a option\<close>
  where \<open>x \<down> n \<equiv> if n = 0 then None else map_option (\<lambda>a. a \<down> n) x\<close>

instance
  by intro_classes
    (simp add: restriction_option_def option.map_comp comp_def min_def)

end

lemma restriction_option_0_is_None [simp] : \<open>x \<down> 0 = None\<close>
  by (simp add: restriction_option_def)

lemma restriction_option_None [simp] : \<open>None \<down> n = None\<close>
  by (simp add: restriction_option_def)

lemma restriction_option_Some [simp] : \<open>Some x \<down> n = (if n = 0 then None else Some (x \<down> n))\<close>
  by (simp add: restriction_option_def)

lemma restriction_option_eq_None_iff : \<open>x \<down> n = None \<longleftrightarrow> n = 0 \<or> x = None\<close>
  by (cases x) simp_all

lemma restriction_option_eq_Some_iff : \<open>x \<down> n = Some y \<longleftrightarrow> n \<noteq> 0 \<and> x \<noteq> None \<and> y = the x \<down> n\<close>
  by (cases x) auto



subsection \<open>Restriction space option type\<close>

instance option :: (restriction_space) restriction_space
proof intro_classes
  show \<open>x \<down> 0 = y \<down> 0\<close> for x y :: \<open>'a option\<close> by simp
next
  show \<open>x \<noteq> y \<Longrightarrow> \<exists>n. x \<down> n \<noteq> y \<down> n\<close> for x y :: \<open>'a option\<close>
    by (cases x; cases y, simp_all add: gt_ex)
      (metis bot_nat_0.not_eq_extremum ex_not_restriction_related restriction_0_related)
qed



subsection \<open>Complete restriction space option type\<close>

lemma option_restriction_chainE :
  fixes \<sigma> :: \<open>nat \<Rightarrow> 'a :: restriction_space option\<close> assumes \<open>chain\<^sub>\<down> \<sigma>\<close>
  obtains \<open>\<sigma> = (\<lambda>n. None)\<close>
  | \<sigma>' where \<open>chain\<^sub>\<down> \<sigma>'\<close> and \<open>\<sigma> = (\<lambda>n. if n = 0 then None else Some (\<sigma>' n))\<close>
proof -
  from \<open>chain\<^sub>\<down> \<sigma>\<close> consider \<open>\<forall>n. \<sigma> n = None\<close> | \<open>\<forall>n>0. \<sigma> n \<noteq> None\<close>
    by (metis bot_nat_0.not_eq_extremum linorder_neqE_nat
        restriction_chain_def_bis restriction_option_eq_None_iff)
  thus thesis
  proof cases
    from that(1) show \<open>\<forall>n. \<sigma> n = None \<Longrightarrow> thesis\<close> by fast
  next
    define \<sigma>' where \<open>\<sigma>' n \<equiv> if n = 0 then undefined \<down> 0 else the (\<sigma> n)\<close> for n
    assume \<open>\<forall>n>0. \<sigma> n \<noteq> None\<close>
    with \<open>chain\<^sub>\<down> \<sigma>\<close> have \<open>chain\<^sub>\<down> \<sigma>'\<close> \<open>\<sigma> = (\<lambda>n. if n = 0 then undefined \<down> 0 else Some (\<sigma>' n))\<close>
      by (simp_all add: \<sigma>'_def restriction_chain_def)
        (metis option.sel restriction_option_eq_Some_iff,
          metis \<sigma>'_def bot_nat_0.not_eq_extremum option.sel restriction_option_0_is_None)
    with that(2) show thesis by force
  qed
qed


lemma non_destructive_Some : \<open>non_destructive Some\<close>
  by (simp add: non_destructiveI)

lemma restriction_cont_Some : \<open>cont\<^sub>\<down> (Some :: 'a :: restriction_space \<Rightarrow> 'a option)\<close>
  by (rule restriction_shift_imp_restriction_cont[where k = 0])
    (simp add: restriction_shiftI)


instance option :: (complete_restriction_space) complete_restriction_space
proof intro_classes
  show \<open>chain\<^sub>\<down> \<sigma> \<Longrightarrow> convergent\<^sub>\<down> \<sigma>\<close> for \<sigma> :: \<open>nat \<Rightarrow> 'a option\<close>
  proof (elim option_restriction_chainE)
    show \<open>\<sigma> = (\<lambda>n. None) \<Longrightarrow> convergent\<^sub>\<down> \<sigma>\<close> by simp
  next
    fix \<sigma>' assume \<open>chain\<^sub>\<down> \<sigma>'\<close> and \<sigma>_def : \<open>\<sigma> = (\<lambda>n. if n = 0 then None else Some (\<sigma>' n))\<close>
    from \<open>chain\<^sub>\<down> \<sigma>'\<close> have \<open>convergent\<^sub>\<down> \<sigma>'\<close> by (simp add: restriction_chain_imp_restriction_convergent)
    hence \<open>convergent\<^sub>\<down> (\<lambda>n. \<sigma>' (n + 1))\<close> by (unfold restriction_convergent_shift_iff)
    then obtain \<Sigma>' where \<open>(\<lambda>n. \<sigma>' (n + 1)) \<midarrow>\<down>\<rightarrow> \<Sigma>'\<close> by (blast dest: restriction_convergentD')
    hence \<open>(\<lambda>n. Some (\<sigma>' (n + 1))) \<midarrow>\<down>\<rightarrow> Some \<Sigma>'\<close> by (fact restriction_contD[OF restriction_cont_Some])
    hence \<open>convergent\<^sub>\<down> (\<lambda>n. Some (\<sigma>' (n + 1)))\<close> by (blast intro: restriction_convergentI)
    hence \<open>convergent\<^sub>\<down> (\<lambda>n. \<sigma> (n + 1))\<close> by (simp add: \<sigma>_def)
    thus \<open>convergent\<^sub>\<down> \<sigma>\<close> using restriction_convergent_shift_iff by blast
  qed
qed


(*<*)
end
  (*>*)
