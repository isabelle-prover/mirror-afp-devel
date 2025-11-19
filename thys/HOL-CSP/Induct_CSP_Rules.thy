(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSP - A Shallow Embedding of CSP in Isabelle/HOL
 * Version         : 2.0
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff, Lina Ye.
 *                   (Based on HOL-CSP 1.0 by Haykal Tej and Burkhart Wolff)
 *
 * This file       : More Fixpoint and k-Induction Schemata
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

chapter \<open> Advanced Induction Schemata \<close>

(*<*)
theory  Induct_CSP_Rules
  imports HOLCF
begin

default_sort type
  (*>*)

section \<open>k-fixpoint-induction\<close>

lemma nat_k_induct [case_names base step]:
  \<open>P n\<close> if \<open>\<forall>i<k. P i\<close> and \<open>\<forall>n\<^sub>0. (\<forall>i<k. P (n\<^sub>0 + i)) \<longrightarrow> P (n\<^sub>0 + k)\<close> for k n :: nat
proof (induct rule: nat_less_induct)
  fix n assume \<open>\<forall>m<n. P m\<close>
  show \<open>P n\<close>
  proof (cases \<open>n < k\<close>)
    from that(1) show \<open>n < k \<Longrightarrow> P n\<close> by blast
  next
    from \<open>\<forall>m<n. P m\<close> that(2)[rule_format, of \<open>n - k\<close>]
    show \<open>\<not> n < k \<Longrightarrow> P n\<close> by auto
  qed
qed

thm fix_ind fix_ind2 

lemma fix_ind_k [case_names admissibility base_k_steps step]:
  assumes adm : \<open>adm P\<close>
    and base_k_steps : \<open>\<forall>i<k. P (iterate i\<cdot>f\<cdot>\<bottom>)\<close>
    and step : \<open>\<And>X. (\<forall>i<k. P (iterate i\<cdot>f\<cdot>X)) \<Longrightarrow> P (iterate k\<cdot>f\<cdot>X)\<close>
  shows \<open>P (fix\<cdot>f)\<close>
proof (unfold fix_def2, rule admD [OF adm chain_iterate])
  show \<open>P (iterate i\<cdot>f\<cdot>\<bottom>)\<close> for i
  proof (induct i rule : nat_k_induct[of k])
    show \<open>\<forall>i<k. P (iterate i\<cdot>f\<cdot>\<bottom>)\<close> by (fact base_k_steps)
  next
    show \<open>\<forall>n\<^sub>0. (\<forall>i<k. P (iterate (n\<^sub>0 + i)\<cdot>f\<cdot>\<bottom>)) \<longrightarrow> P (iterate (n\<^sub>0 + k)\<cdot>f\<cdot>\<bottom>)\<close>
      by (metis add.commute iterate_iterate step)
  qed
qed


lemma nat_k_skip_induct [case_names lower_bound base_k step]:
  \<open>P n\<close> if \<open>1 \<le> k\<close> and \<open>\<forall>i<k. P i\<close> and \<open>\<forall>n\<^sub>0. P n\<^sub>0 \<longrightarrow> P (n\<^sub>0 + k)\<close> for k n :: nat
proof (induct n rule: nat_less_induct)
  fix n assume \<open>\<forall>m<n. P m\<close>
  show \<open>P n\<close>
  proof (cases \<open>n < k\<close>)
    from that(2) show \<open>n < k \<Longrightarrow> P n\<close> by blast
  next
    from \<open>\<forall>m<n. P m\<close> \<open>1 \<le> k\<close> that(3)[rule_format, of \<open>n - k\<close>]
    show \<open>\<not> n < k \<Longrightarrow> P n\<close> by auto
  qed
qed

lemma fix_ind_k_skip [case_names lower_bound admissibility base_k_steps step]:
  assumes k_1 : \<open>1 \<le> k\<close>
    and adm : \<open>adm P\<close>
    and base_k_steps : \<open>\<forall>i<k. P (iterate i\<cdot>f\<cdot>\<bottom>)\<close>
    and step : \<open>\<And>X. P X \<Longrightarrow> P (iterate k\<cdot>f\<cdot>X)\<close>
  shows \<open>P (fix\<cdot>f)\<close>
proof (unfold fix_def2, rule admD [OF adm chain_iterate])
  show \<open>P (iterate i\<cdot>f\<cdot>\<bottom>)\<close> for i
  proof (induct i rule : nat_k_skip_induct[of k])
    show \<open>1 \<le> k\<close> by (fact \<open>1 \<le> k\<close>)
  next
    show \<open>\<forall>i<k. P (iterate i\<cdot>f\<cdot>\<bottom>)\<close> by (fact base_k_steps)
  next
    show \<open>\<forall>n\<^sub>0. P (iterate n\<^sub>0\<cdot>f\<cdot>\<bottom>) \<longrightarrow> P (iterate (n\<^sub>0 + k)\<cdot>f\<cdot>\<bottom>)\<close>
      by (metis add.commute iterate_iterate step)
  qed
qed



section\<open>Parallel fixpoint-induction\<close>

lemma parallel_fix_ind_inc[case_names admissibility base_fst base_snd step]:
  assumes adm: \<open>adm (\<lambda>X. P (fst X) (snd X))\<close>
    and base_fst: \<open>\<And>Y. P \<bottom> Y\<close> and base_snd: \<open>\<And>X. P X \<bottom>\<close>
    and step: \<open>\<And>X Y. P X Y \<Longrightarrow> P (G\<cdot>X) Y \<Longrightarrow> P X (H\<cdot>Y) \<Longrightarrow> P (G\<cdot>X) (H\<cdot>Y)\<close>
  shows \<open>P (fix\<cdot>G) (fix\<cdot>H)\<close>
proof -
  from adm have adm': \<open>adm (case_prod P)\<close>
    unfolding split_def .
  have \<open>P (iterate i\<cdot>G\<cdot>\<bottom>) (iterate j\<cdot>H\<cdot>\<bottom>)\<close> for i j
  proof (induct \<open>i + j\<close> arbitrary: i j rule: nat_less_induct)
    case 1
    { fix i' j'
      assume i: \<open>i = Suc i'\<close> and j: \<open>j = Suc j'\<close>
      have \<open>P (iterate i'\<cdot>G\<cdot>\<bottom>) (iterate j'\<cdot>H\<cdot>\<bottom>)\<close>
        using "1.hyps" add_strict_mono i j by blast
      moreover have \<open>P (iterate i'\<cdot>G\<cdot>\<bottom>) (iterate j\<cdot>H\<cdot>\<bottom>)\<close>
        using "1.hyps" i by auto
      moreover have \<open>P (iterate i\<cdot>G\<cdot>\<bottom>) (iterate j'\<cdot>H\<cdot>\<bottom>)\<close>
        using "1.hyps" j by auto
      ultimately have ?case by (simp add: i j step)
    }
    thus ?case by (cases i; cases j; simp add: base_fst base_snd)
  qed
  hence \<open>case_prod P (iterate i\<cdot>G\<cdot>\<bottom>, iterate i\<cdot>H\<cdot>\<bottom>)\<close> for i by simp
  hence \<open>case_prod P (\<Squnion>i. (iterate i\<cdot>G\<cdot>\<bottom>, iterate i\<cdot>H\<cdot>\<bottom>))\<close>
    by - (rule admD [OF adm'], simp, assumption)
  hence \<open>P (\<Squnion>i. iterate i\<cdot>G\<cdot>\<bottom>) (\<Squnion>i. iterate i\<cdot>H\<cdot>\<bottom>)\<close>
    by (simp add: lub_Pair)  
  thus \<open>P (fix\<cdot>G) (fix\<cdot>H)\<close> by (simp add: fix_def2)
qed

(*<*)
end
  (*>*)