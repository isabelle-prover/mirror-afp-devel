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


section \<open>Formal power Series\<close>

(*<*)
theory RS_Formal_Power_Series
  imports Restriction_Spaces "HOL-Analysis.FPS_Convergence"
begin
  (*>*)

instantiation fps ::("{comm_ring_1}") restriction_space begin
definition restriction_fps :: "'a fps \<Rightarrow> nat \<Rightarrow> 'a fps"  
  where \<open>restriction_fps a n \<equiv> \<Sum>i<n. fps_const (fps_nth a i)*fps_X^i\<close>

lemma intersection_equality:\<open>(n::nat) \<le> m \<Longrightarrow> {..<m} \<inter> {i. i < n} = {i. i<n}\<close>
  by auto

lemma exist_noneq:\<open>x \<noteq> y \<Longrightarrow>
           \<exists>n. (\<Sum>i\<in>{x. x < n}. fps_const (fps_nth x i) * fps_X ^ i) \<noteq>
               (\<Sum>i\<in>{x. x < n}. fps_const (fps_nth y i) * fps_X ^ i)\<close> for x y::\<open>'a fps\<close>
proof -
  assume \<open>x\<noteq>y\<close>
  then have \<open>\<exists>n. (n = (LEAST n. fps_nth x n \<noteq> fps_nth y n))\<close> 
    using fps_nth_inject by blast
  then obtain n where \<open> (n = (LEAST n. fps_nth x n \<noteq> fps_nth y n))\<close> by blast
  then have \<open>\<forall>i<n. fps_nth x i = fps_nth y i\<close>
    using not_less_Least by blast
  then have f0:\<open>(\<Sum>i<n. fps_const (fps_nth x i) * fps_X ^ i) = (\<Sum>i<n. fps_const (fps_nth y i) * fps_X ^ i)\<close>
    by(auto)
  have rule:\<open>a\<noteq>c \<Longrightarrow> a+b \<noteq> c+b\<close> for a b c::"'a fps"
    unfolding fps_plus_def using fps_ext 
    by(auto simp:fun_eq_iff fps_ext Abs_fps_inverse fps_nth_inverse Abs_fps_inject) 
  have \<open>fps_nth x n \<noteq> fps_nth y n\<close> 
    by (metis (mono_tags, lifting) LeastI_ex \<open>n = (LEAST n. fps_nth x n \<noteq> fps_nth y n)\<close> \<open>x \<noteq> y\<close> fps_ext)
  then have \<open> (\<Sum>i<n. fps_const (fps_nth x i) * fps_X ^ i) + fps_const (fps_nth x n) * fps_X ^ n \<noteq>
    (\<Sum>i<n. fps_const (fps_nth y i) * fps_X ^ i) + fps_const (fps_nth y n) * fps_X ^ n\<close>
    by (metis (no_types, lifting) f0 add_left_imp_eq fps_nth_fps_const fps_shift_times_fps_X_power') 
  moreover have \<open> (\<Sum>i\<in>{x. x < Suc n}. fps_const (fps_nth z i) * fps_X ^ i) 
= (\<Sum>i<n. fps_const (fps_nth z i) * fps_X ^ i) + fps_const (fps_nth z n) * fps_X ^ n\<close> for z::"'a fps"
  proof -
    have "\<forall>n. {..<n::nat} = {na. na < n}"
      by (simp add: lessThan_def)
    then show ?thesis
      using sum.lessThan_Suc by auto
  qed
  ultimately show \<open>\<exists>n. (\<Sum>i\<in>{x. x < n}. fps_const (fps_nth x i) * fps_X ^ i) \<noteq>
               (\<Sum>i\<in>{x. x < n}. fps_const (fps_nth y i) * fps_X ^ i)\<close>
    by(auto intro: exI[where x=\<open>Suc n\<close>]) 
qed


instance
  using intersection_equality exist_noneq 
  by intro_classes
    (auto cong: if_cong simp add:
     Collect_mono Int_absorb2 restriction_fps_def fps_sum_nth
     if_distrib[where f=fps_const]  if_distrib[where f=\<open>\<lambda>x. a * x\<close> for a]
     if_distrib[where f=\<open>\<lambda>x. x * a\<close> for a] lessThan_def sum.If_cases min_def)

end                                                           

lemma fps_sum_rep_nthb: "fps_nth (\<Sum>i<m. fps_const(a i)*fps_X^i) n = (if n < m then a n else 0)"
  by (simp add: fps_sum_nth if_distrib cong del: if_weak_cong)

lemma restriction_eq_iff :\<open>a\<down>n = b\<down>n \<longleftrightarrow> (\<forall>i<n. fps_nth a i = fps_nth b i)\<close>
  by (auto simp:restriction_fps_def) 
    (metis (full_types) fps_sum_rep_nthb)


lemma restriction_eqI :
  \<open>(\<And>i. i < n \<Longrightarrow> fps_nth x i = fps_nth y i) \<Longrightarrow> x \<down> n = y \<down> n\<close>
  by (simp add: restriction_eq_iff)

lemma restriction_eqI' :
  \<open>(\<And>i. i \<le> n \<Longrightarrow> fps_nth x i = fps_nth y i) \<Longrightarrow> x \<down> n = y \<down> n\<close>
  by (simp add: restriction_eq_iff)

instantiation fps :: (comm_ring_1) complete_restriction_space 
begin
instance
proof (intro_classes, rule restriction_convergentI)
  fix \<sigma> :: \<open>nat \<Rightarrow>'a fps\<close> assume h:\<open>restriction_chain \<sigma>\<close>
  have h':\<open>\<forall>n. (\<Sum>i<n. fps_const (fps_nth (\<sigma> (Suc n)) i) * fps_X ^ i) = \<sigma> n\<close>
    using h unfolding restriction_chain_def restriction_fps_def by auto
  let ?\<Sigma> = \<open>Abs_fps (\<lambda>n. fps_nth (\<sigma> (Suc n)) n)\<close>
  have \<open>?\<Sigma> \<down> (n) = \<sigma> n\<close> for n
  proof (subst restricted_restriction_chain_is[OF \<open>restriction_chain \<sigma>\<close>, symmetric],
      rule restriction_eqI)
    fix i assume \<open>i < n\<close> 
    then have \<open>i \<le> n\<close> by auto
    from restriction_chain_def_ter
      [THEN iffD1, OF \<open>restriction_chain \<sigma>\<close>, rule_format, OF \<open>i \<le> n\<close>]
    show \<open>fps_nth (Abs_fps (\<lambda>n. fps_nth (\<sigma> (Suc n)) n)) i = fps_nth (\<sigma> n) i\<close>
      by (subst Abs_fps_inverse, use Abs_fps_inject restriction_fps_def in blast)
        (smt (verit, ccfv_threshold) Suc_leI \<open>i < n\<close> h le_refl lessI restriction_eq_iff 
          restriction_chain_def restriction_chain_def_ter)     
  qed
  thus \<open>restriction_chain \<sigma> \<Longrightarrow> \<sigma> \<midarrow>\<down>\<rightarrow> ?\<Sigma>\<close> 
  proof -
    have "(\<down>) (Abs_fps (\<lambda>n. fps_nth (\<sigma> (Suc n)) n)) = \<sigma>"
      using \<open>\<And>n. Abs_fps (\<lambda>n. fps_nth (\<sigma> (Suc n)) n) \<down> n = \<sigma> n\<close> by force
    then show ?thesis
      by (metis restriction_tendsto_restrictions)
  qed
qed

end

(*<*)
end
  (*>*)