(***********************************************************************************
 * Copyright (c) University of Exeter, UK
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
 * SPDX-License-Identifier: BSD-3-Clause
 ***********************************************************************************)

chapter\<open>Lipschitz Continuity of Intervals\<close>

text\<open>An extension of of Lipschitz Continuity, developed for the Lipschitz Continuity of intervals.\<close>

theory
  Lipschitz_Interval_Extension
  imports
  Inclusion_Isotonicity
  "HOL-Analysis.Lipschitz"
  Interval_Utilities
begin

section \<open>Definition of Lipschitz Continuity on Intervals\<close>

text \<open>An interval extension F is said to be lipschitz in X if there is a constant L such that 
@{term \<open>w(F(X)) \<le> Lw(X)\<close>} for every @{term \<open>X \<subseteq> X\<close>}. Hence the width of 
@{term \<open>F(X)\<close>} approaches @{term \<open>0\<close>} at least linearly with the width of X.\<close>

definition lipschitzI_on\<^marker>\<open>tag important\<close> :: "'a::{zero,minus,preorder,times} \<Rightarrow> 'a interval set \<Rightarrow> ('a interval \<Rightarrow> 'a interval) \<Rightarrow> bool"
  where "lipschitzI_on C U F \<longleftrightarrow> (0 \<le> C \<and> (\<forall>x \<in> U. width (F x) \<le> C * width x))"


text \<open>The definition @{term "lipschitzI_on"} refers to definition 6.1 in\<^cite>\<open>"moore.ea:introduction:2009"\<close>\<close>

bundle lipschitzI_syntax begin
notation\<^marker>\<open>tag important\<close> lipschitzI_on ("_-lipschitzI'_on" [1000])
end
bundle no_lipschitzI_syntax begin
no_notation lipschitzI_on ("_-lipschitzI'_on" [1000])
end

unbundle lipschitzI_syntax

lemma lipschitzI_onI: "C-lipschitzI_on U F"
  if "\<And>x . x \<in> U \<Longrightarrow> width (F x) \<le> C * width x" "0 \<le> C"
  using that by (auto simp: lipschitzI_on_def)

lemma lipschitzI_onD:
  "width (F x) \<le> C * width x "
  if "C-lipschitzI_on U F" "x \<in> U"
  using that by (auto simp: lipschitzI_on_def)

lemma lipschitzI_on_nonneg:
  "0 \<le> C" if "C-lipschitzI_on U F"
  using that by (auto simp: lipschitzI_on_def)

lemma lipschitz_on_normD:
  "norm (width (F x)) \<le> C * norm (width x)"
  if "C-lipschitzI_on U F" "x \<in> U"
  using lipschitzI_onD[OF that]
  by (simp add: width_def dist_norm) 

lemma lipschitzI_on_mono: "L-lipschitzI_on D (F:: 'a::{linordered_ring} interval \<Rightarrow> 'a interval)" 
  if "M-lipschitzI_on E F" "M \<le> L" "D \<subseteq> E" 
  using that  diff_ge_0_iff_ge lower_le_upper 
   order_trans[OF _ mult_right_mono]
  unfolding lipschitzI_on_def width_def 
  by (metis (no_types, lifting) order_trans subsetD width_def)

lemmas lipschitzI_on_subset
 = lipschitzI_on_mono[OF _ _ order_refl]
  and lipschitzI_on_le = lipschitzI_on_mono[OF _ order_refl]

lemma lipschitzI_on_leI:
  "C-lipschitzI_on U F"
  if "\<And>x. x \<in> U \<Longrightarrow> width (F x) \<le> C * width x"
     "0 \<le> C"
  for F::"'a::{minus,preorder,times,zero} interval \<Rightarrow> 'a interval"
proof (rule lipschitzI_onI)
  fix x assume x: "x \<in> U"
  consider "upper x \<le> lower x" | "lower x \<le> upper x" 
    by simp
  then show "width (F x) \<le> C * width x"
  proof cases
    case 1
    then have "width (F x) \<le> C * width x"
      by (auto intro!: that x)
    then show ?thesis
      by (simp add: dist_commute)
  qed (auto intro!: that x)
qed fact

subsection\<open>Lipschitz Continuity of Operations\<close>

text \<open>Let F and G be inclusion isotonic interval extensions with @{term \<open>F\<close>} Lipschitz 
in @{term \<open>Y\<close>} and @{term \<open>G\<close>} Lipschitz in @{term \<open>X\<close>} 
and @{term \<open>G(X) \<subseteq> Y\<close>}. Then the composition @{term \<open>H(X) = F(G(X))\<close>} is 
Lipschitz in @{term \<open>X\<close>} and is inclusion isotonic\<close>

lemma lipschitzI_on_compose:
  fixes U :: \<open>'a::{linordered_ring} interval set\<close>
  assumes f: "C-lipschitzI_on U F" and g: "D-lipschitzI_on (F`U) G"
  shows "(D * C)-lipschitzI_on U (G o F)"
proof (rule lipschitzI_onI)
  show "D * C \<ge> 0" using lipschitzI_on_nonneg[OF f] lipschitzI_on_nonneg[OF g] by simp
  fix x assume H: "x \<in> U" 
  have "width (G(F x)) \<le> D * C * width x"
    using lipschitzI_onD[OF g] H assms 
    unfolding width_def lipschitzI_on_def apply simp  
    by (smt (verit, ccfv_SIG) mult.assoc mult_left_mono order_trans)
  then show "width ((G \<circ> F) x) \<le> D * C * width x"
    unfolding comp_def by simp
qed


text \<open>The definition @{thm "lipschitzI_on_compose"} refers to lemma 6.3 in
\<^cite>\<open>"moore.ea:introduction:2009"\<close>\<close>

lemma lipschitzI_on_compose2:
  fixes U :: \<open>'a::{linordered_ring} interval set\<close>
  assumes F: "C-lipschitzI_on U F" and G: "D-lipschitzI_on (F`U) G"
  shows "(D * C)-lipschitzI_on U (\<lambda>x. G (F x))"
  using lipschitzI_on_compose F G unfolding o_def by blast

lemma lipschitzI_on_cong:
  "C-lipschitzI_on U G \<longleftrightarrow> D-lipschitzI_on V F"
  if "C = D" "U = V" "\<And>x. x \<in> V \<Longrightarrow> G x = F x"
  using that by (auto simp: lipschitzI_on_def)

lemma lipschitzI_on_transform:
  "C-lipschitzI_on U G"
  if "C-lipschitzI_on U F"
    "\<And>x. x \<in> U \<Longrightarrow> G x = F x"
  using that
  unfolding lipschitzI_on_def width_def
  by simp

lemma lipschitz_on_empty_iff: "C-lipschitzI_on {} f \<longleftrightarrow> C \<ge> 0"
  by (auto simp: lipschitzI_on_def)

lemma lipschitz_on_id: "(1::real)-lipschitzI_on U (\<lambda>x. x)"
  by (auto simp: lipschitzI_on_def)

lemma lipschitz_on_constant: 
  assumes \<open>lower c = upper c\<close>
  shows "(0::real)-lipschitzI_on U (\<lambda>x. c)"
  using assms by (auto simp: lipschitzI_on_def width_def)

lemma lipschitzI_on_mult: 
  fixes X :: "'a::{linordered_idom}"
  assumes "lipschitzI_on C U f"
  and "1 \<le> X"
shows "lipschitzI_on (X*C) U f"
  using assms interval_width_positive lower_le_upper mult_le_cancel_right1
  unfolding lipschitzI_on_def width_def  
 by (smt (verit) diff_ge_0_iff_ge linorder_not_le mult.assoc order_trans)  


subsection "Interval bounds on reals"

lemma bounded_image_real:
  fixes X :: "real interval" and f :: "real \<Rightarrow> real"
  assumes "\<forall>x\<in>{lower X..upper X}. 
          f (lower X) - L * (upper X - lower X) \<le> f x \<and> f x \<le> f (lower X) + L * (upper X - lower X)"
  shows "\<exists>x e. \<forall>y\<in>f ` {lower X..upper X}. dist x y \<le> e"
proof -
  let ?x = "f (lower X)"
  let ?e = "L * (upper X - lower X)"
  have "\<forall>y\<in>f ` {lower X..upper X}. dist ?x y \<le> ?e"
  proof
    fix y assume "y \<in> f ` {lower X..upper X}"
    then obtain x where "x \<in> {lower X..upper X}" and "y = f x" by auto
    then have "?x - ?e \<le> y \<and> y \<le> ?x + ?e" using assms by auto
    then show "dist ?x y \<le> ?e" 
      unfolding dist_real_def by force 
  qed
  then show ?thesis by auto
qed

lemma lipschitz_bounded_image_real:
  fixes X :: "real set" and f :: "real \<Rightarrow> real"
  assumes "bounded X" and "L-lipschitz_on X f"
  shows "bounded (f ` X)"
  using assms(1) assms(2) bounded_uniformly_continuous_image lipschitz_on_uniformly_continuous by blast 

lemma inf_le_sup_image_real: 
  fixes X :: "real interval" and f :: "real \<Rightarrow> real"
  assumes "L-lipschitz_on (set_of X) f"
  shows  "Inf (f ` set_of X) \<le> Sup (f ` set_of X)"
proof -
  have "bounded (f ` set_of X)"
    using assms bounded_set_of lipschitz_bounded_image_real by blast 
  then have "bdd_below (f ` set_of X)" and "bdd_above (f ` set_of X)" 
    using bounded_imp_bdd_below bounded_imp_bdd_above by auto
  then have "Inf (f ` set_of X) \<le> Sup (f ` set_of X)"
    by (metis set_of_nonempty cInf_le_cSup empty_is_image) 
  then show ?thesis by simp
qed

lemma sup_image_le_real:
  fixes f :: "real \<Rightarrow> real" and F :: "real interval \<Rightarrow> real interval" and X :: "real interval"
  assumes "f ` set_of X \<subseteq> set_of (F X)"
    and "L-lipschitz_on (set_of X) f"
  shows "Sup (f ` set_of X) \<le> Sup (set_of (F X))"
proof -
  have a0: "bounded (f ` set_of X)" 
    using lipschitz_bounded_image_real[of "set_of X"] assms bounded_set_of[of "X"] by simp
  have a1: "bdd_above (f ` set_of X)" 
    using assms
    using a0 bounded_imp_bdd_above by presburger  
  then have a2: "\<forall>y\<in>f ` set_of X. y \<le> Sup (f ` set_of X)" using bounded_has_Sup(1) a0
    by blast  
  then have a3: "Sup (f ` set_of X) \<le> Sup (set_of (F X))" 
    using set_of_nonempty assms a0 a1 a2 atLeastAtMost_iff closed_real_atLeastAtMost closed_subset_contains_Sup empty_is_image set_of_eq sup_set_of
    by metis 
  then show ?thesis by simp
qed

lemma inf_image_le_real:
  fixes f :: "real \<Rightarrow> real" and F :: "real interval \<Rightarrow> real interval" and X :: "real interval"
  assumes "f ` set_of X \<subseteq> set_of (F X)"
    and "L-lipschitz_on (set_of X) f"
  shows "Inf (set_of (F X)) \<le> Inf (f ` (set_of X))"
proof -
  have a0: "bounded (f ` set_of X)" 
    using lipschitz_bounded_image_real[of "set_of X"] assms bounded_set_of[of "X"] by simp
  have a1: "bdd_above (f ` set_of X)" 
    using assms 
    by (metis atLeastAtMost_iff bdd_above.unfold set_of_eq subset_eq)
  then have a2: "\<forall>y\<in>f ` set_of X. y \<ge> Inf (f ` set_of X)" 
    using bounded_has_Inf(1) a0
    by blast  
  then have a3: "Inf (set_of (F X)) \<le> Inf (f ` (set_of X))" using assms
    by (metis set_of_nonempty a0 bounded_imp_bdd_below closed_real_atLeastAtMost closed_subset_contains_Inf empty_is_image in_bounds inf_set_of set_of_eq)
  then show ?thesis by simp
qed

end
