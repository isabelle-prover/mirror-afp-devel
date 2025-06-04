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



section \<open>Functions\<close>

(*<*)
theory Fun_Ultrametric_Restriction_Spaces
  imports Ultrametric_Restriction_Spaces Banach_Theorem_Extension
begin
  (*>*)


subsection \<open>Restriction Space\<close>


instantiation \<open>fun\<close> :: (type, restriction_\<sigma>) restriction_\<sigma>
begin

definition restriction_\<sigma>_fun :: \<open>('a \<Rightarrow> 'b) itself \<Rightarrow> nat \<Rightarrow> real\<close>
  where \<open>restriction_\<sigma>_fun _ \<equiv> restriction_\<sigma> TYPE('b)\<close>

instance by intro_classes

end

instantiation \<open>fun\<close> :: (type, non_decseq_restriction_space) non_decseq_restriction_space
begin

definition dist_fun :: \<open>['a \<Rightarrow> 'b, 'a \<Rightarrow> 'b] \<Rightarrow> real\<close>
  where \<open>dist_fun f g \<equiv> INF n \<in> restriction_related_set f g. restriction_\<sigma> TYPE('a \<Rightarrow> 'b) n\<close>

definition uniformity_fun :: \<open>(('a \<Rightarrow> 'b) \<times> ('a \<Rightarrow> 'b)) filter\<close>
  where \<open>uniformity_fun \<equiv> INF e\<in>{0 <..}. principal {(x, y). dist x y < e}\<close>

definition open_fun :: \<open>('a \<Rightarrow> 'b) set \<Rightarrow> bool\<close>
  where \<open>open_fun U \<equiv> \<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity\<close>

instance by intro_classes
    (simp_all add: restriction_\<sigma>_fun_def dist_fun_def open_fun_def
      uniformity_fun_def restriction_\<sigma>_tendsto_zero)

end


instance \<open>fun\<close> :: (type, decseq_restriction_space) decseq_restriction_space
  by intro_classes (simp add: restriction_\<sigma>_fun_def decseq_restriction_\<sigma>)

instance \<open>fun\<close> :: (type, strict_decseq_restriction_space) strict_decseq_restriction_space
  by intro_classes
    (simp add: restriction_\<sigma>_fun_def strict_decseq_restriction_\<sigma>)


instantiation \<open>fun\<close> :: (type, restriction_\<delta>) restriction_\<delta>
begin

definition restriction_\<delta>_fun :: \<open>('a \<Rightarrow> 'b) itself \<Rightarrow> real\<close>
  where \<open>restriction_\<delta>_fun _ \<equiv> restriction_\<delta> TYPE('b)\<close>

instance by intro_classes (simp_all add: restriction_\<delta>_fun_def)

end


instance \<open>fun\<close> :: (type, at_least_geometric_restriction_space) at_least_geometric_restriction_space
proof intro_classes
  show \<open>0 < restriction_\<sigma> TYPE('a \<Rightarrow> 'b) n\<close> for n
    by (simp add: restriction_\<sigma>_fun_def)
next
  show \<open>restriction_\<sigma> TYPE('a \<Rightarrow> 'b) (Suc n)
        \<le> restriction_\<delta> TYPE('a \<Rightarrow> 'b) * restriction_\<sigma> TYPE('a \<Rightarrow> 'b) n\<close> for n
    by (simp add: restriction_\<sigma>_le restriction_\<sigma>_fun_def restriction_\<delta>_fun_def)
next
  show \<open>dist f g = Inf (restriction_\<sigma>_related_set f g)\<close> for f g :: \<open>'a \<Rightarrow> 'b\<close>
    by (simp add: dist_fun_def)
qed

instance \<open>fun\<close> :: (type, geometric_restriction_space) geometric_restriction_space
proof intro_classes
  show \<open>restriction_\<sigma> TYPE('a \<Rightarrow> 'b) n = restriction_\<delta> TYPE('a \<Rightarrow> 'b) ^ n\<close> for n
    by (simp add: restriction_\<sigma>_fun_def restriction_\<sigma>_is restriction_\<delta>_fun_def)
next
  show \<open>dist f g = Inf (restriction_\<sigma>_related_set f g)\<close> for f g :: \<open>'a \<Rightarrow> 'b\<close>
    by (simp add: dist_fun_def)
qed


lemma dist_image_le_dist_fun : \<open>dist (f x) (g x) \<le> dist f g\<close>
  for f g :: \<open>'a \<Rightarrow> 'b :: non_decseq_restriction_space\<close>
proof (unfold dist_restriction_is, rule cInf_superset_mono)
  show \<open>restriction_\<sigma>_related_set f g \<noteq> {}\<close> by simp
next
  show \<open>bdd_below (restriction_\<sigma>_related_set (f x) (g x))\<close>
    by (simp add: bounded_imp_bdd_below bounded_restriction_\<sigma>_related_set)
next
  show \<open>restriction_\<sigma>_related_set f g \<subseteq> restriction_\<sigma>_related_set (f x) (g x)\<close>
    unfolding restriction_fun_def restriction_\<sigma>_fun_def 
    by (simp add: image_def subset_iff) metis
qed


lemma Sup_dist_image_le_dist_fun : \<open>(SUP x. dist (f x) (g x)) \<le> dist f g\<close>
  for f g :: \<open>'a \<Rightarrow> 'b :: non_decseq_restriction_space\<close>
  by (simp add: dist_image_le_dist_fun cSUP_least)
    \<comment> \<open>The other inequality will require the additional assumption \<^const>\<open>decseq\<close>.\<close>



context fixes f g :: \<open>'a \<Rightarrow> 'b :: decseq_restriction_space\<close> begin

lemma reached_dist_fun : \<open>\<exists>x. dist f g = dist (f x) (g x)\<close>
proof (cases \<open>f = g\<close>)
  show \<open>f = g \<Longrightarrow> \<exists>x. dist f g = dist (f x) (g x)\<close> by simp
next
  assume \<open>f \<noteq> g\<close>
  let ?n = \<open>Sup (restriction_related_set f g)\<close>
  from not_eq_imp_dist_restriction_is_restriction_\<sigma>_Sup_restriction_eq_simplified(2, 3)[OF \<open>f \<noteq> g\<close>]
  obtain x where \<open>\<forall>m\<le>?n. f x \<down> m = g x \<down> m\<close> \<open>f x \<down> Suc ?n \<noteq> g x \<down> Suc ?n\<close>
    unfolding restriction_fun_def by (meson lessI)
  hence \<open>dist (f x) (g x) = restriction_\<sigma> TYPE('b) ?n\<close>
    by (metis (no_types, lifting) le_neq_implies_less not_less_eq_eq
        not_eq_imp_dist_restriction_is_restriction_\<sigma>_Sup_restriction_eq_simplified)
  with not_eq_imp_dist_restriction_is_restriction_\<sigma>_Sup_restriction_eq_simplified(1)
    [OF \<open>f \<noteq> g\<close>, unfolded restriction_\<sigma>_fun_def]
  have \<open>dist f g = dist (f x) (g x)\<close> by simp
  thus \<open>\<exists>x. dist f g = dist (f x) (g x)\<close> ..
qed


lemma dist_fun_eq_Sup_dist_image : \<open>dist f g = (SUP x. dist (f x) (g x))\<close>
proof (rule order_antisym)
  show \<open>(SUP x. dist (f x) (g x)) \<le> dist f g\<close> by (fact Sup_dist_image_le_dist_fun)
next
  from reached_dist_fun obtain x where \<open>dist f g = dist (f x) (g x)\<close> ..
  thus \<open>dist f g \<le> (SUP x. dist (f x) (g x))\<close>
  proof (rule ord_eq_le_trans)
    show \<open>dist (f x) (g x) \<le> (SUP x. dist (f x) (g x))\<close>
    proof (rule cSup_upper)
      show \<open>dist (f x) (g x) \<in> range (\<lambda>x. dist (f x) (g x))\<close> by simp
    next
      show \<open>bdd_above (range (\<lambda>x. dist (f x) (g x)))\<close>
        by (rule bdd_aboveI[of _ \<open>dist f g\<close>]) (auto intro: dist_image_le_dist_fun)
    qed
  qed
qed


lemma fun_restriction_space_Sup_properties :
  \<open>dist (f x) (g x) \<le> dist f g\<close>
  \<open>(\<And>x. dist (f x) (g x) \<le> b) \<Longrightarrow> dist f g \<le> b\<close>
  by (use reached_dist_fun in \<open>auto simp add: dist_image_le_dist_fun\<close>)


end


subsection \<open>Completeness\<close>

text \<open>Actually we can obtain even better: when the instance \<^typ>\<open>'b\<close> of
      \<^class>\<open>decseq_restriction_space\<close> is also an instance of \<^class>\<open>complete_space\<close>,
      the type \<^typ>\<open>'a \<Rightarrow> 'b\<close> is an instance of \<^class>\<open>complete_space\<close>.\<close>

text \<open>This is because when \<^typ>\<open>'b\<close> is an instance of \<^class>\<open>decseq_restriction_space\<close>
      (and not only \<^class>\<open>non_decseq_restriction_space\<close>) the distance between two functions
      is reached (see @{thm reached_dist_fun}).\<close>



text \<open>The only remaining thing is to prove that completeness is preserved on higher-order.\<close>

instance \<open>fun\<close> :: (type, complete_decseq_restriction_space) complete_decseq_restriction_space
  by intro_classes (fact restriction_chain_imp_restriction_convergent)

instance \<open>fun\<close> :: (type, complete_strict_decseq_restriction_space) complete_strict_decseq_restriction_space
  by intro_classes (fact restriction_chain_imp_restriction_convergent)

instance \<open>fun\<close> :: (type, complete_at_least_geometric_restriction_space) complete_at_least_geometric_restriction_space
  by intro_classes (fact restriction_chain_imp_restriction_convergent)

instance \<open>fun\<close> :: (type, complete_geometric_restriction_space) complete_geometric_restriction_space
  by intro_classes (fact restriction_chain_imp_restriction_convergent)



subsection \<open>Kind of Extensionality\<close>

context fixes f :: \<open>['a :: metric_space, 'b :: type] \<Rightarrow>
                    'c :: decseq_restriction_space\<close> begin

lemma lipschitz_with_simplification:
  \<open>lipschitz_with f \<alpha> \<longleftrightarrow> (\<forall>y. lipschitz_with (\<lambda>x. f x y) \<alpha>)\<close>
proof (intro iffI allI)
  fix y assume assm : \<open>lipschitz_with f \<alpha>\<close>
  show \<open>lipschitz_with (\<lambda>x. f x y) \<alpha>\<close>
  proof (rule lipschitz_withI)
    from assm[THEN lipschitz_withD1] show \<open>0 \<le> \<alpha>\<close> .
  next
    show \<open>dist (f x1 y) (f x2 y) \<le> \<alpha> * dist x1 x2\<close> for x1 x2
      by (rule order_trans[OF _ assm[THEN lipschitz_withD2]])
        (simp add: dist_image_le_dist_fun)
  qed
next
  assume assm : \<open>\<forall>y. lipschitz_with (\<lambda>x. f x y) \<alpha>\<close>
  show \<open>lipschitz_with f \<alpha>\<close>
  proof (rule lipschitz_withI)
    from assm[rule_format, THEN lipschitz_withD1] show \<open>0 \<le> \<alpha>\<close> .
  next
    fix x1 x2
    obtain y where \<open>dist (f x1) (f x2) = dist (f x1 y) (f x2 y)\<close>
      by (meson reached_dist_fun)
    also have \<open>\<dots> \<le> \<alpha> * dist x1 x2\<close> by (rule assm[rule_format, THEN lipschitz_withD2])
    finally show \<open>dist (f x1) (f x2) \<le> \<alpha> * dist x1 x2\<close> .
  qed
qed


lemma non_expanding_simplification :
  \<open>non_expanding f \<longleftrightarrow> (\<forall>y. non_expanding (\<lambda>x. f x y))\<close>
  by (metis lipschitz_with_simplification non_expanding_on_def)


lemma contraction_with_simplification:
  \<open>contraction_with f \<alpha> \<longleftrightarrow> (\<forall>y. contraction_with (\<lambda>x. f x y) \<alpha>)\<close>
  by (metis contraction_with_on_def lipschitz_with_simplification)


end

(*<*)
end
  (*>*)
