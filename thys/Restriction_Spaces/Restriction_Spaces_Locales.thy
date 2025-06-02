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


section \<open>Locales factorizing the proof Work\<close>

(*<*)
theory Restriction_Spaces_Locales
  imports Main
begin
  (*>*)

named_theorems restriction_shift_simpset
named_theorems restriction_shift_introset \<comment> \<open>Useful for future automation.\<close>


text \<open>In order to factorize the proof work, we first work with locales and then with classes.\<close>


subsection \<open>Basic Notions for Restriction\<close>

locale Restriction =
  fixes restriction :: \<open>['a, nat] \<Rightarrow> 'a\<close>  (infixl \<open>\<down>\<close> 60)
    and relation    :: \<open>['a, 'a] \<Rightarrow> bool\<close> (infixl \<open>\<lessapprox>\<close> 50)
  assumes restriction_restriction [simp] : \<open>x \<down> n \<down> m = x \<down> min n m\<close>
begin


abbreviation restriction_related_set  :: \<open>'a \<Rightarrow> 'a \<Rightarrow> nat set\<close>
  where \<open>restriction_related_set x y  \<equiv> {n. x \<down> n \<lessapprox> y \<down> n}\<close>

abbreviation restriction_not_related_set :: \<open>'a \<Rightarrow> 'a \<Rightarrow> nat set\<close>
  where \<open>restriction_not_related_set x y \<equiv> {n. \<not> x \<down> n \<lessapprox> y \<down> n}\<close>

lemma restriction_related_set_Un_restriction_not_related_set :
  \<open>restriction_related_set x y \<union> restriction_not_related_set x y = UNIV\<close> by blast

lemma disjoint_restriction_related_set_restriction_not_related_set :
  \<open>restriction_related_set x y \<inter> restriction_not_related_set x y = {}\<close> by blast

lemma \<open>bdd_below (restriction_related_set x y)\<close> by (fact bdd_below_bot)

lemma \<open>bdd_below (restriction_not_related_set x y)\<close> by (fact bdd_below_bot)


end


locale PreorderRestrictionSpace = Restriction +
  assumes restriction_0_related   [simp] : \<open>x \<down> 0 \<lessapprox> y \<down> 0\<close>
    and mono_restriction_related   : \<open>  x \<lessapprox> y \<Longrightarrow> x \<down> n \<lessapprox> y \<down> n\<close>
    and ex_not_restriction_related : \<open>\<not> x \<lessapprox> y \<Longrightarrow> \<exists>n. \<not> x \<down> n \<lessapprox> y \<down> n\<close>
    and related_trans : \<open>x \<lessapprox> y \<Longrightarrow> y \<lessapprox> z \<Longrightarrow> x \<lessapprox> z\<close>
begin

lemma exists_restriction_related [simp] : \<open>\<exists>n. x \<down> n \<lessapprox> y \<down> n\<close>
  using restriction_0_related by blast

lemma all_restriction_related_iff_related : \<open>(\<forall>n. x \<down> n \<lessapprox> y \<down> n) \<longleftrightarrow> x \<lessapprox> y\<close>
  using mono_restriction_related ex_not_restriction_related by blast

lemma restriction_related_le : \<open>x \<down> n \<lessapprox> y \<down> n\<close> if \<open>n \<le> m\<close> and \<open>x \<down> m \<lessapprox> y \<down> m\<close>
proof -
  from mono_restriction_related[OF \<open>x \<down> m \<lessapprox> y \<down> m\<close>] have \<open>x \<down> m \<down> n \<lessapprox> y \<down> m \<down> n\<close> .
  also have \<open>(\<lambda>x. x \<down> m \<down> n) = (\<lambda>x. x \<down> n)\<close> by (simp add: \<open>n \<le> m\<close>)
  finally show \<open>x \<down> n \<lessapprox> y \<down> n\<close> .
qed

corollary restriction_related_pred : \<open>x \<down> Suc n \<lessapprox> y \<down> Suc n \<Longrightarrow> x \<down> n \<lessapprox> y \<down> n\<close>
  by (metis le_add2 plus_1_eq_Suc restriction_related_le)

lemma all_ge_restriction_related_iff_related : \<open>(\<forall>n\<ge>m. x \<down> n \<lessapprox> y \<down> n) \<longleftrightarrow> x \<lessapprox> y\<close>
  by (metis all_restriction_related_iff_related nle_le restriction_related_le)


lemma take_lemma_restriction : \<open>x \<lessapprox> y\<close>
  if \<open>\<And>n. \<lbrakk>\<And>k. k \<le> n \<Longrightarrow> x \<down> k \<lessapprox> y \<down> k\<rbrakk> \<Longrightarrow> x \<down> Suc n \<lessapprox> y \<down> Suc n\<close>
proof (subst all_restriction_related_iff_related[symmetric], intro allI)
  show \<open>x \<down> n \<lessapprox> y \<down> n\<close> for n
    by (induct n rule: full_nat_induct)
      (metis not_less_eq_eq restriction_0_related restriction_related_le that zero_induct)
qed

lemma ex_not_restriction_related_optimized :
  \<open>\<exists>!n. \<not> x \<down> Suc n \<lessapprox> y \<down> Suc n \<and> (\<forall>m\<le>n. x \<down> m \<lessapprox> y \<down> m)\<close> if \<open>\<not> x \<lessapprox> y\<close>
proof (rule ex1I)
  let ?S = \<open>{n. \<not> x \<down> Suc n \<lessapprox> y \<down> Suc n \<and> (\<forall>m\<le>n. x \<down> m \<lessapprox> y \<down> m)}\<close>
  let ?n = \<open>Inf {n. \<not> x \<down> Suc n \<lessapprox> y \<down> Suc n \<and> (\<forall>m\<le>n. x \<down> m \<lessapprox> y \<down> m)}\<close>
  from restriction_related_le[of _ _ x y] take_lemma_restriction[of x y] \<open>\<not> x \<lessapprox> y\<close>
  have \<open>?S \<noteq> {}\<close> by auto
  from Inf_nat_def1[OF this] have \<open>?n \<in> ?S\<close> .
  thus \<open>\<not> x \<down> Suc ?n \<lessapprox> y \<down> Suc ?n \<and> (\<forall>m\<le>?n. x \<down> m \<lessapprox> y \<down> m)\<close> by blast
  thus \<open>\<not> x \<down> Suc n \<lessapprox> y \<down> Suc n \<and> (\<forall>m\<le>n. x \<down> m \<lessapprox> y \<down> m) \<Longrightarrow> n = ?n\<close> for n
    by (meson not_less_eq_eq order_antisym_conv)
qed




lemma nonempty_restriction_related_set : \<open>restriction_related_set x y \<noteq> {}\<close>
  using restriction_0_related by blast

lemma non_UNIV_restriction_not_related_set : \<open>restriction_not_related_set x y \<noteq> UNIV\<close>
  using restriction_0_related by blast

lemma UNIV_restriction_related_set_iff : \<open>restriction_related_set x y = UNIV \<longleftrightarrow> x \<lessapprox> y\<close>
  using all_restriction_related_iff_related by blast

lemma empty_restriction_not_related_set_iff: \<open>restriction_not_related_set x y = {} \<longleftrightarrow> x \<lessapprox> y\<close>
  by (simp add: all_restriction_related_iff_related)


lemma finite_restriction_related_set_iff :
  \<open>finite (restriction_related_set x y) \<longleftrightarrow> \<not> x \<lessapprox> y\<close>
proof (rule iffI)
  assume \<open>finite (restriction_related_set x y)\<close>
  obtain n where \<open>\<not> x \<down> n \<lessapprox> y \<down> n\<close> 
    using \<open>finite (restriction_related_set x y)\<close> by fastforce
  with mono_restriction_related show \<open>\<not> x \<lessapprox> y\<close> by blast
next
  assume \<open>\<not> x \<lessapprox> y\<close>
  then obtain n where \<open>\<forall>m>n. \<not> x \<down> m \<lessapprox> y \<down> m\<close>
    by (meson all_restriction_related_iff_related less_le_not_le restriction_related_le)
  hence \<open>restriction_related_set x y \<subseteq> {0..n}\<close>
    by (simp add: subset_iff) (meson linorder_not_le)
  thus \<open>finite (restriction_related_set x y)\<close>
    by (simp add: subset_eq_atLeast0_atMost_finite)
qed

lemma infinite_restriction_not_related_set_iff :
  \<open>infinite (restriction_not_related_set x y) \<longleftrightarrow> \<not> x \<lessapprox> y\<close>
  by (metis empty_restriction_not_related_set_iff finite_restriction_related_set_iff
      finite.emptyI finite_Collect_not infinite_UNIV_char_0)

lemma bdd_above_restriction_related_set_iff :
  \<open>bdd_above (restriction_related_set x y) \<longleftrightarrow> \<not> x \<lessapprox> y\<close>
  by (simp add: bdd_above_nat finite_restriction_related_set_iff)



context fixes x y assumes \<open>\<not> x \<lessapprox> y\<close> begin

lemma Sup_in_restriction_related_set :
  \<open>Sup (restriction_related_set x y) \<in> restriction_related_set x y\<close>
  using Max_in[OF finite_restriction_related_set_iff[THEN iffD2, OF \<open>\<not> x \<lessapprox> y\<close>]
      nonempty_restriction_related_set]
    cSup_eq_Max[OF finite_restriction_related_set_iff[THEN iffD2, OF \<open>\<not> x \<lessapprox> y\<close>]
      nonempty_restriction_related_set]
  by argo

lemma Inf_in_restriction_not_related_set :
  \<open>Inf (restriction_not_related_set x y) \<in> restriction_not_related_set x y\<close>
  by (metis \<open>\<not> x \<lessapprox> y\<close> Inf_nat_def1 finite.emptyI infinite_restriction_not_related_set_iff)

lemma Inf_restriction_not_related_set_eq_Suc_Sup_restriction_related_set :
  \<open>Inf (restriction_not_related_set x y) = Suc (Sup (restriction_related_set x y))\<close>
proof -
  let ?S_eq  = \<open>restriction_related_set  x y\<close>
  let ?S_neq = \<open>restriction_not_related_set x y\<close>
  from Inf_in_restriction_not_related_set have \<open>Inf ?S_neq \<in> ?S_neq\<close> by blast
  from Sup_in_restriction_related_set have \<open>Sup ?S_eq \<in> ?S_eq\<close> by blast
  hence \<open>Suc (Sup ?S_eq) \<notin> ?S_eq\<close>
    by (metis Suc_n_not_le_n \<open>\<not> x \<lessapprox> y\<close> bdd_above_restriction_related_set_iff cSup_upper)
  with restriction_related_set_Un_restriction_not_related_set
  have \<open>Suc (Sup ?S_eq) \<in> ?S_neq\<close> by auto
  show \<open>Inf ?S_neq = Suc (Sup ?S_eq)\<close>
  proof (rule order_antisym)
    show \<open>Inf ?S_neq \<le> Suc (Sup ?S_eq)\<close>
      by (fact wellorder_Inf_le1[OF \<open>Suc (Sup ?S_eq) \<in> ?S_neq\<close>])
  next
    from \<open>Inf ?S_neq \<in> ?S_neq\<close> \<open>Sup ?S_eq \<in> ?S_eq\<close> show \<open>Suc (Sup ?S_eq) \<le> Inf ?S_neq\<close>
      by (metis (mono_tags, lifting) mem_Collect_eq not_less_eq_eq restriction_related_le)
  qed
qed

end


lemma restriction_related_set_is_atMost :
  \<open>restriction_related_set x y =
   (if x \<lessapprox> y then UNIV else {..Sup (restriction_related_set x y)})\<close>
proof (split if_split, intro conjI impI)
  show \<open>x \<lessapprox> y \<Longrightarrow> restriction_related_set x y = UNIV\<close> 
    by (simp add: UNIV_restriction_related_set_iff)
next
  assume \<open>\<not> x \<lessapprox> y\<close>
  hence * : \<open>Sup (restriction_related_set x y) \<in> restriction_related_set x y\<close>
    by (fact Sup_in_restriction_related_set)
  show \<open>restriction_related_set x y = {..Sup (restriction_related_set x y)} \<close>
  proof (intro subset_antisym subsetI)
    show \<open>n \<in> restriction_related_set x y \<Longrightarrow> n \<in> {..Sup (restriction_related_set x y)}\<close> for n
      by (simp add: \<open>\<not> x \<lessapprox> y\<close> finite_restriction_related_set_iff le_cSup_finite)
  next
    from "*" show \<open>n \<in> {..Sup (restriction_related_set x y)} \<Longrightarrow>
                   n \<in> restriction_related_set x y\<close> for n
      by simp (meson mem_Collect_eq restriction_related_le)
  qed
qed

lemma restriction_not_related_set_is_atLeast :
  \<open>restriction_not_related_set x y =
   (if x \<lessapprox> y then {} else {Inf (restriction_not_related_set x y)..})\<close>
proof (split if_split, intro conjI impI)
  from empty_restriction_not_related_set_iff
  show \<open>x \<lessapprox> y \<Longrightarrow> restriction_not_related_set x y = {}\<close> by blast
next
  assume \<open>\<not> x \<lessapprox> y\<close>
  have \<open>restriction_not_related_set x y = UNIV - restriction_related_set x y\<close> by auto
  also have \<open>\<dots> = UNIV - {..Sup (restriction_related_set x y)}\<close>
    by (subst restriction_related_set_is_atMost) (simp add: \<open>\<not> x \<lessapprox> y\<close>)
  also have \<open>\<dots> = {Suc (Sup (restriction_related_set x y))..}\<close> by auto
  also have \<open>Suc (Sup (restriction_related_set x y)) = Inf (restriction_not_related_set x y)\<close>
    by (simp add: \<open>\<not> x \<lessapprox> y\<close> flip: Inf_restriction_not_related_set_eq_Suc_Sup_restriction_related_set)
  finally show \<open>restriction_not_related_set x y = {Inf (restriction_not_related_set x y)..}\<close> .
qed


end




subsection \<open>Restriction shift Maps\<close>

locale Restriction_2_PreorderRestrictionSpace =
  R1 : Restriction \<open>(\<down>\<^sub>1)\<close> \<open>(\<lessapprox>\<^sub>1)\<close> +
  PRS2 : PreorderRestrictionSpace \<open>(\<down>\<^sub>2)\<close> \<open>(\<lessapprox>\<^sub>2)\<close>
  for restriction\<^sub>1 :: \<open>'a \<Rightarrow> nat \<Rightarrow> 'a\<close>  (infixl \<open>\<down>\<^sub>1\<close> 60)
    and relation\<^sub>1    :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infixl \<open>\<lessapprox>\<^sub>1\<close> 50)
    and restriction\<^sub>2 :: \<open>'b \<Rightarrow> nat \<Rightarrow> 'b\<close>  (infixl \<open>\<down>\<^sub>2\<close> 60)
    and relation\<^sub>2    :: \<open>'b \<Rightarrow> 'b \<Rightarrow> bool\<close> (infixl \<open>\<lessapprox>\<^sub>2\<close> 50)
begin

subsubsection \<open>Definition\<close>

text \<open>This notion is a generalization of constructive map and non-destructive map.\<close>

definition restriction_shift_on :: \<open>['a \<Rightarrow> 'b, int, 'a set] \<Rightarrow> bool\<close>
  where \<open>restriction_shift_on f k A \<equiv>
         \<forall>x\<in>A. \<forall>y\<in>A. \<forall>n. x \<down>\<^sub>1 n \<lessapprox>\<^sub>1 y \<down>\<^sub>1 n \<longrightarrow> f x \<down>\<^sub>2 nat (int n + k) \<lessapprox>\<^sub>2 f y \<down>\<^sub>2 nat (int n + k)\<close>

definition restriction_shift :: \<open>['a \<Rightarrow> 'b, int] \<Rightarrow> bool\<close>
  where \<open>restriction_shift f k \<equiv> restriction_shift_on f k UNIV\<close>


lemma restriction_shift_onI :
  \<open>(\<And>x y n. \<lbrakk>x \<in> A; y \<in> A; \<not> f x \<lessapprox>\<^sub>2 f y; x \<down>\<^sub>1 n \<lessapprox>\<^sub>1 y \<down>\<^sub>1 n\<rbrakk> \<Longrightarrow>
             f x \<down>\<^sub>2 nat (int n + k) \<lessapprox>\<^sub>2 f y \<down>\<^sub>2 nat (int n + k))
   \<Longrightarrow> restriction_shift_on f k A\<close>
  unfolding restriction_shift_on_def
  by (metis PRS2.all_restriction_related_iff_related)

corollary restriction_shiftI :
  \<open>(\<And>x y n. \<lbrakk>\<not> f x \<lessapprox>\<^sub>2 f y; x \<down>\<^sub>1 n \<lessapprox>\<^sub>1 y \<down>\<^sub>1 n\<rbrakk> \<Longrightarrow>
             f x \<down>\<^sub>2 nat (int n + k) \<lessapprox>\<^sub>2 f y \<down>\<^sub>2 nat (int n + k))
   \<Longrightarrow> restriction_shift f k\<close>
  by (unfold restriction_shift_def, rule restriction_shift_onI)



lemma restriction_shift_onD :
  \<open>\<lbrakk>restriction_shift_on f k A; x \<in> A; y \<in> A; x \<down>\<^sub>1 n \<lessapprox>\<^sub>1 y \<down>\<^sub>1 n\<rbrakk>
   \<Longrightarrow> f x \<down>\<^sub>2 nat (int n + k) \<lessapprox>\<^sub>2 f y \<down>\<^sub>2 nat (int n + k)\<close>
  by (unfold restriction_shift_on_def) blast

lemma restriction_shiftD :
  \<open>\<lbrakk>restriction_shift f k; x \<down>\<^sub>1 n \<lessapprox>\<^sub>1 y \<down>\<^sub>1 n\<rbrakk> \<Longrightarrow> f x \<down>\<^sub>2 nat (int n + k) \<lessapprox>\<^sub>2 f y \<down>\<^sub>2 nat (int n + k)\<close>
  unfolding restriction_shift_def using restriction_shift_onD by blast

lemma restriction_shift_on_subset :
  \<open>restriction_shift_on f k B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> restriction_shift_on f k A\<close>
  by (simp add: restriction_shift_on_def subset_iff)

lemma restriction_shift_imp_restriction_shift_on [restriction_shift_simpset] :
  \<open>restriction_shift f k \<Longrightarrow> restriction_shift_on f k A\<close>
  unfolding restriction_shift_def using restriction_shift_on_subset by blast


lemma restriction_shift_on_imp_restriction_shift_on_le [restriction_shift_simpset] :
  \<open>restriction_shift_on f l A\<close> if \<open>l \<le> k\<close> and \<open>restriction_shift_on f k A\<close>
proof (rule restriction_shift_onI)
  fix x y n assume \<open>x \<in> A\<close> \<open>y \<in> A\<close> \<open>x \<down>\<^sub>1 n \<lessapprox>\<^sub>1 y \<down>\<^sub>1 n\<close>
  from \<open>restriction_shift_on f k A\<close>[THEN restriction_shift_onD, OF this]
  have \<open>f x \<down>\<^sub>2 nat (int n + k) \<lessapprox>\<^sub>2 f y \<down>\<^sub>2 nat (int n + k)\<close> .
  moreover have \<open>nat (int n + l) \<le> nat (int n + k)\<close> by (simp add: nat_mono \<open>l \<le> k\<close>)
  ultimately show \<open>f x \<down>\<^sub>2 nat (int n + l) \<lessapprox>\<^sub>2 f y \<down>\<^sub>2 nat (int n + l)\<close>
    using PRS2.restriction_related_le by blast
qed

corollary restriction_shift_imp_restriction_shift_le [restriction_shift_simpset] :
  \<open>l \<le> k \<Longrightarrow> restriction_shift f k \<Longrightarrow> restriction_shift f l\<close>
  unfolding restriction_shift_def
  by (fact restriction_shift_on_imp_restriction_shift_on_le)



lemma restriction_shift_on_if_then_else [restriction_shift_simpset, restriction_shift_introset] :
  \<open>\<lbrakk>\<And>x. P x \<Longrightarrow> restriction_shift_on (f x) k A;
    \<And>x. \<not> P x \<Longrightarrow> restriction_shift_on (g x) k A\<rbrakk> \<Longrightarrow>
    restriction_shift_on (\<lambda>y. if P x then f x y else g x y) k A\<close>
  by (rule restriction_shift_onI) (auto dest: restriction_shift_onD)

corollary restriction_shift_if_then_else [restriction_shift_simpset, restriction_shift_introset] :
  \<open>\<lbrakk>\<And>x. P x \<Longrightarrow> restriction_shift (f x) k;
    \<And>x. \<not> P x \<Longrightarrow> restriction_shift (g x) k\<rbrakk> \<Longrightarrow>
    restriction_shift (\<lambda>y. if P x then f x y else g x y) k\<close>
  unfolding restriction_shift_def by (fact restriction_shift_on_if_then_else)



subsubsection \<open>Three particular Cases\<close>

text \<open>The shift is most often equal to \<^term>\<open>0 :: int\<close>, \<^term>\<open>1 :: int\<close> or \<^term>\<open>- 1 :: int\<close>.
      We provide extra support in these three cases.\<close>

paragraph \<open>Non-too-destructive Map\<close>

definition non_too_destructive_on :: \<open>['a \<Rightarrow> 'b, 'a set] \<Rightarrow> bool\<close>
  where \<open>non_too_destructive_on f A \<equiv> restriction_shift_on f (- 1) A\<close>

definition non_too_destructive :: \<open>['a \<Rightarrow> 'b] \<Rightarrow> bool\<close>
  where \<open>non_too_destructive f \<equiv> non_too_destructive_on f UNIV\<close>


lemma non_too_destructive_onI :
  \<open>non_too_destructive_on f A\<close>
  if \<open>\<And>n x y. \<lbrakk>x \<in> A; y \<in> A; \<not> f x \<lessapprox>\<^sub>2 f y; x \<down>\<^sub>1 Suc n \<lessapprox>\<^sub>1 y \<down>\<^sub>1 Suc n\<rbrakk> \<Longrightarrow> f x \<down>\<^sub>2 n \<lessapprox>\<^sub>2 f y \<down>\<^sub>2 n\<close>
proof (unfold non_too_destructive_on_def, rule restriction_shift_onI)
  fix x y n
  show \<open>\<lbrakk>x \<in> A; y \<in> A; \<not> f x \<lessapprox>\<^sub>2 f y; x \<down>\<^sub>1 n \<lessapprox>\<^sub>1 y \<down>\<^sub>1 n\<rbrakk>
        \<Longrightarrow> f x \<down>\<^sub>2 nat (int n + - 1) \<lessapprox>\<^sub>2 f y \<down>\<^sub>2 nat (int n + - 1)\<close>
    by (cases \<open>n < 1\<close>) (simp_all add: Suc_nat_eq_nat_zadd1 that)
qed

lemma non_too_destructiveI :
  \<open>\<lbrakk>\<And>n x y. \<lbrakk>\<not> f x \<lessapprox>\<^sub>2 f y; x \<down>\<^sub>1 Suc n \<lessapprox>\<^sub>1 y \<down>\<^sub>1 Suc n\<rbrakk> \<Longrightarrow> f x \<down>\<^sub>2 n \<lessapprox>\<^sub>2 f y \<down>\<^sub>2 n\<rbrakk>
   \<Longrightarrow> non_too_destructive f\<close>
  by (unfold non_too_destructive_def, rule non_too_destructive_onI)

lemma non_too_destructive_onD :
  \<open>\<lbrakk>non_too_destructive_on f A; x \<in> A; y \<in> A; x \<down>\<^sub>1 Suc n \<lessapprox>\<^sub>1 y \<down>\<^sub>1 Suc n\<rbrakk> \<Longrightarrow> f x \<down>\<^sub>2 n \<lessapprox>\<^sub>2 f y \<down>\<^sub>2 n\<close>
  unfolding non_too_destructive_on_def using restriction_shift_onD by fastforce

lemma non_too_destructiveD :
  \<open>\<lbrakk>non_too_destructive f; x \<down>\<^sub>1 Suc n \<lessapprox>\<^sub>1 y \<down>\<^sub>1 Suc n\<rbrakk> \<Longrightarrow> f x \<down>\<^sub>2 n \<lessapprox>\<^sub>2 f y \<down>\<^sub>2 n\<close>
  unfolding non_too_destructive_def using non_too_destructive_onD by simp

lemma non_too_destructive_on_subset :
  \<open>non_too_destructive_on f B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> non_too_destructive_on f A\<close>
  by (meson non_too_destructive_on_def restriction_shift_on_subset)

lemma non_too_destructive_imp_non_too_destructive_on [restriction_shift_simpset] :
  \<open>non_too_destructive f \<Longrightarrow> non_too_destructive_on f A\<close>
  unfolding non_too_destructive_def using non_too_destructive_on_subset by auto


corollary non_too_destructive_on_if_then_else [restriction_shift_simpset, restriction_shift_introset]:
  \<open>\<lbrakk>\<And>x. P x \<Longrightarrow> non_too_destructive_on (f x) A; \<And>x. \<not> P x \<Longrightarrow> non_too_destructive_on (g x) A\<rbrakk>
     \<Longrightarrow> non_too_destructive_on (\<lambda>y. if P x then f x y else g x y) A\<close>
  and non_too_destructive_if_then_else [restriction_shift_simpset, restriction_shift_introset] :
  \<open>\<lbrakk>\<And>x. P x \<Longrightarrow> non_too_destructive (f x); \<And>x. \<not> P x \<Longrightarrow> non_too_destructive (g x)\<rbrakk>
     \<Longrightarrow> non_too_destructive (\<lambda>y. if P x then f x y else g x y)\<close>
  by (auto simp add: non_too_destructive_def non_too_destructive_on_def
      intro: restriction_shift_on_if_then_else)



paragraph \<open>Non-destructive Map\<close>

definition non_destructive_on :: \<open>['a \<Rightarrow> 'b, 'a set] \<Rightarrow> bool\<close>
  where \<open>non_destructive_on f A \<equiv> restriction_shift_on f 0 A\<close>

definition non_destructive :: \<open>['a \<Rightarrow> 'b] \<Rightarrow> bool\<close>
  where \<open>non_destructive f \<equiv> non_destructive_on f UNIV\<close>


lemma non_destructive_onI :
  \<open>\<lbrakk>\<And>n x y. \<lbrakk>n \<noteq> 0; x \<in> A; y \<in> A; \<not> f x \<lessapprox>\<^sub>2 f y; x \<down>\<^sub>1 n \<lessapprox>\<^sub>1 y \<down>\<^sub>1 n\<rbrakk> \<Longrightarrow> f x \<down>\<^sub>2 n \<lessapprox>\<^sub>2 f y \<down>\<^sub>2 n\<rbrakk>
   \<Longrightarrow> non_destructive_on f A\<close>
  by (unfold non_destructive_on_def, rule restriction_shift_onI)
    (metis PRS2.restriction_0_related add.right_neutral nat_int)

lemma non_destructiveI :
  \<open>\<lbrakk>\<And>n x y. \<lbrakk>n \<noteq> 0; \<not> f x \<lessapprox>\<^sub>2 f y; x \<down>\<^sub>1 n \<lessapprox>\<^sub>1 y \<down>\<^sub>1 n\<rbrakk> \<Longrightarrow> f x \<down>\<^sub>2 n \<lessapprox>\<^sub>2 f y \<down>\<^sub>2 n\<rbrakk>
   \<Longrightarrow> non_destructive f\<close> by (unfold non_destructive_def, rule non_destructive_onI)

lemma non_destructive_onD :
  \<open>\<lbrakk>non_destructive_on f A; x \<in> A; y \<in> A; \<not> f x \<lessapprox>\<^sub>2 f y; x \<down>\<^sub>1 n \<lessapprox>\<^sub>1 y \<down>\<^sub>1 n\<rbrakk> \<Longrightarrow> f x \<down>\<^sub>2 n \<lessapprox>\<^sub>2 f y \<down>\<^sub>2 n\<close>
  by (simp add: non_destructive_on_def restriction_shift_on_def)

lemma non_destructiveD : \<open>\<lbrakk>non_destructive f; x \<down>\<^sub>1 n \<lessapprox>\<^sub>1 y \<down>\<^sub>1 n\<rbrakk> \<Longrightarrow> f x \<down>\<^sub>2 n \<lessapprox>\<^sub>2 f y \<down>\<^sub>2 n\<close>
  by (simp add: non_destructive_def non_destructive_on_def restriction_shift_on_def)

lemma non_destructive_on_subset :
  \<open>non_destructive_on f B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> non_destructive_on f A\<close>
  by (meson non_destructive_on_def restriction_shift_on_subset)

lemma non_destructive_imp_non_destructive_on [restriction_shift_simpset] :
  \<open>non_destructive f \<Longrightarrow> non_destructive_on f A\<close>
  unfolding non_destructive_def using non_destructive_on_subset by auto

lemma non_destructive_on_imp_non_too_destructive_on [restriction_shift_simpset] :
  \<open>non_destructive_on f A \<Longrightarrow> non_too_destructive_on f A\<close>
  unfolding non_destructive_on_def non_too_destructive_on_def
  by (rule restriction_shift_on_imp_restriction_shift_on_le[of \<open>- 1\<close> 0 f A, simplified])

corollary non_destructive_imp_non_too_destructive [restriction_shift_simpset] :
  \<open>non_destructive f \<Longrightarrow> non_too_destructive f\<close>
  by (unfold non_destructive_def non_too_destructive_def)
    (fact non_destructive_on_imp_non_too_destructive_on)


corollary non_destructive_on_if_then_else [restriction_shift_simpset, restriction_shift_introset] :
  \<open>\<lbrakk>\<And>x. P x \<Longrightarrow> non_destructive_on (f x) A; \<And>x. \<not> P x \<Longrightarrow> non_destructive_on (g x) A\<rbrakk>
     \<Longrightarrow> non_destructive_on (\<lambda>y. if P x then f x y else g x y) A\<close>
  and non_destructive_if_then_else [restriction_shift_simpset, restriction_shift_introset] :
  \<open>\<lbrakk>\<And>x. P x \<Longrightarrow> non_destructive (f x); \<And>x. \<not> P x \<Longrightarrow> non_destructive (g x)\<rbrakk>
     \<Longrightarrow> non_destructive (\<lambda>y. if P x then f x y else g x y)\<close>
  by (auto simp add: non_destructive_def non_destructive_on_def
      intro: restriction_shift_on_if_then_else)



paragraph \<open>Constructive Map\<close>

definition constructive_on :: \<open>['a \<Rightarrow> 'b, 'a set] \<Rightarrow> bool\<close>
  where \<open>constructive_on f A \<equiv> restriction_shift_on f 1 A\<close>

definition constructive :: \<open>['a \<Rightarrow> 'b] \<Rightarrow> bool\<close>
  where \<open>constructive f \<equiv> constructive_on f UNIV\<close>


lemma constructive_onI :
  \<open>\<lbrakk>\<And>n x y. \<lbrakk>x \<in> A; y \<in> A; \<not> f x \<lessapprox>\<^sub>2 f y; x \<down>\<^sub>1 n \<lessapprox>\<^sub>1 y \<down>\<^sub>1 n\<rbrakk> \<Longrightarrow> f x \<down>\<^sub>2 Suc n \<lessapprox>\<^sub>2 f y \<down>\<^sub>2 Suc n\<rbrakk>
   \<Longrightarrow> constructive_on f A\<close>
  by (simp add: Suc_as_int constructive_on_def restriction_shift_onI)

lemma constructiveI :
  \<open>\<lbrakk>\<And>n x y. \<lbrakk>\<not> f x \<lessapprox>\<^sub>2 f y; x \<down>\<^sub>1 n \<lessapprox>\<^sub>1 y \<down>\<^sub>1 n\<rbrakk> \<Longrightarrow> f x \<down>\<^sub>2 Suc n \<lessapprox>\<^sub>2 f y \<down>\<^sub>2 Suc n\<rbrakk>
   \<Longrightarrow> constructive f\<close> by (unfold constructive_def, rule constructive_onI)

lemma constructive_onD :
  \<open>\<lbrakk>constructive_on f A; x \<in> A; y \<in> A; x \<down>\<^sub>1 n \<lessapprox>\<^sub>1 y \<down>\<^sub>1 n\<rbrakk> \<Longrightarrow> f x \<down>\<^sub>2 Suc n \<lessapprox>\<^sub>2 f y \<down>\<^sub>2 Suc n\<close>
  unfolding constructive_on_def by (metis Suc_as_int restriction_shift_onD)

lemma constructiveD : \<open>\<lbrakk>constructive f; x \<down>\<^sub>1 n \<lessapprox>\<^sub>1 y \<down>\<^sub>1 n\<rbrakk> \<Longrightarrow> f x \<down>\<^sub>2 Suc n \<lessapprox>\<^sub>2 f y \<down>\<^sub>2 Suc n\<close>
  unfolding constructive_def using constructive_onD by blast

lemma constructive_on_subset :
  \<open>constructive_on f B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> constructive_on f A\<close>
  by (meson constructive_on_def restriction_shift_on_subset)

lemma constructive_imp_constructive_on [restriction_shift_simpset] :
  \<open>constructive f \<Longrightarrow> constructive_on f A\<close>
  unfolding constructive_def using constructive_on_subset by auto


lemma constructive_on_imp_non_destructive_on [restriction_shift_simpset] :
  \<open>constructive_on f A \<Longrightarrow> non_destructive_on f A\<close>
  by (rule non_destructive_onI)
    (meson PRS2.restriction_related_pred constructive_onD)

corollary constructive_imp_non_destructive [restriction_shift_simpset] :
  \<open>constructive f \<Longrightarrow> non_destructive f\<close>
  unfolding constructive_def non_destructive_def
  by (fact constructive_on_imp_non_destructive_on)


corollary constructive_on_if_then_else [restriction_shift_simpset, restriction_shift_introset] :
  \<open>\<lbrakk>\<And>x. P x \<Longrightarrow> constructive_on (f x) A; \<And>x. \<not> P x \<Longrightarrow> constructive_on (g x) A\<rbrakk>
     \<Longrightarrow> constructive_on (\<lambda>y. if P x then f x y else g x y) A\<close>
  and constructive_if_then_else [restriction_shift_simpset, restriction_shift_introset] :
  \<open>\<lbrakk>\<And>x. P x \<Longrightarrow> constructive (f x); \<And>x. \<not> P x \<Longrightarrow> constructive (g x)\<rbrakk>
     \<Longrightarrow> constructive (\<lambda>y. if P x then f x y else g x y)\<close>
  by (auto simp add: constructive_def constructive_on_def
      intro: restriction_shift_on_if_then_else)


end



subsubsection \<open>Properties\<close>

locale PreorderRestrictionSpace_2_PreorderRestrictionSpace =
  PRS1 : PreorderRestrictionSpace \<open>(\<down>\<^sub>1)\<close> \<open>(\<lessapprox>\<^sub>1)\<close> +
  PRS2 : PreorderRestrictionSpace \<open>(\<down>\<^sub>2)\<close> \<open>(\<lessapprox>\<^sub>2)\<close>
  for restriction\<^sub>1 :: \<open>'a \<Rightarrow> nat \<Rightarrow> 'a\<close>  (infixl \<open>\<down>\<^sub>1\<close> 60)
    and relation\<^sub>1    :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infixl \<open>\<lessapprox>\<^sub>1\<close> 50)
    and restriction\<^sub>2 :: \<open>'b \<Rightarrow> nat \<Rightarrow> 'b\<close>  (infixl \<open>\<down>\<^sub>2\<close> 60)
    and relation\<^sub>2    :: \<open>'b \<Rightarrow> 'b \<Rightarrow> bool\<close> (infixl \<open>\<lessapprox>\<^sub>2\<close> 50)
begin

sublocale Restriction_2_PreorderRestrictionSpace by unfold_locales

lemma restriction_shift_on_restriction_restriction :
  \<open>f (x \<down>\<^sub>1 n) \<down>\<^sub>2 nat (int n + k) \<lessapprox>\<^sub>2 f x \<down>\<^sub>2 nat (int n + k)\<close>
  if \<open>restriction_shift_on f k A\<close> \<open>x \<down>\<^sub>1 n \<in> A\<close> \<open>x \<in> A\<close> \<open>x \<down>\<^sub>1 n \<lessapprox>\<^sub>1 x \<down>\<^sub>1 n\<close>
    \<comment>\<open>the last assumption is trivial if \<^term>\<open>(\<lessapprox>\<^sub>1)\<close> is reflexive\<close>
  by (rule restriction_shift_onD
      [OF \<open>restriction_shift_on f k A\<close> \<open>x \<down>\<^sub>1 n \<in> A\<close> \<open>x \<in> A\<close>])
    (simp add: \<open>x \<down>\<^sub>1 n \<lessapprox>\<^sub>1 x \<down>\<^sub>1 n\<close>)

corollary restriction_shift_restriction_restriction :
  \<open>f (x \<down>\<^sub>1 n) \<down>\<^sub>2 nat (int n + k) \<lessapprox>\<^sub>2 f x \<down>\<^sub>2 nat (int n + k)\<close>
  if \<open>restriction_shift f k\<close> and \<open>x \<down>\<^sub>1 n \<lessapprox>\<^sub>1 x \<down>\<^sub>1 n\<close>
  by (rule restriction_shiftD[OF \<open>restriction_shift f k\<close>])
    (simp add: \<open>x \<down>\<^sub>1 n \<lessapprox>\<^sub>1 x \<down>\<^sub>1 n\<close>)


corollary constructive_on_restriction_restriction :
  \<open>\<lbrakk>constructive_on f A; x \<down>\<^sub>1 n \<in> A; x \<in> A; x \<down>\<^sub>1 n \<lessapprox>\<^sub>1 x \<down>\<^sub>1 n\<rbrakk>
   \<Longrightarrow> f (x \<down>\<^sub>1 n) \<down>\<^sub>2 Suc n \<lessapprox>\<^sub>2 f x \<down>\<^sub>2 Suc n\<close>
  using restriction_shift_on_restriction_restriction
    restriction_shift_restriction_restriction Suc_as_int
  unfolding constructive_on_def by presburger

corollary constructive_restriction_restriction :
  \<open>constructive f \<Longrightarrow> x \<down>\<^sub>1 n \<lessapprox>\<^sub>1 x \<down>\<^sub>1 n \<Longrightarrow> f (x \<down>\<^sub>1 n) \<down>\<^sub>2 Suc n \<lessapprox>\<^sub>2 f x \<down>\<^sub>2 Suc n\<close>
  by (simp add: constructive_def constructive_on_restriction_restriction)


corollary non_destructive_on_restriction_restriction :
  \<open>\<lbrakk>non_destructive_on f A; x \<down>\<^sub>1 n \<in> A; x \<in> A; x \<down>\<^sub>1 n \<lessapprox>\<^sub>1 x \<down>\<^sub>1 n\<rbrakk>
   \<Longrightarrow> f (x \<down>\<^sub>1 n) \<down>\<^sub>2 n \<lessapprox>\<^sub>2 f x \<down>\<^sub>2 n\<close>
  using restriction_shift_on_restriction_restriction
    restriction_shift_restriction_restriction
  unfolding non_destructive_on_def by (metis add.commute add_0 nat_int)

corollary non_destructive_restriction_restriction :
  \<open>non_destructive f \<Longrightarrow> x \<down>\<^sub>1 n \<lessapprox>\<^sub>1 x \<down>\<^sub>1 n \<Longrightarrow> f (x \<down>\<^sub>1 n) \<down>\<^sub>2 n \<lessapprox>\<^sub>2 f x \<down>\<^sub>2 n\<close>
  by (simp add: non_destructive_def non_destructive_on_restriction_restriction)


corollary non_too_destructive_on_restriction_restriction :
  \<open>\<lbrakk>non_too_destructive_on f A; x \<down>\<^sub>1 Suc n \<in> A; x \<in> A; x \<down>\<^sub>1 Suc n \<lessapprox>\<^sub>1 x \<down>\<^sub>1 Suc n\<rbrakk>
   \<Longrightarrow> f (x \<down>\<^sub>1 Suc n) \<down>\<^sub>2 n \<lessapprox>\<^sub>2 f x \<down>\<^sub>2 n\<close>
  using restriction_shift_on_restriction_restriction
    restriction_shift_restriction_restriction
  unfolding non_too_destructive_on_def by fastforce

corollary non_too_destructive_restriction_restriction :
  \<open>non_too_destructive f \<Longrightarrow> x \<down>\<^sub>1 Suc n \<lessapprox>\<^sub>1 x \<down>\<^sub>1 Suc n \<Longrightarrow> f (x \<down>\<^sub>1 Suc n) \<down>\<^sub>2 n \<lessapprox>\<^sub>2 f x \<down>\<^sub>2 n\<close>
  by (simp add: non_too_destructive_def non_too_destructive_on_restriction_restriction)


end


locale Restriction_2_PreorderRestrictionSpace_2_PreorderRestrictionSpace =
  R2PRS1 : Restriction_2_PreorderRestrictionSpace \<open>(\<down>\<^sub>1)\<close> \<open>(\<lessapprox>\<^sub>1)\<close> \<open>(\<down>\<^sub>2)\<close> \<open>(\<lessapprox>\<^sub>2)\<close> +
  PRS2 : PreorderRestrictionSpace \<open>(\<down>\<^sub>3)\<close> \<open>(\<lessapprox>\<^sub>3)\<close>
  for restriction\<^sub>1 :: \<open>'a \<Rightarrow> nat \<Rightarrow> 'a\<close>  (infixl \<open>\<down>\<^sub>1\<close> 60)
    and relation\<^sub>1    :: \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> (infixl \<open>\<lessapprox>\<^sub>1\<close> 50)
    and restriction\<^sub>2 :: \<open>'b \<Rightarrow> nat \<Rightarrow> 'b\<close>  (infixl \<open>\<down>\<^sub>2\<close> 60)
    and relation\<^sub>2    :: \<open>'b \<Rightarrow> 'b \<Rightarrow> bool\<close> (infixl \<open>\<lessapprox>\<^sub>2\<close> 50)
    and restriction\<^sub>3 :: \<open>'c \<Rightarrow> nat \<Rightarrow> 'c\<close>  (infixl \<open>\<down>\<^sub>3\<close> 60)
    and relation\<^sub>3    :: \<open>'c \<Rightarrow> 'c \<Rightarrow> bool\<close> (infixl \<open>\<lessapprox>\<^sub>3\<close> 50)
begin

interpretation R2PRS2 : Restriction_2_PreorderRestrictionSpace \<open>(\<down>\<^sub>1)\<close> \<open>(\<lessapprox>\<^sub>1)\<close> \<open>(\<down>\<^sub>3)\<close> \<open>(\<lessapprox>\<^sub>3)\<close>
  by unfold_locales

interpretation PRS2PRS3 : PreorderRestrictionSpace_2_PreorderRestrictionSpace \<open>(\<down>\<^sub>2)\<close> \<open>(\<lessapprox>\<^sub>2)\<close> \<open>(\<down>\<^sub>3)\<close> \<open>(\<lessapprox>\<^sub>3)\<close>
  by unfold_locales



theorem restriction_shift_on_comp_restriction_shift_on [restriction_shift_simpset] :
  \<open>R2PRS2.restriction_shift_on (\<lambda>x. g (f x)) (k + l) A\<close>
  if \<open>f ` A \<subseteq> B\<close> \<open>PRS2PRS3.restriction_shift_on g l B\<close> \<open>R2PRS1.restriction_shift_on f k A\<close>
proof (rule R2PRS2.restriction_shift_onI)
  fix x y n assume \<open>x \<in> A\<close> \<open>y \<in> A\<close> \<open>x \<down>\<^sub>1 n \<lessapprox>\<^sub>1 y \<down>\<^sub>1 n\<close>
  from \<open>R2PRS1.restriction_shift_on f k A\<close>[THEN R2PRS1.restriction_shift_onD, OF this]
  have \<open>f x \<down>\<^sub>2 nat (int n + k) \<lessapprox>\<^sub>2 f y \<down>\<^sub>2 nat (int n + k)\<close> .
  moreover from \<open>x \<in> A\<close> \<open>y \<in> A\<close> \<open>f ` A \<subseteq> B\<close> have \<open>f x \<in> B\<close> \<open>f y \<in> B\<close> by auto
  ultimately have \<open>g (f x) \<down>\<^sub>3 nat (int (nat (int n + k)) + l) \<lessapprox>\<^sub>3
                   g (f y) \<down>\<^sub>3 nat (int (nat (int n + k)) + l)\<close>
    using \<open>PRS2PRS3.restriction_shift_on g l B\<close>[THEN PRS2PRS3.restriction_shift_onD] by blast
  moreover have \<open>nat (int n + (k + l)) \<le> nat (int (nat (int n + k)) + l)\<close>
    by (simp add: nat_mono)
  ultimately show \<open>g (f x) \<down>\<^sub>3 nat (int n + (k + l)) \<lessapprox>\<^sub>3 g (f y) \<down>\<^sub>3 nat (int n + (k + l))\<close>
    by (metis PRS2.restriction_related_le)
qed

corollary restriction_shift_comp_restriction_shift_on [restriction_shift_simpset] :
  \<open>PRS2PRS3.restriction_shift g l \<Longrightarrow> R2PRS1.restriction_shift_on f k A \<Longrightarrow>
   R2PRS2.restriction_shift_on (\<lambda>x. g (f x)) (k + l) A\<close>
  using PRS2PRS3.restriction_shift_imp_restriction_shift_on
    restriction_shift_on_comp_restriction_shift_on by blast

corollary restriction_shift_comp_restriction_shift [restriction_shift_simpset] :
  \<open>PRS2PRS3.restriction_shift g l \<Longrightarrow> R2PRS1.restriction_shift f k \<Longrightarrow>
   R2PRS2.restriction_shift (\<lambda>x. g (f x)) (k + l)\<close>
  by (simp add: R2PRS1.restriction_shift_imp_restriction_shift_on
      R2PRS2.restriction_shift_def restriction_shift_comp_restriction_shift_on)



corollary non_destructive_on_comp_non_destructive_on [restriction_shift_simpset] :
  \<open>\<lbrakk>f ` A \<subseteq> B; PRS2PRS3.non_destructive_on g B; R2PRS1.non_destructive_on f A\<rbrakk> \<Longrightarrow>
    R2PRS2.non_destructive_on (\<lambda>x. g (f x)) A\<close>
  by (simp add: R2PRS1.non_destructive_on_def R2PRS2.non_destructive_on_def
      R2PRS2.restriction_shift_on_def R2PRS1.restriction_shift_on_def)
    (meson PRS2.mono_restriction_related PRS2PRS3.non_destructive_onD image_subset_iff)

corollary non_destructive_comp_non_destructive_on [restriction_shift_simpset] :
  \<open>PRS2PRS3.non_destructive g \<Longrightarrow> R2PRS1.non_destructive_on f A \<Longrightarrow>
   R2PRS2.non_destructive_on (\<lambda>x. g (f x)) A\<close>
  by (simp add: PRS2PRS3.non_destructiveD R2PRS1.non_destructive_on_def
      R2PRS2.non_destructive_on_def R2PRS2.restriction_shift_on_def
      R2PRS1.restriction_shift_on_def)

corollary non_destructive_comp_non_destructive [restriction_shift_simpset] :
  \<open>PRS2PRS3.non_destructive g \<Longrightarrow> R2PRS1.non_destructive f \<Longrightarrow>
   R2PRS2.non_destructive (\<lambda>x. g (f x))\<close>
  by (simp add: PRS2PRS3.non_destructiveD R2PRS1.non_destructiveD
      R2PRS2.non_destructive_def R2PRS2.non_destructive_onI)


corollary constructive_on_comp_non_destructive_on [restriction_shift_simpset] :
  \<open>\<lbrakk>f ` A \<subseteq> B; PRS2PRS3.constructive_on g B; R2PRS1.non_destructive_on f A\<rbrakk> \<Longrightarrow>
    R2PRS2.constructive_on (\<lambda>x. g (f x)) A\<close>
  by (metis PRS2PRS3.constructive_on_def R2PRS1.non_destructive_on_def
      R2PRS2.constructive_on_def add.commute add_cancel_left_right
      restriction_shift_on_comp_restriction_shift_on)

corollary constructive_comp_non_destructive_on [restriction_shift_simpset] :
  \<open>PRS2PRS3.constructive g \<Longrightarrow> R2PRS1.non_destructive_on f A \<Longrightarrow>
   R2PRS2.constructive_on (\<lambda>x. g (f x)) A\<close>
  by (simp add: R2PRS1.Restriction_2_PreorderRestrictionSpace_axioms
      PRS2PRS3.constructiveD R2PRS1.non_destructive_on_def R2PRS2.constructive_onI
      Restriction_2_PreorderRestrictionSpace.restriction_shift_on_def)

corollary constructive_comp_non_destructive [restriction_shift_simpset] :
  \<open>PRS2PRS3.constructive g \<Longrightarrow> R2PRS1.non_destructive f \<Longrightarrow>
   R2PRS2.constructive (\<lambda>x. g (f x))\<close>
  by (simp add: PRS2PRS3.constructiveD R2PRS1.non_destructiveD R2PRS2.constructiveI)


corollary non_destructive_on_comp_constructive_on [restriction_shift_simpset] :
  \<open>\<lbrakk>f ` A \<subseteq> B; PRS2PRS3.non_destructive_on g B; R2PRS1.constructive_on f A\<rbrakk> \<Longrightarrow>
    R2PRS2.constructive_on (\<lambda>x. g (f x)) A\<close>
  by (simp add: PRS2PRS3.non_destructive_onD R2PRS1.constructive_onD
      R2PRS2.constructive_onI image_subset_iff)

corollary non_destructive_comp_constructive_on [restriction_shift_simpset] :
  \<open>PRS2PRS3.non_destructive g \<Longrightarrow> R2PRS1.constructive_on f A \<Longrightarrow>
   R2PRS2.constructive_on (\<lambda>x. g (f x)) A\<close>
  using PRS2PRS3.non_destructive_def non_destructive_on_comp_constructive_on by blast

corollary non_destructive_comp_constructive [restriction_shift_simpset] :
  \<open>PRS2PRS3.non_destructive g \<Longrightarrow> R2PRS1.constructive f \<Longrightarrow>
   R2PRS2.constructive (\<lambda>x. g (f x))\<close>
  using PRS2PRS3.non_destructiveD R2PRS1.constructiveD R2PRS2.constructiveI by presburger


corollary non_too_destructive_on_comp_non_destructive_on [restriction_shift_simpset] :
  \<open>\<lbrakk>f ` A \<subseteq> B; PRS2PRS3.non_too_destructive_on g B; R2PRS1.non_destructive_on f A\<rbrakk> \<Longrightarrow>
    R2PRS2.non_too_destructive_on (\<lambda>x. g (f x)) A\<close>
  by (metis PRS2PRS3.non_too_destructive_on_def R2PRS1.non_destructive_on_def
      R2PRS2.non_too_destructive_on_def add.commute
      add.right_neutral restriction_shift_on_comp_restriction_shift_on)

corollary non_too_destructive_comp_non_destructive_on [restriction_shift_simpset] :
  \<open>PRS2PRS3.non_too_destructive g \<Longrightarrow> R2PRS1.non_destructive_on f A \<Longrightarrow>
   R2PRS2.non_too_destructive_on (\<lambda>x. g (f x)) A\<close>
  by (metis PRS2PRS3.non_too_destructive_imp_non_too_destructive_on
      non_too_destructive_on_comp_non_destructive_on top_greatest)

corollary non_too_destructive_comp_non_destructive [restriction_shift_simpset] :
  \<open>PRS2PRS3.non_too_destructive g \<Longrightarrow> R2PRS1.non_destructive f \<Longrightarrow>
   R2PRS2.non_too_destructive (\<lambda>x. g (f x))\<close>
  by (simp add: PRS2PRS3.non_too_destructiveD R2PRS1.non_destructiveD R2PRS2.non_too_destructiveI)


corollary non_destructive_on_comp_non_too_destructive_on [restriction_shift_simpset] :
  \<open>\<lbrakk>f ` A \<subseteq> B; PRS2PRS3.non_destructive_on g B; R2PRS1.non_too_destructive_on f A\<rbrakk> \<Longrightarrow>
    R2PRS2.non_too_destructive_on (\<lambda>x. g (f x)) A\<close>
  by (simp add: PRS2PRS3.non_destructive_onD R2PRS1.non_too_destructive_onD
      R2PRS2.non_too_destructive_onI image_subset_iff)

corollary non_destructive_comp_non_too_destructive_on [restriction_shift_simpset] :
  \<open>PRS2PRS3.non_destructive g \<Longrightarrow> R2PRS1.non_too_destructive_on f A \<Longrightarrow>
   R2PRS2.non_too_destructive_on (\<lambda>x. g (f x)) A\<close>
  by (simp add: PRS2PRS3.non_destructiveD R2PRS1.non_too_destructive_onD R2PRS2.non_too_destructive_onI)

corollary non_destructive_comp_non_too_destructive [restriction_shift_simpset] :
  \<open>PRS2PRS3.non_destructive g \<Longrightarrow> R2PRS1.non_too_destructive f \<Longrightarrow>
   R2PRS2.non_too_destructive (\<lambda>x. g (f x))\<close>
  using R2PRS1.non_too_destructive_imp_non_too_destructive_on R2PRS2.non_too_destructive_def
    non_destructive_comp_non_too_destructive_on by blast


corollary non_too_destructive_on_comp_constructive_on [restriction_shift_simpset] :
  \<open>\<lbrakk>f ` A \<subseteq> B; PRS2PRS3.non_too_destructive_on g B; R2PRS1.constructive_on f A\<rbrakk> \<Longrightarrow>
    R2PRS2.non_destructive_on (\<lambda>x. g (f x)) A\<close>
  using restriction_shift_on_comp_restriction_shift_on[of f A B g \<open>- 1\<close> 1]
  by (simp add: PRS2PRS3.non_too_destructive_on_def
      R2PRS2.non_destructive_on_def R2PRS1.constructive_on_def )

corollary non_too_destructive_comp_constructive_on [restriction_shift_simpset] :
  \<open>PRS2PRS3.non_too_destructive g \<Longrightarrow> R2PRS1.constructive_on f A \<Longrightarrow>
   R2PRS2.non_destructive_on (\<lambda>x. g (f x)) A\<close>
  by (metis PRS2PRS3.non_too_destructive_imp_non_too_destructive_on
      non_too_destructive_on_comp_constructive_on top_greatest)

corollary non_too_destructive_comp_constructive [restriction_shift_simpset] :
  \<open>PRS2PRS3.non_too_destructive g \<Longrightarrow> R2PRS1.constructive f \<Longrightarrow>
   R2PRS2.non_destructive (\<lambda>x. g (f x))\<close>
  by (simp add: PRS2PRS3.non_too_destructiveD R2PRS1.constructiveD R2PRS2.non_destructiveI)


corollary constructive_on_comp_non_too_destructive_on [restriction_shift_simpset] :
  \<open>\<lbrakk>f ` A \<subseteq> B; PRS2PRS3.constructive_on g B; R2PRS1.non_too_destructive_on f A\<rbrakk> \<Longrightarrow>
    R2PRS2.non_destructive_on (\<lambda>x. g (f x)) A\<close>
  using restriction_shift_on_comp_restriction_shift_on[of f A B g 1 \<open>- 1\<close>] 
  by (simp add: R2PRS1.non_too_destructive_on_def
      PRS2PRS3.constructive_on_def R2PRS2.non_destructive_on_def)

corollary constructive_comp_non_too_destructive_on [restriction_shift_simpset] :
  \<open>PRS2PRS3.constructive g \<Longrightarrow> R2PRS1.non_too_destructive_on f A \<Longrightarrow>
   R2PRS2.non_destructive_on (\<lambda>x. g (f x)) A\<close>
  using PRS2PRS3.constructive_imp_constructive_on constructive_on_comp_non_too_destructive_on by blast

corollary constructive_comp_non_too_destructive [restriction_shift_simpset] :
  \<open>PRS2PRS3.constructive g \<Longrightarrow> R2PRS1.non_too_destructive f \<Longrightarrow>
   R2PRS2.non_destructive (\<lambda>x. g (f x))\<close>
  by (metis R2PRS1.non_too_destructive_imp_non_too_destructive_on R2PRS2.non_destructiveI
      R2PRS2.non_destructive_onD UNIV_I constructive_comp_non_too_destructive_on)



end



(*<*)
end
  (*>*)