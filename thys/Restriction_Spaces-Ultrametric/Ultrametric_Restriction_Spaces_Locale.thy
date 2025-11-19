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
theory Ultrametric_Restriction_Spaces_Locale
  imports Restriction_Spaces.Restriction_Spaces_Locales Elementary_Ultrametric_Spaces
begin
  (*>*)

subsection \<open>Preliminaries on strictly decreasing Sequences\<close>

abbreviation strict_decseq :: \<open>(nat \<Rightarrow> 'a :: order) \<Rightarrow> bool\<close>
  where \<open>strict_decseq \<equiv> monotone (<) (\<lambda>x y. y < x)\<close>

lemma strict_decseq_def : \<open>strict_decseq X \<longleftrightarrow> (\<forall>m n. m < n \<longrightarrow> X n < X m)\<close>
  by (fact monotone_def)

lemma strict_decseqI : \<open>strict_decseq X\<close> if \<open>\<And>n. X (Suc n) < X n\<close>
  by (metis Suc_le_eq decseqD decseq_Suc_iff le_less_trans nless_le strict_decseq_def that)

lemma strict_decseqD : \<open>strict_decseq X \<Longrightarrow> m < n \<Longrightarrow> X n < X m\<close>
  using strict_decseq_def by blast

lemma strict_decseq_def_bis : \<open>strict_decseq X \<longleftrightarrow> (\<forall>m n. X n < X m \<longleftrightarrow> m < n)\<close>
  by (metis linorder_less_linear order_less_imp_not_less strict_decseq_def)

lemma strict_decseq_def_ter : \<open>strict_decseq X \<longleftrightarrow> (\<forall>m n. X n \<le> X m \<longleftrightarrow> m \<le> n)\<close>
  unfolding strict_decseq_def_bis
  by (rule iffI, metis le_simps(2) order_le_less, simp add: less_le_not_le)

lemma strict_decseq_imp_decseq : \<open>strict_decseq \<sigma> \<Longrightarrow> decseq \<sigma>\<close>
  by (simp add: monotone_on_def order_le_less)


lemma strict_decseq_SucI : \<open>(\<And>n. X (Suc n) < X n) \<Longrightarrow> strict_decseq X\<close>
  by (metis Suc_le_eq decseqD decseq_Suc_iff less_le_not_le order_less_le strict_decseq_def)

lemma strict_decseq_SucD : \<open>strict_decseq A \<Longrightarrow> A (Suc i) < A i\<close>
  by (simp add: strict_decseq_def)



text \<open>
Classically, a restriction space is given the structure of a metric space by defining
\<open>dist x y \<equiv> Inf {(1 / 2) ^ n| n. x \<down> n = y \<down> n}\<close>.
This obviously also works if we replace \<^term>\<open>1 / 2 :: real\<close> by any real \<^term>\<open>\<delta>\<close>
such that \<^term>\<open>0 < (\<delta> :: real)\<close> and \<^term>\<open>(\<delta> :: real) < 1\<close>.
But more generally, this still works if we set
\<open>dist x y \<equiv> Inf {\<sigma> n| n. x \<down> n = y \<down> n}\<close> where \<^term>\<open>\<sigma>\<close> is a sequence of \<^typ>\<open>real\<close>
verifying \<^term>\<open>\<forall>n. 0 < (\<sigma> :: nat \<Rightarrow> real) n\<close> and \<^term>\<open>\<sigma> \<longlonglongrightarrow> 0\<close>.
As you would expect, the more structure you have, the more powerful theorems you get.
We explore all these variants in the theory below.
\<close>

subsection \<open>The Construction with Locales\<close>

text \<open>Our formalization will extend the class \<^class>\<open>metric_space\<close>.
      But some proofs are redundant, especially when it comes to the product type.
      So first we will be working with locales, and interpret them with the classes.\<close>

locale NonDecseqRestrictionSpace = PreorderRestrictionSpace +
  \<comment>\<open>Factorization of the proof work.\<close>
  fixes M :: \<open>'a set\<close> and restriction_\<sigma> :: \<open>nat \<Rightarrow> real\<close> (\<open>\<sigma>\<^sub>\<down>\<close>)
    and restriction_dist :: \<open>'a \<Rightarrow> 'a \<Rightarrow> real\<close> (\<open>dist\<^sub>\<down>\<close>)
  assumes restriction_\<sigma>_tendsto_zero : \<open>restriction_\<sigma> \<longlonglongrightarrow> 0\<close>
    and zero_less_restriction_\<sigma> [simp] : \<open>0 < restriction_\<sigma> n\<close>
    and dist_restriction_is :
    \<open>dist\<^sub>\<down> x y = (INF n \<in> restriction_related_set x y. restriction_\<sigma> n)\<close>
begin

lemma zero_le_restriction_\<sigma> [simp] : \<open>0 \<le> \<sigma>\<^sub>\<down> n\<close> 
  by (simp add: order_less_imp_le)

lemma restriction_\<sigma>_neq_zero [simp] : \<open>\<sigma>\<^sub>\<down> n \<noteq> 0\<close> 
  by (metis zero_less_restriction_\<sigma> order_less_irrefl)


(* lemma eventually_inf_to:
  \<open>r \<longlonglongrightarrow> k \<Longrightarrow> \<forall>e>0. k \<in> ball k (k + e) \<longrightarrow> (\<forall>\<^sub>F n in sequentially. r n \<in> ball k (k + e))\<close>
  unfolding eventually_sequentially inj_on_def
  using lim_explicit by blast *)


lemma bounded_range_restriction_\<sigma>: \<open>bounded (range \<sigma>\<^sub>\<down>)\<close>
  by (fact convergent_imp_bounded[OF restriction_\<sigma>_tendsto_zero])

abbreviation restriction_\<sigma>_related_set :: \<open>'a \<Rightarrow> 'a \<Rightarrow> real set\<close>
  where \<open>restriction_\<sigma>_related_set x y \<equiv> \<sigma>\<^sub>\<down> ` restriction_related_set x y\<close>

abbreviation restriction_\<sigma>_not_related_set :: \<open>'a \<Rightarrow> 'a \<Rightarrow> real set\<close>
  where \<open>restriction_\<sigma>_not_related_set x y \<equiv> \<sigma>\<^sub>\<down> ` restriction_not_related_set x y\<close>

lemma nonempty_restriction_\<sigma>_related_set :
  \<open>restriction_\<sigma>_related_set x y \<noteq> {}\<close> by simp

lemma restriction_\<sigma>_related_set_Un_restriction_\<sigma>_not_related_set :
  \<open>restriction_\<sigma>_related_set x y \<union> restriction_\<sigma>_not_related_set x y = range \<sigma>\<^sub>\<down>\<close>
  by blast

lemma \<open>bdd_above (restriction_\<sigma>_related_set x y)\<close>
  by (meson bdd_above.I2 bdd_above.unfold bounded_imp_bdd_above
      bounded_range_restriction_\<sigma> rangeI)

lemma \<open>bdd_above (restriction_\<sigma>_not_related_set x y)\<close>
  by (meson bdd_above.E bdd_above.I2 bounded_imp_bdd_above
      bounded_range_restriction_\<sigma> range_eqI)

lemma bounded_restriction_\<sigma>_related_set: \<open>bounded (restriction_\<sigma>_related_set x y)\<close>
  by (meson bounded_range_restriction_\<sigma> bounded_subset image_mono top_greatest)

lemma bounded_restriction_\<sigma>_not_related_set: \<open>bounded (restriction_\<sigma>_not_related_set x y)\<close>
  by (meson bounded_range_restriction_\<sigma> bounded_subset image_mono subset_UNIV)

corollary restriction_space_Inf_properties:
  \<open>a \<in> restriction_\<sigma>_related_set x y \<Longrightarrow> dist\<^sub>\<down> x y \<le> a\<close>
  \<open>\<lbrakk>\<And>a. a \<in> restriction_\<sigma>_related_set x y \<Longrightarrow> b \<le> a\<rbrakk> \<Longrightarrow> b \<le> dist\<^sub>\<down> x y\<close>
  unfolding dist_restriction_is
  by (simp_all add: bounded_has_Inf(1) bounded_restriction_\<sigma>_related_set cInf_greatest)

lemma restriction_\<sigma>_related_set_alt :
  \<open>restriction_\<sigma>_related_set x y = {\<sigma>\<^sub>\<down> n| n. n \<in> restriction_related_set x y}\<close>
  by blast


lemma exists_less_restriction_\<sigma> : \<open>\<exists>n. m < n \<and> \<sigma>\<^sub>\<down> n < \<sigma>\<^sub>\<down> m\<close>
proof (rule ccontr)
  assume \<open>\<not> (\<exists>n>m. \<sigma>\<^sub>\<down> n < \<sigma>\<^sub>\<down> m)\<close>
  hence \<open>\<forall>n\<ge>m. \<sigma>\<^sub>\<down> m \<le> \<sigma>\<^sub>\<down> n\<close>
    by (metis linorder_not_le nle_le)
  hence \<open>\<not> \<sigma>\<^sub>\<down> \<longlonglongrightarrow> 0\<close>
    by (meson Lim_bounded2 linorder_not_le zero_less_restriction_\<sigma>)
  with restriction_\<sigma>_tendsto_zero show False by simp
qed


lemma \<open>dist\<^sub>\<down> x y = Inf (restriction_\<sigma>_related_set x y)\<close>
  by (fact dist_restriction_is)


lemma not_related_imp_dist_restriction_is_some_restriction_\<sigma> :
  \<open>\<exists>n. dist\<^sub>\<down> x y = \<sigma>\<^sub>\<down> n \<and> (\<forall>m\<le>n. x \<down> m \<lessapprox> y \<down> m) \<close> if \<open>\<not> x \<lessapprox> y\<close>
proof -
  have \<open>finite (restriction_related_set x y)\<close>
    by (simp add: finite_restriction_related_set_iff \<open>\<not> x \<lessapprox> y\<close>)
  have \<open>Inf (restriction_\<sigma>_related_set x y) \<in> restriction_\<sigma>_related_set x y\<close>
    by (rule closed_contains_Inf[OF nonempty_restriction_\<sigma>_related_set])
      (simp_all add: \<open>finite (restriction_related_set x y)\<close> finite_imp_closed)
  hence \<open>dist\<^sub>\<down> x y \<in> restriction_\<sigma>_related_set x y\<close>
    by (fold dist_restriction_is)
  with restriction_related_le obtain n
    where \<open>n \<in> restriction_related_set x y\<close> \<open>dist\<^sub>\<down> x y = \<sigma>\<^sub>\<down> n\<close>
      \<open>\<forall>m\<le>n. x \<down> m \<lessapprox> y \<down> m\<close>  by blast
  with \<open>dist\<^sub>\<down> x y \<in> restriction_\<sigma>_related_set x y\<close> show ?thesis by blast
qed


lemma not_related_imp_dist_restriction_le_some_restriction_\<sigma> :
  \<open>\<not> x \<lessapprox> y \<Longrightarrow> \<exists>n. dist\<^sub>\<down> x y \<le> \<sigma>\<^sub>\<down> n \<and> (\<not> x \<down> Suc n \<lessapprox> y \<down> Suc n) \<and> (\<forall>m\<le>n. x \<down> m \<lessapprox> y \<down> m)\<close>
  by (blast intro: restriction_space_Inf_properties
      dest: ex_not_restriction_related_optimized)


lemma restriction_dist_eq_0_iff_related : \<open>dist\<^sub>\<down> x y = 0 \<longleftrightarrow> x \<lessapprox> y\<close>
proof (rule iffI)
  show \<open>dist\<^sub>\<down> x y = 0 \<Longrightarrow> x \<lessapprox> y\<close>
    by (erule contrapos_pp)
      (auto dest: not_related_imp_dist_restriction_is_some_restriction_\<sigma>)
next
  show \<open>dist\<^sub>\<down> x y = 0\<close> if \<open>x \<lessapprox> y\<close>
  proof (rule order_antisym)
    show \<open>0 \<le> dist\<^sub>\<down> x y\<close> by (simp add: cINF_greatest dist_restriction_is)
  next
    define \<Delta> where \<open>\<Delta> n \<equiv> - \<sigma>\<^sub>\<down> n\<close> for n
    have * : \<open>\<Delta> n \<le> - dist\<^sub>\<down> x y\<close> for n
      unfolding \<Delta>_def using \<open>x \<lessapprox> y\<close> restriction_space_Inf_properties(1)
      by simp (metis UNIV_restriction_related_set_iff rangeI)
    from restriction_\<sigma>_tendsto_zero tendsto_minus_cancel_left
    have \<open>\<Delta> \<longlonglongrightarrow> 0\<close> unfolding \<Delta>_def by force
    from lim_le[OF convergentI[OF \<open>\<Delta> \<longlonglongrightarrow> 0\<close>] "*"] limI[OF \<open>\<Delta> \<longlonglongrightarrow> 0\<close>]
    show \<open>dist\<^sub>\<down> x y \<le> 0\<close> by simp
  qed
qed


end


locale DecseqRestrictionSpace = NonDecseqRestrictionSpace +
  assumes decseq_restriction_\<sigma> : \<open>decseq \<sigma>\<^sub>\<down>\<close>
begin

lemma dist_restriction_is_bis :
  \<open>dist\<^sub>\<down> x y = (if x \<lessapprox> y then 0 else \<sigma>\<^sub>\<down> (Sup (restriction_related_set x y)))\<close>
  if \<open>x \<in> M\<close> and \<open>y \<in> M\<close>
proof (split if_split, intro conjI impI)
  from \<open>x \<in> M\<close> and \<open>y \<in> M\<close> show \<open>x \<lessapprox> y \<Longrightarrow> restriction_dist x y = 0\<close>
    by (simp add: restriction_dist_eq_0_iff_related)
next
  show \<open>dist\<^sub>\<down> x y = \<sigma>\<^sub>\<down> (Sup (restriction_related_set x y))\<close> if \<open>\<not> x \<lessapprox> y\<close>
  proof (rule order_antisym)
    show \<open>dist\<^sub>\<down> x y \<le> \<sigma>\<^sub>\<down> (Sup (restriction_related_set x y))\<close>
      unfolding dist_restriction_is
      by (rule cINF_lower[OF _ Sup_in_restriction_related_set[OF \<open>\<not> x \<lessapprox> y\<close>]])
        (meson bdd_below.I2 zero_le_restriction_\<sigma>)
  next
    show \<open>\<sigma>\<^sub>\<down> (Sup (restriction_related_set x y)) \<le> dist\<^sub>\<down> x y\<close>
    proof (unfold dist_restriction_is, rule cINF_greatest)
      show \<open>restriction_related_set x y \<noteq> {}\<close> by (fact nonempty_restriction_related_set)
    next
      fix n assume \<open>n \<in> restriction_related_set x y\<close>
      hence \<open>n \<le> Sup (restriction_related_set x y)\<close>
        by (metis \<open>n \<in> restriction_related_set x y\<close> le_cSup_finite
            finite_restriction_related_set_iff \<open>\<not> x \<lessapprox> y\<close>)
      from decseqD[OF decseq_restriction_\<sigma> this]
      show \<open>restriction_\<sigma> (Sup (restriction_related_set x y)) \<le> restriction_\<sigma> n\<close> .
    qed
  qed
qed


lemma not_eq_imp_dist_restriction_is_restriction_\<sigma>_Sup_restriction_eq :
  \<open>dist\<^sub>\<down> x y = \<sigma>\<^sub>\<down> (Sup (restriction_related_set x y))\<close>
  \<open>\<forall>m\<le>Sup (restriction_related_set x y). x \<down> m \<lessapprox> y \<down> m\<close>
  \<open>\<forall>m>Sup (restriction_related_set x y). \<not> x \<down> m \<lessapprox> y \<down> m\<close>
  if \<open>\<not> x \<lessapprox> y\<close> and \<open>x \<in> M\<close> and \<open>y \<in> M\<close>
  subgoal by (subst dist_restriction_is_bis; simp add: \<open>\<not> x \<lessapprox> y\<close> \<open>x \<in> M\<close> \<open>y \<in> M\<close>)
  subgoal using Sup_in_restriction_related_set[OF \<open>\<not> x \<lessapprox> y\<close>] restriction_related_le by blast
  using cSup_upper[OF _ bdd_above_restriction_related_set_iff[THEN iffD2, OF \<open>\<not> x \<lessapprox> y\<close>],
      of \<open>Suc (Sup (restriction_related_set x y))\<close>]
  by (metis (mono_tags, lifting) Suc_leI dual_order.refl mem_Collect_eq not_less_eq_eq restriction_related_le)



theorem restriction_dist_tendsto_zero_independent_of_restriction_\<sigma> :
  \<comment>\<open>Very powerful theorem: the convergence of the distance to \<^term>\<open>0 :: real\<close>
     is actually independent from the restriction sequence chosen.\<close>
  \<comment>\<open>This is the theorem for which we had to work with locales first.\<close>

assumes \<open>DecseqRestrictionSpace (\<down>) (\<lessapprox>) restriction_\<sigma>' restriction_dist'\<close>
  and \<open>\<Sigma> \<in> M\<close> and \<open>range \<sigma> \<subseteq> M\<close>
shows \<open>(\<lambda>n. dist\<^sub>\<down> (\<sigma> n) \<Sigma>) \<longlonglongrightarrow> 0 \<longleftrightarrow> (\<lambda>n. restriction_dist' (\<sigma> n) \<Sigma>) \<longlonglongrightarrow> 0\<close>
proof -
  { fix restriction_\<sigma> restriction_dist restriction_\<sigma>' restriction_dist'
    assume a1 : \<open>DecseqRestrictionSpace (\<down>) (\<lessapprox>) restriction_\<sigma>  restriction_dist \<close>
      and a2 : \<open>DecseqRestrictionSpace (\<down>) (\<lessapprox>) restriction_\<sigma>' restriction_dist'\<close>
      and  * : \<open>(\<lambda>n. restriction_dist (\<sigma> n) \<Sigma>) \<longlonglongrightarrow> 0\<close>

    interpret i1 : DecseqRestrictionSpace \<open>(\<down>)\<close> \<open>(\<lessapprox>)\<close> M restriction_\<sigma>  restriction_dist  by (fact a1)
    interpret i2 : DecseqRestrictionSpace \<open>(\<down>)\<close> \<open>(\<lessapprox>)\<close> M restriction_\<sigma>' restriction_dist' by (fact a2)



    have \<open>(\<lambda>n. restriction_dist' (\<sigma> n) \<Sigma>) \<longlonglongrightarrow> 0\<close>
    proof (rule metric_LIMSEQ_I)
      fix \<epsilon> :: real assume \<open>0 < \<epsilon>\<close>

      from metric_LIMSEQ_D[OF i2.restriction_\<sigma>_tendsto_zero \<open>0 < \<epsilon>\<close>]
      obtain N where ** : \<open>N \<le> n \<Longrightarrow> restriction_\<sigma>' n < \<epsilon>\<close> for n by auto

      fix N' :: nat

      have \<open>\<exists>N'. \<forall>n\<ge>N'. N \<in> restriction_related_set (\<sigma> n) \<Sigma>\<close>
      proof (rule ccontr)
        assume \<open>\<nexists>N'. \<forall>n\<ge>N'. N \<in> restriction_related_set (\<sigma> n) \<Sigma>\<close>
        hence *** : \<open>\<forall>N'. \<exists>n\<ge>N'. \<not> \<sigma> n \<down> N \<lessapprox> \<Sigma> \<down> N\<close> by simp
        have **** : \<open>\<forall>N'. \<exists>n\<ge>N'. restriction_\<sigma> N \<le> restriction_dist (\<sigma> n) \<Sigma>\<close>
        proof (rule allI)
          fix N' :: nat
          from "***" obtain n where \<open>N' \<le> n\<close> \<open>\<not> \<sigma> n \<down> N \<lessapprox> \<Sigma> \<down> N\<close> by blast
          hence \<open>\<not> \<sigma> n \<lessapprox> \<Sigma>\<close> using mono_restriction_related by blast
          have \<open>restriction_\<sigma> N \<le> restriction_dist (\<sigma> n) \<Sigma>\<close>
          proof (subst i1.dist_restriction_is_bis)
            show \<open>\<sigma> n \<in> M\<close> \<open>\<Sigma> \<in> M\<close>
              by (simp_all add: assms(2, 3) range_subsetD)
          next
            show \<open>restriction_\<sigma> N \<le> (if \<sigma> n \<lessapprox> \<Sigma> then 0
                  else restriction_\<sigma> (Sup (restriction_related_set (\<sigma> n) \<Sigma>)))\<close>
              using \<open>\<not> \<sigma> n \<lessapprox> \<Sigma>\<close> \<open>\<not> \<sigma> n \<down> N \<lessapprox> \<Sigma> \<down> N\<close> assms(2, 3) nle_le
                not_eq_imp_dist_restriction_is_restriction_\<sigma>_Sup_restriction_eq(2)
              by (fastforce intro: decseqD[OF i1.decseq_restriction_\<sigma>])
          qed
          with \<open>N' \<le> n\<close> show \<open>\<exists>n\<ge>N'. restriction_\<sigma> N \<le> restriction_dist (\<sigma> n) \<Sigma>\<close> by blast
        qed
        from metric_LIMSEQ_D[OF "*", of \<open>restriction_\<sigma> N\<close>]
        have \<open>\<exists>N''. \<forall>n\<ge>N''. restriction_dist (\<sigma> n) \<Sigma> < restriction_\<sigma> N\<close>
          by (metis abs_of_nonneg i1.zero_le_restriction_\<sigma> i1.zero_less_restriction_\<sigma> norm_conv_dist order_trans real_norm_def
              verit_comp_simplify1(3))
        with "****" show False by fastforce
      qed

      then obtain N' where *** : \<open>N' \<le> n \<Longrightarrow> N \<in> restriction_related_set (\<sigma> n) \<Sigma>\<close> for n by blast
      have \<open>restriction_dist' (\<sigma> n) \<Sigma> < \<epsilon>\<close> if \<open>N' \<le> n\<close> for n
      proof (rule le_less_trans[OF i2.restriction_space_Inf_properties(1), of \<open>restriction_\<sigma>' N\<close>])
        from \<open>N' \<le> n\<close> "***"
        show \<open>restriction_\<sigma>' N \<in> i2.restriction_\<sigma>_related_set (\<sigma> n) \<Sigma>\<close> by blast
      next
        show \<open>restriction_\<sigma>' N < \<epsilon>\<close> by (simp add: "**")
      qed
      thus \<open>\<exists>N. \<forall>n\<ge>N. dist (restriction_dist' (\<sigma> n) \<Sigma>) 0 < \<epsilon>\<close>
        by (metis abs_of_nonneg dist_0_norm dist_commute i2.not_related_imp_dist_restriction_is_some_restriction_\<sigma>
            i2.restriction_dist_eq_0_iff_related i2.zero_less_restriction_\<sigma> order_less_imp_not_less real_norm_def
            verit_comp_simplify1(3))
    qed }
  note * = this

  show \<open>(\<lambda>n. dist\<^sub>\<down> (\<sigma> n) \<Sigma>) \<longlonglongrightarrow> 0 = (\<lambda>n. restriction_dist' (\<sigma> n) \<Sigma>) \<longlonglongrightarrow> 0\<close>
    using "*" DecseqRestrictionSpace_axioms assms(1) by blast
qed

end


(*<*)
end
  (*>*)