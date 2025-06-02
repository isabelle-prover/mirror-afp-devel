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


section \<open>Ultrametric Structure of restriction Spaces\<close>

(*<*)
theory Ultrametric_Restriction_Spaces
  imports Ultrametric_Restriction_Spaces_Locale
    Restriction_Spaces Banach_Theorem_Extension
begin
  (*>*)



text \<open>This has only be proven with the sort constraint,
      not inside the context of the class \<^class>\<open>metric_space\<close> ...\<close>

context metric_space begin

lemma LIMSEQ_def : \<open>X \<longlonglongrightarrow> L \<longleftrightarrow> (\<forall>r>0. \<exists>no. \<forall>n\<ge>no. dist (X n) L < r)\<close>
  unfolding tendsto_iff eventually_sequentially ..

lemma LIMSEQ_iff_nz: \<open>X \<longlonglongrightarrow> L \<longleftrightarrow> (\<forall>r>0. \<exists>no>0. \<forall>n\<ge>no. dist (X n) L < r)\<close>
  by (meson Suc_leD LIMSEQ_def zero_less_Suc)

lemma metric_LIMSEQ_I: \<open>(\<And>r. 0 < r \<Longrightarrow> \<exists>no. \<forall>n\<ge>no. dist (X n) L < r) \<Longrightarrow> X \<longlonglongrightarrow> L\<close>
  by (simp add: LIMSEQ_def)

lemma metric_LIMSEQ_D: \<open>X \<longlonglongrightarrow> L \<Longrightarrow> 0 < r \<Longrightarrow> \<exists>no. \<forall>n\<ge>no. dist (X n) L < r\<close>
  by (simp add: LIMSEQ_def)



lemma LIMSEQ_dist_iff:
  \<open>f \<longlonglongrightarrow> l \<longleftrightarrow> (\<lambda>x. dist (f x) l) \<longlonglongrightarrow> 0\<close>
proof (unfold LIMSEQ_def, rule iffI)
  show \<open>(\<lambda>n. dist (f n) l) \<longlonglongrightarrow> 0 \<Longrightarrow> (\<forall>r>0. \<exists>no. \<forall>n\<ge>no. dist (f n) l < r)\<close>
    by (metis (mono_tags, lifting) eventually_at_top_linorder order_tendstoD(2))
next
  show \<open>\<forall>r>0. \<exists>no. \<forall>n\<ge>no. dist (f n) l < r \<Longrightarrow> (\<lambda>n. dist (f n) l) \<longlonglongrightarrow> 0\<close>
    by (simp add: metric_space_class.LIMSEQ_def)
qed


lemma Cauchy_converges_subseq:
  fixes u::"nat \<Rightarrow> 'a"
  assumes "Cauchy u"
    "strict_mono r"
    "(u \<circ> r) \<longlonglongrightarrow> l"
  shows "u \<longlonglongrightarrow> l"
proof -
  have *: "eventually (\<lambda>n. dist (u n) l < e) sequentially" if "e > 0" for e
  proof -
    have "e/2 > 0" using that by auto
    then obtain N1 where N1: "\<And>m n. m \<ge> N1 \<Longrightarrow> n \<ge> N1 \<Longrightarrow> dist (u m) (u n) < e/2"
      using \<open>Cauchy u\<close> unfolding Cauchy_def by blast
    obtain N2 where N2: "\<And>n. n \<ge> N2 \<Longrightarrow> dist ((u \<circ> r) n) l < e / 2"
      using order_tendstoD(2)[OF iffD1[OF LIMSEQ_dist_iff \<open>(u \<circ> r) \<longlonglongrightarrow> l\<close>] \<open>e/2 > 0\<close>]
      unfolding eventually_sequentially by auto
    have "dist (u n) l < e" if "n \<ge> max N1 N2" for n
    proof -
      have "dist (u n) l \<le> dist (u n) ((u \<circ> r) n) + dist ((u \<circ> r) n) l"
        by (rule dist_triangle)
      also have "\<dots> < e/2 + e/2"
      proof (intro add_strict_mono)
        show "dist (u n) ((u \<circ> r) n) < e / 2"
          using N1[of n "r n"] N2[of n] that unfolding comp_def
          by (meson assms(2) le_trans max.bounded_iff strict_mono_imp_increasing)
        show "dist ((u \<circ> r) n) l < e / 2"
          using N2 that by auto
      qed
      finally show ?thesis by simp
    qed 
    then show ?thesis unfolding eventually_sequentially by blast
  qed
  have "(\<lambda>n. dist (u n) l) \<longlonglongrightarrow> 0"
    by (simp add: less_le_trans * order_tendstoI)
  then show ?thesis using LIMSEQ_dist_iff by auto
qed


end




subsection \<open>The Construction with Classes\<close>

class restriction_\<sigma> = restriction_space +
  fixes restriction_\<sigma> :: \<open>'a itself \<Rightarrow> nat \<Rightarrow> real\<close> (\<open>\<sigma>\<^sub>\<down>\<close>)


setup \<open>Sign.add_const_constraint (\<^const_name>\<open>dist\<close>, NONE)\<close>
  \<comment> \<open>To be able to use \<^const>\<open>dist\<close> out of the \<^class>\<open>metric_space\<close> class.\<close>


class non_decseq_restriction_space =
  uniformity_dist + open_uniformity + restriction_\<sigma> +
  \<comment>\<open>We do not assume the restriction sequence to be \<^const>\<open>decseq\<close> yet.\<close>
  assumes restriction_\<sigma>_tendsto_zero' : \<open>\<sigma>\<^sub>\<down> TYPE('a) \<longlonglongrightarrow> 0\<close> 
    and zero_less_restriction_\<sigma>' [simp] : \<open>0 < \<sigma>\<^sub>\<down> TYPE('a) n\<close>
    (* and decseq_restriction_\<sigma> : \<open>decseq (\<sigma>\<^sub>\<down> TYPE('a))\<close> *)
    and dist_restriction_is' : \<open>dist x y = (INF n \<in> {n. x \<down> n = y \<down> n}. \<sigma>\<^sub>\<down> TYPE('a) n)\<close>
begin 

sublocale NonDecseqRestrictionSpace \<open>(\<down>)\<close> \<open>(=)\<close> \<open>UNIV\<close> \<open>\<sigma>\<^sub>\<down> TYPE ('a)\<close> dist
  by unfold_locales (simp_all add: restriction_\<sigma>_tendsto_zero' dist_restriction_is')

end

setup \<open>Sign.add_const_constraint (\<^const_name>\<open>dist\<close>, SOME \<^typ>\<open>'a :: metric_space \<Rightarrow> 'a \<Rightarrow> real\<close>)\<close>
  \<comment> \<open>Only allow \<^const>\<open>dist\<close> in class \<^class>\<open>metric_space\<close> (back to normal).\<close>

text \<open>We hide duplicated facts
@{thm restriction_\<sigma>_tendsto_zero zero_less_restriction_\<sigma> dist_restriction_is}.\<close>
hide_fact restriction_\<sigma>_tendsto_zero' zero_less_restriction_\<sigma>' dist_restriction_is'


context non_decseq_restriction_space begin

subclass ultrametric_space
proof unfold_locales
  show \<open>dist x y = 0 \<longleftrightarrow> x = y\<close> for x y
    by (simp add: "restriction_dist_eq_0_iff_related")

  have dist_commute : \<open>dist x y = dist y x\<close> for x y
    by (simp add: dist_restriction_is) metis

  show \<open>dist x y \<le> max (dist x z) (dist y z)\<close> for x y z
  proof -
    consider \<open>x \<noteq> y\<close> and \<open>y \<noteq> z\<close> and \<open>x \<noteq> z\<close> | \<open>x = y \<or> y = z \<or> x = z\<close> by blast

    thus \<open>dist x y \<le> max (dist x z) (dist y z)\<close>
    proof cases
      assume \<open>x \<noteq> y\<close> and \<open>y \<noteq> z\<close> and \<open>x \<noteq> z\<close>
      from this(1)[THEN not_related_imp_dist_restriction_le_some_restriction_\<sigma>]
        this(2, 3)[THEN not_related_imp_dist_restriction_is_some_restriction_\<sigma>]
      obtain l m n
        where   * : \<open>dist x y \<le> \<sigma>\<^sub>\<down> TYPE('a) l\<close> \<open>x \<down> Suc l \<noteq> y \<down> Suc l\<close>
          and  ** : \<open>dist y z = \<sigma>\<^sub>\<down> TYPE('a) m\<close> \<open>\<forall>k\<le>m. y \<down> k = z \<down> k\<close>
          and *** : \<open>dist x z = \<sigma>\<^sub>\<down> TYPE('a) n\<close> \<open>\<forall>k\<le>n. x \<down> k = z \<down> k\<close> by blast
      have \<open>min n m \<le> l\<close>
      proof (rule ccontr)
        assume \<open>\<not> min n m \<le> l\<close>
        hence \<open>Suc l \<le> n\<close> and \<open>Suc l \<le> m\<close> by simp_all
        with "**"(2) "***"(2) Suc_le_lessD
        have \<open>x \<down> Suc l = z \<down> Suc l\<close> \<open>y \<down> Suc l = z \<down> Suc l\<close> by simp_all
        hence \<open>x \<down> Suc l = y \<down> Suc l\<close> by simp
        with \<open>x \<down> Suc l \<noteq> y \<down> Suc l\<close> show False ..
      qed

      have \<open>dist x y \<le> \<sigma>\<^sub>\<down> TYPE('a) (min n m)\<close>
        by (rule restriction_space_Inf_properties(1))
          (simp add: "**"(2) "***"(2))
      also have \<open>\<dots> \<le> max (dist x z) (dist y z)\<close>
        unfolding "**"(1) "***"(1) by linarith
      finally show \<open>dist x y \<le> max (dist x z) (dist y z)\<close> .
    next
      show \<open>x = y \<or> y = z \<or> x = z \<Longrightarrow> dist x y \<le> max (dist x z) (dist y z)\<close>
        by (elim disjE, simp_all add: dist_commute)
          (metis not_related_imp_dist_restriction_is_some_restriction_\<sigma>
            restriction_dist_eq_0_iff_related zero_le_restriction_\<sigma> dual_order.refl)
    qed
  qed
qed

end

context non_decseq_restriction_space begin


lemma restriction_tendsto_self: \<open>(\<lambda>n. x \<down> n) \<longlonglongrightarrow> x\<close>
proof -
  have \<open>(\<lambda>n. dist (x \<down> n) x) \<longlonglongrightarrow> 0\<close>
  proof (rule real_tendsto_sandwich[OF _ ])
    show \<open>\<forall>\<^sub>F n in sequentially. 0 \<le> dist (x \<down> n) x\<close> by simp
  next
    show \<open>\<forall>\<^sub>F n in sequentially. dist (x \<down> n) x \<le> \<sigma>\<^sub>\<down> TYPE('a) n\<close>
      by (auto intro: eventually_sequentiallyI[OF restriction_space_Inf_properties(1)])
  next
    show \<open>(\<lambda>n. 0) \<longlonglongrightarrow> 0\<close> by simp
  next
    show \<open>\<sigma>\<^sub>\<down> TYPE('a) \<longlonglongrightarrow> 0\<close> by (simp add: restriction_\<sigma>_tendsto_zero)
  qed
  thus \<open>(\<lambda>n. x \<down> n) \<longlonglongrightarrow> x\<close>
    by (subst tendsto_iff[of \<open>(\<lambda>n. x \<down> n)\<close>], subst eventually_sequentially)
      (simp add: LIMSEQ_iff)
qed

end





class decseq_restriction_space = non_decseq_restriction_space +
  assumes decseq_restriction_\<sigma>' : \<open>decseq (\<sigma>\<^sub>\<down> TYPE('a))\<close>
begin

sublocale DecseqRestrictionSpace \<open>(\<down>)\<close> \<open>(=)\<close> \<open>UNIV :: 'a set\<close>
  \<open>restriction_\<sigma> TYPE('a)\<close> dist
  by unfold_locales (simp add: decseq_restriction_\<sigma>')


\<comment> \<open>Removing \<^term>\<open>x \<in> M\<close> and \<^term>\<open>y \<in> M\<close>.\<close>
lemmas dist_restriction_is_bis_simplified = dist_restriction_is_bis[simplified]
  and not_eq_imp_dist_restriction_is_restriction_\<sigma>_Sup_restriction_eq_simplified =
  not_eq_imp_dist_restriction_is_restriction_\<sigma>_Sup_restriction_eq[simplified]

end

text \<open>We hide duplicated fact @{thm decseq_restriction_\<sigma>}.\<close>
hide_fact decseq_restriction_\<sigma>'



class strict_decseq_restriction_space = non_decseq_restriction_space +
  assumes strict_decseq_restriction_\<sigma> : \<open>strict_decseq (\<sigma>\<^sub>\<down> TYPE('a))\<close>
begin

subclass decseq_restriction_space
  by unfold_locales
    (fact strict_decseq_imp_decseq[OF strict_decseq_restriction_\<sigma>])

end




text \<open>Generic Properties\<close>


lemma (in metric_space) dist_sequences_tendsto_zero_imp_tendsto_iff :
  \<open>(\<lambda>n. dist (\<sigma> n) (\<psi> n)) \<longlonglongrightarrow> 0 \<Longrightarrow> \<sigma> \<longlonglongrightarrow> \<Sigma> \<longleftrightarrow> \<psi> \<longlonglongrightarrow> \<Sigma>\<close>
proof (rule iffI)
  show \<open>\<psi> \<longlonglongrightarrow> \<Sigma>\<close> if \<open>\<sigma> \<longlonglongrightarrow> \<Sigma>\<close> and \<open>(\<lambda>n. dist (\<sigma> n) (\<psi> n)) \<longlonglongrightarrow> 0\<close> for \<sigma> \<psi>
  proof -
    from that have * : \<open>(\<lambda>n. dist (\<sigma> n) (\<psi> n) + dist (\<sigma> n) \<Sigma>) \<longlonglongrightarrow> 0\<close>
      unfolding LIMSEQ_dist_iff using tendsto_add_zero by blast
    have \<open>(\<lambda>n. dist (\<psi> n) \<Sigma>) \<longlonglongrightarrow> 0\<close>
      by (rule real_tendsto_sandwich
          [of \<open>\<lambda>n. 0\<close> \<open>\<lambda>n. dist (\<psi> n) \<Sigma>\<close> _ \<open>\<lambda>n. dist (\<sigma> n) (\<psi> n) + dist (\<sigma> n) \<Sigma>\<close>])
        (simp_all add: "*" dist_triangle3)
    with LIMSEQ_dist_iff show \<open>\<psi> \<longlonglongrightarrow> \<Sigma>\<close> by blast
  qed
  thus \<open>(\<lambda>n. dist (\<sigma> n) (\<psi> n)) \<longlonglongrightarrow> 0 \<Longrightarrow> \<psi> \<longlonglongrightarrow> \<Sigma> \<Longrightarrow> \<sigma> \<longlonglongrightarrow> \<Sigma>\<close>
    by (simp add: dist_commute)
qed


lemma (in non_decseq_restriction_space) restricted_sequence_tendsto_iff :
  \<open>(\<lambda>n. \<sigma> n \<down> n) \<longlonglongrightarrow> \<Sigma> \<longleftrightarrow> \<sigma> \<longlonglongrightarrow> \<Sigma>\<close>
proof -
  have \<open>(\<lambda>n. dist (\<sigma> n \<down> n) (\<sigma> n)) \<longlonglongrightarrow> 0\<close>
  proof (unfold metric_space_class.LIMSEQ_def, intro allI impI)
    fix \<epsilon> :: real assume \<open>0 < \<epsilon>\<close>
    from restriction_\<sigma>_tendsto_zero[unfolded metric_space_class.LIMSEQ_def, rule_format, OF \<open>0 < \<epsilon>\<close>]
    obtain no where \<open>\<forall>n\<ge>no. \<sigma>\<^sub>\<down> TYPE('a) n < \<epsilon>\<close> 
      by (auto simp add: dist_real_def)
    have \<open>no \<le> n \<Longrightarrow> dist (dist (\<sigma> n \<down> n) (\<sigma> n)) 0 < \<epsilon>\<close> for n 
      by (simp, rule le_less_trans[OF restriction_space_Inf_properties(1)[of \<open>\<sigma>\<^sub>\<down> TYPE('a) n\<close>]])
        (simp, simp add: \<open>\<forall>n\<ge>no. \<sigma>\<^sub>\<down> TYPE('a) n < \<epsilon>\<close>)
    thus \<open>\<exists>no. \<forall>n\<ge>no. dist (dist (\<sigma> n \<down> n) (\<sigma> n)) 0 < \<epsilon>\<close> by blast
  qed

  thus \<open>(\<lambda>n. \<sigma> n \<down> n) \<longlonglongrightarrow> \<Sigma> \<longleftrightarrow> \<sigma> \<longlonglongrightarrow> \<Sigma>\<close> 
    by (simp add: dist_sequences_tendsto_zero_imp_tendsto_iff)
qed



lemma (in non_decseq_restriction_space) Cauchy_restriction_chain :
  \<open>Cauchy \<sigma>\<close> if \<open>chain\<^sub>\<down> \<sigma>\<close>
proof (rule metric_CauchyI)
  fix \<epsilon> :: real assume \<open>0 < \<epsilon>\<close>
  from LIMSEQ_D[OF restriction_\<sigma>_tendsto_zero \<open>0 < \<epsilon>\<close>, simplified]
  obtain M where \<open>\<sigma>\<^sub>\<down> TYPE('a) M < \<epsilon>\<close> by blast
  moreover have \<open>M \<le> m \<Longrightarrow> M \<le> n \<Longrightarrow> dist (\<sigma> m) (\<sigma> n) \<le> \<sigma>\<^sub>\<down> TYPE('a) M\<close> for m n
    by (rule restriction_space_Inf_properties(1), simp add: image_iff)
      (metis restriction_chain_def_ter \<open>chain\<^sub>\<down> \<sigma>\<close>)
  ultimately have \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. dist (\<sigma> m) (\<sigma> n) < \<epsilon>\<close>
    by (meson dual_order.strict_trans2)
  thus \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (\<sigma> m) (\<sigma> n) < \<epsilon>\<close> ..
qed




lemma (in non_decseq_restriction_space) restriction_tendsto_imp_tendsto :
  \<open>\<sigma> \<longlonglongrightarrow> \<Sigma>\<close> if \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
proof (rule metric_LIMSEQ_I)
  fix \<epsilon> :: real assume \<open>0 < \<epsilon>\<close>
  with restriction_\<sigma>_tendsto_zero[THEN LIMSEQ_D]
  obtain n0 where \<open>\<forall>k\<ge>n0. \<sigma>\<^sub>\<down> TYPE('a) k < \<epsilon>\<close> by auto
  hence \<open>\<sigma>\<^sub>\<down> TYPE('a) n0 < \<epsilon>\<close> by simp
  from restriction_tendstoD[OF \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>]
  obtain n1 where \<open>\<forall>k\<ge>n1. \<Sigma> \<down> n0 = \<sigma> k \<down> n0\<close> ..
  hence \<open>\<forall>k\<ge>n1. dist (\<sigma> k) \<Sigma> \<le> \<sigma>\<^sub>\<down> TYPE('a) n0\<close>
    by (simp add: restriction_space_Inf_properties(1))
  with \<open>\<sigma>\<^sub>\<down> TYPE('a) n0 < \<epsilon>\<close>
  have \<open>\<forall>k\<ge>n1. dist (\<sigma> k) \<Sigma> < \<epsilon>\<close> by (meson order_le_less_trans)
  thus \<open>\<exists>n1. \<forall>k\<ge>n1. dist (\<sigma> k) \<Sigma> < \<epsilon>\<close> ..
qed






text \<open>In Decseq Restriction Space\<close>

context decseq_restriction_space begin

lemma le_dist_to_restriction_eqE : 
  obtains k where \<open>n \<le> k\<close> \<open>\<And>x y :: 'a. dist x y \<le> \<sigma>\<^sub>\<down> TYPE('a) k \<Longrightarrow> x \<down> n = y \<down> n\<close>
proof -
  have \<open>\<exists>k\<ge>n. \<forall>x y :: 'a. dist x y \<le> \<sigma>\<^sub>\<down> TYPE('a) k \<longrightarrow> x \<down> n = y \<down> n\<close>
  proof (rule ccontr)
    assume \<open>\<not> (\<exists>k\<ge>n. \<forall>x y :: 'a. dist x y \<le> \<sigma>\<^sub>\<down> TYPE('a) k \<longrightarrow> x \<down> n = y \<down> n)\<close>
    hence \<open>\<forall>k\<ge>n. \<exists>x y :: 'a. dist x y \<le> \<sigma>\<^sub>\<down> TYPE('a) k \<and> x \<down> n \<noteq> y \<down> n\<close> by simp
    then obtain X Y :: \<open>nat \<Rightarrow> 'a\<close>
      where * : \<open>\<forall>k\<ge>n. dist (X k) (Y k) \<le> \<sigma>\<^sub>\<down> TYPE('a) k\<close>
        \<open>\<forall>k\<ge>n. X k \<down> n \<noteq> Y k \<down> n\<close> by metis
    moreover obtain n0 where \<open>\<forall>k\<ge>n0. \<sigma>\<^sub>\<down> TYPE('a) k < \<sigma>\<^sub>\<down> TYPE('a) n\<close>
      by (metis LIMSEQ_D zero_less_restriction_\<sigma> abs_of_nonneg diff_zero
          restriction_\<sigma>_tendsto_zero real_norm_def zero_le_restriction_\<sigma>)
    ultimately have \<open>\<forall>k\<ge>n+n0. dist (X k) (Y k) < \<sigma>\<^sub>\<down> TYPE('a) n\<close>
      by (metis dual_order.strict_trans2 add_leE)
    moreover from "*"(2) have \<open>\<forall>k\<ge>n. \<sigma>\<^sub>\<down> TYPE('a) n \<le> dist (X k) (Y k)\<close>
      by (simp add: dist_restriction_is_bis)
        (metis (full_types) decseq_restriction_\<sigma>[THEN decseqD] linorder_linear
          not_eq_imp_dist_restriction_is_restriction_\<sigma>_Sup_restriction_eq_simplified(2))
    ultimately show False by (metis le_add1 linorder_not_le order_refl)
  qed
  thus \<open>(\<And>k. \<lbrakk>n \<le> k; \<And>x y :: 'a. dist x y \<le> \<sigma>\<^sub>\<down> TYPE('a) k \<Longrightarrow> x \<down> n = y \<down> n\<rbrakk>
        \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> by blast
qed



theorem tendsto_iff_restriction_tendsto : \<open>\<sigma> \<longlonglongrightarrow> \<Sigma> \<longleftrightarrow> \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
proof (rule iffI)
  show \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<Longrightarrow> \<sigma> \<longlonglongrightarrow> \<Sigma>\<close> by (fact restriction_tendsto_imp_tendsto)
next
  show \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> if \<open>\<sigma> \<longlonglongrightarrow> \<Sigma>\<close>
  proof (rule restriction_tendstoI)
    fix n
    obtain n0 where \<open>dist x y \<le> \<sigma>\<^sub>\<down> TYPE('a) n0 \<Longrightarrow> x \<down> n = y \<down> n\<close> for x y :: 'a
      by (metis le_dist_to_restriction_eqE)
    moreover from metric_LIMSEQ_D[OF \<open>\<sigma> \<longlonglongrightarrow> \<Sigma>\<close> zero_less_restriction_\<sigma>]
    obtain n1 where \<open>\<forall>k\<ge>n1. dist (\<sigma> k) \<Sigma> < \<sigma>\<^sub>\<down> TYPE('a) n0\<close> ..
    ultimately have \<open>\<forall>k\<ge>n1. \<Sigma> \<down> n = \<sigma> k \<down> n\<close> by (metis dual_order.order_iff_strict)
    thus \<open>\<exists>n1. \<forall>k\<ge>n1. \<Sigma> \<down> n = \<sigma> k \<down> n\<close> ..
  qed
qed

corollary convergent_iff_restriction_convergent : \<open>convergent \<sigma> \<longleftrightarrow> convergent\<^sub>\<down> \<sigma>\<close>
  by (simp add: convergent_def restriction_convergent_def tendsto_iff_restriction_tendsto)



theorem complete_iff_restriction_complete :
  \<open>(\<forall>\<sigma>. Cauchy \<sigma> \<longrightarrow> convergent \<sigma>) \<longleftrightarrow> (\<forall>\<sigma>. chain\<^sub>\<down> \<sigma> \<longrightarrow> convergent\<^sub>\<down> \<sigma>)\<close>
  \<comment> \<open>The following result shows that we have not lost anything with our
      definitions of convergence, completeness, etc. specific to restriction spaces.\<close>
proof (intro iffI impI allI)
  fix \<sigma> assume hyp : \<open>\<forall>\<sigma>. Cauchy \<sigma> \<longrightarrow> convergent \<sigma>\<close> and \<open>chain\<^sub>\<down> \<sigma>\<close>
  from Cauchy_restriction_chain \<open>chain\<^sub>\<down> \<sigma>\<close> have \<open>Cauchy \<sigma>\<close> by blast
  hence \<open>convergent \<sigma>\<close> by (simp add: hyp)
  thus \<open>convergent\<^sub>\<down> \<sigma>\<close> by (simp add: convergent_iff_restriction_convergent)
next
  fix \<sigma> assume hyp : \<open>\<forall>\<sigma>. chain\<^sub>\<down> \<sigma> \<longrightarrow> convergent\<^sub>\<down> \<sigma>\<close> and \<open>Cauchy \<sigma>\<close>
  from \<open>Cauchy \<sigma>\<close> have * : \<open>\<forall>n. \<exists>k. \<forall>l\<ge>k. \<sigma> l \<down> n = \<sigma> k \<down> n\<close>
    by (metis (mono_tags, opaque_lifting) Cauchy_altdef2 dual_order.order_iff_strict
        le_dist_to_restriction_eqE zero_less_restriction_\<sigma>) 
  define f where \<open>f \<equiv> rec_nat
                      (LEAST k. \<forall>l\<ge>k. \<sigma> l \<down> 0 = \<sigma> k \<down> 0)
                      (\<lambda>n k. LEAST l. k < l \<and> (\<forall>m\<ge>l. \<sigma> m \<down> Suc n = \<sigma> l \<down> Suc n))\<close>
  have f_Suc_def : \<open>f (Suc n) = (LEAST l. f n < l \<and> (\<forall>m\<ge>l. \<sigma> m \<down> Suc n = \<sigma> l \<down> Suc n))\<close>
    (is \<open>f (Suc n) = Least (?f_Suc n)\<close>) for n by (simp add: f_def)
  from "*" have ** : \<open>\<exists>k>f n. \<forall>m\<ge>k. \<sigma> m \<down> Suc n = \<sigma> k \<down> Suc n\<close> for n
    by (metis dual_order.trans lessI linorder_not_le order_le_less)
  have \<open>strict_mono f\<close>
  proof (unfold strict_mono_Suc_iff, rule allI)
    show \<open>f n < f (Suc n)\<close> for n
      by (fact LeastI_ex[of \<open>?f_Suc n\<close>, folded f_Suc_def, OF "**", THEN conjunct1])
  qed

  have \<open>chain\<^sub>\<down> (\<lambda>n. (\<sigma> \<circ> f) n \<down> n)\<close> \<comment> \<open>key point\<close>
  proof (rule restriction_chainI)
    fix n
    have \<open>\<sigma> (f (Suc n)) \<down> n = \<sigma> (f n) \<down> n\<close>
    proof (cases n)
      show \<open>n = 0 \<Longrightarrow> \<sigma> (f (Suc n)) \<down> n = \<sigma> (f n) \<down> n\<close> by simp
    next
      show \<open>n = Suc nat \<Longrightarrow> \<sigma> (f (Suc n)) \<down> n = \<sigma> (f n) \<down> n\<close> for nat
      proof (clarify, intro LeastI_ex[of \<open>?f_Suc nat\<close>,
            folded f_Suc_def, THEN conjunct2, rule_format, OF "**"])
        show \<open>n = Suc nat \<Longrightarrow> f (Suc nat) \<le> f (Suc (Suc nat))\<close>
          by (simp add: \<open>strict_mono f\<close> strict_mono_less_eq)
      qed
    qed
    thus \<open>(\<sigma> \<circ> f) (Suc n) \<down> Suc n \<down> n = (\<sigma> \<circ> f) n \<down> n\<close> by simp
  qed
  with hyp have \<open>convergent\<^sub>\<down> (\<lambda>n. (\<sigma> \<circ> f) n \<down> n)\<close> by simp
  hence \<open>convergent\<^sub>\<down> (\<lambda>n. (\<sigma> \<circ> f) n)\<close>
    by (simp add: restriction_convergent_restricted_iff_restriction_convergent)
  hence \<open>convergent (\<lambda>n. (\<sigma> \<circ> f) n)\<close>
    by (simp add: convergent_iff_restriction_convergent)
  with Cauchy_converges_subseq[OF \<open>Cauchy \<sigma>\<close> \<open>strict_mono f\<close>]
  show \<open>convergent \<sigma>\<close> unfolding convergent_def by blast
qed

end


text \<open>The following classes will be useful later.\<close>


class complete_decseq_restriction_space = decseq_restriction_space +
  assumes restriction_chain_imp_restriction_convergent' : \<open>chain\<^sub>\<down> \<sigma> \<Longrightarrow> convergent\<^sub>\<down> \<sigma>\<close>
begin

subclass complete_restriction_space
  by unfold_locales (fact restriction_chain_imp_restriction_convergent')

subclass complete_ultrametric_space
proof (unfold_locales)
  from complete_iff_restriction_complete restriction_chain_imp_restriction_convergent
  show \<open>Cauchy \<sigma> \<Longrightarrow> convergent \<sigma>\<close> for \<sigma> by blast
qed

end

text \<open>We hide duplicated fact @{thm restriction_chain_imp_restriction_convergent}.\<close>
hide_fact restriction_chain_imp_restriction_convergent'


class complete_strict_decseq_restriction_space = strict_decseq_restriction_space + 
  assumes restriction_chain_imp_restriction_convergent' : \<open>chain\<^sub>\<down> \<sigma> \<Longrightarrow> convergent\<^sub>\<down> \<sigma>\<close>
begin

subclass complete_decseq_restriction_space
  by (unfold_locales) (fact restriction_chain_imp_restriction_convergent')

end

text \<open>We hide duplicated fact @{thm restriction_chain_imp_restriction_convergent'}.\<close>
hide_fact restriction_chain_imp_restriction_convergent'



class restriction_\<delta> = restriction_\<sigma> +
  fixes restriction_\<delta> :: \<open>'a itself \<Rightarrow> real\<close> (\<open>\<delta>\<^sub>\<down>\<close>)
  assumes zero_less_restriction_\<delta> [simp] : \<open>0 < \<delta>\<^sub>\<down> TYPE('a)\<close>
    and restriction_\<delta>_less_one  [simp] : \<open>\<delta>\<^sub>\<down> TYPE('a) < 1\<close>
begin

lemma zero_le_restriction_\<delta> [simp] : \<open>0 \<le> \<delta>\<^sub>\<down> TYPE('a)\<close>
  and restriction_\<delta>_le_one  [simp] : \<open>\<delta>\<^sub>\<down> TYPE('a) \<le> 1\<close>
  and zero_le_pow_restriction_\<delta> [simp] : \<open>0 \<le> \<delta>\<^sub>\<down> TYPE('a) ^ n\<close>
  by (simp_all add: order_less_imp_le)

lemma pow_restriction_\<delta>_le_one [simp] : \<open>\<delta>\<^sub>\<down> TYPE('a) ^ n \<le> 1\<close>
  by (simp add: power_le_one)

lemma pow_restriction_\<delta>_less_one [simp] : \<open>n \<noteq> 0 \<Longrightarrow> \<delta>\<^sub>\<down> TYPE('a) ^ n < 1\<close>
  by (metis restriction_\<delta>_less_one zero_less_restriction_\<delta> not_gr_zero power_0 power_strict_decreasing)

end


setup \<open>Sign.add_const_constraint (\<^const_name>\<open>dist\<close>, NONE)\<close>
  \<comment> \<open>To be able to use \<^const>\<open>dist\<close> out of the \<^class>\<open>metric_space\<close> class.\<close>

class at_least_geometric_restriction_space =
  uniformity_dist + open_uniformity + restriction_\<delta> +
  assumes zero_less_restriction_\<sigma>' : \<open>0 < \<sigma>\<^sub>\<down> TYPE('a) n\<close>
    and restriction_\<sigma>_le :
    \<open>\<sigma>\<^sub>\<down> TYPE('a) (Suc n) \<le> \<delta>\<^sub>\<down> TYPE('a) * \<sigma>\<^sub>\<down> TYPE('a) n\<close>
    and dist_restriction_is' :
    \<open>dist x y = (INF n \<in> {n. x \<down> n = y \<down> n}. \<sigma>\<^sub>\<down> TYPE('a) n)\<close>

setup \<open>Sign.add_const_constraint (\<^const_name>\<open>dist\<close>, SOME \<^typ>\<open>'a :: metric_space \<Rightarrow> 'a \<Rightarrow> real\<close>)\<close>
  \<comment> \<open>Only allow \<^const>\<open>dist\<close> in class \<^class>\<open>metric_space\<close> (back to normal).\<close>

context at_least_geometric_restriction_space begin

lemma restriction_\<sigma>_le_restriction_\<sigma>_times_pow_restriction_\<delta> :
  \<open>\<sigma>\<^sub>\<down> TYPE('a) (n + k) \<le> \<sigma>\<^sub>\<down> TYPE('a) n * \<delta>\<^sub>\<down> TYPE('a) ^ k\<close>
  by (induct k, simp_all)
    (metis dual_order.trans restriction_\<sigma>_le zero_less_restriction_\<delta>
      mult.left_commute mult_le_cancel_left_pos)


lemma restriction_\<sigma>_le_pow_restriction_\<delta> :
  \<open>\<sigma>\<^sub>\<down> TYPE('a) n \<le> \<sigma>\<^sub>\<down> TYPE('a) 0 * \<delta>\<^sub>\<down> TYPE('a) ^ n\<close>
  by (metis add_0 restriction_\<sigma>_le_restriction_\<sigma>_times_pow_restriction_\<delta>)




subclass strict_decseq_restriction_space
proof unfold_locales
  have \<open>\<forall>\<^sub>F n in sequentially. 0 \<le> \<sigma>\<^sub>\<down> TYPE('a) n\<close>
    by (simp add: zero_less_restriction_\<sigma>' order_less_imp_le)
  moreover have \<open>\<forall>\<^sub>F n in sequentially. \<sigma>\<^sub>\<down> TYPE('a) n
                 \<le> \<sigma>\<^sub>\<down> TYPE('a) 0 * \<delta>\<^sub>\<down> TYPE('a) ^ n\<close>
    by (simp add: restriction_\<sigma>_le_pow_restriction_\<delta>)
  moreover have \<open>(\<lambda>n. 0) \<longlonglongrightarrow> 0\<close> by simp
  moreover have \<open>(\<lambda>n. \<sigma>\<^sub>\<down> TYPE('a) 0 * \<delta>\<^sub>\<down> TYPE('a) ^ n) \<longlonglongrightarrow> 0\<close>
    by (simp add: LIMSEQ_abs_realpow_zero2 abs_of_pos tendsto_mult_right_zero)
  ultimately show \<open>\<sigma>\<^sub>\<down> TYPE('a) \<longlonglongrightarrow> 0\<close> by (fact real_tendsto_sandwich)
next
  show \<open>0 < \<sigma>\<^sub>\<down> TYPE('a) n\<close> for n
    by (fact zero_less_restriction_\<sigma>')
next
  show \<open>dist x y = Inf (\<sigma>\<^sub>\<down> TYPE('a) ` {n. x \<down> n = y \<down> n})\<close> for x y
    by (fact dist_restriction_is')
next
  show \<open>strict_decseq (\<sigma>\<^sub>\<down> TYPE('a))\<close>
    by (rule strict_decseqI, rule le_less_trans[OF restriction_\<sigma>_le])
      (simp add: zero_less_restriction_\<sigma>')
qed

lemma \<open>0 < \<delta>\<^sub>\<down> TYPE('a) ^ n\<close> by simp



end

text \<open>We hide duplicated facts
@{thm zero_less_restriction_\<sigma> dist_restriction_is}.\<close>
hide_fact zero_less_restriction_\<sigma>' dist_restriction_is'




class complete_at_least_geometric_restriction_space = at_least_geometric_restriction_space + 
  assumes restriction_chain_imp_restriction_convergent' : \<open>chain\<^sub>\<down> \<sigma> \<Longrightarrow> convergent\<^sub>\<down> \<sigma>\<close>
begin

subclass complete_strict_decseq_restriction_space
  by unfold_locales (fact restriction_chain_imp_restriction_convergent')

end

text \<open>We hide duplicated fact @{thm restriction_chain_imp_restriction_convergent}.\<close>
hide_fact restriction_chain_imp_restriction_convergent'



setup \<open>Sign.add_const_constraint (\<^const_name>\<open>dist\<close>, NONE)\<close>
  \<comment> \<open>To be able to use \<^const>\<open>dist\<close> out of the \<^class>\<open>metric_space\<close> class.\<close>

class geometric_restriction_space = uniformity_dist + open_uniformity + restriction_\<delta> +
  assumes restriction_\<sigma>_is : \<open>\<sigma>\<^sub>\<down> TYPE('a) n = \<delta>\<^sub>\<down> TYPE('a) ^ n\<close>
    and dist_restriction_is' : \<open>dist x y = (INF n \<in> {n. x \<down> n = y \<down> n}. \<sigma>\<^sub>\<down> TYPE('a) n)\<close>
begin

text \<open>This is what ``restriction space'' usually mean in the literature.
      The previous classes are generalizations of this concept
      (even this one is a generalization, since we usually
      have \<^term>\<open>\<delta>\<^sub>\<down> TYPE('a) = 1 / 2\<close>).\<close>

subclass at_least_geometric_restriction_space
proof unfold_locales
  show \<open>0 < \<sigma>\<^sub>\<down> TYPE('a) n\<close> for n by (simp add: restriction_\<sigma>_is)
next
  show \<open>\<sigma>\<^sub>\<down> TYPE('a) (Suc n) \<le> \<delta>\<^sub>\<down> TYPE('a) * \<sigma>\<^sub>\<down> TYPE('a) n\<close> for n
    by (simp add: restriction_\<sigma>_is)
next
  show \<open>dist x y = Inf (\<sigma>\<^sub>\<down> TYPE('a) ` {n. x \<down> n = y \<down> n})\<close> for x y
    by (fact dist_restriction_is')
qed


lemma \<open>0 < \<delta>\<^sub>\<down> TYPE('a) ^ n\<close> by simp

end

setup \<open>Sign.add_const_constraint (\<^const_name>\<open>dist\<close>, SOME \<^typ>\<open>'a :: metric_space \<Rightarrow> 'a \<Rightarrow> real\<close>)\<close>
  \<comment> \<open>Only allow \<^const>\<open>dist\<close> in class \<^class>\<open>metric_space\<close> (back to normal).\<close>


text \<open>We hide duplicated fact @{thm dist_restriction_is}.\<close>
hide_fact dist_restriction_is'


class complete_geometric_restriction_space = geometric_restriction_space + 
  assumes restriction_chain_imp_restriction_convergent' : \<open>chain\<^sub>\<down> \<sigma> \<Longrightarrow> convergent\<^sub>\<down> \<sigma>\<close>
begin 

subclass complete_at_least_geometric_restriction_space
  by (unfold_locales) (fact restriction_chain_imp_restriction_convergent')

end 

text \<open>We hide duplicated fact @{thm restriction_chain_imp_restriction_convergent}.\<close>
hide_fact restriction_chain_imp_restriction_convergent'

(* remove that, useless now *)
theorem geometric_restriction_space_completeI : \<open>convergent \<sigma>\<close>
  if \<open>\<And>\<sigma> :: nat \<Rightarrow> 'a. restriction_chain \<sigma> \<Longrightarrow> \<exists>\<Sigma>. \<forall>n. \<Sigma> \<down> n = \<sigma> n\<close>
    and \<open>Cauchy \<sigma>\<close> for \<sigma> :: \<open>nat \<Rightarrow> 'a :: geometric_restriction_space\<close>
  by (metis complete_iff_restriction_complete convergent_def
      convergent_iff_restriction_convergent ext restriction_tendsto_self that)



\<comment> \<open>Because \<^const>\<open>cball\<close> is not defined in \<^class>\<open>metric_space\<close>.\<close>
lemma (in non_decseq_restriction_space) restriction_cball_subset_cball :
  \<open>\<sigma>\<^sub>\<down> TYPE('a) n \<le> r \<Longrightarrow> \<B>\<^sub>\<down>(\<Sigma>, n) \<subseteq> {x. dist \<Sigma> x \<le> r}\<close>
  by (simp add: subset_iff restriction_cball_mem_iff)
    (simp add: dual_order.trans restriction_space_Inf_properties(1))

corollary restriction_cball_subset_cball_bis :
  \<open>\<sigma>\<^sub>\<down> TYPE('a) n \<le> r \<Longrightarrow> \<B>\<^sub>\<down>(\<Sigma>, n) \<subseteq> cball \<Sigma> r\<close>
  for \<Sigma> :: \<open>'a :: non_decseq_restriction_space\<close>
  unfolding cball_def by (fact restriction_cball_subset_cball)


lemma (in non_decseq_restriction_space) restriction_ball_subset_ball :
  \<open>\<sigma>\<^sub>\<down> TYPE('a) n < r \<Longrightarrow> restriction_ball \<Sigma> n \<subseteq> {x. dist \<Sigma> x < r}\<close>
  by (simp add: subset_iff restriction_cball_mem_iff)
    (metis (mono_tags, lifting) image_eqI mem_Collect_eq order_le_less_trans
      restriction_related_pred restriction_space_Inf_properties(1))

corollary restriction_ball_subset_ball_bis :
  \<open>\<sigma>\<^sub>\<down> TYPE('a) n < r \<Longrightarrow> restriction_ball \<Sigma> n \<subseteq> ball \<Sigma> r\<close>
  for \<Sigma> :: \<open>'a :: non_decseq_restriction_space\<close>
  unfolding ball_def by (fact restriction_ball_subset_ball)



lemma (in strict_decseq_restriction_space)
  restriction_cball_is_cball : \<open>\<B>\<^sub>\<down>(\<Sigma>, n) = {x. dist \<Sigma> x \<le> \<sigma>\<^sub>\<down> TYPE('a) n}\<close>
proof (intro subset_antisym subsetI)
  from restriction_cball_subset_cball
  show \<open>x \<in> \<B>\<^sub>\<down>(\<Sigma>, n) \<Longrightarrow> x \<in> {x. dist \<Sigma> x \<le> \<sigma>\<^sub>\<down> TYPE('a) n}\<close> for x by blast
next
  show \<open>x \<in> \<B>\<^sub>\<down>(\<Sigma>, n)\<close> if \<open>x \<in> {x. dist \<Sigma> x \<le> \<sigma>\<^sub>\<down> TYPE('a) n}\<close> for x
  proof (cases \<open>\<Sigma> = x\<close>)
    show \<open>\<Sigma> = x \<Longrightarrow> x \<in> \<B>\<^sub>\<down>(\<Sigma>, n)\<close> by simp
  next
    assume \<open>\<Sigma> \<noteq> x\<close>
    with not_related_imp_dist_restriction_is_some_restriction_\<sigma> obtain m
      where \<open>dist \<Sigma> x = \<sigma>\<^sub>\<down> TYPE('a) m\<close> \<open>\<forall>k\<le>m. \<Sigma> \<down> k = x \<down> k\<close> by blast
    from \<open>x \<in> {x. dist \<Sigma> x \<le> \<sigma>\<^sub>\<down> TYPE('a) n}\<close>
    have \<open>dist \<Sigma> x \<le> \<sigma>\<^sub>\<down> TYPE('a) n\<close> by simp
    with \<open>dist \<Sigma> x = \<sigma>\<^sub>\<down> TYPE('a) m\<close> have \<open>n \<le> m\<close>
      by (metis linorder_not_less strict_decseq_restriction_\<sigma> strict_decseq_def_bis)
    with \<open>\<forall>k\<le>m. \<Sigma> \<down> k = x \<down> k\<close> have \<open>\<Sigma> \<down> n = x \<down> n\<close> by simp
    thus \<open>x \<in> \<B>\<^sub>\<down>(\<Sigma>, n)\<close> by (simp add: restriction_cball_mem_iff)
  qed
qed

lemma restriction_cball_is_cball_bis : \<open>\<B>\<^sub>\<down>(\<Sigma>, n) = cball \<Sigma> (\<sigma>\<^sub>\<down> TYPE('a) n)\<close>
  for \<Sigma> :: \<open>'a :: strict_decseq_restriction_space\<close>
  by (simp add: cball_def restriction_cball_is_cball)


lemma (in strict_decseq_restriction_space)
  restriction_ball_is_ball : \<open>restriction_ball \<Sigma> n = {x. dist \<Sigma> x < \<sigma>\<^sub>\<down> TYPE('a) n}\<close>
proof (intro subset_antisym subsetI)
  show \<open>x \<in> restriction_ball \<Sigma> n \<Longrightarrow> x \<in> {x. dist \<Sigma> x < \<sigma>\<^sub>\<down> TYPE('a) n}\<close> for x
    by (simp add: subset_iff)
      (metis lessI local.restriction_cball_is_cball strict_decseq_restriction_\<sigma>
        mem_Collect_eq order_le_less_trans strict_decseq_def_bis)
next
  show \<open>x \<in> restriction_ball \<Sigma> n\<close> if \<open>x \<in> {x. dist \<Sigma> x < \<sigma>\<^sub>\<down> TYPE('a) n}\<close> for x
  proof (cases \<open>\<Sigma> = x\<close>)
    show \<open>\<Sigma> = x \<Longrightarrow> x \<in> restriction_ball \<Sigma> n\<close> by simp
  next
    assume \<open>\<Sigma> \<noteq> x\<close>
    with not_related_imp_dist_restriction_is_some_restriction_\<sigma> obtain m
      where \<open>dist \<Sigma> x = \<sigma>\<^sub>\<down> TYPE('a) m\<close> \<open>\<forall>k\<le>m. \<Sigma> \<down> k = x \<down> k\<close> by blast
    from \<open>x \<in> {x. dist \<Sigma> x < \<sigma>\<^sub>\<down> TYPE('a) n}\<close>
    have \<open>dist \<Sigma> x < \<sigma>\<^sub>\<down> TYPE('a) n\<close> by simp
    with \<open>dist \<Sigma> x = \<sigma>\<^sub>\<down> TYPE('a) m\<close> have \<open>n < m\<close>
      using strict_decseq_restriction_\<sigma> strict_decseq_def_bis by auto
    with \<open>\<forall>k\<le>m. \<Sigma> \<down> k = x \<down> k\<close> have \<open>\<Sigma> \<down> Suc n = x \<down> Suc n\<close> by simp
    thus \<open>x \<in> restriction_ball \<Sigma> n\<close> by (simp add: restriction_cball_mem_iff)
  qed
qed

lemma restriction_ball_is_ball_bis : \<open>restriction_ball \<Sigma> n = ball \<Sigma> (\<sigma>\<^sub>\<down> TYPE('a) n)\<close>
  for \<Sigma> :: \<open>'a :: strict_decseq_restriction_space\<close>
  by (simp add: ball_def restriction_ball_is_ball)





lemma isCont_iff_restriction_cont_at : \<open>isCont f \<Sigma> \<longleftrightarrow> restriction_cont_at f \<Sigma>\<close>
  for f :: \<open>'a :: decseq_restriction_space \<Rightarrow> 'b :: decseq_restriction_space\<close>
  by (unfold restriction_cont_at_def continuous_at_sequentially comp_def,
      fold tendsto_iff_restriction_tendsto) simp


lemma (in strict_decseq_restriction_space)
  open_iff_restriction_open : \<open>open U \<longleftrightarrow> open\<^sub>\<down> U\<close>
proof (unfold open_dist restriction_open_iff_restriction_cball_characterization, intro iffI ballI)
  fix \<Sigma> assume \<open>\<forall>x\<in>U. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> U\<close> and \<open>\<Sigma> \<in> U\<close>
  then obtain e where \<open>0 < e\<close> \<open>\<forall>y. dist y \<Sigma> < e \<longrightarrow> y \<in> U\<close> by blast
  from \<open>0 < e\<close> obtain n where \<open>\<sigma>\<^sub>\<down> TYPE('a) n < e\<close>
    by (metis eventually_at_top_linorder le_refl restriction_\<sigma>_tendsto_zero order_tendstoD(2))
  with \<open>\<forall>y. dist y \<Sigma> < e \<longrightarrow> y \<in> U\<close> dist_commute restriction_cball_is_cball
  have \<open>\<B>\<^sub>\<down>(\<Sigma>, n) \<subseteq> U\<close> by auto
  thus \<open>\<exists>n. \<B>\<^sub>\<down>(\<Sigma>, n) \<subseteq> U\<close> ..
next
  fix x assume \<open>\<forall>\<Sigma>\<in>U. \<exists>n. \<B>\<^sub>\<down>(\<Sigma>, n) \<subseteq> U\<close> \<open>x \<in> U\<close>
  then obtain n where \<open>\<B>\<^sub>\<down>(x, n) \<subseteq> U\<close> by blast
  hence \<open>\<forall>y. dist y x < \<sigma>\<^sub>\<down> TYPE('a) n \<longrightarrow> y \<in> U\<close>
    by (simp add: dist_commute restriction_cball_is_cball subset_iff)
  thus \<open>\<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> U\<close>
    using zero_less_restriction_\<sigma>' by blast
qed


lemma (in strict_decseq_restriction_space)
  closed_iff_restriction_closed : \<open>closed U \<longleftrightarrow> closed\<^sub>\<down> U\<close>
  by (simp add: closed_open open_iff_restriction_open restriction_open_Compl_iff)




lemma continuous_on_iff_restriction_cont_on :
  \<open>open U \<Longrightarrow> continuous_on U f \<longleftrightarrow> restriction_cont_on f U\<close>
  for f :: \<open>'a :: decseq_restriction_space \<Rightarrow> 'b :: decseq_restriction_space\<close>
  by (simp add: restriction_cont_on_def continuous_on_eq_continuous_at
      flip: isCont_iff_restriction_cont_at)





subsection \<open>Equivalence between Lipschitz Map and Restriction shift Map\<close>

text \<open>For a function @{term [show_types] \<open>f :: 'a \<Rightarrow> 'b\<close>}, it is equivalent to have
      \<^term>\<open>restriction_shift_on f k A\<close> and
      \<^term>\<open>lipschitz_with_on f (restriction_\<delta> TYPE('b :: geometric_restriction_space) ^ k) A\<close>
      when \<^typ>\<open>'a\<close> is of sort \<^class>\<open>geometric_restriction_space\<close> and 
      \<^term>\<open>restriction_\<sigma> TYPE('b :: geometric_restriction_space) =
           restriction_\<sigma> TYPE('a :: geometric_restriction_space)\<close>
      (\<^typ>\<open>'b\<close> is then necessarily also of sort \<^class>\<open>geometric_restriction_space\<close>).\<close>

text \<open>Weaker versions of this result wan be established with weaker assumptions on the sort,
      this is what we do below.\<close>

lemma restriction_shift_nonneg_on_imp_lipschitz_with_on :
  \<open>lipschitz_with_on f (restriction_\<delta> TYPE('b) ^ k) A\<close> if \<open>restriction_shift_on f (int k) A\<close>
  and le_restriction_\<sigma> : \<open>\<And>n. restriction_\<sigma> TYPE('b) n \<le> restriction_\<sigma> TYPE('a) n\<close>
for f :: \<open>'a :: decseq_restriction_space \<Rightarrow> 'b :: at_least_geometric_restriction_space\<close>
proof (rule lipschitz_with_onI)
  show \<open>0 \<le> restriction_\<delta> TYPE('b) ^ k\<close> by simp
next
  fix x y assume \<open>x \<in> A\<close> \<open>y \<in> A\<close> \<open>x \<noteq> y\<close> \<open>f x \<noteq> f y\<close>
  from \<open>restriction_shift_on f k A\<close>[THEN restriction_shift_onD, OF \<open>x \<in> A\<close> \<open>y \<in> A\<close>]
  have \<open>i \<in> restriction_related_set x y \<Longrightarrow> i + k \<in> restriction_related_set (f x) (f y)\<close> for i
    by (simp add: nat_int_add)
  hence \<open>Sup (restriction_related_set x y) + k \<in> restriction_related_set (f x) (f y)\<close>
    using \<open>x \<noteq> y\<close> Sup_in_restriction_related_set by blast
  hence \<open>Sup (restriction_related_set x y) + k \<le> Sup (restriction_related_set (f x) (f y))\<close>
    by (simp add: \<open>f x \<noteq> f y\<close> bdd_above_restriction_related_set_iff cSup_upper)
  moreover have \<open>dist (f x) (f y) = restriction_\<sigma> TYPE('b) (Sup (restriction_related_set (f x) (f y)))\<close>
    by (simp add: \<open>f x \<noteq> f y\<close> dist_restriction_is_bis_simplified)
  ultimately have \<open>dist (f x) (f y) \<le> restriction_\<sigma> TYPE('b) (Sup (restriction_related_set x y) + k)\<close>
    by (simp add: decseqD decseq_restriction_space_class.decseq_restriction_\<sigma>)
  hence \<open>dist (f x) (f y) \<le> restriction_\<sigma> TYPE('b) (Sup (restriction_related_set x y)) * restriction_\<delta> TYPE('b) ^ k\<close>
    by (meson order.trans restriction_\<sigma>_le_restriction_\<sigma>_times_pow_restriction_\<delta>)
  also have \<open>\<dots> \<le> restriction_\<sigma> TYPE('a) (Sup (restriction_related_set x y)) * restriction_\<delta> TYPE('b) ^ k\<close>
    by (simp add: le_restriction_\<sigma>)
  finally show \<open>dist (f x) (f y) \<le> restriction_\<delta> TYPE('b) ^ k * dist x y\<close>
    by (simp add: dist_restriction_is_bis[of x y] \<open>x \<noteq> y\<close> mult.commute)
qed

corollary restriction_shift_nonneg_imp_lipschitz_with :
  \<open>\<lbrakk>restriction_shift f (int k); \<And>n. restriction_\<sigma> TYPE('b) n \<le> restriction_\<sigma> TYPE('a) n\<rbrakk>
   \<Longrightarrow> lipschitz_with f (restriction_\<delta> TYPE('b) ^ k)\<close>
  for f :: \<open>'a :: decseq_restriction_space \<Rightarrow> 'b :: at_least_geometric_restriction_space\<close>
  using restriction_shift_def restriction_shift_nonneg_on_imp_lipschitz_with_on by blast


lemma lipschitz_with_on_imp_restriction_shift_neg_on :
  \<open>restriction_shift_on f (- int k) A\<close> if \<open>lipschitz_with_on f (restriction_\<delta> TYPE('b) powi - int k) A\<close>
  and le_restriction_\<sigma> : \<open>\<And>n. restriction_\<sigma> TYPE('a) n \<le> restriction_\<sigma> TYPE('b) n\<close>
for f :: \<open>'a :: decseq_restriction_space \<Rightarrow> 'b :: at_least_geometric_restriction_space\<close>
proof (rule restriction_shift_onI, goal_cases)
  fix x y n assume \<open>x \<in> A\<close> \<open>y \<in> A\<close> \<open>f x \<noteq> f y\<close> \<open>x \<down> n = y \<down> n\<close>
  from \<open>f x \<noteq> f y\<close> have \<open>x \<noteq> y\<close> by blast
  from \<open>lipschitz_with_on f (restriction_\<delta> TYPE('b) powi - int k) A\<close>
    [THEN lipschitz_with_onD2, OF \<open>x \<in> A\<close> \<open>y \<in> A\<close>]
  have \<open>dist (f x) (f y) \<le> restriction_\<delta> TYPE('b) powi - int k * dist x y\<close> .
  hence \<open>dist (f x) (f y) * restriction_\<delta> TYPE('b) ^ k \<le> dist x y\<close>
    by (subst (asm) mult.commute)
      (drule mult_imp_div_pos_le[rotated]; simp add: power_int_minus_divide)
  hence \<open>restriction_\<sigma> TYPE('b) (Sup (restriction_related_set (f x) (f y))) * restriction_\<delta> TYPE('b) ^ k
         \<le> restriction_\<sigma> TYPE('b) (Sup (restriction_related_set x y))\<close>
    by (simp add: dist_restriction_is_bis \<open>x \<noteq> y\<close> \<open>f x \<noteq> f y\<close> )
      (drule order_trans[OF _ le_restriction_\<sigma>], simp)
  from order_trans[OF restriction_\<sigma>_le_restriction_\<sigma>_times_pow_restriction_\<delta>
      [of \<open>Sup (restriction_related_set (f x) (f y))\<close> k] this]
  have \<open>restriction_\<sigma> TYPE('b) (Sup (restriction_related_set (f x) (f y)) + k)
        \<le> restriction_\<sigma> TYPE('b) (Sup (restriction_related_set x y))\<close> .
  hence \<open>Sup (restriction_related_set x y) \<le> Sup (restriction_related_set (f x) (f y)) + k\<close>
    using strict_decseq_def_ter strict_decseq_restriction_\<sigma> by blast
  from order_trans[OF cSup_upper this] have \<open>n \<le> Sup (restriction_related_set (f x) (f y)) + k\<close>
    by (simp add: \<open>x \<down> n = y \<down> n\<close> \<open>x \<noteq> y\<close> bdd_above_restriction_related_set_iff)
  hence \<open>nat (int n + - int k) \<le> Sup (restriction_related_set (f x) (f y))\<close> by linarith
  thus \<open>f x \<down> nat (int n + - int k) = f y \<down> nat (int n + - int k)\<close>
    by (metis not_eq_imp_dist_restriction_is_restriction_\<sigma>_Sup_restriction_eq_simplified(2))
qed

corollary lipschitz_with_imp_restriction_shift_neg :
  \<open>\<lbrakk>lipschitz_with f (restriction_\<delta> TYPE('b) powi - int k);
    \<And>n. restriction_\<sigma> TYPE('a) n \<le> restriction_\<sigma> TYPE('b) n\<rbrakk>
   \<Longrightarrow> restriction_shift f (- int k)\<close>
  for f :: \<open>'a :: decseq_restriction_space \<Rightarrow> 'b :: at_least_geometric_restriction_space\<close>
  using lipschitz_with_on_imp_restriction_shift_neg_on restriction_shift_def by blast



text \<open>We obtained that \<^const>\<open>restriction_shift\<close> implies \<^const>\<open>lipschitz_with\<close>
      when \<^term>\<open>0 \<le> k\<close> and that \<^const>\<open>lipschitz_with\<close> implies
      \<^const>\<open>restriction_shift\<close> when \<^term>\<open>k \<le> 0\<close>. To cover the remaining cases,
      we give move from \<^class>\<open>at_least_geometric_restriction_space\<close>
      to \<^class>\<open>geometric_restriction_space\<close>.\<close>


theorem lipschitz_with_on_iff_restriction_shift_on :
  \<open>lipschitz_with_on f (restriction_\<delta> TYPE('b) powi k) A \<longleftrightarrow> restriction_shift_on f k A\<close>
  if same_restriction_\<sigma> : \<open>restriction_\<sigma> TYPE('b) = restriction_\<sigma> TYPE('a)\<close>
  for f :: \<open>'a :: decseq_restriction_space \<Rightarrow> 'b :: geometric_restriction_space\<close>
proof (rule iffI)
  \<comment> \<open>We could do a case on \<^term>\<open>k\<close>, but both cases are actually handled by the proof
      required after applying @{thm lipschitz_with_on_imp_restriction_shift_neg_on}.\<close>
  show \<open>restriction_shift_on f k A\<close> if \<open>lipschitz_with_on f (restriction_\<delta> TYPE('b) powi k) A\<close>
  proof (rule restriction_shift_onI)
    fix x y n assume \<open>x \<in> A\<close> \<open>y \<in> A\<close> \<open>f x \<noteq> f y\<close> \<open>x \<down> n = y \<down> n\<close>
    from \<open>f x \<noteq> f y\<close> have \<open>x \<noteq> y\<close> by blast
    from \<open>lipschitz_with_on f (restriction_\<delta> TYPE('b) powi k) A\<close>
      [THEN lipschitz_with_onD2, OF \<open>x \<in> A\<close> \<open>y \<in> A\<close>]
    have \<open>dist (f x) (f y) \<le> restriction_\<delta> TYPE('b) powi k * dist x y\<close> .
    also have \<open>dist (f x) (f y) = restriction_\<delta> TYPE('b) ^ Sup (restriction_related_set (f x) (f y))\<close>
      by (simp add: dist_restriction_is_bis \<open>f x \<noteq> f y\<close> restriction_\<sigma>_is)
    also have \<open>dist x y = restriction_\<delta> TYPE('b) ^ Sup (restriction_related_set x y)\<close>
      by (simp add: dist_restriction_is_bis \<open>x \<noteq> y\<close> restriction_\<sigma>_is same_restriction_\<sigma>[symmetric])
    finally have \<open>restriction_\<delta> TYPE('b) ^ Sup (restriction_related_set (f x) (f y))
                  \<le> restriction_\<delta> TYPE('b) powi k * restriction_\<delta> TYPE('b) ^ Sup (restriction_related_set x y)\<close> .
    also have \<open>\<dots> = restriction_\<delta> TYPE('b) powi (k + Sup (restriction_related_set x y))\<close>
      by (subst power_int_add, metis order_less_irrefl zero_less_restriction_\<delta>) simp
    finally have \<open>restriction_\<delta> TYPE('b) ^ Sup (restriction_related_set (f x) (f y)) \<le> \<dots>\<close> .
    moreover have \<open>restriction_\<delta> TYPE('b) powi m \<le> restriction_\<delta> TYPE('b) powi m' \<Longrightarrow> m' \<le> m\<close> for m m'
      by (rule ccontr, unfold not_le,
          drule power_int_strict_decreasing[OF _ zero_less_restriction_\<delta> restriction_\<delta>_less_one])
        (fold not_le, blast)
    ultimately have \<open>k + Sup (restriction_related_set x y) \<le> Sup (restriction_related_set (f x) (f y))\<close> by simp
    hence \<open>Sup (restriction_related_set x y) \<le> Sup (restriction_related_set (f x) (f y)) - k\<close> by simp
    with \<open>x \<down> n = y \<down> n\<close> \<open>x \<noteq> y\<close> linorder_not_le
      not_eq_imp_dist_restriction_is_restriction_\<sigma>_Sup_restriction_eq_simplified(3)
    have \<open>n \<le> Sup (restriction_related_set (f x) (f y)) - k\<close> by fastforce
    hence \<open>nat (int n + k) \<le> Sup (restriction_related_set (f x) (f y))\<close> by simp
    thus \<open>f x \<down> nat (int n + k) = f y \<down> nat (int n + k)\<close> 
      by (metis not_eq_imp_dist_restriction_is_restriction_\<sigma>_Sup_restriction_eq_simplified(2))
  qed
next
  show \<open>lipschitz_with_on f (restriction_\<delta> TYPE('b) powi k) A\<close> if \<open>restriction_shift_on f k A\<close>
  proof (cases k)
    show \<open>k = int k' \<Longrightarrow> lipschitz_with_on f (restriction_\<delta> TYPE('b) powi k) A\<close> for k'
      by (simp, rule restriction_shift_nonneg_on_imp_lipschitz_with_on)
        (use \<open>restriction_shift_on f k A\<close> same_restriction_\<sigma> in simp_all)
  next
    fix k' assume \<open>k = - int (Suc k')\<close>
    show \<open>lipschitz_with_on f (restriction_\<delta> TYPE('b) powi k) A\<close>
    proof (rule lipschitz_with_onI)
      show \<open>0 \<le> restriction_\<delta> TYPE('b) powi k\<close> by simp
    next
      fix x y assume \<open>x \<in> A\<close> \<open>y \<in> A\<close> \<open>x \<noteq> y\<close> \<open>f x \<noteq> f y\<close>
      have \<open>i \<in> restriction_related_set x y \<Longrightarrow> i - Suc k' \<in> restriction_related_set (f x) (f y)\<close> for i
        using \<open>restriction_shift_on f k A\<close>[THEN restriction_shift_onD, OF \<open>x \<in> A\<close> \<open>y \<in> A\<close>, of i]
        by (unfold \<open>k = - int (Suc k')\<close>, clarify) (metis diff_conv_add_uminus nat_minus_as_int)
      hence \<open>Sup (restriction_related_set x y) - Suc k' \<in> restriction_related_set (f x) (f y)\<close>
        using \<open>x \<noteq> y\<close> not_eq_imp_dist_restriction_is_restriction_\<sigma>_Sup_restriction_eq_simplified by blast
      hence \<open>Sup (restriction_related_set x y) - Suc k' \<le> Sup (restriction_related_set (f x) (f y))\<close>
        by (simp add: \<open>f x \<noteq> f y\<close> bdd_above_restriction_related_set_iff cSup_upper)
      hence * : \<open>Sup (restriction_related_set x y) + k \<le> Sup (restriction_related_set (f x) (f y))\<close>
        by (simp add: \<open>k = - int (Suc k')\<close>)
      have \<open>dist (f x) (f y) = restriction_\<delta> TYPE('b) powi Sup (restriction_related_set (f x) (f y))\<close>
        by (simp add: \<open>f x \<noteq> f y\<close> dist_restriction_is_bis_simplified restriction_\<sigma>_is)
      also have \<open>\<dots> \<le> restriction_\<delta> TYPE('b) powi (Sup (restriction_related_set x y) + k)\<close>
        by (rule power_int_decreasing[OF "*"]; simp)
          (metis order_less_irrefl zero_less_restriction_\<delta>)
      also have \<open>\<dots> = restriction_\<delta> TYPE('b) powi k * restriction_\<delta> TYPE('b) powi (Sup (restriction_related_set x y))\<close>
        by (subst power_int_add, metis order_less_irrefl zero_less_restriction_\<delta>) simp
      also have \<open>restriction_\<delta> TYPE('b) powi (Sup (restriction_related_set x y)) = dist x y\<close>
        by (simp add: \<open>x \<noteq> y\<close> dist_restriction_is_bis_simplified
            restriction_\<sigma>_is same_restriction_\<sigma>[symmetric])
      finally show \<open>dist (f x) (f y) \<le> restriction_\<delta> TYPE('b) powi k * dist x y\<close> .
    qed
  qed
qed

corollary lipschitz_with_iff_restriction_shift :
  \<open>restriction_\<sigma> TYPE('b) = restriction_\<sigma> TYPE('a) \<Longrightarrow>
   lipschitz_with f (restriction_\<delta> TYPE('b) powi k) \<longleftrightarrow> restriction_shift f k\<close>
  for f :: \<open>'a :: decseq_restriction_space \<Rightarrow> 'b :: geometric_restriction_space\<close>
  by (simp add: lipschitz_with_on_iff_restriction_shift_on restriction_shift_def)



(*<*)
end
  (*>*)
