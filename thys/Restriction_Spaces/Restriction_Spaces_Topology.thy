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


section \<open>Topological Notions\<close>

(*<*)
theory Restriction_Spaces_Topology
  imports Restriction_Spaces_Prod Restriction_Spaces_Fun
begin
  (*>*)


named_theorems restriction_cont_simpset \<comment> \<open>For future automation.\<close>

subsection \<open>Continuity\<close>

context restriction begin

definition restriction_cont_at :: \<open>['b :: restriction \<Rightarrow> 'a, 'b] \<Rightarrow> bool\<close>
  (\<open>cont\<^sub>\<down> (_) at (_)\<close> [1000, 1000])
  where \<open>cont\<^sub>\<down> f at \<Sigma> \<equiv> \<forall>\<sigma>. \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<longrightarrow> (\<lambda>n. f (\<sigma> n)) \<midarrow>\<down>\<rightarrow> f \<Sigma>\<close>

lemma restriction_cont_atI : \<open>(\<And>\<sigma>. \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<Longrightarrow> (\<lambda>n. f (\<sigma> n)) \<midarrow>\<down>\<rightarrow> f \<Sigma>) \<Longrightarrow> cont\<^sub>\<down> f at \<Sigma>\<close>
  by (simp add: restriction_cont_at_def)

lemma restriction_cont_atD : \<open>cont\<^sub>\<down> f at \<Sigma> \<Longrightarrow> \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<Longrightarrow> (\<lambda>n. f (\<sigma> n)) \<midarrow>\<down>\<rightarrow> f \<Sigma>\<close>
  by (simp add: restriction_cont_at_def)

lemma restriction_cont_at_comp [restriction_cont_simpset] :
  \<open>cont\<^sub>\<down> f at \<Sigma> \<Longrightarrow> cont\<^sub>\<down> g at (f \<Sigma>) \<Longrightarrow> cont\<^sub>\<down> (\<lambda>x. g (f x)) at \<Sigma>\<close>
  by (simp add: restriction_cont_at_def restriction_class.restriction_cont_at_def)

lemma restriction_cont_at_if_then_else [restriction_cont_simpset] :
  \<open>\<lbrakk>\<And>x. P x \<Longrightarrow> cont\<^sub>\<down> (f x) at \<Sigma>; \<And>x. \<not> P x \<Longrightarrow> cont\<^sub>\<down> (g x) at \<Sigma>\<rbrakk>
   \<Longrightarrow> cont\<^sub>\<down> (\<lambda>y. if P x then f x y else g x y) at \<Sigma>\<close>
  by (auto intro!: restriction_cont_atI) (blast dest: restriction_cont_atD)+



definition restriction_open :: \<open>'a set \<Rightarrow> bool\<close> (\<open>open\<^sub>\<down>\<close>)
  where \<open>open\<^sub>\<down> U \<equiv> \<forall>\<Sigma>\<in>U. \<forall>\<sigma>. \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<longrightarrow> (\<exists>n0. \<forall>k\<ge>n0. \<sigma> k \<in> U)\<close>

lemma restriction_openI : \<open>(\<And>\<Sigma> \<sigma>. \<Sigma> \<in> U \<Longrightarrow> \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<Longrightarrow> \<exists>n0. \<forall>k\<ge>n0. \<sigma> k \<in> U) \<Longrightarrow> open\<^sub>\<down> U\<close>
  by (simp add: restriction_open_def)

lemma restriction_openD : \<open>open\<^sub>\<down> U \<Longrightarrow> \<Sigma> \<in> U \<Longrightarrow> \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<Longrightarrow> \<exists>n0. \<forall>k\<ge>n0. \<sigma> k \<in> U\<close>
  by (simp add: restriction_open_def)

lemma restriction_openE :
  \<open>open\<^sub>\<down> U \<Longrightarrow> \<Sigma> \<in> U \<Longrightarrow> \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<Longrightarrow> (\<And>n0. (\<And>n. n0 \<le> k \<Longrightarrow> \<sigma> k \<in> U) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
  using restriction_openD by blast

lemma restriction_open_UNIV  [simp] : \<open>open\<^sub>\<down> UNIV\<close>
  and restriction_open_empty [simp] : \<open>open\<^sub>\<down> {}\<close>
  by (simp_all add: restriction_open_def)


lemma restriction_open_union :
  \<open>open\<^sub>\<down> U \<Longrightarrow> open\<^sub>\<down> V \<Longrightarrow> open\<^sub>\<down> (U \<union> V)\<close>
  by (metis Un_iff restriction_open_def)

lemma restriction_open_Union :
  \<open>(\<And>i. i \<in> I \<Longrightarrow> open\<^sub>\<down> (U i)) \<Longrightarrow> open\<^sub>\<down> (\<Union>i\<in>I. U i)\<close>
  by (rule restriction_openI) (metis UN_iff restriction_openD)

lemma restriction_open_inter :
  \<open>open\<^sub>\<down> (U \<inter> V)\<close> if \<open>open\<^sub>\<down> U\<close> and \<open>open\<^sub>\<down> V\<close>
proof (rule restriction_openI)
  fix \<Sigma> \<sigma> assume \<open>\<Sigma> \<in> U \<inter> V\<close> \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
  from \<open>\<Sigma> \<in> U \<inter> V\<close> have \<open>\<Sigma> \<in> U\<close> and \<open>\<Sigma> \<in> V\<close> by simp_all
  from \<open>open\<^sub>\<down> U\<close> \<open>\<Sigma> \<in> U\<close> \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> restriction_openD
  obtain n0 where \<open>\<forall>k\<ge>n0. \<sigma> k \<in> U\<close> by blast
  moreover from \<open>open\<^sub>\<down> V\<close> \<open>\<Sigma> \<in> V\<close> \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> restriction_openD
  obtain n1 where \<open>\<forall>k\<ge>n1. \<sigma> k \<in> V\<close> by blast
  ultimately have \<open>\<forall>k\<ge>max n0 n1. \<sigma> k \<in> U \<inter> V\<close> by simp
  thus \<open>\<exists>n0. \<forall>k\<ge>n0. \<sigma> k \<in> U \<inter> V\<close> by blast
qed

lemma restriction_open_finite_Inter :
  \<open>finite I \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> open\<^sub>\<down> (U i)) \<Longrightarrow> open\<^sub>\<down> (\<Inter>i\<in>I. U i)\<close>
  by (induct I rule: finite_induct)
    (simp_all add: restriction_open_inter)



definition restriction_closed :: \<open>'a set \<Rightarrow> bool\<close> (\<open>closed\<^sub>\<down>\<close>)
  where \<open>closed\<^sub>\<down> S \<equiv> open\<^sub>\<down> (- S)\<close>

lemma restriction_closedI : \<open>(\<And>\<Sigma> \<sigma>. \<Sigma> \<notin> S \<Longrightarrow> \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<Longrightarrow> \<exists>n0. \<forall>k\<ge>n0. \<sigma> k \<notin> S) \<Longrightarrow> closed\<^sub>\<down> S\<close>
  by (simp add: restriction_closed_def restriction_open_def)

lemma restriction_closedD : \<open>closed\<^sub>\<down> S \<Longrightarrow> \<Sigma> \<notin> S \<Longrightarrow> \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<Longrightarrow> \<exists>n0. \<forall>k\<ge>n0. \<sigma> k \<notin> S\<close>
  by (simp add: restriction_closed_def restriction_open_def)

lemma restriction_closedE :
  \<open>closed\<^sub>\<down> S \<Longrightarrow> \<Sigma> \<notin> S \<Longrightarrow> \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<Longrightarrow> (\<And>n0. (\<And>n. n0 \<le> k \<Longrightarrow> \<sigma> k \<notin> S) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
  using restriction_closedD by blast

lemma restriction_closed_UNIV  [simp] : \<open>closed\<^sub>\<down> UNIV\<close>
  and restriction_closed_empty [simp] : \<open>closed\<^sub>\<down> {}\<close>
  by (simp_all add: restriction_closed_def)

end


subsection \<open>Balls\<close>

context restriction begin

definition restriction_cball :: \<open>'a \<Rightarrow> nat \<Rightarrow> 'a set\<close> (\<open>\<B>\<^sub>\<down>'(_, _')\<close>)
  where \<open>\<B>\<^sub>\<down>(a, n) \<equiv> {x. x \<down> n = a \<down> n}\<close>

lemma restriction_cball_mem_iff : \<open>x \<in> \<B>\<^sub>\<down>(a, n) \<longleftrightarrow>  x \<down> n = a \<down> n\<close>
  and restriction_cball_memI    : \<open>x \<down> n = a \<down> n \<Longrightarrow> x \<in> \<B>\<^sub>\<down>(a, n)\<close>
  and restriction_cball_memD    : \<open>x \<in> \<B>\<^sub>\<down>(a, n) \<Longrightarrow> x \<down> n = a \<down> n\<close>
  by (simp_all add: restriction_cball_def)



abbreviation (iff) restriction_ball :: \<open>'a \<Rightarrow> nat \<Rightarrow> 'a set\<close>
  where \<open>restriction_ball a n \<equiv> \<B>\<^sub>\<down>(a, Suc n)\<close>

lemma \<open>x \<in> restriction_ball a n \<longleftrightarrow>  x \<down> Suc n = a \<down> Suc n\<close>
  and \<open>x \<down> Suc n = a \<down> Suc n \<Longrightarrow> x \<in> restriction_ball a n\<close>
  and \<open>x \<in> restriction_ball a n \<Longrightarrow> x \<down> Suc n = a \<down> Suc n\<close>
  by (simp_all add: restriction_cball_def)



lemma \<open>a \<in> restriction_ball a n\<close>
  and center_mem_restriction_cball [simp] : \<open>a \<in> \<B>\<^sub>\<down>(a, n)\<close>
  by (simp_all add: restriction_cball_memI)

lemma (in restriction_space) restriction_cball_0_is_UNIV [simp] :
  \<open>\<B>\<^sub>\<down>(a, 0) = UNIV\<close> by (simp add: restriction_cball_def)




lemma every_point_of_restriction_cball_is_centre :
  \<open>b \<in> \<B>\<^sub>\<down>(a, n) \<Longrightarrow> \<B>\<^sub>\<down>(a, n) = \<B>\<^sub>\<down>(b, n)\<close>
  by (simp add: restriction_cball_def)


lemma \<open>b \<in> restriction_ball a n \<Longrightarrow> restriction_ball a n = restriction_ball b n\<close>
  by (simp add: every_point_of_restriction_cball_is_centre)


definition restriction_sphere :: \<open>'a \<Rightarrow> nat \<Rightarrow> 'a set\<close> (\<open>\<S>\<^sub>\<down>'(_, _')\<close>)
  where \<open>\<S>\<^sub>\<down>(a, n) \<equiv> {x. x \<down> n = a \<down> n \<and> x \<down> Suc n \<noteq> a \<down> Suc n}\<close>

lemma restriction_sphere_mem_iff : \<open>x \<in> \<S>\<^sub>\<down>(a, n) \<longleftrightarrow> x \<down> n = a \<down> n \<and> x \<down> Suc n \<noteq> a \<down> Suc n\<close>
  and restriction_sphere_memI    : \<open>x \<down> n = a \<down> n \<Longrightarrow> x \<down> Suc n \<noteq> a \<down> Suc n \<Longrightarrow> x \<in> \<S>\<^sub>\<down>(a, n)\<close>
  and restriction_sphere_memD1   : \<open>x \<in> \<S>\<^sub>\<down>(a, n) \<Longrightarrow> x \<down> n = a \<down> n\<close>
  and restriction_sphere_memD2   : \<open>x \<in> \<S>\<^sub>\<down>(a, n) \<Longrightarrow> x \<down> Suc n \<noteq> a \<down> Suc n\<close>
  by (simp_all add: restriction_sphere_def)

lemma restriction_sphere_is_diff : \<open>\<S>\<^sub>\<down>(a, n) = \<B>\<^sub>\<down>(a, n) - \<B>\<^sub>\<down>(a, Suc n)\<close>
  by (simp add: set_eq_iff restriction_sphere_mem_iff restriction_cball_mem_iff)




lemma restriction_open_restriction_cball [simp] : \<open>open\<^sub>\<down> \<B>\<^sub>\<down>(a, n)\<close>
  by (metis restriction_cball_mem_iff restriction_tendstoE restriction_openI)

lemma restriction_closed_restriction_cball [simp] : \<open>closed\<^sub>\<down> \<B>\<^sub>\<down>(a, n)\<close>
  by (metis restriction_cball_mem_iff restriction_closedI restriction_tendstoE)

lemma restriction_open_Compl_iff : \<open>open\<^sub>\<down> (- S) \<longleftrightarrow> closed\<^sub>\<down> S\<close>
  by (simp add: restriction_closed_def)

lemma restriction_open_restriction_sphere [simp] : \<open>open\<^sub>\<down> \<S>\<^sub>\<down>(a, n)\<close>
  by (simp add: restriction_sphere_is_diff Diff_eq
      restriction_open_Compl_iff restriction_open_inter)

lemma restriction_closed_restriction_sphere : \<open>closed\<^sub>\<down> \<S>\<^sub>\<down>(a, n)\<close>
  by (simp add: restriction_closed_def restriction_sphere_is_diff)
    (simp add: restriction_open_union restriction_open_Compl_iff)

end


context restriction_space begin

lemma restriction_cball_anti_mono : \<open>n \<le> m \<Longrightarrow> \<B>\<^sub>\<down>(a, m) \<subseteq> \<B>\<^sub>\<down>(a, n)\<close>
  by (meson restriction_cball_memD restriction_cball_memI restriction_related_le subsetI)

lemma inside_every_cball_iff_eq : \<open>(\<forall>n. x \<in> \<B>\<^sub>\<down>(\<Sigma>, n)) \<longleftrightarrow> x = \<Sigma>\<close>
  by (simp add: all_restriction_related_iff_related restriction_cball_mem_iff)



lemma Inf_many_inside_cball_iff_eq : \<open>(\<exists>\<^sub>\<infinity>n. x \<in> \<B>\<^sub>\<down>(\<Sigma>, n)) \<longleftrightarrow> x = \<Sigma>\<close>
  by (unfold INFM_nat_le)
    (meson inside_every_cball_iff_eq nle_le restriction_cball_anti_mono subset_eq)

lemma Inf_many_inside_cball_imp_eq : \<open>\<exists>\<^sub>\<infinity>n. x \<in> \<B>\<^sub>\<down>(\<Sigma>, n) \<Longrightarrow> x = \<Sigma>\<close>
  by (simp add: Inf_many_inside_cball_iff_eq)



lemma restriction_cballs_disjoint_or_subset :
  \<open>\<B>\<^sub>\<down>(a, n) \<inter> \<B>\<^sub>\<down>(b, m) = {} \<or> \<B>\<^sub>\<down>(a, n) \<subseteq> \<B>\<^sub>\<down>(b, m) \<or> \<B>\<^sub>\<down>(b, m) \<subseteq> \<B>\<^sub>\<down>(a, n)\<close>
proof (unfold disj_imp, intro impI)
  assume \<open>\<B>\<^sub>\<down>(a, n) \<inter> \<B>\<^sub>\<down>(b, m) \<noteq> {}\<close> \<open>\<not> \<B>\<^sub>\<down>(a, n) \<subseteq> \<B>\<^sub>\<down>(b, m)\<close>
  from \<open>\<B>\<^sub>\<down>(a, n) \<inter> \<B>\<^sub>\<down>(b, m) \<noteq> {}\<close> obtain x where \<open>x \<in> \<B>\<^sub>\<down>(a, n)\<close> \<open>x \<in> \<B>\<^sub>\<down>(b, m)\<close> by blast
  with every_point_of_restriction_cball_is_centre
  have \<open>\<B>\<^sub>\<down>(a, n) = \<B>\<^sub>\<down>(x, n)\<close> \<open>\<B>\<^sub>\<down>(b, m) = \<B>\<^sub>\<down>(x, m)\<close> by auto
  with \<open>\<not> \<B>\<^sub>\<down>(a, n) \<subseteq> \<B>\<^sub>\<down>(b, m)\<close> show \<open>\<B>\<^sub>\<down>(b, m) \<subseteq> \<B>\<^sub>\<down>(a, n)\<close>
    by (metis nle_le restriction_cball_anti_mono)
qed



lemma equal_restriction_to_cball :
  \<open>a \<notin> \<B>\<^sub>\<down>(b, n) \<Longrightarrow> x \<in> \<B>\<^sub>\<down>(b, n) \<Longrightarrow> y \<in> \<B>\<^sub>\<down>(b, n) \<Longrightarrow> x \<down> k = a \<down> k \<longleftrightarrow> y \<down> k = a \<down> k\<close>
  by (metis nat_le_linear restriction_cball_memD restriction_cball_memI restriction_related_le)

end


context restriction begin

lemma restriction_tendsto_iff_restriction_cball_characterization :
  \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<longleftrightarrow> (\<forall>n. \<exists>n0. \<forall>k\<ge>n0. \<sigma> k \<in> \<B>\<^sub>\<down>(\<Sigma>, n))\<close>
  by (metis restriction_cball_mem_iff restriction_tendsto_def)

corollary restriction_tendsto_restriction_cballI : \<open>(\<And>n. \<exists>n0. \<forall>k\<ge>n0. \<sigma> k \<in> \<B>\<^sub>\<down>(\<Sigma>, n)) \<Longrightarrow> \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
  by (simp add: restriction_tendsto_iff_restriction_cball_characterization)

corollary restriction_tendsto_restriction_cballD : \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<Longrightarrow> \<exists>n0. \<forall>k\<ge>n0. \<sigma> k \<in> \<B>\<^sub>\<down>(\<Sigma>, n)\<close>
  by (simp add: restriction_tendsto_iff_restriction_cball_characterization)

corollary restriction_tendsto_restriction_cballE :
  \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<Longrightarrow> (\<And>n0. (\<And>k. n0 \<le> k \<Longrightarrow> \<sigma> k \<in> \<B>\<^sub>\<down>(\<Sigma>, n)) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
  using restriction_tendsto_restriction_cballD by blast

end



context restriction begin

theorem restriction_closed_iff_sequential_characterization :
  \<open>closed\<^sub>\<down> S \<longleftrightarrow> (\<forall>\<Sigma> \<sigma>. range \<sigma> \<subseteq> S \<longrightarrow> \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<longrightarrow> \<Sigma> \<in> S)\<close>
proof (intro iffI allI impI)
  show \<open>restriction_closed S \<Longrightarrow> range \<sigma> \<subseteq> S \<Longrightarrow> \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<Longrightarrow> \<Sigma> \<in> S\<close> for \<Sigma> \<sigma>
    by (meson le_add1 range_subsetD restriction_closedD)
next
  assume * : \<open>\<forall>\<Sigma> \<sigma>. range \<sigma> \<subseteq> S \<longrightarrow> \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<longrightarrow> \<Sigma> \<in> S\<close>
  show \<open>closed\<^sub>\<down> S\<close>
  proof (rule restriction_closedI, rule ccontr)
    fix \<Sigma> \<sigma> assume \<open>\<Sigma> \<notin> S\<close> \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> \<open>\<nexists>n0. \<forall>k\<ge>n0. \<sigma> k \<notin> S\<close>
    from \<open>\<nexists>n0. \<forall>k\<ge>n0. \<sigma> k \<notin> S\<close> INFM_nat_le have \<open>\<exists>\<^sub>\<infinity>k. \<sigma> k \<in> S\<close> by auto
    from this[THEN extraction_subseqD[of \<open>\<lambda>x. x \<in> S\<close>]]
    obtain f :: \<open>nat \<Rightarrow> nat\<close> where \<open>strict_mono f\<close> \<open>\<forall>k. \<sigma> (f k) \<in> S\<close> by blast
    from \<open>\<forall>k. \<sigma> (f k) \<in> S\<close> have \<open>range (\<sigma> \<circ> f) \<subseteq> S\<close> by auto
    moreover from \<open>strict_mono f\<close> \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> have \<open>(\<sigma> \<circ> f) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
      by (fact restriction_tendsto_subseq)
    ultimately have \<open>\<Sigma> \<in> S\<close> by (fact "*"[rule_format])
    with \<open>\<Sigma> \<notin> S\<close> show False ..
  qed
qed


corollary restriction_closed_sequentialI :
  \<open>(\<And>\<Sigma> \<sigma>. range \<sigma> \<subseteq> S \<Longrightarrow> \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<Longrightarrow> \<Sigma> \<in> S) \<Longrightarrow> closed\<^sub>\<down> S\<close>
  by (simp add: restriction_closed_iff_sequential_characterization)

corollary restriction_closed_sequentialD :
  \<open>closed\<^sub>\<down> S \<Longrightarrow> range \<sigma> \<subseteq> S \<Longrightarrow> \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<Longrightarrow> \<Sigma> \<in> S\<close>
  by (simp add: restriction_closed_iff_sequential_characterization)

end



context restriction_space begin

theorem restriction_open_iff_restriction_cball_characterization :
  \<open>open\<^sub>\<down> U \<longleftrightarrow> (\<forall>\<Sigma>\<in>U. \<exists>n. \<B>\<^sub>\<down>(\<Sigma>, n) \<subseteq> U)\<close>
proof (intro iffI ballI)
  show \<open>open\<^sub>\<down> U \<Longrightarrow> \<Sigma> \<in> U \<Longrightarrow> \<exists>n. \<B>\<^sub>\<down>(\<Sigma>, n) \<subseteq> U\<close> for \<Sigma>
  proof (rule ccontr)
    assume \<open>open\<^sub>\<down> U\<close> \<open>\<Sigma> \<in> U\<close> \<open>\<nexists>n. \<B>\<^sub>\<down>(\<Sigma>, n) \<subseteq> U\<close>
    from \<open>\<nexists>n. \<B>\<^sub>\<down>(\<Sigma>, n) \<subseteq> U\<close> have \<open>\<forall>n. \<exists>\<sigma>. \<sigma> \<in> \<B>\<^sub>\<down>(\<Sigma>, n) \<inter> - U\<close> by auto
    then obtain \<sigma> where \<open>\<sigma> n \<in> \<B>\<^sub>\<down>(\<Sigma>, n)\<close> \<open>\<sigma> n \<in> - U\<close> for n by (metis IntE)
    from \<open>\<And>n. \<sigma> n \<in> \<B>\<^sub>\<down>(\<Sigma>, n)\<close> have \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> 
      by (metis restriction_cball_memD restriction_related_le restriction_tendstoI)
    moreover from \<open>open\<^sub>\<down> U\<close> have \<open>closed\<^sub>\<down> (- U)\<close>
      by (simp add: restriction_closed_def)
    ultimately have \<open>\<Sigma> \<in> - U\<close>
      using \<open>\<And>n. \<sigma> n \<in> - U\<close> restriction_closedD by blast
    with \<open>\<Sigma> \<in> U\<close> show False by simp
  qed
next
  show \<open>\<forall>\<Sigma>\<in>U. \<exists>n. \<B>\<^sub>\<down>(\<Sigma>, n) \<subseteq> U \<Longrightarrow> open\<^sub>\<down> U\<close>
    by (metis center_mem_restriction_cball restriction_open_def
        restriction_open_restriction_cball subset_iff)
qed


corollary restriction_open_restriction_cballI :
  \<open>(\<And>\<Sigma>. \<Sigma> \<in> U \<Longrightarrow> \<exists>n. \<B>\<^sub>\<down>(\<Sigma>, n) \<subseteq> U) \<Longrightarrow> open\<^sub>\<down> U\<close>
  by (simp add: restriction_open_iff_restriction_cball_characterization)

corollary restriction_open_restriction_cballD :
  \<open>open\<^sub>\<down> U \<Longrightarrow> \<Sigma> \<in> U \<Longrightarrow> \<exists>n. \<B>\<^sub>\<down>(\<Sigma>, n) \<subseteq> U\<close>
  by (simp add: restriction_open_iff_restriction_cball_characterization)

corollary restriction_open_restriction_cballE :
  \<open>open\<^sub>\<down> U \<Longrightarrow> \<Sigma> \<in> U \<Longrightarrow> (\<And>n. \<B>\<^sub>\<down>(\<Sigma>, n) \<subseteq> U \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
  using restriction_open_restriction_cballD by blast

end


context restriction begin

definition restriction_cont_on :: \<open>['b :: restriction \<Rightarrow> 'a, 'b set] \<Rightarrow> bool\<close>
  (\<open>cont\<^sub>\<down> (_) on (_)\<close> [1000, 1000])
  where \<open>cont\<^sub>\<down> f on A \<equiv> \<forall>\<Sigma>\<in>A. cont\<^sub>\<down> f at \<Sigma>\<close>

lemma restriction_cont_onI : \<open>(\<And>\<Sigma> \<sigma>. \<Sigma> \<in> A \<Longrightarrow> \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<Longrightarrow> (\<lambda>n. f (\<sigma> n)) \<midarrow>\<down>\<rightarrow> f \<Sigma>) \<Longrightarrow> cont\<^sub>\<down> f on A\<close>
  by (simp add: restriction_cont_on_def restriction_cont_atI)

lemma restriction_cont_onD : \<open>cont\<^sub>\<down> f on A \<Longrightarrow> \<Sigma> \<in> A \<Longrightarrow> \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<Longrightarrow> (\<lambda>n. f (\<sigma> n)) \<midarrow>\<down>\<rightarrow> f \<Sigma>\<close>
  by (simp add: restriction_cont_on_def restriction_cont_atD)

lemma restriction_cont_on_comp [restriction_cont_simpset] :
  \<open>cont\<^sub>\<down> f on A \<Longrightarrow> cont\<^sub>\<down> g on B \<Longrightarrow> f ` A \<subseteq> B \<Longrightarrow> cont\<^sub>\<down> (\<lambda>x. g (f x)) on A\<close>
  by (simp add: image_subset_iff restriction_cont_at_comp
      restriction_cont_on_def restriction_class.restriction_cont_on_def)

lemma restriction_cont_on_if_then_else [restriction_cont_simpset] :
  \<open>\<lbrakk>\<And>x. P x \<Longrightarrow> cont\<^sub>\<down> (f x) on A; \<And>x. \<not> P x \<Longrightarrow> cont\<^sub>\<down> (g x) on A\<rbrakk>
   \<Longrightarrow> cont\<^sub>\<down> (\<lambda>y. if P x then f x y else g x y) on A\<close>
  by (auto intro!: restriction_cont_onI) (blast dest: restriction_cont_onD)+

lemma restriction_cont_on_subset [restriction_cont_simpset] :
  \<open>cont\<^sub>\<down> f on B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> cont\<^sub>\<down> f on A\<close>
  by (simp add: restriction_cont_on_def subset_iff)


abbreviation restriction_cont :: \<open>['b :: restriction \<Rightarrow> 'a] \<Rightarrow> bool\<close> (\<open>cont\<^sub>\<down>\<close>)
  where \<open>cont\<^sub>\<down> f \<equiv> cont\<^sub>\<down> f on UNIV\<close>

lemma restriction_contI : \<open>(\<And>\<Sigma> \<sigma>. \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<Longrightarrow> (\<lambda>n. f (\<sigma> n)) \<midarrow>\<down>\<rightarrow> f \<Sigma>) \<Longrightarrow> cont\<^sub>\<down> f\<close>
  by (simp add: restriction_cont_onI)

lemma restriction_contD : \<open>cont\<^sub>\<down> f \<Longrightarrow> \<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma> \<Longrightarrow> (\<lambda>n. f (\<sigma> n)) \<midarrow>\<down>\<rightarrow> f \<Sigma>\<close>
  by (simp add: restriction_cont_onD)

lemma restriction_cont_comp [restriction_cont_simpset] :
  \<open>cont\<^sub>\<down> g \<Longrightarrow> cont\<^sub>\<down> f \<Longrightarrow> cont\<^sub>\<down> (\<lambda>x. g (f x))\<close>
  by (simp add: restriction_cont_on_comp)

lemma restriction_cont_if_then_else [restriction_cont_simpset] :
  \<open>\<lbrakk>\<And>x. P x \<Longrightarrow> cont\<^sub>\<down> (f x); \<And>x. \<not> P x \<Longrightarrow> cont\<^sub>\<down> (g x)\<rbrakk>
   \<Longrightarrow> cont\<^sub>\<down> (\<lambda>y. if P x then f x y else g x y)\<close>
  by (auto intro!: restriction_contI) (blast dest: restriction_contD)+

end



context restriction_space begin

theorem restriction_cont_at_iff_restriction_cball_characterization :
  \<open>cont\<^sub>\<down> f at \<Sigma> \<longleftrightarrow> (\<forall>n. \<exists>k. f ` \<B>\<^sub>\<down>(\<Sigma>, k) \<subseteq> \<B>\<^sub>\<down>(f \<Sigma>, n))\<close>
  for f :: \<open>'b :: restriction_space \<Rightarrow> 'a\<close>
proof (intro iffI allI)
  show \<open>\<exists>k. f ` \<B>\<^sub>\<down>(\<Sigma>, k) \<subseteq> \<B>\<^sub>\<down>(f \<Sigma>, n)\<close> if \<open>cont\<^sub>\<down> f at \<Sigma>\<close> for n
  proof (rule ccontr)
    assume \<open>\<nexists>k. f ` \<B>\<^sub>\<down>(\<Sigma>, k) \<subseteq> \<B>\<^sub>\<down>(f \<Sigma>, n)\<close>
    hence \<open>\<forall>k. \<exists>\<psi>. \<psi> \<in> f ` \<B>\<^sub>\<down>(\<Sigma>, k) \<and> \<psi> \<notin> \<B>\<^sub>\<down>(f \<Sigma>, n)\<close> by auto
    then obtain \<psi> where * : \<open>\<psi> k \<in> f ` \<B>\<^sub>\<down>(\<Sigma>, k)\<close> \<open>\<psi> k \<notin> \<B>\<^sub>\<down>(f \<Sigma>, n)\<close> for k by metis
    from "*"(1) obtain \<sigma> where ** : \<open>\<sigma> k \<in> \<B>\<^sub>\<down>(\<Sigma>, k)\<close> \<open>\<psi> k = f (\<sigma> k)\<close> for k
      by (simp add: image_iff) metis
    have \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
      by (rule restriction_class.restriction_tendsto_restriction_cballI)
        (use "**"(1) restriction_space_class.restriction_cball_anti_mono in blast)
    with restriction_cont_atD \<open>restriction_cont_at f \<Sigma>\<close>
    have \<open>(\<lambda>k. f (\<sigma> k)) \<midarrow>\<down>\<rightarrow> f \<Sigma>\<close> by blast
    hence \<open>\<psi> \<midarrow>\<down>\<rightarrow> f \<Sigma>\<close> by (fold "**"(2))
    with "*"(2) restriction_tendsto_restriction_cballD show False by blast
  qed
next
  show \<open>\<forall>n. \<exists>k. f ` \<B>\<^sub>\<down>(\<Sigma>, k) \<subseteq> \<B>\<^sub>\<down>(f \<Sigma>, n) \<Longrightarrow> cont\<^sub>\<down> f at \<Sigma>\<close>
    by (intro restriction_cont_atI restriction_tendsto_restriction_cballI)
      (meson image_iff restriction_class.restriction_tendsto_restriction_cballD subset_eq)
qed


corollary restriction_cont_at_restriction_cballI :
  \<open>(\<And>n. \<exists>k. f ` \<B>\<^sub>\<down>(\<Sigma>, k) \<subseteq> \<B>\<^sub>\<down>(f \<Sigma>, n)) \<Longrightarrow> cont\<^sub>\<down> f at \<Sigma>\<close>
  for f :: \<open>'b :: restriction_space \<Rightarrow> 'a\<close>
  by (simp add: restriction_cont_at_iff_restriction_cball_characterization)

corollary restriction_cont_at_restriction_cballD :
  \<open>cont\<^sub>\<down> f at \<Sigma> \<Longrightarrow> \<exists>k. f ` \<B>\<^sub>\<down>(\<Sigma>, k) \<subseteq> \<B>\<^sub>\<down>(f \<Sigma>, n)\<close>
  for f :: \<open>'b :: restriction_space \<Rightarrow> 'a\<close>
  by (simp add: restriction_cont_at_iff_restriction_cball_characterization)

corollary restriction_cont_at_restriction_cballE :
  \<open>cont\<^sub>\<down> f at \<Sigma> \<Longrightarrow> (\<And>k. f ` \<B>\<^sub>\<down>(\<Sigma>, k) \<subseteq> \<B>\<^sub>\<down>(f \<Sigma>, n) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
  for f :: \<open>'b :: restriction_space \<Rightarrow> 'a\<close>
  using restriction_cont_at_restriction_cballD by blast



theorem restriction_cont_iff_restriction_open_characterization :
  \<open>cont\<^sub>\<down> f \<longleftrightarrow> (\<forall>U. open\<^sub>\<down> U \<longrightarrow> open\<^sub>\<down> (f -` U))\<close>
  for f :: \<open>'b :: restriction_space \<Rightarrow> 'a\<close>
proof (intro iffI allI impI)
  fix U :: \<open>'a set\<close> assume \<open>cont\<^sub>\<down> f\<close> \<open>open\<^sub>\<down> U\<close>
  show \<open>open\<^sub>\<down> (f -` U)\<close>
  proof (rule restriction_space_class.restriction_open_restriction_cballI)
    fix \<Sigma> assume \<open>\<Sigma> \<in> f -` U\<close>
    hence \<open>f \<Sigma> \<in> U\<close> by simp
    with \<open>open\<^sub>\<down> U\<close> restriction_open_restriction_cballD
    obtain n where \<open>\<B>\<^sub>\<down>(f \<Sigma>, n) \<subseteq> U\<close> by blast
    moreover obtain k where \<open>f ` \<B>\<^sub>\<down>(\<Sigma>, k) \<subseteq> \<B>\<^sub>\<down>(f \<Sigma>, n)\<close>
      by (meson UNIV_I \<open>cont\<^sub>\<down> f\<close> restriction_cont_at_restriction_cballE restriction_cont_on_def)
    ultimately have \<open>\<B>\<^sub>\<down>(\<Sigma>, k) \<subseteq> f -` U\<close> by blast
    thus \<open>\<exists>k. \<B>\<^sub>\<down>(\<Sigma>, k) \<subseteq> f -` U\<close> ..
  qed
next
  show \<open>\<forall>U. open\<^sub>\<down> U \<longrightarrow> open\<^sub>\<down> (f -` U) \<Longrightarrow> cont\<^sub>\<down> f\<close>
    by (unfold restriction_cont_on_def, intro ballI restriction_cont_at_restriction_cballI)
      (simp add: image_subset_iff_subset_vimage restriction_space_class.restriction_open_restriction_cballD)
qed

corollary restriction_cont_restriction_openI :
  \<open>(\<And>U. open\<^sub>\<down> U \<Longrightarrow> open\<^sub>\<down> (f -` U)) \<Longrightarrow> cont\<^sub>\<down> f\<close>
  for f :: \<open>'b :: restriction_space \<Rightarrow> 'a\<close>
  by (simp add: restriction_cont_iff_restriction_open_characterization)

corollary restriction_cont_restriction_openD :
  \<open>cont\<^sub>\<down> f \<Longrightarrow> open\<^sub>\<down> U \<Longrightarrow> open\<^sub>\<down> (f -` U)\<close>
  for f :: \<open>'b :: restriction_space \<Rightarrow> 'a\<close>
  by (simp add: restriction_cont_iff_restriction_open_characterization)


theorem restriction_cont_iff_restriction_closed_characterization :
  \<open>cont\<^sub>\<down> f \<longleftrightarrow> (\<forall>S. closed\<^sub>\<down> S \<longrightarrow> closed\<^sub>\<down> (f -` S))\<close>
  for f :: \<open>'b :: restriction_space \<Rightarrow> 'a\<close>
  by (metis boolean_algebra_class.boolean_algebra.double_compl local.restriction_closed_def
      restriction_class.restriction_closed_def restriction_cont_iff_restriction_open_characterization vimage_Compl)

corollary restriction_cont_restriction_closedI :
  \<open>(\<And>U. closed\<^sub>\<down> U \<Longrightarrow> closed\<^sub>\<down> (f -` U)) \<Longrightarrow> cont\<^sub>\<down> f\<close>
  for f :: \<open>'b :: restriction_space \<Rightarrow> 'a\<close>
  by (simp add: restriction_cont_iff_restriction_closed_characterization)

corollary restriction_cont_restriction_closedD :
  \<open>cont\<^sub>\<down> f \<Longrightarrow> closed\<^sub>\<down> U \<Longrightarrow> closed\<^sub>\<down> (f -` U)\<close>
  for f :: \<open>'b :: restriction_space \<Rightarrow> 'a\<close>
  by (simp add: restriction_cont_iff_restriction_closed_characterization)


theorem restriction_shift_on_restriction_open_imp_restriction_cont_on :
  \<open>cont\<^sub>\<down> f on U\<close> if \<open>open\<^sub>\<down> U\<close> and \<open>restriction_shift_on f k U\<close>
proof (intro restriction_cont_onI restriction_tendstoI)
  fix \<Sigma> \<sigma> and n :: nat assume \<open>\<Sigma> \<in> U\<close> \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
  with \<open>open\<^sub>\<down> U\<close> obtain n0 where \<open>\<forall>l\<ge>n0. \<sigma> l \<in> U\<close>
    by (meson restriction_class.restriction_openD)
  moreover from \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>[THEN restriction_class.restriction_tendstoD]
  obtain n1 where \<open>\<forall>l\<ge>n1. \<Sigma> \<down> nat (int n - k) = \<sigma> l \<down> nat (int n - k)\<close> ..
  ultimately have \<open>\<forall>l\<ge>max n0 n1. \<sigma> l \<in> U \<and> \<Sigma> \<down> nat (int n - k) = \<sigma> l \<down> nat (int n - k)\<close> by simp
  with \<open>\<Sigma> \<in> U\<close> \<open>restriction_shift_on f k U\<close> restriction_shift_onD
  have \<open>\<forall>l\<ge>max n0 n1. f \<Sigma> \<down> nat (int (nat (int n - k)) + k) = f (\<sigma> l) \<down> nat (int (nat (int n - k)) + k)\<close> by blast
  moreover have \<open>n \<le> nat (int (nat (int n - k)) + k)\<close> by auto
  ultimately have \<open>\<forall>l\<ge>max n0 n1. f \<Sigma> \<down> n = f (\<sigma> l) \<down> n\<close> by (meson restriction_related_le)
  thus \<open>\<exists>n2. \<forall>l\<ge>n2. f \<Sigma> \<down> n = f (\<sigma> l) \<down> n\<close> by blast
qed

corollary restriction_shift_imp_restriction_cont [restriction_cont_simpset] :
  \<open>restriction_shift f k \<Longrightarrow> cont\<^sub>\<down> f\<close>
  by (simp add: restriction_shift_def
      restriction_shift_on_restriction_open_imp_restriction_cont_on)

corollary non_too_destructive_imp_restriction_cont [restriction_cont_simpset] :
  \<open>non_too_destructive f \<Longrightarrow> cont\<^sub>\<down> f\<close>
  by (simp add: non_too_destructive_def non_too_destructive_on_def
      restriction_shift_on_restriction_open_imp_restriction_cont_on)


end



subsection \<open>Compactness\<close>

context restriction begin

definition restriction_compact :: \<open>'a set \<Rightarrow> bool\<close> (\<open>compact\<^sub>\<down>\<close>)
  where \<open>compact\<^sub>\<down> K \<equiv>
         \<forall>\<sigma>. range \<sigma> \<subseteq> K \<longrightarrow>
         (\<exists>f :: nat \<Rightarrow> nat. \<exists>\<Sigma>. \<Sigma> \<in> K \<and> strict_mono f \<and> (\<sigma> \<circ> f) \<midarrow>\<down>\<rightarrow> \<Sigma>)\<close>


lemma restriction_compactI :
  \<open>(\<And>\<sigma>. range \<sigma> \<subseteq> K \<Longrightarrow> \<exists>f :: nat \<Rightarrow> nat. \<exists>\<Sigma>. \<Sigma> \<in> K \<and> strict_mono f \<and> (\<sigma> \<circ> f) \<midarrow>\<down>\<rightarrow> \<Sigma>)
   \<Longrightarrow> compact\<^sub>\<down> K\<close> by (simp add: restriction_compact_def)

lemma restriction_compactD :
  \<open>compact\<^sub>\<down> K \<Longrightarrow> range \<sigma> \<subseteq> K \<Longrightarrow>
   \<exists>f :: nat \<Rightarrow> nat. \<exists>\<Sigma>. \<Sigma> \<in> K \<and> strict_mono f \<and> (\<sigma> \<circ> f) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
  by (simp add: restriction_compact_def)

lemma restriction_compactE :
  assumes \<open>compact\<^sub>\<down> K\<close> and \<open>range \<sigma> \<subseteq> K\<close>
  obtains f :: \<open>nat \<Rightarrow> nat\<close> and \<Sigma> where \<open>\<Sigma> \<in> K\<close> \<open>strict_mono f\<close> \<open>(\<sigma> \<circ> f) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
  by (meson assms restriction_compactD)

lemma restriction_compact_empty [simp] : \<open>compact\<^sub>\<down> {}\<close>
  by (simp add: restriction_compact_def)



lemma (in restriction_space) restriction_compact_imp_restriction_closed :
  \<open>closed\<^sub>\<down> K\<close> if \<open>compact\<^sub>\<down> K\<close>
proof (rule restriction_closed_sequentialI)
  fix \<sigma> \<Sigma> assume \<open>range \<sigma> \<subseteq> K\<close> \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
  from restriction_compactD \<open>compact\<^sub>\<down> K\<close> \<open>range \<sigma> \<subseteq> K\<close> 
  obtain f and \<Sigma>' where \<open>\<Sigma>' \<in> K\<close> \<open>strict_mono f\<close> \<open>(\<sigma> \<circ> f) \<midarrow>\<down>\<rightarrow> \<Sigma>'\<close> by blast
  from restriction_tendsto_subseq \<open>strict_mono f\<close> \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
  have \<open>(\<sigma> \<circ> f) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> by blast
  with \<open>(\<sigma> \<circ> f) \<midarrow>\<down>\<rightarrow> \<Sigma>'\<close> have \<open>\<Sigma>' = \<Sigma>\<close> by (fact restriction_tendsto_unique)
  with \<open>\<Sigma>' \<in> K\<close> show \<open>\<Sigma> \<in> K\<close> by simp
qed


lemma restriction_compact_union : \<open>compact\<^sub>\<down> (K \<union> L)\<close>
  if \<open>compact\<^sub>\<down> K\<close> and \<open>compact\<^sub>\<down> L\<close>
proof (rule restriction_compactI)
  fix \<sigma> :: \<open>nat \<Rightarrow> _\<close> assume \<open>range \<sigma> \<subseteq> K \<union> L\<close>
  { fix K L and f :: \<open>nat \<Rightarrow> nat\<close>
    assume \<open>compact\<^sub>\<down> K\<close> \<open>strict_mono f\<close> \<open>\<sigma> (f n) \<in> K\<close> for n
    from \<open>(\<And>n. \<sigma> (f n) \<in> K)\<close> have \<open>range (\<sigma> \<circ> f) \<subseteq> K\<close> by auto
    with \<open>compact\<^sub>\<down> K\<close> restriction_compactD obtain g \<Sigma>
      where \<open>\<Sigma> \<in> K\<close> \<open>strict_mono g\<close> \<open>(\<sigma> \<circ> f \<circ> g) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> by blast
    hence \<open>\<Sigma> \<in> K \<union> L \<and> strict_mono (f \<circ> g) \<and> (\<sigma> \<circ> (f \<circ> g)) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
      by (metis (no_types, lifting) Un_iff \<open>strict_mono f\<close> comp_assoc
          monotone_on_o subset_UNIV)
    hence \<open>\<exists>f \<Sigma>. \<Sigma> \<in> K \<union> L \<and> strict_mono f \<and> (\<sigma> \<circ> f) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> by blast
  } note * = this
  have \<open>(\<exists>\<^sub>\<infinity>n. \<sigma> n \<in> K) \<or> (\<exists>\<^sub>\<infinity>n. \<sigma> n \<in> L)\<close>
  proof (rule ccontr)
    assume \<open>\<not> ((\<exists>\<^sub>\<infinity>n. \<sigma> n \<in> K) \<or> (\<exists>\<^sub>\<infinity>n. \<sigma> n \<in> L))\<close>
    hence \<open>finite {n. \<sigma> n \<in> K} \<and> finite {n. \<sigma> n \<in> L}\<close>
      using frequently_cofinite by blast
    then obtain n where \<open>n \<notin> {n. \<sigma> n \<in> K} \<and> n \<notin> {n. \<sigma> n \<in> L}\<close>
      by (metis (mono_tags, lifting) INFM_nat_le dual_order.refl
          frequently_cofinite le_sup_iff mem_Collect_eq)
    hence \<open>\<sigma> n \<notin> K \<union> L\<close> by simp
    with \<open>range \<sigma> \<subseteq> K \<union> L\<close> show False by blast
  qed
  thus \<open>\<exists>f \<Sigma>. \<Sigma> \<in> K \<union> L \<and> strict_mono f \<and> (\<sigma> \<circ> f) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
    by (elim disjE extraction_subseqE)
      (use "*" \<open>compact\<^sub>\<down> K\<close> in blast, metis "*" Un_iff \<open>compact\<^sub>\<down> L\<close>)
qed

lemma restriction_compact_finite_Union :
  \<open>\<lbrakk>finite I; \<And>i. i \<in> I \<Longrightarrow> compact\<^sub>\<down> (K i)\<rbrakk> \<Longrightarrow> compact\<^sub>\<down> (\<Union>i\<in>I. K i)\<close>
  by (induct I rule: finite_induct)
    (simp_all add: restriction_compact_union)


lemma (in restriction_space) restriction_compact_Inter :
  \<open>compact\<^sub>\<down> (\<Inter>i. K i)\<close> if \<open>\<And>i. compact\<^sub>\<down> (K i)\<close>
proof (rule restriction_compactI)
  fix \<sigma> :: \<open>nat \<Rightarrow> 'a\<close> assume \<open>range \<sigma> \<subseteq> \<Inter> (range K)\<close>
  hence \<open>range \<sigma> \<subseteq> K i\<close> for i by blast
  with \<open>\<And>i. compact\<^sub>\<down> (K i)\<close> restriction_compactD
  obtain f \<Sigma> where \<open>strict_mono f\<close> \<open>(\<sigma> \<circ> f) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> by blast
  from \<open>\<And>i. compact\<^sub>\<down> (K i)\<close> have \<open>closed\<^sub>\<down> (K i)\<close> for i
    by (simp add: restriction_compact_imp_restriction_closed)
  moreover from \<open>\<And>i. range \<sigma> \<subseteq> K i\<close> have \<open>range (\<sigma> \<circ> f) \<subseteq> K i\<close> for i by auto
  ultimately have \<open>\<Sigma> \<in> K i\<close> for i
    by (meson \<open>(\<sigma> \<circ> f) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> restriction_closed_sequentialD)
  with \<open>strict_mono f\<close> \<open>(\<sigma> \<circ> f) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
  show \<open>\<exists>f \<Sigma>. \<Sigma> \<in> \<Inter> (range K) \<and> strict_mono f \<and> (\<sigma> \<circ> f) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> by blast
qed

lemma finite_imp_restriction_compact : \<open>compact\<^sub>\<down> K\<close> if \<open>finite K\<close>
proof (rule restriction_compactI)
  fix \<sigma> :: \<open>nat \<Rightarrow> _\<close> assume \<open>range \<sigma> \<subseteq> K\<close>
  have \<open>\<exists>\<Sigma>\<in>K. \<exists>\<^sub>\<infinity>n. \<sigma> n = \<Sigma>\<close>
  proof (rule ccontr)
    assume \<open>\<not> (\<exists>\<Sigma>\<in>K. \<exists>\<^sub>\<infinity>n. \<sigma> n = \<Sigma>)\<close>
    hence \<open>\<forall>\<Sigma>\<in>K. finite {n. \<sigma> n = \<Sigma>}\<close> by (simp add: frequently_cofinite)
    with \<open>finite K\<close> have \<open>finite (\<Union>\<Sigma>\<in>K. {n. \<sigma> n = \<Sigma>})\<close> by blast
    also from \<open>range \<sigma> \<subseteq> K\<close> have \<open>(\<Union>\<Sigma>\<in>K. {n. \<sigma> n = \<Sigma>}) = UNIV\<close> by auto
    finally show False by simp
  qed
  then obtain \<Sigma> where \<open>\<Sigma> \<in> K\<close> \<open>\<exists>\<^sub>\<infinity>n. \<sigma> n = \<Sigma>\<close> ..
  from extraction_subseqD[of _ \<sigma>, OF \<open>\<exists>\<^sub>\<infinity>n. \<sigma> n = \<Sigma>\<close>]
  obtain f :: \<open>nat \<Rightarrow> nat\<close> where \<open>strict_mono f\<close> \<open>\<sigma> (f n) = \<Sigma>\<close> for n by blast
  from \<open>\<And>n. \<sigma> (f n) = \<Sigma>\<close> have \<open>(\<sigma> \<circ> f) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
    by (simp add: restriction_tendstoI)
  with \<open>strict_mono f\<close> \<open>\<Sigma> \<in> K\<close>
  show \<open>\<exists>f \<Sigma>. \<Sigma> \<in> K \<and> strict_mono f \<and> (\<sigma> \<circ> f) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> by blast
qed


lemma restriction_compact_restriction_closed_subset : \<open>compact\<^sub>\<down> L\<close>
  if \<open>L \<subseteq> K\<close> \<open>compact\<^sub>\<down> K\<close> \<open>closed\<^sub>\<down> L\<close>
proof (rule restriction_compactI)
  fix \<sigma> :: \<open>nat \<Rightarrow> _\<close> assume \<open>range \<sigma> \<subseteq> L\<close>
  with \<open>L \<subseteq> K\<close> have \<open>range \<sigma> \<subseteq> K\<close> by blast
  with \<open>compact\<^sub>\<down> K\<close> restriction_compactD
  obtain f \<Sigma> where \<open>\<Sigma> \<in> K\<close> \<open>strict_mono f\<close> \<open>(\<sigma> \<circ> f) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> by blast
  from \<open>range \<sigma> \<subseteq> L\<close> have \<open>range (\<sigma> \<circ> f) \<subseteq> L\<close> by auto
  from restriction_closed_sequentialD \<open>restriction_closed L\<close>
    \<open>(\<sigma> \<circ> f) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> \<open>range (\<sigma> \<circ> f) \<subseteq> L\<close> have \<open>\<Sigma> \<in> L\<close> by blast
  with \<open>strict_mono f\<close> \<open>(\<sigma> \<circ> f) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
  show \<open>\<exists>f \<Sigma>. \<Sigma> \<in> L \<and> strict_mono f \<and> (\<sigma> \<circ> f) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> by blast
qed


lemma restriction_cont_image_of_restriction_compact :
  \<open>compact\<^sub>\<down> (f ` K)\<close> if \<open>compact\<^sub>\<down> K\<close> and \<open>cont\<^sub>\<down> f on K\<close>
proof (rule restriction_compactI)
  fix \<sigma> :: \<open>nat \<Rightarrow> _\<close> assume \<open>range \<sigma> \<subseteq> f ` K\<close>
  hence \<open>\<forall>n. \<exists>\<gamma>. \<gamma> \<in> K \<and> \<sigma> n = f \<gamma>\<close> by (meson imageE range_subsetD)
  then obtain \<gamma> :: \<open>nat \<Rightarrow> _\<close> where \<open>range \<gamma> \<subseteq> K\<close> \<open>\<sigma> n = f (\<gamma> n)\<close> for n
    by (metis image_subsetI)
  from restriction_class.restriction_compactD[OF \<open>compact\<^sub>\<down> K\<close> \<open>range \<gamma> \<subseteq> K\<close>]
  obtain g \<Sigma> where \<open>\<Sigma> \<in> K\<close> \<open>strict_mono g\<close> \<open>(\<gamma> \<circ> g) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> by blast
  from \<open>cont\<^sub>\<down> f on K\<close> \<open>\<Sigma> \<in> K\<close>
  have \<open>cont\<^sub>\<down> f at \<Sigma>\<close> by (simp add: restriction_cont_on_def)
  with \<open>(\<gamma> \<circ> g) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> restriction_cont_atD
  have \<open>(\<lambda>n. f ((\<gamma> \<circ> g) n)) \<midarrow>\<down>\<rightarrow> f \<Sigma>\<close> by blast 
  also have \<open>(\<lambda>n. f ((\<gamma> \<circ> g) n)) = (\<sigma> \<circ> g)\<close>
    by (simp add: \<open>\<And>n. \<sigma> n = f (\<gamma> n)\<close> comp_def)
  finally have \<open>(\<sigma> \<circ> g) \<midarrow>\<down>\<rightarrow> f \<Sigma>\<close> .
  with \<open>\<Sigma> \<in> K\<close> \<open>strict_mono g\<close>
  show \<open>\<exists>g \<Sigma>. \<Sigma> \<in> f ` K \<and> strict_mono g \<and> (\<sigma> \<circ> g) \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> by blast
qed

end





subsection \<open>Properties for Function and Product\<close>

lemma restriction_cball_fun_is : \<open>\<B>\<^sub>\<down>(f, n) = {g. \<forall>x. g x \<in> \<B>\<^sub>\<down>(f x, n)}\<close>
  by (simp add: set_eq_iff restriction_cball_mem_iff restriction_fun_def) metis

lemma restriction_cball_prod_is :
  \<open>\<B>\<^sub>\<down>(\<Sigma>, n) = \<B>\<^sub>\<down>(fst \<Sigma>, n) \<times> \<B>\<^sub>\<down>(snd \<Sigma>, n)\<close>
  by (simp add: set_eq_iff restriction_cball_def restriction_prod_def)


lemma restriction_open_prod_imp_restriction_open_image_fst :
  \<open>open\<^sub>\<down> (fst ` U)\<close> if \<open>open\<^sub>\<down> U\<close>
proof (rule restriction_openI)
  fix \<Sigma> \<sigma> assume \<open>\<Sigma> \<in> fst ` U\<close> and \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
  from \<open>\<Sigma> \<in> fst ` U\<close> obtain v where \<open>(\<Sigma>, v) \<in> U\<close> by auto
  from \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> have \<open>(\<lambda>n. (\<sigma> n, v)) \<midarrow>\<down>\<rightarrow> (\<Sigma>, v)\<close>
    by (simp add: restriction_tendsto_prod_iff restriction_tendsto_const)
  from restriction_openD[OF \<open>restriction_open U\<close> \<open>(\<Sigma>, v) \<in> U\<close> this]
  obtain n0 where \<open>\<forall>k\<ge>n0. (\<sigma> k, v) \<in> U\<close> ..
  thus \<open>\<exists>n0. \<forall>k\<ge>n0. \<sigma> k \<in> fst ` U\<close> by (metis fst_conv imageI)
qed

lemma restriction_open_prod_imp_restriction_open_image_snd :
  \<open>open\<^sub>\<down> (snd ` U)\<close> if \<open>open\<^sub>\<down> U\<close>
proof (rule restriction_openI)
  fix \<Sigma> \<sigma> assume \<open>\<Sigma> \<in> snd ` U\<close> and \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
  from \<open>\<Sigma> \<in> snd ` U\<close> obtain u where \<open>(u, \<Sigma>) \<in> U\<close> by auto
  from \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> have \<open>(\<lambda>n. (u, \<sigma> n)) \<midarrow>\<down>\<rightarrow> (u, \<Sigma>)\<close>
    by (simp add: restriction_tendsto_prod_iff restriction_tendsto_const)
  from restriction_openD[OF \<open>restriction_open U\<close> \<open>(u, \<Sigma>) \<in> U\<close> this]
  obtain n0 where \<open>\<forall>k\<ge>n0. (u, \<sigma> k) \<in> U\<close> ..
  thus \<open>\<exists>n0. \<forall>k\<ge>n0. \<sigma> k \<in> snd ` U\<close> by (metis snd_conv imageI)
qed

lemma restriction_open_prod_iff :
  \<open>open\<^sub>\<down> (U \<times> V) \<longleftrightarrow> (V = {} \<or> open\<^sub>\<down> U) \<and> (U = {} \<or> open\<^sub>\<down> V)\<close>
proof (intro iffI conjI)
  show \<open>open\<^sub>\<down> (U \<times> V) \<Longrightarrow> V = {} \<or> open\<^sub>\<down> U\<close>
    by (metis fst_image_times restriction_open_prod_imp_restriction_open_image_fst)
next
  show \<open>open\<^sub>\<down> (U \<times> V) \<Longrightarrow> U = {} \<or> open\<^sub>\<down> V\<close>
    by (metis restriction_open_prod_imp_restriction_open_image_snd snd_image_times)
next
  assume \<open>(V = {} \<or> open\<^sub>\<down> U) \<and> (U = {} \<or> open\<^sub>\<down> V)\<close>
  then consider \<open>U = {}\<close> | \<open>V = {}\<close> | \<open>open\<^sub>\<down> U \<and> open\<^sub>\<down> V\<close> by fast
  thus \<open>open\<^sub>\<down> (U \<times> V)\<close>
  proof cases
    show \<open>U = {} \<Longrightarrow> open\<^sub>\<down> (U \<times> V)\<close> by simp
  next
    show \<open>V = {} \<Longrightarrow> open\<^sub>\<down> (U \<times> V)\<close> by simp
  next
    show \<open>open\<^sub>\<down> (U \<times> V)\<close> if * : \<open>open\<^sub>\<down> U \<and> open\<^sub>\<down> V\<close>
    proof (rule restriction_openI)
      fix \<Sigma> \<sigma> assume \<open>\<Sigma> \<in> U \<times> V\<close> and \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close>
      from \<open>\<Sigma> \<in> U \<times> V\<close> have \<open>fst \<Sigma> \<in> U\<close> \<open>snd \<Sigma> \<in> V\<close> by auto
      from \<open>\<sigma> \<midarrow>\<down>\<rightarrow> \<Sigma>\<close> have \<open>(\<lambda>n. fst (\<sigma> n)) \<midarrow>\<down>\<rightarrow> fst \<Sigma>\<close> \<open>(\<lambda>n. snd (\<sigma> n)) \<midarrow>\<down>\<rightarrow> snd \<Sigma>\<close>
        by (simp_all add: restriction_tendsto_prod_iff)
      from restriction_openD[OF "*"[THEN conjunct1] \<open>fst \<Sigma> \<in> U\<close> \<open>(\<lambda>n. fst (\<sigma> n)) \<midarrow>\<down>\<rightarrow> fst \<Sigma>\<close>]
      obtain n0 where \<open>\<forall>k\<ge>n0. fst (\<sigma> k) \<in> U\<close> ..
      moreover from restriction_openD[OF "*"[THEN conjunct2] \<open>snd \<Sigma> \<in> V\<close> \<open>(\<lambda>n. snd (\<sigma> n)) \<midarrow>\<down>\<rightarrow> snd \<Sigma>\<close>]
      obtain n1 where \<open>\<forall>k\<ge>n1. snd (\<sigma> k) \<in> V\<close> ..
      ultimately have \<open>\<forall>k\<ge>max n0 n1. \<sigma> k \<in> U \<times> V\<close> by (simp add: mem_Times_iff)
      thus \<open>\<exists>n2. \<forall>k\<ge>n2. \<sigma> k \<in> U \<times> V\<close> by blast
    qed
  qed
qed



lemma restriction_cont_at_prod_codomain_iff:
  \<open>cont\<^sub>\<down> f at \<Sigma> \<longleftrightarrow> cont\<^sub>\<down> (\<lambda>x. fst (f x)) at \<Sigma> \<and> cont\<^sub>\<down> (\<lambda>x. snd (f x)) at \<Sigma>\<close>
  by (auto simp add: restriction_cont_at_def restriction_tendsto_prod_iff)

lemma restriction_cont_on_prod_codomain_iff:
  \<open>cont\<^sub>\<down> f on A \<longleftrightarrow> cont\<^sub>\<down> (\<lambda>x. fst (f x)) on A \<and> cont\<^sub>\<down> (\<lambda>x. snd (f x)) on A\<close>
  by (metis restriction_cont_at_prod_codomain_iff restriction_cont_on_def)

lemma restriction_cont_prod_codomain_iff:
  \<open>cont\<^sub>\<down> f \<longleftrightarrow> cont\<^sub>\<down> (\<lambda>x. fst (f x)) \<and> cont\<^sub>\<down> (\<lambda>x. snd (f x))\<close>
  by (fact restriction_cont_on_prod_codomain_iff)


lemma restriction_cont_at_prod_codomain_imp [restriction_cont_simpset] :
  \<open>cont\<^sub>\<down> f at \<Sigma> \<Longrightarrow> cont\<^sub>\<down> (\<lambda>x. fst (f x)) at \<Sigma>\<close>
  \<open>cont\<^sub>\<down> f at \<Sigma> \<Longrightarrow> cont\<^sub>\<down> (\<lambda>x. snd (f x)) at \<Sigma>\<close>
  by (simp_all add: restriction_cont_at_prod_codomain_iff)

lemma restriction_cont_on_prod_codomain_imp [restriction_cont_simpset] :
  \<open>cont\<^sub>\<down> f on A \<Longrightarrow> cont\<^sub>\<down> (\<lambda>x. fst (f x)) on A\<close>
  \<open>cont\<^sub>\<down> f on A \<Longrightarrow> cont\<^sub>\<down> (\<lambda>x. snd (f x)) on A\<close>
  by (simp_all add: restriction_cont_on_prod_codomain_iff)

lemma restriction_cont_prod_codomain_imp [restriction_cont_simpset] :
  \<open>cont\<^sub>\<down> f \<Longrightarrow> cont\<^sub>\<down> (\<lambda>x. fst (f x))\<close>
  \<open>cont\<^sub>\<down> f \<Longrightarrow> cont\<^sub>\<down> (\<lambda>x. snd (f x))\<close>
  by (simp_all add: restriction_cont_prod_codomain_iff)




lemma restriction_cont_at_fun_imp [restriction_cont_simpset] :
  \<open>cont\<^sub>\<down> f at A \<Longrightarrow> cont\<^sub>\<down> (\<lambda>x. f x y) at A\<close>
  by (rule restriction_cont_atI)
    (metis restriction_cont_atD restriction_tendsto_fun_imp)

lemma restriction_cont_on_fun_imp [restriction_cont_simpset] :
  \<open>cont\<^sub>\<down> f on A \<Longrightarrow> cont\<^sub>\<down> (\<lambda>x. f x y) on A\<close>
  by (simp add: restriction_cont_at_fun_imp restriction_cont_on_def)

corollary restriction_cont_fun_imp [restriction_cont_simpset] :
  \<open>cont\<^sub>\<down> f \<Longrightarrow> cont\<^sub>\<down> (\<lambda>x. f x y)\<close>
  by (fact restriction_cont_on_fun_imp) 



lemma restriction_cont_at_prod_domain_imp [restriction_cont_simpset] :
  \<open>cont\<^sub>\<down> f at \<Sigma> \<Longrightarrow> cont\<^sub>\<down> (\<lambda>x. f (x, snd \<Sigma>)) at (fst \<Sigma>)\<close>
  \<open>cont\<^sub>\<down> f at \<Sigma> \<Longrightarrow> cont\<^sub>\<down> (\<lambda>y. f (fst \<Sigma>, y)) at (snd \<Sigma>)\<close>
  for f :: \<open>'a :: restriction_space \<times> 'b :: restriction_space \<Rightarrow> 'c :: restriction_space\<close>
  by (simp add: restriction_cball_prod_is subset_iff image_iff
      restriction_cont_at_iff_restriction_cball_characterization,
      meson center_mem_restriction_cball)+

lemma restriction_cont_on_prod_domain_imp [restriction_cont_simpset] :
  \<open>cont\<^sub>\<down> (\<lambda>x. f (x, y)) on {x. (x, y) \<in> A}\<close>
  \<open>cont\<^sub>\<down> (\<lambda>y. f (x, y)) on {y. (x, y) \<in> A}\<close> if \<open>cont\<^sub>\<down> f on A\<close>
for f :: \<open>'a :: restriction_space \<times> 'b :: restriction_space \<Rightarrow> 'c :: restriction_space\<close>
proof -
  show \<open>cont\<^sub>\<down> (\<lambda>x. f (x, y)) on {x. (x, y) \<in> A}\<close>
  proof (unfold restriction_cont_on_def, rule ballI)
    fix x assume \<open>x \<in> {x. (x, y) \<in> A}\<close>
    with \<open>cont\<^sub>\<down> f on A\<close> have \<open>cont\<^sub>\<down> f at (x, y)\<close>
      unfolding restriction_cont_on_def by simp
    thus \<open>cont\<^sub>\<down> (\<lambda>x. f (x, y)) at x\<close>
      by (fact restriction_cont_at_prod_domain_imp[of f \<open>(x, y)\<close>, simplified])
  qed
next
  show \<open>cont\<^sub>\<down> (\<lambda>y. f (x, y)) on {y. (x, y) \<in> A}\<close>
  proof (unfold restriction_cont_on_def, rule ballI)
    fix y assume \<open>y \<in> {y. (x, y) \<in> A}\<close>
    with \<open>cont\<^sub>\<down> f on A\<close> have \<open>cont\<^sub>\<down> f at (x, y)\<close>
      unfolding restriction_cont_on_def by simp
    thus \<open>cont\<^sub>\<down> (\<lambda>y. f (x, y)) at y\<close>
      by (fact restriction_cont_at_prod_domain_imp[of f \<open>(x, y)\<close>, simplified])
  qed
qed

lemma restriction_cont_prod_domain_imp [restriction_cont_simpset] :
  \<open>cont\<^sub>\<down> f \<Longrightarrow> cont\<^sub>\<down> (\<lambda>x. f (x, y))\<close>
  \<open>cont\<^sub>\<down> f \<Longrightarrow> cont\<^sub>\<down> (\<lambda>y. f (x, y))\<close>
for f :: \<open>'a :: restriction_space \<times> 'b :: restriction_space \<Rightarrow> 'c :: restriction_space\<close>
  by (metis UNIV_I restriction_cont_at_prod_domain_imp(1) restriction_cont_on_def split_pairs)
    (metis UNIV_I restriction_cont_at_prod_domain_imp(2) restriction_cont_on_def split_pairs)



(*<*)
end
  (*>*)