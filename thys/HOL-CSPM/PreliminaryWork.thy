(*<*)
\<comment>\<open> ********************************************************************
 * Project         : HOL-CSPM - Architectural operators for HOL-CSP
 *
 * Author          : Benoît Ballenghien, Safouan Taha, Burkhart Wolff
 *
 * This file       : Preliminary induction rules for set, multiset, nat
 *
 * Copyright (c) 2023 Université Paris-Saclay, France
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


chapter \<open>Some Preliminary Work\<close>

theory PreliminaryWork
  imports "HOL-Library.Multiset"
begin



section \<open>Induction Rules for \<^typ>\<open>'\<alpha> set\<close>\<close>


lemma finite_subset_induct_singleton
      [consumes 3, case_names singleton insertion]:
  \<open>\<lbrakk>a \<in> A; finite F; F \<subseteq> A; P {a}; 
    \<And>x F. finite F \<Longrightarrow> x \<in> A \<Longrightarrow> x \<notin> (insert a F) \<Longrightarrow> P (insert a F)
          \<Longrightarrow> P (insert x (insert a F))\<rbrakk> \<Longrightarrow> P (insert a F)\<close>
  apply (erule Finite_Set.finite_subset_induct, simp_all)
  by (metis insert_absorb2 insert_commute)


lemma finite_set_induct_nonempty
      [consumes 2, case_names singleton insertion]:
  assumes \<open>A \<noteq> {}\<close> and \<open>finite A\<close>
      and singleton: \<open>\<And>a. a \<in> A \<Longrightarrow> P {a}\<close>
      and insert: \<open>\<And>x F. \<lbrakk>F \<noteq> {}; finite F; x \<in> A; x \<notin> F;  P F\<rbrakk> 
                          \<Longrightarrow> P (insert x F)\<close>
    shows \<open>P A\<close>
proof-
  obtain a A' where \<open>a \<in> A\<close> \<open>finite A'\<close> \<open>A' \<subseteq> A\<close> \<open>A = insert a A'\<close>
    using \<open>A \<noteq> {}\<close> \<open>finite A\<close> by fastforce
  show \<open>P A\<close>
    apply (subst \<open>A = insert a A'\<close>, rule finite_subset_induct_singleton[of a A])
    by (simp_all add: \<open>a \<in> A\<close> \<open>finite A'\<close> \<open>A' \<subseteq> A\<close> singleton insert)
qed


lemma finite_subset_induct_singleton'
      [consumes 3, case_names singleton insertion]:
  \<open>\<lbrakk>a \<in> A; finite F; F \<subseteq> A; P {a};
    \<And>x F. \<lbrakk>finite F; x \<in> A; insert a F \<subseteq> A; x \<notin> insert a F; P (insert a F)\<rbrakk>
           \<Longrightarrow> P (insert x (insert a F))\<rbrakk>
   \<Longrightarrow> P (insert a F)\<close>
  apply (erule Finite_Set.finite_subset_induct', simp_all)
  by (metis insert_absorb2 insert_commute)


lemma induct_subset_empty_single[consumes 1]:
  \<open>\<lbrakk>finite A; P {}; \<forall>a \<in> A. P {a}; 
    \<And>F a. \<lbrakk>a \<in> A; finite F; F \<subseteq> A; F \<noteq> {}; P F\<rbrakk> \<Longrightarrow> P (insert a F)\<rbrakk> \<Longrightarrow> P A\<close>
  by (rule finite_subset_induct') auto



section \<open>Induction Rules for \<^typ>\<open>'\<alpha> multiset\<close>\<close>

text \<open>The following rule comes directly from \<^theory>\<open>HOL-Library.Multiset\<close> but is written
      with \<^emph>\<open>consumes 2\<close> instead of \<^emph>\<open>consumes 1\<close>. I rewrite here a correct version.\<close>
lemma msubset_induct [consumes 1, case_names empty add]:
  \<open>\<lbrakk>F \<subseteq># A; P {#}; \<And>a F. \<lbrakk>a \<in># A; P F\<rbrakk> \<Longrightarrow> P (add_mset a F)\<rbrakk> \<Longrightarrow> P F\<close>
  by (fact multi_subset_induct)


lemma msubset_induct_singleton [consumes 2, case_names m_singleton add]:
  \<open>\<lbrakk>a \<in># A; F \<subseteq># A; P {#a#};
    \<And>x F. \<lbrakk>x \<in># A; P (add_mset a F)\<rbrakk> \<Longrightarrow> P (add_mset x (add_mset a F))\<rbrakk>
    \<Longrightarrow> P (add_mset a F)\<close>
  by (erule msubset_induct, simp_all add: add_mset_commute)


lemma mset_induct_nonempty [consumes 1, case_names m_singleton add]:
  assumes \<open>A \<noteq> {#}\<close>
      and m_singleton: \<open>\<And>a. a \<in># A \<Longrightarrow> P {#a#}\<close>
      and add: \<open>\<And>x F. \<lbrakk>F \<noteq> {#}; x \<in># A; P F\<rbrakk> \<Longrightarrow> P (add_mset x F)\<close>
    shows \<open>P A\<close>
proof-
  obtain a A' where \<open>a \<in># A\<close> \<open>A' \<subseteq># A\<close> \<open>A = add_mset a A'\<close>
    by (metis  \<open>A \<noteq> {#}\<close> diff_subset_eq_self insert_DiffM multiset_nonemptyE)
  show \<open>P A\<close>
    apply (subst \<open>A = add_mset a A'\<close>, rule msubset_induct_singleton[of a A])
    by (simp_all add: \<open>a \<in># A\<close> \<open>A' \<subseteq># A\<close> m_singleton add)
qed 


lemma msubset_induct' [consumes 2, case_names empty add]:
  assumes \<open>F \<subseteq># A\<close>
    and empty: \<open>P {#}\<close>
    and insert: \<open>\<And>a F. \<lbrakk>a \<in># A - F; F \<subseteq># A; P F\<rbrakk> \<Longrightarrow> P (add_mset a F)\<close>
  shows \<open>P F\<close>
proof -
  from \<open>F \<subseteq># A\<close>
  show ?thesis
  proof (induct F)
    show \<open>P {#}\<close> by (simp add: assms(2))
  next
    case (add x F)
    then show \<open>P (add_mset x F)\<close>
      using Diff_eq_empty_iff_mset add_diff_cancel_left add_diff_cancel_left'
            add_mset_add_single local.insert mset_subset_eq_insertD
            subset_mset.le_iff_add subset_mset.less_imp_le by fastforce
  qed
qed


lemma msubset_induct_singleton' [consumes 2, case_names m_singleton add]:
  \<open>\<lbrakk>a \<in># A - F; F \<subseteq># A; P {#a#};
    \<And>x F. \<lbrakk>x \<in># A - F; F \<subseteq># A; P (add_mset a F)\<rbrakk>
           \<Longrightarrow> P (add_mset x (add_mset a F))\<rbrakk>
   \<Longrightarrow> P (add_mset a F)\<close>
  by (erule msubset_induct', simp_all add: add_mset_commute)


lemma msubset_induct_singleton'' [consumes 1, case_names m_singleton add]:
  \<open>\<lbrakk>add_mset a F \<subseteq># A; P {#a#};
    \<And>x F. \<lbrakk>add_mset x (add_mset a F) \<subseteq># A; P (add_mset a F)\<rbrakk>
           \<Longrightarrow> P (add_mset x (add_mset a F))\<rbrakk>
   \<Longrightarrow> P (add_mset a F)\<close>
  apply (induct F, simp) 
  by (metis add_mset_commute diff_subset_eq_self subset_mset.trans union_single_eq_diff)


lemma mset_induct_nonempty' [consumes 1, case_names m_singleton add]:
  assumes nonempty: \<open>A \<noteq> {#}\<close> and m_singleton: \<open>\<And>a. a \<in># A \<Longrightarrow> P {#a#}\<close>
      and hyp: \<open>\<And>a x F. \<lbrakk>a \<in># A; x \<in># A - add_mset a F; add_mset a F \<subseteq># A;
                          P (add_mset a F)\<rbrakk> \<Longrightarrow> P (add_mset x (add_mset a F))\<close>
    shows \<open>P A\<close>
proof-
  obtain a A' where \<open>A = add_mset a A'\<close> \<open>add_mset a A' \<subseteq># A\<close>
    using nonempty multiset_cases subset_mset_def by auto
  show \<open>P A\<close>
    apply (subst \<open>A = add_mset a A'\<close>)
    using \<open>add_mset a A' \<subseteq># A\<close>
  proof (induct A' rule: msubset_induct_singleton'')
    show \<open>P {#a#}\<close> using \<open>A = add_mset a A'\<close> m_singleton by force
  next
    case (add x F)
    show \<open>P (add_mset x (add_mset a F))\<close>
      apply (subst hyp) 
          apply (simp add: \<open>A = add_mset a A'\<close>)
         apply (metis \<open>add_mset x (add_mset a F) \<subseteq># A\<close> add_mset_add_single
                      mset_subset_eq_insertD subset_mset.add_diff_inverse 
                      subset_mset.add_le_cancel_left subset_mset_def)
        apply (meson \<open>add_mset x (add_mset a F) \<subseteq># A\<close> mset_subset_eq_insertD
                     subset_mset.dual_order.strict_implies_order)
      by (simp_all add: \<open>P (add_mset a F)\<close>)
  qed
qed


lemma induct_subset_mset_empty_single:
  \<open>\<lbrakk>P {#}; \<forall>a \<in># M. P {#a#}; 
    \<And>N a. \<lbrakk>a \<in># M; N \<subseteq># M; N \<noteq> {#}; P N\<rbrakk> \<Longrightarrow> P (add_mset a N)\<rbrakk> \<Longrightarrow> P M\<close>
  by (metis in_diffD mset_induct_nonempty')



section \<open>Strong Induction for \<^typ>\<open>nat\<close>\<close>

lemma strong_nat_induct[consumes 0, case_names 0 Suc]: 
  \<open>\<lbrakk>P 0; \<And>n. (\<And>m. m \<le> n \<Longrightarrow> P m) \<Longrightarrow> P (Suc n)\<rbrakk> \<Longrightarrow> P n\<close>
  by (induct n rule: nat_less_induct) (metis gr0_implies_Suc gr_zeroI less_Suc_eq_le)

lemma strong_nat_induct_non_zero[consumes 1, case_names 1 Suc]: 
  \<open>\<lbrakk>0 < n; P 1; \<And>n. 0 < n \<Longrightarrow> (\<And>m. 0 < m \<and> m \<le> n \<Longrightarrow> P m) \<Longrightarrow> P (Suc n)\<rbrakk>
   \<Longrightarrow> P n\<close>
  by (induct n rule: nat_less_induct) (metis One_nat_def gr0_implies_Suc gr_zeroI less_Suc_eq_le)



section \<open>Preliminaries for Cartesian Product Results\<close>

lemma prem_Multi_cartprod:
  \<open>(\<lambda>(x, y). x @ y ) ` (A  \<times> B ) = {s @ t  |s t. (s, t) \<in> A  \<times> B }\<close>
  \<open>(\<lambda>(x, y). x # y ) ` (A' \<times> B ) = {s # t  |s t. (s, t) \<in> A' \<times> B }\<close>
  \<open>(\<lambda>(x, y). [x, y]) ` (A' \<times> B') = {[s, t] |s t. (s, t) \<in> A' \<times> B'}\<close>
  by auto



end
