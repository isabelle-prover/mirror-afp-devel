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

section \<open>Non-Overlapping Multi-Intervals (\thy)\<close>

theory 
  Multi_Interval_Non_Overlapping
imports
  Multi_Interval_Preliminaries
begin

subsection\<open>Type Definition\<close>

typedef (overloaded) 'a minterval_non_ovl =
  "{is::'a::{minus_mono} interval list. valid_mInterval_non_ovl is}"
  morphisms bounds_of_minterval_non_ovl mInterval_non_ovl 
  unfolding valid_mInterval_non_ovl_def
  apply(intro exI[where x="[Interval (l,l) ]" for l])
  by(auto simp add: valid_mInterval_ovl_def sorted_wrt_lower_def non_adjacent_sorted_wrt_lower_def)

setup_lifting type_definition_minterval_non_ovl

lift_definition mlower_non_ovl::"('a::{minus_mono}) minterval_non_ovl \<Rightarrow> 'a" is \<open>lower o hd\<close> .
lift_definition mupper_non_ovl::"('a::{minus_mono}) minterval_non_ovl \<Rightarrow> 'a" is \<open>upper o last\<close> .
lift_definition mlist_non_ovl::"('a::{minus_mono}) minterval_non_ovl \<Rightarrow> 'a interval list" is \<open>id\<close> .

subsection\<open>Equality and Orderings\<close>

lemma minterval_non_ovl_eq_iff: "a = b \<longleftrightarrow> mlist_non_ovl a = mlist_non_ovl b"
  by transfer auto

lemma ainterval_eqI: "mlist_non_ovl a = mlist_non_ovl b \<Longrightarrow> a = b"
  by (auto simp: minterval_non_ovl_eq_iff)

lemma minterval_non_ovl_imp_upper_lower_eq : 
  "a = b \<longrightarrow> mlower_non_ovl a = mlower_non_ovl b \<and> mupper_non_ovl a = mupper_non_ovl b"
  by transfer auto


lemma mlower_non_ovl_le_mupper_non_ovl[simp]: "mlower_non_ovl i \<le> mupper_non_ovl i"
  by (transfer, metis comp_def hd_Nil_eq_last lower_le_upper lower_le_upper_aux 
                      non_adjacent_implies_non_overlapping valid_mInterval_non_ovl_def) 

lift_definition set_of_non_ovl :: "'a::{minus_mono} minterval_non_ovl \<Rightarrow> 'a set"
  is "\<lambda> is. \<Union>x\<in>set is. {lower x..upper x}" .

lemma set_non_ovl_of_subset: "set_of_non_ovl (x::'a::minus_mono minterval_non_ovl) \<subseteq> {mlower_non_ovl x .. mupper_non_ovl x}"
  apply(transfer, simp)
  using set_of_subeq_aux
        mInterval_ovl_lower_hd_min[symmetric, simplified o_def]
        mInterval_adj_upper_last_max[symmetric, simplified o_def]
        valid_non_ovl_imp_adj valid_non_ovl_imp_ovl
        list.set_map
  by (metis (mono_tags, lifting)) 


lemma not_in_non_ovl_eq:
  \<open>(\<not> e \<in> set_of_non_ovl xs) = (\<forall> x \<in> set (mlist_non_ovl xs). \<not> e \<in> set_of x)\<close>
proof(induction "(mlist_non_ovl xs)")
  case Nil
  then show ?case
    by (metis UN_iff empty_iff empty_set mlist_non_ovl.rep_eq set_of_non_ovl.rep_eq) 
next
  case (Cons a x)
  then show ?case 
    by (simp add: mlist_non_ovl.rep_eq set_of_eq set_of_non_ovl.rep_eq) 
qed

lemma in_non_ovl_eq:
  \<open>(e \<in> set_of_non_ovl xs) = (\<exists> x \<in> set (mlist_non_ovl xs). e \<in> set_of x)\<close>
proof(induction "(mlist_non_ovl xs)")
  case Nil
  then show ?case 
    by (metis UN_iff empty_iff empty_set mlist_non_ovl.rep_eq set_of_non_ovl.rep_eq) 
next
  case (Cons a x)
  then show ?case 
    by (simp add: mlist_non_ovl.rep_eq set_of_eq set_of_non_ovl.rep_eq)
qed

lemma set_of_non_ovl_non_zero_list_all: 
  \<open>0 \<notin> set_of_non_ovl xs \<Longrightarrow> \<forall> x \<in> set (mlist_non_ovl xs). \<not> 0 \<in>\<^sub>i x\<close>
proof(induction "mlist_non_ovl xs")
  case Nil
  then show ?case 
    by simp
next
  case (Cons a x)
  then show ?case 
    using in_non_ovl_eq by blast
qed

context notes [[typedef_overloaded]] begin


lift_definition(code_dt) mInterval_non_ovl'::"'a::minus_mono interval list \<Rightarrow> 'a minterval_non_ovl option"
  is "\<lambda> is. if  valid_mInterval_non_ovl is then Some is else None"
  by (auto simp add: valid_mInterval_non_ovl_def)

lemma mInterval_non_ovl'_split:
  "P (mInterval_non_ovl' is) \<longleftrightarrow>
    (\<forall>ivl.  valid_mInterval_non_ovl is \<longrightarrow> mlist_non_ovl ivl = is \<longrightarrow> P (Some ivl)) \<and> (\<not> valid_mInterval_non_ovl is \<longrightarrow> P None)"
 by transfer auto

lemma mInterval_non_ovl'_split_asm:
  "P (mInterval_non_ovl' is) \<longleftrightarrow>
    \<not>((\<exists>ivl. valid_mInterval_non_ovl is \<and> mlist_non_ovl ivl = is \<and> \<not>P (Some ivl)) \<or> (\<not> valid_mInterval_non_ovl is \<and> \<not>P None))"
  unfolding mInterval_non_ovl'_split
  by auto

lemmas mInterval_non_ovl'_splits = mInterval_non_ovl'_split mInterval_non_ovl'_split_asm

lemma mInterval'_eq_Some: "mInterval_non_ovl' is = Some i \<Longrightarrow> mlist_non_ovl i = is"
  by (simp split: mInterval_non_ovl'_splits)

end

instantiation "minterval_non_ovl" :: ("{minus_mono}") equal
begin

definition "equal_class.equal a b \<equiv> (mlist_non_ovl a = mlist_non_ovl b)"

instance proof qed (simp add: equal_minterval_non_ovl_def minterval_non_ovl_eq_iff)
end

instantiation minterval_non_ovl :: ("{minus_mono}") ord begin

definition less_eq_minterval_non_ovl :: "'a minterval_non_ovl \<Rightarrow> 'a minterval_non_ovl \<Rightarrow> bool"
  where "less_eq_minterval_non_ovl a b \<longleftrightarrow> mlower_non_ovl b \<le> mlower_non_ovl a \<and> mupper_non_ovl a \<le> mupper_non_ovl b"

definition less_minterval_non_ovl :: "'a minterval_non_ovl \<Rightarrow> 'a minterval_non_ovl \<Rightarrow> bool"
  where  "less_minterval_non_ovl x y = (x \<le> y \<and> \<not> y \<le> x)"

instance proof qed
end

instantiation minterval_non_ovl :: ("{minus_mono,lattice}") sup
begin

lift_definition sup_minterval_non_ovl :: "'a minterval_non_ovl \<Rightarrow> 'a minterval_non_ovl \<Rightarrow> 'a minterval_non_ovl"
  is "\<lambda> a b. [Interval (inf (lower (hd a)) (lower (hd b)), sup (upper (last a)) (upper (last b)))]"
  by(auto simp: valid_mInterval_ovl_def sorted_wrt_lower_def non_adjacent_sorted_wrt_lower_def 
                non_overlapping_sorted_def le_infI1 le_supI1 valid_mInterval_non_ovl_def mupper_non_ovl_def 
                mlower_non_ovl_def )

lemma mlower_non_ovl_sup[simp]: "mlower_non_ovl (sup A B) = inf (mlower_non_ovl A) (mlower_non_ovl B)"
  apply(transfer)
  by (metis comp_apply le_supE le_supI1 list.sel(1) lower_bounds lower_le_upper_aux sup_inf_absorb 
            valid_mInterval_adj_def valid_non_ovl_imp_adj) 

lemma mupper_non_ovl_sup[simp]: "mupper_non_ovl (sup A B) = sup (mupper_non_ovl A) (mupper_non_ovl B)"
  apply(transfer)
  by (metis (no_types, lifting) comp_def inf_sup_absorb last.simps le_infI1 le_inf_iff lower_le_upper_aux 
            upper_bounds valid_mInterval_adj_def valid_non_ovl_imp_adj)
instance 
  by(standard) 
end

instantiation minterval_non_ovl :: ("{lattice,minus_mono}") preorder
begin
instance
  apply(standard)
  subgoal 
    using less_minterval_non_ovl_def by auto
  subgoal 
    by (simp add: less_eq_minterval_non_ovl_def) 
  subgoal 
    by (meson less_eq_minterval_non_ovl_def order.trans)
  done 
end

lemma set_of_minterval_non_ovl_union: "set_of_non_ovl A \<union> set_of_non_ovl B \<subseteq> set_of_non_ovl (sup A B)" 
  for A::"'a::{lattice, minus_mono} minterval_non_ovl"
  apply(transfer, simp)
  using set_of_subeq_aux
        mInterval_ovl_lower_hd_min[symmetric, simplified o_def]
        mInterval_adj_upper_last_max[symmetric, simplified o_def]
        valid_non_ovl_imp_adj valid_non_ovl_imp_ovl
        list.set_map
  by (smt (verit) le_sup_iff lower_bounds lower_le_upper_aux lower_sup set_of_eq set_of_subset_iff 
                  sup.commute sup.commute sup.order_iff sup_ge1 sup_ge1 sup_inf_absorb upper_bounds 
                  valid_mInterval_adj_def) 

lemma minterval_non_ovl_union_commute: "sup A B = sup B A" for A::"'a::{minus_mono,lattice} minterval_non_ovl"
  apply (auto simp add: minterval_non_ovl_eq_iff inf.commute sup.commute)[1]
  by (simp add: mlist_non_ovl.rep_eq inf_commute sup_minterval_non_ovl.rep_eq sup_commute)

lemma minterval_non_ovl_union_mono1: "set_of_non_ovl a \<subseteq> set_of_non_ovl (sup a A)" 
  for A :: "'a::{minus_mono,lattice} minterval_non_ovl"
  apply(transfer, simp)
  using set_of_subeq_aux
        mInterval_ovl_lower_hd_min[symmetric, simplified o_def]
        mInterval_adj_upper_last_max[symmetric, simplified o_def]
        valid_non_ovl_imp_adj valid_non_ovl_imp_ovl
        list.set_map
  by (smt (verit, del_insts) inf.absorb_iff2 inf_le1 le_infI1 lower_bounds lower_le_upper_aux 
          set_of_eq set_of_subset_iff sup_ge1 upper_bounds valid_mInterval_adj_def)

lemma minterval_non_ovl_union_mono2: "set_of_non_ovl A \<subseteq> set_of_non_ovl (sup a A)" for A :: "'a::{lattice, minus_mono} minterval_non_ovl"
  apply(transfer, simp)
  using set_of_subeq_aux
        mInterval_ovl_lower_hd_min[symmetric, simplified o_def]
        mInterval_adj_upper_last_max[symmetric, simplified o_def]
        valid_non_ovl_imp_adj valid_non_ovl_imp_ovl
        list.set_map
  by (smt (verit, del_insts) inf.absorb_iff2 le_sup_iff lower_bounds lower_le_upper_aux nle_le 
          set_of_eq set_of_subset_iff sup_inf_absorb upper_bounds valid_mInterval_adj_def) 

lift_definition minterval_non_ovl_of :: "'a::{minus_mono} \<Rightarrow> 'a minterval_non_ovl" is "\<lambda>x. [Interval(x, x)]"
  unfolding valid_mInterval_non_ovl_def valid_mInterval_ovl_def non_adjacent_sorted_wrt_lower_def 
            cmp_non_adjacent_def sorted_wrt_lower_def 
  by simp

lemma mlower_non_ovl_minterval_non_ovl_of[simp]: "mlower_non_ovl (minterval_non_ovl_of a) = a"
  by transfer auto

lemma mupper_non_ovl_minterval_non_ovl_of[simp]: "mupper_non_ovl (minterval_non_ovl_of a) = a"
  by transfer auto

definition width_non_ovl :: "'a::{minus_mono} minterval_non_ovl \<Rightarrow> 'a"
  where "width_non_ovl i = mupper_non_ovl i - mlower_non_ovl i"

subsection\<open>Zero and One\<close>

instantiation "minterval_non_ovl" :: ("{minus_mono,zero}") zero
begin

lift_definition zero_minterval_non_ovl::"'a minterval_non_ovl" is "mk_mInterval_non_ovl [Interval (0, 0)]" 
  by (simp add: mk_mInterval_non_ovl_valid sorted_wrt_lower_def)

lemma mlower_non_ovl_zero[simp]: "mlower_non_ovl 0 = 0"
  by(transfer, simp add: mk_mInterval_non_ovl_def mk_mInterval_ovl_def interval_sort_lower_width_def)

lemma mupper_non_ovl_zero[simp]: "mupper_non_ovl 0 = 0"
  by(transfer, simp add: mk_mInterval_non_ovl_def mk_mInterval_ovl_def interval_sort_lower_width_def)

instance proof qed
end

instantiation "minterval_non_ovl" :: ("{minus_mono,one}") one
begin

lift_definition one_minterval_non_ovl::"'a minterval_non_ovl" is "mk_mInterval_non_ovl [Interval (1, 1)]" 
  by (metis list.simps(3) mk_mInterval_non_ovl_single mk_mInterval_non_ovl_valid sorted_wrt_lower_mk_mInterval_non_ovl)
  
lemma mlower_non_ovl_one[simp]: "mlower_non_ovl 1 = 1"
  by(transfer, simp add: mk_mInterval_non_ovl_def mk_mInterval_ovl_def interval_sort_lower_width_def)

lemma mupper_non_ovl_one[simp]: "mupper_non_ovl 1 = 1"
  by(transfer, simp add: mk_mInterval_non_ovl_def mk_mInterval_ovl_def interval_sort_lower_width_def)

instance proof qed  
end


subsection\<open>Addition\<close>

instantiation minterval_non_ovl :: ("{minus_mono,ordered_ab_semigroup_add,linordered_field}") plus
begin 

lemma valid_mk_interval_iList_plus:
  assumes "valid_mInterval_non_ovl a" and "valid_mInterval_non_ovl b"
  shows "valid_mInterval_non_ovl (mk_mInterval_non_ovl (iList_plus a b))"
  by (metis (no_types, lifting) assms(1) assms(2) bin_op_interval_list_empty iList_plus_lower_upper_eq 
            mk_mInterval_non_ovl_id mk_mInterval_non_ovl_non_empty mk_mInterval_non_ovl_valid 
            sorted_wrt_lower_mk_mInterval_non_ovl) 

lift_definition plus_minterval_non_ovl::"'a minterval_non_ovl \<Rightarrow> 'a minterval_non_ovl \<Rightarrow> 'a minterval_non_ovl"
   is "\<lambda> a b . mk_mInterval_non_ovl (iList_plus a b)"
   by (simp add: valid_mk_interval_iList_plus)

lemma interval_plus_com:
  \<open>a + b = b + a\<close> for a::"'a::{minus_mono,ordered_ab_semigroup_add,linordered_field} minterval_non_ovl"
  apply(transfer)
  using iList_plus_mInterval_non_ovl_commute plus_minterval_non_ovl_def 
  by auto 

instance proof qed

end

subsection \<open>Unary Minus\<close>

lemma a: "(x::'a::ordered_ab_group_add interval) \<noteq> y \<Longrightarrow> -x \<noteq> -y"
      apply(simp add:uminus_interval_def)
      by (smt (z3) Pair_inject bounds_of_interval_inverse case_prod_Pair_iden case_prod_unfold neg_equal_iff_equal uminus_interval.rep_eq) 

lemma b: "distinct (is::'a::ordered_ab_group_add interval list) \<Longrightarrow> distinct (map (\<lambda> i. -i) is)"
proof(induction "is")
  case Nil
  then show ?case by simp
next
  case (Cons a "is")
  then show ?case using a by force 
qed


instantiation "minterval_non_ovl" :: ("{minus_mono, ordered_ab_group_add}") uminus
begin

lift_definition uminus_minterval_non_ovl::"'a minterval_non_ovl \<Rightarrow> 'a minterval_non_ovl" 
             is "\<lambda> is . mk_mInterval_non_ovl (rev (map (\<lambda> i. -i) is))" 
  by (metis (no_types, lifting) distinct_remdups_id list.map_disc_iff mk_mInterval_non_ovl_def 
            mk_mInterval_ovl_sorted non_adj_sorted_mkInterval_non_ovl non_adjacent_implies_distinct 
            o_def rev_is_Nil_conv valid_mInterval_non_ovl_def valid_mInterval_ovl_def 
            valid_ovl_mkInterval_non_ovl) 

instance ..
end

subsection \<open>Subtraction\<close>

instantiation "minterval_non_ovl" :: ("{minus_mono, linordered_field, ordered_ab_group_add}") minus
begin

definition minus_minterval_non_ovl::"'a minterval_non_ovl \<Rightarrow> 'a minterval_non_ovl \<Rightarrow> 'a minterval_non_ovl"
  where "minus_minterval_non_ovl a b = a + - b"

instance ..
end

subsection \<open>Multiplication\<close>

instantiation "minterval_non_ovl" :: ("{minus_mono, linordered_field}") times
begin

lift_definition times_minterval_non_ovl::"'a minterval_non_ovl \<Rightarrow> 'a minterval_non_ovl \<Rightarrow> 'a minterval_non_ovl"
  is "\<lambda> a b . mk_mInterval_non_ovl (iList_times a b)"
  by (metis (no_types, lifting) bin_op_interval_list_empty distinct_remdups_id iList_times_def
            mk_mInterval_non_ovl_def mk_mInterval_ovl_sorted non_adj_sorted_mkInterval_non_ovl 
            non_adjacent_implies_distinct o_def valid_mInterval_non_ovl_def valid_mInterval_ovl_def 
            valid_ovl_mkInterval_non_ovl) 

instance ..
end

subsection \<open>Multiplicative Inverse and Division\<close>

locale minterval_non_ovl_division = inverse +
  constrains inverse :: \<open>'a::{linordered_field, zero, minus, minus_mono, real_normed_algebra,linear_continuum_topology} minterval_non_ovl \<Rightarrow> 'a minterval_non_ovl\<close>
         and divide  :: \<open>'a::{linordered_field, zero, minus, minus_mono, real_normed_algebra,linear_continuum_topology} minterval_non_ovl \<Rightarrow> 'a minterval_non_ovl \<Rightarrow> 'a minterval_non_ovl\<close>
       assumes inverse_left: \<open>\<not> 0 \<in> set_of_non_ovl x \<Longrightarrow> 1 \<le> (inverse x) * x\<close>
           and divide:      \<open>\<not> 0 \<in> set_of_non_ovl y \<Longrightarrow> x \<le> (divide x y) * y\<close> 
begin 
end 


locale minterval_non_ovl_division_inverse = inverse +
  constrains inverse :: \<open>'a::{linordered_field, zero, minus, minus_mono, real_normed_algebra,linear_continuum_topology} minterval_non_ovl \<Rightarrow> 'a minterval_non_ovl\<close>
         and divide  :: \<open>'a::{linordered_field, zero, minus, minus_mono, real_normed_algebra,linear_continuum_topology} minterval_non_ovl \<Rightarrow> 'a minterval_non_ovl \<Rightarrow> 'a minterval_non_ovl\<close>
       assumes inverse_non_zero_def: \<open>\<not> 0 \<in> set_of_non_ovl x \<Longrightarrow> (inverse x) 
                               = mInterval_non_ovl (mk_mInterval_non_ovl(un_op_interval_list (\<lambda> i. mk_interval (1 / (upper i), 1 / (lower i))) (mlist_non_ovl x)))\<close>
           and divide_non_zero_def:  \<open>\<not> 0 \<in> set_of_non_ovl y \<Longrightarrow> (divide x y) = inverse y * x\<close> 
begin 

end 

subsection \<open>Membership\<close>

abbreviation (in preorder) in_minterval_non_ovl ("(_/ \<in>\<^sub>n\<^sub>o _)" [51, 51] 50)
  where "in_minterval_non_ovl x X \<equiv> x \<in> set_of_non_ovl X"

lemma in_minterval_non_ovl_to_minterval_non_ovl[intro!]: "a \<in>\<^sub>n\<^sub>o minterval_non_ovl_of a"
  by (simp add: minterval_non_ovl_of.rep_eq set_of_non_ovl_def) 

instance minterval_non_ovl :: ("{one, preorder, minus_mono, linordered_semiring}") power
proof qed

lemma set_of_one_non_ovl[simp]: "set_of_non_ovl (1::'a::{one, minus_mono, order} minterval_non_ovl) = {1}"
  apply(transfer) 
  by(auto simp: mk_mInterval_non_ovl_def mk_mInterval_ovl_def interval_sort_lower_width_def set_of_non_ovl_def)

lifting_update minterval_non_ovl.lifting
lifting_forget minterval_non_ovl.lifting


end
