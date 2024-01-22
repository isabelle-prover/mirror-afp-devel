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

section \<open>Adjacent Multi-Intervals (\thy)\<close>

theory 
  Multi_Interval_Adjacent
imports
  Multi_Interval_Preliminaries
begin

subsection \<open>A Type For Non Overlapping Multi Intervals\<close>

typedef (overloaded) 'a minterval_adj =
  "{is::'a::{minus_mono,linorder} interval list. valid_mInterval_adj is}"
  morphisms bounds_of_minterval_adj mInterval_adj
  unfolding valid_mInterval_adj_def
  apply(intro exI[where x="[Interval (l,l) ]" for l])
  by(auto simp add: sorted_wrt_lower_def non_overlapping_sorted_def)

setup_lifting type_definition_minterval_adj

lift_definition mlower_adj::"('a::{minus_mono}) minterval_adj \<Rightarrow> 'a" is \<open>lower o hd\<close> .
lift_definition mupper_adj::"('a::{minus_mono}) minterval_adj \<Rightarrow> 'a" is \<open>upper o last\<close> .
lift_definition mlist_adj::"('a::{minus_mono}) minterval_adj \<Rightarrow> 'a interval list" is \<open>id\<close> .

subsection\<open>Equality and Orderings\<close>

lemma minterval_adj_eq_iff: "a = b \<longleftrightarrow> mlist_adj a = mlist_adj b"
  by transfer auto

lemma ainterval_eqI: "mlist_adj a = mlist_adj b \<Longrightarrow> a = b"
  by (auto simp: minterval_adj_eq_iff)

lemma minterval_adj_imp_upper_lower_eq : 
  "a = b \<longrightarrow> mlower_adj a = mlower_adj b \<and> mupper_adj a = mupper_adj b"
  by transfer auto


lemma mlower_adj_le_mupper_adj[simp]: "mlower_adj i \<le> mupper_adj i"
  by (transfer, metis comp_def   lower_le_upper_aux valid_mInterval_adj_def) 

lift_definition set_of_adj :: "'a::{minus_mono} minterval_adj \<Rightarrow> 'a set"
  is "\<lambda> is. \<Union>x\<in>set is. {lower x..upper x}" .

lemma set_adj_of_subset: "set_of_adj (x::'a::minus_mono minterval_adj) \<subseteq> {mlower_adj x .. mupper_adj x}"
  apply(transfer, simp)
  using set_of_subeq_aux
        mInterval_ovl_lower_hd_min[symmetric, simplified o_def]
        mInterval_adj_upper_last_max[symmetric, simplified o_def]
        valid_adj_imp_ovl
        list.set_map
  by (smt (verit, best)) 

lemma not_in_adj_eq:
  \<open>(\<not> e \<in> set_of_adj xs) = (\<forall> x \<in> set (mlist_adj xs). \<not> e \<in> set_of x)\<close>
proof(induction "(mlist_adj xs)")
  case Nil
  then show ?case
    by (metis UN_iff empty_iff empty_set mlist_adj.rep_eq set_of_adj.rep_eq) 
next
  case (Cons a x)
  then show ?case 
    by (simp add: mlist_adj.rep_eq set_of_eq set_of_adj.rep_eq) 
qed

lemma in_adj_eq:
  \<open>(e \<in> set_of_adj xs) = (\<exists> x \<in> set (mlist_adj xs). e \<in> set_of x)\<close>
proof(induction "(mlist_adj xs)")
  case Nil
  then show ?case 
    by (metis UN_iff empty_iff empty_set mlist_adj.rep_eq set_of_adj.rep_eq) 
next
  case (Cons a x)
  then show ?case 
    by (simp add: mlist_adj.rep_eq set_of_eq set_of_adj.rep_eq)
qed

lemma set_of_adj_non_zero_list_all: 
  \<open>0 \<notin> set_of_adj xs \<Longrightarrow> \<forall> x \<in> set (mlist_adj xs). \<not> 0 \<in>\<^sub>i x\<close>
proof(induction "mlist_adj xs")
  case Nil
  then show ?case 
    by simp
next
  case (Cons a x)
  then show ?case 
    using in_adj_eq by blast
qed

context notes [[typedef_overloaded]] begin


lift_definition(code_dt) mInterval_adj'::"'a::minus_mono interval list \<Rightarrow> 'a minterval_adj option"
  is "\<lambda> is. if  valid_mInterval_adj is then Some is else None"
  by (auto simp add: valid_mInterval_adj_def)

lemma mInterval_adj'_split:
  "P (mInterval_adj' is) \<longleftrightarrow>
    (\<forall>ivl.  valid_mInterval_adj is \<longrightarrow> mlist_adj ivl = is \<longrightarrow> P (Some ivl)) \<and> (\<not> valid_mInterval_adj is \<longrightarrow> P None)"
 by transfer auto

lemma mInterval_adj'_split_asm:
  "P (mInterval_adj' is) \<longleftrightarrow>
    \<not>((\<exists>ivl. valid_mInterval_adj is \<and> mlist_adj ivl = is \<and> \<not>P (Some ivl)) \<or> (\<not> valid_mInterval_adj is \<and> \<not>P None))"
  unfolding mInterval_adj'_split
  by auto

lemmas mInterval_adj'_splits = mInterval_adj'_split mInterval_adj'_split_asm

lemma mInterval'_eq_Some: "mInterval_adj' is = Some i \<Longrightarrow> mlist_adj i = is"
  by (simp split: mInterval_adj'_splits)

end

instantiation "minterval_adj" :: ("{minus_mono}") equal
begin

definition "equal_class.equal a b \<equiv> (mlist_adj a = mlist_adj b)"

instance proof qed (simp add: equal_minterval_adj_def minterval_adj_eq_iff)
end

instantiation minterval_adj :: ("{minus_mono}") ord begin

definition less_eq_minterval_adj :: "'a minterval_adj \<Rightarrow> 'a minterval_adj \<Rightarrow> bool"
  where "less_eq_minterval_adj a b \<longleftrightarrow> mlower_adj b \<le> mlower_adj a \<and> mupper_adj a \<le> mupper_adj b"

definition less_minterval_adj :: "'a minterval_adj \<Rightarrow> 'a minterval_adj \<Rightarrow> bool"
  where  "less_minterval_adj x y = (x \<le> y \<and> \<not> y \<le> x)"

instance proof qed
end

instantiation minterval_adj :: ("{minus_mono,lattice}") sup
begin

lift_definition sup_minterval_adj :: "'a minterval_adj \<Rightarrow> 'a minterval_adj \<Rightarrow> 'a minterval_adj"
  is "\<lambda> a b. [Interval (inf (lower (hd a)) (lower (hd b)), sup (upper (last a)) (upper (last b)))]"
  by(auto simp: valid_mInterval_ovl_def sorted_wrt_lower_def non_adjacent_sorted_wrt_lower_def 
                non_overlapping_sorted_def le_infI1 le_supI1 valid_mInterval_adj_def mupper_adj_def 
                mlower_adj_def )

lemma mlower_adj_sup[simp]: "mlower_adj (sup A B) = inf (mlower_adj A) (mlower_adj B)"
  apply(transfer)
  by (metis comp_apply le_supE le_supI1 list.sel(1) lower_bounds lower_le_upper_aux sup_inf_absorb 
            valid_mInterval_adj_def) 

lemma mupper_adj_sup[simp]: "mupper_adj (sup A B) = sup (mupper_adj A) (mupper_adj B)"
  apply(transfer)
  by (metis (no_types, lifting) comp_def inf_sup_absorb last.simps le_infI1 le_inf_iff lower_le_upper_aux 
            upper_bounds valid_mInterval_adj_def)
instance 
  by(standard) 
end

instantiation minterval_adj :: ("{lattice,minus_mono}") preorder
begin
instance
  apply(standard)
  subgoal 
    using less_minterval_adj_def by auto
  subgoal 
    by (simp add: less_eq_minterval_adj_def) 
  subgoal 
    by (meson less_eq_minterval_adj_def order.trans)
  done 
end

lemma set_of_minterval_adj_union: "set_of_adj A \<union> set_of_adj B \<subseteq> set_of_adj (sup A B)" 
  for A::"'a::{lattice, minus_mono} minterval_adj"
  apply(transfer, simp)
  using set_of_subeq_aux
        mInterval_ovl_lower_hd_min[symmetric, simplified o_def]
        mInterval_adj_upper_last_max[symmetric, simplified o_def]
        valid_adj_imp_ovl
        list.set_map
  by (smt (verit) le_sup_iff lower_bounds lower_le_upper_aux lower_sup set_of_eq set_of_subset_iff 
                  sup.commute sup.commute sup.order_iff sup_ge1 sup_ge1 sup_inf_absorb upper_bounds 
                  valid_mInterval_adj_def) 

lemma minterval_adj_union_commute: "sup A B = sup B A" for A::"'a::{minus_mono,lattice} minterval_adj"
  apply (auto simp add: minterval_adj_eq_iff inf.commute sup.commute)[1]
  by (simp add: mlist_adj.rep_eq inf_commute sup_minterval_adj.rep_eq sup_commute)

lemma minterval_adj_union_mono1: "set_of_adj a \<subseteq> set_of_adj (sup a A)" 
  for A :: "'a::{minus_mono,lattice} minterval_adj"
  apply(transfer, simp)
  using set_of_subeq_aux
        mInterval_ovl_lower_hd_min[symmetric, simplified o_def]
        mInterval_adj_upper_last_max[symmetric, simplified o_def]
        valid_adj_imp_ovl
        list.set_map
  by (smt (verit, del_insts) inf.absorb_iff2 inf_le1 le_infI1 lower_bounds lower_le_upper_aux 
          set_of_eq set_of_subset_iff sup_ge1 upper_bounds valid_mInterval_adj_def)

lemma minterval_adj_union_mono2: "set_of_adj A \<subseteq> set_of_adj (sup a A)" for A :: "'a::{lattice, minus_mono} minterval_adj"
  apply(transfer, simp)
  using set_of_subeq_aux
        mInterval_ovl_lower_hd_min[symmetric, simplified o_def]
        mInterval_adj_upper_last_max[symmetric, simplified o_def]
        valid_adj_imp_ovl
        list.set_map
  by (smt (verit, del_insts) inf.absorb_iff2 le_sup_iff lower_bounds lower_le_upper_aux nle_le 
          set_of_eq set_of_subset_iff sup_inf_absorb upper_bounds valid_mInterval_adj_def) 

lift_definition minterval_adj_of :: "'a::{minus_mono} \<Rightarrow> 'a minterval_adj" is "\<lambda>x. [Interval(x, x)]"
  unfolding valid_mInterval_adj_def valid_mInterval_ovl_def non_adjacent_sorted_wrt_lower_def 
            cmp_non_adjacent_def sorted_wrt_lower_def non_overlapping_sorted_def
  by simp

lemma mlower_adj_minterval_adj_of[simp]: "mlower_adj (minterval_adj_of a) = a"
  by transfer auto

lemma mupper_adj_minterval_adj_of[simp]: "mupper_adj (minterval_adj_of a) = a"
  by transfer auto

definition width_adj :: "'a::{minus_mono} minterval_adj \<Rightarrow> 'a"
  where "width_adj i = mupper_adj i - mlower_adj i"

subsection\<open>Zero and One\<close>

instantiation "minterval_adj" :: ("{minus_mono,zero}") zero
begin

lift_definition zero_minterval_adj::"'a minterval_adj" is "mk_mInterval_adj [Interval (0, 0)]" 
  by (simp add: mk_mInterval_adj_valid) 

lemma mlower_adj_zero[simp]: "mlower_adj 0 = 0"
  by(transfer, simp add: mk_mInterval_adj_def mk_mInterval_ovl_def interval_sort_lower_width_def)

lemma mupper_adj_zero[simp]: "mupper_adj 0 = 0"
  by(transfer, simp add: mk_mInterval_adj_def mk_mInterval_ovl_def interval_sort_lower_width_def)

instance proof qed
end

instantiation "minterval_adj" :: ("{minus_mono,one}") one
begin

lift_definition one_minterval_adj::"'a minterval_adj" is "mk_mInterval_adj [Interval (1, 1)]" 
  by (simp add: mk_mInterval_adj_valid)
  
lemma mlower_adj_one[simp]: "mlower_adj 1 = 1"
  by(transfer, simp add: mk_mInterval_adj_def mk_mInterval_ovl_def interval_sort_lower_width_def)

lemma mupper_adj_one[simp]: "mupper_adj 1 = 1"
  by(transfer, simp add: mk_mInterval_adj_def mk_mInterval_ovl_def interval_sort_lower_width_def)

instance proof qed  
end

subsection\<open>Addition\<close>

instantiation minterval_adj :: ("{minus_mono,ordered_ab_semigroup_add,linordered_field}") plus
begin 

lift_definition plus_minterval_adj::"'a minterval_adj \<Rightarrow> 'a minterval_adj \<Rightarrow> 'a minterval_adj"
  is "\<lambda> a b . mk_mInterval_adj (iList_plus a b)"
  by (metis bin_op_interval_list_empty iList_plus_def mk_mInterval_adj_valid valid_mInterval_adj_def) 

instance proof qed

lemma interval_plus_com:
  \<open>a + b = b + a\<close> for a::"'a minterval_adj"
  apply(transfer)
  using iList_plus_mInterval_adj_commute plus_minterval_adj_def 
  by(auto)

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


instantiation "minterval_adj" :: ("{minus_mono, ordered_ab_group_add}") uminus
begin

lift_definition uminus_minterval_non_ovl::"'a minterval_adj \<Rightarrow> 'a minterval_adj" 
             is "\<lambda> is . mk_mInterval_non_ovl (rev (map (\<lambda> i. -i) is))"
  by (metis (no_types, opaque_lifting) list.map_disc_iff mk_mInterval_non_ovl_id mk_mInterval_non_ovl_non_empty 
      mk_mInterval_non_ovl_valid rev_is_Nil_conv sorted_wrt_lower_mk_mInterval_non_ovl 
      valid_non_ovl_imp_adj)

instance ..
end

subsection \<open>Subtraction\<close>

instantiation "minterval_adj" :: ("{minus_mono, linordered_field, ordered_ab_group_add}") minus
begin

definition minus_minterval_non_ovl::"'a minterval_adj \<Rightarrow> 'a minterval_adj \<Rightarrow> 'a minterval_adj"
  where "minus_minterval_non_ovl a b = a + - b"

instance ..
end

subsection \<open>Multiplication\<close>

instantiation "minterval_adj" :: ("{minus_mono, linordered_field}") times
begin

lift_definition times_minterval_non_ovl::"'a minterval_adj \<Rightarrow> 'a minterval_adj \<Rightarrow> 'a minterval_adj"
  is "\<lambda> a b . mk_mInterval_non_ovl (iList_times a b)"
  by (metis bin_op_interval_list_empty iList_times_def mk_mInterval_non_ovl_id 
            mk_mInterval_non_ovl_non_empty mk_mInterval_non_ovl_valid sorted_wrt_lower_mk_mInterval_non_ovl 
            valid_non_ovl_imp_adj)

instance ..
end

subsection \<open>Multiplicative Inverse and Division\<close>

locale minterval_adj_division = inverse +
  constrains inverse :: \<open>'a::{linordered_field, zero, minus, minus_mono, real_normed_algebra,linear_continuum_topology} minterval_adj \<Rightarrow> 'a minterval_adj\<close>
         and divide  :: \<open>'a::{linordered_field, zero, minus, minus_mono, real_normed_algebra,linear_continuum_topology} minterval_adj \<Rightarrow> 'a minterval_adj \<Rightarrow> 'a minterval_adj\<close>
       assumes inverse_left: \<open>\<not> 0 \<in> set_of_adj x \<Longrightarrow> 1 \<le> (inverse x) * x\<close>
           and divide:      \<open>\<not> 0 \<in> set_of_adj y \<Longrightarrow> x \<le> (divide x y) * y\<close> 
begin 
end 


locale minterval_adj_division_inverse = inverse +
  constrains inverse :: \<open>'a::{linordered_field, zero, minus, minus_mono, real_normed_algebra,linear_continuum_topology} minterval_adj \<Rightarrow> 'a minterval_adj\<close>
         and divide  :: \<open>'a::{linordered_field, zero, minus, minus_mono, real_normed_algebra,linear_continuum_topology} minterval_adj \<Rightarrow> 'a minterval_adj \<Rightarrow> 'a minterval_adj\<close>
       assumes inverse_non_zero_def: \<open>\<not> 0 \<in> set_of_adj x \<Longrightarrow> (inverse x) 
                               = mInterval_adj (mk_mInterval_adj(un_op_interval_list (\<lambda> i. mk_interval (1 / (upper i), 1 / (lower i))) (mlist_adj x)))\<close>
           and divide_non_zero_def:  \<open>\<not> 0 \<in> set_of_adj y \<Longrightarrow> (divide x y) = inverse y * x\<close> 
begin 
end 

subsection \<open>Membership\<close>

abbreviation (in preorder) in_minterval_adj ("(_/ \<in>\<^sub>a\<^sub>d\<^sub>j _)" [51, 51] 50)
  where "in_minterval_adj x X \<equiv> x \<in> set_of_adj X"

lemma in_minterval_adj_to_minterval_adj[intro!]: "a \<in>\<^sub>a\<^sub>d\<^sub>j minterval_adj_of a"
  by (metis (mono_tags, lifting) UN_iff list.set_intros(1) lower_in_interval lower_point_interval 
            minterval_adj_of.rep_eq  set_of_eq set_of_adj.rep_eq)

instance minterval_adj ::  ("{one, preorder, minus_mono, linordered_semiring}") power
proof qed

lemma set_of_one_adj[simp]: "set_of_adj (1::'a::{one, minus_mono, order} minterval_adj) = {1}"
  apply(transfer)
  by(auto simp: mk_mInterval_adj_def mk_mInterval_ovl_def interval_sort_lower_width_def set_of_adj_def)


lifting_update minterval_adj.lifting
lifting_forget minterval_adj.lifting

end
