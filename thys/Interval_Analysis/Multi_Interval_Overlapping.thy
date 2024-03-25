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

section \<open>Overlapping Multi-Intervals (\thy)\<close>

theory 
  Multi_Interval_Overlapping
imports
  Multi_Interval_Preliminaries
begin

subsection \<open>Type Definition\<close>

typedef (overloaded) 'a minterval_ovl =
  "{is::'a::{minus_mono} interval list. valid_mInterval_ovl is}"
  morphisms bounds_of_minterval_ovl mInterval_ovl 
  unfolding valid_mInterval_ovl_def
  apply(intro exI[where x="[Interval (l,l) ]" for l])
  by(auto simp add: sorted_wrt_lower_def non_overlapping_sorted_def)

setup_lifting type_definition_minterval_ovl

lift_definition mlower_ovl::"('a::{minus_mono}) minterval_ovl \<Rightarrow> 'a" is \<open>lower o hd\<close> .
lift_definition mupper_ovl::"('a::{minus_mono}) minterval_ovl \<Rightarrow> 'a" is \<open>upper o last\<close> .
lift_definition mlist_ovl::"('a::{minus_mono}) minterval_ovl \<Rightarrow> 'a interval list" is \<open>id\<close> .

subsection\<open>Equality and Orderings\<close>

lemma minterval_ovl_eq_iff: "a = b \<longleftrightarrow> mlist_ovl a = mlist_ovl b"
  by transfer auto

lemma ainterval_eqI: "mlist_ovl a = mlist_ovl b \<Longrightarrow> a = b"
  by (auto simp: minterval_ovl_eq_iff)

lemma minterval_ovl_imp_upper_lower_eq : 
  "a = b \<longrightarrow> mlower_ovl a = mlower_ovl b \<and> mupper_ovl a = mupper_ovl b"
  by transfer auto

lemma valid_mInterval_ovl_lower_le_upper: 
  "valid_mInterval_ovl i \<Longrightarrow> (lower \<circ> hd) i \<le> (upper \<circ> last) i"
proof(induction i)
  case Nil
  then show ?case 
    unfolding valid_mInterval_ovl_def  o_def sorted_wrt_lower_def cmp_lower_width_def
    by simp 
next
  case (Cons a i)
  then show ?case 
    unfolding valid_mInterval_ovl_def  o_def sorted_wrt_lower_def cmp_lower_width_def
    by (metis (no_types, lifting) Cons.IH Cons.prems comp_apply distinct.simps(2)  
        in_bounds last.simps list.sel(1) lower_in_interval order_less_imp_le order_less_le_trans 
        sorted_wrt_lower_unroll valid_mInterval_ovl_def) 
qed

lemma mlower_non_ovl_le_mupper_non_ovl[simp]: "mlower_ovl i \<le> mupper_ovl i"
  by(transfer, metis valid_mInterval_ovl_lower_le_upper)

lift_definition set_of_ovl :: "'a::{minus_mono} minterval_ovl \<Rightarrow> 'a set"
  is "\<lambda> is. \<Union>x\<in>set is. {lower x..upper x}" .

lemma not_in_ovl_eq:
  \<open>(\<not> e \<in> set_of_ovl xs) = (\<forall> x \<in> set (mlist_ovl xs). \<not> e \<in> set_of x)\<close>
proof(induction "(mlist_ovl xs)")
  case Nil
  then show ?case 
    by (metis UN_iff empty_iff empty_set mlist_ovl.rep_eq set_of_ovl.rep_eq) 
next
  case (Cons a x)
  then show ?case 
    by (simp add: mlist_ovl.rep_eq set_of_eq set_of_ovl.rep_eq) 
qed

lemma in_ovl_eq:
  \<open>(e \<in> set_of_ovl xs) = (\<exists> x \<in> set (mlist_ovl xs). e \<in> set_of x)\<close>
proof(induction "(mlist_ovl xs)")
  case Nil
  then show ?case 
    by (metis UN_iff empty_iff empty_set mlist_ovl.rep_eq set_of_ovl.rep_eq) 
next
  case (Cons a x)
  then show ?case 
    by (simp add: mlist_ovl.rep_eq set_of_eq set_of_ovl.rep_eq)
qed

context notes [[typedef_overloaded]] begin

lift_definition(code_dt) mInterval_ovl'::"'a::minus_mono interval list \<Rightarrow> 'a minterval_ovl option"
  is "\<lambda> is. if  valid_mInterval_ovl is then Some is else None"
  by (auto simp add: valid_mInterval_ovl_def)

lemma mInterval_ovl'_split:
  "P (mInterval_ovl' is) \<longleftrightarrow>
    (\<forall>ivl.  valid_mInterval_ovl is \<longrightarrow> mlist_ovl ivl = is \<longrightarrow> P (Some ivl)) \<and> (\<not> valid_mInterval_ovl is \<longrightarrow> P None)"
 by transfer auto

lemma mInterval_ovl'_split_asm:
  "P (mInterval_ovl' is) \<longleftrightarrow>
    \<not>((\<exists>ivl. valid_mInterval_ovl is \<and> mlist_ovl ivl = is \<and> \<not>P (Some ivl)) \<or> (\<not> valid_mInterval_ovl is \<and> \<not>P None))"
  unfolding mInterval_ovl'_split
  by auto

lemmas mInterval_ovl'_splits = mInterval_ovl'_split mInterval_ovl'_split_asm

lemma mInterval'_eq_Some: "mInterval_ovl' is = Some i \<Longrightarrow> mlist_ovl i = is"
  by (simp split: mInterval_ovl'_splits)

end

lemma set_of_ovl_non_zero_list_all: 
  \<open>0 \<notin> set_of_ovl xs \<Longrightarrow> \<forall> x \<in> set (mlist_ovl xs). \<not> 0 \<in>\<^sub>i x\<close>
proof(induction "mlist_ovl xs")
  case Nil
  then show ?case 
    by simp
next
  case (Cons a x)
  then show ?case 
    using in_ovl_eq by blast
qed

instantiation "minterval_ovl" :: ("{minus_mono}") equal
begin

definition "equal_class.equal a b \<equiv> (mlist_ovl a = mlist_ovl b)"

instance proof qed (simp add: equal_minterval_ovl_def minterval_ovl_eq_iff)
end

instantiation minterval_ovl :: ("{minus_mono}") ord begin

definition less_eq_minterval_ovl :: "'a minterval_ovl \<Rightarrow> 'a minterval_ovl \<Rightarrow> bool"
  where "less_eq_minterval_ovl a b \<longleftrightarrow> mlower_ovl b \<le> mlower_ovl a \<and> mupper_ovl a \<le> mupper_ovl b"

definition less_minterval_ovl :: "'a minterval_ovl \<Rightarrow> 'a minterval_ovl \<Rightarrow> bool"
  where  "less_minterval_ovl x y = (x \<le> y \<and> \<not> y \<le> x)"

instance proof qed
end

instantiation minterval_ovl :: ("{minus_mono,lattice}") sup
begin

lift_definition sup_minterval_non_ovl :: "'a minterval_ovl \<Rightarrow> 'a minterval_ovl \<Rightarrow> 'a minterval_ovl"
  is "\<lambda> a b. [Interval (inf (lower (hd a)) (lower (hd b)), sup (upper (last a)) (upper (last b)))]"
  by(auto simp: valid_mInterval_ovl_def sorted_wrt_lower_def non_adjacent_sorted_wrt_lower_def 
                non_overlapping_sorted_def le_infI1 le_supI1 valid_mInterval_non_ovl_def mupper_ovl_def 
                mlower_ovl_def)
instance 
  by(standard) 
end

instantiation minterval_ovl :: ("{lattice,minus_mono}") preorder
begin
instance
  apply(standard)
  subgoal 
    using less_minterval_ovl_def by auto
  subgoal 
    by (simp add: less_eq_minterval_ovl_def) 
  subgoal 
    by (meson less_eq_minterval_ovl_def order.trans)
  done 
end

lift_definition minterval_ovl_of :: "'a::{minus_mono} \<Rightarrow> 'a minterval_ovl" is "\<lambda>x. [Interval(x, x)]"
  unfolding valid_mInterval_ovl_def valid_mInterval_ovl_def non_adjacent_sorted_wrt_lower_def 
            cmp_non_adjacent_def sorted_wrt_lower_def 
  by simp

lemma mlower_ovl_minterval_ovl_of[simp]: "mlower_ovl (minterval_ovl_of a) = a"
  by transfer auto

lemma mupper_ovl_minterval_ovl_of[simp]: "mupper_ovl (minterval_ovl_of a) = a"
  by transfer auto

definition width_ovl :: "'a::{minus_mono} minterval_ovl \<Rightarrow> 'a"
  where "width_ovl i = mupper_ovl i - mlower_ovl i"

subsection\<open>Zero and One\<close>

instantiation "minterval_ovl" :: ("{minus_mono,zero}") zero
begin

lift_definition zero_minterval_ovl::"'a minterval_ovl" is "mk_mInterval_ovl [Interval (0, 0)]" 
  by (simp add: mk_mInterval_ovl_valid)
  
lemma mlower_ovl_zero[simp]: "mlower_ovl 0 = 0"
  by(transfer, simp add: mk_mInterval_ovl_def interval_sort_lower_width_def)

lemma mupper_ovl_zero[simp]: "mupper_ovl 0 = 0"
  by(transfer, simp add: mk_mInterval_ovl_def interval_sort_lower_width_def)

instance proof qed
end

instantiation "minterval_ovl" :: ("{minus_mono,one}") one
begin

lift_definition one_minterval_ovl::"'a minterval_ovl" is "mk_mInterval_ovl [Interval (1, 1)]" 
  by (simp add: mk_mInterval_ovl_valid)

lemma mlower_ovl_one[simp]: "mlower_ovl 1 = 1"
  by(transfer, simp add: mk_mInterval_ovl_def interval_sort_lower_width_def)

lemma mupper_ovl_one[simp]: "mupper_ovl 1 = 1"
  by(transfer, simp add: mk_mInterval_ovl_def interval_sort_lower_width_def)

instance proof qed  
end


subsection\<open>Addition\<close>

instantiation minterval_ovl :: ("{minus_mono,ordered_ab_semigroup_add,linordered_field}") plus
begin 

lift_definition plus_minterval_ovl::"'a minterval_ovl \<Rightarrow> 'a minterval_ovl \<Rightarrow> 'a minterval_ovl"
  is "\<lambda> a b . mk_mInterval_ovl (iList_plus a b)"
  by (metis bin_op_interval_list_non_empty iList_plus_def mk_mInterval_ovl_valid valid_mInterval_ovl_def) 

lemma valid_mk_interval_iList_plus:
  assumes "valid_mInterval_ovl a" and "valid_mInterval_ovl b"
  shows "valid_mInterval_ovl (mk_mInterval_ovl (iList_plus a b))"
  by (metis (no_types, lifting) assms(1) assms(2) bin_op_interval_list_empty iList_plus_lower_upper_eq 
            mk_mInterval_ovl_id mk_mInterval_ovl_valid ) 

lift_definition plus_minterval_non_ovl::"'a minterval_ovl \<Rightarrow> 'a minterval_ovl \<Rightarrow> 'a minterval_ovl"
   is "\<lambda> a b . mk_mInterval_ovl (iList_plus a b)"
   by (simp add: valid_mk_interval_iList_plus)

lemma interval_plus_com:
  \<open>a + b = b + a\<close> for a::"'a::{minus_mono,ordered_ab_semigroup_add,linordered_field} minterval_ovl"
  apply(transfer)
  using plus_minterval_ovl_def 
  by (metis (no_types, opaque_lifting) foldr_isort_elements iList_plus_commute 
            interval_sort_lower_width_def mk_mInterval_ovl_def mk_mInterval_ovl_distinct 
            mk_mInterval_ovl_sorted o_def set_remdups sorted_wrt_lower_distinct_lists_eq) 

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


instantiation "minterval_ovl" :: ("{minus_mono, ordered_ab_group_add}") uminus
begin

lift_definition uminus_minterval_ovl::"'a minterval_ovl \<Rightarrow> 'a minterval_ovl" 
             is "\<lambda> is . mk_mInterval_ovl (rev (map (\<lambda> i. -i) is))" 
  by (metis list.map_disc_iff mk_mInterval_ovl_valid rev_is_Nil_conv valid_mInterval_ovl_def) 
instance ..
end

subsection \<open>Subtraction\<close>

instantiation "minterval_ovl" :: ("{minus_mono, linordered_field, ordered_ab_group_add}") minus
begin

definition minus_minterval_ovl::"'a minterval_ovl \<Rightarrow> 'a minterval_ovl \<Rightarrow> 'a minterval_ovl"
  where "minus_minterval_ovl a b = a + - b"

instance ..
end


subsection \<open>Multiplication\<close>

instantiation "minterval_ovl" :: ("{minus_mono,linordered_semiring}") times
begin

lift_definition times_minterval_ovl :: "'a minterval_ovl \<Rightarrow> 'a minterval_ovl \<Rightarrow> 'a minterval_ovl"
  is "\<lambda> a b . mk_mInterval_ovl (iList_times a b)"
  by (metis bin_op_interval_list_non_empty iList_times_def mk_mInterval_ovl_empty 
            mk_mInterval_ovl_valid)

instance ..
end

subsection \<open>Multiplicative Inverse and Division\<close>

locale minterval_ovl_division = inverse +
  constrains inverse :: \<open>'a::{linordered_field, zero, minus, minus_mono, real_normed_algebra,linear_continuum_topology} minterval_ovl \<Rightarrow> 'a minterval_ovl\<close>
         and divide  :: \<open>'a::{linordered_field, zero, minus, minus_mono, real_normed_algebra,linear_continuum_topology} minterval_ovl \<Rightarrow> 'a minterval_ovl \<Rightarrow> 'a minterval_ovl\<close>
       assumes inverse_left: \<open>\<not> 0 \<in> set_of_ovl x \<Longrightarrow> 1 \<le> (inverse x) * x\<close>
           and divide:      \<open>\<not> 0 \<in> set_of_ovl y \<Longrightarrow> x \<le> (divide x y) * y\<close> 
begin 
end 


locale minterval_ovl_division_inverse = inverse +
  constrains inverse :: \<open>'a::{linordered_field, zero, minus, minus_mono, real_normed_algebra,linear_continuum_topology} minterval_ovl \<Rightarrow> 'a minterval_ovl\<close>
         and divide  :: \<open>'a::{linordered_field, zero, minus, minus_mono, real_normed_algebra,linear_continuum_topology} minterval_ovl \<Rightarrow> 'a minterval_ovl \<Rightarrow> 'a minterval_ovl\<close>
       assumes inverse_non_zero_def: \<open>\<not> 0 \<in> set_of_ovl x \<Longrightarrow> (inverse x) 
                               = mInterval_ovl (mk_mInterval_ovl(un_op_interval_list (\<lambda> i. mk_interval (1 / (upper i), 1 / (lower i))) (mlist_ovl x)))\<close>
           and divide_non_zero_def:  \<open>\<not> 0 \<in> set_of_ovl y \<Longrightarrow> (divide x y) = inverse y * x\<close> 
begin 

end



subsection \<open>Membership\<close>

abbreviation (in preorder) in_minterval_ovl ("(_/ \<in>\<^sub>n\<^sub>o _)" [51, 51] 50)
  where "in_minterval_ovl x X \<equiv> x \<in> set_of_ovl X"

lemma in_minterval_ovl_to_minterval_ovl[intro!]: "a \<in>\<^sub>n\<^sub>o minterval_ovl_of a"
  by (metis (mono_tags, lifting) UN_iff list.set_intros(1) lower_in_interval lower_point_interval 
            minterval_ovl_of.rep_eq  set_of_eq set_of_ovl.rep_eq)

instance minterval_ovl :: ("{one, preorder, minus_mono, linordered_semiring}") power
proof qed


lemma set_of_one_ovl[simp]: "set_of_ovl (1::'a::{one, order, minus_mono} minterval_ovl) = {1}"
  apply (auto simp: set_of_ovl_def)[1]
  subgoal 
    by (simp add: interval_sort_lower_width_set_eq mk_mInterval_ovl_def one_minterval_ovl.rep_eq)
  subgoal
    by (simp add: interval_sort_lower_width_set_eq mk_mInterval_ovl_def one_minterval_ovl.rep_eq) 
  done


lifting_update minterval_ovl.lifting
lifting_forget minterval_ovl.lifting

end
