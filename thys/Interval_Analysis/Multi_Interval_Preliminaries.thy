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

chapter \<open>Multi-Intervals\<close>

section \<open>Preliminaries\<close>

theory 
  Multi_Interval_Preliminaries
imports
  "HOL-Library.Interval"
  "HOL-Analysis.Analysis"
  Inclusion_Isotonicity
begin

subsection\<open>A Class for Capturing Monotonicity of Minus\<close>

text\<open>
  We try to keep our formalisation of interval arithmetic as generic as possible. In particular,
  we want to support intervals of type @{typ "nat"}, @{typ "int"}, @{typ "real"}, and @{typ "ereal"}. 
  For all these types, minus (substraction) is monotonous. Sadly, Isabelle lacks a type class 
  capturing this. Luckily, it is very easy to define our own:
\<close>
class minus_mono = minus + linorder +
  assumes minus_mono: " A \<le> B \<Longrightarrow> D \<le> C \<Longrightarrow> A - C \<le> B - D"
begin end 

instance nat::minus_mono
  by(standard, simp)
instance int::minus_mono
  by(standard, simp)
instance real::minus_mono
  by(standard, simp)
instance integer::minus_mono
  by(standard, simp)
instance ereal::minus_mono
  by(standard, simp add:ereal_minus_mono)

subsection\<open>Infrastructure for Lifting Interval Operations to Lists of Intervals\<close>
definition un_op_interval_list::\<open>('a interval  \<Rightarrow> 'a interval) 
                                \<Rightarrow> 'a interval list \<Rightarrow> 'a interval list\<close> 
  where
  \<open>un_op_interval_list op xs = map op xs\<close>


definition bin_op_interval_list::\<open>('a interval \<Rightarrow> 'a interval \<Rightarrow> 'a interval) 
                              \<Rightarrow> 'a interval list \<Rightarrow> 'a interval list \<Rightarrow> 'a interval list\<close> 
  where
  \<open>bin_op_interval_list op xs ys  = concat (map (\<lambda> x . map (op x) xs) ys)\<close>

lemma bin_op_interval_list_non_empty: \<open>(xs \<noteq> [] \<and> ys \<noteq> []) = (bin_op_interval_list op xs ys \<noteq> [])\<close>
  unfolding bin_op_interval_list_def
  by(auto simp add: ex_in_conv)

lemma bin_op_interval_list_empty: \<open>(xs = [] \<or> ys = []) = (bin_op_interval_list op xs ys = [])\<close>
  unfolding bin_op_interval_list_def
  by(auto simp add: ex_in_conv)

lemma bin_op_interval_unroll: \<open>bin_op_interval_list op (xs) (y#ys) =  (map (op y) xs)@( bin_op_interval_list op xs ys)\<close>
  unfolding bin_op_interval_list_def by(simp)

lemma bin_op_interval_list_commute: 
  assumes op_commute: \<open>\<And> x y. op x y = op y x\<close> 
  shows \<open>set (bin_op_interval_list (op) xs ys) = set (bin_op_interval_list (op) ys xs)\<close>
  unfolding bin_op_interval_list_def 
proof(induction xs ys rule:list_induct2')
  case 1
  then show ?case by simp
next
  case (2 x xs)
  then show ?case by simp
next
  case (3 y ys)
  then show ?case by simp
next
  case (4 x xs y ys)
  then show ?case 
    by(auto simp add: op_commute, blast)
  qed

lemma bin_op_interval_list_assoc: 
  assumes op_assoc: \<open>\<And> x y z. op (op x y) z = op x (op y z)\<close> 
  shows \<open>set (bin_op_interval_list (op) ((bin_op_interval_list (op) xs ys)) zs)  = set (bin_op_interval_list (op) xs ((bin_op_interval_list (op) ys zs)))\<close>
  unfolding bin_op_interval_list_def 
proof(induction xs ys rule:list_induct2')
  case 1
  then show ?case by simp
next
  case (2 x xs)
  then show ?case by simp
next
  case (3 y ys)
  then show ?case by simp
next
  case (4 x xs y ys)
  then show ?case 
  proof(induction zs)
    case Nil
    then show ?case by simp
  next
    case (Cons a zs)
    then show ?case 
      apply(auto simp add: 4 list.set_map op_assoc)[1]
      subgoal
        by (meson imageI) 
      subgoal 
        by blast
      subgoal 
        by (meson UnionI imageI insertI1)
      subgoal 
        by (meson UN_I imageI insertCI)
      done 
    qed
  qed


subsubsection\<open>Lifting Unary Minus, Addition, and Multiplication\<close>

definition \<open>iList_uminus = un_op_interval_list (\<lambda> x. - x)\<close>
definition \<open>iList_plus   = bin_op_interval_list (+)\<close>
definition \<open>iList_times  = bin_op_interval_list (*)\<close>

lemma iList_plus_lower: 
  assumes  \<open>A \<noteq> []\<close> and \<open>B \<noteq> []\<close>
shows \<open>lower (hd (iList_plus A B)) = lower (hd A) + lower (hd B)\<close>
proof(insert assms, induction B)
  case Nil
  then show ?case by simp
next
  case (Cons a B)
  then show ?case 
    unfolding iList_plus_def
    apply(simp add: hd_map bin_op_interval_unroll[of "(+)" A a B])
    using add.commute by blast 
qed

lemma iList_plus_upper: 
  assumes \<open>A \<noteq> []\<close> and \<open>B \<noteq> []\<close>
shows \<open>upper (hd (iList_plus A B)) = upper (hd A) + upper (hd B)\<close>
proof(insert assms, induction B)
  case Nil
  then show ?case by simp
next
  case (Cons a B)
  then show ?case 
    unfolding iList_plus_def
    apply(simp add: hd_map bin_op_interval_unroll[of "(+)" A a B])
    using add.commute by blast 
qed

lemma iList_plus_unroll: 
  \<open>iList_plus ys (x # xs) = map ((+) x) ys @ iList_plus ys xs\<close>
  by (simp add: iList_plus_def bin_op_interval_unroll[of "(+)" ys x xs])

lemma "a \<noteq> [] \<Longrightarrow> (iList_plus [Interval (0, 0)] a) = (a::'a::{ordered_ab_group_add,zero} interval list)"
proof(induction a rule:list_nonempty_induct)
  case (single x)
  then show ?case 
    by (metis add.right_neutral append.right_neutral 
    bin_op_interval_list_non_empty iList_plus_def iList_plus_unroll list.map(2) zero_interval_def)
next
  case (cons x xs)
  then show ?case 
    by (metis add.right_neutral append_Cons append_Nil iList_plus_unroll list.map(1) list.map(2) zero_interval_def)
qed


lemma iList_plus_commute: 
  \<open>set (iList_plus xs ys) = set (iList_plus ys xs)\<close>
  using bin_op_interval_list_commute[of "(+)" xs ys] add.commute
  unfolding iList_plus_def 
  by auto

lemma iList_plus_assoc: 
  \<open>set (iList_plus xs (iList_plus ys zs)) = set (iList_plus (iList_plus xs ys) zs)\<close>
  using bin_op_interval_list_assoc[of "(+)" xs ys zs] add.assoc
  unfolding iList_plus_def 
  by auto

lemma remdups_append1:
  "remdups (remdups xs @ ys) = remdups (xs @ ys)"
by(induction xs) auto


lemma bin_op_interval_remdups_left:
  \<open>remdups (bin_op_interval_list op (remdups x) y) = remdups (bin_op_interval_list op x y)\<close>
proof(induction y)
  case Nil
  then show ?case 
    by (simp add: bin_op_interval_list_def) 
next
  case (Cons y' ys')
  then show ?case 
    by (metis (no_types, opaque_lifting) bin_op_interval_list_non_empty bin_op_interval_unroll 
              remdups_append1 remdups_append2 remdups_map_remdups) 
qed
  
lemma iList_plus_remdups_left: 
"remdups (iList_plus (remdups a) b) = remdups (iList_plus a b)"  
  for a::"'a::{minus_mono,ordered_ab_semigroup_add,linorder,linordered_field} interval list"
proof(induction b)
  case Nil
  then show ?case 
    by (metis bin_op_interval_list_empty iList_plus_def) 
next
  case (Cons a b)
  then show ?case 
    by (metis bin_op_interval_remdups_left iList_plus_def list.discI remdups.simps(1))
qed

lemma interval_add_eq: \<open>a + b = Interval(lower a + lower b, upper a + upper b)\<close>
  apply(subst interval_eq_iff[of "a+b" "Interval (lower a + lower b, upper a + upper b)"])
  using upper_plus[of a b] lower_plus[of a b] 
  by (simp add: add_mono) 

lemma iList_plus_lower_upper_eq:  
  \<open>iList_plus = bin_op_interval_list (\<lambda> a b. Interval(lower a + lower b, upper a + upper b))\<close>
  unfolding iList_plus_def using interval_add_eq
  by metis

subsubsection\<open>A Locale for Multi-Interval Division Where the Quotient does not Contain \<open>0\<close>\<close>

(* TODO *)

context interval_division
begin 

  definition \<open>iList_inverse = un_op_interval_list inverse\<close>
  definition \<open>iList_divide  = bin_op_interval_list divide\<close>

end 

subsection\<open>Utilities for (Sorted) Lists of Intervals\<close>

definition \<open>cmp_lower_width = (\<lambda> x y.  if lower x = lower y then width x \<le> width y else lower x < lower y)\<close>

definition \<open>sorted_wrt_lower = sorted_wrt cmp_lower_width\<close>

lemma interval_lower_width_eq: 
\<open>(lower x = lower y \<and> width x = width y) = (x = (y::'a::{minus_mono, linordered_field} interval))\<close>
  by (metis interval_eqI le_add_diff_inverse lower_le_upper width_def)

lemma sorted_wrt_lower_distinct_lists_eq:
  assumes \<open>set xs = set (ys::'a::{minus_mono, linordered_field} interval list)\<close>  
      and \<open>distinct xs\<close> and \<open>distinct ys\<close>
      and \<open>sorted_wrt_lower xs\<close> and \<open>sorted_wrt_lower ys\<close>
    shows\<open> xs = ys\<close>
proof(insert assms, unfold sorted_wrt_lower_def cmp_lower_width_def, induct xs ys rule:list_induct2')
  case 1
  then show ?case by simp
next
  case (2 x xs)
  then show ?case by simp
next
  case (3 y ys)
  then show ?case by simp
next
  case (4 x xs y ys)
  then show ?case 
    using interval_lower_width_eq 
    apply(auto)[1]
    subgoal by (smt (verit) insert_iff interval_lower_width_eq order.asym order_le_imp_less_or_eq)
    subgoal by (smt (verit, ccfv_SIG) antisym insertI1 insert_eq_iff interval_lower_width_eq not_less_iff_gr_or_eq) 
    done 
qed

definition \<open>sorted_wrt_upper = sorted_wrt (\<lambda> x y. upper x \<le> upper y)\<close>

definition \<open>cmp_non_overlapping = (\<lambda> x y.  upper x \<le> lower y)\<close>

lemma cmp_non_overlapping_lower: \<open>cmp_non_overlapping x y \<Longrightarrow> lower x \<le> lower y\<close>
  using  lower_le_upper unfolding cmp_non_overlapping_def
  by(metis dual_order.trans)

lemma cmp_non_overlapping_upper: \<open>cmp_non_overlapping x y \<Longrightarrow> upper x \<le> upper y\<close>
  using  lower_le_upper unfolding cmp_non_overlapping_def
  by(metis dual_order.trans)

definition \<open>non_overlapping_sorted = sorted_wrt cmp_non_overlapping\<close>
definition \<open>contiguous xs = (\<forall> i < length xs - 1 . upper (xs ! i) = lower (xs ! (i + 1)))\<close>

lemma non_overlapping_sorted_empty: \<open>non_overlapping_sorted []\<close>
  by (simp add: non_overlapping_sorted_def cmp_non_overlapping_def)


lemma non_overlapping_sorted_unroll:
  assumes "xs \<noteq> [] " shows "non_overlapping_sorted (x # xs) = (upper x \<le> lower (hd xs) \<and>  non_overlapping_sorted xs)" 
proof(cases xs)
  case Nil
  then show ?thesis using assms by(simp) 
next
  case (Cons y ys)
  then show ?thesis 
    apply(simp add:  non_overlapping_sorted_def cmp_non_overlapping_def  cmp_lower_width_def)
    using lower_le_upper
    by (metis dual_order.trans) 
qed

lemma contiguous_non_overlapping: \<open>contiguous (is::'a::{preorder} interval list) \<Longrightarrow> non_overlapping_sorted  is\<close>
proof(induction "is"rule:induct_list012)
  case 1
  then show ?case 
  unfolding contiguous_def non_overlapping_sorted_def cmp_non_overlapping_def 
  using lower_le_upper   
  by simp 
next
  case (2 x)
  then show ?case 
  unfolding contiguous_def non_overlapping_sorted_def cmp_non_overlapping_def 
  using lower_le_upper   
  by simp 
next
  case (3 x y zs)
  then show ?case
    apply(subst non_overlapping_sorted_unroll[of "(y#zs)" x])
    subgoal by(simp)
    subgoal apply(simp add: 3) using 3
      unfolding contiguous_def non_overlapping_sorted_def cmp_non_overlapping_def
      using lower_le_upper   
      by fastforce 
    done 
qed

definition \<open>cmp_non_adjacent = (\<lambda> x y.  upper x < lower y)\<close>

lemma cmp_non_adjacent_lower: \<open>cmp_non_adjacent x y \<Longrightarrow> lower x < lower y\<close>
  using  lower_le_upper unfolding cmp_non_adjacent_def
  by(metis dual_order.strict_trans2)

lemma cmp_non_adjacent_upper: \<open>cmp_non_adjacent x y \<Longrightarrow> upper x < upper y\<close>
  using  lower_le_upper unfolding cmp_non_adjacent_def
  by(metis dual_order.strict_trans1)

definition \<open>non_adjacent_sorted_wrt_lower = sorted_wrt cmp_non_adjacent\<close>

lemma non_adjacent_sorted_wrt_lower_unroll:
  assumes "xs \<noteq> [] " 
  shows "non_adjacent_sorted_wrt_lower (x # xs) = 
        ((upper x < lower (hd xs)) \<and> non_adjacent_sorted_wrt_lower xs)" 
proof(cases xs)
  case Nil
  then show ?thesis using assms by(simp) 
next
  case (Cons y ys)
  then show ?thesis 
    apply(simp add:non_adjacent_sorted_wrt_lower_def  cmp_non_adjacent_def) 
    by (meson cmp_non_adjacent_def cmp_non_adjacent_lower dual_order.strict_trans) 
qed


lemma non_adjacent_implies_non_overlapping:
  assumes \<open>non_adjacent_sorted_wrt_lower is\<close> shows \<open>non_overlapping_sorted is\<close>
proof(insert assms, induction "is")
  case Nil
  then show ?case 
    unfolding non_overlapping_sorted_def cmp_non_overlapping_def
              non_adjacent_sorted_wrt_lower_def cmp_non_adjacent_def
    by(simp)
next
  case (Cons a "is")
  then show ?case
    unfolding non_overlapping_sorted_def cmp_non_overlapping_def
              non_adjacent_sorted_wrt_lower_def cmp_non_adjacent_def
    using order.strict_implies_order by auto 
qed

lemma non_overlapping_implies_sorted_wrt_lower:
  assumes \<open>non_overlapping_sorted (is::'a::{minus_mono} interval list)\<close> 
  shows \<open>sorted_wrt_lower is\<close>
proof(insert assms, induction "is")
  case Nil
  then show ?case unfolding sorted_wrt_lower_def by simp
next
  case (Cons a "is")
  then show ?case 
    unfolding non_overlapping_sorted_def sorted_wrt_lower_def
              cmp_lower_width_def cmp_non_overlapping_def
    by (simp, metis (no_types, lifting) cmp_non_adjacent_def cmp_non_adjacent_lower minus_mono 
                                  dual_order.strict_iff_order lower_le_upper width_def) 
qed

lemma non_overlapping_implies_sorted_wrt_upper:
  assumes \<open>non_overlapping_sorted is\<close> 
  shows \<open>sorted_wrt_upper is\<close>
proof(insert assms, induction "is" rule:induct_list012)
  case 1
  then show ?case by(simp add: leD sorted_wrt_upper_def) 
next
  case (2 x)
  then show ?case by(simp add: leD sorted_wrt_upper_def)
next
  case (3 x y zs)
  then show ?case 
    by(auto simp add: cmp_non_overlapping_upper non_overlapping_sorted_def sorted_wrt_upper_def leD)[1]
qed

lemma non_adjacent_implies_sorted_wrt_lower:
  assumes \<open>non_adjacent_sorted_wrt_lower is\<close> 
  shows \<open>sorted_wrt_lower is\<close>
proof(insert assms, induction "is")
  case Nil
  then show ?case 
    unfolding sorted_wrt_lower_def 
    by simp
next
  case (Cons a "is")
  then show ?case 
    unfolding sorted_wrt_lower_def non_adjacent_sorted_wrt_lower_def
              cmp_non_adjacent_def cmp_lower_width_def width_def
    by(simp split:if_splits, metis dual_order.strict_trans2 lower_le_upper order_less_irrefl) 
qed

lemma non_adjacent_implies_distinct:
  assumes \<open>non_adjacent_sorted_wrt_lower is\<close> 
  shows \<open>distinct is\<close>
proof(insert assms, induction "is")
  case Nil
  then show ?case 
    unfolding sorted_wrt_lower_def 
    by simp
next
  case (Cons a "is")
  then show ?case 
    unfolding sorted_wrt_lower_def non_adjacent_sorted_wrt_lower_def
              cmp_non_adjacent_def cmp_lower_width_def width_def
    by(simp split:if_splits, metis dual_order.strict_trans2 lower_le_upper order_less_irrefl) 
qed

fun merge_overlapping_intervals_sorted_wrt_lower :: "'a::linorder interval list \<Rightarrow> 'a interval list"  where
"merge_overlapping_intervals_sorted_wrt_lower [] = []" |
"merge_overlapping_intervals_sorted_wrt_lower [x] = [x]" |
"merge_overlapping_intervals_sorted_wrt_lower (x#y#ys) = 
     (  if upper x \<le> lower y 
       then x#(merge_overlapping_intervals_sorted_wrt_lower (y#ys))
       else merge_overlapping_intervals_sorted_wrt_lower ((mk_interval(lower x, max (upper x) (upper y)))#ys)
      ) " 



lemma sorted_wrt_lower_unroll:
  assumes "xs \<noteq> [] " 
  shows "sorted_wrt_lower (x # xs) = ((if lower x \<noteq> lower (hd xs) 
                                       then lower x < lower (hd xs) 
                                       else width x \<le> width (hd xs) ) \<and> sorted_wrt_lower (xs))" 
proof(cases xs)
  case Nil
  then show ?thesis using assms by(simp) 
next
  case (Cons y ys)
  then show ?thesis 
    apply(simp add: sorted_wrt_lower_def cmp_lower_width_def) 
    by (smt (verit) dual_order.irrefl dual_order.strict_trans2 dual_order.trans order.strict_implies_order)
qed

lemma sorted_wrt_upper_unroll:
  assumes "xs \<noteq> [] " 
  shows "sorted_wrt_upper (x # xs) = ((upper x \<le> upper (hd xs))\<and> sorted_wrt_upper (xs))" 
proof(cases xs)
  case Nil
  then show ?thesis using assms by(simp) 
next
  case (Cons y ys)
  then show ?thesis 
    apply(simp add: sorted_wrt_upper_def cmp_lower_width_def)
    using dual_order.trans by blast 
qed

lemma sorted_wrt_lower_tail: " sorted_wrt_lower (x # xs) \<Longrightarrow>  sorted_wrt_lower (xs)"
  unfolding sorted_wrt_lower_def
  by simp

lemma sorted_wrt_lower_tail':"sorted_wrt_lower (x # y # ys) \<Longrightarrow> sorted_wrt_lower (x # ys)"
  unfolding sorted_wrt_lower_def by simp

lemma iList_plus_leq_B: 
  assumes "sorted_wrt_lower A" and "sorted_wrt_lower B" and "1 < length B"
  shows "hd (map lower (iList_plus A B)) \<le> hd (map lower (iList_plus A (tl B)))"
  proof(insert assms, induction B)
    case Nil
    then show ?case by simp
  next
    case (Cons b bs) note * = this
    then show ?case
    proof(cases bs)
      case Nil
      then show ?thesis
        using * by simp
    next
      case (Cons b' bs') note ** = this
      then have a: \<open>hd (map lower (iList_plus A (b#bs))) \<le> hd (map lower (iList_plus A bs))\<close>
      proof(induction "bs")
        case Nil
        then show ?case by simp
      next
        case (Cons b'' bs'')
        then show ?case 
          using * ** 
          by (smt (z3) add.commute add_right_mono dual_order.eq_iff hd_append iList_plus_lower 
              iList_plus_unroll list.map_disc_iff list.map_sel(1) list.sel(1) list.simps(3) 
              map_append order_less_imp_le sorted_wrt_lower_unroll)
      qed
      then show ?thesis
        using * ** a by simp
    qed  
  qed

lemma iList_plus_leq_A: 
  assumes "sorted_wrt_lower A" and "sorted_wrt_lower B" and "1 < length A"
  shows "hd (map lower (iList_plus A B)) \<le> hd (map lower (iList_plus (tl A) B))"
  proof(insert assms, induction A)
    case Nil
    then show ?case by simp
  next
    case (Cons a as) note * = this
    then show ?case
    proof(cases as)
      case Nil
      then show ?thesis
        using * by simp
    next
      case (Cons a' as') note ** = this
      then have a: \<open>hd (map lower (iList_plus (a#as) B)) \<le> hd (map lower (iList_plus as B))\<close>
      proof(induction "as")
        case Nil
        then show ?case by simp
      next
        case (Cons a'' as'')
        then show ?case 
          using * **
          by (smt (verit, best) add_right_mono bin_op_interval_list_empty dual_order.eq_iff 
                  iList_plus_def iList_plus_lower list.map_sel(1) list.sel(1) list.simps(3) 
                  order_less_imp_le sorted_wrt_lower_unroll)
      qed
      then show ?thesis
        using * ** a by simp
    qed  
  qed

value \<open>merge_overlapping_intervals_sorted_wrt_lower [mk_interval(1::int,2), mk_interval(2,3), mk_interval(5,7), mk_interval(6,10)]\<close>

lemma merge_overlapping_intervals_sorted_wrt_lower_non_nil:
  assumes \<open>xs \<noteq> []\<close>
  shows \<open>(merge_overlapping_intervals_sorted_wrt_lower xs) \<noteq> []\<close>
  using assms 
  by(induction xs rule:"merge_overlapping_intervals_sorted_wrt_lower.induct", simp_all)

lemma merge_overlapping_intervals_sorted_hd_lower:
  assumes \<open>xs \<noteq> []\<close>
  shows "lower (hd (merge_overlapping_intervals_sorted_wrt_lower (xs))) = lower (hd xs)"
proof(insert assms, induction xs rule:"merge_overlapping_intervals_sorted_wrt_lower.induct")
  case 1
  then show ?case by(simp)
next
  case (2 x)
  then show ?case by(simp)
next
  case (3 x y ys) 
  then show ?case 
    using "3.IH"(2) list.sel(1) lower_le_upper max.coboundedI2 mk_interval_lower 
    by (metis list.discI max.commute merge_overlapping_intervals_sorted_wrt_lower.simps(3))
qed

lemma merge_overlapping_intervals_sorted_hd_upper:
  assumes \<open>xs \<noteq> []\<close>
  shows "upper (hd xs) \<le> upper (hd (merge_overlapping_intervals_sorted_wrt_lower xs))"
proof(insert assms(1), induction "xs" rule:"merge_overlapping_intervals_sorted_wrt_lower.induct")
  case 1
  then show ?case by(simp)
next
  case (2 x)
  then show ?case by(simp)
next 
  case (3 x y ys) 
  then show ?case 
    proof(cases "upper x \<le> lower y")
    case True note non_overlapping = this
    then show ?thesis by simp 
  next
    case False note overlapping_or_included = this
    then show ?thesis proof(cases "upper x \<le> upper y")
      case True note overlapping = this
      then show ?thesis 
        proof(cases "lower x \<le> upper y")
          case True
          then show ?thesis 
            using "3.IH"(2)[simplified overlapping_or_included]
            apply(simp add: overlapping_or_included overlapping True) 
            using overlapping by simp 
        next
          case False
          then show ?thesis 
            using  overlapping_or_included overlapping False
            by (metis lower_le_upper max.coboundedI1 max_def)
        qed 
    next
      case False note included = this
      then show ?thesis 
        proof(cases "lower x \<le> upper y")
          case True
          then show ?thesis 
            using "3.IH"(2)[simplified overlapping_or_included]
            using included by simp 
        next
          case False
          then show ?thesis 
            using  overlapping_or_included included False
                   lower_le_upper[of x] lower_le_upper[of y]
            using "3.IH"(2) by fastforce 
        qed 
    qed
  qed
qed

lemma Interval_id[simp]: \<open>Interval (lower x, upper x) = x  \<close>  
  by (simp add: interval_eq_iff)

lemma mk_interval_id[simp]: \<open>(mk_interval (lower x, upper x)) = x\<close>
  using lower_le_upper[of x] unfolding mk_interval' by(auto)  

lemma merge_overlapping_intervals_sorted_hd_width:
  assumes \<open>xs \<noteq> []\<close>
  shows "width (hd xs) \<le> width (hd (merge_overlapping_intervals_sorted_wrt_lower (xs::'a::{minus_mono} interval list)))"
proof(insert assms, induction xs rule:"merge_overlapping_intervals_sorted_wrt_lower.induct")
  case 1
  then show ?case by(simp)
next
  case (2 x)
  then show ?case by(simp)
next
  case (3 x y ys)
  then show ?case 
   proof(cases "upper x \<le> lower y")
    case True note non_overlapping = this
    then show ?thesis by simp 
  next
    case False note overlapping_or_included = this
    then show ?thesis proof(cases "upper x \<le> upper y")
      case True note overlapping = this
      then show ?thesis 
        proof(cases "lower x \<le> upper y")
          case True
          then show ?thesis 
            using "3.IH"(2)[simplified overlapping_or_included]
            apply(simp add: width_def overlapping_or_included overlapping True) 
            using True diff_right_mono list.sel(1) list.simps(3) 
                      merge_overlapping_intervals_sorted_hd_lower merge_overlapping_intervals_sorted_hd_upper 
                      mk_interval_lower mk_interval_upper order.trans overlapping minus_mono
            by (smt (verit, best) dual_order.refl) 
        next
          case False
          then show ?thesis 
            using  overlapping_or_included overlapping False
            by (metis lower_le_upper max.coboundedI1 max_def)
        qed 
    next
      case False note included = this
      then show ?thesis 
        proof(cases "lower x \<le> upper y")
          case True
          then show ?thesis 
            using "3.IH"(2)[simplified overlapping_or_included] included 
            by (metis list.discI list.sel(1) max_def 
                       merge_overlapping_intervals_sorted_wrt_lower.simps(3) mk_interval_id 
                       overlapping_or_included) 
        next
          case False
          then show ?thesis 
            using  overlapping_or_included included False
                   lower_le_upper[of x] lower_le_upper[of y]
            using "3.IH"(2)[simplified overlapping_or_included]
            by (metis list.discI list.sel(1) max_def merge_overlapping_intervals_sorted_wrt_lower.simps(3) mk_interval_id) 
        qed 
    qed
  qed
qed



lemma merge_overlapping_intervals_sorted_wrt_lower_sorted_lower:
  assumes \<open>sorted_wrt_lower (xs::'a::{minus_mono} interval list)\<close>
  shows \<open>sorted_wrt_lower (merge_overlapping_intervals_sorted_wrt_lower xs)\<close> 
proof(insert assms, induction xs rule:"merge_overlapping_intervals_sorted_wrt_lower.induct")
  case 1
  then show ?case 
    unfolding sorted_wrt_lower_def 
    by(simp)
next
  case (2 x)
  then show ?case 
    unfolding sorted_wrt_lower_def 
    by(simp)
next
  case (3 x y ys)
  then show ?case 
   proof(cases "upper x \<le> lower y")
    case True note non_overlapping = this
    then show ?thesis
      by (smt (verit) "3.IH"(1) "3.prems" dual_order.trans list.discI merge_overlapping_intervals_sorted_hd_lower 
                      merge_overlapping_intervals_sorted_hd_width merge_overlapping_intervals_sorted_wrt_lower.simps(3) 
                      merge_overlapping_intervals_sorted_wrt_lower_non_nil sorted_wrt_lower_unroll) 
  next
    case False note overlapping_or_included = this
    then show ?thesis proof(cases "upper x \<le> upper y")
      case True note overlapping = this
      then show ?thesis 
        proof(cases "lower x \<le> upper y")
          case True
          then show ?thesis 
            using "3.IH"(2)[simplified overlapping_or_included]
            by (smt (verit, ccfv_threshold) "3.prems" list.sel(1) max.absorb2 
                    merge_overlapping_intervals_sorted_wrt_lower.simps(3) 
                    mk_interval_id mk_interval_lower overlapping overlapping_or_included sorted_wrt1 
                    sorted_wrt_lower_def sorted_wrt_lower_tail' sorted_wrt_lower_unroll)
        next
          case False
          then show ?thesis 
            using  overlapping_or_included overlapping False 
            using lower_le_upper order_trans by blast
        qed 
    next
      case False note included = this
      then show ?thesis 
        proof(cases "lower x \<le> upper y")
          case True
          then show ?thesis 
            using "3.IH"(2)[simplified overlapping_or_included] included 
                  "3.prems" overlapping_or_included sorted_wrt_lower_tail' 
            by (metis max_def merge_overlapping_intervals_sorted_wrt_lower.simps(3) mk_interval_id) 
        next
          case False
          then show ?thesis 
            using  overlapping_or_included included False
                   lower_le_upper[of x] lower_le_upper[of y]
            using "3.IH"(2)[simplified overlapping_or_included]
                  "3.prems" sorted_wrt_lower_tail' 
            by (metis max_def merge_overlapping_intervals_sorted_wrt_lower.simps(3) mk_interval_id) 
        qed 
    qed
  qed
qed

lemma merge_overlapping_intervals_sorted_sorted_non_non_overlapping:
  assumes \<open>sorted_wrt_lower (xs::'a::{minus_mono} interval list)\<close>
  shows \<open>non_overlapping_sorted (merge_overlapping_intervals_sorted_wrt_lower xs)\<close>
  proof(insert assms, induction xs rule:"merge_overlapping_intervals_sorted_wrt_lower.induct")
    case 1
    then show ?case unfolding non_overlapping_sorted_def
      by (metis merge_overlapping_intervals_sorted_wrt_lower.simps(1) sorted_wrt.simps(1))
  next
    case (2 x)
    then show ?case unfolding non_overlapping_sorted_def 
      by (metis merge_overlapping_intervals_sorted_wrt_lower.simps(2) sorted_wrt1)
  next
    case (3 x y ys)
    then show ?case 
   proof(cases "upper x \<le> lower y")
    case True note non_overlapping = this
    then show ?thesis 
      using "3"dual_order.trans list.discI merge_overlapping_intervals_sorted_hd_lower 
            merge_overlapping_intervals_sorted_hd_width merge_overlapping_intervals_sorted_wrt_lower.simps 
            merge_overlapping_intervals_sorted_wrt_lower_non_nil non_overlapping_sorted_unroll
      by (smt (verit, ccfv_threshold) list.sel(1) sorted_wrt_lower_tail) 
   next
    case False note overlapping_or_included = this
    then show ?thesis proof(cases "upper x \<le> upper y")
      case True note overlapping = this
      then show ?thesis 
        proof(cases "lower x \<le> upper y")
          case True
          then show ?thesis 
            using "3.IH"(2)[simplified overlapping_or_included]
            by (smt (verit) "3.prems" list.discI list.sel(1) 
                    max.absorb2 merge_overlapping_intervals_sorted_wrt_lower.simps(3) 
                    mk_interval_id mk_interval_lower overlapping overlapping_or_included sorted_wrt_lower_tail' 
                    sorted_wrt_lower_unroll) 
        next
          case False
          then show ?thesis 
            using  overlapping_or_included overlapping False 
            using lower_le_upper order_trans by blast
        qed 
    next
      case False note included = this
      then show ?thesis 
        proof(cases "lower x \<le> upper y")
          case True
          then show ?thesis 
            using "3.IH"(2)[simplified overlapping_or_included] included 
            using "3.prems" overlapping_or_included sorted_wrt_lower_tail'
            by (metis max.orderE merge_overlapping_intervals_sorted_wrt_lower.simps(3) mk_interval_id nle_le)
        next
          case False
          then show ?thesis 
            using  overlapping_or_included included False
                   lower_le_upper[of x] lower_le_upper[of y]
            using "3.IH"(2)[simplified overlapping_or_included]
            using "3.prems" sorted_wrt_lower_tail'
            by (metis max.orderE merge_overlapping_intervals_sorted_wrt_lower.simps(3) mk_interval_id nle_le)
        qed 
    qed
  qed
qed
      


fun merge_adjacent_intervals_sorted_wrt_lower :: "'a::linorder interval list \<Rightarrow> 'a interval list"  where
"merge_adjacent_intervals_sorted_wrt_lower [] = []" |
"merge_adjacent_intervals_sorted_wrt_lower [x] = [x]" |
"merge_adjacent_intervals_sorted_wrt_lower (x#y#ys) = 
     (  if upper x < lower y 
       then x#(merge_adjacent_intervals_sorted_wrt_lower (y#ys))
       else merge_adjacent_intervals_sorted_wrt_lower ((mk_interval(lower x, max (upper y) (upper x)))#ys)
      ) " 

value \<open>merge_adjacent_intervals_sorted_wrt_lower [mk_interval(1::int,2), mk_interval(2,3), mk_interval(5,7), mk_interval(6,10)]\<close>

lemma merge_adjacent_intervals_sorted_wrt_lower_non_nil:
  assumes \<open>xs \<noteq> []\<close>
  shows \<open>(merge_adjacent_intervals_sorted_wrt_lower xs) \<noteq> []\<close>
  using assms by(induction xs rule:"merge_adjacent_intervals_sorted_wrt_lower.induct", simp_all)

lemma merge_adjacent_intervals_sorted_wrt_lower_non_nil':
  shows \<open>(merge_adjacent_intervals_sorted_wrt_lower (x#xs)) \<noteq> []\<close>
  by(simp add: merge_adjacent_intervals_sorted_wrt_lower_non_nil)

lemma merge_adjacent_intervals_sorted_wrt_lower_sorted_lower_lower_hd:
  assumes \<open>sorted_wrt_lower xs\<close> 
  shows \<open>lower (hd (merge_adjacent_intervals_sorted_wrt_lower xs)) = lower (hd xs)\<close>
  using assms
proof(induction xs rule:"merge_adjacent_intervals_sorted_wrt_lower.induct")
  case 1
  then show ?case 
    by (metis merge_adjacent_intervals_sorted_wrt_lower.simps(1)) 
next
  case (2 x)
  then show ?case by simp
next
  case (3 x y ys) 
  then show ?case 
  proof(cases "(sorted_wrt_lower (mk_interval (lower x, max (upper y) (upper x)) # ys))")
    case True
    then show ?thesis
      by (simp, metis "3.IH"(2) list.sel(1) lower_le_upper max.coboundedI2 mk_interval_lower) 
  next
    case False
    then show ?thesis 
      apply(simp, subst 3 (2))
        apply (smt (verit) 3 dual_order.strict_trans leD list.discI list.sel(1) lower_le_upper max.coboundedI2 
                           mk_interval_lower sorted_wrt1 sorted_wrt_lower_def sorted_wrt_lower_unroll) 
       apply (smt (verit) "3.prems" dual_order.trans interval_eqI list.discI list.sel(1) 
                          lower_le_upper max.strict_order_iff max_def mk_interval_lower mk_interval_upper 
                          sorted_wrt1 sorted_wrt_lower_def sorted_wrt_lower_unroll) 
      by (simp add: 3 max.coboundedI2 sorted_wrt_lower_def)
    qed
  qed

lemma merge_adjacent_intervals_sorted_wrt_lower_sorted_lower_lower_subset:
  \<open>set (map lower (merge_adjacent_intervals_sorted_wrt_lower xs)) \<subseteq> set (map lower xs)\<close>
  apply(induction xs rule:"merge_adjacent_intervals_sorted_wrt_lower.induct")
by(auto simp add: max.coboundedI2 mk_interval' sorted_wrt_lower_def image_def)

lemma merge_adjacent_intervals_sorted_wrt_lower_set_eq:
  assumes \<open>set (xs::real interval list) = set ys\<close> 
      and \<open>distinct xs\<close> and \<open>distinct ys\<close>
      and \<open>sorted_wrt_lower xs\<close> and \<open>sorted_wrt_lower ys\<close>
  shows \<open>merge_adjacent_intervals_sorted_wrt_lower xs = merge_adjacent_intervals_sorted_wrt_lower ys\<close>
  using sorted_wrt_lower_distinct_lists_eq[of xs ys, simplified assms, simplified]
  by(auto)


lemma merge_adjacent_intervals_sorted_wrt_lower_lower_upper:
  assumes "sorted_wrt_lower xs"
  shows "x \<in> set (merge_adjacent_intervals_sorted_wrt_lower xs) \<Longrightarrow> \<exists> l \<in> set xs. \<exists> u \<in> set xs. lower l = lower x \<and> upper u = upper x"
proof(insert assms, induction xs rule:merge_adjacent_intervals_sorted_wrt_lower.induct)
  case 1
  then show ?case 
    by simp 
next
  case (2 x)
  then show ?case
    by simp
next
  case (3 x y ys)
  then show ?case 
    proof(cases ys)
      case Nil
      then show ?thesis
        using 3
        by (simp, smt (z3) empty_iff empty_set list.sel(1) list.sel(3) list.set_cases 
                max_def merge_adjacent_intervals_sorted_wrt_lower.simps(2) 
                merge_adjacent_intervals_sorted_wrt_lower.simps(3) 
                merge_adjacent_intervals_sorted_wrt_lower_sorted_lower_lower_hd mk_interval_lower 
                mk_interval_upper) 
    next
      case (Cons a list)
      then show ?thesis
        apply(auto simp add: mk_interval' max_def)[1]
        subgoal 
          using 3
          by (smt (z3) insert_iff interval_eq_iff list.sel(1) list.simps(15) list.simps(3) lower_le_upper 
                  max.coboundedI1 max_def_raw merge_adjacent_intervals_sorted_wrt_lower.simps(3) 
                  mk_interval_lower mk_interval_upper sorted_wrt_lower_tail' sorted_wrt_lower_unroll)
        subgoal 
          using 3 
          by (smt (verit) dual_order.trans list.discI list.inject list.sel(1) lower_le_upper max_def 
                  merge_adjacent_intervals_sorted_wrt_lower.elims mk_interval_id mk_interval_lower 
                  mk_interval_upper order.asym set_ConsD sorted_wrt_lower_tail' sorted_wrt_lower_unroll)
        done 
      qed
    qed



primrec interval_insert_sort_lower_width :: "('a::{linorder,minus}) interval \<Rightarrow> 'a interval list \<Rightarrow> 'a interval list" where
  "interval_insert_sort_lower_width x [] = [x]" |
  "interval_insert_sort_lower_width x (y#ys) =
  (if cmp_lower_width x y then (x#y#ys) else y#(interval_insert_sort_lower_width x ys))"

lemma interval_insert_sort_lower_width_length:
\<open>length (interval_insert_sort_lower_width x xs) = 1 + length xs \<close>
  by(induction xs, auto)

lemma interval_insert_sort_lower_width_nonempty:
\<open>interval_insert_sort_lower_width x xs \<noteq> []\<close>
   by(induction xs, auto)

  

lemma interval_insert_sort_wrt_lower:
\<open>sorted_wrt_lower xs \<Longrightarrow> sorted_wrt_lower (interval_insert_sort_lower_width x xs)\<close>
proof(induction xs)
  case Nil
  then show ?case by(simp add: sorted_wrt_lower_def cmp_lower_width_def)
next
  case (Cons a xs)
  then show ?case 
    apply(auto)[1]
    subgoal 
      by (metis cmp_lower_width_def list.discI list.sel(1) sorted_wrt_lower_unroll)
    subgoal 
      apply(subst sorted_wrt_lower_unroll)
      apply(simp add: interval_insert_sort_lower_width_nonempty)
      apply(simp add: cmp_lower_width_def sorted_wrt_lower_def split:if_split)
      using interval_insert_sort_lower_width.simps(1)[of a] 
            interval_insert_sort_lower_width.simps(2)
                      list.sel(1) list.set_cases list.set_sel(1)
      by (smt (verit) interval_insert_sort_lower_width.simps(1) less_le_not_le nle_le) 
      done
qed

lemma interval_isort_elements: "set (interval_insert_sort_lower_width x xs) = {x} \<union> set xs "
proof(induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by(auto)
qed

lemma foldr_isort_elements: "set (foldr interval_insert_sort_lower_width xs []) = set xs"
proof(induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case 
    using interval_isort_elements by(auto)
qed

definition interval_sort_lower_width :: "('a::{linorder,minus}) interval list \<Rightarrow> 'a interval list" where
  "interval_sort_lower_width xs = foldr interval_insert_sort_lower_width xs []"

lemma interval_sort_lower_width_length: \<open>length (interval_sort_lower_width xs) = (length xs)\<close>
proof(induction xs)
  case Nil
  then show ?case unfolding interval_sort_lower_width_def by simp 
next
  case (Cons a xs)
  then show ?case 
    unfolding interval_sort_lower_width_def 
    by (simp add: interval_insert_sort_lower_width_length) 
qed

lemma interval_sort_lower_width_sorted: \<open>sorted_wrt_lower  (interval_sort_lower_width xs)\<close>
proof(induction xs)
  case Nil
  then show ?case 
    unfolding interval_sort_lower_width_def sorted_wrt_lower_def 
    by simp
next
  case (Cons a xs)
  then show ?case 
  unfolding interval_sort_lower_width_def 
  using interval_insert_sort_wrt_lower
  by auto 
qed


lemma interval_sort_lower_width_set_eq:  
  \<open>set (interval_sort_lower_width x) = set x\<close>
  by (simp add: foldr_isort_elements interval_sort_lower_width_def)

lemma interval_sort_lower_width_remdups:
  \<open>remdups (interval_sort_lower_width (remdups xs)) =  interval_sort_lower_width (remdups xs)\<close>
  unfolding interval_sort_lower_width_def
proof(induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case 
    by (metis (no_types, opaque_lifting) foldr_isort_elements interval_sort_lower_width_def 
              interval_sort_lower_width_length length_remdups_card_conv length_remdups_eq set_remdups) 
qed

lemma interval_sort_lower_width_distinct:
  assumes \<open>distinct xs\<close> shows 
  \<open>distinct (interval_sort_lower_width (remdups xs))\<close>
  using interval_sort_lower_width_remdups by auto 

lemma foldr_interval_insert_sort_lower_width_distinct:
  assumes \<open>distinct zs\<close> 
  shows \<open>distinct (foldr interval_insert_sort_lower_width zs [])\<close>
proof(insert assms, induction zs)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a zs)
  then show ?case 
    by (simp, metis (no_types, opaque_lifting) Cons.prems distinct_remdups_id foldr.simps(2) 
              interval_sort_lower_width_def interval_sort_lower_width_distinct o_apply)
qed
  

lemma non_overlapping_sorted_remdups: 
"non_overlapping_sorted xs \<Longrightarrow>  non_overlapping_sorted (remdups xs)" 
 proof(induction "xs")
   case Nil
   then show ?case
     by(simp)
 next
   case (Cons a xs)
   then show ?case 
     unfolding non_overlapping_sorted_def
     by(auto)
 qed

lemma insert_in_lower_width: "x \<in> set (interval_insert_sort_lower_width a list) = (x = a \<or> x \<in> set list)"
proof(induction "list")
  case Nil
  then show ?case by(simp)
next
  case (Cons a list)
  then show ?case 
    unfolding interval_insert_sort_lower_width_def cmp_lower_width_def
    by auto
qed

lemma remdups_set_eq:
  assumes \<open>set xs = set ys\<close> 
  shows \<open>set (remdups xs) = set (remdups ys)\<close>
  using assms by simp  
                                                        

lemma remdups_lower_hd:
  assumes "xs \<noteq> []" and "sorted_wrt_lower xs" 
  shows "(lower \<circ> hd) (remdups xs) = (lower \<circ> hd) xs"
  using assms proof(induction xs rule:list_nonempty_induct)
    case (single x)
    then show ?case by(simp add:interval_sort_lower_width_def)
  next
    case (cons x xs)
    then show ?case 
      by (simp, metis cmp_lower_width_def list.collapse order.asym set_ConsD sorted_wrt.simps(2) 
                sorted_wrt_lower_def sorted_wrt_lower_unroll)
  qed  

subsection\<open>Various Notions of Validity of Sorted Lists of Intervals\<close>

subsubsection\<open>Validity Tests\<close>

(* Overlapping *)
definition \<open>valid_mInterval_ovl is = (sorted_wrt_lower is \<and> distinct is \<and> is \<noteq> [])\<close> 
text\<open>
  The predicate @{const "valid_mInterval_ovl"} requires that a list of intervals is 
  distinct and sorted with respect to the lower bound of each interval.
\<close>

(* Non-Overlapping (but possibly adjacent) *)
definition valid_mInterval_adj :: "'a::minus_mono interval list \<Rightarrow> bool"  
  where \<open>valid_mInterval_adj is = (non_overlapping_sorted is \<and> distinct is \<and> is \<noteq> [])\<close>
text\<open>
  The predicate @{const "valid_mInterval_adj"} is strictly stronger than @{const "valid_mInterval_ovl"}:
\<close>
lemma valid_adj_imp_ovl: \<open>valid_mInterval_adj x \<Longrightarrow> valid_mInterval_ovl x\<close>
  by (simp add: non_overlapping_implies_sorted_wrt_lower valid_mInterval_adj_def valid_mInterval_ovl_def) 
text\<open>
  Informally,@{const "valid_mInterval_ovl"} further limits the list of intervals to be non-overlapping. 
  Note that adjacent intervals (i.e., intervals that share the same bounds) are allowed. For example:
\<close>
lemma "valid_mInterval_adj [Interval(1::int,2), Interval(2,3)]"
  apply(simp add: valid_mInterval_adj_def non_overlapping_sorted_def cmp_non_overlapping_def)
  by (smt (verit) lower_bounds) 

(* Disjunct (non-overlapping and non-adjacent) *)
definition \<open>valid_mInterval_non_ovl is = (valid_mInterval_ovl is \<and> non_adjacent_sorted_wrt_lower is)\<close>
text\<open>
  Informally,@{const "valid_mInterval_non_ovl"} further limits the list of intervals to also forbid 
  adjacent intervals (i.e., intervals that share the same bounds) are allowed. It is strictly stronger
  than the other two predicates:
\<close>
lemma valid_non_ovl_imp_ovl: \<open>valid_mInterval_non_ovl x \<Longrightarrow> valid_mInterval_ovl x\<close>
  using valid_mInterval_non_ovl_def by blast 
lemma valid_non_ovl_imp_adj: \<open>valid_mInterval_non_ovl x \<Longrightarrow> valid_mInterval_adj x\<close>
  by (simp add: non_adjacent_implies_non_overlapping valid_mInterval_adj_def valid_mInterval_non_ovl_def 
                valid_mInterval_ovl_def) 

lemma valid_mInterval_non_ovl_sorted: "valid_mInterval_non_ovl xs \<Longrightarrow> sorted_wrt_lower xs"
  by (metis (no_types, lifting) valid_mInterval_non_ovl_def valid_mInterval_ovl_def) 

lemma valid_mInterval_non_ovl_unroll:
  \<open>ys \<noteq> [] \<Longrightarrow> valid_mInterval_non_ovl (y # ys) \<Longrightarrow> valid_mInterval_non_ovl ys\<close>
  unfolding valid_mInterval_non_ovl_def valid_mInterval_ovl_def non_adjacent_sorted_wrt_lower_def
  by(auto simp add: sorted_wrt_lower_tail)

lemma valid_mInterval_non_ovl_eqI:
  assumes \<open>valid_mInterval_non_ovl xs\<close>
  and     \<open>valid_mInterval_non_ovl ys\<close>
  and     \<open>set xs = set ys\<close>
  shows \<open>xs = ys\<close>
proof(insert assms, induction xs ys rule:list_induct2')
  case 1
  then show ?case 
    by(simp)
next
  case (2 x xs)
  then show ?case 
    by simp
next
  case (3 y ys)
  then show ?case 
    by simp
next
  case (4 x xs y ys)
  then show ?case 
  proof(cases xs)
    case Nil note xsNil = this
    then show ?thesis 
    proof(cases ys)
      case Nil
      then show ?thesis 
        using xsNil 4 by simp 
    next
      case (Cons a list)
      then show ?thesis 
        using xsNil 4 
        by (simp add: valid_mInterval_non_ovl_def valid_mInterval_ovl_def)
    qed
  next
    case (Cons x' xs') note xCons = this
    then show ?thesis 
    proof(cases ys)
      case Nil
      then show ?thesis 
        using xCons 4
        by (simp add: valid_mInterval_non_ovl_def valid_mInterval_ovl_def)
    next
      case (Cons y' ys')
      then show ?thesis 
        using xCons 4 valid_mInterval_non_ovl_unroll[of xs x] valid_mInterval_non_ovl_unroll[of ys y]
        unfolding cmp_non_adjacent_def non_adjacent_sorted_wrt_lower_def valid_mInterval_non_ovl_def 
                  valid_mInterval_ovl_def sorted_wrt_lower_def cmp_lower_width_def
        by (metis (no_types, lifting) "4.prems"(1) "4.prems"(2) cmp_non_adjacent_lower insert_eq_iff 
                  list.distinct(1) list.set_intros(1) list.simps(15) non_adjacent_sorted_wrt_lower_def 
                  order.asym set_ConsD sorted_wrt.simps(2) valid_mInterval_non_ovl_def) 
    qed
  qed
qed

subsubsection\<open>Constructors\<close>

paragraph\<open>Overlapping Intervals\<close>

definition \<open> mk_mInterval_ovl = remdups o interval_sort_lower_width\<close>

lemma mk_mInterval_ovl_non_empty: \<open>is \<noteq> [] \<Longrightarrow> (mk_mInterval_ovl is) \<noteq> []\<close>
  unfolding mk_mInterval_ovl_def o_def interval_sort_lower_width_def  
proof(induction "is" rule:list_nonempty_induct)
  case (single x)
  then show ?case by simp
next
  case (cons x xs)
  then show ?case 
    apply(simp)
    by (metis (no_types, lifting) interval_insert_sort_lower_width.simps(2) list.collapse list.simps(3))
qed

lemma mk_mInterval_ovl_empty[simp]:
  "mk_mInterval_ovl [] = []"
  by(simp add: mk_mInterval_ovl_def interval_sort_lower_width_def) 

lemma mk_mInterval_ovl_distinct: \<open>distinct (mk_mInterval_ovl is)\<close>
  unfolding mk_mInterval_ovl_def by simp 

lemma sorted_wrt_lower_remdups:
"sorted_wrt_lower xs \<Longrightarrow>  sorted_wrt_lower (remdups xs)" 
 proof(induction "xs")
   case Nil
   then show ?case
     by(simp)
 next
   case (Cons a xs)
   then show ?case 
     unfolding sorted_wrt_lower_def
     by(auto)
 qed

lemma interval_sort_lower_width_swap_remdups:
  \<open>remdups (interval_sort_lower_width xs) = interval_sort_lower_width (remdups xs)\<close>
  for xs::"'a::{minus_mono, linordered_field} interval list"
proof(induction xs)
  case Nil
  then show ?case 
    by (metis interval_sort_lower_width_remdups remdups.simps(1)) 
next
  case (Cons a xs)
  then show ?case 
        by (metis (mono_tags, lifting) distinct_remdups interval_sort_lower_width_remdups 
                  interval_sort_lower_width_set_eq interval_sort_lower_width_sorted set_remdups 
                  sorted_wrt_lower_distinct_lists_eq sorted_wrt_lower_remdups) 
qed


lemma mk_mInterval_ovl_sorted: \<open>sorted_wrt_lower (mk_mInterval_ovl is)\<close>
 proof(induction "is")
   case Nil
   then show ?case   
     unfolding mk_mInterval_ovl_def sorted_wrt_lower_def interval_sort_lower_width_def
     by simp
 next
   case (Cons a "is")
   then show ?case 
     using interval_sort_lower_width_sorted sorted_wrt_lower_remdups
     unfolding mk_mInterval_ovl_def sorted_wrt_lower_def interval_sort_lower_width_def o_def
     by blast
 qed

theorem mk_mInterval_ovl_valid: \<open>is \<noteq> [] \<Longrightarrow> valid_mInterval_ovl (mk_mInterval_ovl is)\<close>
  unfolding valid_mInterval_ovl_def
  by (simp add: mk_mInterval_ovl_distinct mk_mInterval_ovl_non_empty mk_mInterval_ovl_sorted) 

lemma valid_mk_mInterval_ovl_id:
  assumes \<open>valid_mInterval_ovl xs\<close> 
  shows \<open>mk_mInterval_ovl xs = xs\<close>
proof(insert assms, induction xs)
  case Nil
  then show ?case 
    by(simp add: valid_mInterval_ovl_def)
next
  case (Cons a xs)
  then show ?case 
    apply(simp add: mk_mInterval_ovl_def interval_sort_lower_width_def valid_mInterval_ovl_def 
                    sorted_wrt_lower_def cmp_lower_width_def)
    by (metis (no_types, opaque_lifting) cmp_lower_width_def distinct_singleton foldr_isort_elements 
              insertI1 interval_insert_sort_lower_width.simps(1) interval_insert_sort_lower_width.simps(2) 
               interval_sort_lower_width_def list.distinct(1) list.simps(15) min_list.cases remdups.simps(2) 
               remdups_id_iff_distinct) 
qed

lemma mk_mInterval_ovl_eq:
  assumes \<open>set xs = set (ys::'a::{minus_mono, linordered_field} interval list)\<close> 
  shows \<open>mk_mInterval_ovl xs = mk_mInterval_ovl ys \<close>
  by (metis (no_types, lifting) assms comp_def interval_sort_lower_width_set_eq mk_mInterval_ovl_def 
             mk_mInterval_ovl_def mk_mInterval_ovl_distinct mk_mInterval_ovl_sorted set_remdups 
             sorted_wrt_lower_distinct_lists_eq)

paragraph\<open>Adjacent Intervals\<close>

definition mk_mInterval_adj :: "('a::{minus, linorder,linorder}) interval list \<Rightarrow> 'a interval list"
  where \<open>mk_mInterval_adj = remdups o merge_overlapping_intervals_sorted_wrt_lower o mk_mInterval_ovl\<close> 

lemma mk_mInterval_adj_non_overlapping_sorted:  \<open>non_overlapping_sorted (mk_mInterval_adj (is::'a::{minus_mono} interval list))\<close>
  using interval_sort_lower_width_sorted sorted_wrt_lower_remdups mk_mInterval_ovl_sorted[of "is"]
        merge_overlapping_intervals_sorted_wrt_lower_sorted_lower[of "(mk_mInterval_ovl is)"]
        merge_overlapping_intervals_sorted_sorted_non_non_overlapping non_overlapping_sorted_remdups
  unfolding mk_mInterval_adj_def o_def
  by blast

lemma mk_mInterval_adj_sorted:  \<open>sorted_wrt_lower (mk_mInterval_adj (is::'a::minus_mono interval list))\<close>
  using interval_sort_lower_width_sorted sorted_wrt_lower_remdups mk_mInterval_ovl_sorted[of "is"]
        merge_overlapping_intervals_sorted_wrt_lower_sorted_lower[of "(mk_mInterval_ovl is)"]
  unfolding mk_mInterval_adj_def o_def
  by auto

lemma mk_mInterval_adj_non_empty: \<open>is \<noteq> [] \<Longrightarrow> (mk_mInterval_adj is) \<noteq> []\<close>
  unfolding mk_mInterval_adj_def o_def 
  using mk_mInterval_ovl_non_empty merge_overlapping_intervals_sorted_wrt_lower_non_nil
  by (metis remdups_eq_nil_right_iff) 

lemma mk_mInterval_adj_empty[simp]:
  "mk_mInterval_adj [] = []"
  by(simp add: mk_mInterval_adj_def) 

lemma mk_mInterval_adj_distinct: \<open>distinct (mk_mInterval_adj is)\<close>
  unfolding mk_mInterval_adj_def by simp 

theorem mk_mInterval_adj_valid: \<open>is \<noteq> [] \<Longrightarrow> valid_mInterval_adj (mk_mInterval_adj is)\<close>
  unfolding valid_mInterval_adj_def 
  using mk_mInterval_adj_non_overlapping_sorted mk_mInterval_adj_distinct mk_mInterval_adj_non_empty
  by auto 

lemma valid_mk_mInterval_adj_id:
  assumes \<open>valid_mInterval_adj xs\<close> 
  shows \<open>mk_mInterval_adj xs = xs\<close>
proof(insert assms, induction xs)
  case Nil
  then show ?case 
    by(simp add: valid_mInterval_adj_def)
next
  case (Cons a xs)
  then show ?case 
    using valid_mk_mInterval_ovl_id[of "a#xs", simplified valid_adj_imp_ovl[of "a#xs", simplified Cons, simplified], simplified]  
          valid_mk_mInterval_ovl_id[of "xs", simplified valid_adj_imp_ovl[of "xs", simplified Cons, simplified], simplified]  
    unfolding valid_mInterval_adj_def mk_mInterval_adj_def o_def
    apply(simp add: mk_mInterval_ovl_def interval_sort_lower_width_def valid_mInterval_ovl_def
                    sorted_wrt_lower_def cmp_lower_width_def non_overlapping_sorted_def cmp_non_overlapping_def)
    by (smt (verit) One_nat_def add.commute foldr_interval_insert_sort_lower_width_distinct foldr_isort_elements 
            interval_insert_sort_lower_width.simps(2) interval_insert_sort_lower_width_length length_remdups_card_conv 
            length_remdups_eq list.sel(1) list.sel(3) list.set_intros(1) list.size(4) merge_overlapping_intervals_sorted_wrt_lower.elims 
            merge_overlapping_intervals_sorted_wrt_lower.simps(2) remdups.simps(2) remdups_id_iff_distinct set_remdups) 
  
  qed

lemma mk_mInterval_adj_eq:
  assumes \<open>set xs = set (ys::'a::{minus_mono, linordered_field} interval list)\<close> 
  shows \<open>mk_mInterval_adj xs = mk_mInterval_adj ys \<close>
  by (metis (no_types, lifting) assms comp_def interval_sort_lower_width_set_eq mk_mInterval_adj_def 
             mk_mInterval_ovl_def mk_mInterval_ovl_distinct mk_mInterval_ovl_sorted set_remdups 
             sorted_wrt_lower_distinct_lists_eq)

lemma mk_mInterval_ovl_id:
  "mk_mInterval_ovl (mk_mInterval_ovl x) = mk_mInterval_ovl x"
  unfolding mk_mInterval_ovl_def o_def 
  by (metis comp_def mk_mInterval_ovl_def mk_mInterval_ovl_empty mk_mInterval_ovl_valid valid_mk_mInterval_ovl_id)
 
value "valid_mInterval_adj (mk_mInterval_adj ([Ivl (1::int) 2, Ivl 1 3, Ivl 1 1]))"
value "valid_mInterval_adj (mk_mInterval_adj ([Ivl (1::int) 1, Ivl 1 2, Ivl 2 3]))"

paragraph\<open>Non-Overlapping Intervals\<close>
definition \<open>mk_mInterval_non_ovl = remdups o merge_adjacent_intervals_sorted_wrt_lower o mk_mInterval_ovl\<close>

lemma mk_mInterval_non_ovl_distinct:
  "distinct (mk_mInterval_non_ovl is)"
  by (simp add: mk_mInterval_non_ovl_def)

lemma mk_mInterval_non_ovl_non_empty:
  "is \<noteq> [] \<Longrightarrow> mk_mInterval_non_ovl is \<noteq> []"
  by (simp add: merge_adjacent_intervals_sorted_wrt_lower_non_nil mk_mInterval_ovl_non_empty mk_mInterval_non_ovl_def) 

lemma mk_mInterval_non_ovl_empty[simp]:
  "mk_mInterval_non_ovl [] = []"
  by (simp add: merge_adjacent_intervals_sorted_wrt_lower_non_nil mk_mInterval_non_ovl_def) 

lemma mk_mInterval_non_ovl_eq:
  assumes \<open>set xs = set (ys::'a::{minus_mono, linordered_field} interval list)\<close> 
  shows \<open>mk_mInterval_non_ovl xs = mk_mInterval_non_ovl ys \<close>
  unfolding mk_mInterval_non_ovl_def o_def
  by (metis (no_types, opaque_lifting) assms comp_apply foldr_isort_elements 
            interval_sort_lower_width_def mk_mInterval_ovl_def mk_mInterval_ovl_distinct 
            mk_mInterval_ovl_sorted set_remdups sorted_wrt_lower_distinct_lists_eq) 

lemma sorted_wrt_lower_merge_adjacent_intervals_sorted_wrt_lower:
  "sorted_wrt_lower xs \<Longrightarrow> sorted_wrt_lower (merge_adjacent_intervals_sorted_wrt_lower xs)"
proof(induction xs rule:merge_adjacent_intervals_sorted_wrt_lower.induct)
  case 1
  then show ?case by simp
next
  case (2 x)
  then show ?case by simp
next
  case (3 x y ys)
  then show ?case
  proof(cases "upper x < lower y")
    case True
    then show ?thesis 
      using 3 
      by (smt (verit, del_insts) leD list.discI list.sel(1) lower_le_upper 
              merge_adjacent_intervals_sorted_wrt_lower.simps(3) 
              merge_adjacent_intervals_sorted_wrt_lower_non_nil 
              merge_adjacent_intervals_sorted_wrt_lower_sorted_lower_lower_hd 
              sorted_wrt_lower_unroll) 
  next
    case False
    then show ?thesis 
      using 3 
      by (smt (verit, del_insts) list.distinct(1) list.sel(1) max.absorb3 max_absorb2 
              merge_adjacent_intervals_sorted_wrt_lower.simps(3) mk_interval_id mk_interval_lower 
              not_le_imp_less sorted_wrt_lower_tail' sorted_wrt_lower_unroll)
  qed
qed



lemma mk_mInterval_non_ovl_sorted_wrt_lower:
  "is \<noteq> [] \<Longrightarrow> sorted_wrt_lower (mk_mInterval_non_ovl (is::int interval list))"
  unfolding mk_mInterval_non_ovl_def o_def
  using mk_mInterval_ovl_sorted sorted_wrt_lower_merge_adjacent_intervals_sorted_wrt_lower sorted_wrt_lower_remdups by blast 

lemma valid_ovl_mkInterval_non_ovl: "is \<noteq> [] \<Longrightarrow> valid_mInterval_ovl (mk_mInterval_non_ovl is)"
  unfolding valid_mInterval_ovl_def 
  by (simp add: merge_adjacent_intervals_sorted_wrt_lower_non_nil mk_mInterval_non_ovl_def 
                mk_mInterval_ovl_non_empty mk_mInterval_ovl_sorted sorted_wrt_lower_merge_adjacent_intervals_sorted_wrt_lower 
                sorted_wrt_lower_remdups) 

lemma non_adj_sorted_mkInterval_non_ovl:
"sorted_wrt_lower xs
\<Longrightarrow> non_adjacent_sorted_wrt_lower (merge_adjacent_intervals_sorted_wrt_lower xs)"  
proof(induction xs rule:merge_adjacent_intervals_sorted_wrt_lower.induct)
  case 1
  then show ?case 
    unfolding non_adjacent_sorted_wrt_lower_def by(simp)
next
  case (2 x)
  then show ?case 
    unfolding non_adjacent_sorted_wrt_lower_def by(simp)
next
  case (3 x y ys)
  then show ?case 
  proof(cases "upper x < lower y")
    case True
    then show ?thesis
      apply(simp)
      apply(subst non_adjacent_sorted_wrt_lower_unroll)
      subgoal by(simp add: merge_adjacent_intervals_sorted_wrt_lower_non_nil) 
      subgoal using 3 True 
        by (metis list.sel(1) merge_adjacent_intervals_sorted_wrt_lower_sorted_lower_lower_hd sorted_wrt_lower_tail) 
      done 
  next
    case False
    then show ?thesis 
    proof(cases ys)
      case Nil
      then show ?thesis
        unfolding non_adjacent_sorted_wrt_lower_def cmp_non_adjacent_def
        by(simp add: max_def 3 False split:if_splits)
    next
      case (Cons a list)
      then have a: "sorted_wrt_lower (mk_interval (lower x, max (upper y) (upper x)) # ys)" 
      proof(cases "upper y \<le> upper x")
        case True note * = this
        then show ?thesis 
        proof (cases "upper y = upper x")
          case True
          then show ?thesis 
            using False True apply(simp)
            using 3 * False sorted_wrt_lower_unroll[of "y#ys" x, simplified]
                  sorted_wrt_lower_tail[of y ys] 
                  sorted_wrt_lower_tail'[of x y ys]
            by auto             
        next
          case False
          then show ?thesis 
            using False True apply(simp)
            using 3 * False sorted_wrt_lower_unroll[of "y#ys" x, simplified]
                  sorted_wrt_lower_tail[of y ys] 
                  sorted_wrt_lower_tail'[of x y ys]
            by auto             
        qed
      next
        case False
        then show ?thesis 
            using Cons False  apply(simp)
            using 3 False sorted_wrt_lower_unroll[of "y#ys" x, simplified]
                  sorted_wrt_lower_tail[of y ys] 
                  sorted_wrt_lower_tail'[of x y ys]
            apply(simp)  
            by (smt (verit, ccfv_threshold) less_le_not_le list.distinct(1) list.sel(1) max.absorb1 
                    max.assoc max.cobounded2 mk_interval_id mk_interval_lower sorted_wrt_lower_unroll)            
      qed
      then show ?thesis
        using False 3[simplified a False , simplified]
        by simp
    qed
  qed
qed


lemma bin_op_mInterval_commute: 
  assumes op_commute: \<open>\<And> x y. op x y = op y x\<close> 
  shows \<open>mk_mInterval_non_ovl (bin_op_interval_list op x y) = mk_mInterval_non_ovl (bin_op_interval_list op y (x::'a::{minus_mono, linordered_field} interval list))\<close>
  using bin_op_interval_list_commute  mk_mInterval_non_ovl_eq
  by (metis op_commute) 

lemma iList_plus_mInterval_ovl_assoc:
  \<open>mk_mInterval_ovl (iList_plus x (iList_plus y z)) = mk_mInterval_ovl (iList_plus (iList_plus x (y::'a::{minus_mono, linordered_field} interval list)) z)\<close>
  by (meson iList_plus_assoc mk_mInterval_ovl_eq) 

lemma iList_plus_mInterval_adj_commute: 
  \<open>mk_mInterval_adj (iList_plus x y) = mk_mInterval_adj (iList_plus y (x::'a::{minus_mono, linordered_field} interval list))\<close>
  by (meson iList_plus_commute mk_mInterval_adj_eq) 


lemma iList_plus_mInterval_non_ovl_assoc: 
  \<open>mk_mInterval_non_ovl (iList_plus x (iList_plus y z)) = mk_mInterval_non_ovl (iList_plus (iList_plus x (y::'a::{minus_mono, linordered_field} interval list)) z)\<close>
  by (meson iList_plus_assoc mk_mInterval_non_ovl_eq)

lemma iList_plus_mInterval_non_ovl_commute: 
  \<open>mk_mInterval_non_ovl (iList_plus x y) = mk_mInterval_non_ovl (iList_plus y (x::'a::{minus_mono, linordered_field} interval list))\<close>
  by (meson iList_plus_commute mk_mInterval_non_ovl_eq) 

lemma iList_plus_mInterval_adj_assoc: 
  \<open>mk_mInterval_non_ovl (iList_plus x (iList_plus y z)) = mk_mInterval_non_ovl (iList_plus (iList_plus x (y::'a::{minus_mono, linordered_field} interval list)) z)\<close>
  by (meson iList_plus_assoc mk_mInterval_non_ovl_eq) 

lemma sorted_wrt_lower_mk_mInterval_non_ovl: "sorted_wrt_lower (mk_mInterval_non_ovl xs)"
  unfolding mk_mInterval_non_ovl_def
  by (simp add: mk_mInterval_ovl_sorted sorted_wrt_lower_merge_adjacent_intervals_sorted_wrt_lower 
                sorted_wrt_lower_remdups)

theorem mk_mInterval_non_ovl_valid: \<open>sorted_wrt_lower is \<Longrightarrow> is \<noteq> [] \<Longrightarrow> valid_mInterval_non_ovl (mk_mInterval_non_ovl is)\<close>
  using  non_adj_sorted_mkInterval_non_ovl[of "is"] valid_ovl_mkInterval_non_ovl[of "is"]
  unfolding valid_mInterval_non_ovl_def mk_mInterval_non_ovl_def o_def
  by (simp add: distinct_remdups_id mk_mInterval_ovl_sorted non_adj_sorted_mkInterval_non_ovl non_adjacent_implies_distinct) 

lemma valid_mk_mInterval_non_ovl_id:
  assumes \<open>valid_mInterval_non_ovl xs\<close> 
  shows \<open>mk_mInterval_non_ovl xs = xs\<close>
proof(insert assms, induction xs)
  case Nil
  then show ?case 
    by(simp add: valid_mInterval_non_ovl_def valid_mInterval_ovl_def)
next
  case (Cons a xs)
  then show ?case 
    using valid_mk_mInterval_ovl_id[of "a#xs", simplified valid_non_ovl_imp_ovl[of "a#xs", simplified Cons, simplified], simplified]  
          valid_mk_mInterval_ovl_id[of "xs", simplified valid_non_ovl_imp_ovl[of "xs", simplified Cons, simplified], simplified]  
    unfolding valid_mInterval_non_ovl_def mk_mInterval_non_ovl_def o_def
    apply(simp)    
    apply(simp add: mk_mInterval_ovl_def interval_sort_lower_width_def valid_mInterval_ovl_def
                    sorted_wrt_lower_def cmp_lower_width_def non_overlapping_sorted_def cmp_non_overlapping_def)
    by (smt (verit) Cons.prems list.sel(1) list.sel(3) merge_adjacent_intervals_sorted_wrt_lower.elims 
             merge_adjacent_intervals_sorted_wrt_lower.simps(2) non_adj_sorted_mkInterval_non_ovl non_adjacent_implies_distinct 
             non_adjacent_sorted_wrt_lower_def non_adjacent_sorted_wrt_lower_unroll remdups_id_iff_distinct sorted_wrt.simps(2) 
             valid_mInterval_non_ovl_sorted)   
qed

lemma mk_mInterval_non_ovl_single: 
  "mk_mInterval_non_ovl [x] = [x]"
  by (simp add: non_adjacent_implies_sorted_wrt_lower non_adjacent_sorted_wrt_lower_def 
                valid_mInterval_non_ovl_def valid_mInterval_ovl_def valid_mk_mInterval_non_ovl_id)

lemma mk_mInterval_non_ovl_id: 
  "mk_mInterval_non_ovl (mk_mInterval_non_ovl x) = mk_mInterval_non_ovl x"
  unfolding mk_mInterval_non_ovl_def o_def 
  by (metis (no_types, opaque_lifting) comp_apply distinct_remdups_id mk_mInterval_non_ovl_def mk_mInterval_non_ovl_empty 
             mk_mInterval_ovl_sorted non_adj_sorted_mkInterval_non_ovl non_adjacent_implies_distinct 
             valid_mInterval_non_ovl_def valid_mk_mInterval_non_ovl_id valid_ovl_mkInterval_non_ovl)

value "valid_mInterval_non_ovl (mk_mInterval_non_ovl ([Ivl (1::int) 2, Ivl 1 3, Ivl 1 1]))"
value "valid_mInterval_non_ovl (mk_mInterval_non_ovl ([Ivl (1::int) 1, Ivl 1 2, Ivl 2 3]))"


value\<open>mk_mInterval_ovl [mk_interval ((1::int), 4), mk_interval (0,2), mk_interval (3,5), mk_interval (5,7),
                    mk_interval (7,7), mk_interval (8,8)]\<close>
value\<open>mk_mInterval_adj [mk_interval ((1::int), 4), mk_interval (0,2), mk_interval (3,5), mk_interval (5,7), 
                    mk_interval (7,7), mk_interval (8,8)]\<close>
value\<open>mk_mInterval_non_ovl [mk_interval ((1::int), 4), mk_interval (0,2), mk_interval (3,5), mk_interval (5,7), 
                    mk_interval (7,7), mk_interval (8,8)]\<close>

subsection\<open>Union over a List of Intervals\<close>

definition \<open>set_of_interval_list XS = foldr (\<lambda>x a. set_of x \<union> a) XS {}\<close>

lemma set_of_interval_list_nonempty:
  assumes non_empty: \<open>XS \<noteq> ([]::real interval list)\<close>
  shows \<open>(set_of_interval_list XS) \<noteq> {}\<close>
using assms proof(induction XS rule:list_nonempty_induct)
  case (single x)
  then show ?case by(simp add:set_of_interval_list_def set_of_eq)
next
  case (cons x xs)
  then show ?case 
    by(simp add:set_of_interval_list_def)
qed                                                                              


lemma set_of_interval_list_bdd_below:
  assumes non_empty: \<open>XS \<noteq> ([]::real interval list)\<close>
shows \<open>bdd_below (set_of_interval_list XS)\<close>
using assms proof(induction XS rule:list_nonempty_induct)
  case (single x)
  then show ?case by(simp add:set_of_interval_list_def set_of_eq)
next
  case (cons x xs)
  then show ?case 
    by(simp add:set_of_eq set_of_interval_list_def sorted_wrt_lower_def)
qed


lemma set_of_interval_list_bdd_above:
  assumes non_empty: \<open>XS \<noteq> ([]::real interval list)\<close>
shows \<open>bdd_above (set_of_interval_list XS)\<close>
using assms proof(induction XS rule:list_nonempty_induct)
  case (single x)
  then show ?case by(simp add:set_of_interval_list_def set_of_eq)
next
  case (cons x xs)
  then show ?case 
    by(simp add:set_of_eq set_of_interval_list_def contiguous_def)
qed


lemma inf_set_of_interval_list_lower:
  assumes non_empty: \<open>XS \<noteq> ([]::real interval list)\<close>
  and     sorted: \<open>sorted_wrt_lower XS\<close>
shows \<open>Inf (set_of_interval_list XS) = lower (hd XS)\<close>
using assms proof(induction XS rule:list_nonempty_induct)
  case (single x)
  then show ?case by(simp add:set_of_interval_list_def set_of_eq)
next
  case (cons x xs)
  then show ?case 
    apply(simp add: set_of_interval_list_def)  
    apply(subst cInf_union_distrib)
    subgoal by simp
    subgoal by(simp add:set_of_eq)
    subgoal by(fold set_of_interval_list_def , simp add: set_of_interval_list_nonempty)
    subgoal 
      apply (fold set_of_interval_list_def)
      using sorted_wrt_lower_unroll[of xs x, simplified cons, simplified]
            set_of_interval_list_bdd_below
      by(simp) 
    subgoal 
      using sorted_wrt_lower_unroll[of xs x, simplified cons, simplified]
      by (metis inf.orderE interval_bounds_real(2) lower_le_upper nle_le order_less_le set_of_eq) 
    done 
qed

lemma contiguous_sorted_wrt_upper:
  assumes "contiguous (xs:: real interval list)"
  shows "sorted_wrt_upper xs" 
  unfolding sorted_wrt_upper_def
  using assms unfolding contiguous_def lower_le_upper 
  by (metis assms contiguous_non_overlapping non_overlapping_implies_sorted_wrt_upper sorted_wrt_upper_def)

lemma contiguous_sorted_wrt_lower:
  assumes "contiguous (XS:: real interval list)"
  shows "sorted_wrt_lower XS" 
  unfolding sorted_wrt_lower_def
  using assms contiguous_non_overlapping[of XS] non_overlapping_implies_sorted_wrt_lower 
    sorted_wrt_lower_def by metis

lemma max_last_sorted_wrt_upper:
  assumes "XS \<noteq> []" "sorted_wrt_upper (XS:: 'a::{linorder} interval list)" 
  shows "Max (set(map upper XS)) = upper (last XS)"
  using assms 
proof (induction XS rule: list_nonempty_induct)
  case (single x)
  then show ?case by simp
next
  case (cons x xs)
  then have a0: "sorted_wrt (\<lambda>x y. upper x \<le> upper y) (x # xs)" by (simp add: sorted_wrt_upper_def) 
  then have a1: "Max (set (map upper (x # xs))) = upper (last (x # xs))" using cons unfolding sorted_wrt_upper_def by simp
  then show ?case using a0 a1 cons unfolding sorted_wrt_upper_def by simp
qed

lemma min_hd_sorted_wrt_lower:
  assumes "XS \<noteq> []" "sorted_wrt_lower (XS:: 'a::{linorder,minus,preorder} interval list)" 
  shows "Min (set(map lower XS)) = lower (hd XS)"
  using assms 
proof (induction XS rule: list_nonempty_induct)
  case (single x)
  then show ?case by simp
next
  case (cons x xs)
  then have a0: "sorted_wrt (\<lambda> x y.  if lower x = lower y then width x \<le> width y else lower x < lower y) (x # xs)" 
    unfolding sorted_wrt_lower_def cmp_lower_width_def by simp
  then have a1: "Min (set(map lower (x # xs))) = lower (hd (x # xs))" using cons unfolding sorted_wrt_lower_def cmp_lower_width_def 
    by (smt (verit, del_insts) arg_min_list.simps(2) cons.IH cons.prems f_arg_min_list_f image_set list.distinct(1) list.exhaust_sel list.sel(1) order_less_imp_le sorted_wrt_lower_unroll) 
  then show ?case using a0 a1 cons unfolding sorted_wrt_upper_def by simp
qed

lemma lower_isort:
  assumes \<open>xs \<noteq> []\<close>and \<open>(lower o hd) xs = Min (lower ` (set xs))\<close>
  shows \<open>(lower \<circ> hd) (interval_sort_lower_width xs) = (lower \<circ> hd) xs\<close>
  proof(insert assms, induction xs rule:list_nonempty_induct)
    case (single x)
    then show ?case by(simp add:interval_sort_lower_width_def)
  next
    case (cons x xs)
    then show ?case 
      apply(simp add:interval_sort_lower_width_def)
      by (metis (no_types, opaque_lifting) comp_eq_dest_lhs cons.prems foldr.simps(2) foldr_isort_elements 
                interval_insert_sort_lower_width_nonempty interval_sort_lower_width_def 
                interval_sort_lower_width_sorted list.sel(1) list.set_map min_hd_sorted_wrt_lower) 
  qed  

lemma min_sort: 
  "Min (set (map lower (foldr interval_insert_sort_lower_width xs []))) = Min (set (map lower xs))"
  using foldr_isort_elements
  by (metis list.set_map) 

lemma mk_mInterval_lower: 
  assumes "xs \<noteq> []" 
  shows "Min (set (map lower (mk_mInterval_non_ovl xs))) = Min (set (map lower xs))"
proof (induction xs)
  case Nil
  then show ?case 
    unfolding mk_mInterval_non_ovl_def mk_mInterval_ovl_def interval_sort_lower_width_def  
    by simp
next
  case (Cons a xs)
  have a: "Min (set (map lower (foldr interval_insert_sort_lower_width xs []))) = Min (set (map lower xs))"
    using foldr_isort_elements
    by (metis list.set_map) 
  then show ?case
    unfolding mk_mInterval_non_ovl_def mk_mInterval_ovl_def o_def
    using Cons 
    by (smt (verit, ccfv_SIG) foldr_isort_elements interval_sort_lower_width_def interval_sort_lower_width_sorted 
            list.discI list.set_map merge_adjacent_intervals_sorted_wrt_lower_non_nil set_empty
             merge_adjacent_intervals_sorted_wrt_lower_sorted_lower_lower_hd  min_hd_sorted_wrt_lower 
             set_remdups sorted_wrt_lower_merge_adjacent_intervals_sorted_wrt_lower sorted_wrt_lower_remdups) 
qed

lemma sup_set_of_interval_list_upper:
  assumes non_empty: \<open>XS \<noteq> ([]::real interval list)\<close>
  and     sorted: \<open>sorted_wrt_upper XS\<close>
shows \<open>Sup (set_of_interval_list XS) = upper (last XS)\<close>
using assms proof(induction XS rule:list_nonempty_induct)
  case (single x)
  then show ?case by(simp add:set_of_interval_list_def set_of_eq)
next
  case (cons x xs)
  have "Max (set (map upper (x # xs))) = upper (last (x # xs))" using max_last_sorted_wrt_upper assms cons by blast
  then show ?case 
    apply(simp add: set_of_interval_list_def)  
    apply(subst cSup_union_distrib)
        apply(fold set_of_interval_list_def)
    subgoal by simp
    subgoal using bdd_above_set_of by metis
    subgoal using cons.hyps set_of_interval_list_nonempty by presburger
    subgoal using cons.hyps set_of_interval_list_bdd_above by presburger
    subgoal 
    proof -
      assume a1: "Max (insert (upper x) (upper ` set xs)) = upper (if xs = [] then x else last xs)"
      have f2: "\<forall>i. Sup (set_of i) = (upper i::real)"
        by (simp add: set_of_eq)
      have "[] = xs \<or> sorted_wrt_upper xs"
        by (metis cons.prems sorted_wrt_upper_unroll)
      then show ?thesis
        using f2 a1 cons.IH sup_real_def by force
    qed
    done
qed                                                                          

lemma compact_set_of_interval_list: 
   \<open>compact (set_of_interval_list (XS::('a::{preorder,ordered_euclidean_space,topological_space} interval list)))\<close>
proof(induction XS)
  case Nil
  then show ?case by(simp add:set_of_interval_list_def)
next
  case (Cons a XS)
  then show ?case 
    by(simp add:set_of_interval_list_def, subst compact_Un, simp_all add: compact_set_of Cons set_of_eq)
qed

lemma lower_le_upper_aux: \<open>xs \<noteq> [] \<Longrightarrow> non_overlapping_sorted xs \<Longrightarrow> lower (hd xs) \<le> upper (last xs)\<close>
proof(induction xs rule:induct_list012)
  case 1
  then show ?case by(simp)
next
  case (2 x)
  then show ?case by(simp)
next
  case (3 x y zs)
  then show ?case 
    proof(cases zs)
      case Nil
      then show ?thesis
        using  3 dual_order.trans
        unfolding non_overlapping_sorted_def cmp_non_overlapping_def              
        by (simp, smt (verit, best) dual_order.trans lower_le_upper)
    next
      case (Cons a list)
      then show ?thesis 
        using  3 dual_order.trans
        unfolding non_overlapping_sorted_def cmp_non_overlapping_def              
        by (simp, smt (verit, best) dual_order.trans lower_le_upper)
    qed
  qed

lemma contiguous_lower_le_upper:  
  assumes non_empty: \<open>XS \<noteq> ([]::real interval list)\<close>
  and     contiguous: \<open>contiguous XS\<close>
shows \<open>(lower (hd XS)) \<le> (upper (last XS))\<close>
  by (simp add: contiguous contiguous_non_overlapping lower_le_upper_aux non_empty) 

lemma diameter_Sup_Inf:
  assumes \<open>compact X\<close> \<open>X \<noteq> {}\<close>
  shows \<open>diameter X \<le> Sup X - Inf X\<close>
  using assms diameter_compact_attained[of "X"]
  by (metis bounded_imp_bdd_above bounded_imp_bdd_below compact_imp_bounded sup_inf_dist_bounded) 


lemma diameter_width_compact:
  assumes \<open>compact X\<close> \<open>bdd_below X\<close> \<open>bdd_above X\<close> \<open>X \<noteq> {}\<close>
  shows \<open>diameter X = Sup X - Inf X\<close>
  using assms diameter_Sup_Inf[of X, simplified assms, simplified]
        closed_contains_Inf[of X, simplified assms, simplified] 
        closed_contains_Sup[of X, simplified assms, simplified] 
  by (smt (verit, best) compact_imp_bounded compact_imp_closed diameter_bounded_bound dist_real_def) 

lemma diameter_contiguous: 
  assumes non_empty: \<open>XS \<noteq> ([]::real interval list)\<close>
  and     contiguous: \<open>contiguous XS\<close>
shows \<open>diameter (set_of_interval_list XS) = dist (lower (hd XS)) (upper (last XS))\<close>
  apply(subst diameter_width_compact) 
  subgoal
    by (simp add: compact_set_of_interval_list contiguous non_empty)  
  subgoal
    by (simp add: \<open>compact (set_of_interval_list XS)\<close> bounded_imp_bdd_below compact_imp_bounded) 
  subgoal 
    by (simp add: contiguous set_of_interval_list_bdd_above non_empty)
  subgoal 
    by (simp add: set_of_interval_list_nonempty non_empty)
  subgoal 
    using sup_set_of_interval_list_upper[of XS, simplified assms, simplified] 
          inf_set_of_interval_list_lower[of XS, simplified assms, simplified]
          contiguous_lower_le_upper[of XS, simplified assms, simplified]
    unfolding  dist_real_def abs_real_def 
    by (simp add: contiguous contiguous_non_overlapping contiguous_sorted_wrt_upper non_overlapping_implies_sorted_wrt_lower)
  done 


lemma interval_list_union_contiguous_lower:
  assumes non_empty: \<open>XS \<noteq> []\<close>
  and     sorted: \<open>sorted_wrt_lower XS\<close>
shows \<open>lower (interval_list_union XS) = lower (hd XS)\<close>
using assms proof(induction XS rule:interval_list_union.induct)
  case 1
  then show ?case by simp
next
  case (2 I)
  then show ?case by simp
next
  case (3 I v va)
  then show ?case 
    unfolding sorted_wrt_lower_def cmp_lower_width_def
    apply (simp)
    by (metis inf.idem inf.strict_order_iff)
qed

lemma interval_list_union_contiguous_upper:
  assumes non_empty: \<open>XS \<noteq> []\<close>
  and     sorted: \<open>sorted_wrt_upper XS\<close>
shows \<open>upper (interval_list_union XS) = upper (last XS)\<close>
using assms proof(induction XS rule:interval_list_union.induct)
  case 1
  then show ?case by simp
next
  case (2 I)
  then show ?case by simp
next
  case (3 I v va)
  then show ?case 
    unfolding sorted_wrt_upper_def cmp_lower_width_def
    apply (simp)
    by (metis last_in_set sup.absorb2) 
qed


lemma interval_list_union_contiguous:
  assumes non_empty: \<open>XS \<noteq> []\<close>
  and     sorted_lower: \<open>sorted_wrt_lower XS\<close>
  and     sorted_upper: \<open>sorted_wrt_upper XS\<close>
shows \<open>interval_list_union XS = Interval (lower (hd XS), upper (last XS))\<close>
  by (metis Interval_id assms  interval_list_union_contiguous_lower interval_list_union_contiguous_upper non_empty) 

lemma contiguous_bounds_lower:
  assumes non_empty: \<open>XS \<noteq> []\<close>
  and     contiguous: \<open>contiguous (XS::real interval list )\<close>
shows "lower (hd XS) = Min (set (map lower XS))"
  using min_hd_sorted_wrt_lower[of XS, simplified assms contiguous_sorted_wrt_lower[of XS, simplified assms]] 
  by auto[1]

lemma contiguous_bounds_upper:
  assumes non_empty: \<open>XS \<noteq> []\<close>
  and     contiguous: \<open>contiguous (XS::real interval list )\<close>
shows "upper (last XS) = Max (set (map upper XS))"
  using max_last_sorted_wrt_upper[of XS, simplified assms contiguous_sorted_wrt_upper[of XS, simplified assms]] 
  by auto[1]

lemma set_of_interval_list_contiguous:
  assumes non_empty: \<open>XS \<noteq> ([]::real interval list)\<close>
  and     contiguous: \<open>contiguous XS\<close>
shows \<open>set_of_interval_list XS = {lower (hd XS)..upper (last XS)}\<close>
  using assms
proof(induction XS rule:list_nonempty_induct)
  case (single x)
  then show ?case 
    using set_of_eq
    unfolding contiguous_def set_of_interval_list_def by auto[1]
next
  case (cons x xs)
  then show ?case 
    using set_of_eq
      sup_set_of_interval_list_upper[of "(x # xs)", simplified cons contiguous_sorted_wrt_upper[of "(x # xs)", simplified assms], simplified ]
      inf_set_of_interval_list_lower[of "(x # xs)", simplified cons contiguous_sorted_wrt_lower[of "(x # xs)", simplified assms], simplified ]
    unfolding set_of_interval_list_def contiguous_def set_of_eq
    apply(auto)[1]
    subgoal 
      using cons.prems contiguous_non_overlapping lower_le_upper_aux non_overlapping_sorted_unroll 
      by fastforce
    subgoal 
      by (smt (verit, ccfv_threshold) Suc_less_eq Suc_pred atLeastAtMost_iff length_greater_0_conv 
          list.sel(1) lower_le_upper neq_Nil_conv nth_Cons_0 nth_Cons_Suc)
    subgoal 
      using less_diff_conv by force
    subgoal 
      by (smt (verit, del_insts) One_nat_def Suc_eq_plus1 atLeastAtMost_iff hd_conv_nth 
          length_greater_0_conv less_diff_conv nth_Cons_0 nth_Cons_Suc)
    done
qed

lemma set_of_interval_list_set_eq_interval_list_union_contiguous:
  assumes non_empty: \<open>XS \<noteq> ([]::real interval list)\<close>
  and     contiguous: \<open>contiguous XS\<close>
shows \<open>set_of_interval_list XS = set_of (interval_list_union XS)\<close>
  using interval_list_union_contiguous[of XS, simplified assms, simplified]
        set_of_interval_list_contiguous[of XS,simplified assms, simplified]
        contiguous_non_overlapping[of XS, simplified assms, simplified]
        non_overlapping_implies_sorted_wrt_upper[of XS]
        non_overlapping_implies_sorted_wrt_lower[of XS]
  interval_list_union_contiguous_lower[of XS] 
  interval_list_union_contiguous_upper[of XS]
  apply(simp add:set_of_eq)
  by (metis non_empty)


lemma mInterval_ovl_lower_hd_min:
  \<open>valid_mInterval_ovl x \<Longrightarrow> Min (set (map lower x)) = (lower o hd) x\<close>
proof(induction x rule:induct_list012)
  case 1
  then show ?case unfolding valid_mInterval_ovl_def by simp 
next
  case (2 x)
  then show ?case unfolding valid_mInterval_ovl_def by simp 
next
  case (3 x y zs)
  then show ?case
    apply(simp add: valid_mInterval_ovl_def non_overlapping_sorted_def cmp_non_overlapping_def image_def)
    by (metis (no_types, lifting) list.sel(1) list.simps(3) min.absorb3 min_def sorted_wrt_lower_unroll) 
qed

lemma mInterval_adj_lower_hd_min: 
  \<open>valid_mInterval_adj x \<Longrightarrow> Min (set (map lower x)) = (lower o hd) x\<close>
proof(induction x rule:induct_list012)
  case 1
  then show ?case unfolding valid_mInterval_adj_def by simp 
next
  case (2 x)
  then show ?case by simp 
next
  case (3 x y zs)
  then show ?case
    apply(simp add: valid_mInterval_adj_def non_overlapping_sorted_def cmp_non_overlapping_def image_def)
    by (metis lower_le_upper min.absorb1 min.bounded_iff)
qed

lemma mInterval_non_ovl_lower_hd_min: 
  \<open>valid_mInterval_non_ovl x \<Longrightarrow> Min (set (map lower x)) = (lower o hd) x\<close>
  unfolding valid_mInterval_non_ovl_def 
  using mInterval_ovl_lower_hd_min
  by(auto)


lemma mInterval_ovl_lower_last_max:
  \<open>valid_mInterval_ovl x  \<Longrightarrow> (Max (set (map lower x))) = (lower o last) x\<close>
proof(induction x rule:induct_list012)
  case 1
  then show ?case unfolding valid_mInterval_ovl_def by simp 
next
  case (2 x)
  then show ?case unfolding valid_mInterval_ovl_def by simp 
next
  case (3 x y zs)
  then show ?case
    by(auto simp add: sorted_wrt_lower_def cmp_lower_width_def valid_mInterval_ovl_def 
                      non_overlapping_sorted_def max_def cmp_non_overlapping_def image_def
               split: if_splits)
qed

lemma mInterval_adj_upper_hd_min: 
  \<open> valid_mInterval_adj x  \<Longrightarrow> Min (set (map upper x)) = (upper o hd) x\<close>  
proof(induction x rule:induct_list012)
  case 1
  then show ?case unfolding valid_mInterval_adj_def by simp 
next
  case (2 x)
  then show ?case unfolding valid_mInterval_adj_def by simp 
next
  case (3 x y zs)
  then show ?case
    apply(simp add: sorted_wrt_lower_def cmp_lower_width_def valid_mInterval_adj_def 
                      non_overlapping_sorted_def max_def cmp_non_overlapping_def image_def
               split: if_splits)
    by (metis (no_types, opaque_lifting) dual_order.trans lower_le_upper min.absorb2 min.commute) 
  qed

lemma mInterval_adj_upper_last_max: 
  \<open> valid_mInterval_adj x  \<Longrightarrow> Max (set (map upper x)) = (upper o last) x\<close>  
proof(induction x rule:induct_list012)
  case 1
  then show ?case unfolding valid_mInterval_adj_def by simp 
next
  case (2 x)
  then show ?case unfolding valid_mInterval_adj_def by simp 
next
  case (3 x y zs)
  then show ?case
    apply(simp add: sorted_wrt_lower_def cmp_lower_width_def valid_mInterval_adj_def 
                      non_overlapping_sorted_def max_def cmp_non_overlapping_def image_def
               split: if_splits)
    subgoal using le_left_mono lower_le_upper by blast
    subgoal using last_in_set lower_le_upper order_trans by blast 
    done 
qed


lemma set_of_subeq_aux:
  \<open>(\<Union>x\<in>set is. {lower x..upper x}) \<subseteq> {Min (lower ` (set is)) .. Max (upper ` (set is))}\<close>
proof(induction "is")
  case Nil
  then show ?case by simp
next
  case (Cons a "is")
  then show ?case
    apply(auto)[1]
    apply (meson List.finite_set Min.coboundedI finite_imageI finite_insert imageI insertCI order.trans)
    by (meson List.finite_set Max.coboundedI finite_imageI finite_insert imageI insert_iff order_trans)+
qed

lemma lower_merge_adjacent_intervals:
  assumes "xs \<noteq> []" 
    and \<open>sorted_wrt_lower xs\<close>
  shows "(lower \<circ> hd) (merge_adjacent_intervals_sorted_wrt_lower xs) = (lower \<circ> hd) xs"
  using assms proof(induction xs rule:list_nonempty_induct)
    case (single x)
    then show ?case by(simp add:interval_sort_lower_width_def)
  next
    case (cons x xs)
    then show ?case 
      apply(simp)
      by (metis list.sel(1) merge_adjacent_intervals_sorted_wrt_lower_sorted_lower_lower_hd) 
  qed

lemma sorted_wrt_lower_hd_min:
  \<open>x \<noteq> [] \<Longrightarrow> sorted_wrt_lower x \<Longrightarrow> Min (set (map lower x)) = (lower o hd) x\<close>
proof(induction x rule:induct_list012)
  case 1
  then show ?case by simp   
next
  case (2 x)
  then show ?case by simp 
next
  case (3 x y zs)
  then show ?case
    apply(simp add: valid_mInterval_ovl_def non_overlapping_sorted_def cmp_non_overlapping_def image_def)
    by (metis (no_types, lifting) list.sel(1) list.simps(3) min.absorb3 min_def sorted_wrt_lower_unroll) 
qed

lemma lower_hd_min_over_mk_mInterval_non_ovl:
  "xs \<noteq> [] \<Longrightarrow> (lower o hd) xs = Min (lower ` (set xs)) \<Longrightarrow> (lower \<circ> hd) (mk_mInterval_non_ovl xs) = (lower \<circ> hd) xs"
  unfolding mk_mInterval_non_ovl_def mk_mInterval_ovl_def 
  by (metis list.set_map mInterval_ovl_lower_hd_min mk_mInterval_lower mk_mInterval_non_ovl_def mk_mInterval_ovl_def valid_ovl_mkInterval_non_ovl) 
  

theorem valid_mInterval_non_ovl_nempty: "valid_mInterval_non_ovl x \<Longrightarrow>  x \<noteq> []"
  unfolding valid_mInterval_non_ovl_def valid_mInterval_ovl_def
  by simp


end 
