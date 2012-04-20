(*  Title:       Executable multivariate polynomials
    Author:      Christian Sternagel <christian.sternagel@uibk.ac.at>
                 René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann
    License:     LGPL
*)

(*
Copyright 2010 Christian Sternagel and René Thiemann

This file is part of IsaFoR/CeTA.

IsaFoR/CeTA is free software: you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

IsaFoR/CeTA is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along
with IsaFoR/CeTA. If not, see <http://www.gnu.org/licenses/>.
*)

header {* Strongly Normalizing Orders *}

theory SN_Orders
imports Abstract_Rewriting
begin

text {*
We define several classes of orders which are used to build ordered semirings. 
Note that we do not use Isabelle's preorders since the condition 
   $x > y = x \geq y \wedge  y \not\geq x$
   is sometimes not applicable. E.g., for $\delta$-orders over the rationals
   we have $0.2 \geq 0.1 \wedge 0.1 \not\geq 0.2$, but $0.2 >_\delta 0.1$ does not 
   hold if $\delta$ is larger than $0.1$.
*}
class non_strict_order = 
  fixes ge :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<succeq>" 50)
  assumes ge_refl: "x \<succeq> (x :: 'a)"
  and ge_trans[trans]: "\<lbrakk>x \<succeq> y; (y :: 'a) \<succeq> z\<rbrakk> \<Longrightarrow> x \<succeq> z"

class ordered_ab_semigroup = non_strict_order + ab_semigroup_add +
  assumes plus_left_mono: "\<lbrakk>x \<succeq> y\<rbrakk> \<Longrightarrow>  x + z \<succeq> y + z"

lemma plus_right_mono: "y \<succeq> (z :: 'a :: ordered_ab_semigroup) \<Longrightarrow> x + y \<succeq> x + z"
  by (simp add: add_commute[of x], rule plus_left_mono, auto)

class ordered_semiring_0 = ordered_ab_semigroup + semiring_0 +
 assumes times_left_mono: "\<lbrakk>z \<succeq> 0; x \<succeq> y\<rbrakk> \<Longrightarrow> x * z \<succeq> y * z"
     and times_right_mono: "\<lbrakk>x \<succeq> 0; y \<succeq> z\<rbrakk> \<Longrightarrow> x * y \<succeq> x * z"

class ordered_semiring_1 = ordered_semiring_0 + semiring_1 +
  assumes one_ge_zero: "1 \<succeq> 0"

class max_ordered_monoid_add = ordered_ab_semigroup + ab_semigroup_add + monoid_add + 
  fixes max0 :: "'a \<Rightarrow> 'a"
  assumes max0_id_pos: "x \<succeq> 0 \<Longrightarrow> max0 x = x"
  and max0_pos: " max0 x \<succeq> 0"
  and max0_mono: "x \<succeq> y \<Longrightarrow> max0 x \<succeq> max0 y"
  and max0_x: "max0 x \<succeq> x"

class max_ordered_ab_semigroup = ordered_ab_semigroup + monoid_add + ord +
  assumes max_ge_x[intro]: "max x y \<succeq> x" 
      and max_ge_y[intro]: "max x y \<succeq> y"

class max_ordered_semiring_1 = max_ordered_monoid_add + ordered_semiring_1

text {*
   We do not use a class to define order-pairs of a strict and a weak-order 
   since often we
   have parametric strict orders, e.g. on rational numbers there are several orders 
   $>$ where $x > y = x \geq y + \delta$ for some parameter $\delta$
*}
locale order_pair = 
  fixes gt :: "'a :: {non_strict_order,zero} \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<succ>" 50)
  and default :: "'a"
  assumes compat[trans]: "\<lbrakk>x \<succeq> y; y \<succ> z\<rbrakk> \<Longrightarrow> x \<succ> z"
  and compat2[trans]: "\<lbrakk>x \<succ> y; y \<succeq> z\<rbrakk> \<Longrightarrow> x \<succ> z"
  and gt_trans[trans]: "\<lbrakk>x \<succ> y; y \<succ> z\<rbrakk> \<Longrightarrow> x \<succ> z"
  and default_ge_zero: "default \<succeq> 0"


locale one_mono_ordered_semiring_1 = order_pair gt 
  for gt :: "'a :: ordered_semiring_1 \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<succ>" 50) + 
  assumes plus_gt_left_mono: "x \<succ> y \<Longrightarrow> x + z \<succ> y + z"
  and default_gt_zero: "default \<succ> 0"

locale SN_one_mono_ordered_semiring_1 = one_mono_ordered_semiring_1 + order_pair + 
  assumes SN: "SN {(x,y) . y \<succeq> 0 \<and> x \<succ> y}"


locale SN_strict_mono_ordered_semiring_1 = SN_one_mono_ordered_semiring_1 +
  fixes mono :: "'a :: ordered_semiring_1 \<Rightarrow> bool"
  assumes mono: "\<lbrakk>mono x; y \<succ> z; x \<succeq> 0\<rbrakk> \<Longrightarrow> x * y \<succ> x * z" 

locale both_mono_ordered_semiring_1 = order_pair gt 
  for gt :: "'a :: ordered_semiring_1 \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<succ>" 50) +
  fixes arc_pos :: "'a \<Rightarrow> bool" 
  assumes plus_gt_both_mono: "\<lbrakk>x \<succ> y; z \<succ> u\<rbrakk> \<Longrightarrow> x + z \<succ> y + u"
  and times_gt_left_mono: "x \<succ> y \<Longrightarrow> x * z \<succ> y * z" 
  and times_gt_right_mono: "y \<succ> z \<Longrightarrow> x * y \<succ> x * z" 
  and zero_leastI: "x \<succ> 0" 
  and zero_leastII: "0 \<succ> x \<Longrightarrow> x = 0" 
  and zero_leastIII: "(x :: 'a) \<succeq> 0"
  and arc_pos_one: "arc_pos (1 :: 'a)"
  and arc_pos_default: "arc_pos default"
  and arc_pos_zero: "\<not> arc_pos 0"
  and arc_pos_plus: "arc_pos x \<Longrightarrow> arc_pos (x + y)"
  and arc_pos_mult: "\<lbrakk>arc_pos x; arc_pos y\<rbrakk> \<Longrightarrow> arc_pos (x * y)"
  and not_all_ge: "\<And> c d. arc_pos d \<Longrightarrow> \<exists> e. ge e 0 \<and> arc_pos e \<and> \<not> (ge c (d * e))"


locale SN_both_mono_ordered_semiring_1 = both_mono_ordered_semiring_1 +
  assumes SN: "SN {(x,y) . arc_pos y \<and> x \<succ> y}"

locale weak_SN_strict_mono_ordered_semiring_1 = 
  fixes weak_gt :: "'a :: ordered_semiring_1 \<Rightarrow> 'a \<Rightarrow> bool"
   and  default :: "'a"
   and  mono :: "'a \<Rightarrow> bool"
  assumes weak_gt_mono: "\<forall> x y. (x,y) \<in> set xys \<longrightarrow> weak_gt x y \<Longrightarrow> \<exists> gt. SN_strict_mono_ordered_semiring_1  default gt mono \<and> (\<forall> x y. (x,y) \<in> set xys \<longrightarrow> gt x y)"

locale weak_SN_both_mono_ordered_semiring_1 = 
  fixes weak_gt :: "'a :: ordered_semiring_1 \<Rightarrow> 'a \<Rightarrow> bool"
   and  default :: "'a"
   and  arc_pos :: "'a \<Rightarrow> bool"
  assumes weak_gt_both_mono: "\<forall> x y. (x,y) \<in> set xys \<longrightarrow> weak_gt x y \<Longrightarrow> \<exists> gt. SN_both_mono_ordered_semiring_1 default gt arc_pos \<and> (\<forall> x y. (x,y) \<in> set xys \<longrightarrow> gt x y)"

class poly_carrier = max_ordered_semiring_1 + comm_semiring_1 (* max_ordered can be replaced by ordered,
  max is only added for Scala export *)

locale poly_order_carrier = SN_one_mono_ordered_semiring_1 default gt 
  for default :: "'a :: poly_carrier" and gt (infix "\<succ>" 50) +
  fixes power_mono :: "bool"
  and   discrete :: "bool"
  assumes times_gt_mono: "\<lbrakk>y \<succ> z; x \<succeq> 1\<rbrakk> \<Longrightarrow> y * x \<succ> z * x"
  and gt_imp_ge: "x \<succ> y \<Longrightarrow> x \<succeq> y"
  and power_mono: "power_mono \<Longrightarrow> x \<succ> y \<Longrightarrow> y \<succeq> 0 \<Longrightarrow> n \<ge> 1 \<Longrightarrow> x ^ n \<succ> y ^ n"
  and discrete: "discrete \<Longrightarrow> x \<succeq> y \<Longrightarrow> \<exists> k. x = ((op + 1)^^k) y"

class large_ordered_semiring_1 = comm_semiring_1 + ordered_semiring_1 +
  assumes ex_large_of_nat: "\<exists> x. of_nat x \<succeq> y"

class bin_max_ordered_semiring_1 = large_ordered_semiring_1 + max_ordered_ab_semigroup + max_ordered_semiring_1

context ordered_semiring_1
begin
lemma pow_mono: assumes ab: "a \<succeq> b" and b: "b \<succeq> 0"
  shows "a ^ n \<succeq> b ^ n \<and> b ^ n \<succeq> 0"
proof (induct n)
  case 0
  show ?case by (auto simp: ge_refl one_ge_zero)
next
  case (Suc n)
  hence abn: "a ^ n \<succeq> b ^ n" and bn: "b ^ n \<succeq> 0" by auto
  have bsn: "b ^ Suc n \<succeq> 0" unfolding power_Suc
    using times_left_mono[OF bn b] by auto
  have "a ^ Suc n = a * a ^ n" unfolding power_Suc by simp
  also have "... \<succeq> b * a ^ n"
    by (rule times_left_mono[OF ge_trans[OF abn bn] ab])
  also have "... \<succeq> b * b ^ n"
    by (rule times_right_mono[OF b abn])
  finally show ?case using bsn unfolding power_Suc by simp
qed

lemma pow_ge_zero[intro]: assumes a: "a \<succeq> (0 :: 'a)"
  shows "a ^ n \<succeq> 0"
proof (induct n)
  case 0
  from one_ge_zero show ?case by simp
next
  case (Suc n)
  show ?case using times_left_mono[OF Suc a] by simp
qed
end

lemma of_nat_ge_zero[intro,simp]: "of_nat n \<succeq> (0 :: 'a :: ordered_semiring_1)"
proof (induct n)
  case 0
  show ?case by (simp add: ge_refl)
next
  case (Suc n)
  from plus_right_mono[OF Suc, of 1] have "of_nat (Suc n) \<succeq> (1 :: 'a)" by simp
  also have "... \<succeq> 0" using one_ge_zero .
  finally show ?case .
qed

lemma mult_ge_zero[intro]: "(a :: 'a :: ordered_semiring_1) \<succeq> 0 \<Longrightarrow> b \<succeq> 0 \<Longrightarrow> a * b \<succeq> 0"
  using times_left_mono[of b a 0] by auto

lemma pow_mono_one: assumes a: "a \<succeq> (1 :: 'a :: ordered_semiring_1)"
  shows "a ^ n \<succeq> 1"
proof (induct n)
  case (Suc n)
  show ?case unfolding power_Suc
    using ge_trans[OF times_right_mono[OF ge_trans[OF a one_ge_zero] Suc], of 1]
    a
    by (auto simp: field_simps)
qed (auto simp: ge_refl)

lemma pow_mono_exp: assumes a: "a \<succeq> (1 :: 'a :: ordered_semiring_1)"
  shows "n \<ge> m \<Longrightarrow> a ^ n \<succeq> a ^ m"
proof (induct m arbitrary: n)
  case 0
  show ?case using pow_mono_one[OF a] by auto
next
  case (Suc m nn)
  then obtain n where nn: "nn = Suc n" by (cases nn, auto)
  note Suc = Suc[unfolded nn]
  hence rec: "a ^ n \<succeq> a ^ m" by auto
  show ?case unfolding nn power_Suc
    by (rule times_right_mono[OF ge_trans[OF a one_ge_zero] rec])
qed

lemma mult_ge_one[intro]: assumes a: "(a :: 'a :: ordered_semiring_1) \<succeq> 1"
  and b: "b \<succeq> 1"
  shows "a * b \<succeq> 1"
proof -
  from ge_trans[OF b one_ge_zero] have b0: "b \<succeq> 0" .
  from times_left_mono[OF b0 a] have "a * b \<succeq> b" by simp
  from ge_trans[OF this b] show ?thesis .
qed

lemma listsum_ge_mono: fixes as :: "('a :: ordered_semiring_0) list"
  assumes "length as = length bs"
  and "\<And> i. i < length bs \<Longrightarrow> as ! i \<succeq> bs ! i"
  shows "listsum as \<succeq> listsum bs"
  using assms 
proof (induct as arbitrary: bs)
  case (Nil bs)
  from Nil(1) show ?case by (simp add: ge_refl)
next
  case (Cons a as bbs)
  from Cons(2) obtain b bs where bbs: "bbs = b # bs" and len: "length as = length bs" by (cases bbs, auto)
  note ge = Cons(3)[unfolded bbs]
  {
    fix i
    assume "i < length bs"
    hence "Suc i < length (b # bs)" by simp
    from ge[OF this] have "as ! i \<succeq> bs ! i" by simp
  }
  from Cons(1)[OF len this] have IH: "listsum as \<succeq> listsum bs" .
  from ge[of 0] have ab: "a \<succeq> b" by simp
  from ge_trans[OF plus_left_mono[OF ab] plus_right_mono[OF IH]]
  show ?case unfolding bbs  by simp
qed

lemma listsum_ge_0_nth: fixes xs :: "('a :: ordered_semiring_0)list"
  assumes ge: "\<And> i. i < length xs \<Longrightarrow> xs ! i \<succeq> 0"
  shows "listsum xs \<succeq> 0"
proof -
  let ?l = "replicate  (length xs) (0 :: 'a)"
  have "length xs = length ?l" by simp
  from listsum_ge_mono[OF this] ge have "listsum xs \<succeq> listsum ?l" by simp
  also have "... = 0" using listsum_0[of ?l] by auto
  finally show ?thesis .
qed

lemma listsum_ge_0: fixes xs :: "('a :: ordered_semiring_0)list"
  assumes ge: "\<And> x. x \<in> set xs \<Longrightarrow> x \<succeq> 0"
  shows "listsum xs \<succeq> 0"
  by (rule listsum_ge_0_nth, insert ge[unfolded set_conv_nth], auto)

lemma foldr_max: "a \<in> set as \<Longrightarrow> foldr max as b \<succeq> (a :: 'a :: max_ordered_ab_semigroup)"
proof (induct as arbitrary: b)
  case Nil thus ?case by simp
next
  case (Cons c as)
  show ?case
  proof (cases "a = c")
    case True
    show ?thesis unfolding True by auto
  next
    case False
    with Cons have "foldr max as b \<succeq> a" by auto
    from ge_trans[OF _ this] show ?thesis by auto
  qed
qed

lemma of_nat_mono[intro]: assumes "n \<ge> m" shows "(of_nat n :: 'a :: ordered_semiring_1)  \<succeq> of_nat m"
proof -
  let ?n = "of_nat :: nat \<Rightarrow> 'a"
  from assms
  show ?thesis
  proof (induct m arbitrary: n)
    case 0
    show ?case by auto
  next
    case (Suc m nn)
    then obtain n where nn: "nn = Suc n" by (cases nn, auto)
    note Suc = Suc[unfolded nn]
    hence rec: "?n n \<succeq> ?n m" by simp
    show ?case unfolding nn of_nat_Suc
      by (rule plus_right_mono[OF rec])
  qed
qed


end
