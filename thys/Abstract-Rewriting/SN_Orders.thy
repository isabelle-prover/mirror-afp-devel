(*  Title:       Executable multivariate polynomials
    Author:      Christian Sternagel <christian.sternagel@uibk.ac.at>
                 René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann
    License:     LGPL
*)

(*
Copyright 2010 Christian Sternagel, René Thiemann

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

header {* SN\_Orders *}

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
  fixes ge :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<ge>" 21)
  assumes ge_refl: "x \<ge> (x :: 'a)"
  and ge_trans[trans]: "\<lbrakk>x \<ge> y; (y :: 'a) \<ge> z\<rbrakk> \<Longrightarrow> x \<ge> z"

class ordered_ab_semigroup = non_strict_order + ab_semigroup_add +
  assumes plus_left_mono: "\<lbrakk>ge (x :: 'a) y\<rbrakk> \<Longrightarrow> ge (plus x z)  (plus y z)"

lemma plus_right_mono: "ge y (z :: 'a :: ordered_ab_semigroup) \<Longrightarrow> ge (x + y) (x + z)"
  by (simp add: add_commute[of x], rule plus_left_mono, auto)

class ordered_semiring_0 = ordered_ab_semigroup + semiring_0 +
 assumes times_left_mono: "\<lbrakk>ge z 0; ge x y\<rbrakk> \<Longrightarrow> ge (x * z) (y * z)"
     and times_right_mono: "\<lbrakk>ge x 0; ge y z\<rbrakk> \<Longrightarrow> ge (x * y) (x * z)"

class ordered_semiring_1 = ordered_semiring_0 + semiring_1 +
  assumes one_ge_zero: "ge 1 0"

class max_ordered_monoid_add = ordered_ab_semigroup + ab_semigroup_add + monoid_add + 
  fixes max0 :: "'a \<Rightarrow> 'a"
  assumes max0_id_pos: "ge x 0 \<Longrightarrow> max0 x = x"
  and max0_pos: " ge (max0 x) 0"
  and max0_mono: "ge x y \<Longrightarrow> ge (max0 x) (max0 y)"
  and max0_x: "ge (max0 x) x"


text {*
   We do not use a class to define order-pairs of a strict and a weak-order 
   since often we
   have parametric strict orders, e.g. on rational numbers there are several orders 
   $>$ where $x > y = x \geq y + \delta$ for some parameter $\delta$
*}
locale order_pair = 
  fixes gt :: "'a :: {non_strict_order,zero} \<Rightarrow> 'a \<Rightarrow> bool" 
  and default :: "'a"
  assumes compat[trans]: "\<lbrakk>x \<ge> y; gt y z\<rbrakk> \<Longrightarrow> gt x z"
  and compat2[trans]: "\<lbrakk>gt x y; y \<ge> z\<rbrakk> \<Longrightarrow> gt x z"
  and default_ge_zero: "default \<ge> 0"


locale one_mono_ordered_semiring_1 = order_pair gt 
  for gt :: "'a :: ordered_semiring_1 \<Rightarrow> 'a \<Rightarrow> bool" + 
  assumes plus_gt_left_mono: "gt x y \<Longrightarrow> gt (x + z) (y + z)"
  and default_gt_zero: "gt default 0"

locale SN_one_mono_ordered_semiring_1 = one_mono_ordered_semiring_1 + order_pair + 
  assumes SN: "SN {(x,y) . ((y :: 'a :: ordered_semiring_1) \<ge> 0) \<and> (gt x y)}"


locale SN_strict_mono_ordered_semiring_1 = SN_one_mono_ordered_semiring_1 +
  fixes mono :: "'a :: ordered_semiring_1 \<Rightarrow> bool"
  assumes mono: "\<lbrakk>mono x; gt y z; x \<ge> 0\<rbrakk> \<Longrightarrow> gt (x * y) (x * z)" 

locale both_mono_ordered_semiring_1 = order_pair gt 
  for gt :: "'a :: ordered_semiring_1 \<Rightarrow> 'a \<Rightarrow> bool" + 
  assumes plus_gt_both_mono: "\<lbrakk>gt x y; gt z u\<rbrakk> \<Longrightarrow> gt (x + z) (y + u)"
  and times_gt_left_mono: "gt x y \<Longrightarrow> gt (x * z) (y * z)" 
  and zero_leastI: "gt x 0" 
  and zero_leastII: "gt 0 x \<Longrightarrow> x = 0" 
  and zero_leastIII: "(x :: 'a) \<ge> 0"

locale SN_both_mono_ordered_semiring_1 = both_mono_ordered_semiring_1 +
  fixes arc_pos :: "'a :: ordered_semiring_1 \<Rightarrow> bool"
  assumes SN: "SN {(x,y) . arc_pos y \<and> gt x y}"
  and arc_pos_plus: "arc_pos x \<Longrightarrow> arc_pos (x + y)"
  and arc_pos_mult: "\<lbrakk>arc_pos x; arc_pos y\<rbrakk> \<Longrightarrow> arc_pos (x * y)"
  and arc_pos_default: "arc_pos default"

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

class poly_carrier = ordered_semiring_1 + comm_semiring_1

locale poly_order_carrier = SN_one_mono_ordered_semiring_1 default gt 
  for default :: "'a :: poly_carrier" and gt +
  fixes power_mono :: "bool"
  and   discrete :: "bool"
  assumes times_gt_mono: "\<lbrakk>gt y z; ge x 1\<rbrakk> \<Longrightarrow> gt (y * x) (z * x)"
  and gt_imp_ge: "gt x y \<Longrightarrow> ge x y"
  and power_mono: "power_mono \<Longrightarrow> gt x y \<Longrightarrow> ge y 0 \<Longrightarrow> n \<ge> 1 \<Longrightarrow> gt (x ^ n) (y ^ n)"
  and discrete: "discrete \<Longrightarrow> ge x y \<Longrightarrow> \<exists> k. x = ((op + 1)^^k) y"

end
