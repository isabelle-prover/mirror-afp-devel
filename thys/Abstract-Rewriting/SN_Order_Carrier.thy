(*  Title:       Executable multivariate polynomials
    Author:      Christian Sternagel <christian.sternagel@uibk.ac.at>
                 Rene Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and Rene Thiemann
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

header {* Carriers of Strongly Normalizing Orders *}

theory SN_Order_Carrier
imports SN_Orders Rat
begin

text {*
  This theory shows that standard semirings can be used 
  in combination with polynomials, e.g. the naturals, integers,
  rationals.
  
  It also contains the arctic integers and rationals where
  0 is -infty, 1 is zero, + is max and * is plus.
*}

subsection {* The standard semiring over the naturals *}

instantiation nat :: max_ordered_semiring_1
begin
fun ge_nat :: "nat \<Rightarrow> nat \<Rightarrow> bool" where "ge_nat x y = (y \<le> x)"
fun max0_nat :: "nat \<Rightarrow> nat" where "max0_nat x = x"
instance by (intro_classes, auto)
end

definition nat_mono :: "nat \<Rightarrow> bool" where "nat_mono x \<equiv> x \<noteq> 0"

interpretation nat_SN: SN_strict_mono_ordered_semiring_1 1 "op > :: nat \<Rightarrow> nat \<Rightarrow> bool" nat_mono
proof (unfold_locales)
  have "SN {(x,y). (y :: nat) < x}" (is "SN ?gt")
  proof (rule ccontr, unfold SN_defs, clarify)
    fix x f
    assume steps: "\<forall> i. (f i, f (Suc i)) \<in> ?gt"
    have "\<forall> i. f i + i \<le> f 0"
    proof 
      fix i
      show "f i + i \<le> f 0"
      proof (induct i, simp)
        case (Suc i)
        with spec[OF steps, of i] show ?case by auto
      qed
    qed
    hence "f (Suc (f 0)) + Suc (f 0) \<le> f 0" by blast
    thus False by auto
  qed
  thus "SN {(x,y). (y :: nat) \<succeq> 0 \<and> y < x}" by auto
qed (auto simp: nat_mono_def)

instantiation nat :: poly_carrier 
begin 
instance ..
end

interpretation nat_poly: poly_order_carrier 1 "op > :: nat \<Rightarrow> nat \<Rightarrow> bool" True discrete
proof (unfold_locales)
  fix x y :: nat
  assume ge: "x \<succeq> y"
  obtain k where k: "x - y = k" by auto
  show "\<exists> k. x = (op + 1 ^^ k) y" 
  proof (rule exI[of _ k])
    from ge k have "x = k + y" by simp
    also have "\<dots> = (op + 1 ^^ k) y" 
      by (induct k, auto)
    finally show "x = (op + 1 ^^ k) y" .
  qed
qed (auto simp: field_simps power_strict_mono)
      


subsection {* The standard semiring over the integers *}

definition int_mono :: "int \<Rightarrow> bool" where "int_mono x \<equiv> x \<ge> 1"


instantiation int :: max_ordered_semiring_1
begin
fun ge_int :: "int \<Rightarrow> int \<Rightarrow> bool" where "ge_int x y = (y \<le> x)"
fun max0_int :: "int \<Rightarrow> int" where "max0_int x = max 0 x"
instance by (intro_classes, auto simp: mult_right_mono mult_left_mono)
end

instantiation int :: poly_carrier
begin
instance ..
end

interpretation int_SN: SN_strict_mono_ordered_semiring_1 1 "op > :: int \<Rightarrow> int \<Rightarrow> bool" int_mono
proof (unfold_locales)
  show "SN {(x,y). y \<succeq> 0 \<and> (y :: int) < x}" (is "SN ?gt")
  proof (rule ccontr, unfold SN_defs, clarify)
    fix x f
    assume steps: "\<forall> i. (f i, f (Suc i)) \<in> ?gt"
    have main: "\<forall> i. f i + int i \<le> f 0"
    proof 
      fix i
      show "f i + int i \<le> f 0"
      proof (induct i)
        case (Suc i)
        with spec[OF steps, of i] show ?case by auto
      qed simp
    qed
    have contra: "\<forall> i. int (Suc i) \<le> f 0" 
    proof
      fix i
      from spec[OF main, of "Suc i"] spec[OF steps, of i] 
      show "int (Suc i) \<le> f 0" by auto
    qed
    show False 
    proof (cases "0 \<le> f 0")
      case False
      with spec[OF contra, of 0] show False by auto
    next
      case True
      obtain n where "f 0 = int n" using zero_le_imp_eq_int[OF True] ..
      with spec[OF contra, of n] show False by auto
    qed
  qed
qed (auto simp: mult_strict_left_mono int_mono_def)

instantiation int :: bin_max_ordered_semiring_1
begin
instance 
proof 
  fix y :: int
  show "\<exists> x. of_nat x \<succeq> y"
    by (rule exI[of _ "nat y"], simp) 
qed auto
end



interpretation int_poly: poly_order_carrier 1 "op > :: int \<Rightarrow> int \<Rightarrow> bool" True discrete
proof (unfold_locales)
  fix x y :: int
  assume ge: "x \<succeq> y"
  then obtain k where k: "x - y = k" and kp: "0 \<le> k" by auto
  then obtain nk where nk: "nk = nat k" and k: "x - y = int nk" by auto
  show "\<exists> k. x = (op + 1 ^^ k) y"
  proof (rule exI[of _ nk])
    from k have "x = int nk + y" by simp
    also have "\<dots> = (op + 1 ^^ nk) y"
      by (induct nk, auto)
    finally show "x = (op + 1 ^^ nk) y" .
  qed
qed (auto simp: field_simps power_strict_mono)



subsection {* The standard semiring over the rationals using delta-orderings *}

definition rat_gt :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> bool" where 
  "rat_gt \<delta> \<equiv> (\<lambda> x y. x - y \<ge> \<delta>)"


lemma rat_gt_SN: assumes dpos: "\<delta> > 0" shows "SN {(x,y). 0 \<le> y \<and> rat_gt \<delta> x y}"
  proof (rule ccontr, unfold SN_defs, clarify)
  fix x f
  let ?R = "{(x,y). 0 \<le> y \<and> rat_gt \<delta> x y}"
  let ?Rd = "{(x,y). (0 :: rat) \<le> y \<and> x - y \<ge> \<delta>}" 
  assume Rsteps: "\<forall> i. (f i, f (Suc i)) \<in> ?R"
  from Rsteps have steps:  "\<forall> i. (f i, f (Suc i)) \<in> ?Rd" unfolding rat_gt_def by auto  
  from spec[OF steps, of 0] dpos have fz_0: "f 0 > 0" by auto
  {
    fix n :: nat
    have "f n \<le> f 0 - (of_nat n) * \<delta>"
    proof (induct n, simp)
      case (Suc n)
      with spec[OF steps, of n] show ?case by (auto simp: field_simps)
    qed
  } note main1 = this
  { 
    fix n :: nat
    have "f 0 \<ge> of_nat (Suc n) * \<delta>" using main1[of "Suc n"] spec[OF steps, of "n"] by auto
  } note main2 = this
  obtain numeratord denomd where d_id: "\<delta> = Fract numeratord denomd" by (cases \<delta>, auto)
  with dpos have denomd: "denomd \<noteq> 0" by (cases "denomd = 0", simp_all add: rat_number_collapse)
  obtain numerator0 denom0 where fz: "f 0 = Fract numerator0 denom0" by (cases "f 0", auto)
  with fz_0 have denom0: "denom0 \<noteq> 0" by (cases "denom0 = 0", simp_all add: rat_number_collapse)
  from fz d_id main2 have contra: "\<And> n. Fract numerator0 denom0 \<ge> Fract (int (Suc n) * numeratord) denomd" by (simp add: of_nat_rat)
  from denom0 have square: "denom0 * denom0 > 0" by  (cases "denom0 > 0", simp add: mult_pos_pos, simp add: mult_neg_neg)
  from dpos d_id denomd have pos: "numeratord * denomd  > 0" 
    by (auto simp: sgn_times mult_less_0_iff zero_less_mult_iff zero_less_Fract_iff, cases "numeratord = 0", auto simp: rat_number_collapse, cases "denomd < 0", simp_all,
      simp only: minus_rat_cancel[symmetric, of numeratord denomd],
      simp only: zero_less_Fract_iff[of "- denomd" "- numeratord"])
  let ?p = "numeratord * denom0 * denomd * denom0"
  have id: "?p = (denom0 * denom0) * (numeratord * denomd)" by auto
  have posp: "?p > 0" using mult_pos_pos[OF square pos] by (simp add: id)
  have "\<exists> p . ?p = p + 1 \<and> p \<ge> 0"
    by (rule exI[of _ "?p - 1"], simp add: posp)
  from this obtain p where p: "?p = p + 1" and ppos: "0 \<le> p" by auto
  have id2: "\<And> n. n * numeratord * denom0 * (denomd * denom0) = n * ?p" by auto
  from contra square denomd denom0 show False 
  proof (simp add: p id2, simp add: distrib_left distrib_right)
    let ?r = "numerator0 * denomd * (denomd * denom0)"
    let ?rr = "?r - p - 1"
    assume ass: "\<And> n. p + int n * p + (1 + int n) \<le> ?r"
    have nppos: "\<And> n. 0 \<le> int n * p" by  (rule mult_nonneg_nonneg[OF _ ppos], simp)
    {
      fix n
      have "int n = 0 + int n" by auto
      also have "\<dots> \<le> int n * p + int n" using nppos[of n] by auto
      finally have "p + 1 + int n \<le> p + 1 + int n * p + int n" by auto
      with ass[of n] have "int n \<le> ?rr" by auto
    } note contra2 = this
    show False 
    proof (cases "0 \<le> ?rr")
      case False
      with contra2[of 0] show False by auto
    next
      case True
      from zero_le_imp_eq_int[OF True] obtain n where id2: "?rr = int n" by auto
      from contra2[of "Suc n"] show False by (simp only: id2)
    qed
  qed
qed

definition rat_mono :: "rat \<Rightarrow> bool" where "rat_mono x \<equiv> x \<ge> 1"



instantiation rat :: max_ordered_semiring_1
begin
fun ge_rat :: "rat \<Rightarrow> rat \<Rightarrow> bool" where "ge_rat x y = (y \<le> x)"
fun max0_rat :: "rat \<Rightarrow> rat" where "max0_rat x = max 0 x"
instance by (intro_classes, auto simp: mult_right_mono mult_left_mono)
end

instantiation rat :: bin_max_ordered_semiring_1
begin
instance 
proof 
  fix y :: rat
  from ex_le_of_nat[of y]
  show "\<exists> x. of_nat x \<succeq> y" by simp
qed auto
end


instantiation rat :: poly_carrier
begin
instance ..
end

lemma rat_interpretation: assumes dpos: "\<delta> > 0" and default: "\<delta> \<le> def"
  shows "SN_strict_mono_ordered_semiring_1 def (rat_gt \<delta>) rat_mono"
proof -
  from dpos default have defz: "0 \<le> def" by auto
  show ?thesis
  proof (unfold_locales)
    show "SN {(x,y). y \<succeq> 0 \<and> rat_gt \<delta> x y}"
      by simp (rule rat_gt_SN[OF dpos])
  next
    fix x y z :: rat
    assume "rat_mono x" and yz: "rat_gt \<delta> y z"
    hence x: "1 \<le> x" unfolding rat_mono_def by simp
    have "\<exists> d > 0. rat_gt \<delta> = (\<lambda> x y. d \<le> x - y)" 
      by (rule exI[of _ \<delta>], auto simp: dpos rat_gt_def)
    from this obtain d where d: "0 < d" and rat: "rat_gt \<delta> = (\<lambda> x y. d \<le> x - y)" by auto
    from yz have yzd: "d \<le> y - z" by (simp add: rat)
    show "rat_gt \<delta> (x * y) (x * z)"
    proof (simp only: rat)
      let ?p = "(x - 1) * (y - z)"
      from x have x1: "0 \<le> x - 1" by auto
      from yzd d have yz0: "0 \<le> y - z" by auto
      have "0 \<le> ?p" 
        by (rule mult_nonneg_nonneg[OF x1 yz0])
      have "x * y - x * z = x * (y - z)" using right_diff_distrib[of x y z] by auto
      also have "\<dots> = ((x - 1) + 1) * (y - z)" by auto
      also have "\<dots> = ?p + 1 * ( y - z)" by (rule ring_distribs(2))
      also have "\<dots> = ?p + (y - z)" by simp
      also have "\<dots> \<succeq> (0 + d)" using yzd `0 \<le> ?p` by auto
      finally 
      show "d \<le> x * y - x * z" by auto
    qed
  next
    fix x y z
    assume "rat_gt \<delta> x y" "rat_gt \<delta> y z"
    thus "rat_gt \<delta> x z" unfolding rat_gt_def using dpos by auto
  qed (auto simp: rat_gt_def dpos default defz)
qed

lemma rat_poly: assumes dpos: "\<delta> > 0" and default: "\<delta> \<le> def"
  shows "poly_order_carrier def (rat_gt \<delta>) (1 \<le> \<delta>) False"
proof -
  from rat_interpretation[OF dpos default] 
  interpret SN_strict_mono_ordered_semiring_1 "def" "rat_gt \<delta>" rat_mono .
  interpret poly_order_carrier "def" "rat_gt \<delta>" False False
  proof(unfold_locales)
    fix y z x :: rat
    assume gt: "rat_gt \<delta> y z" and ge: "x \<succeq> 1"
    from ge have ge: "x \<succeq> 0" and m: "rat_mono x" unfolding rat_mono_def by auto
    show "rat_gt \<delta> (y * x) (z * x)"
      using mono[OF m gt ge] by (auto simp: field_simps)
  next
    fix x y :: rat
    assume gt: "rat_gt \<delta> x y"
    thus "x \<succeq> y" using dpos unfolding rat_gt_def by auto
  next
    fix x y :: rat and n :: nat
    assume False thus "rat_gt \<delta> (x ^ n) (y ^ n)" ..
  next
    fix x y :: rat
    assume False
    thus "\<exists> k. x = (op + 1 ^^ k) y" by simp
  qed
  show ?thesis
  proof(unfold_locales)
    fix x y :: rat and n :: nat
    assume one: "1 \<le> \<delta>" and gt: "rat_gt \<delta> x y" and y: "y \<succeq> 0" and n: "1 \<le> n"
    then obtain p where n: "n = Suc p" and x: "x \<succeq> 1" and y2: "0 \<le> y" and xy: "x \<succeq> y" by (cases n, auto simp: rat_gt_def)
    show "rat_gt \<delta> (x ^ n) (y ^ n)" 
    proof (simp only: n, induct p, simp add: gt)
      case (Suc p)
      from times_gt_mono[OF this x]
      have one: "rat_gt \<delta> (x ^ Suc (Suc p)) (x * y ^ Suc p)" by (auto simp: field_simps)
      also have "\<dots> \<succeq> y * y ^ Suc p" 
        by (rule times_left_mono[OF _ xy], auto simp: zero_le_power[OF y2, of "Suc p", simplified])
      finally show ?case by auto
    qed
  next
    fix x y :: rat
    assume False
    thus "\<exists> k. x = (op + 1 ^^ k) y" by simp
  qed (rule times_gt_mono, simp, simp, 
      rule gt_imp_ge, simp)
qed


lemma rat_minimal_delta: assumes "\<And> x  y :: rat. (x,y) \<in> set xys \<Longrightarrow> x > y"
  shows "\<exists> \<delta> > 0. \<forall> x y. (x,y) \<in> set xys \<longrightarrow> rat_gt \<delta> x y"
using assms 
proof (induct xys)
  case Nil
  show ?case by (rule exI[of _ 1], auto)
next
  case (Cons xy xys)
  show ?case
  proof (cases xy)
    case (Pair x y)
    with Cons have "x > y" by auto
    then obtain d1 where "d1 = x - y" and d1pos: "d1 > 0" and "d1 \<le> x - y" by auto
    hence xy: "rat_gt d1 x y" unfolding rat_gt_def by auto
    from Cons obtain d2 where d2pos: "d2 > 0" and xys: "\<forall> x y. (x, y) \<in> set xys \<longrightarrow> rat_gt d2 x y" by auto
    obtain d where d: "d = min d1 d2" by auto
    with d1pos d2pos xy have dpos: "d > 0" and "rat_gt d x y" unfolding rat_gt_def by auto
    with xys d Pair have "\<forall> x y. (x,y) \<in> set (xy # xys) \<longrightarrow> rat_gt d x y" unfolding rat_gt_def by force
    with dpos show ?thesis by auto 
  qed
qed

interpretation weak_rat_SN: weak_SN_strict_mono_ordered_semiring_1 "op >" 1 rat_mono
proof
  fix xysp :: "(rat \<times> rat) list"
  assume orient: "\<forall> x y. (x,y) \<in> set xysp \<longrightarrow> x > y" 
  obtain xys where xsy: "xys = (1,0) # xysp" by auto
  with orient have "\<And> x y. (x,y) \<in> set xys \<Longrightarrow> x > y" by auto
  with rat_minimal_delta have "\<exists> \<delta> > 0. \<forall> x y. (x,y) \<in> set xys \<longrightarrow> rat_gt \<delta> x y" by auto
  then obtain \<delta> where dpos: "\<delta> > 0" and orient: "\<And> x y. (x,y) \<in> set xys \<Longrightarrow> rat_gt \<delta> x y" by auto
  from orient have orient1: "\<forall> x y. (x,y) \<in> set xysp \<longrightarrow> rat_gt \<delta> x y" and orient2: "rat_gt \<delta> 1 0" unfolding xsy by auto
  from orient2 have oned: "\<delta> \<le> 1" unfolding rat_gt_def by auto
  show " \<exists>gt. SN_strict_mono_ordered_semiring_1 1 gt rat_mono \<and> (\<forall>x y. (x, y) \<in> set xysp \<longrightarrow> gt x y)" 
    by (intro exI conjI, rule rat_interpretation[OF dpos oned], rule orient1)
qed


subsection {* The arctic semiring over the integers *}
text {* plus is interpreted as max, times is interpreted as plus, 0 is -infinity, 1 is 0 *}

datatype arctic = MinInfty | Num_arc int


instantiation arctic :: max_ordered_semiring_1
begin
fun plus_arctic :: "arctic \<Rightarrow> arctic \<Rightarrow> arctic"
where "plus_arctic MinInfty y = y"
   |  "plus_arctic x MinInfty = x"
   |  "plus_arctic (Num_arc x) (Num_arc y) = (Num_arc (max x y))"
fun times_arctic :: "arctic \<Rightarrow> arctic \<Rightarrow> arctic"
where "times_arctic MinInfty y = MinInfty"
   |  "times_arctic x MinInfty = MinInfty"
   |  "times_arctic (Num_arc x) (Num_arc y) = (Num_arc (x + y))"
fun ge_arctic :: "arctic \<Rightarrow> arctic \<Rightarrow> bool"
where "ge_arctic x MinInfty = True"
   |  "ge_arctic MinInfty (Num_arc _) = False"
   |  "ge_arctic (Num_arc x) (Num_arc y) = (y \<le> x)"
definition zero_arctic :: arctic
where "zero_arctic = MinInfty"
definition one_arctic :: arctic
where "one_arctic = Num_arc 0"
definition max0_arctic :: "arctic \<Rightarrow> arctic" where [simp]: "max0_arctic \<equiv> id"
instance
proof
  fix x y :: arctic
  show "x + y = y + x"
    by (cases x, cases y, auto, cases y, auto)
next
  fix x y z :: arctic
  show "(x + y) + z = x + (y + z)"
    by (cases x, auto, cases y, auto, cases z, auto)
next
  fix x y z :: arctic
  show "(x * y) * z = x * (y * z)"
    by (cases x, auto, cases y, auto, cases z, auto)
next
  fix x :: arctic
  show "x * 0 = 0"
    by (cases x, auto simp: zero_arctic_def)
next
  fix x y z :: arctic
  show "x * (y + z) = x * y + x * z"
    by (cases x, auto, cases y, auto, cases z, auto)
next
  fix x y z :: arctic
  show "(x + y) * z = x * z + y * z"
    by (cases x, auto, cases y, cases z, auto, cases z, auto)
next
  fix x y z :: arctic
  assume "x \<succeq> y" 
  thus "x + z \<succeq> y + z"
    by (cases x, cases y, cases z, auto, cases y, cases z, auto, cases z, auto)
next
  fix x y z :: arctic
  assume "x \<succeq> y" 
  thus "x * z \<succeq> y * z"
    by (cases x, cases y, cases z, auto, cases y, cases z, auto, cases z, auto)
next
  fix x y z :: arctic
  assume "y \<succeq> z"
  thus "x * y \<succeq> x * z"
    by (cases x, cases y, cases z, auto, cases y, cases z, auto, cases z, auto)
next
  fix x :: arctic
  show "x \<succeq> x" 
    by (cases x, auto)
next
  fix x y z :: arctic
  assume "x \<succeq> y" and "y \<succeq> z"
  thus "x \<succeq> z"
    by (cases x, cases y, auto, cases y, cases z, auto, cases z, auto)
next
  fix x :: arctic
  show "0 + x = x"
    by (simp add: zero_arctic_def)
next
  fix x :: arctic
  show "0 * x = 0"
    by (simp add: zero_arctic_def)
next
  fix x :: arctic
  show "1 * x = x"
    by (cases x, simp_all add: one_arctic_def)
next
  fix x :: arctic
  show "x * 1 = x"
    by (cases x, simp_all add: one_arctic_def)
next
  show "(0 :: arctic) \<noteq> 1"
    by (simp add: zero_arctic_def one_arctic_def)
next
  show "(1 :: arctic) \<succeq> 0"
    by (simp add: zero_arctic_def one_arctic_def)
next
  fix x :: arctic
  show "x \<succeq> 0" by (cases x, auto simp: zero_arctic_def)
next
  fix x :: arctic
  show "max0 x \<succeq> x" by (cases x, auto)
next
  fix x :: arctic
  show "x + 0 = x" by (cases x, auto simp: zero_arctic_def)
qed auto
end


text {* x > y is interpreted as y = -inf or (x,y != -inf and x > y on the integers) *}
fun gt_arctic :: "arctic \<Rightarrow> arctic \<Rightarrow> bool"
where "gt_arctic _ MinInfty = True"
   |  "gt_arctic MinInfty (Num_arc _) = False"
   |  "gt_arctic (Num_arc x) (Num_arc y) = (y < x)"


fun get_arctic_num :: "arctic \<Rightarrow> int"
where "get_arctic_num (Num_arc n) = n"

fun pos_arctic :: "arctic \<Rightarrow> bool"
where "pos_arctic MinInfty = False"
    | "pos_arctic (Num_arc n) = (0 <= n)"

interpretation arctic_SN: SN_both_mono_ordered_semiring_1 1 gt_arctic pos_arctic
proof 
  fix x y z :: arctic
  assume "x \<succeq> y" and "gt_arctic y z"
  thus "gt_arctic x z"
    by (cases z, simp, cases y, simp, cases x, auto)
next 
  fix x y z :: arctic
  assume "gt_arctic x y" and "y \<succeq> z"
  thus "gt_arctic x z"
    by (cases z, simp, cases y, simp, cases x, auto)
next
  fix x y z :: arctic
  assume "gt_arctic x y" and "gt_arctic y z"
  thus "gt_arctic x z"
    by (cases z, simp, cases y, simp, cases x, auto)
next
  fix x y z u
  assume "gt_arctic x y" and "gt_arctic z u"
  thus "gt_arctic (x + z) (y + u)"
    by (cases y, cases u, simp, cases z, auto, cases x, auto, cases u, auto, cases z, auto, cases x, auto, cases x, auto, cases z, auto, cases x, auto)
next
  fix x y z
  assume "gt_arctic x y"
  thus "gt_arctic (x * z) (y * z)"
    by (cases y, simp, cases z, simp, cases x, auto)
next
  fix x
  assume "gt_arctic 0 x"
  thus "x = 0"
    by (cases x, auto simp: zero_arctic_def)
next
  show "pos_arctic 1" unfolding one_arctic_def by simp
next
  fix x
  show "gt_arctic x 0" unfolding zero_arctic_def by simp
next
  fix x y
  assume "pos_arctic x" 
  thus "pos_arctic (x + y)" by (cases x, simp, cases y, auto)
next
  fix x y
  assume "pos_arctic x" and "pos_arctic y"
  thus "pos_arctic (x * y)" by (cases x, simp, cases y, auto)
next
  show "SN {(x,y). pos_arctic y \<and> gt_arctic x y}" (is "SN ?rel")
  proof - {
    fix x
    assume "\<exists> f . f 0 = x \<and> (\<forall> i. (f i, f (Suc i)) \<in> ?rel)"
    from this obtain f where "f 0 = x" and seq: "\<forall> i. (f i, f (Suc i)) \<in> ?rel" by auto
    from seq have steps: "\<forall> i. gt_arctic (f i) (f (Suc i)) \<and> pos_arctic (f (Suc i)) " by auto
    let ?g = "\<lambda> i. get_arctic_num (f i)"
    have "\<forall> i. ?g (Suc i) \<ge> 0 \<and> ?g i  > ?g (Suc i)"
    proof
      fix i
      from steps have i: "gt_arctic (f i) (f (Suc i)) \<and> pos_arctic (f (Suc i))" by auto
      from i obtain n where fi: "f i = Num_arc n" by (cases "f (Suc i)", simp, cases "f i", auto)
      from i obtain m where fsi: "f (Suc i) = Num_arc m" by (cases "f (Suc i)", auto)
      with i have gz: "0 \<le> m" by simp
      from i fi fsi have "n > m" by auto
      with fi fsi gz
      show "?g (Suc i) \<ge> 0 \<and> ?g i > ?g (Suc i)" by auto
    qed
    from this obtain g where "\<forall> i. g (Suc i) \<ge> 0 \<and> (op > :: int \<Rightarrow> int \<Rightarrow> bool) (g i) (g (Suc i))" by auto
    hence "\<exists> f. f 0 = g 0 \<and> (\<forall> i. (f i, f (Suc i)) \<in> {(x,y). y \<ge> 0 \<and> x > y})" by auto
    with int_SN.SN have False unfolding SN_defs by auto
  }
  thus ?thesis unfolding SN_defs by auto
  qed 
next
  show "(1 :: arctic) \<succeq> 0" unfolding zero_arctic_def by simp
next
  fix x :: arctic 
  show "x \<succeq> 0" unfolding zero_arctic_def by simp
next
    fix y z x :: arctic
  assume "gt_arctic y z"
  thus "gt_arctic (x * y) (x * z)"
    by (cases x, simp, cases z, simp, cases y, auto)
next
  show "\<not> pos_arctic 0" unfolding zero_arctic_def by simp
next
  fix c d
  assume "pos_arctic d" 
  then obtain n where d: "d = Num_arc n" and n: "0 \<le> n"
    by (cases d, auto)  
  show "\<exists> e. e \<succeq> 0 \<and> pos_arctic e \<and> \<not> c \<succeq> d * e"
  proof (cases c)
    case MinInfty
    show ?thesis
      by (rule exI[of _ "Num_arc 0"],
        unfold d MinInfty zero_arctic_def, simp)
  next
    case (Num_arc m)
    show ?thesis
      by (rule exI[of _ "Num_arc (abs m  + 1)"], insert n,
        unfold d Num_arc zero_arctic_def, simp)
  qed
qed


subsection {* The arctic semiring over the rationals *}

text {* completely analogous to the integers, where one has to use delta-orderings *}

datatype arctic_rat = MinInfty_rat | Num_arc_rat rat


instantiation arctic_rat :: max_ordered_semiring_1
begin
fun plus_arctic_rat :: "arctic_rat \<Rightarrow> arctic_rat \<Rightarrow> arctic_rat"
where "plus_arctic_rat MinInfty_rat y = y"
   |  "plus_arctic_rat x MinInfty_rat = x"
   |  "plus_arctic_rat (Num_arc_rat x) (Num_arc_rat y) = (Num_arc_rat (max x y))"
fun times_arctic_rat :: "arctic_rat \<Rightarrow> arctic_rat \<Rightarrow> arctic_rat"
where "times_arctic_rat MinInfty_rat y = MinInfty_rat"
   |  "times_arctic_rat x MinInfty_rat = MinInfty_rat"
   |  "times_arctic_rat (Num_arc_rat x) (Num_arc_rat y) = (Num_arc_rat (x + y))"
fun ge_arctic_rat :: "arctic_rat \<Rightarrow> arctic_rat \<Rightarrow> bool"
where "ge_arctic_rat x MinInfty_rat = True"
   |  "ge_arctic_rat MinInfty_rat (Num_arc_rat _) = False"
   |  "ge_arctic_rat (Num_arc_rat x) (Num_arc_rat y) = (y \<le> x)"
definition zero_arctic_rat :: arctic_rat
where "zero_arctic_rat = MinInfty_rat"
definition one_arctic_rat :: arctic_rat
where "one_arctic_rat = Num_arc_rat 0"
definition max0_arctic_rat :: "arctic_rat \<Rightarrow> arctic_rat" where [simp]: "max0_arctic_rat \<equiv> id"
instance
proof
  fix x y :: arctic_rat
  show "x + y = y + x"
    by (cases x, cases y, auto, cases y, auto)
next
  fix x y z :: arctic_rat
  show "(x + y) + z = x + (y + z)"
    by (cases x, auto, cases y, auto, cases z, auto)
next
  fix x y z :: arctic_rat
  show "(x * y) * z = x * (y * z)"
    by (cases x, auto, cases y, auto, cases z, auto)
next
  fix x :: arctic_rat
  show "x * 0 = 0"
    by (cases x, auto simp: zero_arctic_rat_def)
next
  fix x y z :: arctic_rat
  show "x * (y + z) = x * y + x * z"
    by (cases x, auto, cases y, auto, cases z, auto)
next
  fix x y z :: arctic_rat
  show "(x + y) * z = x * z + y * z"
    by (cases x, auto, cases y, cases z, auto, cases z, auto)
next
  fix x y z :: arctic_rat
  assume "x \<succeq> y" 
  thus "x + z \<succeq> y + z"
    by (cases x, cases y, cases z, auto, cases y, cases z, auto, cases z, auto)
next
  fix x y z :: arctic_rat
  assume "x \<succeq> y" 
  thus "x * z \<succeq> y * z"
    by (cases x, cases y, cases z, auto, cases y, cases z, auto, cases z, auto)
next
  fix x y z :: arctic_rat
  assume "y \<succeq> z"
  thus "x * y \<succeq> x * z"
    by (cases x, cases y, cases z, auto, cases y, cases z, auto, cases z, auto)
next
  fix x :: arctic_rat
  show "x \<succeq> x" 
    by (cases x, auto)
next
  fix x y z :: arctic_rat
  assume "x \<succeq> y" and "y \<succeq> z"
  thus "x \<succeq> z"
    by (cases x, cases y, auto, cases y, cases z, auto, cases z, auto)
next
  fix x :: arctic_rat
  show "0 + x = x"
    by (simp add: zero_arctic_rat_def)
next
  fix x :: arctic_rat
  show "0 * x = 0"
    by (simp add: zero_arctic_rat_def)
next
  fix x :: arctic_rat
  show "1 * x = x"
    by (cases x, simp_all add: one_arctic_rat_def)
next
  fix x :: arctic_rat
  show "x * 1 = x"
    by (cases x, simp_all add: one_arctic_rat_def)
next
  show "(0 :: arctic_rat) \<noteq> 1"
    by (simp add: zero_arctic_rat_def one_arctic_rat_def)
next
  show "(1 :: arctic_rat) \<succeq> 0"
    by (simp add: zero_arctic_rat_def one_arctic_rat_def)
next
  fix x :: arctic_rat
  show "x \<succeq> 0" by (cases x, auto simp: zero_arctic_rat_def)
next
  fix x :: arctic_rat
  show "max0 x \<succeq> x" by (cases x, auto)
next
  fix x :: arctic_rat
  show "x + 0 = x" by (cases x, auto simp: zero_arctic_rat_def)
qed auto
end


text {* x >d y is interpreted as y = -inf or (x,y != -inf and x >d y on the rationals) *}
fun gt_arctic_rat :: "rat \<Rightarrow> arctic_rat \<Rightarrow> arctic_rat \<Rightarrow> bool"
where "gt_arctic_rat \<delta> _ MinInfty_rat = True"
   |  "gt_arctic_rat \<delta> MinInfty_rat (Num_arc_rat _) = False"
   |  "gt_arctic_rat \<delta> (Num_arc_rat x) (Num_arc_rat y) = rat_gt \<delta> x y"


fun get_arctic_rat_num :: "arctic_rat \<Rightarrow> rat"
where "get_arctic_rat_num (Num_arc_rat n) = n"

fun pos_arctic_rat :: "arctic_rat \<Rightarrow> bool"
where "pos_arctic_rat MinInfty_rat = False"
    | "pos_arctic_rat (Num_arc_rat n) = (0 \<le> n)"

lemma arctic_rat_interpretation: assumes dpos: "\<delta> > 0" shows "SN_both_mono_ordered_semiring_1 1 (gt_arctic_rat \<delta>) pos_arctic_rat"
proof -
  from rat_interpretation[OF dpos] interpret SN_strict_mono_ordered_semiring_1 \<delta> "rat_gt \<delta>" rat_mono by simp
  show ?thesis 
  proof
    fix x y z :: arctic_rat
    assume "x \<succeq> y" and "gt_arctic_rat \<delta> y z"
    thus "gt_arctic_rat \<delta> x z"
      by (cases z, simp, cases y, simp, cases x, simp, simp add: compat)
  next 
    fix x y z :: arctic_rat
    assume "gt_arctic_rat \<delta> x y" and "y \<succeq> z"
    thus "gt_arctic_rat \<delta> x z"
      by (cases z, simp, cases y, simp, cases x, simp, simp add: compat2)
  next
    fix x y z :: arctic_rat
    assume "gt_arctic_rat \<delta> x y" and "gt_arctic_rat \<delta> y z"
    thus "gt_arctic_rat \<delta> x z"
      by (cases z, simp, cases y, simp, cases x, simp, insert dpos, auto simp: compat2 rat_gt_def)
  next
    fix x y z u
    assume "gt_arctic_rat \<delta> x y" and "gt_arctic_rat \<delta> z u"
    thus "gt_arctic_rat \<delta> (x + z) (y + u)"
      by (cases y, cases u, simp, cases z, simp, cases x, simp, simp add: rat_gt_def, 
        cases z, cases x, simp, cases u, simp, simp, cases x, simp, cases z, simp, cases u, simp add: rat_gt_def, simp add: rat_gt_def)
  next
    fix x y z
    assume "gt_arctic_rat \<delta> x y"
    thus "gt_arctic_rat \<delta> (x * z) (y * z)"
      by (cases y, simp, cases z, simp, cases x, simp, simp add: plus_gt_left_mono)
  next
    fix x
    assume "gt_arctic_rat \<delta> 0 x"
    thus "x = 0"
      by (cases x, auto simp: zero_arctic_rat_def)
  next
    show "pos_arctic_rat 1" unfolding one_arctic_rat_def by simp
  next
    fix x
    show "gt_arctic_rat \<delta> x 0" unfolding zero_arctic_rat_def by simp
  next
    fix x y
    assume "pos_arctic_rat x" 
    thus "pos_arctic_rat (x + y)" by (cases x, simp, cases y, auto)
  next
    fix x y
    assume "pos_arctic_rat x" and "pos_arctic_rat y"
    thus "pos_arctic_rat (x * y)" by (cases x, simp, cases y, auto)
  next
    show "SN {(x,y). pos_arctic_rat y \<and> gt_arctic_rat \<delta> x y}" (is "SN ?rel")
    proof - {
      fix x
      assume "\<exists> f . f 0 = x \<and> (\<forall> i. (f i, f (Suc i)) \<in> ?rel)"
      from this obtain f where "f 0 = x" and seq: "\<forall> i. (f i, f (Suc i)) \<in> ?rel" by auto
      from seq have steps: "\<forall> i. gt_arctic_rat \<delta> (f i) (f (Suc i)) \<and> pos_arctic_rat (f (Suc i)) " by auto
      let ?g = "\<lambda> i. get_arctic_rat_num (f i)"
      have "\<forall> i. ?g (Suc i) \<ge> 0 \<and> rat_gt \<delta> (?g i) (?g (Suc i))"
      proof
        fix i
        from steps have i: "gt_arctic_rat \<delta> (f i) (f (Suc i)) \<and> pos_arctic_rat (f (Suc i))" by auto
        from i obtain n where fi: "f i = Num_arc_rat n" by (cases "f (Suc i)", simp, cases "f i", auto)
        from i obtain m where fsi: "f (Suc i) = Num_arc_rat m" by (cases "f (Suc i)", auto)
        with i have gz: "0 \<le> m" by simp
        from i fi fsi have "rat_gt \<delta> n m" by auto
        with fi fsi gz
        show "?g (Suc i) \<ge> 0 \<and> rat_gt \<delta> (?g i) (?g (Suc i))" by auto
      qed
      from this obtain g where "\<forall> i. g (Suc i) \<ge> 0 \<and> rat_gt \<delta> (g i) (g (Suc i))" by auto
      hence "\<exists> f. f 0 = g 0 \<and> (\<forall> i. (f i, f (Suc i)) \<in> {(x,y). y \<ge> 0 \<and> rat_gt \<delta> x y})" by auto
      with SN have False unfolding SN_defs by auto
    }
    thus ?thesis unfolding SN_defs by auto
    qed 
  next
    show "(1 :: arctic_rat) \<succeq> 0" unfolding zero_arctic_rat_def by simp
  next
    fix x :: arctic_rat
    show "x \<succeq> 0" unfolding zero_arctic_rat_def by simp
  next
    show "\<not> pos_arctic_rat 0" unfolding zero_arctic_rat_def by simp
  next
    fix c d
    assume "pos_arctic_rat d" 
    then obtain n where d: "d = Num_arc_rat n" and n: "0 \<le> n"
      by (cases d, auto)  
    show "\<exists> e. e \<succeq> 0 \<and> pos_arctic_rat e \<and> \<not> c \<succeq> d * e"
    proof (cases c)
      case MinInfty_rat
      show ?thesis
        by (rule exI[of _ "Num_arc_rat 0"],
          unfold d MinInfty_rat zero_arctic_rat_def, simp)
    next
      case (Num_arc_rat m)
      show ?thesis
        by (rule exI[of _ "Num_arc_rat (abs m  + 1)"], insert n,
          unfold d Num_arc_rat zero_arctic_rat_def, simp)
    qed
  next
    fix x y z
    assume gt: "gt_arctic_rat \<delta> y z"
    {
      fix x y z
      assume gt: "rat_gt \<delta> y z"
      have "rat_gt \<delta> (x + y) (x + z)"
        using plus_gt_left_mono[OF gt] by (auto simp: field_simps)
    }
    with gt show "gt_arctic_rat \<delta> (x * y) (x * z)"
      by (cases x, simp, cases z, simp, cases y, simp_all)
  qed
qed

fun weak_gt_arctic_rat :: "arctic_rat \<Rightarrow> arctic_rat \<Rightarrow> bool"
where "weak_gt_arctic_rat _ MinInfty_rat = True"
   |  "weak_gt_arctic_rat MinInfty_rat (Num_arc_rat _) = False"
   |  "weak_gt_arctic_rat (Num_arc_rat x) (Num_arc_rat y) = (x > y)"

interpretation weak_arctic_rat_SN: weak_SN_both_mono_ordered_semiring_1 weak_gt_arctic_rat 1 pos_arctic_rat
proof
  fix xys
  assume orient: "\<forall> x y. (x,y) \<in> set xys \<longrightarrow> weak_gt_arctic_rat x y"
  obtain xysp where xysp: "xysp = map (\<lambda> (ax, ay). (case ax of Num_arc_rat x \<Rightarrow> x , case ay of Num_arc_rat y \<Rightarrow> y)) (filter (\<lambda> (ax,ay). ax \<noteq> MinInfty_rat \<and> ay \<noteq> MinInfty_rat) xys)"
    (is "_ = map ?f _")
    by auto
  have "\<forall> x y. (x,y) \<in> set xysp \<longrightarrow> x > y" 
  proof (intro allI impI)
    fix x y
    assume "(x,y) \<in> set xysp"
    with xysp obtain ax ay where "(ax,ay) \<in> set xys" and "ax \<noteq> MinInfty_rat" and "ay \<noteq> MinInfty_rat" and "(x,y) = ?f (ax,ay)" by auto
    hence "(Num_arc_rat x, Num_arc_rat y) \<in> set xys" by (cases ax, simp, cases ay, auto)
    with orient show "x > y" by force
  qed
  with rat_minimal_delta[of xysp] obtain \<delta> where dpos: "\<delta> > 0" and orient2: "\<And> x y. (x, y) \<in> set xysp \<Longrightarrow> rat_gt \<delta> x y" by auto
  have orient: "\<forall> x y. (x,y) \<in> set xys \<longrightarrow> gt_arctic_rat \<delta> x y"
  proof(intro allI impI)
    fix ax ay
    assume axay: "(ax,ay) \<in> set xys"
    with orient have orient: "weak_gt_arctic_rat ax ay" by auto
    show "gt_arctic_rat \<delta> ax ay"
    proof (cases ay, simp)
      case (Num_arc_rat y) note ay = this
      show ?thesis
      proof (cases ax)
        case MinInfty_rat
        with ay orient show ?thesis by auto
      next
        case (Num_arc_rat x) note ax = this
        from ax ay axay have "(x,y) \<in> set xysp" unfolding xysp by force
        from ax ay orient2[OF this] show ?thesis by simp
      qed
    qed
  qed
  show "\<exists>gt. SN_both_mono_ordered_semiring_1 1 gt pos_arctic_rat \<and> (\<forall>x y. (x, y) \<in> set xys \<longrightarrow> gt x y)"
    by (intro exI conjI, rule arctic_rat_interpretation[OF dpos], rule orient)
qed  

    
end
