(*  Title:       Computing Square Roots using the Babylonian Method
    Author:      René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  René Thiemann
    License:     LGPL
*)

(*
Copyright 2013 René Thiemann

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

theory Sqrt_Babylonian
imports 
  "../Real_Impl/Real_Impl_Auxiliary"
begin

section Introduction

text {*
  This theory provides executable algorithms for computing square-roots of numbers which
  are all based on the Babylonian method (which is also known as Heron's method or Newton's method).
  
  For integers / naturals / rationals precise algorithms are given, i.e., here $sqrt\ x$ delivers
  a list of all integers / naturals / rationals $y$ where $y^2 = x$. 
  To this end, the Babylonian method has been adapted by using integer-divisions.

  In addition to the precise algorithms, we also provide three approximation algorithms. One works for 
  arbitrary linear ordered fields, where some number $y$ is computed such that
  @{term "abs(y^2 - x) < \<epsilon>"}. Moreover, for the integers we provide algorithms to compute
  @{term "floor (sqrt (x :: int))"} and @{term "ceiling (sqrt (x :: int))"} which are both based
  on the underlying algorithm that is used to compute the precise square-roots on integers, if these 
  exist.

  The major motivation for developing the precise algorithms was given by \ceta{} \cite{CeTA},
  a tool for certifiying termination proofs. Here, non-linear equations of the form
  $(a_1x_1 + \dots a_nx_n)^2 = p$ had to be solved over the integers, where $p$ is a concrete polynomial.
  For example, for the equation $(ax + by)^2 = 4x^2 - 12xy + 9y^2$ one easily figures out that
  $a^2 = 4, b^2 = 9$, and $ab = -6$, which results in a possible solution $a = \sqrt 4 = 2, b = - \sqrt 9 = -3$.
*}

section {* The Babylonian method *}

text {*
The Babylonian method for computing $\sqrt n$ iteratively computes 
\[
x_{i+1} = \frac{\frac n{x_i} + x_i}2
\]
until $x_i^2 \approx n$. Note that if $x_0^2 \geq n$, then for all $i$ we have both
$x_i^2 \geq n$ and $x_i \geq x_{i+1}$. 
*}

section {* The Babylonian method using integer division *}
text {*
  First, the algorithm is developed for the non-negative integers.
  Here, the division operation $\frac xy$ is replaced by @{term "x div y = \<lfloor>of_int x / of_int y\<rfloor>"}.
  Note that replacing @{term "\<lfloor>of_int x / of_int y\<rfloor>"} by @{term "\<lceil>of_int x / of_int y\<rceil>"} would lead to non-termination
  in the following algorithm.

  We explicititly develop the algorithm on the integers and not on the naturals, as the calculations
  on the integers have been much easier. For example, $y - x + x = y$ on the integers, which would require
  the side-condition $y \geq x$ for the naturals. These conditions will make the reasoning much more tedious---as
  we have experienced in an earlier state of this development where everything was based on naturals.

For the main algorithm we use the auxiliary guard @{term "\<not> (x < (0 :: int) \<or> n < (0 :: int))"}  to ensure that we do not have to worry
  about negative numbers for the termination argument and during the soundness proof. Moreover, since the elements
  $x_0, x_1, x_2,\dots$ are monotone decreasing, we abort as soon as $x_i^2 \leq n$. *}

function sqrt_babylon_int_main :: "int \<Rightarrow> int \<Rightarrow> int \<times> bool" where 
  "sqrt_babylon_int_main x n = (if (x < 0 \<or> n < 0) then (0,False) else (if x * x \<le> n then (x, x * x = n)
    else sqrt_babylon_int_main ((n div x + x) div 2) n))"
    by pat_completeness auto

text {* For the executable algorithm we omit the guard and use a let-construction *}

partial_function (tailrec) sqrt_int_main :: "int \<Rightarrow> int \<Rightarrow> int \<times> bool" where 
  [code]: "sqrt_int_main x n = (let x2 = x * x in if x2 \<le> n then (x, x2 = n)
    else sqrt_int_main ((n div x + x) div 2) n)"

text {* Once we have proven soundness of @{const sqrt_babylon_int_main} and equivalence to @{const sqrt_int_main}, it
  is easy to assemble the following algorithm which computes all square roots for arbitrary integers. *}

definition sqrt_int :: "int \<Rightarrow> int list" where 
  "sqrt_int x \<equiv> if x < 0 then [] else case sqrt_int_main x x of (y,True) \<Rightarrow> if y = 0 then [0] else [y,-y] | _ \<Rightarrow> []"

text {* For proving soundness, we first need some basic properties of integers. *}

lemma int_lesseq_square: "(z :: int) \<le> z * z" 
proof (cases "z \<ge> 0")
  case True
  have "1 * z = z" "0 * z = 0" by (auto simp: field_simps)
  with True show ?thesis by (metis abs_of_nonneg mult_right_mono not_le zabs_less_one_iff)
qed auto

lemma square_int_pos_mono: assumes x: "0 \<le> (x :: int)" and y: "0 \<le> y" 
  shows "(x * x \<le> y * y) = (x \<le> y)"
  using assms by (metis mult_mono mult_strict_mono' not_less)

lemma square_int_pos_strict_mono: assumes x: "0 \<le> (x :: int)" and y: "0 \<le> y" 
  shows "(x * x < y * y) = (x < y)"
  using assms by (metis mult_mono mult_strict_mono' not_less)

lemma square_int_pos_inj: assumes x: "0 \<le> (x :: int)" and y: "0 \<le> y" 
  and id: "x * x = y * y"
  shows "x = y"
proof -
  from square_int_pos_mono[OF x y] id have xy: "x \<le> y" by auto
  from square_int_pos_mono[OF y x] id have yx: "y \<le> x" by auto
  from xy yx show ?thesis by auto
qed
    
lemma iteration_mono_eq: assumes xn: "x * x = (n :: int)"
  shows "(n div x + x) div 2 = x" unfolding xn[symmetric]
  by simp

text {* The following property is the essential property for
  proving termination of @{const "sqrt_babylon_int_main"}.
*}
lemma iteration_mono_less: assumes x: "x \<ge> 0" 
  and n: "n \<ge> 0"
  and xn: "x * x > (n :: int)"
  shows "(n div x + x) div 2 < x"
proof -
  let ?sx = "(n div x + x) div 2"
  from xn have xn_le: "x * x \<ge> n" by auto
  from xn x n have x0: "x > 0" by (cases "x = 0", auto)
  have "n div x * x \<le> n" unfolding mod_div_equality_int
    using transfer_nat_int_function_closures x n
    by simp
  also have "\<dots> \<le> x * x" using xn by auto
  finally have le: "n div x \<le> x" using x x0 by auto
  have "?sx \<le> ((x * x) div x + x) div 2" 
    by (rule zdiv_mono1, insert le, auto)
  also have "\<dots> \<le> x" by fastforce
  finally have le: "?sx \<le> x" .
  {
    assume "?sx = x"
    hence "n div x \<ge> x" by auto
    from mult_right_mono[OF this x]
    have ge: "n div x * x \<ge> x * x" . 
    from mod_div_equality[of n x] have "n div x * x = n - n mod x" by arith
    from ge[unfolded this]
    have le: "x * x \<le> n - n mod x" .
    have ge: "n mod x \<ge> 0" using n x transfer_nat_int_function_closures by auto
    from le ge 
    have "n \<ge> x * x" by auto
    with xn have False by auto
  }
  with le show ?thesis by fastforce 
qed

lemma iteration_mono_lesseq: assumes x: "x \<ge> 0" and n: "n \<ge> 0" and xn: "x * x \<ge> (n :: int)"
  shows "(n div x + x) div 2 \<le> x"
proof (cases "x * x = n")
  case True
  from iteration_mono_eq[OF this] show ?thesis by simp
next
  case False
  with assms have "x * x > n" by auto
  from iteration_mono_less[OF x n this]
  show ?thesis by simp
qed
  
termination (* of sqrt_babylon_int_main *)
proof -
  let ?mm = "\<lambda> x  n :: int. nat x"
  let ?m1 = "\<lambda> (x,n). ?mm x n"
  let ?m = "measures [?m1]"
  show ?thesis
  proof (relation ?m, simp)
    fix x n :: int
    assume "\<not> x * x \<le> n"
    hence x: "x * x > n" by auto
    assume "\<not> (x < 0 \<or> n < 0)"
    hence x_n: "x \<ge> 0" "n \<ge> 0" by auto
    from x x_n have x0: "x > 0" by (cases "x = 0", auto)
    from iteration_mono_less[OF x_n x] x0
    show "(((n div x + x) div 2,n),(x,n)) \<in> ?m" by auto
  qed
qed 

text {* We next prove that @{const sqrt_int_main} is a correct implementation of @{const sqrt_babylon_int_main}.
We additionally prove that the result is always positive, a lower bound, and that the returned boolean indicates
whether the result is a square or not. We proof all these results in one go, so that we can share the 
inductive proof.  
 *}
lemma sqrt_int_main_babylon_pos: "x \<ge> 0 \<Longrightarrow> n \<ge> 0 \<Longrightarrow> 
  sqrt_int_main x n = sqrt_babylon_int_main x n \<and> (sqrt_int_main x n = (y,b) \<longrightarrow> y \<ge> 0 \<and> y * y \<le> n \<and> b = (y * y = n))"
proof (induct x n rule: sqrt_babylon_int_main.induct)
  case (1 x n)
  hence id: "(x < 0 \<or> n < 0) = False" by auto
  note d = sqrt_int_main.simps[of x n] sqrt_babylon_int_main.simps[of x n] id if_False Let_def
  show ?case
  proof (cases "x * x \<le> n")
    case True
    thus ?thesis unfolding d using 1(2) by auto
  next
    case False
    hence id: "(x * x \<le> n) = False" by simp
    from 1(3) 1(2) have not: "\<not> (x < 0 \<or> n < 0)" by auto
    show ?thesis unfolding d id
      by (rule 1(1)[OF not False _ 1(3)], insert transfer_nat_int_function_closures 1(2) 1(3), auto)
  qed
qed

lemma sqrt_int_main: "x \<ge> 0 \<Longrightarrow> n \<ge> 0 \<Longrightarrow> sqrt_int_main x n = sqrt_babylon_int_main x n"
  using sqrt_int_main_babylon_pos by blast

lemma sqrt_int_main_pos: "x \<ge> 0 \<Longrightarrow> n \<ge> 0 \<Longrightarrow> sqrt_int_main x n = (y,b) \<Longrightarrow> y \<ge> 0" 
  using sqrt_int_main_babylon_pos by blast

lemma sqrt_int_main_sound: "x \<ge> 0 \<Longrightarrow> n \<ge> 0 \<Longrightarrow> sqrt_int_main x n = (y,b) \<Longrightarrow> b = (y * y = n)"
  using sqrt_int_main_babylon_pos by blast

text {* In order to prove completeness of the algorithms, we provide sharp upper and lower bounds
  for @{const sqrt_int_main}. *}

lemma sqrt_int_main_lower: "x \<ge> 0 \<Longrightarrow> n \<ge> 0 \<Longrightarrow> sqrt_int_main x n = (y,b) \<Longrightarrow> y * y \<le> n" 
  using sqrt_int_main_babylon_pos by blast

lemma sqrt_babylon_int_main_upper: 
  shows "y * y \<ge> n \<Longrightarrow> y \<ge> 0 \<Longrightarrow> n \<ge> 0 \<Longrightarrow> sqrt_babylon_int_main y n = (x,b) \<Longrightarrow> n < (x + 1) * (x + 1)"
proof (induct y n rule: sqrt_babylon_int_main.induct)
  case (1 y n)
  from 1(3) have y0: "y \<ge> 0" .
  from 1(4) have n0: "n \<ge> 0" .
  def y' \<equiv> "(n div y + y) div 2"
  from y0 n0 have y'0: "y' \<ge> 0" unfolding y'_def
    by (metis Divides.transfer_nat_int_function_closures(1) add_increasing zero_le_numeral)
  let ?sqrt = "sqrt_babylon_int_main"
  from 1(5) have sqrt: "?sqrt y n = (x,b)" by auto
  from y0 n0 have not: "\<not> (y < 0 \<or> n < 0)" "(y < 0 \<or> n < 0) = False" by auto
  note sqrt = sqrt[unfolded sqrt_babylon_int_main.simps[of y n] not(2) if_False, folded y'_def]
  note IH = 1(1)[folded y'_def, OF not(1) _ _ y'0 n0]
  show ?case
  proof (cases "y * y \<le> n")
    case False note yyn = this
    with sqrt have sqrt: "?sqrt y' n = (x,b)" by simp
    show ?thesis
    proof (cases "n \<le> y' * y'")
      case True
      show ?thesis 
        by (rule IH[OF False True sqrt])
    next
      case False
      with sqrt have x: "x = y'" unfolding sqrt_babylon_int_main.simps[of y' n]
        using n0 y'0 by simp
      from yyn have yyn: "y * y > n" by simp
      from False have yyn': "n > y' * y'" by auto
      show ?thesis
      proof (cases "n = 0")
        case True
        thus ?thesis 
          by (metis comm_semiring_1_class.normalizing_semiring_rules(10) x y'0 zle_add1_eq_le zmult_zless_mono2)
      next
        case False note n00 = this
        from yyn n0 have y00: "y \<noteq> 0" by auto
        let ?y = "of_int y :: rat"
        let ?n = "of_int n :: rat"
        def Y \<equiv> ?y
        def NY \<equiv> "?n / ?y"
        def S \<equiv> "Y + NY"
        def s \<equiv> "n div y + y"
        from y00 y0 have y0: "?y > 0" by auto
        from yyn have "(of_int (y * y - n) :: rat) > 0" by linarith
        hence "?y * ?y - ?n > 0" by simp
        with y0 have "Y - NY > 0" unfolding Y_def NY_def
          by (metis diff_divide_eq_iff divide_less_cancel divide_pos_pos linordered_field_no_lb pos_divide_less_eq)                
        hence "(Y - NY) * (Y - NY) > 0" 
          by (metis mult_pos_pos)
        also have "(Y - NY) * (Y - NY) = (Y + NY) * (Y + NY) - 4 * Y * NY" 
          by (simp add: field_simps)
        also have "4 * Y * NY = 4 * ?n" unfolding Y_def NY_def using y0 by auto
        finally have ineq1: "((Y + NY) / 2) * ((Y + NY) / 2) > ?n" by simp
        {
          have "?n / ?y < of_int (floor (?n / ?y)) + 1" 
            by (rule divide_less_floor1)
          also have "floor (?n / ?y) = of_int (n div y)"
            unfolding div_is_floor_divide ..
          finally have less: "S < of_int s + 1" 
            unfolding S_def Y_def NY_def s_def by auto
          have "S / 2 < of_int (floor (S / 2)) + 1"
            by (rule divide_less_floor1)
          hence "S / 2 \<le> of_int (s div 2) + 1" using less by auto
        }
        hence ge: "of_int y' + 1 \<ge> (Y + NY) / 2" unfolding y'_def s_def S_def by simp
        have pos1: "(Y + NY) / 2 \<ge> 0" unfolding Y_def NY_def using n0 y0
          by (auto simp: field_simps)
        have pos2: "of_int y' + (1 :: rat) \<ge> 0" using y'0 by auto
        have ineq2: "(of_int y' + 1) * (of_int y' + 1) \<ge> ((Y + NY) / 2) * ((Y + NY) / 2)"
          by (rule mult_mono[OF ge ge pos2 pos1])
        from order.strict_trans2[OF ineq1 ineq2]
        have "?n < of_int ((x + 1) * (x + 1))" unfolding x by simp
        thus "n < (x + 1) * (x + 1)" by linarith
      qed
    qed
  next
    case True
    with sqrt have x: "x = y" by auto
    with 1(2) True have n: "n = y * y" by auto
    show ?thesis unfolding n x using y0 
      by (simp add: field_simps)
  qed
qed

lemma sqrt_int_main_upper: 
  "x * x \<ge> n \<Longrightarrow> x \<ge> 0 \<Longrightarrow> n \<ge> 0 \<Longrightarrow> sqrt_int_main x n = (y,b) \<Longrightarrow> n < (y + 1) * (y + 1)"
  using sqrt_babylon_int_main_upper[of n x y b] sqrt_int_main[of x n] by auto

text {* After having proven the bounds, we can show completeness of @{const sqrt_int_main}. *}

lemma sqrt_int_main_complete: assumes x0: "x \<ge> 0"
  and xx: "x * x = n"
  and yy: "y * y \<ge> n"
  and y0: "y \<ge> 0"
  and n0: "n \<ge> 0"
  shows "sqrt_int_main y n = (x,True)"
proof -
  note xx' = xx[symmetric]
  obtain x' b where s: "sqrt_int_main y n = (x',b)" by force
  from sqrt_int_main_pos[OF y0 n0 s] have x'0: "x' \<ge> 0" by auto
  from sqrt_int_main_lower[OF y0 n0 s, unfolded xx']  
  have "x' \<le> x" unfolding square_int_pos_mono[OF x'0 x0] .
  moreover from sqrt_int_main_upper[OF yy y0 n0 s, unfolded xx']
  have "x < x' + 1" using square_int_pos_strict_mono[OF x0, of "x' + 1"] x'0 by auto
  ultimately have x': "x' = x" by linarith
  from sqrt_int_main_sound[OF y0 n0, unfolded s, OF refl, unfolded xx']
  show ?thesis unfolding s x' by auto
qed  

text {* Having proven soundness and completeness of @{const sqrt_int_main},
  it is easy to prove soundness of @{const sqrt_int}. *}

lemma sqrt_int[simp]: "set (sqrt_int x) = {y. y * y = x}"
proof -
  note d = sqrt_int_def
  show ?thesis
  proof (cases "x < 0 \<or> \<not> snd (sqrt_int_main x x)")
    case True
    hence left: "set (sqrt_int x) = {}" unfolding d by (cases "x < 0", simp, cases "sqrt_int_main x x", auto)  
    {
      fix y
      assume x: "y * y = x"
      have "\<exists> y. y * y = x \<and> y \<ge> 0"
      proof (cases "y \<ge> 0")
        case True
        with x show ?thesis by auto
      next
        case False
        show ?thesis
          by (rule exI[of _ "-y"], insert False x, auto)
      qed
      then obtain y where x: "y * y = x" and y: "y \<ge> 0" by auto
      from y x have x0: "x \<ge> 0" by auto
      from sqrt_int_main_complete[OF y x int_lesseq_square x0 x0] True
      have False unfolding sqrt_int_main[OF x0 x0] by auto
    }
    with left show ?thesis by auto
  next
    case False
    then obtain y where Some: "sqrt_int_main x x = (y, True)" and x: "x \<ge> 0" 
      by (cases "sqrt_int_main x x", auto)
    hence left: "set (sqrt_int x) = {y,-y}" unfolding d by (cases "y = 0", auto)
    have "\<exists> z. z \<ge> 0 \<and> {y,-y} = {z,-z}"
    proof (cases "y \<ge> 0")
      case False
      show ?thesis by (rule exI[of _ "-y"], insert False, auto)
    qed auto
    then obtain z where z: "z \<ge> 0" and yz: "{y,-y} = {z,-z}" by auto
    from sqrt_int_main_sound[OF x x Some]
    have y: "y * y = x" "-y * -y = x" by auto
    with yz have zz: "z * z = x" "-z * -z = x" by auto
    from y have "set (sqrt_int x) \<subseteq> {y. y * y = x}" unfolding left by auto
    moreover
    {
      fix u
      assume u: "u * u = x"
      have "u \<in> {z,-z}"
      proof (cases "u \<ge> 0")
        case True
        from u zz have "u * u = z * z" by auto
        from square_int_pos_inj[OF True z this]
        show ?thesis by auto
      next
        case False
        hence up: "-u \<ge> 0" by auto
        from u zz have "-u * -u = z * z" by auto
        from square_int_pos_inj[OF up z this] show ?thesis by auto
      qed
    }
    hence "{y. y * y = x} \<subseteq> set (sqrt_int x)" unfolding left yz by auto
    finally show ?thesis by auto
  qed
qed

section {* Floor and ceiling of square roots *}

text {* Using the bounds for @{const sqrt_int_main} we can easily design
  algorithms which compute @{term "floor (sqrt x)"} and @{term "ceiling (sqrt x)"}.
  To this end, we first develop algorithms for non-negative @{term x}, and later on
  these are used for the general case. *}

definition "sqrt_int_floor_pos x = fst (sqrt_int_main x x)"
definition "sqrt_int_ceiling_pos x = (case sqrt_int_main x x of (y,b) \<Rightarrow> if b then y else y + 1)"

lemma sqrt_int_floor_pos_lower: assumes x: "x \<ge> 0"
  shows "sqrt_int_floor_pos x * sqrt_int_floor_pos x \<le> x"
proof -
  obtain y b where s: "sqrt_int_main x x = (y,b)" by force
  from sqrt_int_main_lower[OF x x s] show ?thesis unfolding sqrt_int_floor_pos_def s by simp
qed

lemma sqrt_int_floor_pos_pos: assumes x: "x \<ge> 0"
  shows "sqrt_int_floor_pos x \<ge> 0"
proof -
  obtain y b where s: "sqrt_int_main x x = (y,b)" by force
  from sqrt_int_main_pos[OF x x s] show ?thesis unfolding sqrt_int_floor_pos_def s by simp
qed

lemma sqrt_int_floor_pos_upper: assumes x: "x \<ge> 0"
  shows "(sqrt_int_floor_pos x + 1) * (sqrt_int_floor_pos x + 1) > x"
proof -
  obtain y b where s: "sqrt_int_main x x = (y,b)" by force
  from sqrt_int_main_upper[OF int_lesseq_square x x s]
  show ?thesis unfolding sqrt_int_floor_pos_def s by auto
qed

lemma sqrt_int_floor_pos: assumes x: "x \<ge> 0" 
  shows "sqrt_int_floor_pos x = floor (sqrt (real x))"
proof -
  let ?s1 = "real_of_int (sqrt_int_floor_pos x)"
  let ?s2 = "sqrt (real x)"
  from sqrt_int_floor_pos_pos[OF x] have s1: "?s1 \<ge> 0" by simp
  from x have s2: "?s2 \<ge> 0" by auto
  from s1 have s11: "?s1 + 1 \<ge> 0" by auto
  have id: "?s2 * ?s2 = real x" using x by simp
  show ?thesis
  proof (rule floor_unique[symmetric])
    show "?s1 \<le> ?s2"
      unfolding square_lesseq_square[OF s1 s2, symmetric]
      unfolding id
      using sqrt_int_floor_pos_lower[OF x] 
      by (metis of_int_le_iff of_int_mult real_eq_of_int)
    show "?s2 < ?s1 + 1"
      unfolding square_less_square[OF s2 s11, symmetric]
      unfolding id
      using sqrt_int_floor_pos_upper[OF x]
        by (metis real_eq_of_int real_of_int_add real_of_int_less_iff real_of_int_mult real_of_one)
  qed
qed

lemma sqrt_int_ceiling_pos: assumes x: "x \<ge> 0"
  shows "sqrt_int_ceiling_pos x = ceiling (sqrt (real x))"
proof -
  obtain y b where s: "sqrt_int_main x x = (y,b)" by force
  from sqrt_int_main_pos[OF x x s] have y: "y \<ge> 0" by simp
  let ?s = "sqrt_int_ceiling_pos x"
  let ?sx = "sqrt (real x)"
  note d = sqrt_int_ceiling_pos_def
  show ?thesis
  proof (cases b)
    case True
    hence id: "?s = y" unfolding s d by auto
    from sqrt_int_main_sound[OF x x s] True have xy: "x = y * y" by auto
    show ?thesis unfolding id xy using y 
      by (metis ceiling_real_of_int id real_of_int_ge_zero_cancel_iff real_of_int_mult real_sqrt_mult_distrib2 sqrt_sqrt xy)
  next
    case False
    hence id: "?s = sqrt_int_floor_pos x + 1" unfolding d sqrt_int_floor_pos_def s by simp
    show ?thesis unfolding id sqrt_int_floor_pos[OF x]
    proof (rule ceiling_unique[symmetric])
      show "?sx \<le> real_of_int (\<lfloor>sqrt (real x)\<rfloor> + 1)"
        by (metis real_of_int_add real_of_int_def real_of_int_floor_add_one_ge real_of_one)
      let ?l = "real_of_int (\<lfloor>sqrt (real x)\<rfloor> + 1) - 1"
      let ?m = "real_of_int \<lfloor>sqrt (real x)\<rfloor>"
      have "?l = ?m" by simp
      also have "\<dots> < ?sx" 
      proof -
        have le: "?m \<le> ?sx" by (rule of_int_floor_le)
        have neq: "?m \<noteq> ?sx"
        proof
          assume "?m = ?sx"
          hence "?m * ?m = ?sx * ?sx" by simp
          also have "\<dots> = real x" using x by simp
          finally have xs: "x = \<lfloor>sqrt (real x)\<rfloor> * \<lfloor>sqrt (real x)\<rfloor>" 
            by (metis floor_real_of_int real_of_int_def real_of_int_mult)
          hence "\<lfloor>sqrt (real x)\<rfloor> \<in> set (sqrt_int x)" by simp
          with False s x show False unfolding sqrt_int_def by simp
        qed
        from le neq show ?thesis by arith
      qed
      finally show "?l < ?sx" .
    qed
  qed
qed

definition "sqrt_int_floor x = (if x \<ge> 0 then sqrt_int_floor_pos x else - sqrt_int_ceiling_pos (- x))"
definition "sqrt_int_ceiling x = (if x \<ge> 0 then sqrt_int_ceiling_pos x else - sqrt_int_floor_pos (- x))"

lemma sqrt_int_floor[simp]: "sqrt_int_floor x = floor (sqrt (real x))"
proof -
  note d = sqrt_int_floor_def
  show ?thesis 
  proof (cases "x \<ge> 0")
    case True
    with sqrt_int_floor_pos[OF True] show ?thesis unfolding d by simp
  next
    case False
    hence "- x \<ge> 0" by auto
    from False sqrt_int_ceiling_pos[OF this] show ?thesis unfolding d 
      by (simp add: real_sqrt_minus ceiling_minus)
  qed
qed

lemma sqrt_int_ceiling[simp]: "sqrt_int_ceiling x = ceiling (sqrt (real x))"
proof -
  note d = sqrt_int_ceiling_def
  show ?thesis 
  proof (cases "x \<ge> 0")
    case True
    with sqrt_int_ceiling_pos[OF True] show ?thesis unfolding d by simp
  next
    case False
    hence "- x \<ge> 0" by auto
    from False sqrt_int_floor_pos[OF this] show ?thesis unfolding d 
      by (simp add: real_sqrt_minus floor_minus)
  qed
qed


section {* Square roots for the naturals *}

text {* The idea is to use the algorithm for the integers and then convert between naturals and integers.

In the following lemma, we first observe that the first result of @{const sqrt_int} is always non-negative.
*}

lemma sqrt_int_empty_0_pos_neg: "\<exists> y. y > 0 \<and> (sqrt_int x = [] \<or> sqrt_int x = [0] \<or> sqrt_int x = [y,-y])"
proof (cases "sqrt_int x = []")
  case True
  show ?thesis
    by (rule exI[of _ 1], insert True, auto)
next
  case False
  note d = sqrt_int_def
  from False have x: "x \<ge> 0" unfolding d by (cases "x \<ge> 0", auto)
  from False x obtain y where main: "sqrt_int_main x x = (y,True)" unfolding d
    by (cases "sqrt_int_main x x", case_tac b, auto)
  from sqrt_int_main_pos[OF x x main] have y: "y \<ge> 0" by auto
  show ?thesis
  proof (cases "y = 0")
    case True
    with main x have res: "sqrt_int x = [0]" unfolding d by auto
    show ?thesis
      by (rule exI[of _ 1], insert True res, auto)
  next
    case False
    with y have y: "y > 0" by auto
    with main x have res: "sqrt_int x = [y,-y]" unfolding d by auto
    thus ?thesis using y by auto
  qed
qed

lemma sqrt_int_pos: "sqrt_int x = Cons s ms \<Longrightarrow> s \<ge> 0"
  using sqrt_int_empty_0_pos_neg[of x] by auto

text {* With this knowledge, it is easy to define a square-root function on the naturals. *}

definition sqrt_nat :: "nat \<Rightarrow> nat list"
  where "sqrt_nat x \<equiv> case (sqrt_int (int x)) of [] \<Rightarrow> [] | x # xs \<Rightarrow> [nat x]"

text {* The soundness of @{const sqrt_nat} is straight-forward. *}

lemma sqrt_nat[simp]: "set (sqrt_nat x) = { y. y * y = x}" (is "?l = ?r")
proof -
  note d = sqrt_nat_def
  let ?sx = "sqrt_int (int x)"
  from sqrt_int_empty_0_pos_neg[of "int x"] obtain y where y: "y > 0"
    and choice: "?sx = [] \<or> (?sx = [0] \<or> ?sx = [y,-y])" by auto
  have arith: "\<And> n. of_nat (n * n) = of_nat n * of_nat n" using int_arith_rules by auto
  {
    fix z
    assume "z \<in> ?l"
    with choice have hd: "hd ?sx \<in> set (?sx) \<and> z = nat (hd ?sx) \<and> ?sx \<noteq> []" unfolding d
      by (cases ?sx, auto)
    hence z: "z = nat (hd ?sx)" by auto
    from hd have "hd ?sx * hd ?sx = int x" "hd ?sx \<ge> 0" using y choice by auto
    hence "z * z = x" unfolding z by (metis arith int_nat_eq nat_int)
    hence "z \<in> ?r" by auto
  }
  moreover
  {
    fix z
    assume "z \<in> ?r"
    hence x: "x = z * z" by auto
    from arg_cong[OF this, of int]
    have x: "int x = int z * int z" unfolding arith .
    hence mem: "int z \<in> set ?sx" by auto
    from choice mem have "?sx = [0] \<or> ?sx = [y,-y]" by (cases ?sx, auto)
    hence "z \<in> ?l"
    proof
      assume "?sx = [0]"
      with mem have z: "z = 0" by auto
      with x have x: "x = 0" by auto
      thus ?thesis unfolding d z x by eval
    next
      assume sx: "?sx = [y,-y]"
      with mem y have y: "y = int z" by auto
      show ?thesis unfolding d sx list.simps y by auto
    qed
  }
  ultimately show ?thesis by blast
qed

section {* Square roots for the rationals *}

text {* For the rationals, the idea again, to apply the algorithm for the integers and then convert between integers
  and rationals. Here, the essential idea is to compute the square-roots of the numerator and denominator
  separately. *}

definition sqrt_rat :: "rat \<Rightarrow> rat list"
  where "sqrt_rat x \<equiv> case quotient_of x of (z,n) \<Rightarrow> (case sqrt_int n of 
    [] \<Rightarrow> [] 
  | sn # xs \<Rightarrow> map (\<lambda> sz. of_int sz / of_int sn) (sqrt_int z))"

text {* Whereas soundness of @{const sqrt_rat} is simple, it is a bit more tedious to show
  that all roots are computed, which uses facts on @{const coprime}. *}

lemma sqrt_rat[simp]: "set (sqrt_rat x) = { y. y * y = x}" (is "?l = ?r")
proof -
  note d = sqrt_rat_def
  obtain z n where q: "quotient_of x = (z,n)" by force
  let ?sz = "sqrt_int z"
  let ?sn = "sqrt_int n"
  from q have n: "n > 0" by (rule quotient_of_denom_pos)
  from q have x: "x = of_int z / of_int n" by (rule quotient_of_div)
  {
    fix y
    assume "y \<in> ?l"
    note y = this[unfolded d q split]
    then obtain sn snn where sn: "?sn = sn # snn" by (cases ?sn, auto)
    from y[unfolded sn] obtain sz where sz: "sz \<in> set ?sz" and y: "y = of_int sz / of_int sn" by auto
    from sn have sn: "sn \<in> set ?sn" by auto
    from sn have sn: "n = sn * sn" by auto
    from sz have sz: "z = sz * sz" by auto
    have "y \<in> ?r" unfolding x sn sz y by auto
  }
  moreover
  {
    fix y
    assume "y \<in> ?r"
    obtain yz yn where yq: "quotient_of y = (yz,yn)" by force
    let ?syz = "(of_int yz) :: rat"
    let ?syn = "(of_int yn) :: rat"
    from yq have yn: "yn > 0" by (rule quotient_of_denom_pos)
    from yq have y: "y = ?syz / ?syn" by (rule quotient_of_div)
    from `y \<in> ?r` x 
    have "of_int z / of_int n = y * y" by simp 
    also have "\<dots> = ?syz * ?syz / (?syn * ?syn)" unfolding y by simp
    finally have id: "of_int z / of_int n = ?syz * ?syz / (?syn * ?syn)" .
    have arith: "\<And> x y. of_int x * of_int y = of_int (x * y)" by simp
    have sn: "n = yn * yn"
    proof -
      from quotient_of_coprime[OF q] have cop: "coprime z n" .
      from quotient_of_coprime[OF yq] have ycop: "coprime yz yn" .
      hence ycop: "coprime (yz * yz) (yn * yn)" by (metis coprime_mul_eq_int gcd_mult_cancel_int)
      from arg_cong[OF id, of "\<lambda> x. x * of_int n * ?syn * ?syn"]
      have "of_int z * (?syn * ?syn) = (?syz * ?syz) * of_int n" using n yn by (simp add: field_simps)
      from this[unfolded arith] have id: "z * (yn * yn) = (yz * yz) * n" by linarith
      hence "abs z * abs (yn * yn) = abs (yz * yz) * abs n" unfolding abs_mult[symmetric] by simp
      with coprime_crossproduct_int[OF cop ycop] have "abs n = abs (yn * yn)" by auto
      with yn n show "n = yn * yn" by auto
    qed
    with id n have sz: "of_int z = ?syz * ?syz"  by auto
    from sz have sz: "z = yz * yz" unfolding arith by linarith
    from sqrt_int_empty_0_pos_neg[of n] obtain sn where
      s_n: "?sn = [] \<or> ?sn = [0] \<or> ?sn = [sn,-sn]" and pos: "sn > 0" by auto
    from sn have y_n: "yn \<in> set ?sn" by simp
    with s_n yn have s_n: "?sn = [sn,-sn]" by (cases ?sn, auto)
    from y_n pos s_n yn have sn: "sn = yn" by auto
    with s_n have sn: "?sn = [yn,-yn]" by auto
    from sz have yz: "yz \<in> set ?sz" by auto
    have "y \<in> ?l" unfolding d q using sn y yz by auto
  }
  ultimately show ?thesis by auto
qed

lemma sqr_rat_of_int: assumes x: "x * x = rat_of_int i"
  shows "\<exists> j :: int. j * j = i"
proof -
  from x have mem: "x \<in> set (sqrt_rat (rat_of_int i))" by simp
  from x have "rat_of_int i \<ge> 0" by (metis zero_le_square)
  hence *: "quotient_of (rat_of_int i) = (i,1)" by (metis Rat.of_int_def quotient_of_int)
  have 1: "sqrt_int 1 = [1,-1]" by code_simp
  from mem sqrt_rat_def * split 1 
  have x: "x \<in> rat_of_int ` {y. y * y = i}" by auto
  thus ?thesis by auto
qed

lemma sqrt_rat_pos: assumes sqrt: "sqrt_rat x = Cons s ms" 
  shows "s \<ge> 0"
proof -
  obtain z n where q: "quotient_of x = (z,n)" by force
  note sqrt = sqrt[unfolded sqrt_rat_def q, simplified]
  let ?sz = "sqrt_int z"
  let ?sn = "sqrt_int n"
  from q have n: "n > 0" by (rule quotient_of_denom_pos)
  from sqrt obtain sz mz where sz: "?sz = sz # mz" by (cases ?sn, auto)
  from sqrt obtain sn mn where sn: "?sn = sn # mn" by (cases ?sn, auto)
  from sqrt_int_pos[OF sz] sqrt_int_pos[OF sn] have pos: "0 \<le> sz" "0 \<le> sn" by auto
  from sqrt sz sn have s: "s = of_int sz / of_int sn" by auto
  show ?thesis unfolding s using pos
    by (metis of_int_0_le_iff zero_le_divide_iff)
qed

section {* Approximating square roots *}

text {*
  The difference to the previous algorithms is that now we abort, once the distance is below
  $\epsilon$. Moreover, here we use standard division and not integer division.

  We first provide the executable version without guard @{term "x > 0"} as partial function,
  and afterwards prove termination and soundness for a similar algorithm that is defined within the upcoming
locale.
*}

partial_function (tailrec) sqrt_approx_main_impl :: "'a :: linordered_field \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where 
  [code]: "sqrt_approx_main_impl \<epsilon> n x = (if x * x - n < \<epsilon> then x else sqrt_approx_main_impl \<epsilon> n 
    ((n / x + x) / 2))"

text {* We setup a locale where we ensure that we have standard assumptions: positive $\epsilon$ and
  positive $n$. We require sort @{term floor_ceiling}, since @{term "\<lfloor> x \<rfloor>"} is used for the termination
  argument. *}
locale sqrt_approximation = 
  fixes \<epsilon> :: "'a :: {linordered_field,floor_ceiling}"
  and n :: 'a
  assumes \<epsilon> : "\<epsilon> > 0"
  and n: "n > 0"
begin

function sqrt_approx_main :: "'a \<Rightarrow> 'a" where 
  "sqrt_approx_main x = (if x > 0 then (if x * x - n < \<epsilon> then x else sqrt_approx_main 
    ((n / x + x) / 2)) else 0)"
    by pat_completeness auto

text {* Termination essentially is a proof of convergence. Here, one complication is the fact
  that the limit is not always defined. E.g., if @{typ "'a"} is @{typ rat} then there is no
  square root of 2. Therefore, the error-rate $\frac x{\sqrt n} - 1$ is not expressible. 
  Instead we use the expression $\frac{x^2}n - 1$ as error-rate which
  does not require any square-root operation. *}
termination
proof -
  def er \<equiv> "\<lambda> x. (x * x / n - 1)" 
  def c \<equiv> "2 * n / \<epsilon>"
  def m \<equiv> "\<lambda> x. nat \<lfloor> c * er x \<rfloor>"
  have c: "c > 0" unfolding c_def using n \<epsilon>
    by (auto intro: divide_pos_pos)
  show ?thesis
  proof
    show "wf (measures [m])" by simp
  next
    fix x 
    assume x: "0 < x" and xe: "\<not> x * x - n < \<epsilon>"
    def y \<equiv> "(n / x + x) / 2"    
    show "((n / x + x) / 2,x) \<in> measures [m]" unfolding y_def[symmetric]
    proof (rule measures_less)
      from n have inv_n: "1 / n > 0" by (auto intro: divide_pos_pos)
      from xe have "x * x - n \<ge> \<epsilon>" by simp
      from this[unfolded mult_le_cancel_left_pos[OF inv_n, of \<epsilon>, symmetric]]
      have erxen: "er x \<ge> \<epsilon> / n" unfolding er_def using n by (simp add: field_simps)
      have en: "\<epsilon> / n > 0" and ne: "n / \<epsilon> > 0" using \<epsilon> n by (auto intro: divide_pos_pos)
      from en erxen have erx: "er x > 0" by linarith
      have pos: "er x * 4 + er x * (er x * 4) > 0" using erx
        by (auto intro: add_pos_nonneg)
      have "er y = 1 / 4 * (n / (x * x) - 2  + x * x / n)" unfolding er_def y_def using x n
        by (simp add: field_simps)
      also have "\<dots> = 1 / 4 * er x * er x / (1 + er x)" unfolding er_def using x n
        by (simp add: field_simps)
      finally have "er y = 1 / 4 * er x * er x / (1 + er x)" .
      also have "\<dots> < 1 / 4 * (1 + er x) * er x / (1 + er x)" using erx erx pos
        by (auto intro: mult_pos_pos simp: field_simps)
      also have "\<dots> = er x / 4" using erx by (simp add: field_simps)
      finally have er_y_x: "er y \<le> er x / 4" by linarith
      from erxen have "c * er x \<ge> 2" unfolding c_def mult_le_cancel_left_pos[OF ne, of _ "er x", symmetric]
        using n \<epsilon> by (auto simp: field_simps)
      hence pos: "\<lfloor>c * er x\<rfloor> > 0" "\<lfloor>c * er x\<rfloor> \<ge> 2" by auto
      show "m y < m x" unfolding m_def nat_mono_iff[OF pos(1)]
      proof -      
        have "\<lfloor>c * er y\<rfloor> \<le> \<lfloor>c * (er x / 4)\<rfloor>"
          by (rule floor_mono, unfold mult_le_cancel_left_pos[OF c], rule er_y_x)
        also have "\<dots> < \<lfloor>c * er x / 4 + 1\<rfloor>" by auto
        also have "\<dots> \<le> \<lfloor>c * er x\<rfloor>"
          by (rule floor_mono, insert pos(2), simp add: field_simps)
        finally show "\<lfloor>c * er y\<rfloor> < \<lfloor>c * er x\<rfloor>" .
      qed
    qed
  qed
qed

text {* Once termination is proven, it is easy to show equivalence of 
  @{const sqrt_approx_main_impl} and @{const sqrt_approx_main}. *}
lemma sqrt_approx_main_impl: "x > 0 \<Longrightarrow> sqrt_approx_main_impl \<epsilon> n x = sqrt_approx_main x"
proof (induct x rule: sqrt_approx_main.induct)
  case (1 x)
  hence x: "x > 0" by auto
  hence nx: "0 < (n / x + x) / 2" using n by (auto intro: divide_pos_pos pos_add_strict)
  note simps = sqrt_approx_main_impl.simps[of _ _ x] sqrt_approx_main.simps[of x]
  show ?case 
  proof (cases "x * x - n < \<epsilon>")
    case True
    thus ?thesis unfolding simps using x by auto
  next
    case False
    show ?thesis using 1(1)[OF x False nx] unfolding simps using x False by auto
  qed
qed

text {* Also soundness is not complicated. *}

lemma sqrt_approx_main_sound: assumes x: "x > 0" and xx: "x * x > n"
  shows "sqrt_approx_main x * sqrt_approx_main x > n \<and> sqrt_approx_main x * sqrt_approx_main x - n < \<epsilon>"
  using assms
proof (induct x rule: sqrt_approx_main.induct)
  case (1 x)
  from 1 have x:  "x > 0" "(x > 0) = True" by auto
  note simp = sqrt_approx_main.simps[of x, unfolded x if_True]
  show ?case
  proof (cases "x * x - n < \<epsilon>")
    case True
    with 1 show ?thesis unfolding simp by simp
  next
    case False
    let ?y = "(n / x + x) / 2"
    from False simp have simp: "sqrt_approx_main x = sqrt_approx_main ?y" by simp
    from n x have y: "?y > 0" by (auto intro: divide_pos_pos pos_add_strict)
    note IH = 1(1)[OF x(1) False y]
    from x have x4: "4 * x * x > 0" by (auto intro: mult_sign_intros)
    show ?thesis unfolding simp
    proof (rule IH)
      show "n < ?y * ?y"
        unfolding mult_less_cancel_left_pos[OF x4, of n, symmetric]
      proof -
        have id: "4 * x * x * (?y * ?y) = 4 * x * x * n + (n - x * x) * (n - x * x)" using x(1)
          by (simp add: field_simps)
        from 1(3) have "x * x - n > 0" by auto
        from mult_pos_pos[OF this this]
        show "4 * x * x * n < 4 * x * x * (?y * ?y)" unfolding id 
          by (simp add: field_simps)
      qed
    qed
  qed
qed   

end

text {* It remains to assemble everything into one algorithm. *}

definition sqrt_approx :: "'a :: {linordered_field,floor_ceiling} \<Rightarrow> 'a \<Rightarrow> 'a" where
  "sqrt_approx \<epsilon> x \<equiv> if \<epsilon> > 0 then (if x = 0 then 0 else let xpos = abs x in sqrt_approx_main_impl \<epsilon> xpos (xpos + 1)) else 0"


lemma sqrt_approx: assumes \<epsilon>: "\<epsilon> > 0"
  shows "\<bar>sqrt_approx \<epsilon> x * sqrt_approx \<epsilon> x - \<bar>x\<bar>\<bar> < \<epsilon>"
proof (cases "x = 0")
  case True
  with \<epsilon> show ?thesis unfolding sqrt_approx_def by auto
next
  case False
  let ?x = "\<bar>x\<bar>" 
  let ?sqrti = "sqrt_approx_main_impl \<epsilon> ?x (?x + 1)"
  let ?sqrt = "sqrt_approximation.sqrt_approx_main \<epsilon> ?x (?x + 1)"
  def sqrt \<equiv> ?sqrt
  from False have x: "?x > 0" "?x + 1 > 0" by auto
  interpret sqrt_approximation \<epsilon> ?x
    by (unfold_locales, insert x \<epsilon>, auto)
  from False \<epsilon> have "sqrt_approx \<epsilon> x = ?sqrti" unfolding sqrt_approx_def by (simp add: Let_def)
  also have "?sqrti = ?sqrt"
    by (rule sqrt_approx_main_impl, auto)
  finally have id: "sqrt_approx \<epsilon> x = sqrt" unfolding sqrt_def .
  have sqrt: "sqrt * sqrt > ?x \<and> sqrt * sqrt - ?x < \<epsilon>" unfolding sqrt_def
    by (rule sqrt_approx_main_sound[OF x(2)], insert x mult_pos_pos[OF x(1) x(1)], auto simp: field_simps)
  show ?thesis unfolding id using sqrt by auto
qed

section {* Some tests *}

text {* Testing executabity and show that sqrt 2 is irrational *}
lemma "\<not> (\<exists> i :: rat. i * i = 2)"
proof -
  have "set (sqrt_rat 2) = {}" by eval
  thus ?thesis by simp
qed

text {* Testing speed *}
lemma "\<not> (\<exists> i :: int. i * i = 1234567890123456789012345678901234567890)"
proof -
  have "set (sqrt_int 1234567890123456789012345678901234567890) = {}" by eval
  thus ?thesis by simp
qed

text {* The following test *}

value "let \<epsilon> = 1 / 100000000 :: rat; s = sqrt_approx \<epsilon> 2 in (s, s * s - 2, \<bar>s * s - 2\<bar> < \<epsilon>)"

text {* results in (1.4142135623731116, 4.738200762148612e-14, True). *}
 
end
