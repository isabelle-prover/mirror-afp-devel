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
imports Rat 
begin

section Introduction

text {*
  This theory provides executable algorithms for computing square-roots of numbers which
  are all based on the Babylonian method (which is also known as Heron's method or Newton's method).
  
  For integers / naturals / rationals precise algorithms are given, i.e., here $sqrt\ x$ delivers
  a list of all integers / naturals / rationals $y$ where $y^2 = x$. 
  To this end, the Babylonian method has been adapted by using integer-divisions.

  In addition to the precise algorithms, we also provide one approximation algorithm for 
  arbitrary linear ordered fields, where some number $y$ is computed such that
  @{term "abs(y^2 - x) < \<epsilon>"}.

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

function sqrt_babylon_int_main :: "int \<Rightarrow> int \<Rightarrow> int option" where 
  "sqrt_babylon_int_main x n = (if (x < 0 \<or> n < 0) then None else (if x * x \<le> n then (if x * x = n then Some x else None)
    else sqrt_babylon_int_main ((n div x + x) div 2) n))"
    by pat_completeness auto

text {* For the executable algorithm we omit the guard and use a let-construction *}

partial_function (tailrec) sqrt_int_main :: "int \<Rightarrow> int \<Rightarrow> int option" where 
  [code]: "sqrt_int_main x n = (let x2 = x * x in if x2 \<le> n then (if x2 = n then Some x else None)
    else sqrt_int_main ((n div x + x) div 2) n)"

text {* Once we have proven soundness of @{const sqrt_babylon_int_main} and equivalence to @{const sqrt_int_main}, it
  is easy to assemble the following algorithm which computes all square roots for arbitrary integers. *}

definition sqrt_int :: "int \<Rightarrow> int list" where 
  "sqrt_int x \<equiv> if x < 0 then [] else case sqrt_int_main x x of Some y \<Rightarrow> if y = 0 then [0] else [y,-y] | None \<Rightarrow> []"

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

lemma square_int_pos_inj: assumes x: "0 \<le> (x :: int)" and y: "0 \<le> y" 
  and id: "x * x = y * y"
  shows "x = y"
proof -
  from square_int_pos_mono[OF x y] id have xy: "x \<le> y" by auto
  from square_int_pos_mono[OF y x] id have yx: "y \<le> x" by auto
  from xy yx show ?thesis by auto
qed
    
lemma mod_div_equality_int: "(n :: int) div x * x = n - n mod x"
  using mod_div_equality[of n x] by arith

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
We additionally prove that the result is always positive, which poses no overhead and allows to share
the inductive proof.  
 *}
lemma sqrt_int_main_babylon_pos: "x \<ge> 0 \<Longrightarrow> n \<ge> 0 \<Longrightarrow> sqrt_int_main x n = sqrt_babylon_int_main x n \<and> (sqrt_int_main x n = Some y \<longrightarrow> y \<ge> 0)"
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

lemma sqrt_int_main_pos: "x \<ge> 0 \<Longrightarrow> n \<ge> 0 \<Longrightarrow> sqrt_int_main x n = Some y \<Longrightarrow> y \<ge> 0" 
  using sqrt_int_main_babylon_pos by blast

text {* Soundness of @{const sqrt_babylon_int_main} is trivial. *}
lemma sqrt_babylon_int_main_sound: "sqrt_babylon_int_main x n = Some y \<Longrightarrow> y * y = n"
proof (induct x n rule: sqrt_babylon_int_main.induct)
  case (1 x n)
  from 1(2) have not: "\<not> (x < 0 \<or> n < 0)" by (cases "x < 0 \<or> n < 0", auto)
  show ?case
  proof (cases "x * x \<le> n")
    case False
    with 1(1)[OF not this] not 1(2) show ?thesis by simp
  next
    case True
    thus ?thesis using 1(2) not by (cases "x * x = n", auto)
  qed
qed

text {* For completeness, we first need the following crucial inquality, which would be
  trivial if one would use standard division instead of integer division.
  (Proving this equation has required a significant amount of time during the development,
   as we first made several proof attemps which have been dead ends.) *}
lemma square_inequality: "2 * x * y \<le> x * x div y * y + y * (y :: int)"
proof -
  have pos: "0 \<le> (y - x) * (y - x) div y * y" 
    by (metis transfer_nat_int_function_closures div_0 eq_iff linear neg_imp_zdiv_nonneg_iff not_le split_mult_pos_le)
  have "x * x div y * y + y * y = 
    ((y - x) * (y - x) + y*(2*x - y)) div y * y + y * y" by (simp add: field_simps)
  also have "\<dots> = 2*y*x - y*y + (y-x)*(y-x) div y * y + y * y"
  proof (cases "y = 0")
    case False
    show ?thesis unfolding div_mult_self2[OF False] by (auto simp: field_simps)
  qed simp
  also have "\<dots> = 2*x*y + (y-x)*(y-x) div y * y" by (auto simp: field_simps)
  also have "\<dots> \<ge> 2*x*y" using pos by auto
  finally show ?thesis .
qed 
  
lemma sqrt_babylon_int_main_complete: assumes x0: "x \<ge> 0"
  shows "x * x = n \<Longrightarrow> y * y \<ge> n \<Longrightarrow> y \<ge> 0 \<Longrightarrow> n \<ge> 0 \<Longrightarrow> sqrt_babylon_int_main y n = Some x"
proof (induct y n rule: sqrt_babylon_int_main.induct)
  case (1 y n)
  have nx: "n = x * x" and xn: "x * x = n" using 1(2) by auto
  from 1(4) have y0: "y \<ge> 0" .
  from 1(5) have n0: "n \<ge> 0" .
  let ?sqrt = "sqrt_babylon_int_main"
  from y0 n0 have not: "\<not> (y < 0 \<or> n < 0)" by auto
  show ?case
  proof (cases "y * y \<le> n")
    case False    
    let ?sy = "(n div y + y) div 2"
    let ?sx = "(n div x + x) div 2"
    from False y0 n0 have id: "?sqrt y n = ?sqrt ?sy n" by auto
    from False xn have "x * x \<le> y * y" by auto
    from this[unfolded square_int_pos_mono[OF x0 y0]] have xy: "x \<le> y" by auto
    have sx0: "?sx \<ge> 0" using transfer_nat_int_function_closures n0 x0 by auto
    have sy0: "?sy \<ge> 0" using transfer_nat_int_function_closures n0 y0 by auto
    show ?thesis unfolding id
    proof (rule 1(1)[OF not False xn _ sy0 n0])
      have "n = ?sx * ?sx" unfolding nx by simp
      also have "\<dots> \<le> ?sy * ?sy" unfolding square_int_pos_mono[OF sx0 sy0]
      proof -
        have "?sx = 2 * x div 2" unfolding nx by simp
        also have "\<dots> \<le> ?sy"
        proof (rule zdiv_mono1)
          show "2 * x \<le> n div y + y" 
          proof (cases "y = 0")
            case True 
            thus ?thesis using xy by auto
          next
            case False
            with y0 have y: "y > 0" by auto
            show ?thesis
            proof (rule mult_right_le_imp_le[OF _ y], unfold nx)
              show "2 * x * y \<le> (x * x div y + y) * y" using square_inequality by (auto simp: field_simps)
            qed
          qed
        qed simp
        finally show "?sx \<le> ?sy" .
      qed
      finally
      show "n \<le> ?sy * ?sy" . 
    qed
  next
    case True
    with 1(3) have yn: "y * y = n" by auto
    with nx have "x * x = y * y" by auto
    from square_int_pos_inj[OF x0 y0 this] yn not show ?thesis by auto
  qed
qed

text {* Having proven soundness and completeness of @{const sqrt_babylon_int_main},
  it is easy to prove soundness of @{const sqrt_int}. *}

lemma sqrt_int[simp]: "set (sqrt_int x) = {y. y * y = x}"
proof -
  note d = sqrt_int_def
  show ?thesis
  proof (cases "x < 0 \<or> sqrt_int_main x x = None")
    case True
    hence left: "set (sqrt_int x) = {}" unfolding d by (cases "x < 0", auto) 
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
      from sqrt_babylon_int_main_complete[OF y x int_lesseq_square x0 x0] True
      have False unfolding sqrt_int_main[OF x0 x0] by auto
    }
    with left show ?thesis by auto
  next
    case False
    then obtain y where Some: "sqrt_int_main x x = Some y" and x: "x \<ge> 0" by auto
    hence left: "set (sqrt_int x) = {y,-y}" unfolding d by (cases "y = 0", auto)
    have "\<exists> z. z \<ge> 0 \<and> {y,-y} = {z,-z}"
    proof (cases "y \<ge> 0")
      case False
      show ?thesis by (rule exI[of _ "-y"], insert False, auto)
    qed auto
    then obtain z where z: "z \<ge> 0" and yz: "{y,-y} = {z,-z}" by auto
    from sqrt_babylon_int_main_sound[OF Some[unfolded sqrt_int_main[OF x x]]] have y: "y * y = x" "-y * -y = x" by auto
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
  from False x obtain y where main: "sqrt_int_main x x = Some y" unfolding d
    by (cases "sqrt_int_main x x", auto)
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
