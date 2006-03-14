(*  Title:       The Cauchy-Schwarz Inequality
    ID:          $Id: CauchySchwarz.thy,v 1.2 2006-03-14 20:51:52 lsf37 Exp $
    Author:      Benjamin Porter <Benjamin.Porter@gmail.com>, 2006
    Maintainer:  Benjamin Porter <Benjamin.Porter@gmail.com>
*)

header {*The Cauchy-Schwarz Inequality*}

theory CauchySchwarz
imports Complex_Main
begin

(*<*)

(* Some basic results that don't need to be in the final doc ..*)

lemma real_sq:
  "(a::real)*a = a^2"
proof -
  have "2 = Suc 1" by simp
  hence "a^2 = a^(Suc 1)"
    apply -
    apply (erule subst)
    by simp
  also have "\<dots> = a*(a^1)" by simp
  also have "\<dots> = a*a" by simp
  finally have "a^2 = a*a" by auto
  thus ?thesis by simp
qed

lemma real_mult_wkorder:
  fixes x::real
  assumes xge0: "0 \<le> x" and yge0: "0 \<le> y"
  shows "0 \<le> x * y"
proof cases
  assume "x = 0"
  thus ?thesis by simp
next
  assume "x\<noteq>0"
  with xge0 have xgt0: "x > 0" by simp
  show ?thesis
  proof cases
    assume "y = 0"
    thus ?thesis by simp
  next
    assume "y \<noteq> 0"
    with yge0 have "y > 0" by simp
    with xgt0 have "x*y > 0" by (rule real_mult_order)
    thus ?thesis by simp
  qed
qed

lemma real_mult_order2:
  fixes c::real
  assumes c0: "0 \<le> c"
  and xy: "x \<le> y"
  shows "c*x \<le> c*y"
proof cases
  assume "0 = c"
  thus ?thesis by auto
next
  assume "0 \<noteq> c"
  with c0 have "0 < c" by simp
  with xy show ?thesis by simp
qed

lemma real_sq_order:
  fixes x::real
  assumes xgt0: "0 \<le> x" and ygt0: "0 \<le> y" and sq: "x^2 \<le> y^2"
  shows "x \<le> y"
proof (rule ccontr)
  assume "\<not>(x \<le> y)"
  then have ylx: "y < x" by simp
  hence "y \<le> x" by simp
  with xgt0 have "x*y \<le> x*x" by (rule real_mult_order2)
  moreover
  have "\<not> (y = 0)"
  proof
    assume "y = 0"
    with ylx have xg0: "0 < x" by simp
    from xg0 xg0 have "0 < x*x" by (rule real_mult_order)
    moreover have "y*y = 0" by simp
    ultimately show False using sq by auto
  qed
  with ygt0 have "0 < y" by simp
  with ylx have "y*y < x*y" by auto
  ultimately have "y*y < x*x" by simp
  with sq show False by (auto simp add: real_sq)
qed

lemma real_add_mult_distrib2:
  fixes x::real
  shows "x*(y+z) = x*y + x*z"
proof -
  have "x*(y+z) = (y+z)*x" by simp
  also have "\<dots> = y*x + z*x" by (rule real_add_mult_distrib)
  also have "\<dots> = x*y + x*z" by simp
  finally show ?thesis .
qed

lemma real_add_mult_distrib_ex:
  fixes x::real
  shows "(x+y)*(z+w) = x*z + y*z + x*w + y*w"
proof -
  have "(x+y)*(z+w) = x*(z+w) + y*(z+w)" by (rule real_add_mult_distrib)
  also have "\<dots> = x*z + x*w + y*z + y*w" by (simp add: real_add_mult_distrib2)
  finally show ?thesis by simp
qed

lemma real_sub_mult_distrib_ex:
  fixes x::real
  shows "(x-y)*(z-w) = x*z - y*z - x*w + y*w"
proof -
  have zw: "(z-w) = (z+ -w)" by simp
  have "(x-y)*(z-w) = (x + -y)*(z-w)" by simp
  also have "\<dots> = x*(z-w) + -y*(z-w)" by (rule real_add_mult_distrib)
  also from zw have "\<dots> = x*(z+ -w) + -y*(z+ -w)"
    apply -
    apply (erule subst)
    by simp
  also have "\<dots> = x*z + x*-w + -y*z + -y*-w" by (simp add: real_add_mult_distrib2)
  finally show ?thesis by simp
qed

lemma double_sum_expand:
  fixes f::"nat \<Rightarrow> real"
  shows "(\<Sum>j\<in>{1..n}. f j)*(\<Sum>j\<in>{1..n}. g j) = (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. f k * g j))"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n)
  {
    assume nz: "n = 0"
    then have
      "(\<Sum>j\<in>{1..Suc n}. f j)*(\<Sum>j\<in>{1..Suc n}. g j) = f 1 * g 1" by simp
    moreover from nz have
      "(\<Sum>k\<in>{1..Suc n}. (\<Sum>j\<in>{1..Suc n}. (f k)*(g j))) = f 1 * g 1" by auto
    ultimately have ?case by simp
  }
  moreover
  {
    assume "\<not>(n=0)"
    then have nge1: "n \<ge> 1" by simp
    hence sn: "Suc n > 1" by simp

    let ?f = "\<Sum>j\<in>{1..n}. f j" and ?g = "\<Sum>j\<in>{1..n}. g j"

    from sn setsum_cl_ivl_Suc have "(\<Sum>j\<in>{1..Suc n}. f j) = ?f + f (Suc n)" by auto
    moreover
    from sn setsum_cl_ivl_Suc have "(\<Sum>j\<in>{1..Suc n}. g j) = ?g + g (Suc n)" by auto
    ultimately have
      "(\<Sum>j\<in>{1..Suc n}. f j)*(\<Sum>j\<in>{1..Suc n}. g j) = (?f + f (Suc n))*(?g + g (Suc n))" by simp
    also have
      "\<dots> = ?f * ?g + ?f*(g (Suc n)) + (f (Suc n))*?g + (f (Suc n))*(g (Suc n))"
      by (auto simp add: real_add_mult_distrib_ex)
    also have
      "\<dots> = (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. (f k)*(g j))) +
      ?f*(g (Suc n)) + (f (Suc n))*?g + (f (Suc n))*(g (Suc n))" using Suc by simp
    also have
      "\<dots> = (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. (f k)*(g j))) +
      (\<Sum>j\<in>{1..n}. f j * g (Suc n)) + ?g * (f (Suc n)) + (f (Suc n))*(g (Suc n))"
      by (auto simp add: setsum_mult real_mult_commute)
    also have
      "\<dots> = (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. (f k)*(g j)) +
      (f k * g (Suc n))) + (?g * f (Suc n)) + (f (Suc n))*(g (Suc n))"
      by (auto simp add: setsum_addf [symmetric])
    also have
      "\<dots> = (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..(Suc n)}. (f k)*(g j))) +
      (\<Sum>j\<in>{1..n}. g j)*(f (Suc n)) + g(Suc n)*(f (Suc n))" by simp
    also have
      "\<dots> = (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..(Suc n)}. (f k)*(g j))) +
      (\<Sum>j\<in>{1..n}. g j * f (Suc n)) + g(Suc n)*(f (Suc n))"
      by (auto simp add: setsum_mult real_mult_commute)
    also from sn setsum_cl_ivl_Suc have
      "\<dots> = (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..(Suc n)}. (f k)*(g j))) +
      (\<Sum>j\<in>{1..Suc n}. (g j)*(f (Suc n)))" by auto
    also from sn setsum_cl_ivl_Suc have
      "\<dots> = (\<Sum>k\<in>{1..Suc n}. (\<Sum>j\<in>{1..(Suc n)}. (f k)*(g j)))"
      by (auto simp add: real_mult_commute)
    finally have ?case .
  }
  ultimately show ?case by (rule case_split_thm)
qed

lemma real_sq_exp:
  fixes x::real
  shows "(x*y)^2 = x^2 * y^2"
proof -
  have "(x*y)^2 = (x*y)*(x*y)" by (simp add:real_sq)
  also have "\<dots> = (x*x)*(y*y)" by simp
  also have "\<dots> = x^2 * y^2" by (simp add: real_sq)
  finally show ?thesis .
qed

lemma real_diff_exp:
  fixes x::real
  shows "(x - y)^2 = x^2 + y^2 - 2*x*y"
proof -
  have "(x - y)^2 = (x-y)*(x-y)" by (simp only: real_sq)
  also from real_sub_mult_distrib_ex have "\<dots> = x*x - x*y - y*x + y*y" by simp
  finally show ?thesis by (auto simp add: real_sq)
qed

lemma double_sum_equiv:
  fixes f::"nat \<Rightarrow> real"
  shows
  "(\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. f k * g j)) =
   (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. f j * g k))"
proof -
  have "(\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. (f k) * (g j))) = (\<Sum>j\<in>{1..n}. f j)*(\<Sum>j\<in>{1..n}. g j)"
    by (simp only: double_sum_expand)
  also have "\<dots> = (\<Sum>j\<in>{1..n}. g j)*(\<Sum>j\<in>{1..n}. f j)"
    by simp
  also have "\<dots> = (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. g k * f j))"
    by (simp only: double_sum_expand)
  finally show ?thesis by (simp add: real_mult_commute)
qed

(*>*)



section {* Abstract *}

text {* The following document presents a formalised proof of the
Cauchy-Schwarz Inequality for the specific case of $R^n$. The system
used is Isabelle/Isar. 

{\em Theorem:} Take $V$ to be some vector space possessing a norm and
inner product, then for all $a,b \in V$ the following inequality
holds: @{text "\<bar>a\<cdot>b\<bar> \<le> \<parallel>a\<parallel>*\<parallel>b\<parallel>"}. Specifically, in the Real case, the
norm is the Euclidean length and the inner product is the standard dot
product. *}


section {* Formal Proof *}

subsection {* Vector, Dot and Norm definitions. *}

text {* This section presents definitions for a real vector type, a
dot product function and a norm function. *}

subsubsection {* Vector *}

text {* We now define a vector type to be a tuple of (function,
length). Where the function is of type @{typ "nat\<Rightarrow>real"}. We also
define some accessor functions and appropriate syntax translations. *}

types vector = "(nat\<Rightarrow>real) * nat";

constdefs ith :: "vector \<Rightarrow> nat \<Rightarrow> real" ("((_)\<^sub>_)" [80,100] 100)
  "ith v i \<equiv> (fst v) i"
  vlen :: "vector \<Rightarrow> nat"
  "vlen v \<equiv> (snd v)"

text {* Now to access the second element of some vector $v$ the syntax
is $v_2$. *}

subsubsection {* Dot and Norm *}

text {* We now define the dot product and norm operations. *}

constdefs dot :: "vector \<Rightarrow> vector \<Rightarrow> real" (infixr "\<cdot>" 60)
  "dot a b \<equiv> (\<Sum>j\<in>{1..(vlen a)}. a\<^sub>j*b\<^sub>j)"
  norm :: "vector \<Rightarrow> real"                  ("\<parallel>_\<parallel>" 100)
  "norm v \<equiv> sqrt (\<Sum>j\<in>{1..(vlen v)}. v\<^sub>j^2)"

syntax(HTML output)
  "norm" :: "vector => real" ("||_||" 100)

text {* Another definition of the norm is @{term "\<parallel>v\<parallel> = sqrt
(v\<cdot>v)"}. We show that our definition leads to this one. *}

lemma norm_dot:
 "\<parallel>v\<parallel> = sqrt (v\<cdot>v)"
proof -
  have "sqrt (v\<cdot>v) = sqrt (\<Sum>j\<in>{1..(vlen v)}. v\<^sub>j*v\<^sub>j)" by (unfold dot_def, simp)
  also with real_sq have "\<dots> = sqrt (\<Sum>j\<in>{1..(vlen v)}. v\<^sub>j^2)" by simp
  also have "\<dots> = \<parallel>v\<parallel>" by (unfold norm_def, simp)
  finally show ?thesis ..
qed

text {* A further important property is that the norm is never negative. *}

lemma norm_pos:
  "\<parallel>v\<parallel> \<ge> 0"
proof -
  have "\<forall>j. v\<^sub>j^2 \<ge> 0" by (unfold ith_def, auto)
  hence "\<forall>j\<in>{1..(vlen v)}. v\<^sub>j^2 \<ge> 0" by simp
  with setsum_nonneg have "(\<Sum>j\<in>{1..(vlen v)}. v\<^sub>j^2) \<ge> 0" .
  with real_sqrt_ge_zero have "sqrt (\<Sum>j\<in>{1..(vlen v)}. v\<^sub>j^2) \<ge> 0" .
  thus ?thesis by (unfold norm_def)
qed

text {* We now prove an intermediary lemma regarding double summation. *}

lemma double_sum_aux:
  fixes f::"nat \<Rightarrow> real"
  shows
  "(\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. f k * g j)) =
   (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. (f k * g j + f j * g k) / 2))"
proof -
  have
    "2 * (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. f k * g j)) =
    (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. f k * g j)) +
    (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. f k * g j))"
    by simp
  also have
    "\<dots> =
    (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. f k * g j)) +
    (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. f j * g k))"
    by (simp only: double_sum_equiv)
  also have
    "\<dots> =
    (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. f k * g j + f j * g k))"
    by (auto simp add: setsum_addf)
  finally have
    "2 * (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. f k * g j)) =
    (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. f k * g j + f j * g k))" .
  hence
    "(\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. f k * g j)) =
     (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. (f k * g j + f j * g k)))*(1/2)"
    by auto
  also have
    "\<dots> =
     (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. (f k * g j + f j * g k)*(1/2)))"
    by (simp add: setsum_mult real_mult_commute)
  finally show ?thesis by (auto simp add: inverse_eq_divide)
qed

text {* The final theorem can now be proven. It is a simple forward
proof that uses properties of double summation and the preceding
lemma.  *}

theorem CauchySchwarzReal:
  fixes x::vector
  assumes "vlen x = vlen y"
  shows "\<bar>x\<cdot>y\<bar> \<le> \<parallel>x\<parallel>*\<parallel>y\<parallel>"
proof -
  have "0 \<le> \<bar>x\<cdot>y\<bar>" by simp
  moreover have "0 \<le> \<parallel>x\<parallel>*\<parallel>y\<parallel>"
    by (auto simp add: norm_pos intro: mult_nonneg_nonneg)
  moreover have "\<bar>x\<cdot>y\<bar>^2 \<le> (\<parallel>x\<parallel>*\<parallel>y\<parallel>)^2"
  proof -
    txt {* We can rewrite the goal in the following form ...*}
    have "(\<parallel>x\<parallel>*\<parallel>y\<parallel>)^2 - \<bar>x\<cdot>y\<bar>^2 \<ge> 0"
    proof -
      obtain n where nx: "n = vlen x" by simp
      hence ny: "n = vlen y" by simp
      {
        txt {* Some preliminary simplification rules. *}
        have "\<forall>j\<in>{1..n}. x\<^sub>j^2 \<ge> 0" by simp
        hence "(\<Sum>j\<in>{1..n}. x\<^sub>j^2) \<ge> 0" by (rule setsum_nonneg)
        hence xp: "(sqrt (\<Sum>j\<in>{1..n}. x\<^sub>j^2))^2 = (\<Sum>j\<in>{1..n}. x\<^sub>j^2)"
          by (rule real_sqrt_pow2)

        have "\<forall>j\<in>{1..n}. y\<^sub>j^2 \<ge> 0" by simp
        hence "(\<Sum>j\<in>{1..n}. y\<^sub>j^2) \<ge> 0" by (rule setsum_nonneg)
        hence yp: "(sqrt (\<Sum>j\<in>{1..n}. y\<^sub>j^2))^2 = (\<Sum>j\<in>{1..n}. y\<^sub>j^2)"
          by (rule real_sqrt_pow2)

        txt {* The main result of this section is that @{text
        "(\<parallel>x\<parallel>*\<parallel>y\<parallel>)^2"} can be written as a double sum. *}
        have
          "(\<parallel>x\<parallel>*\<parallel>y\<parallel>)^2 = \<parallel>x\<parallel>^2 * \<parallel>y\<parallel>^2"
          by (simp add: real_sq_exp)
        also from nx ny have
          "\<dots> = (sqrt (\<Sum>j\<in>{1..n}. x\<^sub>j^2))^2 * (sqrt (\<Sum>j\<in>{1..n}. y\<^sub>j^2))^2"
          by (unfold norm_def, auto)
        also from xp yp have
          "\<dots> = (\<Sum>j\<in>{1..n}. x\<^sub>j^2)*(\<Sum>j\<in>{1..n}. y\<^sub>j^2)"
          by simp
        also from double_sum_expand have
          "\<dots> = (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. (x\<^sub>k^2)*(y\<^sub>j^2)))" .
        finally have
          "(\<parallel>x\<parallel>*\<parallel>y\<parallel>)^2 = (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. (x\<^sub>k^2)*(y\<^sub>j^2)))" .
      }
      moreover
      {
        txt {* We also show that @{text "\<bar>x\<cdot>y\<bar>^2"} can be expressed as a double sum.*}
        have
          "\<bar>x\<cdot>y\<bar>^2 = (x\<cdot>y)^2"
          by simp
        also from nx have
          "\<dots> = (\<Sum>j\<in>{1..n}. x\<^sub>j*y\<^sub>j)^2"
          by (unfold dot_def, simp)
        also from real_sq have
          "\<dots> = (\<Sum>j\<in>{1..n}. x\<^sub>j*y\<^sub>j)*(\<Sum>j\<in>{1..n}. x\<^sub>j*y\<^sub>j)"
          by simp
        also from double_sum_expand have
          "\<dots> = (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. (x\<^sub>k*y\<^sub>k)*(x\<^sub>j*y\<^sub>j)))"
          by simp
        finally have
          "\<bar>x\<cdot>y\<bar>^2 = (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. (x\<^sub>k*y\<^sub>k)*(x\<^sub>j*y\<^sub>j)))" .
      }
      txt {* We now manipulate the double sum expressions to get the
      required inequality. *}
      ultimately have
        "(\<parallel>x\<parallel>*\<parallel>y\<parallel>)^2 - \<bar>x\<cdot>y\<bar>^2 =
         (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. (x\<^sub>k^2)*(y\<^sub>j^2))) -
         (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. (x\<^sub>k*y\<^sub>k)*(x\<^sub>j*y\<^sub>j)))"
        by simp
      also have
        "\<dots> =
         (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. ((x\<^sub>k^2*y\<^sub>j^2) + (x\<^sub>j^2*y\<^sub>k^2))/2)) -
         (\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. (x\<^sub>k*y\<^sub>k)*(x\<^sub>j*y\<^sub>j)))"
        by (simp only: double_sum_aux)
      also have
        "\<dots> =
         (\<Sum>k\<in>{1..n}.  (\<Sum>j\<in>{1..n}. ((x\<^sub>k^2*y\<^sub>j^2) + (x\<^sub>j^2*y\<^sub>k^2))/2 - (x\<^sub>k*y\<^sub>k)*(x\<^sub>j*y\<^sub>j)))"
        by (auto simp add: setsum_subtractf)
      also have
        "\<dots> =
         (\<Sum>k\<in>{1..n}.  (\<Sum>j\<in>{1..n}. (inverse 2)*2*
         (((x\<^sub>k^2*y\<^sub>j^2) + (x\<^sub>j^2*y\<^sub>k^2))*(1/2) - (x\<^sub>k*y\<^sub>k)*(x\<^sub>j*y\<^sub>j))))"
        by auto
      also have
        "\<dots> =
         (\<Sum>k\<in>{1..n}.  (\<Sum>j\<in>{1..n}. (inverse 2)*(2*
        (((x\<^sub>k^2*y\<^sub>j^2) + (x\<^sub>j^2*y\<^sub>k^2))*(1/2) - (x\<^sub>k*y\<^sub>k)*(x\<^sub>j*y\<^sub>j)))))"
        by (simp only: real_mult_assoc)
      also have
        "\<dots> =
         (\<Sum>k\<in>{1..n}.  (\<Sum>j\<in>{1..n}. (inverse 2)*
        ((((x\<^sub>k^2*y\<^sub>j^2) + (x\<^sub>j^2*y\<^sub>k^2))*2*(inverse 2) - 2*(x\<^sub>k*y\<^sub>k)*(x\<^sub>j*y\<^sub>j)))))"
        by (auto simp add: real_add_mult_distrib real_mult_assoc mult_ac)
      also have
        "\<dots> =
        (\<Sum>k\<in>{1..n}.  (\<Sum>j\<in>{1..n}. (inverse 2)*
        ((((x\<^sub>k^2*y\<^sub>j^2) + (x\<^sub>j^2*y\<^sub>k^2)) - 2*(x\<^sub>k*y\<^sub>k)*(x\<^sub>j*y\<^sub>j)))))"
        by (simp only: real_mult_assoc, simp)
      also have
        "\<dots> =
         (inverse 2)*(\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}.
         (((x\<^sub>k^2*y\<^sub>j^2) + (x\<^sub>j^2*y\<^sub>k^2)) - 2*(x\<^sub>k*y\<^sub>k)*(x\<^sub>j*y\<^sub>j))))"
        by (simp only: setsum_mult)
      also have
        "\<dots> =
         (inverse 2)*(\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. (x\<^sub>k*y\<^sub>j - x\<^sub>j*y\<^sub>k)^2))"
        by (simp only: real_diff_exp real_sq_exp, auto simp add: mult_ac)
      also have "\<dots> \<ge> 0"
      proof -
        {
          fix k::nat
          have "\<forall>j\<in>{1..n}. (x\<^sub>k*y\<^sub>j - x\<^sub>j*y\<^sub>k)^2 \<ge> 0" by simp
          hence "(\<Sum>j\<in>{1..n}. (x\<^sub>k*y\<^sub>j - x\<^sub>j*y\<^sub>k)^2) \<ge> 0" by (rule setsum_nonneg)
        }
        hence "\<forall>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. (x\<^sub>k*y\<^sub>j - x\<^sub>j*y\<^sub>k)^2) \<ge> 0" by simp
        hence "(\<Sum>k\<in>{1..n}. (\<Sum>j\<in>{1..n}. (x\<^sub>k*y\<^sub>j - x\<^sub>j*y\<^sub>k)^2)) \<ge> 0"
          by (rule setsum_nonneg)
        thus ?thesis by simp
      qed
      finally show "(\<parallel>x\<parallel>*\<parallel>y\<parallel>)^2 - \<bar>x\<cdot>y\<bar>^2 \<ge> 0" .
    qed
    thus ?thesis by simp
  qed
  ultimately show ?thesis by (rule real_sq_order)
qed


end
