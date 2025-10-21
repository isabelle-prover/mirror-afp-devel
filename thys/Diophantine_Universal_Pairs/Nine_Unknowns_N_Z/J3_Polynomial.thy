theory J3_Polynomial
  imports Main Algebra_Basics Polynomials.More_MPoly_Type "../MPoly_Utils/More_More_MPoly_Type"
    "../Coding/Utils"
  abbrevs pA1 = \<A>\<^sub>1
      and pA2 = \<A>\<^sub>2
      and pA3 = \<A>\<^sub>3
      and pX3 = \<X>\<^sub>3
begin

subsection \<open>The $J_3$ polynomial\<close>

locale section5_given
begin

definition x :: "int mpoly" where "x \<equiv> Var 0"

definition \<A>\<^sub>1 :: "int mpoly" where "\<A>\<^sub>1 \<equiv> Var 1"
definition \<A>\<^sub>2 :: "int mpoly" where "\<A>\<^sub>2 \<equiv> Var 2"
definition \<A>\<^sub>3 :: "int mpoly" where "\<A>\<^sub>3 \<equiv> Var 3"
definition \<X>\<^sub>3 :: "int mpoly" where "\<X>\<^sub>3 \<equiv> Const 1 + \<A>\<^sub>1^2 + \<A>\<^sub>2^2 + \<A>\<^sub>3^2"

lemmas defs = x_def \<A>\<^sub>1_def \<A>\<^sub>2_def \<A>\<^sub>3_def \<X>\<^sub>3_def

text \<open>Functions on triples\<close>

fun fst3:: "'a\<times>'a\<times>'a \<Rightarrow> 'a" where "fst3 (a, b, c) = a"
fun snd3:: "'a\<times>'a\<times>'a \<Rightarrow> 'a" where "snd3 (a, b, c) = b"
fun trd3:: "'a\<times>'a\<times>'a \<Rightarrow> 'a" where "trd3 (a, b, c) = c"
fun fun3:: "'a\<times>'a\<times>'a\<Rightarrow>nat\<Rightarrow>'a::zero" where 
  "fun3 (a,b,c) k = (if k=1 then a else (if k=2 then b else (if k=3 then c else 0)))"
(* Turns a triple into a function nat\<Rightarrow>'a where  f x = 0 if x > 3*)

lemma fun3_1_eq_fst3: "fun3 a 1 = fst3 a" by (metis fst3.elims fun3.simps)
lemma fun3_2_eq_snd3: "fun3 a 2 = snd3 a" by (metis even_plus_one_iff fun3.simps one_dvd snd3.elims)
lemma fun3_3_eq_trd3: "fun3 a 3 = trd3 a"
  by (metis Suc_eq_plus1 add_cancel_right_left eval_nat_numeral(3) even_plus_one_iff fun3.simps 
      numeral_eq_Suc trd3.elims zero_eq_add_iff_both_eq_0)

lemmas fun3_def = fun3_1_eq_fst3 fun3_2_eq_snd3 fun3_3_eq_trd3

definition J3 :: "int mpoly" where 
  "J3 = ((x^2+\<A>\<^sub>1+\<A>\<^sub>2*\<X>\<^sub>3^2-\<A>\<^sub>3*\<X>\<^sub>3^4)^2 + 4*x^2*\<A>\<^sub>1 - 4*x^2*\<A>\<^sub>2*\<X>\<^sub>3^2 - 4*\<A>\<^sub>1*\<A>\<^sub>2*\<X>\<^sub>3^2)^2
          - \<A>\<^sub>1 * ((4*x*(x^2+\<A>\<^sub>1+\<A>\<^sub>2*\<X>\<^sub>3^2 - \<A>\<^sub>3*\<X>\<^sub>3^4) -  8*x*\<A>\<^sub>2*\<X>\<^sub>3^2))^2"

definition r where "r = MPoly_Type.degree J3 0"

lemma J3_vars: "vars J3 \<subseteq> {0, 1, 2, 3}"
  unfolding J3_def defs diff_conv_add_uminus
  by mpoly_vars

text \<open>Key lemma about J3\<close>

(* The domain of possible values for \<epsilon> *)
definition "\<E> \<equiv> {-1, 1::int}\<times>{-1, 1::int}\<times>{-1, 1::int}"

lemma J3_fonction_eq_polynomial:
  fixes f::"nat\<Rightarrow>int"
  defines "X \<equiv> 1 + (f 1)^2 + (f 2)^2 + (f 3)^2" 
  shows "of_int (insertion f J3) =
          (\<Prod>\<epsilon>\<in>\<E>. of_int (f 0)
                  + fst3 \<epsilon> * cpx_sqrt(f 1)
                  + snd3 \<epsilon> * cpx_sqrt(f 2) * of_int X
                  + trd3 \<epsilon> * cpx_sqrt(f 3) * of_int (X^2))"
proof -
  define inser where "inser = insertion f"
  have inser_X: "inser \<X>\<^sub>3 = X"
    unfolding inser_def X_def defs power2_eq_square by simp
  have "\<E> = {(-1,-1,-1), (-1,-1,1), (-1,1,-1), (-1,1,1), (1,-1,-1), (1,-1,1), (1,1,-1), (1,1,1)}"
    unfolding \<E>_def by force
  hence "(\<Prod>\<epsilon>\<in>\<E>.
      (of_int(f 0) + fst3 \<epsilon> * cpx_sqrt(f 1) + snd3 \<epsilon> * cpx_sqrt(f 2) * of_int X
        + trd3 \<epsilon> * cpx_sqrt(f 3) * of_int (X^2)))
      = (\<Prod>\<epsilon>::int\<times>int\<times>int\<in>{(-1,-1,-1), (-1,-1,1), (-1,1,-1), (-1,1,1), (1,-1,-1), (1,-1,1), (1,1,-1), (1,1,1)}.
      (of_int(f 0) + fst3 \<epsilon> * cpx_sqrt(f 1) + snd3 \<epsilon> * cpx_sqrt(f 2) * of_int X
        + trd3 \<epsilon> * cpx_sqrt(f 3) * of_int (X^2)))" by argo
  also have "...
      = (of_int(f 0) - cpx_sqrt(f 1) - cpx_sqrt(f 2) * of_int X - cpx_sqrt(f 3) * of_int (X^2))
      * (of_int(f 0) - cpx_sqrt(f 1) - cpx_sqrt(f 2) * of_int X + cpx_sqrt(f 3) * of_int (X^2))
      * (of_int(f 0) - cpx_sqrt(f 1) + cpx_sqrt(f 2) * of_int X - cpx_sqrt(f 3) * of_int (X^2))
      * (of_int(f 0) - cpx_sqrt(f 1) + cpx_sqrt(f 2) * of_int X + cpx_sqrt(f 3) * of_int (X^2))
      * (of_int(f 0) + cpx_sqrt(f 1) - cpx_sqrt(f 2) * of_int X - cpx_sqrt(f 3) * of_int (X^2))
      * (of_int(f 0) + cpx_sqrt(f 1) - cpx_sqrt(f 2) * of_int X + cpx_sqrt(f 3) * of_int (X^2))
      * (of_int(f 0) + cpx_sqrt(f 1) + cpx_sqrt(f 2) * of_int X - cpx_sqrt(f 3) * of_int (X^2))
      * (of_int(f 0) + cpx_sqrt(f 1) + cpx_sqrt(f 2) * of_int X + cpx_sqrt(f 3) * of_int (X^2))"
    by simp
  also have "... = ((of_int(f 0) - cpx_sqrt(f 1) - cpx_sqrt(f 2) * of_int X)^2 - (cpx_sqrt(f 3) * of_int (X^2))^2)
      * ((of_int(f 0) - cpx_sqrt(f 1) + cpx_sqrt(f 2) * of_int X)^2 - (cpx_sqrt(f 3) * of_int (X^2))^2)
      * ((of_int(f 0) + cpx_sqrt(f 1) - cpx_sqrt(f 2) * of_int X)^2 - (cpx_sqrt(f 3) * of_int (X^2))^2)
      * ((of_int(f 0) + cpx_sqrt(f 1) + cpx_sqrt(f 2) * of_int X)^2 - (cpx_sqrt(f 3) * of_int (X^2))^2)"
    by algebra
  also have "... = ((of_int(f 0) - cpx_sqrt(f 1) - cpx_sqrt(f 2) * of_int X)^2 - of_int (f 3) * of_int (X^2)^2)
      * ((of_int(f 0) - cpx_sqrt(f 1) + cpx_sqrt(f 2) * of_int X)^2 - of_int (f 3) * of_int (X^2)^2)
      * ((of_int(f 0) + cpx_sqrt(f 1) - cpx_sqrt(f 2) * of_int X)^2 - of_int (f 3) * of_int (X^2)^2)
      * ((of_int(f 0) + cpx_sqrt(f 1) + cpx_sqrt(f 2) * of_int X)^2 - of_int (f 3) * of_int (X^2)^2)"
    using square_sqrt[of "f 3"] power_mult_distrib[of _ _ 2] by (smt (verit, best))
  also have "... = ((of_int(f 0) - cpx_sqrt(f 1) - cpx_sqrt(f 2) * of_int X)^2 - of_int (f 3 * X^4))
      * ((of_int(f 0) - cpx_sqrt(f 1) + cpx_sqrt(f 2) * of_int X)^2 - of_int (f 3 * X^4))
      * ((of_int(f 0) + cpx_sqrt(f 1) - cpx_sqrt(f 2) * of_int X)^2 - of_int (f 3 * X^4))
      * ((of_int(f 0) + cpx_sqrt(f 1) + cpx_sqrt(f 2) * of_int X)^2 - of_int (f 3 * X^4))"
    using power2_eq_square of_int_mult by simp
  also have "... = (of_int(f 0)^2 + cpx_sqrt(f 1)^2 + cpx_sqrt(f 2)^2 * (of_int X)^2 - f 3 * X^4
          - 2 * of_int(f 0) * cpx_sqrt(f 1) - 2 * of_int(f 0) * cpx_sqrt(f 2) * of_int X
          + 2 * cpx_sqrt(f 1) * cpx_sqrt(f 2) * of_int X )
      * (of_int(f 0)^2 + cpx_sqrt(f 1)^2 + cpx_sqrt(f 2)^2 * (of_int X)^2 - f 3 * X^4
          - 2 * of_int(f 0) * cpx_sqrt(f 1) + 2 * of_int(f 0) * cpx_sqrt(f 2) * of_int X
          - 2 * cpx_sqrt(f 1) * cpx_sqrt(f 2) * of_int X )
      * (of_int(f 0)^2 + cpx_sqrt(f 1)^2 + cpx_sqrt(f 2)^2 * (of_int X)^2 - f 3 * X^4
          + 2 * of_int(f 0) * cpx_sqrt(f 1) - 2 * of_int(f 0) * cpx_sqrt(f 2) * of_int X
          - 2 * cpx_sqrt(f 1) * cpx_sqrt(f 2) * of_int X )
      * (of_int(f 0)^2 + cpx_sqrt(f 1)^2 + cpx_sqrt(f 2)^2 * (of_int X)^2 - f 3 * X^4
          + 2 * of_int(f 0) * cpx_sqrt(f 1) + 2 * of_int(f 0) * cpx_sqrt(f 2) * of_int X
          + 2 * cpx_sqrt(f 1) * cpx_sqrt(f 2) * of_int X )"
    by algebra
  also have "... = ((of_int(f 0)^2 + cpx_sqrt(f 1)^2 + cpx_sqrt(f 2)^2 * (of_int X)^2 -f 3 * X^4
          - 2 * of_int(f 0) * cpx_sqrt(f 1))^2 - (2 * of_int(f 0) * cpx_sqrt(f 2) * of_int X
          - 2 * cpx_sqrt(f 1) * cpx_sqrt(f 2) * of_int X)^2 )
      * ((of_int(f 0)^2 + cpx_sqrt(f 1)^2 + cpx_sqrt(f 2)^2 * (of_int X)^2 - f 3 * X^4
          + 2 * of_int(f 0) * cpx_sqrt(f 1))^2 - (2 * of_int(f 0) * cpx_sqrt(f 2) * of_int X
          + 2 * cpx_sqrt(f 1) * cpx_sqrt(f 2) * of_int X)^2 )"
    by algebra
  also have "... = (((f 0)^2 + f 1 + f 2 * (of_int X)^2 - f 3 * X^4
          - 2 * of_int(f 0) * cpx_sqrt(f 1))^2 - (2 * of_int(f 0) * cpx_sqrt(f 2) * of_int X
          - 2 * cpx_sqrt(f 1) * cpx_sqrt(f 2) * of_int X)^2 )
      * (((f 0)^2 + f 1 + f 2 * (of_int X)^2 - f 3 * X^4
          + 2 * of_int(f 0) * cpx_sqrt(f 1))^2 - (2 * of_int(f 0) * cpx_sqrt(f 2) * of_int X
          + 2 * cpx_sqrt(f 1) * cpx_sqrt(f 2) * of_int X)^2 )"
    using square_sqrt by simp
  also have "... = (of_int((f 0)^2 + f 1 + f 2 * (of_int X)^2 - f 3 * X^4)^2
          + 4 * of_int(f 0)^2 * cpx_sqrt(f 1)^2
          - 4 * of_int(f 0) * cpx_sqrt(f 1) * ((f 0)^2 + f 1 + f 2 * (of_int X)^2 - f 3 * X^4)
          - 4 * of_int(f 0)^2 * cpx_sqrt(f 2)^2 * (of_int X)^2
          - 4 * cpx_sqrt(f 1)^2 * cpx_sqrt(f 2)^2 * (of_int X)^2
          + 8 * of_int(f 0) * cpx_sqrt(f 2) * of_int X * cpx_sqrt(f 1) * cpx_sqrt(f 2) * of_int X)
      * (of_int((f 0)^2 + f 1 + f 2 * (of_int X)^2 - f 3 * X^4)^2
          + 4 * of_int(f 0)^2 * cpx_sqrt(f 1)^2
          + 4 * of_int(f 0) * cpx_sqrt(f 1) * ((f 0)^2 + f 1 + f 2 * (of_int X)^2 - f 3 * X^4)
          - 4 * of_int(f 0)^2 * cpx_sqrt(f 2)^2 * (of_int X)^2
          - 4 * cpx_sqrt(f 1)^2 * cpx_sqrt(f 2)^2 * (of_int X)^2
          - 8 * of_int(f 0) * cpx_sqrt(f 2) * of_int X * cpx_sqrt(f 1) * cpx_sqrt(f 2) * of_int X)"
    by algebra
  also have "... = (((f 0)^2 + f 1 + f 2 * X^2 - f 3 * X^4)^2
          + 4 * (f 0)^2 * f 1
          - 4 * f 0 * cpx_sqrt(f 1) * ((f 0)^2 + f 1 + f 2 * X^2 - f 3 * X^4)
          - 4 * (f 0)^2 * f 2 * X^2
          - 4 * f 1 * f 2 * X^2
          + 8 * f 0 * f 2  * cpx_sqrt(f 1) * X * X)
      * (((f 0)^2 + f 1 + f 2 * X^2 - f 3 * X^4)^2
          + 4 * (f 0)^2 * f 1
          + 4 * f 0 * cpx_sqrt(f 1) * ((f 0)^2 + f 1 + f 2 * X^2 - f 3 * X^4)
          - 4 * (f 0)^2 *f 2 * X^2
          - 4 * f 1 * f 2 * X^2
          - 8 * f 0 * cpx_sqrt(f 2) * X * cpx_sqrt(f 1) * cpx_sqrt(f 2) * X)"
    using square_sqrt of_int_mult power2_eq_square[of "cpx_sqrt(f 2)"] by force
  also have "... = (((f 0)^2 + f 1 + f 2 * X^2 - f 3 * X^4)^2 + 4 * (f 0)^2 * f 1
          - 4 * f 0 * cpx_sqrt(f 1) * ((f 0)^2 + f 1 + f 2 * X^2 - f 3 * X^4)
          - 4 * (f 0)^2 * f 2 * X^2 - 4 * f 1 * f 2 * X^2
          + 8 * f 0 * f 2  * cpx_sqrt(f 1) * X^2)
      * (((f 0)^2 + f 1 + f 2 * X^2 - f 3 * X^4)^2 + 4 * (f 0)^2 * f 1
          + 4 * f 0 * cpx_sqrt(f 1) * ((f 0)^2 + f 1 + f 2 * X^2 - f 3 * X^4)
          - 4 * (f 0)^2 * f 2 * X^2 - 4 * f 1 * f 2 * X^2
          - 8 * f 0 * f 2 * cpx_sqrt(f 1) * X^2)"
    using power2_eq_square square_sqrt mult.commute of_int_mult
    by (smt (verit, del_insts) Groups.mult_ac(3))
  also have "... = (((f 0)^2 + f 1 + f 2 * X^2 - f 3 * X^4)^2 + 4 * (f 0)^2 * f 1
          - 4 * (f 0)^2 * f 2 * X^2 - 4 * f 1 * f 2 * X^2
        - (4 * f 0 * cpx_sqrt(f 1) * ((f 0)^2 + f 1 + f 2 * X^2 - f 3 * X^4)
          - 8 * f 0 * f 2  * cpx_sqrt(f 1) * X^2))
      * (((f 0)^2 + f 1 + f 2 * X^2 - f 3 * X^4)^2 + 4 * (f 0)^2 * f 1
          - 4 * (f 0)^2 * f 2 * X^2 - 4 * f 1 * f 2 * X^2
        + (4 * f 0 * cpx_sqrt(f 1) * ((f 0)^2 + f 1 + f 2 * X^2 - f 3 * X^4)
          - 8 * f 0 * f 2  * cpx_sqrt(f 1) * X^2))"
    by (simp add:algebra_simps) (* This takes long, even thought we're just distributing a minus here *)
  also have "... = (of_int(((f 0)^2 + f 1 + f 2 * X^2 - f 3 * X^4)^2 + 4 * (f 0)^2 * f 1
          - 4 * (f 0)^2 * f 2 * X^2 - 4 * f 1 * f 2 * X^2))^2
        - cpx_sqrt(f 1)^2 * (of_int (4 * f 0) * of_int((f 0)^2 + f 1 + f 2 * X^2 - f 3 * X^4)
          -  of_int(8 * f 0 * f 2)  * of_int(X^2))^2"
    by algebra
  also have "... = (((f 0)^2 + f 1 + f 2 * X^2 - f 3 * X^4)^2 + 4 * (f 0)^2 * f 1
          - 4 * (f 0)^2 * f 2 * X^2 - 4 * f 1 * f 2 * X^2)^2
        - (f 1) * (4 * f 0 * ((f 0)^2 + f 1 + f 2 * X^2 - f 3 * X^4)
          -  8 * f 0 * f 2  * X^2)^2"
    using square_sqrt of_int_mult of_int_add by simp
  also have "... = (((inser x)^2 + inser \<A>\<^sub>1 + inser \<A>\<^sub>2 * (inser \<X>\<^sub>3)^2 - inser \<A>\<^sub>3 * (inser \<X>\<^sub>3)^4)^2 + 4 * (inser x)^2 * inser \<A>\<^sub>1
          - 4 * (inser x)^2 * inser \<A>\<^sub>2 * (inser \<X>\<^sub>3)^2 - 4 * inser \<A>\<^sub>1 * inser \<A>\<^sub>2 * (inser \<X>\<^sub>3)^2)^2
        - inser \<A>\<^sub>1 * (4 * inser x * ((inser x)^2 + inser \<A>\<^sub>1 + inser \<A>\<^sub>2 * (inser \<X>\<^sub>3)^2 - inser \<A>\<^sub>3 * (inser \<X>\<^sub>3)^4)
          -  8 * inser x * inser \<A>\<^sub>2  * (inser \<X>\<^sub>3)^2)^2"
    using inser_X unfolding defs inser_def by simp
  (* inser is a ring homomorphism so the next steps are obvious *)
  also have "... = ((inser (x^2) + inser \<A>\<^sub>1 + inser (\<A>\<^sub>2 * \<X>\<^sub>3^2) - inser (\<A>\<^sub>3 * \<X>\<^sub>3^4))^2 + 4 * inser (x^2) * inser \<A>\<^sub>1
          - 4 * inser (x^2) * inser \<A>\<^sub>2 * inser (\<X>\<^sub>3^2) - 4 * inser \<A>\<^sub>1 * inser \<A>\<^sub>2 * inser (\<X>\<^sub>3^2))^2
        - inser \<A>\<^sub>1 * (4 * inser x * (inser (x^2) + inser \<A>\<^sub>1 + inser \<A>\<^sub>2 * inser (\<X>\<^sub>3^2) - inser \<A>\<^sub>3 * inser (\<X>\<^sub>3^4))
          -  8 * inser x * inser \<A>\<^sub>2  * inser (\<X>\<^sub>3^2))^2"
    unfolding inser_def power2_eq_square power4_eq_xxxx using insertion_mult[of f] by presburger
  also have "... = ((inser (x^2) + inser \<A>\<^sub>1 + inser (\<A>\<^sub>2 * \<X>\<^sub>3^2) - inser (\<A>\<^sub>3 * \<X>\<^sub>3^4))^2 + 4 * inser (x^2 * \<A>\<^sub>1)
          - 4 * inser (x^2 * \<A>\<^sub>2 * \<X>\<^sub>3^2) - 4 * inser (\<A>\<^sub>1 * \<A>\<^sub>2 * \<X>\<^sub>3^2))^2
        - inser \<A>\<^sub>1 * (4 * inser x * (inser (x^2) + inser \<A>\<^sub>1 + inser (\<A>\<^sub>2 * \<X>\<^sub>3^2) - inser (\<A>\<^sub>3 * \<X>\<^sub>3^4))
          -  8 * inser (x * \<A>\<^sub>2 * \<X>\<^sub>3^2))^2"
    unfolding inser_def using insertion_mult [of f] by (simp add: mult.assoc)
  also have "... = ((inser (x^2) + inser \<A>\<^sub>1 + inser (\<A>\<^sub>2 * \<X>\<^sub>3^2) + inser (-\<A>\<^sub>3 * \<X>\<^sub>3^4))^2 + 4 * inser (x^2 * \<A>\<^sub>1)
          + 4 * inser (- (x^2 * \<A>\<^sub>2 * \<X>\<^sub>3^2)) + 4 * inser (- \<A>\<^sub>1 * \<A>\<^sub>2 * \<X>\<^sub>3^2))^2
        + inser (- \<A>\<^sub>1) * (4 * inser x * (inser (x^2) + inser \<A>\<^sub>1 + inser (\<A>\<^sub>2 * \<X>\<^sub>3^2) + inser (-\<A>\<^sub>3 * \<X>\<^sub>3^4))
          +  8 * inser (- x * \<A>\<^sub>2 * \<X>\<^sub>3^2))^2"
    unfolding inser_def by simp 
  also have "... = ((inser (x^2) + inser \<A>\<^sub>1 + inser (\<A>\<^sub>2 * \<X>\<^sub>3^2) + inser (-\<A>\<^sub>3 * \<X>\<^sub>3^4))^2 + inser (4 * (x^2 * \<A>\<^sub>1))
          + inser (4 * (-  (x^2 * \<A>\<^sub>2 * \<X>\<^sub>3^2))) + inser (4* (- \<A>\<^sub>1 * \<A>\<^sub>2 * \<X>\<^sub>3^2)))^2
        + inser (- \<A>\<^sub>1) * (inser (4 * x) * (inser (x^2) + inser \<A>\<^sub>1 + inser (\<A>\<^sub>2 * \<X>\<^sub>3^2) + inser (-\<A>\<^sub>3 * \<X>\<^sub>3^4))
          +  inser (8 * (- x * \<A>\<^sub>2 * \<X>\<^sub>3^2)))^2"
    unfolding inser_def by simp 
  also have "... = ((inser (x^2) + inser \<A>\<^sub>1 + inser (\<A>\<^sub>2 * \<X>\<^sub>3^2) + inser (-\<A>\<^sub>3 * \<X>\<^sub>3^4))^2 + inser (4 * x^2 * \<A>\<^sub>1)
          + inser (-4 *x^2 * \<A>\<^sub>2 * \<X>\<^sub>3^2) + inser (-4 *  \<A>\<^sub>1 * \<A>\<^sub>2 * \<X>\<^sub>3^2))^2
        + inser (- \<A>\<^sub>1) * (inser (4 * x) * (inser (x^2) + inser \<A>\<^sub>1 + inser (\<A>\<^sub>2 * \<X>\<^sub>3^2) + inser (-\<A>\<^sub>3 * \<X>\<^sub>3^4))
          +  inser (-8 * x * \<A>\<^sub>2 * \<X>\<^sub>3^2))^2"
    by (simp add: mult.assoc)
  also have "... = ((inser (x^2 + \<A>\<^sub>1 + \<A>\<^sub>2 * \<X>\<^sub>3^2 + (- \<A>\<^sub>3 * \<X>\<^sub>3^4)))^2 + inser (4 * x^2 * \<A>\<^sub>1
          + (-4 *x^2 * \<A>\<^sub>2 * \<X>\<^sub>3^2) + (-4 *  \<A>\<^sub>1 * \<A>\<^sub>2 * \<X>\<^sub>3^2)))^2
        + inser (- \<A>\<^sub>1) * (inser (4 * x) * inser (x^2 + \<A>\<^sub>1 + \<A>\<^sub>2 * \<X>\<^sub>3^2 + (-\<A>\<^sub>3 * \<X>\<^sub>3^4))
          +  inser (-8 * x * \<A>\<^sub>2 * \<X>\<^sub>3^2))^2"
    unfolding inser_def using insertion_add[of f] by (smt (verit))
  also have "... = (inser ((x^2 + \<A>\<^sub>1 + \<A>\<^sub>2 * \<X>\<^sub>3^2 - \<A>\<^sub>3 * \<X>\<^sub>3^4)^2
          + (4 * x^2 * \<A>\<^sub>1 - 4 *x^2 * \<A>\<^sub>2 * \<X>\<^sub>3^2 - 4 *  \<A>\<^sub>1 * \<A>\<^sub>2 * \<X>\<^sub>3^2)))^2
        + inser (- \<A>\<^sub>1) * (inser (4 * x * (x^2 + \<A>\<^sub>1 + \<A>\<^sub>2 * \<X>\<^sub>3^2 - \<A>\<^sub>3 * \<X>\<^sub>3^4))
          +  inser (-8 * x * \<A>\<^sub>2 * \<X>\<^sub>3^2))^2"
    unfolding inser_def power2_eq_square using insertion_mult[of f] insertion_add[of f] by force
  also have "... = inser ( (((x^2+\<A>\<^sub>1+\<A>\<^sub>2*\<X>\<^sub>3^2-\<A>\<^sub>3*\<X>\<^sub>3^4)^2 + (4*x^2*\<A>\<^sub>1 - 4*x^2*\<A>\<^sub>2*\<X>\<^sub>3^2 - 4*\<A>\<^sub>1*\<A>\<^sub>2*\<X>\<^sub>3^2)))^2
        + (-\<A>\<^sub>1)*(4*x*(x^2+\<A>\<^sub>1+\<A>\<^sub>2*\<X>\<^sub>3^2-\<A>\<^sub>3*\<X>\<^sub>3^4) +  (-8*x*\<A>\<^sub>2*\<X>\<^sub>3^2))^2)"
    unfolding inser_def power2_eq_square using insertion_mult[of f] insertion_add[of f] by presburger
  also have "... = inser J3" unfolding J3_def by (simp add: add_diff_eq)
  finally show ?thesis unfolding \<E>_def inser_def by presburger
qed

lemma J3_cancels_iff:
  fixes f::"nat\<Rightarrow>int"
  defines "X \<equiv> 1 + (f 1)^2 + (f 2)^2 + (f 3)^2" 
  shows "(insertion f J3 = 0) = (\<exists>\<epsilon>\<in>\<E>.
    of_int(f 0) + of_int (fst3 \<epsilon>) * cpx_sqrt(f 1) + of_int (snd3 \<epsilon>) * cpx_sqrt(f 2) * of_int(X)
        + of_int (trd3 \<epsilon>) * cpx_sqrt(f 3) * of_int (X^2) = 0)"
proof -
  have fin: "finite \<E>" unfolding \<E>_def by blast
  thus ?thesis
    unfolding X_def using J3_fonction_eq_polynomial prod_zero_iff
    by (metis (no_types, lifting) of_int_0_eq_iff)
qed

(* Show that -I is smaller than any zero of F=J3 *)
lemma J3_zeros_bound:
  fixes A1 A2 A3
  defines "X \<equiv> 1 + A1^2 + A2^2 + A3^2"
  defines "I \<equiv> X^3"
  shows "(\<forall>x. insertion ((\<lambda>_. 0)(0:=x, 1:=A1, 2:=A2, 3:=A3)) J3 = 0 \<longrightarrow> x > -I)"
proof -
  {
    fix x :: int
    define A :: "nat \<Rightarrow> int" where "A \<equiv> (\<lambda>_. 0)(1:=A1, 2:=A2, 3:=A3)"
    define f :: "nat \<Rightarrow> int"  where "f \<equiv> (\<lambda>_. 0)(0:=x, 1:=A1, 2:=A2, 3:=A3)"

    have "X \<ge> 0" unfolding X_def by simp
    have "X > 0" unfolding X_def power2_eq_square
      by (smt (verit, best) mult_eq_0_iff sum_squares_gt_zero_iff)
    hence "I \<ge> 0" unfolding I_def by simp

    have aux0: "sqrt (abs (A j)) * norm (X^(j-1))
                \<le> \<bar>A j\<bar> * norm (X^(j-1))" for j
      apply (intro mult_right_mono)
      apply (rule sqrt_int_smaller[of "\<bar>A _\<bar>"])
      by auto

    have sq_le: "x \<le> x^2" for x::int
      apply (cases "x = 0", auto)
      by (smt (verit, del_insts) mult_cancel_left mult_left_mono numeral_2_eq_2
            power2_eq_square power2_less_eq_zero_iff power_0 power_Suc)
    have aux1: "\<bar>A j\<bar> \<le> (A j)^2" for j
      using sq_le[of "\<bar>A j\<bar>"] by auto

    assume "insertion f J3 = 0"
    hence "of_int (insertion f J3) = 0"
      by simp
    hence "\<exists>\<epsilon>\<in>\<E>. 0 = of_int (f 0)
        + of_int (fst3 \<epsilon>) * cpx_sqrt(f 1)
        + of_int (snd3 \<epsilon>) * cpx_sqrt(f 2) * of_int (1 + (f 1)^2 + (f 2)^2 + (f 3)^2)
        + of_int (trd3 \<epsilon>) * cpx_sqrt(f 3) * of_int ((1 + (f 1)^2 + (f 2)^2 + (f 3)^2)^2)"
      by (subst (asm) J3_fonction_eq_polynomial \<E>_def) (simp add: \<E>_def)
    then obtain \<epsilon> :: "int\<times>int\<times>int" where
        \<epsilon>_def: "\<epsilon>\<in>\<E>" and
        \<epsilon>_form: "0 = of_int (f 0) + of_int (fst3 \<epsilon>) * cpx_sqrt(f 1)
              + of_int (snd3 \<epsilon>) * cpx_sqrt(f 2) * of_int (1 + (f 1)^2 + (f 2)^2 + (f 3)^2)
              + of_int (trd3 \<epsilon>) * cpx_sqrt(f 3) * of_int ((1 + (f 1)^2 + (f 2)^2 + (f 3)^2)^2)"
      by (auto simp only: prod_zero_iff)
    have \<epsilon>_abs: "\<forall>j\<in>{1,2,3}. norm (fun3 \<epsilon> j) = 1" using \<epsilon>_def unfolding \<E>_def by auto

    have "x > -I"
    proof (cases "A1 = 0 \<and> A2 = 0 \<and> A3 = 0")
      case True
      then show ?thesis
        using \<epsilon>_form unfolding f_def cpx_sqrt_def I_def
        by (simp add: `X > 0`)
    next
      case False
      hence "X > 1" unfolding X_def power2_eq_square 
        by (smt (verit) not_sum_squares_lt_zero sum_squares_gt_zero_iff)

      from \<epsilon>_def \<epsilon>_form have x_def:
        "of_int x = - (\<Sum>j\<in>{1,2,3}. fun3 \<epsilon> j * cpx_sqrt(A j) * X^(j-1))"
        unfolding f_def A_def X_def apply (simp add: fun3_def del: One_nat_def)
        by (smt (verit, ccfv_SIG) add.commute add_0 add_diff_cancel_right' add_uminus_conv_diff)
      also have "norm (...) \<le> (\<Sum>j\<in>{1,2,3::nat}. norm (fun3 \<epsilon> j) * norm (cpx_sqrt (A j))
                                                  * norm X^(j-1))"
        apply (subst norm_minus_cancel)
        apply (intro sum_norm_le)
        by (simp add: norm_mult norm_power)
      also have "... \<le> (\<Sum>j\<in>{1,2,3::nat}. norm (cpx_sqrt (A j)) * norm X^(j-1))"
         using \<epsilon>_abs by auto
      also have "... \<le> (\<Sum>j\<in>{1,2,3::nat}. sqrt (abs (A j)) * norm (X^(j-1)))"
        by (auto simp: norm_cpx_sqrt)
      also have "... \<le> (\<Sum>j\<in>{1,2,3::nat}. \<bar>A j\<bar> * norm (X^(j-1)))"
        apply (intro sum_mono)
        using aux0 by auto
      also have "... = (\<Sum>j\<in>{1,2,3::nat}. \<bar>A j\<bar> * X^(j-1))"
        unfolding X_def by auto
      also have "... \<le> (\<Sum>j\<in>{1,2,3::nat}. (A j)^2 * X^(j-1))"
      proof -
        have "(\<Sum>j\<in>{1, 2, 3}. \<bar>A j\<bar> * X ^ (j - 1))
              \<le> (\<Sum>j\<in>{1,2,3::nat}. (A j)^2 * X^(j-1))"
          apply (intro sum_mono mult_right_mono)
          by (auto simp: aux1 X_def)
        thus ?thesis by linarith
      qed

      also have "... < abs I"
      proof -
        have "\<forall>j. (A j)\<^sup>2 < X"
          unfolding A_def X_def power2_eq_square apply simp
          by (smt (verit, del_insts) not_sum_power2_lt_zero power2_eq_square)
        hence "\<forall>j. (A (Suc j))\<^sup>2 < X"
          by auto
        hence "(\<Sum>j=0..2. (A (Suc j))\<^sup>2 * X ^ j) < I"
          unfolding I_def
          using digit_repr_lt[of X "power2 \<circ> A \<circ> Suc" 2] `X > 1`
          by auto
        moreover have "(\<Sum>j=0..2. (A (Suc j))\<^sup>2 * X ^ j) = (\<Sum>j\<in>{1..3}. (A j)\<^sup>2 * X ^ (j - 1)) "
          apply (simp add: sum.atLeast1_atMost_eq)
          apply (rule sum.cong)
          by auto
        moreover have "{1..3} = {1::nat, 2, 3}" by auto 
        ultimately have "(\<Sum>j\<in>{1, 2, 3}. (A j)\<^sup>2 * X ^ (j - 1)) < I"
          by auto
        thus ?thesis
          unfolding X_def by linarith
      qed

      finally have "abs x < abs I"
        by auto
      then show ?thesis
        by (simp add: \<open>0 \<le> I\<close>)
    qed
  }
  thus ?thesis by auto
qed

declare single_numeral[simp del]

end

end