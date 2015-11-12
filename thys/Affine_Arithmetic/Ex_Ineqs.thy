section{* Examples on Proving Inequalities *}
theory Ex_Ineqs
imports Affine_Code
begin
text{*\label{sec:examples}*}

text {* The examples below are taken from
  @{url "http://link.springer.com/chapter/10.1007/978-3-642-38088-4_26"},
  ``Formal Verification of Nonlinear Inequalities with Taylor Interval Approximations'',
  Alexey Solovyev, Thomas C. Hales,
  NASA Formal Methods 2013, LNCS 7871
  *}

primrec prove_pos::"nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow>
    (nat \<Rightarrow> real \<Rightarrow> 'a::executable_euclidean_space aform \<Rightarrow> _ \<Rightarrow> real aform option) \<Rightarrow>
    'a::executable_euclidean_space aform \<Rightarrow> bool" where
  "prove_pos 0 p t st F X = False"
| "prove_pos (Suc i) p t st F X = (if 0 < Inf_aform' p (the (F p t X [])) then True else
    case split_aform_largest p st X of
      [a, b] \<Rightarrow> prove_pos i p t st F a \<and> prove_pos i p t st F b
    | _ \<Rightarrow> False)"

approximate_affine schwefel "\<lambda>(x1, x2, x3).
  (FloatR 58806 0 * inverse (FloatR 6103515625 14) +
    (x1 + - (x2*x2))*(x1 + - (x2*x2)) +
    (x2 + - 1)*(x2 + - 1) +
    (x1 + - (x3*x3))*(x1 + - (x3*x3)) +
    (x3 + - 1)*(x3 + - 1))*\<^sub>R1::real"

lemma
  "prove_pos 80 20 (FloatR  1 (-1)) (FloatR 1 1) schwefel (aform_of_ivl (-10,-10,-10) (10,10,10))"
  by eval --"slow: 100s"

approximate_affine delta6 "\<lambda>(x1, x2, x3, x4, x5, x6).
  (x1 * x4 * (-x1 + x2 + x3 + -x4 + x5 + x6) +
   x2 * x5 * (x1 + -x2 + x3 + x4 + - x5 + x6) +
   x3 * x6 * (x1 + x2 + - x3 + x4 + x5 + -x6) +
   - x2 * x3 * x4 +
   - x1 * x3 * x5 +
   - x1 * x2 * x6 +
   - x4 * x5 * x6)*\<^sub>R1::real"

definition "mk_tuple6 x = (x, x, x, x, x, x)"

lemma "prove_pos 20 10 (FloatR 1 (-1)) (FloatR 1 1) delta6
    (aform_of_ivl (mk_tuple6 4) (mk_tuple6 (FloatR 104045 (-14))))"
  by eval

definition "mk_tuple7 x = (x, x, x, x, x, x, x)"

approximate_affine magnetism "\<lambda>(x1, x2, x3, x4, x5, x6, x7).
  (FloatR 409616384 (-14) + x1 * x1 + 2 * x2*x2 + 2 * x3 * x3 + 2 * x4 * x4 + 2 * x5 * x5 +
  2 * x6 * x6 + 2 * x7 * x7 + - x1) *\<^sub>R 1::real"

lemma
  "prove_pos 20 10 (FloatR 1 (-1)) (FloatR 1 1) magnetism
    (aform_of_ivl (mk_tuple7 (-1)) (mk_tuple7 1))"
  by eval

definition "mk_tuple4 x = (x, x, x, x)"
approximate_affine caprasse "\<lambda>(x1, x2, x3, x4).
  (FloatR 7160948587500457 (-51) + - x1 * x3 * x3 * x3 + 4 * x2 * x3 * x3 * x4 +
    4 * x1 * x3 * x4 * x4 + 2 * x2 * x4 * x4 * x4 + 4 * x1 * x3 + 4 * x3 * x3 + - 10 * x2 * x4 +
    -10 * x4 * x4 + 2)*\<^sub>R1::real"

lemma
  "prove_pos 50 40 (FloatR 1 (-3)) (FloatR 1 (-1)) caprasse
    (aform_of_ivl (mk_tuple4 (- FloatR 1 (-1))) (mk_tuple4 (FloatR 1 (-1))))"
  by eval

end
