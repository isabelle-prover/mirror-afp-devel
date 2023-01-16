section \<open>Diophantine Equations\<close>

theory Parametric_Polynomials
  imports Main
  abbrevs ++ = "\<^bold>+" and
          -- = "\<^bold>-" and
          ** = "\<^bold>*" and
          00 = "\<^bold>0" and
          11 = "\<^bold>1"
begin

subsection \<open>Parametric Polynomials\<close>

text \<open>This section defines parametric polynomials and builds up the infrastructure to later prove
      that a given predicate or relation is Diophantine. The formalization follows 
      \<^cite>\<open>"h10lecturenotes"\<close>.\<close>

type_synonym assignment = "nat \<Rightarrow> nat"

text \<open>Definition of parametric polynomials with natural number coefficients and their evaluation 
      function\<close>

datatype ppolynomial =
    Const nat |
    Param nat |
    Var   nat |
    Sum  ppolynomial ppolynomial (infixl "\<^bold>+" 65) |
    NatDiff ppolynomial ppolynomial (infixl "\<^bold>-" 65) |
    Prod ppolynomial ppolynomial (infixl "\<^bold>*" 70)

fun ppeval :: "ppolynomial \<Rightarrow> assignment \<Rightarrow> assignment \<Rightarrow> nat"  where
    "ppeval (Const c) p v = c" |
    "ppeval (Param x) p v = p x" |
    "ppeval (Var x) p v = v x" |
    "ppeval (D1 \<^bold>+ D2) p v = (ppeval D1 p v) + (ppeval D2 p v)" |
    (* The next line lifts subtraction of type "nat \<Rightarrow> nat \<Rightarrow> nat" *)
    "ppeval (D1 \<^bold>- D2) p v = (ppeval D1 p v) - (ppeval D2 p v)" |
    "ppeval (D1 \<^bold>* D2) p v = (ppeval D1 p v) * (ppeval D2 p v)"

definition Sq_pp ("_ \<^bold>^\<^bold>2" [99] 75) where "Sq_pp P = P \<^bold>* P"

definition is_dioph_set :: "nat set \<Rightarrow> bool" where
    "is_dioph_set A = (\<exists>P1 P2::ppolynomial. \<forall>a. (a \<in> A)
                                            \<longleftrightarrow> (\<exists>v. ppeval P1 (\<lambda>x. a) v = ppeval P2 (\<lambda>x. a) v))"

datatype polynomial =
    Const nat |
    Param nat |
    Sum  polynomial polynomial (infixl "[+]" 65) |
    NatDiff polynomial polynomial (infixl "[-]" 65) |
    Prod polynomial polynomial (infixl "[*]" 70)

fun peval :: "polynomial \<Rightarrow> assignment \<Rightarrow> nat"  where
    "peval (Const c) p = c" |
    "peval (Param x) p = p x" |
    "peval (Sum D1 D2) p = (peval D1 p) + (peval D2 p)" |
    (* The next line lifts subtraction of type "nat \<Rightarrow> nat \<Rightarrow> nat" *)
    "peval (NatDiff D1 D2) p = (peval D1 p) - (peval D2 p)" |
    "peval (Prod D1 D2) p = (peval D1 p) * (peval D2 p)"

definition sq_p :: "polynomial \<Rightarrow> polynomial" ("_ [^2]" [99] 75) where "sq_p P = P [*] P"

definition zero_p :: "polynomial" ("\<^bold>0") where "zero_p = Const 0"
definition one_p :: "polynomial" ("\<^bold>1") where "one_p = Const 1"

lemma sq_p_eval: "peval (P[^2]) p = (peval P p)^2"
  unfolding sq_p_def by (simp add: power2_eq_square)

fun convert :: "polynomial \<Rightarrow> ppolynomial"  where
    "convert (Const c) = (ppolynomial.Const c)" |
    "convert (Param x) = (ppolynomial.Param x)" |
    "convert (D1 [+] D2) = (convert D1) \<^bold>+ (convert D2)" |
    "convert (D1 [-] D2) = (convert D1) \<^bold>- (convert D2)" |
    "convert (D1 [*] D2) = (convert D1) \<^bold>* (convert D2)"

lemma convert_eval: "peval P a = ppeval (convert P) a v" (* implicit for all v *)
  by (induction P, auto)

definition list_eval :: "polynomial list \<Rightarrow> assignment \<Rightarrow> (nat \<Rightarrow> nat)" where
    "list_eval PL a = nth (map (\<lambda>x. peval x a) PL)"

end