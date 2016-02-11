(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Algebraic Number Tests\<close>

text \<open>We provide a sequence of examples which demonstrate what can be done with 
  the implementation of algebraic numbers.\<close>

theory Algebraic_Number_Tests
imports
  "../Jordan_Normal_Form/Char_Poly"
  "../Show/Show_Complex"
  "../Polynomial_Factorization/Select_Berlekamp_Hensel_Factorization"
  "~~/src/HOL/Library/Code_Char"
  "~~/src/HOL/Library/Code_Target_Nat"
  "~~/src/HOL/Library/Code_Target_Int"
  Real_Factorization
  Show_Real_Precise  
begin

subsection \<open>Stand-Alone Examples\<close>

text \<open>Ensure that the correct code equations are used\<close>
declare real_code_dels[code, code del]
declare real_code_unfold_dels[code_unfold del]
declare real_alg_code_eqns[code]

abbreviation (input) "show_lines x \<equiv> shows_lines x Nil"

fun show_factorization :: "'a :: {semiring_1,show} \<times> (('a poly \<times> nat)list) \<Rightarrow> string" where
  "show_factorization (c,[]) = show c" 
| "show_factorization (c,((p,i) # ps)) = show_factorization (c,ps) @ '' * ('' @ show p @ '')'' @
  (if i = 1 then [] else ''^'' @ show i)"

text \<open>Determine the roots over the rational, real, and complex numbers.\<close>

definition "testpoly = [:5/2, -7/2, 1/2, -5, 7, -1, 5/2, -7/2, 1/2:]"
definition "test = show_lines (   real_roots_of_rat_poly testpoly)"

value (code) "show_lines (        roots_of_rat_poly testpoly)"
value (code) "show_lines (   real_roots_of_rat_poly testpoly)"
value (code) "show_lines (complex_roots_of_rat_poly testpoly)"


text \<open>Factorize polynomials over the rational, real, and complex numbers.\<close>

value (code) "show_factorization (factorize_rat_poly Full_Factorization testpoly)" 
value (code) "show_factorization (the (factorize_real_poly testpoly))"
value (code) "show_factorization (the (factorize_complex_poly testpoly))"

text \<open>If the input is not a rational polynomial, factorization can fail.\<close>

value (code) "factorize_real_poly [:sqrt(2),1,3,1:]" text \<open>fails\\\<close>
value (code) "factorize_real_poly [:sqrt(2),1,3:]" text \<open>does not fail, reveals internal representation\\\<close>
value (code) "show (factorize_real_poly [:sqrt(2),1,3:])" text \<open>does not fail, pretty printed\<close>


text \<open>A sequence of calculations.\<close>

value (code) "show (- sqrt 2 - sqrt 3)"
value (code) "root 3 4 > sqrt (root 4 3) + \<lfloor>1/10 * root 3 7\<rfloor>"
value (code) "csqrt (4 + 3 * \<i>) \<in> \<real>"
value (code) "show (csqrt (4 + 3 * \<i>))"
value (code) "show (csqrt (1 + \<i>))"

subsection \<open>Example Application: Compute Norms of Eigenvalues\<close>

text \<open>For complexity analysis of some matrix $A$ it is important to compute the norms
  of its eigenvalues, since they determine the spectral radius of $A$, and hence,
  the growth rates of matrix-powers $A^n$, cf.~\cite{JNF-AFP} for a formalized statement
  of this fact.\<close>

definition eigenvalues :: "rat mat \<Rightarrow> complex list" where
  "eigenvalues A = complex_roots_of_rat_poly (char_poly A)"

definition "testmat = mat_of_rows_list 3 [
  [1,-4,2],
  [1/5,7,9],
  [7,1,5 :: rat]
  ]"

definition "test_ev_show_precise = show ([ cmod ev. ev \<leftarrow> eigenvalues testmat])"
value (code) "char_poly testmat"
value (code) test_ev_show_precise

text \<open>Since the precise show function requires validation of the factorization
  provided by the oracle, it is usually much slower than the approximative one
  in  theory \textit{Show-Real-Approx}
  which displays the result up to a certain number of digits. 
  This indicates that as future work, 
  a fully verified efficient factorization algorithm would be valuable.\<close>

end
