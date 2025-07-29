theory Lemma_1_8_Defs
  imports Main "../MPoly_Utils/More_More_MPoly_Type" Bit_Counting
          Utils Multinomial
begin

subsection \<open>Expressing polynomial solutions in terms of carry counting\<close>

subsubsection \<open>Preliminary definitions\<close>

locale Lemma_1_8_Defs =
  fixes P :: "int mpoly" 
    and \<B> :: nat
    and L :: int
    and z :: "nat list"
begin 
  
abbreviation \<sigma> where "\<sigma> \<equiv> count_bits"
abbreviation \<tau> where "\<tau> \<equiv> count_carries"

definition \<delta>::nat where "\<delta> = total_degree P"
definition \<nu>::nat where "\<nu> = max_vars P"
definition b::nat where "b \<equiv> \<B> div 2"
definition n::"nat \<Rightarrow> nat" where "n j = (\<delta>+1)^j"

definition X::"int mpoly" where "X = Var 0"

text \<open>The are assignments of variables, used to evaluate (multivariable) polynomials.\<close>
definition z_assign where "z_assign = ((!\<^sub>0) (map int z))"
definition \<B>_assign where "\<B>_assign = (\<lambda>i. (int \<B>) when i = 0)"

text \<open>We will often use this set as indices of sums.\<close>
definition \<delta>_tuples :: "(nat list) set" where
  "\<delta>_tuples \<equiv> {i. length i = \<nu> + 1 \<and> sum_list i \<le> \<delta>}"

(* Beware : we can't use Abs_poly_mapping ((!) i) *)
definition P_coeff :: "nat list \<Rightarrow> int" where
  "P_coeff i \<equiv> coeff P (Abs_poly_mapping ((!\<^sub>0) i))"

definition D_exponent :: "nat list \<Rightarrow> nat" where
  "D_exponent i \<equiv> n (\<nu>+1) - (\<Sum>s\<le>\<nu>. i!s * n s)"
definition D_precoeff :: "nat list \<Rightarrow> int" where
  "D_precoeff i \<equiv> int (mfact i * fact (\<delta> - sum_list i))"
text \<open>This is really a univariate polynomial\<close>
definition D::"int mpoly" where
  "D \<equiv> \<Sum>i\<in>\<delta>_tuples. of_int (D_precoeff i * P_coeff i) * X^(D_exponent i)"

text \<open>This is really a univariate polynomial\<close>
definition c::"int mpoly" where 
  "c \<equiv> (\<Sum>i\<le>\<nu>. of_nat (z!i) * X^(n i))"

text \<open>Definition of the constant K\<close>
definition R::"int mpoly" where "R \<equiv> (1+c)^\<delta> * D"
definition S::"nat" where "S \<equiv> (\<Sum>i\<le>(2*\<delta>+1) * n \<nu>. b * \<B>^i)"
definition K::int where "K \<equiv> insertion \<B>_assign R + int S"

text \<open>Some more notation used in the proofs :
  (e j) is the coefficient of $X^j$ in R\<close>
definition e::"nat \<Rightarrow> int" 
  where "e j = coeff R (Poly_Mapping.single 0 j)"

end

end