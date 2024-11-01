theory Tangent_Secant_Imperative_Test
  imports Tangent_Numbers_Imperative Secant_Numbers_Imperative
begin

definition "tangent_number_imp n = 
  do {
    a \<leftarrow> tangent_numbers_imperative.compute_imp (nat_of_integer n);
    xs \<leftarrow> Array.freeze a;
    return (map integer_of_nat xs)
  }"

ML_val \<open>@{code tangent_number_imp} 100 ()\<close>


definition "secant_number_imp n = 
  do {
    a \<leftarrow> secant_numbers_imperative.compute_imp (nat_of_integer n);
    xs \<leftarrow> Array.freeze a;
    return (map integer_of_nat xs)
  }"

ML_val \<open>@{code secant_number_imp} 100 ()\<close>

end
