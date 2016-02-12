(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>External Factorization\<close>

text \<open>We just define a function external-factorization-oracle-int-poly 
  which is used as oracle and 
  must be properly redefined in the generated code. 
  
  An example external oracle is available in file Mathematica.hs which has 
  been tested with a MacOS-version of Mathematica 10.\<close>
theory External_Factorization
imports 
  "../Show/Show_Instances"
begin

consts external_factorization_main :: "integer list \<Rightarrow> integer list list" 

lemma external_factorization_main_code [code]: 
  "external_factorization_main p = Code.abort (String.implode 
    (''did not implement external_factorization_main: input was\<newline>'' @ show (map int_of_integer p))) 
    (\<lambda> _. external_factorization_main p)" by simp

definition external_factorization :: "int list \<Rightarrow> int list list" where
  "external_factorization p = map (map int_of_integer) (external_factorization_main 
     (map integer_of_int p))"

end
