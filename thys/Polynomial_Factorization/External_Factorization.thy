(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>External Factorization\<close>

text \<open>We just define a function external-factorization-oracle-int-poly which is used as oracle and must be properly redefined
  in the generated code.\<close>
theory External_Factorization
imports 
  "../Show/Show_Instances"
begin


consts external_factorization :: "int list \<Rightarrow> int list list" 

lemma external_factorization_code [code]: 
  "external_factorization p = Code.abort (String.implode 
    (''did not implement external_factorization: input was\<newline>'' @ show p)) 
    (\<lambda> _. external_factorization p)" by simp


end
