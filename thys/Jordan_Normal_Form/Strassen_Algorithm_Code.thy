(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Strassen's Algorithm as Code Equation\<close>

text \<open>We replace the code-equations for matrix-multiplication 
  by Strassen's algorithm. Note that this will strengthen the class-constraint
  for matrix multiplication from semirings to rings!\<close>

theory Strassen_Algorithm_Code
imports 
  Strassen_Algorithm
begin

text \<open>The aim is to replace the implementation of @{const mat_mult_mat} by @{const strassen_mat_mult}.\<close>

text \<open>We first need a copy of standard matrix multiplication to execute the base case.\<close>

definition "basic_mat_mult = op \<otimes>\<^sub>m"
lemma [code]: "basic_mat_mult A B = mat (dim\<^sub>r A) (dim\<^sub>c B) (\<lambda> (i,j). row A i \<bullet> col B j)"
  unfolding basic_mat_mult_def by auto

text \<open>Next use this new matrix multiplication code within Strassen's algorithm.\<close>
lemmas strassen_mat_mult_code[code] = strassen_mat_mult.simps[folded basic_mat_mult_def]

text \<open>And finally use Strassen's algorithm for implementing matrix-multiplication.\<close>

lemma mat_mult_code[code]: "A \<otimes>\<^sub>m B = (if dim\<^sub>c A = dim\<^sub>r B then strassen_mat_mult A B else basic_mat_mult A B)"
  using strassen_mat_mult[of A B] unfolding basic_mat_mult_def by auto

end
