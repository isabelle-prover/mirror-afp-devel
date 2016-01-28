(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Gauss Jordan Elimination over Finite Fields\<close>

text \<open>This theory contains copies of algorithms for Gauss Jordan Elimination,
  which have been adapted to finite fields.\<close>

theory Gauss_Jordan_Field
imports 
  Prime_Field
  "../Jordan_Normal_Form/Gauss_Jordan"
begin

context 
  fixes F :: "'a ffield" (structure)
begin

text \<open>The basic row operations have all been made generic, so that we just have to instantiate 
them.\<close>

definition multrow_f :: "nat \<Rightarrow> 'a \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
  [code_unfold]: "multrow_f = mat_multrow_gen (op *f)"

definition addrow_f :: "'a \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
  [code_unfold]: "addrow_f = mat_addrow_gen (op +f) (op *f)"

definition eliminate_entries_f :: "'a mat \<Rightarrow> 'a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> 'a mat" where
  [code_unfold]: "eliminate_entries_f = eliminate_entries_gen (op +f) (op *f) (ffield.uminus F) 0f"

text \<open>@{const gauss_jordan} is not reused from @{theory Gauss_Jordan}, as here we take a 
  more efficient version which only works on one matrix.\<close>
context 
  fixes nr nc :: nat
begin
partial_function (tailrec) gauss_jordan_main_f :: "'a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat" where
  [code]: "gauss_jordan_main_f A i j = (
    if i < nr \<and> j < nc then let aij = A $$ (i,j) in if aij = 0f then
      (case [ i' . i' <- [Suc i ..< nr],  A $$ (i',j) \<noteq> 0f] 
        of [] \<Rightarrow> gauss_jordan_main_f A i (Suc j)
         | (i' # _) \<Rightarrow> gauss_jordan_main_f (swaprows i i' A) i j)
      else if aij = 1f then let is = filter (\<lambda> i'. i' \<noteq> i) [0 ..< nr] in
        gauss_jordan_main_f 
        (eliminate_entries_f A A i j is) (Suc i) (Suc j)
      else let iaij = inverse_f F aij in gauss_jordan_main_f (multrow_f i iaij A) i j
    else A)"
end

definition gauss_jordan_f :: "'a mat \<Rightarrow> 'a mat" where
  "gauss_jordan_f A = gauss_jordan_main_f (dim\<^sub>r A) (dim\<^sub>c A) A 0 0"

definition find_base_vectors_f :: "'a mat \<Rightarrow> 'a vec list" where
  [code_unfold]: "find_base_vectors_f = find_base_vectors_gen (ffield.uminus F) 0f 1f"
end

end