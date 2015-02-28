(*  
    Title:      Examples_QR_Abstract_Float.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section{*Examples of execution using floats*}

theory Examples_QR_Abstract_Float
imports
  QR_Decomposition
  "../Gauss_Jordan/Code_Real_Approx_By_Float_Haskell"
begin

(*TODO: Check this after Isabelle2014*)
text{*The following equations must be removed from the code generator. If we don't delete them, the 
exported code will not work.*}

lemma real_code_unfold_dels: 
  "of_rat \<equiv> Ratreal" 
  "of_int a \<equiv> (of_rat (of_int a) :: real)" 
  "0 \<equiv> (of_rat 0 :: real)"
  "1 \<equiv> (of_rat 1 :: real)"
  "numeral k \<equiv> (of_rat (numeral k) :: real)"
  "- numeral k \<equiv> (of_rat (- numeral k) :: real)"
  by simp_all

lemmas real_code_unfold_dels[code_unfold del]

subsubsection{*Examples*}

definition "example1 = (let A = list_of_list_to_matrix [[1,2,4],[9,4,5],[0,0,0]]::real^3^3 in 
  matrix_to_list_of_list (divide_by_norm A))"

definition "example2 = (let A = list_of_list_to_matrix [[1,2,4],[9,4,5],[0,0,4]]::real^3^3 in
  matrix_to_list_of_list (fst (QR_decomposition A)))" 

definition "example3 = (let A = list_of_list_to_matrix [[1,2,4],[9,4,5],[0,0,4]]::real^3^3 in
  matrix_to_list_of_list (snd (QR_decomposition A)))"

definition "example4 = (let A = list_of_list_to_matrix [[1,2,4],[9,4,5],[0,0,4]]::real^3^3 in
  matrix_to_list_of_list (fst (QR_decomposition A) ** (snd (QR_decomposition A))))"

definition "example5 = (let A = list_of_list_to_matrix [[1,sqrt 2,4],[sqrt 5,4,5],[0,sqrt 7,4]]::real^3^3 in
  matrix_to_list_of_list (fst (QR_decomposition A)))"

export_code example1 example2 example3 example4 example5 in SML module_name "QR"

end
