(*  
    Title:      Examples_QR_IArrays_Float.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section{*Examples of execution using floats and IArrays*}

theory Examples_QR_IArrays_Float
imports
  QR_Decomposition_IArrays
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

subsection{*Examples*}

definition "example1 = (let A = list_of_list_to_matrix [[1,2,4],[9,4,5],[0,0,0]]::real^3^3 in 
  iarray_of_iarray_to_list_of_list (matrix_to_iarray (divide_by_norm A)))"

definition "example2 = (let A = list_of_list_to_matrix [[1,2,4],[9,4,5],[0,0,4]]::real^3^3 in
  iarray_of_iarray_to_list_of_list (matrix_to_iarray (fst (QR_decomposition A))))" 

definition "example3 = (let A = list_of_list_to_matrix [[1,2,4],[9,4,5],[0,0,4]]::real^3^3 in
  iarray_of_iarray_to_list_of_list (matrix_to_iarray (snd (QR_decomposition A))))"

definition "example4 = (let A = list_of_list_to_matrix [[1,2,4],[9,4,5],[0,0,4]]::real^3^3 in
  iarray_of_iarray_to_list_of_list (matrix_to_iarray (fst (QR_decomposition A) ** (snd (QR_decomposition A)))))"

definition "example5 = (let A = list_of_list_to_matrix [[1,sqrt 2,4],[sqrt 5,4,5],[0,sqrt 7,4]]::real^3^3 in
  iarray_of_iarray_to_list_of_list (matrix_to_iarray (fst (QR_decomposition A))))"

(*Now there is no problem if there are square roots in the input matrix.*)

definition "example6 = (let A = list_of_list_to_matrix [[1,sqrt 2,4],[sqrt 5,4,5],[0,sqrt 7,4]]::real^3^3 in
  iarray_of_iarray_to_list_of_list (matrix_to_iarray ((fst (QR_decomposition A)))))"
  
definition "example1b = (let A = IArray[IArray[1,2,4],IArray[9,4,5::real],IArray[0,0,0]] in 
   iarray_of_iarray_to_list_of_list ((divide_by_norm_iarray A)))"  
  
definition "example2b = (let A = IArray[IArray[1,2,4],IArray[9,4,5],IArray[0,0,4]]in
  iarray_of_iarray_to_list_of_list ((fst (QR_decomposition_iarrays A))))"
  
definition "example3b = (let A = IArray[IArray[1,2,4],IArray[9,4,5],IArray[0,0,4]] in
  iarray_of_iarray_to_list_of_list ( (snd (QR_decomposition_iarrays A))))"
  
definition "example4b = (let A = IArray[IArray[1,2,4],IArray[9,4,5],IArray[0,0,4]] in
  iarray_of_iarray_to_list_of_list ( 
    ((fst (QR_decomposition_iarrays A)) **i (snd (QR_decomposition_iarrays A)))))"
  
definition "example5b = (let A = IArray[IArray[1,2,4],IArray[9,4,5],IArray[0,0,4],IArray[3,5,4]]in
  iarray_of_iarray_to_list_of_list ( 
    ((fst (QR_decomposition_iarrays A)) **i (snd (QR_decomposition_iarrays A)))))"
  
definition "example6b = (let A = IArray [IArray[1,sqrt 2,4],IArray[sqrt 5,4,5],IArray[0,sqrt 7,4]]
  in iarray_of_iarray_to_list_of_list (fst (QR_decomposition_iarrays A)))"

text{*The following example is presented in Chapter 1 of the book
@{text "Numerical Methods in Scientific Computing"} by Dahlquist and Bjorck*}

definition "book_example = (let A = list_of_list_to_matrix 
  [[1,-0.6691],[1,-0.3907],[1,-0.1219],[1,0.3090],[1,0.5878]]::real^2^5; 
  b = list_to_vec [0.3704,0.5,0.6211,0.8333,0.9804]::real^5;
  QR = (QR_decomposition A);
  Q = fst QR;
  R = snd QR
  in IArray.list_of (vec_to_iarray (the (inverse_matrix R) ** transpose Q *v b)))"

export_code example1 example2 example3 example4 example5 example6 
            example1b example2b example3b example4b example5b example6b book_example
            in SML module_name "QR"

end
