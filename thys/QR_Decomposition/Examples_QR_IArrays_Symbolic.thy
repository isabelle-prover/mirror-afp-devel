(*  
    Title:      Examples_QR_IArrays_Symbolic.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section{*Examples of execution using symbolic computation and iarrays*}

theory Examples_QR_IArrays_Symbolic
imports
  Examples_QR_Abstract_Symbolic
  QR_Decomposition_IArrays
  "~~/src/HOL/Library/Code_Char"
begin

(*TODO: Check this after Isabelle2014*)
text{*When we import the Multivariate Analysis library, execution doesn't work. 
But it can be worked out deleting the following lemma from the code generator:*}

lemmas real_code_unfold_dels(1)[code_unfold del]

subsection{*Execution of the QR decomposition using symbolic computation and iarrays*}

definition "show_vec_real_iarrays v = IArray.of_fun (\<lambda>i. show_real (v !! i)) (IArray.length v)"

lemma vec_to_iarray_show_vec_real[code_unfold]: "vec_to_iarray (show_vec_real v) 
  = show_vec_real_iarrays (vec_to_iarray v)"
  unfolding show_vec_real_def show_vec_real_iarrays_def vec_to_iarray_def by auto

definition "show_matrix_real_iarrays A = IArray.of_fun (\<lambda>i. show_vec_real_iarrays (A !! i)) (IArray.length A)"

lemma matrix_to_iarray_show_matrix_real[code_unfold]: "matrix_to_iarray (show_matrix_real v) 
  = show_matrix_real_iarrays (matrix_to_iarray v)"
  unfolding show_matrix_real_iarrays_def show_matrix_real_def
  unfolding matrix_to_iarray_def 
  by (simp add: vec_to_iarray_show_vec_real)

subsubsection{*Examples*}

value "let A = list_of_list_to_matrix [[1,2,4],[9,4,5],[0,0,0]]::real^3^3 in 
  iarray_of_iarray_to_list_of_list (matrix_to_iarray (show_matrix_real (divide_by_norm A)))"

value "let A = list_of_list_to_matrix [[1,2,4],[9,4,5],[0,0,4]]::real^3^3 in
  iarray_of_iarray_to_list_of_list (matrix_to_iarray (show_matrix_real (fst (QR_decomposition A))))"

value "let A = list_of_list_to_matrix [[1,2,4],[9,4,5],[0,0,4]]::real^3^3 in
  iarray_of_iarray_to_list_of_list (matrix_to_iarray (show_matrix_real (snd (QR_decomposition A))))"

value "let A = list_of_list_to_matrix [[1,2,4],[9,4,5],[0,0,4]]::real^3^3 in
  iarray_of_iarray_to_list_of_list (matrix_to_iarray 
    (show_matrix_real ((fst (QR_decomposition A)) ** (snd (QR_decomposition A)))))"

value "let A = list_of_list_to_matrix [[1,2,4],[9,4,5],[0,0,4],[3,5,4]]::real^3^4 in
  iarray_of_iarray_to_list_of_list (matrix_to_iarray 
    (show_matrix_real ((fst (QR_decomposition A)) ** (snd (QR_decomposition A)))))"

value "let A = IArray[IArray[1,2,4],IArray[9,4,5::real],IArray[0,0,0]] in 
   iarray_of_iarray_to_list_of_list (show_matrix_real_iarrays (divide_by_norm_iarray A))"  
  
value "let A = IArray[IArray[1,2,4],IArray[9,4,5],IArray[0,0,4]]in
  iarray_of_iarray_to_list_of_list (show_matrix_real_iarrays (fst (QR_decomposition_iarrays A)))"
  
value "let A = IArray[IArray[1,2,4],IArray[9,4,5],IArray[0,0,4]] in
  iarray_of_iarray_to_list_of_list (show_matrix_real_iarrays (snd (QR_decomposition_iarrays A)))"
  
value "let A = IArray[IArray[1,2,4],IArray[9,4,5],IArray[0,0,4]] in
  iarray_of_iarray_to_list_of_list (show_matrix_real_iarrays 
    ((fst (QR_decomposition_iarrays A)) **i (snd (QR_decomposition_iarrays A))))"
  
value "let A = IArray[IArray[1,2,4],IArray[9,4,5],IArray[0,0,4],IArray[3,5,4]]in
  iarray_of_iarray_to_list_of_list (show_matrix_real_iarrays 
    ((fst (QR_decomposition_iarrays A)) **i (snd (QR_decomposition_iarrays A))))"

(*
  Limitation: if the input matrix has irrational numbers, then we won't be working in the same
  field extension so the computation will fail.
*)

(*
value[code] "let A = list_of_list_to_matrix [[1,sqrt 2,4],[sqrt 5,4,5],[0,sqrt 7,4]]::real^3^3 in
  iarray_of_iarray_to_list_of_list (matrix_to_iarray (show_matrix_real ((fst (QR_decomposition A)))))"
*)

definition "example = (let A = IArray[IArray[1,2,4],IArray[9,4,5],IArray[0,0,4],IArray[3,5,4]]in
  iarray_of_iarray_to_list_of_list (show_matrix_real_iarrays 
    ((fst (QR_decomposition_iarrays A)) **i (snd (QR_decomposition_iarrays A)))))"

export_code example in SML module_name QR

end
