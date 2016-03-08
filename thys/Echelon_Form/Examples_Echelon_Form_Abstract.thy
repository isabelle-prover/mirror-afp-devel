(*  
    Title:      Examples_Echelon_Form_Abstract.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section{*Examples of execution over matrices represented as functions*}

theory Examples_Echelon_Form_Abstract
imports
  "Code_Cayley_Hamilton"
  "../Gauss_Jordan/Examples_Gauss_Jordan_Abstract"
  Echelon_Form_Inverse
begin

text{*The definitions introduced in this file will be also used in 
  the computations presented in file @{file "Examples_Echelon_Form_IArrays.thy"}. 
  Some of these definitions are not even used in this file since they are quite 
  time consuming.*}

definition test_real_6x4 :: "real^6^4"
  where "test_real_6x4 = list_of_list_to_matrix
        [[0,0,0,0,0,0],
         [0,1,0,0,0,0],
         [0,0,0,0,0,0],
         [0,0,0,0,8,2]]"
  
value "matrix_to_list_of_list (minorM test_real_6x4 0 0)"

value "cofactor (mat 1::rat^3^3) 0 0"

value "vec_to_list (cofactorM_row  (mat 1::int^3^3) 1)"

value "matrix_to_list_of_list (cofactorM  (mat 1::int^3^3))"

definition test_rat_3x3 :: "rat^3^3"
  where "test_rat_3x3 = list_of_list_to_matrix [[3,5,1],[2,1,3],[1,2,1]]"

value "matrix_to_list_of_list (matpow test_rat_3x3 5)" 

definition test_int_3x3 :: "int^3^3"
  where "test_int_3x3 = list_of_list_to_matrix [[3,2,8], [0,3,9], [8,7,9]]"

value "det test_int_3x3"

definition test_real_3x3 :: "real^3^3"
  where "test_real_3x3 = list_of_list_to_matrix [[3,5,1],[2,1,3],[1,2,1]]"

value "charpoly test_real_3x3"

text{*We check that the Cayley-Hamilton theorem holds for this particular case:*}

value "matrix_to_list_of_list (evalmat (charpoly test_real_3x3) test_real_3x3)"

definition test_int_3x3_02 :: "int^3^3"
  where "test_int_3x3_02 = list_of_list_to_matrix [[3,5,1],[2,1,3],[1,2,1]]"

value "matrix_to_list_of_list (adjugate test_int_3x3_02)"

text{*The following integer matrix is not invertible, so the result is @{text "None"}*}

value "inverse_matrix test_int_3x3_02"

definition test_int_3x3_03 :: "int^3^3"
  where "test_int_3x3_03 = list_of_list_to_matrix [[1,-2,4],[1,-1,1],[0,1,-2]]"

value "matrix_to_list_of_list (the (inverse_matrix test_int_3x3_03))"

text{*We check that the previous inverse has been correctly computed:*}

value "test_int_3x3_03 ** (the (inverse_matrix test_int_3x3_03)) = (mat 1::int^3^3)"

definition test_int_8x8 :: "int^8^8"
  where "test_int_8x8 = list_of_list_to_matrix 
       [[ 3, 2, 3, 6, 2, 8, 5, 6],
        [ 0, 5, 5, 2, 3, 9, 4, 7],
        [ 8, 7, 9, 1, 4,-2, 2, 0],
        [ 0, 1, 5, 6, 5, 1, 1, 4],
        [ 0, 3, 4, 5, 2,-4, 2, 1],
        [ 6, 8, 6, 2, 2,-3, 3, 5],
        [-2, 4,-2, 6, 7, 8, 0, 3],
        [ 7, 1, 3, 0,-9,-3, 4,-5]]"

text{*SLOW; several minutes.*}

(*value "det test_int_8x8"

value "matrix_to_list_of_list (echelon_form_of test_int_8x8 euclid_ext2)"*)

text{*The following definitions will be used in 
  file @{file "Examples_Echelon_Form_IArrays.thy"}.
  Using the abstract version of matrices would produce lengthy computations.*}

definition test_int_6x6 :: "int^6^6"
  where "test_int_6x6 = list_of_list_to_matrix 
    [[ 3, 2, 3, 6, 2, 8],
     [ 0, 5, 5, 2, 3, 9],
     [ 8, 7, 9, 1, 4,-2],
     [ 0, 1, 5, 6, 5, 1],
     [ 0, 3, 4, 5, 2,-4],
     [ 6, 8, 6, 2, 2,-3]]"

definition test_real_6x6 :: "real^6^6"
  where "test_real_6x6 = list_of_list_to_matrix 
    [[ 3, 2, 3, 6, 2, 8],
     [ 0, 5, 5, 2, 3, 9],
     [ 8, 7, 9, 1, 4,-2],
     [ 0, 1, 5, 6, 5, 1],
     [ 0, 3, 4, 5, 2,-4],
     [ 6, 8, 6, 2, 2,-3]]"

definition test_int_20x20 :: "int^20^20"
  where "test_int_20x20 =  list_of_list_to_matrix 
    [[3,2,3,6,2,8,5,9,8,7,5,4,7,8,9,8,7,4,5,2],
     [0,5,5,2,3,9,1,2,4,6,1,2,3,6,5,4,5,8,7,1],
     [8,7,9,1,4,-2,8,7,1,4,1,4,5,8,7,4,1,0,0,2],
     [0,1,5,6,5,1,3,5,4,9,3,2,1,4,5,6,9,8,7,4],
     [0,3,4,5,2,-4,0,2,1,0,0,0,1,2,4,5,1,1,2,0],
     [6,8,6,2,2,-3,2,4,7,9,1,2,3,6,5,4,1,2,8,7],
     [3,8,3,6,2,8,8,9,6,7,8,9,7,8,9,5,4,1,2,3,0],
     [0,8,5,2,8,9,1,2,4,6,4,6,5,8,7,9,8,7,4,5],
     [8,8,8,1,4,-2,8,7,1,4,5,5,5,6,4,5,1,2,3,6],
     [0,8,5,6,5,1,3,5,4,9::int,1,2,3,5,4,7,8,9,6,4],
     [3,2,3,6,2,8,5,9,8,7,5,4,7,3,9,8,7,4,5,2],
     [0,5,5,2,3,9,1,2,4,3,1,2,3,6,5,4,5,8,7,1],
     [1,7,9,1,4,-2,8,7,1,4,1,4,5,8,7,4,1,0,0,2],
     [1,1,5,6,5,1,3,5,4,9,3,4,5,6,9,8,7,4,5,4],
     [3,3,4,5,2,-4,0,2,1,0,0,3,1,2,4,5,1,1,2,0],
     [4,8,6,5,2,-3,2,4,2,9,1,2,3,2,5,4,1,2,8,7],
     [5,8,3,6,2,2,9,9,6,7,2,7,7,2,9,5,4,1,2,3,0],
     [2,8,5,2,8,9,5,2,4,6,4,6,5,2,7,1,8,7,4,5],
     [2,1,8,1,4,-2,8,3,1,4,5,5,5,6,4,5,1,2,3,6],
     [0,2,5,6,5,1,3,5,4,9::int,1,2,3,5,4,7,8,9,6,4]]"
     
end

