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

value "let A = list_of_list_to_matrix 
  ([[0,0,0,0,0,0],[0,1,0,0,0,0],[0,0,0,0,0,0],[0,0,0,0,8,2]])::real^6^4 in
  matrix_to_list_of_list (minorM A 0 0)"

value "let A = list_of_list_to_matrix ([[1,0,0],[0,1,0],[0,0,1]])::rat^3^3
  in (cofactor A 0 0)"

value "let A = list_of_list_to_matrix ([[1,0,0],[0,1,0],[0,0,1]])::int^3^3
  in vec_to_list (cofactorM_row A 1)"

value "let A = list_of_list_to_matrix ([[1,0,0],[0,1,0],[0,0,1]])::int^3^3
  in matrix_to_list_of_list (cofactorM A)"

value "let A = list_of_list_to_matrix ([[3,5,1],[2,1,3],[1,2,1]])::rat^3^3
  in matrix_to_list_of_list (matpow A 5)"

value "let A = (list_of_list_to_matrix 
  [[3,2,8],
  [0,3,9],
  [8,7,9]]::int^3^3) in det A"

value "let A = list_of_list_to_matrix ([[3,5,1],[2,1,3],[1,2,1]])::real^3^3
  in (charpoly A)"

value "let A = list_of_list_to_matrix ([[3,5,1],[2,1,3],[1,2,1]])::real^3^3
  in matrix_to_list_of_list (evalmat (charpoly A) A)"

value "let A = list_of_list_to_matrix ([[3,5,1],[2,1,3],[1,2,1]])::int^3^3
  in matrix_to_list_of_list (adjugate A)"

value "let A = list_of_list_to_matrix ([[3,5,1],[2,1,3],[1,2,1]])::int^3^3
  in (inverse_matrix A)"

value "let A = list_of_list_to_matrix ([[1,-2,4],[1,-1,1],[0,1,-2]])::int^3^3
  in matrix_to_list_of_list (the (inverse_matrix A))"

end
