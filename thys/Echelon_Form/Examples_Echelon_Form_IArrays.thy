(*  
    Title:      Examples_Echelon_Form_IArrays.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section{*Examples of computations using immutable arrays*}

theory Examples_Echelon_Form_IArrays
imports 
  Echelon_Form_Inverse_IArrays
  "~~/src/HOL/Library/Code_Target_Numeral"
  "../Gauss_Jordan/Examples_Gauss_Jordan_Abstract"
begin

subsection{*Computing echelon forms, determinants, characteristic polynomials and so on using
  immutable arrays*}

subsubsection{*Serializing gcd*}

text{*First of all, we serialize the gcd to the ones of PolyML and MLton as we did in the
  Gauss-Jordan development.*}

context
includes integer.lifting
begin

lift_definition gcd_integer :: "integer => integer => integer"
  is "gcd :: int => int => int" .

lemma gcd_integer_code [code]:
"gcd_integer l k = \<bar>if l = (0::integer) then k else gcd_integer l (\<bar>k\<bar> mod \<bar>l\<bar>)\<bar>"
by transfer (simp add: gcd_code_int [symmetric] ac_simps)

end

code_printing
 constant "abs :: integer => _" \<rightharpoonup> (SML) "IntInf.abs"
 | constant "gcd_integer :: integer => _ => _" \<rightharpoonup> (SML) "(PolyML.IntInf.gcd ((_),(_)))" (*Only for Poly/ML*)
 (* | constant "gcd_integer :: integer => _ => _" \<rightharpoonup> (SML) "(MLton.IntInf.gcd ((_),(_)))"*) (*Only for MLton*)

lemma gcd_code[code]:
"gcd a b = int_of_integer (gcd_integer (of_int a) (of_int b))"
  by (metis gcd_integer.abs_eq int_of_integer_integer_of_int integer_of_int_eq_of_int)

code_printing
  constant "abs :: real => real" \<rightharpoonup>
    (SML) "Real.abs"

lemma [code, code del]:
  "(abs :: real => real) = abs"
  ..
  
code_printing
constant "divmod_integer :: integer => _ => _" \<rightharpoonup> (SML) "(IntInf.divMod ((_),(_)))"

subsubsection{*Examples*}

(*
definition "matrix_20 = (
  IArray[
  IArray[3,2,3,6,2,8,5,9,8,7,5,4,7,8,9,8,7,4,5,2],
  IArray[0,5,5,2,3,9,1,2,4,6,1,2,3,6,5,4,5,8,7,1],
  IArray[8,7,9,1,4,-2,8,7,1,4,1,4,5,8,7,4,1,0,0,2],
  IArray[0,1,5,6,5,1,3,5,4,9,3,2,1,4,5,6,9,8,7,4],
  IArray[0,3,4,5,2,-4,0,2,1,0,0,0,1,2,4,5,1,1,2,0],
  IArray[6,8,6,2,2,-3,2,4,7,9,1,2,3,6,5,4,1,2,8,7],
  IArray[3,8,3,6,2,8,8,9,6,7,8,9,7,8,9,5,4,1,2,3,0],
  IArray[0,8,5,2,8,9,1,2,4,6,4,6,5,8,7,9,8,7,4,5],
  IArray[8,8,8,1,4,-2,8,7,1,4,5,5,5,6,4,5,1,2,3,6],
  IArray[0,8,5,6,5,1,3,5,4,9::int,1,2,3,5,4,7,8,9,6,4],
  IArray[3,2,3,6,2,8,5,9,8,7,5,4,7,3,9,8,7,4,5,2],
  IArray[0,5,5,2,3,9,1,2,4,3,1,2,3,6,5,4,5,8,7,1],
  IArray[1,7,9,1,4,-2,8,7,1,4,1,4,5,8,7,4,1,0,0,2],
  IArray[1,1,5,6,5,1,3,5,4,9,3,4,5,6,9,8,7,4,5,4],
  IArray[3,3,4,5,2,-4,0,2,1,0,0,3,1,2,4,5,1,1,2,0],
  IArray[4,8,6,5,2,-3,2,4,2,9,1,2,3,2,5,4,1,2,8,7],
  IArray[5,8,3,6,2,2,9,9,6,7,2,7,7,2,9,5,4,1,2,3,0],
  IArray[2,8,5,2,8,9,5,2,4,6,4,6,5,2,7,1,8,7,4,5],
  IArray[2,1,8,1,4,-2,8,3,1,4,5,5,5,6,4,5,1,2,3,6],
  IArray[0,2,5,6,5,1,3,5,4,9::int,1,2,3,5,4,7,8,9,6,4]
  ])"
*)

definition "matrix_reals = (IArray 
  [IArray[3,2,3,6,2,8],
  IArray[0,5,5,2,3,9],
  IArray[8,7,9,1,4,-2],
  IArray[0,1,5,6,5,1],
  IArray[0,3,4,5,2,-4],
  IArray[6,8,6,2,2,-3::real]])"

definition "matrix_int = (IArray 
  [IArray[3,2,3,6,2,8],
  IArray[0,5,5,2,3,9],
  IArray[8,7,9,1,4,-2],
  IArray[0,1,5,6,5,1],
  IArray[0,3,4,5,2,-4],
  IArray[6,8,6,2,2,-3::int]])"

definition "Test1 = charpoly_iarrays (matrix_reals)"
definition "Test2 = det_iarrays_rings (matrix_int)"

(*value "det_iarrays_rings matrix_20"*)
value "Test1"
value "Test2"

value "let A = (list_of_list_to_matrix 
  [[3,2,3,6,2,8],
  [0,5,5,2,3,9],
  [8,7,9,1,4,-2],
  [0,1,5,6,5,1],
  [0,3,4,5,2,-4],
  [6,8,6,2,2,-3]]::int^6^6) in det A"

value "let A = (IArray[IArray[3,2,3,6],
  IArray[0,5,5,2],IArray[8,7,9,1],IArray[0::int,1,5,6]]) in det_iarrays_rings A"

value "let A = (list_of_list_to_matrix 
  [[3,2,3,6,2,8],
  [0,5,5,2,3,9],
  [8,7,9,1,4,-2],
  [0,1,5,6,5,1],
  [0,3,4,5,2,-4],
  [6,8,6,2,2,-3]]::real^6^6) in charpoly A"

value "let A = (list_of_list_to_matrix 
  [[3,2,3,6,2,8],
  [0,5,5,2,3,9],
  [8,7,9,1,4,-2],
  [0,1,5,6,5,1],
  [0,3,4,5,2,-4],
  [6,8,6,2,2,-3]]::real^6^6) in charpoly A"

text{*The following integer matrix is not invertible, so the result is @{text "None"}*}
value "let A = (IArray[IArray[3,5,1],IArray[2,1,3],IArray[1,2,1::int]])
  in (inverse_matrix_ring_iarray A)"

text{*The following integer matrix is invertible*}

value "let A = (IArray[IArray[1,-2,4],IArray[1,-1,1],IArray[0,1,-2::int]])
  in (the (inverse_matrix_ring_iarray A))"

export_code charpoly_iarrays matrix_reals (*matrix_20*) matrix_int Test1 Test2 
  in SML module_name Echelon

(*Analogously, code can be exported to Haskell using the file Code_Rational presented in the
  Gauss-Jordan AFP entry.*)

end
