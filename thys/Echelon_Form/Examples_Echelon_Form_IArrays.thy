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
  Examples_Echelon_Form_Abstract
begin

text{*The file @{file "Examples_Echelon_Form_Abstract.thy"} is only imported to 
  include the definitions of matrices that we use in the following examples. 
  Otherwise, it could be removed.*}

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

lemma gcd_code [code]:
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

value "det test_int_3x3"

value "det test_int_3x3_03"

value "det test_int_6x6"

value "det test_int_8x8"

value "det test_int_20x20"

value "charpoly test_real_3x3"
  
value "charpoly test_real_6x6"

value "inverse_matrix test_int_3x3_02"

value "matrix_to_iarray (echelon_form_of test_int_3x3 euclid_ext2)"

value "matrix_to_iarray (echelon_form_of test_int_8x8 euclid_ext2)"

text{*The following computations are much faster when code is exported.*}

(*value "matrix_to_iarray (echelon_form_of_euclidean test_int_20x20)"*)

(*value "echelon_form_of_iarrays (matrix_to_iarray test_int_20x20) euclid_ext2"*)

(*value "matrix_to_iarray (echelon_form_of test_int_20x20 euclid_ext2)"*)

text{*The following matrix will have an integer inverse since its determinant is equal to one*}

value "det test_int_3x3_03"

value "the (matrix_to_iarray_option (inverse_matrix test_int_3x3_03))"

text{*We check that the previous inverse has been correctly computed:*}

value "matrix_matrix_mult_iarray 
              (matrix_to_iarray test_int_3x3_03) 
              (the (matrix_to_iarray_option (inverse_matrix test_int_3x3_03)))"

value "matrix_matrix_mult_iarray 
              (the (matrix_to_iarray_option (inverse_matrix test_int_3x3_03)))
              (matrix_to_iarray test_int_3x3_03)"

text{*The following matrices have determinant different from zero, 
    and thus do not have an integer inverse*}
              
value "det test_int_6x6"
              
value "matrix_to_iarray_option (inverse_matrix test_int_6x6)"

value "det test_int_20x20"
             
value "matrix_to_iarray_option (inverse_matrix test_int_20x20)"

text{*The inverse in dimension 20 has (trivial) inverse.*}

value "the (matrix_to_iarray_option (inverse_matrix (mat 1::int^20^20)))"

value "the (matrix_to_iarray_option (inverse_matrix (mat 1::int^20^20))) = matrix_to_iarray (mat 1::int^20^20)"

export_code charpoly det echelon_form_of test_int_8x8 test_int_20x20
  in SML module_name Echelon

(*Analogously, code can be exported to Haskell using the file Code_Rational presented in the
  Gauss-Jordan AFP entry.*)

end
