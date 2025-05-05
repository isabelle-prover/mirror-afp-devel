(*
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Code Equations for All Algorithms\<close>

text \<open>In this theory we load all executable algorithms, i.e., Gauss-Jordan, determinants,
  Jordan normal form computation.\<close>

theory Matrix_Impl
imports 
  Matrix_IArray_Impl
  Gauss_Jordan_IArray_Impl
  Determinant_Impl
  Show_Matrix
  Shows_Literal_Matrix
  Jordan_Normal_Form_Existence
  Show.Show_Instances
begin

end
