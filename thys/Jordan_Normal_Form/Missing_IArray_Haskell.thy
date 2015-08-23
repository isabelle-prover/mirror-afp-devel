(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Haskell Serialization for IArrays\<close>

text \<open>Since we are going to implement matrices via IArrays, we are also interested
  in the Haskell serialization in the AFP-entry Gauss-Jordan of J.\ Divas\'on and
  J.\ Aransay \cite{Gauss_Jordan-AFP}.
 
  This following theory just fixes one omission, that there is no need to derive
  the Eq-class code for IArrays, as it conflicts with the class instance already
  provided in Haskell. Once this is fixed in their AFP-entry, this file should be 
  deleted.\<close>
theory Missing_IArray_Haskell
imports
  "../Gauss_Jordan/IArray_Haskell"
begin

code_printing
  class_instance iarray :: "HOL.equal" \<rightharpoonup> (Haskell) -

end