theory Code_Real_Approx_By_Float_Fix
  imports
  "HOL-Library.Code_Real_Approx_By_Float"
  "Gauss_Jordan.Code_Real_Approx_By_Float_Haskell"
begin
(*<*)
section \<open>Fix for Floating Point Approximation using Haskell\<close>

code_printing
  type_constructor real \<rightharpoonup> (Haskell) "Prelude.Double" (*Double precision*)
  | constant "0 :: real" \<rightharpoonup> (Haskell) "0.0"
  | constant "1 :: real" \<rightharpoonup> (Haskell) "1.0"
  | constant "Code_Real_Approx_By_Float.real_of_integer" \<rightharpoonup> (Haskell) "Prelude.fromIntegral (_)"
  | class_instance real :: "HOL.equal" => (Haskell) - (*This is necessary. See the tutorial on code generation, page 29*)
  | constant "HOL.equal :: real \<Rightarrow> real \<Rightarrow> bool" \<rightharpoonup>
    (Haskell) "_ == _"
  |  constant "(<) :: real => real => bool" \<rightharpoonup>
    (Haskell) "_ < _"
  |  constant "(\<le>) :: real => real => bool" \<rightharpoonup>
    (Haskell) "_ <= _"
  | constant "(+) :: real \<Rightarrow> real \<Rightarrow> real" \<rightharpoonup>
    (Haskell) "_ + _"
  | constant "(-) :: real \<Rightarrow> real \<Rightarrow> real" \<rightharpoonup>
    (Haskell) "_ - _"
  | constant "(*) :: real \<Rightarrow> real \<Rightarrow> real" \<rightharpoonup>
    (Haskell) "_ * _"
  | constant "(/) :: real \<Rightarrow> real \<Rightarrow> real" \<rightharpoonup>
    (Haskell) "_ '/ _"
  | constant "uminus :: real => real" \<rightharpoonup>
    (Haskell) "Prelude.negate"
  | constant "sqrt :: real => real" \<rightharpoonup>
    (Haskell) "Prelude.sqrt" 
  | constant Code_Real_Approx_By_Float.exp_real \<rightharpoonup>
    (Haskell) "Prelude.exp"
  | constant ln \<rightharpoonup>
    (Haskell) "Prelude.log"
  | constant cos \<rightharpoonup>
    (Haskell) "Prelude.cos"
  | constant sin \<rightharpoonup>
    (Haskell) "Prelude.sin"
  | constant tan \<rightharpoonup>
    (Haskell) "Prelude.tan"
  | constant pi \<rightharpoonup>
    (Haskell) "Prelude.pi"
  | constant arctan \<rightharpoonup>
    (Haskell) "Prelude.atan"
  | constant arccos \<rightharpoonup>
    (Haskell) "Prelude.acos"
  | constant arcsin \<rightharpoonup>
    (Haskell) "Prelude.asin"

code_printing
  constant Realfract \<rightharpoonup> (Haskell) 
    "(Prelude.fromIntegral (integer'_of'_int _) '/ Prelude.fromIntegral (integer'_of'_int _))"

code_printing
  constant Realfract \<rightharpoonup> (SML) "(Real.fromInt (IntInf.toInt (integer'_of'_int _))) '// Real.fromInt (IntInf.toInt (integer'_of'_int _))"
(*>*)
end