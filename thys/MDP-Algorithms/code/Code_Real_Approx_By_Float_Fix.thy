theory Code_Real_Approx_By_Float_Fix
  imports
  "HOL-Library.Code_Real_Approx_By_Float"
begin

code_printing
    constant Code_Real_Approx_By_Float.real_of_integer \<rightharpoonup>
    (SML) "Real.fromLargeInt"
  | constant "HOL.equal :: real \<Rightarrow> real \<Rightarrow> bool" \<rightharpoonup>
    (SML) "Real.abs (_ - _) < Math.pow (10.0, Real.~ 8.0)"
end