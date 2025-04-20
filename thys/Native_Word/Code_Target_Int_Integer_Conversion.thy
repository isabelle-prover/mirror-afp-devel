(*  Title:      Code_Target_Int_Integer_Conversion.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

chapter \<open>Implementation of conversion of integer to int\<close>

theory Code_Target_Int_Integer_Conversion
  imports
    "HOL-Library.Code_Target_Int"
    Code_Int_Integer_Conversion
begin

lemma int_of_integer_symbolic_code [code drop: int_of_integer_symbolic, code]:
  "int_of_integer_symbolic = int_of_integer"
  by (fact int_of_integer_symbolic_def)

end
