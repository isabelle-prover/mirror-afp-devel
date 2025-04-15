(*  Title:      Code_Target_Int_Bit.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

chapter \<open>Implementation of bit operations on int by target language operations\<close>

theory Code_Target_Int_Bit
  imports
    "HOL-Library.Code_Target_Int"
    Code_Int_Integer_Conversion
    "HOL-Library.Code_Bit_Shifts_for_Arithmetic"
begin

lemma int_of_integer_symbolic_code [code drop: int_of_integer_symbolic, code]:
  "int_of_integer_symbolic = int_of_integer"
  by (fact int_of_integer_symbolic_def)

end
