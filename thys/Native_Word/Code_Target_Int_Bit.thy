(*  Title:      Code_Target_Int_Bit.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

chapter \<open>Implementation of bit operations on int by target language operations\<close>

theory Code_Target_Int_Bit
  imports
    "HOL-Library.Code_Target_Int"
    "HOL-Library.Code_Target_Bit_Shifts"
    Code_Int_Integer_Conversion
begin

lemma int_of_integer_symbolic_code [code drop: int_of_integer_symbolic, code]:
  "int_of_integer_symbolic = int_of_integer"
  by (fact int_of_integer_symbolic_def)

context
  includes bit_operations_syntax  
begin

context
begin

qualified definition even :: \<open>int \<Rightarrow> bool\<close>
  where [code_abbrev]: \<open>even = Parity.even\<close>

end

lemma [code]:
  \<open>Code_Target_Int_Bit.even i \<longleftrightarrow> i AND 1 = 0\<close>
  by (simp add: Code_Target_Int_Bit.even_def even_iff_mod_2_eq_zero and_one_eq)

lemma [code_unfold]:
  \<open>of_bool (odd i) = i AND 1\<close> for i :: int
  by (simp add: and_one_eq mod2_eq_if)

lemma [code_unfold]:
  \<open>bit x n \<longleftrightarrow> x AND (push_bit n 1) \<noteq> 0\<close> for x :: int
  by (fact bit_iff_and_push_bit_not_eq_0)

end

end
