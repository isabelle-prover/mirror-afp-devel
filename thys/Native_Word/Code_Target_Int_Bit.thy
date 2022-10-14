(*  Title:      Code_Target_Int_Bit.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

chapter \<open>Implementation of bit operations on int by target language operations\<close>

theory Code_Target_Int_Bit
  imports
  Code_Target_Integer_Bit
  "HOL-Library.Code_Target_Int"
begin

context
  includes bit_operations_syntax
begin

declare [[code drop:
  "lsb :: int \<Rightarrow> _" int_of_integer_symbolic
  ]]

lemma [code_unfold]:
  \<open>of_bool (odd i) = i AND 1\<close> for i :: int
  by (simp add: and_one_eq mod2_eq_if)

lemma [code_unfold]:
  \<open>bit x n \<longleftrightarrow> x AND (push_bit n 1) \<noteq> 0\<close> for x :: int
  by (fact bit_iff_and_push_bit_not_eq_0)

context
includes integer.lifting
begin

lemma lsb_int_code [code]:
  "lsb (int_of_integer x) = lsb x"
  by transfer simp

lemma set_bit_int_code [code]:
  "set_bit (int_of_integer x) n b = int_of_integer (set_bit x n b)"
  by transfer simp

lemma int_of_integer_symbolic_code [code]:
  "int_of_integer_symbolic = int_of_integer"
  by (simp add: int_of_integer_symbolic_def)

context
begin

qualified definition even :: \<open>int \<Rightarrow> bool\<close>
  where [code_abbrev]: \<open>even = Parity.even\<close>

end

lemma [code]:
  \<open>Code_Target_Int_Bit.even i \<longleftrightarrow> i AND 1 = 0\<close>
  by (simp add: Code_Target_Int_Bit.even_def even_iff_mod_2_eq_zero and_one_eq)

lemma bin_rest_code:
  "int_of_integer i div 2 = int_of_integer (bin_rest_integer i)"
  by transfer simp

end

end

end
