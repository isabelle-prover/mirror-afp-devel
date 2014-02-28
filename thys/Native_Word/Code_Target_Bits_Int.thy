(*  Title:      Code_Target_Bits_Int.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

header {* Implementation of bit operations on int by target language operations *}

theory Code_Target_Bits_Int
imports
  "Bits_Integer"
  "~~/src/HOL/Library/Code_Target_Int"
begin

lemma [code, code del]: "bitAND = (bitAND :: int \<Rightarrow> _)" ..
lemma [code, code del]: "bitOR = (bitOR :: int \<Rightarrow> _)" ..
lemma [code, code del]: "bitXOR = (bitXOR :: int \<Rightarrow> _)" ..
lemma [code, code del]: "bitNOT = (bitNOT :: int \<Rightarrow> _)" ..
lemma [code, code del]: "bin_last = bin_last" ..
lemma [code, code del]: "bin_rest = bin_rest" ..
lemma [code, code del]: "bin_nth = bin_nth" ..
lemma [code, code del]: "Bit = Bit" ..
lemma [code, code del]: "test_bit = (test_bit :: int \<Rightarrow> _)" ..
lemma [code, code del]: "lsb = (lsb :: int \<Rightarrow> _)" ..
lemma [code, code del]: "set_bit = (set_bit :: int \<Rightarrow> _)" ..
lemma [code, code del]: "shiftl = (shiftl :: int \<Rightarrow> _)" ..
lemma [code, code del]: "shiftr = (shiftr :: int \<Rightarrow> _)" ..
lemma [code, code del]: "int_of_integer_symbolic = int_of_integer_symbolic" ..

context
includes integer.lifting
begin

lemma bitAND_int_code [code]:
  "int_of_integer i AND int_of_integer j = int_of_integer (i AND j)"
by transfer simp

lemma bitOR_int_code [code]:
  "int_of_integer i OR int_of_integer j = int_of_integer (i OR j)"
by transfer simp

lemma bitXOR_int_code [code]:
  "int_of_integer i XOR int_of_integer j = int_of_integer (i XOR j)"
by transfer simp

lemma bitNOT_int_code [code]:
  "NOT (int_of_integer i) = int_of_integer (NOT i)"
by transfer simp

declare bin_last_conv_AND [code]

lemma bin_rest_code [code]:
   "bin_rest (int_of_integer i) = int_of_integer (bin_rest_integer i)"
by transfer simp

declare bitval_bin_last [code_unfold]

declare bin_nth_conv_AND [code]

lemma Bit_code [code]: "int_of_integer i BIT b = int_of_integer (Bit_integer i b)"
by transfer simp

lemma test_bit_int_code [code]: "int_of_integer x !! n = x !! n"
by transfer simp

lemma lsb_int_code [code]: "lsb (int_of_integer x) = lsb x"
by transfer simp

lemma set_bit_int_code [code]: "set_bit (int_of_integer x) n b = int_of_integer (set_bit x n b)"
by transfer simp

lemma shiftl_int_code [code]: "int_of_integer x << n = int_of_integer (x << n)"
by transfer simp

lemma shiftr_int_code [code]: "int_of_integer x >> n = int_of_integer (x >> n)"
by transfer simp

lemma int_of_integer_symbolic_code [code]:
  "int_of_integer_symbolic = int_of_integer"
by(simp add: int_of_integer_symbolic_def[abs_def])

end

code_identifier code_module Code_Target_Bits_Int \<rightharpoonup>
  (SML) Bit_Int and (OCaml) Bit_Int and (Haskell) Bit_Int and (Scala) Bit_Int

end
