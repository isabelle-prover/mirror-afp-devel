(*  Title:      Code_Symbolic_Int_Bit.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

chapter \<open>Symbolic implementation of bit operations on int\<close>

theory Code_Symbolic_Int_Bit
imports
  Main
begin

section \<open>Implementations of bit operations on \<^typ>\<open>int\<close> operating on symbolic representation\<close>

context
  includes bit_operations_syntax
begin

lemma test_bit_int_code [code]:
  "bit (0::int)          n = False"
  "bit (Int.Neg num.One) n = True"
  "bit (Int.Pos num.One)      0 = True"
  "bit (Int.Pos (num.Bit0 m)) 0 = False"
  "bit (Int.Pos (num.Bit1 m)) 0 = True"
  "bit (Int.Neg (num.Bit0 m)) 0 = False"
  "bit (Int.Neg (num.Bit1 m)) 0 = True"
  "bit (Int.Pos num.One)      (Suc n) = False"
  "bit (Int.Pos (num.Bit0 m)) (Suc n) = bit (Int.Pos m) n"
  "bit (Int.Pos (num.Bit1 m)) (Suc n) = bit (Int.Pos m) n"
  "bit (Int.Neg (num.Bit0 m)) (Suc n) = bit (Int.Neg m) n"
  "bit (Int.Neg (num.Bit1 m)) (Suc n) = bit (Int.Neg (Num.inc m)) n"
  by (simp_all add: Num.add_One bit_0 bit_Suc)

lemma int_not_code [code]:
  "NOT (0 :: int) = -1"
  "NOT (Int.Pos n) = Int.Neg (Num.inc n)"
  "NOT (Int.Neg n) = Num.sub n num.One"
  by (simp_all add: Num.add_One not_int_def)

lemma int_and_code [code]: fixes i j :: int shows
  "0 AND j = 0"
  "i AND 0 = 0"
  "Int.Pos n AND Int.Pos m = (case and_num n m of None \<Rightarrow> 0 | Some n' \<Rightarrow> Int.Pos n')"
  "Int.Neg n AND Int.Neg m = NOT (Num.sub n num.One OR Num.sub m num.One)"
  "Int.Pos n AND Int.Neg num.One = Int.Pos n"
  "Int.Pos n AND Int.Neg (num.Bit0 m) = Num.sub (or_not_num_neg (Num.BitM m) n) num.One"
  "Int.Pos n AND Int.Neg (num.Bit1 m) = Num.sub (or_not_num_neg (num.Bit0 m) n) num.One"
  "Int.Neg num.One AND Int.Pos m = Int.Pos m"
  "Int.Neg (num.Bit0 n) AND Int.Pos m = Num.sub (or_not_num_neg (Num.BitM n) m) num.One"
  "Int.Neg (num.Bit1 n) AND Int.Pos m = Num.sub (or_not_num_neg (num.Bit0 n) m) num.One"
  apply (auto simp add: and_num_eq_None_iff [where ?'a = int] and_num_eq_Some_iff [where ?'a = int]
    split: option.split)
     apply (simp_all only: sub_one_eq_not_neg numeral_or_not_num_eq minus_minus and_not_numerals
       bit.de_Morgan_disj bit.double_compl and_not_num_eq_None_iff and_not_num_eq_Some_iff ac_simps)
  done

lemma int_or_code [code]: fixes i j :: int shows
  "0 OR j = j"
  "i OR 0 = i"
  "Int.Pos n OR Int.Pos m = Int.Pos (or_num n m)"
  "Int.Neg n OR Int.Neg m = NOT (Num.sub n num.One AND Num.sub m num.One)"
  "Int.Pos n OR Int.Neg num.One = Int.Neg num.One"
  "Int.Pos n OR Int.Neg (num.Bit0 m) = (case and_not_num (Num.BitM m) n of None \<Rightarrow> -1 | Some n' \<Rightarrow> Int.Neg (Num.inc n'))"
  "Int.Pos n OR Int.Neg (num.Bit1 m) = (case and_not_num (num.Bit0 m) n of None \<Rightarrow> -1 | Some n' \<Rightarrow> Int.Neg (Num.inc n'))"
  "Int.Neg num.One OR Int.Pos m = Int.Neg num.One"
  "Int.Neg (num.Bit0 n) OR Int.Pos m = (case and_not_num (Num.BitM n) m of None \<Rightarrow> -1 | Some n' \<Rightarrow> Int.Neg (Num.inc n'))"
  "Int.Neg (num.Bit1 n) OR Int.Pos m = (case and_not_num (num.Bit0 n) m of None \<Rightarrow> -1 | Some n' \<Rightarrow> Int.Neg (Num.inc n'))"
  apply (auto simp add: numeral_or_num_eq split: option.splits)
         apply (simp_all only: and_not_num_eq_None_iff and_not_num_eq_Some_iff and_not_numerals
           numeral_or_not_num_eq or_int_def bit.double_compl ac_simps flip: numeral_eq_iff [where ?'a = int])
         apply simp_all
  done

lemma int_xor_code [code]: fixes i j :: int shows
  "0 XOR j = j"
  "i XOR 0 = i"
  "Int.Pos n XOR Int.Pos m = (case xor_num n m of None \<Rightarrow> 0 | Some n' \<Rightarrow> Int.Pos n')"
  "Int.Neg n XOR Int.Neg m = Num.sub n num.One XOR Num.sub m num.One"
  "Int.Neg n XOR Int.Pos m = NOT (Num.sub n num.One XOR Int.Pos m)"
  "Int.Pos n XOR Int.Neg m = NOT (Int.Pos n XOR Num.sub m num.One)"
  by (simp_all add: xor_num_eq_None_iff [where ?'a = int] xor_num_eq_Some_iff [where ?'a = int] split: option.split)

declare [[code drop: \<open>drop_bit :: nat \<Rightarrow> int \<Rightarrow> int\<close>]]

lemma drop_bit_int_code [code]: fixes i :: int shows
  "drop_bit 0 i = i"
  "drop_bit (Suc n) 0 = (0 :: int)"
  "drop_bit (Suc n) (Int.Pos num.One) = 0"
  "drop_bit (Suc n) (Int.Pos (num.Bit0 m)) = drop_bit n (Int.Pos m)"
  "drop_bit (Suc n) (Int.Pos (num.Bit1 m)) = drop_bit n (Int.Pos m)"
  "drop_bit (Suc n) (Int.Neg num.One) = - 1"
  "drop_bit (Suc n) (Int.Neg (num.Bit0 m)) = drop_bit n (Int.Neg m)"
  "drop_bit (Suc n) (Int.Neg (num.Bit1 m)) = drop_bit n (Int.Neg (Num.inc m))"
  by (simp_all add: drop_bit_Suc add_One)

declare [[code drop: \<open>push_bit :: nat \<Rightarrow> int \<Rightarrow> int\<close>]]

lemma push_bit_int_code [code]:
  "push_bit 0 i = i"
  "push_bit (Suc n) i = push_bit n (Int.dup i)"
  by (simp_all add: ac_simps)

end

end
