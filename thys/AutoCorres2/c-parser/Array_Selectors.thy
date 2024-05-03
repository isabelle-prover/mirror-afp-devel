(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Array_Selectors
  imports
    CTranslationSetup
  keywords "array_selectors" :: thy_defn
begin

named_theorems array_selectors_simps

lemmas [array_selectors_simps] =\<comment> \<open>numerals\<close>
  Arrays.arr_fupdate_same
  Arrays.arr_fupdate_other
  Numeral_Type.card_num0
  Numeral_Type.card_num1 
  Numeral_Type.card_bit0
  Numeral_Type.card_bit1
  Nat.One_nat_def
  Nat.mult_Suc_right
  Nat.mult_0_right
  Nat.Suc_not_Zero
  Num.Suc_numeral
  Num.eq_numeral_Suc
  Num.Suc_eq_numeral
  Num.less_Suc_numeral
  Num.mult_num_simps
  Num.add_num_simps
  Num.pred_numeral_simps
  Num.numeral_times_numeral
  Num.num.distinct
  Num.num.inject
  Nat.add_0_right
  Num.arith_simps
  Num.more_arith_simps
  Num.rel_simps
  Nat.Zero_not_Suc

lemmas [array_selectors_simps] =
  comp_apply
  fcp_beta

ML_file "array_selectors.ML"

experiment
begin

definition "my_array \<equiv> fupdate 3
  (apfst (\<lambda>_. 0x30) o apsnd (\<lambda>_. 43))
  (fupdate 2 (apfst (\<lambda>_. 0x20) o apsnd (\<lambda>_. 42))
  (fupdate 1 (apfst (\<lambda>_. 0x10) o apsnd (\<lambda>_. 41))
  (fupdate 0 (apfst (\<lambda>_. 0x0) o apsnd (\<lambda>_. 40))
  ((ARRAY _. (0, 0))::(32 word \<times> nat)[4]))))"

lemmas [array_selectors_simps] =
  apfst_conv
  apsnd_conv
  \<comment> \<open>in applications, the update functions are from the recursive record package,
  therefore the recursive record package simpset is included by default\<close>

array_selectors (no_recursive_record_simpset)\<comment> \<open>does not make a difference here\<close>
  my_array_sels is my_array_def

lemma "my_array.[0] \<equiv> (0, 40)"
  "my_array.[1] \<equiv> (0x10, 41)"
  "my_array.[Suc 0] \<equiv> (0x10, 41)"
  "my_array.[2] \<equiv> (0x20, 42)"
  "my_array.[3] \<equiv> (0x30, 43)"
  by (rule my_array_sels)+

end

end