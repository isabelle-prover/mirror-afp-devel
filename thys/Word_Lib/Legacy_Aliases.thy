(*
 * Copyright Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section \<open>Legacy aliases\<close>

theory Legacy_Aliases
  imports "HOL-Library.Word"
begin

context abstract_boolean_algebra
begin

lemma conj_assoc: "(x \<^bold>\<sqinter> y) \<^bold>\<sqinter> z = x \<^bold>\<sqinter> (y \<^bold>\<sqinter> z)"
  by (fact conj.assoc)

lemma conj_commute: "x \<^bold>\<sqinter> y = y \<^bold>\<sqinter> x"
  by (fact conj.commute)

lemmas conj_left_commute = conj.left_commute
lemmas conj_ac = conj.assoc conj.commute conj.left_commute

lemma conj_one_left: "\<^bold>1 \<^bold>\<sqinter> x = x"
  by (fact conj.left_neutral)

lemma conj_left_absorb: "x \<^bold>\<sqinter> (x \<^bold>\<sqinter> y) = x \<^bold>\<sqinter> y"
  by (fact conj.left_idem)

lemma conj_absorb: "x \<^bold>\<sqinter> x = x"
  by (fact conj.idem)

lemma disj_assoc: "(x \<^bold>\<squnion> y) \<^bold>\<squnion> z = x \<^bold>\<squnion> (y \<^bold>\<squnion> z)"
  by (fact disj.assoc)

lemma disj_commute: "x \<^bold>\<squnion> y = y \<^bold>\<squnion> x"
  by (fact disj.commute)

lemmas disj_left_commute = disj.left_commute

lemmas disj_ac = disj.assoc disj.commute disj.left_commute

lemma disj_zero_left: "\<^bold>0 \<^bold>\<squnion> x = x"
  by (fact disj.left_neutral)

lemma disj_left_absorb: "x \<^bold>\<squnion> (x \<^bold>\<squnion> y) = x \<^bold>\<squnion> y"
  by (fact disj.left_idem)

lemma disj_absorb: "x \<^bold>\<squnion> x = x"
  by (fact disj.idem)

end

context abstract_boolean_algebra_sym_diff
begin

lemmas xor_assoc = xor.assoc
lemmas xor_commute = xor.commute
lemmas xor_left_commute = xor.left_commute

lemmas xor_ac = xor.assoc xor.commute xor.left_commute

lemma xor_zero_right: "x \<^bold>\<ominus> \<^bold>0 = x"
  by (fact xor.comm_neutral)

lemma xor_zero_left: "\<^bold>0 \<^bold>\<ominus> x = x"
  by (fact xor.left_neutral)

end

abbreviation (input) test_bit :: \<open>'a::semiring_bits \<Rightarrow> nat \<Rightarrow> bool\<close>
  where \<open>test_bit \<equiv> bit\<close>

abbreviation (input) bin_nth :: \<open>int \<Rightarrow> nat \<Rightarrow> bool\<close>
  where \<open>bin_nth \<equiv> bit\<close>

abbreviation (input) bin_last :: \<open>int \<Rightarrow> bool\<close>
  where \<open>bin_last \<equiv> odd\<close>

abbreviation (input) bin_rest :: \<open>int \<Rightarrow> int\<close>
  where \<open>bin_rest w \<equiv> w div 2\<close>

abbreviation (input) bintrunc :: \<open>nat \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>bintrunc \<equiv> take_bit\<close>

abbreviation (input) sbintrunc :: \<open>nat \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>sbintrunc \<equiv> signed_take_bit\<close>

abbreviation (input) bin_cat :: \<open>int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>bin_cat k n l \<equiv> concat_bit n l k\<close>

abbreviation (input) norm_sint :: \<open>nat \<Rightarrow> int \<Rightarrow> int\<close>
  where \<open>norm_sint n \<equiv> signed_take_bit (n - 1)\<close>

abbreviation (input) max_word :: \<open>'a::len word\<close>
  where \<open>max_word \<equiv> - 1\<close>

abbreviation (input) complement :: \<open>'a::len word \<Rightarrow> 'a word\<close>
  where \<open>complement \<equiv> not\<close>

lemma complement_mask:
  "complement (2 ^ n - 1) = not (mask n)"
  unfolding mask_eq_decr_exp by simp

abbreviation (input) shiftl1 :: \<open>'a::len word \<Rightarrow> 'a word\<close>
  where \<open>shiftl1 \<equiv> (*) 2\<close>

abbreviation (input)  shiftr1 :: \<open>'a::len word \<Rightarrow> 'a word\<close>
  where \<open>shiftr1 w \<equiv> w div 2\<close>

abbreviation (input) sshiftr1 :: \<open>'a::len word \<Rightarrow> 'a word\<close>
  where \<open>sshiftr1 \<equiv> signed_drop_bit (Suc 0)\<close>

context
  includes bit_operations_syntax
begin

abbreviation (input) bshiftr1 :: \<open>bool \<Rightarrow> 'a::len word \<Rightarrow> 'a word\<close>
  where \<open>bshiftr1 b w \<equiv> w div 2 OR push_bit (LENGTH('a) - Suc 0) (of_bool b) \<close>

end

lemma shiftr1_1: "shiftr1 (1::'a::len word) = 0"
  by (fact bits_1_div_2)

lemma sshiftr1_eq:
  \<open>sshiftr1 w = word_of_int (sint w div 2)\<close>
  by (rule bit_word_eqI) (auto simp add: bit_simps min_def simp flip: bit_Suc elim: le_SucE)

lemma shiftl1_eq:
  \<open>shiftl1 w = word_of_int (2 * uint w)\<close>
  by (rule bit_word_eqI) (simp add: bit_simps)

lemma bit_shiftl1_iff:
  \<open>bit (shiftl1 w) n \<longleftrightarrow> 0 < n \<and> n < LENGTH('a) \<and> bit w (n - 1)\<close>
  for w :: \<open>'a::len word\<close>
  by (auto simp add: bit_simps)

lemma bit_shiftr1_iff:
  \<open>bit (shiftr1 w) n \<longleftrightarrow> bit w (Suc n)\<close>
  by (simp add: bit_Suc)

lemma shiftr1_eq:
  \<open>shiftr1 w = word_of_int (uint w div 2)\<close>
  by (rule bit_word_eqI) (simp add: bit_simps flip: bit_Suc)

lemma shiftl1_rev:
  "shiftl1 w = word_reverse (shiftr1 (word_reverse w))"
  by (rule bit_word_eqI) (auto simp add: bit_simps Suc_diff_Suc simp flip: bit_Suc)

lemma shiftl1_p:
  "shiftl1 w = w + w"
  for w :: "'a::len word"
  by (fact mult_2)

lemma shiftr1_bintr:
  "(shiftr1 (numeral w) :: 'a::len word) =
    word_of_int (take_bit LENGTH('a) (numeral w) div 2)"
  by (rule bit_word_eqI) (simp add: bit_simps bit_numeral_iff [where ?'a = int] flip: bit_Suc)

lemma sshiftr1_sbintr:
  "(sshiftr1 (numeral w) :: 'a::len word) =
    word_of_int (signed_take_bit (LENGTH('a) - 1) (numeral w) div 2)"
  apply (cases \<open>LENGTH('a)\<close>)
  apply simp_all
  apply (rule bit_word_eqI)
  apply (auto simp add: bit_simps min_def simp flip: bit_Suc elim: le_SucE)
  done

lemma shiftl1_wi:
  "shiftl1 (word_of_int w) = word_of_int (2 * w)"
  by transfer simp

lemma shiftl1_numeral:
  "shiftl1 (numeral w) = numeral (Num.Bit0 w)"
  unfolding word_numeral_alt shiftl1_wi by simp

lemma shiftl1_neg_numeral:
  "shiftl1 (- numeral w) = - numeral (Num.Bit0 w)"
  unfolding word_neg_numeral_alt shiftl1_wi by simp

lemma shiftl1_0:
  "shiftl1 0 = 0"
  by (fact mult_zero_right)

lemma shiftl1_def_u:
  "shiftl1 w = word_of_int (2 * uint w)"
  by (fact shiftl1_eq)

lemma shiftl1_def_s:
  "shiftl1 w = word_of_int (2 * sint w)"
  by simp

lemma shiftr1_0:
  "shiftr1 0 = 0"
  by (fact bits_div_0)

lemma sshiftr1_0:
  "sshiftr1 0 = 0"
  by (fact signed_drop_bit_of_0)

lemma sshiftr1_n1:
  "sshiftr1 (- 1) = - 1"
  by (fact signed_drop_bit_of_minus_1)

lemma uint_shiftr1:
  "uint (shiftr1 w) = uint w div 2"
  by (rule bit_eqI) (simp add: bit_simps flip: bit_Suc)

lemma shiftr1_div_2:
  "uint (shiftr1 w) = uint w div 2"
  by (fact uint_shiftr1)

lemma sshiftr1_div_2:
  "sint (sshiftr1 w) = sint w div 2"
  by (rule bit_eqI) (auto simp add: bit_simps ac_simps min_def simp flip: bit_Suc elim: le_SucE)

lemma bit_sshiftr1_iff:
  \<open>bit (sshiftr1 w) n \<longleftrightarrow> bit w (if n = LENGTH('a) - 1 then LENGTH('a) - 1 else Suc n)\<close>
    for w :: \<open>'a::len word\<close>
  by (auto simp add: bit_simps)

lemma bit_bshiftr1_iff:
  \<open>bit (bshiftr1 b w) n \<longleftrightarrow> b \<and> n = LENGTH('a) - 1 \<or> bit w (Suc n)\<close>
    for w :: \<open>'a::len word\<close>
  by (auto simp add: bit_simps simp flip: bit_Suc)

lemma nth_shiftl1:
  "bit (shiftl1 w) n \<longleftrightarrow> n < size w \<and> n > 0 \<and> bit w (n - 1)"
  by (auto simp add: word_size bit_simps)

lemma nth_shiftr1:
  "bit (shiftr1 w) n = bit w (Suc n)"
  by (simp add: bit_Suc)

lemma nth_sshiftr1: "bit (sshiftr1 w) n = (if n = size w - 1 then bit w n else bit w (Suc n))"
  by (auto simp add: word_size bit_simps)

lemma shiftl_power:
  "(shiftl1 ^^ x) (y::'a::len word) = 2 ^ x * y"
  by (induction x) simp_all

lemma le_shiftr1:
  \<open>shiftr1 u \<le> shiftr1 v\<close> if \<open>u \<le> v\<close>
  using that by (simp add: word_le_nat_alt unat_div div_le_mono)

lemma le_shiftr1':
  "\<lbrakk> shiftr1 u \<le> shiftr1 v ; shiftr1 u \<noteq> shiftr1 v \<rbrakk> \<Longrightarrow> u \<le> v"
  by (meson dual_order.antisym le_cases le_shiftr1)

abbreviation (input) setBit :: \<open>'a::len word \<Rightarrow> nat \<Rightarrow> 'a word\<close>
  where \<open>setBit w n \<equiv> set_bit n w\<close>

abbreviation (input) clearBit :: \<open>'a::len word \<Rightarrow> nat \<Rightarrow> 'a word\<close>
  where \<open>clearBit w n \<equiv> unset_bit n w\<close>

lemma bit_setBit_iff:
  \<open>bit (setBit w m) n \<longleftrightarrow> (m = n \<and> n < LENGTH('a) \<or> bit w n)\<close>
  for w :: \<open>'a::len word\<close>
  by (auto simp add: bit_simps)

lemma bit_clearBit_iff:
  \<open>bit (clearBit w m) n \<longleftrightarrow> m \<noteq> n \<and> bit w n\<close>
  for w :: \<open>'a::len word\<close>
  by (auto simp add: bit_simps)

lemmas less_def = less_eq [symmetric]
lemmas le_def = not_less [symmetric, where ?'a = nat]

end
