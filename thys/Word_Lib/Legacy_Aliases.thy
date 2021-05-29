(*
 * Copyright Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section \<open>Legacy aliases\<close>

theory Legacy_Aliases
  imports "HOL-Library.Word"
begin

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
  "complement (2 ^ n - 1) = NOT (mask n)"
  unfolding mask_eq_decr_exp by simp

lemmas less_def = less_eq [symmetric]
lemmas le_def = not_less [symmetric, where ?'a = nat]

end
