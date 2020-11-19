(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section "Additional Word Operations"

theory Word_Lib
  imports
  "HOL-Library.Signed_Division"
  More_Word
  Signed_Words
  Traditional_Infix_Syntax
  Reversed_Bit_Lists
begin

(* Haskellish names/syntax *)
notation (input)
  test_bit ("testBit")

lemma scast_scast_id [simp]:
  "scast (scast x :: ('a::len) signed word) = (x :: 'a word)"
  "scast (scast y :: ('a::len) word) = (y :: 'a signed word)"
  by (auto simp: is_up scast_up_scast_id)

lemma scast_ucast_id [simp]:
    "scast (ucast (x :: 'a::len word) :: 'a signed word) = x"
  by (metis down_cast_same is_down len_signed order_refl scast_scast_id(1))

lemma ucast_scast_id [simp]:
    "ucast (scast (x :: 'a::len signed word) :: 'a word) = x"
  by (metis scast_scast_id(2) scast_ucast_id)

lemma scast_of_nat [simp]:
    "scast (of_nat x :: 'a::len signed word) = (of_nat x :: 'a word)"
  by transfer (simp add: take_bit_signed_take_bit)

lemma ucast_of_nat:
  "is_down (ucast :: 'a :: len word \<Rightarrow> 'b :: len word)
    \<Longrightarrow> ucast (of_nat n :: 'a word) = (of_nat n :: 'b word)"
  by transfer simp

lemma word_sint_1 [simp]:
  "sint (1::'a::len word) = (if LENGTH('a) = 1 then -1 else 1)"
  by (fact signed_1)

lemma scast_1':
  "(scast (1::'a::len word) :: 'b::len word) =
   (word_of_int (signed_take_bit (LENGTH('a::len) - Suc 0) (1::int)))"
  by transfer simp

lemma scast_1:
  "(scast (1::'a::len word) :: 'b::len word) = (if LENGTH('a) = 1 then -1 else 1)"
  by (fact signed_1)

lemma scast_eq_scast_id [simp]:
  "((scast (a :: 'a::len signed word) :: 'a word) = scast b) = (a = b)"
  by (metis ucast_scast_id)

lemma ucast_eq_ucast_id [simp]:
  "((ucast (a :: 'a::len word) :: 'a signed word) = ucast b) = (a = b)"
  by (metis scast_ucast_id)

lemma scast_ucast_norm [simp]:
  "(ucast (a :: 'a::len word) = (b :: 'a signed word)) = (a = scast b)"
  "((b :: 'a signed word) = ucast (a :: 'a::len word)) = (a = scast b)"
  by (metis scast_ucast_id ucast_scast_id)+

(* FIXME: these should eventually be moved to HOL/Word. *)
lemmas extra_sle_sless_unfolds [simp] =
    word_sle_eq[where a=0 and b=1]
    word_sle_eq[where a=0 and b="numeral n"]
    word_sle_eq[where a=1 and b=0]
    word_sle_eq[where a=1 and b="numeral n"]
    word_sle_eq[where a="numeral n" and b=0]
    word_sle_eq[where a="numeral n" and b=1]
    word_sless_alt[where a=0 and b=1]
    word_sless_alt[where a=0 and b="numeral n"]
    word_sless_alt[where a=1 and b=0]
    word_sless_alt[where a=1 and b="numeral n"]
    word_sless_alt[where a="numeral n" and b=0]
    word_sless_alt[where a="numeral n" and b=1]
  for n

(* shortcut for some specific lengths *)
lemma word_fixed_sint_1[simp]:
  "sint (1::8 word) = 1"
  "sint (1::16 word) = 1"
  "sint (1::32 word) = 1"
  "sint (1::64 word) = 1"
  by (auto simp: sint_word_ariths)

definition
  ptr_add :: "'a :: len word \<Rightarrow> nat \<Rightarrow> 'a word" where
  "ptr_add ptr n \<equiv> ptr + of_nat n"

definition
  alignUp :: "'a::len word \<Rightarrow> nat \<Rightarrow> 'a word" where
 "alignUp x n \<equiv> x + 2 ^ n - 1 AND NOT (2 ^ n - 1)"

(* standard notation for blocks of 2^n-1 words, usually aligned;
   abbreviation so it simplifies directly *)
abbreviation mask_range :: "'a::len word \<Rightarrow> nat \<Rightarrow> 'a word set" where
  "mask_range p n \<equiv> {p .. p + mask n}"

definition
  w2byte :: "'a :: len word \<Rightarrow> 8 word" where
  "w2byte \<equiv> ucast"

lemmas sdiv_int_def = signed_divide_int_def
lemmas smod_int_def = signed_modulo_int_def

instantiation word :: (len) signed_division
begin

lift_definition signed_divide_word :: \<open>'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is \<open>\<lambda>k l. signed_take_bit (LENGTH('a) - Suc 0) k sdiv signed_take_bit (LENGTH('a) - Suc 0) l\<close>
  by (simp flip: signed_take_bit_decr_length_iff)

lift_definition signed_modulo_word :: \<open>'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word\<close>
  is \<open>\<lambda>k l. signed_take_bit (LENGTH('a) - Suc 0) k smod signed_take_bit (LENGTH('a) - Suc 0) l\<close>
  by (simp flip: signed_take_bit_decr_length_iff)

instance ..

end

lemma sdiv_word_def [code]:
  \<open>v sdiv w = word_of_int (sint v sdiv sint w)\<close>
  for v w :: \<open>'a::len word\<close>
  by transfer simp

lemma smod_word_def [code]:
  \<open>v smod w = word_of_int (sint v smod sint w)\<close>
  for v w :: \<open>'a::len word\<close>
  by transfer simp

lemma sdiv_smod_id:
  \<open>(a sdiv b) * b + (a smod b) = a\<close>
  for a b :: \<open>'a::len word\<close>
  by (cases \<open>sint a < 0\<close>; cases \<open>sint b < 0\<close>) (simp_all add: signed_modulo_int_def sdiv_word_def smod_word_def)

(* Count leading zeros  *)
definition
  word_clz :: "'a::len word \<Rightarrow> nat"
where
  "word_clz w \<equiv> length (takeWhile Not (to_bl w))"

(* Count trailing zeros  *)
definition
  word_ctz :: "'a::len word \<Rightarrow> nat"
where
  "word_ctz w \<equiv> length (takeWhile Not (rev (to_bl w)))"

definition
  word_log2 :: "'a::len word \<Rightarrow> nat"
where
  "word_log2 (w::'a::len word) \<equiv> size w - 1 - word_clz w"


(* Bit population count. Equivalent of __builtin_popcount. *)
definition
  pop_count :: "('a::len) word \<Rightarrow> nat"
where
  "pop_count w \<equiv> length (filter id (to_bl w))"


(* Sign extension from bit n *)

definition
  sign_extend :: "nat \<Rightarrow> 'a::len word \<Rightarrow> 'a word"
where
  "sign_extend n w \<equiv> if w !! n then w OR NOT (mask n) else w AND mask n"

lemma sign_extend_eq_signed_take_bit:
  \<open>sign_extend = signed_take_bit\<close>
proof (rule ext)+
  fix n and w :: \<open>'a::len word\<close>
  show \<open>sign_extend n w = signed_take_bit n w\<close>
  proof (rule bit_word_eqI)
    fix q
    assume \<open>q < LENGTH('a)\<close>
    then show \<open>bit (sign_extend n w) q \<longleftrightarrow> bit (signed_take_bit n w) q\<close>
      by (auto simp add: test_bit_eq_bit bit_signed_take_bit_iff
        sign_extend_def bit_and_iff bit_or_iff bit_not_iff bit_mask_iff not_less
        exp_eq_0_imp_not_bit not_le min_def)
  qed
qed

definition
  sign_extended :: "nat \<Rightarrow> 'a::len word \<Rightarrow> bool"
where
  "sign_extended n w \<equiv> \<forall>i. n < i \<longrightarrow> i < size w \<longrightarrow> w !! i = w !! n"


lemma ptr_add_0 [simp]:
  "ptr_add ref 0 = ref "
  unfolding ptr_add_def by simp

lemma pop_count_0[simp]:
  "pop_count 0 = 0"
  by (clarsimp simp:pop_count_def)

lemma pop_count_1[simp]:
  "pop_count 1 = 1"
  by (clarsimp simp:pop_count_def to_bl_1)

lemma pop_count_0_imp_0:
  "(pop_count w = 0) = (w = 0)"
  apply (rule iffI)
   apply (clarsimp simp:pop_count_def)
   apply (subst (asm) filter_empty_conv)
   apply (clarsimp simp:eq_zero_set_bl)
   apply fast
  apply simp
  done

end
