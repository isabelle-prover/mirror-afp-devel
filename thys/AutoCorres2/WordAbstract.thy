(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

chapter "WA phase: Word Abstraction"

theory WordAbstract
imports
  L2Peephole
  NatBitwise
begin

section "Basic Definitions"

definition "WORD_MAX x \<equiv> ((2 ^ (len_of x - 1) - 1) :: int)"
definition "WORD_MIN x \<equiv> (- (2 ^ (len_of x - 1)) :: int)"
definition "UWORD_MAX x \<equiv> ((2 ^ (len_of x)) - 1 :: nat)"

lemma WORD_values [simplified]:
  "WORD_MAX (TYPE( 8 signed)) = (2 ^  7 - 1)"
  "WORD_MAX (TYPE(16 signed)) = (2 ^ 15 - 1)"
  "WORD_MAX (TYPE(32 signed)) = (2 ^ 31 - 1)"
  "WORD_MAX (TYPE(64 signed)) = (2 ^ 63 - 1)"

  "WORD_MIN (TYPE( 8 signed)) = - (2 ^  7)"
  "WORD_MIN (TYPE(16 signed)) = - (2 ^ 15)"
  "WORD_MIN (TYPE(32 signed)) = - (2 ^ 31)"
  "WORD_MIN (TYPE(64 signed)) = - (2 ^ 63)"

  "UWORD_MAX (TYPE( 8)) = (2 ^  8 - 1)"
  "UWORD_MAX (TYPE(16)) = (2 ^ 16 - 1)"
  "UWORD_MAX (TYPE(32)) = (2 ^ 32 - 1)"
  "UWORD_MAX (TYPE(64)) = (2 ^ 64 - 1)"
  by (auto simp: WORD_MAX_def WORD_MIN_def UWORD_MAX_def)

lemmas WORD_values_add1 =
   WORD_values [THEN arg_cong [where f="\<lambda>x. x + 1"],
    simplified semiring_norm, simplified numeral_One]

lemmas WORD_values_minus1 =
   WORD_values [THEN arg_cong [where f="\<lambda>x. x - 1"],
    simplified semiring_norm, simplified numeral_One nat_numeral]

lemmas WORD_values_fold [L1unfold] =
  WORD_values [symmetric]
  WORD_values_add1 [symmetric]
  WORD_values_minus1 [symmetric]

lemma WORD_signed_to_unsigned [simp]:
   "WORD_MAX TYPE('a signed) = WORD_MAX TYPE('a::len)"
   "WORD_MIN TYPE('a signed) = WORD_MIN TYPE('a::len)"
   "UWORD_MAX TYPE('a signed) = UWORD_MAX TYPE('a::len)"
  by (auto simp: WORD_MAX_def WORD_MIN_def UWORD_MAX_def)

(*
 * The following set of theorems allow us to discharge simple
 * equalities involving INT_MIN, INT_MAX and UINT_MAX without
 * the constants being unfolded in the final output.
 *
 * For example:
 *
 *    (4 < INT_MAX)  becomes  True
 *    (x < INT_MAX)  remains  (x < INT_MAX)
 *)

lemma INT_MIN_comparisons [simp]:
  "\<lbrakk> a \<le> - (2 ^ (len_of TYPE('a) - 1)) \<rbrakk> \<Longrightarrow> a \<le> WORD_MIN (TYPE('a::len))"
  "a < - (2 ^ (len_of TYPE('a) - 1)) \<Longrightarrow> a < WORD_MIN (TYPE('a::len))"
  "a \<ge> - (2 ^ (len_of TYPE('a) - 1)) \<Longrightarrow> a \<ge> WORD_MIN (TYPE('a::len))"
  "a > - (2 ^ (len_of TYPE('a) - 1)) \<Longrightarrow> a \<ge> WORD_MIN (TYPE('a::len))"
  by (auto simp: WORD_MIN_def)

lemma INT_MAX_comparisons [simp]:
  "a \<le> (2 ^ (len_of TYPE('a) - 1)) - 1 \<Longrightarrow> a \<le> WORD_MAX (TYPE('a::len))"
  "a < (2 ^ (len_of TYPE('a) - 1)) - 1 \<Longrightarrow> a < WORD_MAX (TYPE('a::len))"
  "a \<ge> (2 ^ (len_of TYPE('a) - 1)) - 1 \<Longrightarrow> a \<ge> WORD_MAX (TYPE('a::len))"
  "a > (2 ^ (len_of TYPE('a) - 1)) - 1 \<Longrightarrow> a \<ge> WORD_MAX (TYPE('a::len))"
  by (auto simp: WORD_MAX_def)

lemma UINT_MAX_comparisons [simp]:
  "x \<le> (2 ^ (len_of TYPE('a))) - 1 \<Longrightarrow> x \<le> UWORD_MAX (TYPE('a::len))"
  "x < (2 ^ (len_of TYPE('a))) - 1 \<Longrightarrow> x \<le> UWORD_MAX (TYPE('a::len))"
  "x \<ge> (2 ^ (len_of TYPE('a))) - 1 \<Longrightarrow> x \<ge> UWORD_MAX (TYPE('a::len))"
  "x > (2 ^ (len_of TYPE('a))) - 1 \<Longrightarrow> x > UWORD_MAX (TYPE('a::len))"
  by (auto simp: UWORD_MAX_def)

lemma is_up_SCAST_same_signed [simp]: "is_up (SCAST (('a::len) \<rightarrow> 'a signed))"
  unfolding is_up
  by simp

lemma sint_ucast_signed [simp, L2opt]:"sint (UCAST ('a::len \<rightarrow> 'a signed) x) = sint x"
  using is_up_SCAST_same_signed scast_ucast_norm(2) sint_up_scast
  by (metis scast_scast_id(1))

section "Abstracting values and expressions"

(*
 * This definition is used when we are trying to introduce a new type
 * in the program text: it simply states that introducing a given
 * abstraction is desired in the current context.
 *)
definition "introduce_typ_abs_fn f \<equiv> True"

declare introduce_typ_abs_fn_def [simp]

lemma introduce_typ_abs_fn:
  "introduce_typ_abs_fn f"
  by simp

(*
 * Show that a binary operator "X" (of type "'a \<Rightarrow> 'a \<Rightarrow> bool") is an
 * abstraction (over function f) of "X'".
 *
 * For example, (a \<le>\<^sub>i\<^sub>n\<^sub>t b) could be an abstraction of (a \<le>\<^sub>w\<^sub>3\<^sub>2 b)
 * over the abstraction function "unat".
 *)
definition
  abstract_bool_binop :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'a)
               \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> bool"
where
  "abstract_bool_binop P f X X' \<equiv> \<forall>a b. P (f a) (f b) \<longrightarrow> (X' a b = X (f a) (f b))"

(* Show that a binary operator "X" (of type "'a \<Rightarrow> 'a \<Rightarrow> 'b") abstracts "X'". *)
definition
  abstract_binop :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'a)
               \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> bool"
where
   "abstract_binop P f X X' \<equiv> \<forall>a b. P (f a) (f b) \<longrightarrow> (f (X' a b) = X (f a) (f b))"

(* The value "a" is the abstract version of "b" under precondition "P". *)
definition "abstract_val P a f b \<equiv> P \<longrightarrow> (a = f b)"

(* The variable "a" is the abstracted version of the variable "b". *)
definition "abs_var a f b \<equiv> abstract_val True a f b"


lemmas basic_abstract_defs = 
  abstract_bool_binop_def 
  abstract_binop_def 
  abstract_val_def 
  abs_var_def

lemma abstract_val_trivial:
  "abstract_val True (f b) f b"
  by (simp add: basic_abstract_defs)

lemma abstract_binop_is_abstract_val:
    "abstract_binop P f X X' = (\<forall>a b. abstract_val (P (f a) (f b)) (X (f a) (f b)) f (X' a b))"
  by (auto simp add: basic_abstract_defs)

lemma abstract_expr_bool_binop:
  "\<lbrakk> abstract_bool_binop E f X X';
     introduce_typ_abs_fn f;
     abstract_val P a f a';
     abstract_val Q b f b' \<rbrakk> \<Longrightarrow>
           abstract_val (P \<and> Q \<and> E a b) (X a b) id (X' a' b')"
  by (clarsimp simp add: basic_abstract_defs)

lemma abstract_expr_binop:
  "\<lbrakk> abstract_binop E f X X';
     abstract_val P a f a';
     abstract_val Q b f b' \<rbrakk> \<Longrightarrow>
           abstract_val (P \<and> Q \<and> E a b) (X a b) f (X' a' b')"
  by (clarsimp simp add: basic_abstract_defs)

lemma unat_abstract_bool_binops:
    "abstract_bool_binop (\<lambda>_ _. True) (unat :: ('a::len) word \<Rightarrow> nat) (<) (<)"
    "abstract_bool_binop (\<lambda>_ _. True) (unat :: ('a::len) word \<Rightarrow> nat) (\<le>) (\<le>)"
    "abstract_bool_binop (\<lambda>_ _. True) (unat :: ('a::len) word \<Rightarrow> nat) (=) (=)"
  by (auto simp:  word_less_nat_alt word_le_nat_alt eq_iff basic_abstract_defs)

lemmas unat_mult_simple = iffD1 [OF unat_mult_lem [unfolded word_bits_len_of]]

lemma le_to_less_plus_one:
    "((a::nat) \<le> b) = (a < b + 1)"
  by arith

lemma unat_abstract_binops:
  "abstract_binop (\<lambda>a b. a + b \<le> UWORD_MAX TYPE('a::len)) (unat :: 'a word \<Rightarrow> nat) (+) (+)"
  "abstract_binop (\<lambda>a b. a * b \<le> UWORD_MAX TYPE('a)) (unat :: 'a word \<Rightarrow> nat) (*) (*)"
  "abstract_binop (\<lambda>a b. a \<ge> b) (unat :: 'a word \<Rightarrow> nat) (-) (-)"
  "abstract_binop (\<lambda>a b. True) (unat :: 'a word \<Rightarrow> nat) (div) (div)"
  "abstract_binop (\<lambda>a b. True) (unat :: 'a word \<Rightarrow> nat) (mod) (mod)"
  by (auto simp: unat_plus_if' unat_div unat_mod UWORD_MAX_def le_to_less_plus_one
              WordAbstract.unat_mult_simple word_bits_def unat_sub word_le_nat_alt
              basic_abstract_defs)

lemma unat_of_int:
  "\<lbrakk>i \<ge> 0; i < 2 ^ LENGTH('a)\<rbrakk> \<Longrightarrow> unat (of_int i :: 'a::len word) = nat i"
  by (metis nat_less_numeral_power_cancel_iff of_nat_nat unat_of_nat_len)

(* fixme generalises Word_Lemmas_32.unat_of_int_32 *)
lemma unat_of_int_signed:
  "\<lbrakk>i \<ge> 0; i < 2 ^ LENGTH('a)\<rbrakk> \<Longrightarrow> unat (of_int i :: 'a::len signed word) = nat i"
  by (simp add: unat_of_int)

lemma nat_sint:
  "0 <=s (x :: 'a::len signed word) \<Longrightarrow> nat (sint x) = unat x"
  apply (subst unat_of_int_signed[where 'a='a, symmetric])
    apply (simp add: word_sle_def)
   apply (rule less_trans[OF sint_lt])
   apply simp
  apply simp
  done

lemma int_unat_nonneg:
  "0 <=s (x :: 'a::len signed word) \<Longrightarrow> int (unat x) = sint x"
  by (simp add: int_unat word_sle_msb_le sint_eq_uint)

lemma uint_sint_nonneg:
  "0 <=s (x :: 'a::len signed word) \<Longrightarrow> uint x = sint x"
  by (simp add: int_unat word_sle_msb_le sint_eq_uint)

lemma unat_bitwise_abstract_binops:
  "abstract_binop (\<lambda>a b. True) (unat :: 'a::len word \<Rightarrow> nat) Bit_Operations.and Bit_Operations.and"
  "abstract_binop (\<lambda>a b. True) (unat :: 'a::len word \<Rightarrow> nat) Bit_Operations.or Bit_Operations.or"
  "abstract_binop (\<lambda>a b. True) (unat :: 'a::len word \<Rightarrow> nat) Bit_Operations.xor Bit_Operations.xor"
  apply (simp add: unsigned_and_eq uint_nat unat_of_int basic_abstract_defs)
  apply (simp add: unsigned_or_eq  uint_nat unat_of_int basic_abstract_defs)
  apply (simp add: unsigned_xor_eq uint_nat unat_of_int basic_abstract_defs)
  done

lemma abstract_val_unsigned_bitNOT:
  "abstract_val P x unat (x' :: 'a::len word) \<Longrightarrow>
   abstract_val P (UWORD_MAX TYPE('a) - x) unat (NOT x')"
  apply (clarsimp simp: UWORD_MAX_def NOT_eq basic_abstract_defs)
  by (metis nat_le_Suc_less diff_Suc_eq_diff_pred mask_eq_sum_exp mask_eq_sum_exp_nat 
    minus_diff_commute unat_lt2p unat_minus_one_word unat_sub_if_size unsigned_0)


lemma snat_abstract_bool_binops:
    "abstract_bool_binop (\<lambda>_ _. True) (sint :: ('a::len) signed word \<Rightarrow> int) (<) (word_sless)"
    "abstract_bool_binop (\<lambda>_ _. True) (sint :: 'a signed word \<Rightarrow> int) (\<le>) (word_sle)"
    "abstract_bool_binop (\<lambda>_ _. True) (sint :: 'a signed word \<Rightarrow> int) (=) (=)"
  by (auto simp: word_sless_def word_sle_def less_le basic_abstract_defs)

lemma snat_abstract_binops:
  "abstract_binop (\<lambda>a b. WORD_MIN TYPE('a::len) \<le> a + b \<and> a + b \<le> WORD_MAX TYPE('a)) (sint :: 'a signed word \<Rightarrow> int) (+) (+)"
  "abstract_binop (\<lambda>a b. WORD_MIN TYPE('a) \<le> a * b \<and> a * b \<le> WORD_MAX TYPE('a)) (sint :: 'a signed word \<Rightarrow> int) (*) (*)"
  "abstract_binop (\<lambda>a b. WORD_MIN TYPE('a) \<le> a - b \<and> a - b \<le> WORD_MAX TYPE('a)) (sint :: 'a signed word \<Rightarrow> int) (-) (-)"
  "abstract_binop (\<lambda>a b. WORD_MIN TYPE('a) \<le> a sdiv b \<and> a sdiv b \<le> WORD_MAX TYPE('a)) (sint :: 'a signed word \<Rightarrow> int) (sdiv) (sdiv)"
  "abstract_binop (\<lambda>a b. WORD_MIN TYPE('a) \<le> a smod b \<and> a smod b \<le> WORD_MAX TYPE('a)) (sint :: 'a signed word \<Rightarrow> int) (smod) (smod)"
  by (auto simp: signed_arith_sint word_size WORD_MIN_def WORD_MAX_def basic_abstract_defs)

lemma sint_bitwise_abstract_binops:
  "abstract_binop (\<lambda>a b. True) (sint :: 'a::len signed word \<Rightarrow> int) Bit_Operations.and Bit_Operations.and"
  "abstract_binop (\<lambda>a b. True) (sint :: 'a::len signed word \<Rightarrow> int) Bit_Operations.or Bit_Operations.or"
  "abstract_binop (\<lambda>a b. True) (sint :: 'a::len signed word \<Rightarrow> int) Bit_Operations.xor Bit_Operations.xor"
  apply (fastforce intro: int_eq_test_bitI
                   simp: nth_sint bin_nth_ops basic_abstract_defs)+
  done

lemma abstract_val_signed_bitNOT:
  "abstract_val P x sint (x' :: 'a::len signed word) \<Longrightarrow>
   abstract_val P (NOT x) sint (NOT x')"
  by (auto intro: int_eq_test_bitI 
      simp add: nth_sint bin_nth_ops word_nth_neq basic_abstract_defs min_less_iff_disj)

lemma abstract_val_signed_unary_minus:
  "\<lbrakk> abstract_val P r sint r' \<rbrakk> \<Longrightarrow>
       abstract_val (P \<and> (- r) \<le> WORD_MAX TYPE('a)) (- r) sint ( - (r' :: ('a :: len) signed word))"
  apply (clarsimp simp add: basic_abstract_defs)
  using sint_range_size [where w=r']
  apply -
  apply (subst signed_arith_sint)
   apply (clarsimp simp: word_size WORD_MAX_def)
  apply simp
  done

lemma bang_big_nonneg:
  "\<lbrakk> 0 <=s (x::'a::len signed word); n \<ge> size x - 1 \<rbrakk> \<Longrightarrow> (x !! n) = False"
  apply (cases "n = size x - 1")
   apply (simp add: word_size msb_nth[where 'a="'a signed", symmetric, simplified] word_sle_msb_le)
  apply (simp add: test_bit_bl)
  apply arith
  done

(* FIXME: move to Word_Lib *)

lemma int_shiftr_nth[simp]:
  "(i >> n) !! m = i !! (n + m)" for i :: int
  by (simp add: shiftr_def bin_nth_shiftr)

(* FIXME: move to Word_Lib *)
lemma int_shiftl_nth[simp]:
  "(i << n) !! m = (n \<le> m \<and> i !! (m - n))" for i :: int
  by (simp add: shiftl_def bin_nth_shiftl)


lemma sint_shiftr_nonneg:
  "\<lbrakk> 0 <=s (x :: 'a::len signed word); 0 \<le> n; n < LENGTH('a) \<rbrakk> \<Longrightarrow> sint (x >> n) = sint x >> n"
  apply (rule int_eq_test_bitI)
  apply (clarsimp simp: bang_big_nonneg[simplified word_size] nth_sint nth_shiftr field_simps 
      simp del: bit_signed_iff)
  done

lemma abstract_val_unsigned_unary_minus:
  "\<lbrakk> abstract_val P r unat r' \<rbrakk> \<Longrightarrow>
       abstract_val P (if r = 0 then 0 else UWORD_MAX TYPE('a::len) + 1 - r) unat ( - (r' :: 'a word))"
  by (clarsimp simp: unat_minus' word_size unat_eq_zero UWORD_MAX_def basic_abstract_defs)

(* Rules for shifts *)
lemma abstract_val_signed_shiftr_signed:
  "\<lbrakk> abstract_val Px x sint (x' :: ('a :: len) signed word);
     abstract_val Pn n sint (n' :: ('b :: len) signed word) \<rbrakk> \<Longrightarrow>
   abstract_val (Px \<and> Pn \<and> 0 \<le> x \<and> 0 \<le> n \<and> n < int LENGTH('a))
                (x >> (nat n)) sint (x' >> (unat n'))"
  apply (clarsimp simp only: abstract_val_def)
  apply (subst nat_sint, simp add: word_sle_def)
  apply (subst sint_shiftr_nonneg)
     apply (simp add: word_sle_def)
    apply simp
   apply (subst SMT.nat_int_comparison(2))
   apply (subst int_unat_nonneg)
    apply (simp add: word_sle_def)
   apply assumption
  apply (rule refl)
  done

lemma abstract_val_signed_shiftr_unsigned:
  "\<lbrakk> abstract_val Px x sint (x' :: ('a :: len) signed word);
     abstract_val Pn n unat (n' :: ('b :: len) word) \<rbrakk> \<Longrightarrow>
   abstract_val (Px \<and> Pn \<and> 0 \<le> x \<and> n < LENGTH('a))
                (x >> n) sint (x' >> unat n')"
  apply (clarsimp simp: shiftr_int_def basic_abstract_defs)
  apply (subst sint_shiftr_nonneg)
     apply (simp add: word_sle_def)
    apply simp
   apply assumption
  apply (clarsimp simp: shiftr_int_def)
  done

lemma foo:  "\<not> n - i < LENGTH('a::len) - Suc 0 \<Longrightarrow>
    n < LENGTH('a) - Suc 0 = False"
  apply simp
  done

lemma sint_shiftl_nonneg:
  "\<lbrakk> 0 <=s (x :: 'a::len signed word); n < LENGTH('a); sint x << n < 2^(LENGTH('a) - 1) \<rbrakk> \<Longrightarrow>
   sint (x << n) = sint x << n"
  apply (rule int_eq_test_bitI)
  subgoal for na
    apply (simp add: nth_sint nth_shiftl word_sle_def int_shiftl_less_cancel int_2p_eq_shiftl
        bang_big_nonneg[simplified word_size]
        del:  bit_signed_iff shiftl_1)
      (* fixme: cleanup *)
    apply (intro impI iffI conjI; (solves simp)?)
      apply (drule(1) int_shiftl_lt_2p_bits[rotated])
      apply (clarsimp simp: nth_sint)
      apply (drule_tac x="LENGTH('a) - 1 - n" in spec)
      apply (subgoal_tac "LENGTH('a) - 1 - n < LENGTH('a) - 1")
       apply simp
      apply arith
     apply (drule(1) int_shiftl_lt_2p_bits[rotated])
     apply (clarsimp simp: nth_sint)
     apply (drule_tac x="na - n" in spec)
     apply simp
    apply (cases "n = 0")
     apply (simp add: word_sle_msb_le[where x=0, simplified word_sle_def, simplified] msb_nth)
    apply (drule(1) int_shiftl_lt_2p_bits[rotated])
    apply (clarsimp simp: nth_sint)
    apply (drule_tac x="LENGTH('a) - 1 - n" in spec)
    apply (subgoal_tac "LENGTH('a) - 1 - n < LENGTH('a) - 1")
     apply simp
    apply simp
    done
  done

lemma abstract_val_signed_shiftl_signed:
  "\<lbrakk> abstract_val Px x sint (x' :: ('a :: len) signed word);
     abstract_val Pn n sint (n' :: ('b :: len) signed word) \<rbrakk> \<Longrightarrow>
   abstract_val (Px \<and> Pn \<and> 0 \<le> x \<and> 0 \<le> n \<and> n < int LENGTH('a) \<and> x << nat n < 2^(LENGTH('a) - 1))
                (x << nat n) sint (x' << unat n')"
  apply (clarsimp simp add: basic_abstract_defs)
  by (metis One_nat_def len_gt_0 nat_int nat_sint signed_0 sint_shiftl_nonneg word_sle_eq 
    zless_nat_conj)

lemma abstract_val_signed_shiftl_unsigned:
  "\<lbrakk> abstract_val Px x sint (x' :: ('a :: len) signed word);
     abstract_val Pn n unat (n' :: ('b :: len) word) \<rbrakk> \<Longrightarrow>
   abstract_val (Px \<and> Pn \<and> 0 \<le> x \<and> n < LENGTH('a) \<and> x << n < 2^(LENGTH('a) - 1))
                (x << n) sint (x' << unat n')"
  by (clarsimp simp: sint_shiftl_nonneg word_sle_def basic_abstract_defs
                     nat_less_eq_zless[where z="int LENGTH('a)", simplified])

lemma abstract_val_unsigned_shiftr_unsigned:
  "\<lbrakk> abstract_val Px x unat (x' :: ('a :: len) word);
     abstract_val Pn n unat (n' :: ('a :: len) word) \<rbrakk> \<Longrightarrow>
   abstract_val (Px \<and> Pn) (x >> n) unat (x' >> unat n')"
  apply (clarsimp simp add: basic_abstract_defs)
  apply (simp add: shiftr_div_2n'  shiftr_int_def)
  using shiftr_eq_div by blast

lemma abstract_val_unsigned_shiftr_signed:
  "\<lbrakk> abstract_val Px x unat (x' :: ('a :: len) word);
     abstract_val Pn n sint (n' :: ('b :: len) signed word) \<rbrakk> \<Longrightarrow>
   abstract_val (Px \<and> Pn \<and> 0 \<le> n) (x >> nat n) unat (x' >> unat n')"
  apply (clarsimp simp: shiftr_div_2n' shiftr_int_def basic_abstract_defs)
  by (simp add: nat_sint shiftr_nat_def word_sle_eq)

lemma abstract_val_unsigned_shiftl_unsigned:
  "\<lbrakk> abstract_val Px x unat (x' :: ('a :: len) word);
     abstract_val Pn n unat (n' :: ('b :: len) word) \<rbrakk> \<Longrightarrow>
   abstract_val (Px \<and> Pn \<and> n < LENGTH('a) \<and> x << n < 2^LENGTH('a))
                (x << n) unat (x' << unat n')"
  by (clarsimp simp: shiftl_t2n Word_Lemmas_Internal.shiftl_nat_def unat_mult_simple field_simps basic_abstract_defs)

lemma abstract_val_unsigned_shiftl_signed:
  "\<lbrakk> abstract_val Px x unat (x' :: ('a :: len) word);
     abstract_val Pn n sint (n' :: ('b :: len) signed word) \<rbrakk> \<Longrightarrow>
   abstract_val (Px \<and> Pn \<and> 0 \<le> n \<and> n < int (LENGTH('a)) \<and> x << nat n < 2^LENGTH('a))
                (x << nat n) unat (x' << unat n')"
  apply (clarsimp simp: shiftl_t2n Word_Lemmas_Internal.shiftl_nat_def unat_mult_simple field_simps basic_abstract_defs)
  apply (simp add: sint_eq_uint word_msb_sint)
  by (metis Word.of_nat_unat len_gt_0 nat_int unat_of_nat_len unat_power_lower word_arith_nat_mult 
    zless_nat_conj)

(* TODO: this would be useful for simplifying signed left shift c_guards,
   which are already implied by the generated word abs guard (premise #2).

   However, the c_guard is translated before the new word abs guards,
   thus L2Opt (which only propagates guards forwards) is unable to
   make use of this rule at present. *)
lemma signed_shiftl_c_guard_simp (* [L2flow] *):
  "\<lbrakk> int bound < 2^LENGTH('a); a * 2^b < int bound; 0 \<le> a \<rbrakk> \<Longrightarrow>
   unat (of_int a :: 'a::len word) * 2 ^ b < bound"
  apply (subst unat_of_int)
    apply assumption
   apply (drule(1) less_trans)
   apply (subgoal_tac "a * 2^b < 2^LENGTH('a) * 2^b")
    apply simp
   apply (erule less_le_trans)
   apply simp
  apply (subgoal_tac "nat (a * 2^b) < nat (int bound)")
   apply (simp add: nat_power_eq nat_mult_distrib)
  apply (subst nat_mono_iff)
   apply (rule le_less_trans, assumption)
   apply (erule le_less_trans[rotated])
   apply (simp add: mult_left_mono[where a="1::int", simplified])
  apply simp
  done

lemmas abstract_val_signed_ops [simplified simp_thms] =
  abstract_expr_bool_binop [OF snat_abstract_bool_binops(1)]
  abstract_expr_bool_binop [OF snat_abstract_bool_binops(2)]
  abstract_expr_bool_binop [OF snat_abstract_bool_binops(3)]
  abstract_expr_binop [OF snat_abstract_binops(1)]
  abstract_expr_binop [OF snat_abstract_binops(2)]
  abstract_expr_binop [OF snat_abstract_binops(3)]
  abstract_expr_binop [OF snat_abstract_binops(4)]
  abstract_expr_binop [OF snat_abstract_binops(5)]
  abstract_expr_binop [OF sint_bitwise_abstract_binops(1)]
  abstract_expr_binop [OF sint_bitwise_abstract_binops(2)]
  abstract_expr_binop [OF sint_bitwise_abstract_binops(3)]
  abstract_val_signed_bitNOT
  abstract_val_signed_unary_minus
  abstract_val_signed_shiftr_signed
  abstract_val_signed_shiftr_unsigned
  abstract_val_signed_shiftl_signed
  abstract_val_signed_shiftl_unsigned

lemmas abstract_val_unsigned_ops [simplified simp_thms] =
  abstract_expr_bool_binop [OF unat_abstract_bool_binops(1)]
  abstract_expr_bool_binop [OF unat_abstract_bool_binops(2)]
  abstract_expr_bool_binop [OF unat_abstract_bool_binops(3)]
  abstract_expr_binop [OF unat_abstract_binops(1)]
  abstract_expr_binop [OF unat_abstract_binops(2)]
  abstract_expr_binop [OF unat_abstract_binops(3)]
  abstract_expr_binop [OF unat_abstract_binops(4)]
  abstract_expr_binop [OF unat_abstract_binops(5)]
  abstract_expr_binop [OF unat_bitwise_abstract_binops(1)]
  abstract_expr_binop [OF unat_bitwise_abstract_binops(2)]
  abstract_expr_binop [OF unat_bitwise_abstract_binops(3)]
  abstract_val_unsigned_bitNOT
  abstract_val_unsigned_unary_minus
  abstract_val_unsigned_shiftr_signed
  abstract_val_unsigned_shiftr_unsigned
  abstract_val_unsigned_shiftl_signed
  abstract_val_unsigned_shiftl_unsigned

lemma mod_less:
  "(a :: nat) < c \<Longrightarrow> a mod b < c"
  by (metis less_trans mod_less_eq_dividend order_leE)

lemma abstract_val_ucast:
    "\<lbrakk> introduce_typ_abs_fn (unat :: ('a::len) word \<Rightarrow> nat);
       abstract_val P v unat v' \<rbrakk>
       \<Longrightarrow>  abstract_val (P \<and> v \<le> nat (WORD_MAX TYPE('a)))
                  (int v) sint (ucast (v' :: 'a word) :: 'a signed word)"
  apply (clarsimp simp: uint_nat [symmetric] basic_abstract_defs)
  apply (subst sint_eq_uint)
   apply (rule not_msb_from_less)
   apply (clarsimp simp: word_less_nat_alt unat_ucast WORD_MAX_def le_to_less_plus_one)
   apply (subst (asm) nat_diff_distrib)
     apply simp
    apply clarsimp
   apply clarsimp
   apply (metis of_nat_numeral nat_numeral nat_power_eq of_nat_0_le_iff)
  apply (clarsimp simp: uint_up_ucast is_up)
  done

(* Base rule for heap-lifted signed words. See the function mk_sword_heap_get_rule. *)
lemma abstract_val_heap_sword_template:
  "\<lbrakk> introduce_typ_abs_fn (sint :: ('a::len) signed word \<Rightarrow> int);
     abstract_val P p' id p \<rbrakk>
   \<Longrightarrow> abstract_val P (sint (ucast (heap_get s p' :: 'a word) :: 'a signed word))
                      sint (ucast (heap_get s p) :: 'a signed word)"
  by (simp add: basic_abstract_defs)

lemma abstract_val_scast:
    "\<lbrakk> introduce_typ_abs_fn (sint :: ('a::len) signed word \<Rightarrow> int);
       abstract_val P C' sint C \<rbrakk>
            \<Longrightarrow>  abstract_val (P \<and> 0 \<le> C') (nat C') unat (scast (C :: ('a::len) signed word) :: ('a::len) word)"
  apply (clarsimp simp: down_cast_same [symmetric] is_down unat_ucast basic_abstract_defs)
  apply (subst sint_eq_uint)
   apply (clarsimp simp: word_msb_sint)
  apply (clarsimp simp: unat_def [symmetric])
  apply (subst word_unat.norm_Rep [symmetric])
  apply clarsimp
  done

lemma abstract_val_scast_upcast:
    "\<lbrakk> len_of TYPE('a::len) \<le> len_of TYPE('b::len);
       abstract_val P C' sint C \<rbrakk>
            \<Longrightarrow>  abstract_val P (C') sint (scast (C :: 'a signed word) :: 'b signed word)"
  by (clarsimp simp: down_cast_same [symmetric] sint_up_scast is_up basic_abstract_defs)

lemma abstract_val_scast_downcast:
    "\<lbrakk> len_of TYPE('b) < len_of TYPE('a::len);
       abstract_val P C' sint C \<rbrakk>
            \<Longrightarrow>  abstract_val P (sbintrunc ((len_of TYPE('b::len) - 1)) C') sint (scast (C :: 'a signed word) :: 'b signed word)"
  by (metis Word.of_int_sint abstract_val_def len_signed word_sbin.inverse_norm)

lemma abstract_val_ucast_upcast:
    "\<lbrakk> len_of TYPE('a::len) \<le> len_of TYPE('b::len);
       abstract_val P C' unat C \<rbrakk>
            \<Longrightarrow>  abstract_val P (C') unat (ucast (C :: 'a word) :: 'b word)"
  by (clarsimp simp: is_up unat_ucast_upcast basic_abstract_defs)

lemma abstract_val_ucast_downcast:
    "\<lbrakk> len_of TYPE('b::len) < len_of TYPE('a::len);
       abstract_val P C' unat C \<rbrakk>
            \<Longrightarrow>  abstract_val P (C' mod (UWORD_MAX TYPE('b) + 1)) unat (ucast (C :: 'a word) :: 'b word)"
  apply (clarsimp simp: scast_def sint_uint UWORD_MAX_def basic_abstract_defs)
  unfolding ucast_def unat_def
  apply (subst int_word_uint)
  apply (metis (mono_tags) uint_mod uint_power_lower unat_def unat_mod unat_power_lower)
  done

(*
 * The pair A/C are a valid abstraction/concrete-isation function pair,
 * under the precondition's P and Q.
 *)
definition
 "valid_typ_abs_fn (P :: 'a \<Rightarrow> bool) (Q :: 'a \<Rightarrow> bool) (A :: 'c \<Rightarrow> 'a) (C :: 'a \<Rightarrow> 'c) \<equiv>
     (\<forall>v. P v \<longrightarrow> A (C v) = v) \<and> (\<forall>v. Q (A v) \<longrightarrow> C (A v) = v)"

declare valid_typ_abs_fn_def [simp]

lemma valid_typ_abs_fn_id:
  "valid_typ_abs_fn (\<lambda>_. True) (\<lambda>_. True) id id"
  by clarsimp

lemma valid_typ_abs_fn_unit:
  "valid_typ_abs_fn (\<lambda>_. True) (\<lambda>_. True) id (id :: unit \<Rightarrow> unit)"
  by clarsimp

lemma valid_typ_abs_fn_unat:
  "valid_typ_abs_fn (\<lambda>v. v \<le> UWORD_MAX TYPE('a::len)) (\<lambda>_. True) (unat :: 'a word \<Rightarrow> nat) (of_nat :: nat \<Rightarrow> 'a word)" 
  supply unsigned_of_nat [simp del] 
  by (clarsimp simp: unat_of_nat_eq UWORD_MAX_def le_to_less_plus_one)

lemma valid_typ_abs_fn_sint:
  "valid_typ_abs_fn (\<lambda>v. WORD_MIN TYPE('a::len) \<le> v \<and> v \<le> WORD_MAX TYPE('a)) (\<lambda>_. True) (sint :: 'a signed word \<Rightarrow> int) (of_int :: int \<Rightarrow> 'a signed word)"
  by (clarsimp simp: sint_of_int_eq WORD_MIN_def WORD_MAX_def)

lemma valid_typ_abs_fn_tuple:
  "\<lbrakk> valid_typ_abs_fn P_a Q_a abs_a conc_a; valid_typ_abs_fn P_b Q_b abs_b conc_b \<rbrakk> \<Longrightarrow>
          valid_typ_abs_fn (\<lambda>(a, b). P_a a \<and> P_b b) (\<lambda>(a, b). Q_a a \<and> Q_b b) (map_prod abs_a abs_b) (map_prod conc_a conc_b)"
  by clarsimp

lemma valid_typ_abs_fn_tuple_split:
  "\<lbrakk> valid_typ_abs_fn P_a Q_a abs_a conc_a; valid_typ_abs_fn P_b Q_b abs_b conc_b \<rbrakk> \<Longrightarrow>
          valid_typ_abs_fn (\<lambda>(a, b). P_a a \<and> P_b b) (\<lambda>(a, b). Q_a a \<and> Q_b b) (\<lambda>(a, b). (abs_a a, abs_b b)) (map_prod conc_a conc_b)"
  by clarsimp

lemma introduce_typ_abs_fn_tuple:
  "\<lbrakk> introduce_typ_abs_fn abs_a; introduce_typ_abs_fn abs_b \<rbrakk> \<Longrightarrow>
         introduce_typ_abs_fn (map_prod abs_a abs_b)"
  by clarsimp

lemma valid_typ_abs_fn_sum:
  "\<lbrakk> valid_typ_abs_fn P_a Q_a abs_a conc_a; valid_typ_abs_fn P_b Q_b abs_b conc_b \<rbrakk> \<Longrightarrow>
          valid_typ_abs_fn (case_sum P_a P_b) (case_sum Q_a Q_b) (map_sum abs_a abs_b) (map_sum conc_a conc_b)"
  by (auto simp add: map_sum_def split: sum.splits)

lemma introduce_typ_abs_fn_sum:
  "\<lbrakk> introduce_typ_abs_fn abs_a; introduce_typ_abs_fn abs_b \<rbrakk> \<Longrightarrow>
         introduce_typ_abs_fn (map_sum abs_a abs_b)"
  by clarsimp


section "Refinement Lemmas"

named_theorems word_abs

definition
  "corresTA P rx ex A C \<equiv> corresXF (\<lambda>s. s) (\<lambda>r s. rx r) (\<lambda>r s. ex r) P A C"

definition "rel_word_abs ex rx \<equiv> rel_xval (\<lambda>c a. a = ex c) (\<lambda>c a. a = rx c)" 

lemma rel_word_abs_simps[simp]:
  "rel_word_abs ex rx (Result rc) (Exn la) = False"
  "rel_word_abs ex rx (Exn lc) (Result ra) = False"
  "rel_word_abs ex rx (Result rc) (Result ra) = (ra = rx rc)"
  "rel_word_abs ex rx (Exn lc) (Exn la) = (la = ex lc)"
  by (auto simp add: rel_word_abs_def)

lemma corresTA_refines:
  "corresTA P rx ex f\<^sub>a f\<^sub>c \<Longrightarrow> P s \<Longrightarrow> refines f\<^sub>c f\<^sub>a s s (rel_prod (rel_word_abs ex rx) (=))"
  unfolding corresTA_def
  apply (clarsimp simp add: corresXF_refines_conv rel_word_abs_def rel_xval.simps)
  apply (clarsimp simp add: refines_def_old rel_xval.simps reaches_succeeds)
  by (smt (verit) le_boolE le_boolI' linorder_not_le xval_split)

lemma refines_corresTA:
  assumes sim: "\<And>s. P s \<Longrightarrow> refines f\<^sub>c f\<^sub>a s s (rel_prod (rel_word_abs ex rx) (=))"
  shows "corresTA P rx ex f\<^sub>a f\<^sub>c"
  unfolding corresTA_def
  apply (clarsimp simp add: corresXF_refines_conv rel_word_abs_def rel_xval.simps)
  using sim
  apply (fastforce simp add: refines_def_old rel_xval.simps reaches_succeeds rel_word_abs_def split: xval_splits)
  done

lemma corresTA_refines_conv: 
  "corresTA P rx ex f\<^sub>a f\<^sub>c \<longleftrightarrow> (\<forall>s. P s \<longrightarrow> refines f\<^sub>c f\<^sub>a s s (rel_prod (rel_word_abs ex rx) (=)))"
  using corresTA_refines refines_corresTA by metis

lemma admissible_nondet_ord_corresTA [corres_admissible]:
  "ccpo.admissible Inf (\<ge>) (\<lambda>A. corresTA P rx ex  A C)"
  unfolding corresTA_def
  apply (rule admissible_nondet_ord_corresXF)
  done

lemma corresTA_top [corres_top]: "corresTA P rx st \<top> C"
  by (auto simp add: corresTA_def corresXF_def)

lemma corresTA_assume_and_weaken_pre:
  assumes A_C: "\<And>s. P s \<Longrightarrow> corresTA Q rt ex A C"
  assumes P_Q: "\<And>s. P s \<Longrightarrow> Q s" 
  shows "corresTA P rt ex A C"
  unfolding corresTA_def
  apply (rule corresXF_assume_pre)
  apply (rule corresXF_guard_imp)
   apply (rule A_C [unfolded corresTA_def])
   apply assumption
  apply (rule P_Q)
  apply assumption
  done

lemma corresTA_L2_gets:
  "\<lbrakk> \<And>s. abstract_val (Q s) (C s) rx (C' s) \<rbrakk> \<Longrightarrow>
     corresTA Q rx ex (L2_gets (\<lambda>s. C s) n) (L2_gets (\<lambda>s. C' s) n)"
  unfolding L2_defs
  apply (clarsimp simp add: corresTA_refines_conv)
  apply (rule refines_gets)
  apply (simp add: abstract_val_def)
  done

lemma corresTA_L2_modify:
    "\<lbrakk> \<And>s. abstract_val (P s) (m s) id (m' s) \<rbrakk> \<Longrightarrow>
            corresTA P rx ex (L2_modify (\<lambda>s. m s)) (L2_modify (\<lambda>s. m' s))"
  unfolding L2_defs
  apply (clarsimp simp add: corresTA_refines_conv)
  apply (rule refines_modify)
  apply (simp add: abstract_val_def)
  done

(* FIXME: move to spec monad *)

lemma refines_throw: "R (Exn x, s) (Exn y, t) \<Longrightarrow> refines (throw x) (throw y) s t R"
  by (auto simp add: refines_def_old Exn_def)

lemma corresTA_L2_throw:
  "\<lbrakk> abstract_val Q C ex C' \<rbrakk> \<Longrightarrow>
     corresTA (\<lambda>_. Q) rx ex (L2_throw C n) (L2_throw C' n)"
  unfolding L2_defs
  apply (clarsimp simp add: corresTA_refines_conv)
  apply (simp add: abstract_val_def)
  done

lemma corresTA_L2_skip:
  "corresTA (\<lambda>_. True) rx ex L2_skip L2_skip"
  unfolding L2_defs
  by (auto simp add: corresTA_refines_conv refines_gets)


lemma corresTA_L2_fail:
  "corresTA (\<lambda>_. True) rx ex L2_fail L2_fail"
  unfolding L2_defs
  by (auto simp add: corresTA_refines_conv)

lemma corresTA_L2_seq':
  fixes L' :: "('e, 'c1, 's) exn_monad"
  fixes R' :: "'c1 \<Rightarrow> ('e, 'c2, 's) exn_monad"
  fixes L :: "('ea, 'a1, 's) exn_monad"
  fixes R :: "'a1 \<Rightarrow> ('ea, 'a2, 's) exn_monad"
  shows
  "\<lbrakk> corresTA P rx1 ex L L';
     \<And>r. corresTA (Q (rx1 r)) rx2 ex (R (rx1 r)) (R' r) \<rbrakk> \<Longrightarrow>
    corresTA P rx2 ex
       (L2_seq L (\<lambda>r. L2_seq (L2_guard (\<lambda>s. Q r s)) (\<lambda>_. R r)))
       (L2_seq L' (\<lambda>r. R' r))"
  apply atomize
  apply (clarsimp simp: L2_seq_def L2_guard_def corresTA_def)
  apply (erule corresXF_join [where P'="\<lambda>x y s. rx1 y = x"])
  subgoal
    by (auto simp add: corresXF_def reaches_bind reaches_guard  succeeds_bind split: xval_splits)
  subgoal
    by (auto simp add: runs_to_partial_def_old split: xval_splits)
  subgoal by simp
  done

lemma corresTA_L2_seq:
  "\<lbrakk> introduce_typ_abs_fn rx1;
    PROP THIN (Trueprop (corresTA P (rx1 :: 'a \<Rightarrow> 'b) ex L L'));
    PROP THIN  (\<And>r r'. abs_var r rx1 r' \<Longrightarrow> corresTA (Q r) rx2 ex (R r) (R' r')) \<rbrakk> \<Longrightarrow>
       corresTA P rx2 ex (L2_seq L (\<lambda>r. L2_seq (L2_guard (Q r)) (\<lambda>_. R r))) (L2_seq L' R')"
  unfolding THIN_def
  by (rule corresTA_L2_seq', (simp add: basic_abstract_defs)+)

lemma corresTA_L2_seq_unused_result:
  "\<lbrakk> introduce_typ_abs_fn rx1;
    PROP THIN (Trueprop (corresTA P (rx1 :: 'a \<Rightarrow> 'b) ex L L'));
    PROP THIN (Trueprop (corresTA Q rx2 ex R R'))\<rbrakk> \<Longrightarrow>
       corresTA P rx2 ex (L2_seq L (\<lambda>r. L2_seq (L2_guard Q) (\<lambda>_. R))) (L2_seq L' (\<lambda>_. R'))"
  unfolding THIN_def
  by (rule corresTA_L2_seq', simp+)

lemma corresTA_L2_seq_unit:
  fixes L' :: "('e, unit, 's) exn_monad"
  fixes R' :: "unit \<Rightarrow> ('e, 'r, 's) exn_monad"
  fixes L :: "('ea, unit, 's) exn_monad"
  fixes R :: "('ea, 'ra, 's) exn_monad"
  shows
  "\<lbrakk>PROP THIN (Trueprop (corresTA P id ex L L'));
    PROP THIN (Trueprop (corresTA Q rx ex R (R' ()))) \<rbrakk> \<Longrightarrow>
    corresTA P rx ex
       (L2_seq L (\<lambda>r. L2_seq (L2_guard Q) (\<lambda>_. R)))
       (L2_seq L' R')"
  unfolding THIN_def
  by (rule corresTA_L2_seq', simp+)

lemma corresTA_L2_catch':
  fixes L' :: "('e1, 'c, 's) exn_monad"
  fixes R' :: "'e1 \<Rightarrow> ('e2, 'c, 's) exn_monad"
  fixes L :: "('e1a, 'ca, 's) exn_monad"
  fixes R :: "'e1a \<Rightarrow> ('e2a, 'ca, 's) exn_monad"
  shows
  "\<lbrakk>corresTA P rx ex1 L L';
    \<And>r. corresTA (Q (ex1 r)) rx ex2 (R (ex1 r)) (R' r) \<rbrakk> \<Longrightarrow>
    corresTA P rx ex2 (L2_catch L (\<lambda>r. L2_seq (L2_guard (\<lambda>s. Q r s)) (\<lambda>_. R r))) (L2_catch L' (\<lambda>r. R' r))"
  apply atomize
  apply (clarsimp simp: L2_seq_def L2_catch_def L2_guard_def corresTA_def)
  apply (erule corresXF_except [where P'="\<lambda>x y s. ex1 y = x"])
  subgoal
    by (auto simp add: corresXF_def reaches_bind reaches_guard  succeeds_bind split: xval_splits)
  subgoal
    by (auto simp add: runs_to_partial_def_old split: xval_splits)
  subgoal by simp
  done

lemma corresTA_L2_catch:
  "\<lbrakk> introduce_typ_abs_fn ex1;
    PROP THIN (Trueprop (corresTA P rx ex1 L L'));
    PROP THIN (\<And>r r'. abs_var r ex1 r' \<Longrightarrow> corresTA (Q r) rx ex2 (R r) (R' r')) \<rbrakk> \<Longrightarrow>
       corresTA P rx ex2 (L2_catch L (\<lambda>r. L2_seq (L2_guard (\<lambda>s. Q r s)) (\<lambda>_. R r))) (L2_catch L' (\<lambda>r. R' r))"
  unfolding THIN_def
  by (rule corresTA_L2_catch', (simp add: basic_abstract_defs)+)


term "corresTA P rx ex f g" 


lemma corresTA_yield: 
  "abstract_val True v' (map_xval ex rx) v \<Longrightarrow> corresTA P rx ex (yield v') (yield v)"
  apply (auto simp add: corresTA_refines_conv rel_word_abs_def abstract_val_def rel_xval.simps map_xval_def 
      intro!: refines_yield split: xval_splits)
  done


lemma map_sum_apply: "map_sum ex rx = (\<lambda>v. case v of Inl l \<Rightarrow> Inl (ex l) | Inr r \<Rightarrow> Inr (rx r))"
  by (simp add: fun_eq_iff split_sum_all)


(* FIXME: to spec monad *)
lemma refines_try_rel_prod: 
  assumes "refines f g s t (rel_prod (rel_xval (rel_sum L R) R) S)"
  shows "refines (try f) (try g) s t (rel_prod (rel_xval L R) S)"
  using assms
  apply (clarsimp simp add: refines_def_old reaches_try unnest_exn_def rel_xval.simps split: xval_splits sum.splits)
  subgoal for r s' r'
    apply (erule_tac x=r' in allE)
    apply (erule_tac x=s' in allE)

    apply (cases r)
    subgoal for e
      apply (clarsimp simp add: default_option_def Exn_def, safe)
       apply (metis Exception_eq_Exception Exn_def Exn_neq_Result exception_or_result_cases not_None_eq sum_all_ex(2))
      by (smt (verit, ccfv_threshold) Exn_eq_Exception(2) Exn_neq_Result 
          rel_sum.cases rel_sum_simps(2) theLeft.simps the_Exn_Exn(2))

    subgoal for v
      apply (clarsimp simp add: default_option_def Exn_def, safe)
        apply (metis Exception_eq_Exception Exn_def Exn_neq_Result exception_or_result_cases not_None_eq sum_all_ex(2))
      apply (smt (verit, ccfv_threshold) Exn_def Result_neq_Exn rel_sum.cases rel_sum_simps(3) unnest_exn_eq_simps(3))
      by (metis Exn_def Result_eq_Result Result_neq_Exn)
    done
  done

lemma rel_map_xval_sum_rel_sum_conv: 
  "rel_xval (\<lambda>c a. a = map_sum ex rx c) (\<lambda>c a. a = rx c) =
       rel_xval (rel_sum (\<lambda>c a. a = ex c) (\<lambda>c a. a = rx c)) (\<lambda>c a. a = rx c)"
  apply (rule ext)+
  apply (auto simp add: rel_xval.simps rel_sum.simps)
  done

lemma corresTA_L2_try':
  assumes corres_L_L': "corresTA P rx (map_sum ex rx) L L'" 
  shows "corresTA P rx ex (L2_try L) (L2_try L')"
  unfolding L2_defs 
  apply (clarsimp simp add: corresTA_refines_conv rel_word_abs_def)
  apply (rule refines_try_rel_prod)
  using corres_L_L' 
  apply (auto simp add: corresTA_refines_conv rel_word_abs_def rel_map_xval_sum_rel_sum_conv)
  done

lemma corresTA_L2_while:
  assumes init_corres: "abstract_val Q i rx i'"
  and cond_corres: "PROP THIN (\<And>r r' s. abs_var r rx r'
                           \<Longrightarrow> abstract_val (G r s) (C r s) id (C' r' s))"
  and body_corres: "PROP THIN (\<And>r r'. abs_var r rx r'
                           \<Longrightarrow> corresTA (P r) rx ex (B r) (B' r'))"
  shows "corresTA (\<lambda>_. Q) rx ex
       (L2_guarded_while (\<lambda>r s. G r s) (\<lambda>r s. C r s) (\<lambda>r. L2_seq (L2_guard (\<lambda>s. P r s)) (\<lambda>_. B r)) i x)
       (L2_while (\<lambda>r s. C' r s) B' i' x)"
proof -
  note cond_corres = cond_corres [unfolded THIN_def, rule_format]
  note body_corres = body_corres [unfolded THIN_def, rule_format]
  note body_corres' =
       corresXF_guarded_while_body [OF body_corres [unfolded corresTA_def]]

  have init_corres':
    "Q \<Longrightarrow> i = rx i'"
    using init_corres
    by (simp add: basic_abstract_defs)

  note basic_abstract_defs [simp]
  show ?thesis
    thm corresXF_assume_pre
    apply (clarsimp simp: L2_defs  corresTA_def gets_return)
    apply (rule corresXF_assume_pre)
    thm corresXF_guarded_while
    apply (rule corresXF_guarded_while [where P="\<lambda>r s. G (rx r) s"])
    subgoal for s s' x y
      apply (cut_tac r'=x in body_corres, simp)
      apply (fastforce simp add: corresTA_refines_conv corresXF_refines_conv refines_def_old reaches_bind succeeds_bind 
          rel_word_abs_def rel_xval.simps split: xval_splits)
      done
    subgoal 
       apply (insert cond_corres)[1]
      apply (clarsimp)
      done
    subgoal
      by (auto simp add: runs_to_partial_def_old split: xval_splits)
    subgoal using init_corres
      by (clarsimp)
    subgoal using init_corres'
      by clarsimp
    done
qed


lemma corresTA_L2_guard:
  "\<lbrakk> \<And>s. abstract_val (Q s) (G s) id (G' s) \<rbrakk>
           \<Longrightarrow> corresTA (\<lambda>_. True) rx ex (L2_guard (\<lambda>s. G s \<and> Q s)) (L2_guard (\<lambda>s. G' s))"
  unfolding L2_defs 
  apply (auto simp add: corresTA_refines_conv abstract_val_def intro!: refines_guard)
  done


lemma corresTA_L2_guard':
  "\<lbrakk>\<And>s. abstract_val (Q s) (G s) id (G' s); 
    \<And>s. R s \<Longrightarrow> G s \<and> Q s\<rbrakk>
           \<Longrightarrow> corresTA (\<lambda>_. True) rx ex (L2_guard (\<lambda>s. R s)) (L2_guard (\<lambda>s. G' s))"
  unfolding L2_defs 
  apply (auto simp add: corresTA_refines_conv abstract_val_def intro!: refines_guard)
  done

lemma corresTA_L2_guarded_simple:
  assumes G_G': "\<And>s. abstract_val (Q s) (G s) id (G' s)"
  assumes f_f': "\<And>s. G' s \<Longrightarrow> Q s \<Longrightarrow> G s \<Longrightarrow> corresTA P rx ex f f'"
  shows "corresTA (\<lambda>_. True) rx ex (L2_guarded (\<lambda>s. G s \<and> Q s \<and> P s) f) (L2_guarded G' f')"
  unfolding L2_defs L2_guarded_def
  apply (clarsimp simp add: corresTA_refines_conv)
  apply (rule refines_bind_guard_right)
  using G_G' f_f'
  by (auto simp add: corresTA_refines_conv refines_def_old succeeds_bind reaches_bind abstract_val_def)

lemma corresTA_L2_spec:
  "(\<And>s t. abstract_val (Q s) (P s t) id (P' s t)) \<Longrightarrow>
   corresTA Q rx ex (L2_spec {(s, t). P s t}) (L2_spec {(s, t). P' s t})"
  unfolding L2_defs
  by (auto simp add: corresTA_refines_conv abstract_val_def refines_def_old reaches_bind succeeds_bind)

lemma corresTA_L2_assume:
  "(\<And>s r t. abstract_val (Q s) (P s) (\<lambda>X. (\<lambda>(x, y). (rx x, y)) ` X) (P' s)) \<Longrightarrow>
   corresTA Q rx ex (L2_assume P) (L2_assume P')"
  unfolding L2_defs
  apply (auto simp add: corresTA_refines_conv abstract_val_def refines_def_old reaches_bind succeeds_bind
    rel_word_abs_def rel_xval.simps)
  done

lemma corresTA_L2_condition:
  "\<lbrakk>PROP THIN (Trueprop (corresTA P rx ex L L'));
    PROP THIN (Trueprop (corresTA Q rx ex R R'));
     \<And>s. abstract_val (T s) (C s) id (C' s)  \<rbrakk>
   \<Longrightarrow> corresTA T rx ex
          (L2_condition (\<lambda>s. C s)
            (L2_seq (L2_guard P) (\<lambda>_. L))
            (L2_seq (L2_guard Q) (\<lambda>_. R))
           ) (L2_condition (\<lambda>s. C' s) L' R')"
  unfolding THIN_def L2_defs
  by (auto simp add: corresTA_refines_conv abstract_val_def intro!: refines_condition refines_bind_guard_right)


lemma L2_call_L2_defs: "L2_call x emb ns = L2_catch x (\<lambda>e. L2_throw (emb e) ns)"
  unfolding L2_defs L2_call_def
  apply (rule spec_monad_eqI)
  apply (clarsimp simp add: runs_to_iff)
  apply (auto simp add: runs_to_def_old map_exn_def split: xval_splits)
  done

lemma corresTA_L2_call:
  "\<lbrakk>corresTA P rx ex' A B; 
    \<And>r r'. abs_var r ex' r'  \<Longrightarrow> abstract_val Q (emb r) ex (emb' r')
    \<rbrakk> \<Longrightarrow>
        corresTA (\<lambda>s. P s \<and> Q) rx ex (L2_call A emb ns) (L2_call B emb' ns)"
  unfolding L2_call_def
  by (force simp add: corresTA_refines_conv abstract_val_def abs_var_def refines_def_old reaches_map_value map_exn_def
    rel_word_abs_def rel_xval.simps)

(* Backup rule to corresTA_L2_call. Converts the return type of the function call. *)
lemma corresTA_L2_call':
  "\<lbrakk> corresTA P f1 ex' A B;
     valid_typ_abs_fn Q1 Q1' f1 f1';
     valid_typ_abs_fn Q2 Q2' f2 f2';
    \<And>r r'. abs_var r ex' r'  \<Longrightarrow> abstract_val Q (emb r) ex (emb' r')
   \<rbrakk> \<Longrightarrow>
   corresTA (\<lambda>s. P s \<and> Q) f2 ex
       (L2_seq (L2_call A emb ns) (ETA_TUPLED (\<lambda>ret. (L2_seq (L2_guard (\<lambda>_. Q1' ret)) (\<lambda>_. L2_gets (\<lambda>_. f2 (f1' ret)) ns)))))
       (L2_call B emb' ns)"
  unfolding L2_call_def L2_defs
  apply (clarsimp simp add:  ETA_TUPLED_def corresTA_refines_conv abstract_val_def abs_var_def 
      refines_def_old reaches_map_value map_exn_def reaches_bind succeeds_bind reaches_succeeds
    rel_word_abs_def rel_xval.simps)
  subgoal for s s' r'
    apply (erule_tac x=s in allE)
    apply clarsimp
    apply (cases r')
    subgoal
      apply (simp add: default_option_def Exn_def [symmetric])
      by (smt (z3) Exn_def Exn_neq_Result case_exception_or_result_Exn case_xval_simps(1) the_Exn_Exn(1))
    subgoal
      apply simp
      by (metis (mono_tags, lifting) Exn_neq_Result case_exception_or_result_Result case_xval_simps(2) the_Result_simp)
    done
  done
  
lemma corresTA_L2_unknown:
  "corresTA (\<lambda>_. True) rx ex (L2_unknown x) (L2_unknown x)"
  unfolding L2_defs
  by (auto simp add: corresTA_refines_conv intro!: refines_select)


lemma corresTA_L2_call_exec_concrete:
  "\<lbrakk> corresTA P rx ex' A B ; 
    \<And>r r'. abs_var r ex' r'  \<Longrightarrow> abstract_val Q (emb r) ex (emb' r')\<rbrakk> \<Longrightarrow>
        corresTA (\<lambda>s. \<forall>s'. s = st s' \<longrightarrow> P s' \<and> Q) rx ex
               (exec_concrete st (L2_call A emb ns))
               (exec_concrete st (L2_call B emb' ns))"
  unfolding L2_defs L2_call_def
  apply (clarsimp simp add: corresTA_refines_conv abstract_val_def abs_var_def)
  apply (clarsimp simp add: refines_def_old succeeds_exec_concrete_iff reaches_exec_concrete 
      reaches_map_value rel_word_abs_def rel_xval.simps map_exn_def split: xval_splits )
  subgoal for r t t' r'
    apply (erule_tac x=t in allE)
    apply clarsimp
    apply (cases r')
    subgoal
      apply (clarsimp simp add: default_option_def Exn_def [symmetric])
      by (metis Exn_eq_Exn Exn_neq_Result)
    subgoal
      apply simp
      by (metis Result_eq_Result Result_neq_Exn)
    done
  done
  

lemma corresTA_L2_call_exec_abstract:
  "\<lbrakk> corresTA P rx ex' A B; 
    \<And>r r'. abs_var r ex' r'  \<Longrightarrow> abstract_val Q (emb r) ex (emb' r') \<rbrakk> \<Longrightarrow>
        corresTA (\<lambda>s. P (st s) \<and> Q) rx ex
               (exec_abstract st (L2_call A emb ns))
               (exec_abstract st (L2_call B emb' ns))"
  unfolding L2_defs L2_call_def
  apply (clarsimp simp add: corresTA_refines_conv abstract_val_def abs_var_def)
  apply (clarsimp simp add: refines_def_old succeeds_exec_abstract_iff reaches_exec_abstract 
      reaches_map_value rel_word_abs_def rel_xval.simps map_exn_def split: xval_splits )
  subgoal for s r s' r'
    apply (erule_tac x="st s" in allE)
    apply clarsimp
    apply (cases r')
    subgoal
      apply (clarsimp simp add: default_option_def Exn_def [symmetric])
      by (metis Exn_eq_Exn Exn_neq_Result)
    subgoal
      apply simp
      by (metis Result_eq_Result Result_neq_Exn)
    done
  done


(* More backup rules for calls. *)
lemma corresTA_L2_call_exec_concrete':
  "\<lbrakk> corresTA P f1 ex' A B;
     valid_typ_abs_fn Q1 Q1' f1 f1';
     valid_typ_abs_fn Q2 Q2' f2 f2'; 
     \<And>r r'. abs_var r ex' r'  \<Longrightarrow> abstract_val Q (emb r) ex (emb' r')
   \<rbrakk> \<Longrightarrow>
   corresTA (\<lambda>s. \<forall>s'. s = st s' \<longrightarrow> P s' \<and> Q) f2 ex
       (L2_seq (exec_concrete st (L2_call A emb ns)) (\<lambda>ret. (L2_seq (L2_guard (\<lambda>_. Q1' ret)) (\<lambda>_. L2_gets (\<lambda>_. f2 (f1' ret)) []))))
       (exec_concrete st (L2_call B emb' ns))"
  unfolding L2_defs L2_call_def
  apply (clarsimp simp add: corresTA_refines_conv abstract_val_def abs_var_def)
  apply (clarsimp simp add: refines_def_old succeeds_exec_concrete_iff reaches_exec_concrete 
      reaches_bind succeeds_bind
      reaches_map_value rel_word_abs_def rel_xval.simps map_exn_def split: xval_splits )
  subgoal for r t t' r'
    apply (erule_tac x=t in allE)
    apply clarsimp
    apply (cases r')
    subgoal
      apply (clarsimp simp add: default_option_def Exn_def [symmetric])
      by (smt (z3) Exn_def Exn_eq_Exn Exn_neq_Result case_exception_or_result_Exn)


    subgoal for v
      apply clarsimp
      apply (erule_tac x="Result v" in allE)
      apply (erule_tac x="t'" in allE)
      by (smt (z3) Exn_neq_Result Result_eq_Result case_exception_or_result_Result)
    done
  done

lemma corresTA_L2_call_exec_abstract':
  "\<lbrakk> corresTA P f1 ex' A B;
     valid_typ_abs_fn Q1 Q1' f1 f1';
     valid_typ_abs_fn Q2 Q2' f2 f2';
    \<And>r r'. abs_var r ex' r'  \<Longrightarrow> abstract_val Q (emb r) ex (emb' r')
   \<rbrakk> \<Longrightarrow>
   corresTA (\<lambda>s. P (st s) \<and> Q) f2 ex
       (L2_seq (exec_abstract st (L2_call A emb ns)) (\<lambda>ret. (L2_seq (L2_guard (\<lambda>_. Q1' ret)) (\<lambda>_. L2_gets (\<lambda>_. f2 (f1' ret)) []))))
       (exec_abstract st (L2_call B emb' ns))"
  unfolding L2_defs L2_call_def
  apply (clarsimp simp add: corresTA_refines_conv abstract_val_def abs_var_def)
  apply (clarsimp simp add: refines_def_old succeeds_exec_abstract_iff reaches_exec_abstract 
      reaches_bind succeeds_bind
      reaches_map_value rel_word_abs_def rel_xval.simps map_exn_def split: xval_splits )
  subgoal for s r s' r'
    apply (erule_tac x="st s" in allE)
    apply clarsimp
    apply (cases r')
    subgoal
      apply (clarsimp simp add: default_option_def Exn_def [symmetric])
      by (smt (z3) Exn_def Exn_eq_Exn Exn_neq_Result case_exception_or_result_Exn)
    subgoal
      apply clarsimp
      by (smt (z3) Result_eq_Result Result_neq_Exn case_exception_or_result_Result)
    done
  done

 

text \<open>Avoid higher-order unification issues by explicit application with @{term "($)"}: 
\<^item> in concrete program position enforces 'obvious' instantiation
\<^item> in abstract program position enforces introduction of two separate variables for @{term a} and 
  @{term b} instead of a higher-order flex-flex pair.\<close>

lemma abstract_val_fun_app:
   "\<lbrakk> abstract_val Q b id b'; abstract_val P a id a' \<rbrakk> \<Longrightarrow>
           abstract_val (P \<and> Q) (f $ (a $ b)) f (a' $ b')"
  by (simp add: basic_abstract_defs)

lemma corresTA_precond_to_guard:
  "corresTA (\<lambda>s. P s) rx ex A A' \<Longrightarrow> corresTA (\<lambda>_. True) rx ex (L2_seq (L2_guard (\<lambda>s. P s)) (\<lambda>_. A)) A'"
  unfolding L2_defs
  by (auto simp add: corresTA_refines_conv intro: refines_bind_guard_right)


lemma corresTA_precond_to_asm:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> corresTA (\<lambda>_. True) rx ex A A' \<rbrakk> \<Longrightarrow> corresTA P rx ex A A'"
  by (clarsimp simp: corresXF_def corresTA_def)

lemma L2_guard_true: "L2_seq (L2_guard (\<lambda>_. True)) A = A ()"
  unfolding L2_defs
  apply (rule spec_monad_ext)
  apply (auto simp add: run_bind run_guard)
  done

lemma corresTA_simp_trivial_guard:
  "corresTA P rx ex (L2_seq (L2_guard (\<lambda>_. True)) A) C \<equiv> corresTA P rx ex (A ()) C"
  by (simp add: L2_guard_true)

lemma corresTA_extract_preconds_of_call_init:
  "\<lbrakk> corresTA (\<lambda>s. P) rx ex A A' \<rbrakk> \<Longrightarrow> corresTA (\<lambda>s. P \<and> True) rx ex A A'"
  by simp

lemma corresTA_extract_preconds_of_call_step:
  "\<lbrakk> corresTA (\<lambda>s. (abs_var a f a' \<and> R) \<and> C) rx ex A A'; abstract_val Y a f a' \<rbrakk>
           \<Longrightarrow> corresTA (\<lambda>s. R \<and> (Y \<and> C)) rx ex A A'"
  by (clarsimp simp: corresXF_def corresTA_def basic_abstract_defs)

lemma corresTA_extract_preconds_of_call_final:
  "\<lbrakk> corresTA (\<lambda>s. (abs_var a f a') \<and> C) rx ex A A'; abstract_val Y a f a' \<rbrakk>
           \<Longrightarrow> corresTA (\<lambda>s. (Y \<and> C)) rx ex A A'"
  by (clarsimp simp: corresXF_def corresTA_def basic_abstract_defs)

lemma corresTA_extract_preconds_of_call_final':
  "\<lbrakk> corresTA (\<lambda>s. True \<and> C) rx ex A A' \<rbrakk>
           \<Longrightarrow> corresTA (\<lambda>s. C) rx ex A A'"
  by (clarsimp simp: corresXF_def corresTA_def)

lemma corresTA_extract_preconds_of_call_init_prems:
  "\<lbrakk> corresTA (\<lambda>s. P \<and> True) rx ex A A'\<rbrakk> \<Longrightarrow> corresTA (\<lambda>s. P) rx ex A A'"
  by simp

lemma corresTA_extract_preconds_of_call_step_prems:
  "\<lbrakk>\<And>Y.  abstract_val Y a f a' \<Longrightarrow> corresTA (\<lambda>s. R \<and> (Y \<and> C)) rx ex A A' \<rbrakk>
           \<Longrightarrow> corresTA (\<lambda>s. (abs_var a f a' \<and> R) \<and> C) rx ex A A'"
  by (clarsimp simp: corresXF_def corresTA_def basic_abstract_defs)

lemma corresTA_extract_preconds_of_call_final_prems:
  "\<lbrakk>\<And>Y. abstract_val Y a f a' \<Longrightarrow> corresTA (\<lambda>s. (Y \<and> C)) rx ex A A'\<rbrakk>
           \<Longrightarrow> corresTA (\<lambda>s. (abs_var a f a') \<and> C) rx ex A A' "
  by (auto simp: corresXF_def corresTA_def basic_abstract_defs split: prod.splits sum.splits)

lemma corresTA_extract_preconds_of_call_final'_prems:
  "\<lbrakk>corresTA (\<lambda>s. C) rx ex A A' \<rbrakk>
           \<Longrightarrow>  corresTA (\<lambda>s. True \<and> C) rx ex A A'"
  by (clarsimp simp: corresXF_def corresTA_def)

lemma corresTA_case_prod:
 "\<lbrakk> introduce_typ_abs_fn rx1;
    introduce_typ_abs_fn rx2;
    abstract_val (Q x) x (map_prod rx1 rx2) x';
      \<And>a b a' b'. \<lbrakk> abs_var a rx1 a'; abs_var  b rx2 b' \<rbrakk>
                      \<Longrightarrow>  corresTA (P a b) rx ex (M a b) (M' a' b') \<rbrakk>  \<Longrightarrow>
    corresTA (\<lambda>s. case x of (a, b) \<Rightarrow> P a b s \<and> Q (a, b)) rx ex (case x of (a, b) \<Rightarrow> M a b) (case x' of (a, b) \<Rightarrow> M' a b)"
  apply (clarsimp simp add: corresTA_def)
  apply (rule corresXF_assume_pre)
  apply (clarsimp simp: split_def map_prod_def basic_abstract_defs)
  done

lemma abstract_val_case_prod:
  "\<lbrakk> abstract_val True r (map_prod f g) r';
       \<And>a b a' b'. \<lbrakk>  abs_var a f a'; abs_var  b g b' \<rbrakk>
                     \<Longrightarrow> abstract_val (P a b) (M a b) h (M' a' b') \<rbrakk>
       \<Longrightarrow> abstract_val (P (fst r) (snd r))
            (case r of (a, b) \<Rightarrow> M a b) h
            (case r' of (a, b) \<Rightarrow> M' a b)"
  apply (cases r, cases r')
  apply (clarsimp simp: map_prod_def basic_abstract_defs)
  done

lemma abstract_val_case_prod_fun_app:
  "\<lbrakk> abstract_val True r (map_prod f g) r';
       \<And>a b a' b'. \<lbrakk>  abs_var a f a'; abs_var b g b' \<rbrakk>
                     \<Longrightarrow> abstract_val (P a b) (M a b s) h (M' a' b' s) \<rbrakk>
       \<Longrightarrow> abstract_val (P (fst r) (snd r))
            ((case r of (a, b) \<Rightarrow> M a b) s) h
            ((case r' of (a, b) \<Rightarrow> M' a b) s)"
  apply (cases r, cases r')
  apply (clarsimp simp: map_prod_def basic_abstract_defs)
  done

lemma abstract_val_of_nat:
  "abstract_val (r \<le> UWORD_MAX TYPE('a::len)) r unat (of_nat r :: 'a word)"
  by (clarsimp simp: unat_of_nat_eq UWORD_MAX_def le_to_less_plus_one basic_abstract_defs)

lemma abstract_val_of_int:
  "abstract_val (WORD_MIN TYPE('a::len) \<le> r \<and> r \<le> WORD_MAX TYPE('a)) r sint (of_int r :: 'a signed word)"
  by (clarsimp simp: sint_of_int_eq WORD_MIN_def WORD_MAX_def basic_abstract_defs)


lemma abstract_val_tuple:
  "\<lbrakk> abstract_val P a absL a';
     abstract_val Q b absR b' \<rbrakk> \<Longrightarrow>
         abstract_val (P \<and> Q) (a, b) (map_prod absL absR) (a', b')"
  by (clarsimp simp add: basic_abstract_defs)

lemma abstract_val_Inl:
  "\<lbrakk> abstract_val P a absL a'\<rbrakk> \<Longrightarrow>
         abstract_val P (Inl a) (map_sum absL absR) (Inl a')"
  by (clarsimp simp add: basic_abstract_defs)

lemma abstract_val_Inr:
  "\<lbrakk> abstract_val P b absR b'\<rbrakk> \<Longrightarrow>
         abstract_val P (Inr b) (map_sum absL absR) (Inr b')"
  by (clarsimp simp add: basic_abstract_defs)


lemma abstract_val_func:
   "\<lbrakk> abstract_val P a id a'; abstract_val Q b id b' \<rbrakk>
        \<Longrightarrow>  abstract_val (P \<and> Q) (f a b) id (f a' b')"
  by (clarsimp simp add: basic_abstract_defs)

lemma abstract_val_conj:
  "\<lbrakk> abstract_val P a id a';
        abstract_val Q b id b' \<rbrakk> \<Longrightarrow>
     abstract_val (P \<and> (a \<longrightarrow> Q)) (a \<and> b) id (a' \<and> b')"
  apply (clarsimp simp add: basic_abstract_defs)
  apply blast
  done

lemma abstract_val_disj:
  "\<lbrakk> abstract_val P a id a';
        abstract_val Q b id b' \<rbrakk> \<Longrightarrow>
     abstract_val (P \<and> (\<not> a \<longrightarrow> Q)) (a \<or> b) id (a' \<or> b')"
  apply (clarsimp simp add: basic_abstract_defs)
  apply blast
  done

lemma abstract_val_unwrap:
  "\<lbrakk> introduce_typ_abs_fn f; abstract_val P a f b \<rbrakk>
        \<Longrightarrow> abstract_val P a id (f b)"
  by (simp add: basic_abstract_defs)

lemma abstract_val_uint:
  "\<lbrakk> introduce_typ_abs_fn unat; abstract_val P x unat x' \<rbrakk>
      \<Longrightarrow> abstract_val P (int x) id (uint x')"
  by (clarsimp simp add: basic_abstract_defs)

lemma abstract_val_lambda:
   "\<lbrakk> \<And>v. abstract_val (P v) (a v) id (a' v) \<rbrakk> \<Longrightarrow>
           abstract_val (\<forall>v. P v) (\<lambda>v. a v) id (\<lambda>v. a' v)"
  by (auto simp add: basic_abstract_defs)

(* Rules for translating simpl wrappers. *)
lemma corresTA_call_L1:
  "abstract_val True arg_xf id arg_xf' \<Longrightarrow>
   corresTA (\<lambda>_. True) id id
     (L2_call_L1 arg_xf gs ret_xf l1body)
     (L2_call_L1 arg_xf' gs ret_xf l1body)"
  apply (unfold corresTA_def abstract_val_def id_def)
  apply (subst (asm) simp_thms)
  apply (erule subst)
  apply (rule corresXF_id[simplified id_def])
  done


context stack_heap_state
begin
lemma corresTA_with_fresh_stack_ptr[word_abs]: 
  assumes f[simplified THIN_def, rule_format]: "PROP THIN (\<And>p. corresTA Q rx ex (f\<^sub>a p) (f\<^sub>c p))"
  assumes init: "\<And>s. abstract_val (P s) (init\<^sub>a s) id (init\<^sub>c s)"
  shows "corresTA P rx ex 
           (with_fresh_stack_ptr n init\<^sub>a (L2_VARS (\<lambda>p. (L2_seq (L2_guard Q) (\<lambda>_.  f\<^sub>a p))) nm)) 
           (with_fresh_stack_ptr n init\<^sub>c (L2_VARS f\<^sub>c nm))"
  apply (rule refines_corresTA)
  apply (simp add: L2_seq_def L2_guard_def rel_word_abs_def)
  apply (rule refines_rel_prod_with_fresh_stack_ptr )
  subgoal for s
    using init [of s] 
    by (simp add: abstract_val_def)
  subgoal for s s' p
    apply (rule refines_bind_guard_right)
    apply (simp only: rel_word_abs_def [symmetric])
    apply (rule corresTA_refines)
     apply (rule f)
    apply simp
    done
  done
end

context typ_heap_typing
begin

lemma corresTA_guard_with_fresh_stack_ptr[word_abs]: 
  assumes f[simplified THIN_def, rule_format]: "PROP THIN (\<And>p. corresTA Q rx ex (f\<^sub>a p) (f\<^sub>c p))"
  assumes init: "\<And>s. abstract_val (P s) (init\<^sub>a s) id (init\<^sub>c s)"
  shows "corresTA P rx ex 
           (guard_with_fresh_stack_ptr n init\<^sub>a (L2_VARS (\<lambda>p. (L2_seq (L2_guard Q) (\<lambda>_.  f\<^sub>a p))) nm)) 
           (guard_with_fresh_stack_ptr n init\<^sub>c (L2_VARS f\<^sub>c nm))"
  apply (rule refines_corresTA)
  apply (simp add: L2_seq_def L2_guard_def rel_word_abs_def)
  apply (rule refines_rel_xval_guard_with_fresh_stack_ptr )
  subgoal for s
    using init [of s] 
    by (simp add: abstract_val_def)
  subgoal for s s' p
    apply (rule refines_bind_guard_right)
    apply (simp only: rel_word_abs_def [symmetric])
    apply (rule corresTA_refines)
     apply (rule f)
    apply simp
    done
  done

lemma corresTA_assume_with_fresh_stack_ptr[word_abs]: 
  assumes f[simplified THIN_def, rule_format]: "PROP THIN (\<And>p. corresTA Q rx ex (f\<^sub>a p) (f\<^sub>c p))"
  assumes init: "\<And>s. abstract_val (P s) (init\<^sub>a s) id (init\<^sub>c s)"
  shows "corresTA P rx ex 
           (assume_with_fresh_stack_ptr n init\<^sub>a (L2_VARS (\<lambda>p. (L2_seq (L2_guard Q) (\<lambda>_.  f\<^sub>a p))) nm)) 
           (assume_with_fresh_stack_ptr n init\<^sub>c (L2_VARS f\<^sub>c nm))"
  apply (rule refines_corresTA)
  apply (simp add: L2_seq_def L2_guard_def rel_word_abs_def)
  apply (rule refines_rel_xval_assume_with_fresh_stack_ptr)
  subgoal for s
    using init [of s] 
    by (simp add: abstract_val_def)
  subgoal for s s' p
    apply (rule refines_bind_guard_right)
    apply (simp only: rel_word_abs_def [symmetric])
    apply (rule corresTA_refines)
     apply (rule f)
    apply simp
    done
  done

lemma corresTA_with_fresh_stack_ptr[word_abs]: 
  assumes f[simplified THIN_def, rule_format]: "PROP THIN (\<And>p. corresTA Q rx ex (f\<^sub>a p) (f\<^sub>c p))"
  assumes init: "\<And>s. abstract_val (P s) (init\<^sub>a s) id (init\<^sub>c s)"
  shows "corresTA P rx ex 
           (with_fresh_stack_ptr n init\<^sub>a (L2_VARS (\<lambda>p. (L2_seq (L2_guard Q) (\<lambda>_.  f\<^sub>a p))) nm)) 
           (with_fresh_stack_ptr n init\<^sub>c (L2_VARS f\<^sub>c nm))"
  apply (rule refines_corresTA)
  apply (simp add: L2_seq_def L2_guard_def rel_word_abs_def)
  apply (rule refines_rel_xval_with_fresh_stack_ptr)
  subgoal for s
    using init [of s] 
    by (simp add: abstract_val_def)
  subgoal for s s' p
    apply (rule refines_bind_guard_right)
    apply (simp only: rel_word_abs_def [symmetric])
    apply (rule corresTA_refines)
     apply (rule f)
    apply simp
    done
  done
end


lemma abstract_val_call_L1_args:
  "abstract_val P x id x' \<Longrightarrow> abstract_val P y id y' \<Longrightarrow>
   abstract_val P (x and y) id (x' and y')"
  by (simp add: basic_abstract_defs)

lemma abstract_val_call_L1_arg:
  "abs_var x id x' \<Longrightarrow> abstract_val P (\<lambda>s. f s = x) id (\<lambda>s. f s = x')"
  by (simp add: basic_abstract_defs)

(* Variable abstraction *)

lemma abstract_val_abs_var [consumes 1]:
  "\<lbrakk> abs_var a f a' \<rbrakk> \<Longrightarrow> abstract_val True a f a'"
  by (clarsimp simp: fun_upd_def basic_abstract_defs split: if_splits)

lemma abstract_val_abs_var_concretise [consumes 1]:
  "\<lbrakk> abs_var a A a'; introduce_typ_abs_fn A; valid_typ_abs_fn PA PC A (C :: 'a \<Rightarrow> 'c)  \<rbrakk>
      \<Longrightarrow> abstract_val (PC a) (C a) id a'"
  by (clarsimp simp: fun_upd_def basic_abstract_defs split: if_splits)

lemma abstract_val_abs_var_give_up [consumes 1]:
  "\<lbrakk> abs_var a id a' \<rbrakk> \<Longrightarrow> abstract_val True (A a) A a'"
  by (clarsimp simp: fun_upd_def basic_abstract_defs split: if_splits)


lemma abstract_val_abs_var_sint_unat [consumes 1]:
  "\<lbrakk> abs_var a sint a' \<rbrakk> \<Longrightarrow> abstract_val (0 \<le> a) (nat a) id (unat a')"
  apply (simp add: basic_abstract_defs )
  by (metis nat_uint_eq signed_0 sint_eq_uint word_msb_0 word_sle_eq word_sle_msb_le)

lemma abstract_val_abs_var_uint_unat [consumes 1]:
 "\<lbrakk> abs_var a uint a' \<rbrakk> \<Longrightarrow> abstract_val True (nat a) id (unat a')"
  by (simp add: basic_abstract_defs)

lemma abs_var_id: "(abs_var a id a') = (a' = a)"
  by (auto simp add: abs_var_def abstract_val_def)

lemma abstract_val_id: "abstract_val P a id a"
  by (simp add: abstract_val_def)
lemmas abstract_val_id_unit_ptr = abstract_val_id [where a= "a::unit ptr" and P = True] for a

lemma abstract_val_id_True: "abstract_val True a id a"
  by (rule abstract_val_id)

lemmas abs_var_id_unit_ptr = abs_var_id [where a= "a::unit ptr"] for a

(* Misc *)

lemma len_of_word_comparisons [L2opt]:
  "len_of TYPE(64) \<le> len_of TYPE(64)"
  "len_of TYPE(32) \<le> len_of TYPE(64)"
  "len_of TYPE(16) \<le> len_of TYPE(64)"
  "len_of TYPE( 8) \<le> len_of TYPE(64)"
  "len_of TYPE(32) \<le> len_of TYPE(32)"
  "len_of TYPE(16) \<le> len_of TYPE(32)"
  "len_of TYPE( 8) \<le> len_of TYPE(32)"
  "len_of TYPE(16) \<le> len_of TYPE(16)"
  "len_of TYPE( 8) \<le> len_of TYPE(16)"
  "len_of TYPE( 8) \<le> len_of TYPE( 8)"

  "len_of TYPE(32) < len_of TYPE(64)"
  "len_of TYPE(16) < len_of TYPE(64)"
  "len_of TYPE( 8) < len_of TYPE(64)"
  "len_of TYPE(16) < len_of TYPE(32)"
  "len_of TYPE( 8) < len_of TYPE(32)"
  "len_of TYPE( 8) < len_of TYPE(16)"

  "len_of TYPE('a::len signed) = len_of TYPE('a)"
  "(len_of TYPE('a) = len_of TYPE('a)) = True"
  by auto

lemma sbintrunc_eq: "0 \<le> i \<Longrightarrow> i < 2^n \<Longrightarrow> sbintrunc n i = i"
  apply (induction n arbitrary: i)
   apply auto
  done

lemma uint_ucast:
  "uint (ucast x :: ('a :: len) word) = uint x mod 2 ^ LENGTH('a)"
  unfolding uint_nat unat_ucast by (simp add: zmod_int)

lemma uint_scast':
  "uint (SCAST('a::len \<rightarrow> 'b::len) c) = sint c mod 2^LENGTH('b)"
  by (metis Word.of_int_sint word_uint.eq_norm)

lemma uint_ucast':
  "uint (UCAST('a::len \<rightarrow> 'b::len) c) = uint c mod 2^LENGTH('b)"
  by (metis Word.of_int_uint word_uint.eq_norm)

lemma sint_ucast':
  "LENGTH('a) < LENGTH('b) \<Longrightarrow> sint (UCAST('a::len \<rightarrow> 'b::len) c) = uint c"
  by (smt bintrunc_bintrunc_ge less_or_eq_imp_le signed_take_bit_eq uint_sint unsigned_ucast_eq 
    unsigned_word_eqI)

lemma scast_ucast_eq_ucast [simp, L2opt]:
  "LENGTH('a::len) < LENGTH('b::len) \<Longrightarrow> LENGTH('b) \<le> LENGTH('c::len) \<Longrightarrow>
    SCAST('b \<rightarrow> 'c) (UCAST('a \<rightarrow> 'b) x) = UCAST ('a \<rightarrow> 'c) x"
  unfolding word_uint_eq_iff uint_scast' uint_ucast sint_ucast' ..


lemma scast_ucast_simps [simp, L2opt]:
  "\<lbrakk> len_of TYPE('b) \<le> len_of TYPE('a); len_of TYPE('c) \<le> len_of TYPE('b) \<rbrakk> \<Longrightarrow>
         (scast (ucast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = ucast a"
  "\<lbrakk> len_of TYPE('c) \<le> len_of TYPE('a); len_of TYPE('c) \<le> len_of TYPE('b) \<rbrakk> \<Longrightarrow>
         (scast (ucast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = ucast a"
  "\<lbrakk> len_of TYPE('a) \<le> len_of TYPE('b); len_of TYPE('c) \<le> len_of TYPE('b) \<rbrakk> \<Longrightarrow>
         (scast (ucast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = ucast a"
  "\<lbrakk> len_of TYPE('a) \<le> len_of TYPE('b) \<rbrakk> \<Longrightarrow>
     (scast (scast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = scast a"
  "\<lbrakk> len_of TYPE('b) \<le> len_of TYPE('a); len_of TYPE('c) \<le> len_of TYPE('b) \<rbrakk> \<Longrightarrow>
            (ucast (scast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = scast a"
  "\<lbrakk> len_of TYPE('c) \<le> len_of TYPE('a); len_of TYPE('c) \<le> len_of TYPE('b) \<rbrakk> \<Longrightarrow>
     (ucast (scast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = scast a"
  "\<lbrakk> len_of TYPE('a) \<le> len_of TYPE('b); len_of TYPE('c) \<le> len_of TYPE('b) \<rbrakk> \<Longrightarrow>
     (ucast (scast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = scast a"
  "\<lbrakk> len_of TYPE('c) \<le> len_of TYPE('b) \<rbrakk> \<Longrightarrow>
        (ucast (ucast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = ucast a"
  "\<lbrakk> len_of TYPE('a) \<le> len_of TYPE('b) \<rbrakk> \<Longrightarrow>
     (ucast (ucast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = ucast a"
  "\<lbrakk> len_of TYPE('a) \<le> len_of TYPE('b) \<rbrakk> \<Longrightarrow>
            (scast (scast (a :: 'a::len word) :: 'b::len word) :: 'c::len word) = scast a"
  by (auto simp: is_up is_down
      scast_ucast_1 scast_ucast_3 scast_ucast_4
      ucast_scast_1 ucast_scast_3 ucast_scast_4
      scast_scast_a scast_scast_b
      ucast_ucast_a ucast_ucast_b)

declare len_signed [L2opt]

lemmas [L2opt] = zero_sle_ucast_up

lemma zero_sle_ucast_WORD_MAX [L2opt]:
  "(0 <=s ((ucast (b::('a::len) word)) :: ('a::len) signed word))
                = (uint b \<le> WORD_MAX (TYPE('a)))"
  by (clarsimp simp: WORD_MAX_def zero_sle_ucast)

lemmas [L2opt] =
    is_up is_down unat_ucast_upcast sint_ucast_eq_uint

lemmas [L2opt] =
    ucast_down_add scast_down_add
    ucast_down_minus scast_down_minus
    ucast_down_mult scast_down_mult

lemma eq_trivI: "x = y \<Longrightarrow> x = y"
  by simp
(*
 * Setup word abstraction rules.
 *)


(* Common word abstraction rules. *)

lemmas [word_abs] =
  corresTA_L2_gets
  corresTA_L2_modify
  corresTA_L2_throw
  corresTA_L2_skip
  corresTA_L2_fail
  corresTA_L2_seq
  corresTA_L2_seq_unit
  corresTA_L2_catch
  corresTA_L2_try'
  (*corresTA_return*)
  corresTA_L2_while
  corresTA_L2_guard
  corresTA_L2_guarded_simple
  corresTA_L2_spec
  corresTA_L2_assume
  corresTA_L2_condition
  corresTA_L2_unknown
  corresTA_case_prod
  corresTA_L2_call_exec_concrete'
  corresTA_L2_call_exec_concrete
  corresTA_L2_call_exec_abstract'
  corresTA_L2_call_exec_abstract
  corresTA_L2_call'
  corresTA_L2_call
  corresTA_call_L1

lemmas [word_abs] =
  abstract_val_tuple
  abstract_val_Inl
  abstract_val_Inr
  abstract_val_conj
  abstract_val_disj
  abstract_val_case_prod
  abstract_val_trivial
  abstract_val_of_int
  abstract_val_of_nat
  abstract_val_call_L1_args

(* follow the convention that later rules are prefered *)
lemmas abs_var_rules = 
  abstract_val_call_L1_arg
  abstract_val_abs_var_sint_unat
  abstract_val_abs_var_uint_unat
  abstract_val_abs_var_give_up
  abstract_val_abs_var_concretise
  abstract_val_abs_var

lemmas word_abs_base [word_abs] =
  valid_typ_abs_fn_id [where 'a="'a::c_type"]
  valid_typ_abs_fn_id [where 'a="bool"]
  valid_typ_abs_fn_id [where 'a="'gx c_exntype"]
  valid_typ_abs_fn_tuple_split
  valid_typ_abs_fn_tuple
  valid_typ_abs_fn_sum
  valid_typ_abs_fn_unit
  valid_typ_abs_fn_sint
  valid_typ_abs_fn_unat
  len_of_word_comparisons

(*
 * Signed word abstraction rules: 'a sword \<rightarrow> int
 *)

lemmas word_abs_sword =
  abstract_val_signed_ops
  abstract_val_scast
  abstract_val_scast_upcast
  abstract_val_scast_downcast
  abstract_val_unwrap [where f=sint]
  introduce_typ_abs_fn [where f="sint :: (sword64 \<Rightarrow> int)"]
  introduce_typ_abs_fn [where f="sint :: (sword32 \<Rightarrow> int)"]
  introduce_typ_abs_fn [where f="sint :: (sword16 \<Rightarrow> int)"]
  introduce_typ_abs_fn [where f="sint :: (sword8 \<Rightarrow> int)"]

(*
 * Unsigned word abstraction rules: 'a word \<rightarrow> nat
 *)

lemmas word_abs_word =
  abstract_val_unsigned_ops
  abstract_val_uint
  abstract_val_ucast
  abstract_val_ucast_upcast
  abstract_val_ucast_downcast
  abstract_val_unwrap [where f=unat]
  introduce_typ_abs_fn [where f="unat :: (word64 \<Rightarrow> nat)"]
  introduce_typ_abs_fn [where f="unat :: (word32 \<Rightarrow> nat)"]
  introduce_typ_abs_fn [where f="unat :: (word16 \<Rightarrow> nat)"]
  introduce_typ_abs_fn [where f="unat :: (word8 \<Rightarrow> nat)"]

(* 'a \<rightarrow> 'a *)
lemmas word_abs_default =
  introduce_typ_abs_fn [where f="id :: ('a::c_type \<Rightarrow> 'a)"]
  introduce_typ_abs_fn [where f="id :: (bool \<Rightarrow> bool)"]
  introduce_typ_abs_fn [where f="id :: ('gx c_exntype \<Rightarrow> 'gx c_exntype)"]
  introduce_typ_abs_fn [where f="id :: (unit \<Rightarrow> unit)"]
  introduce_typ_abs_fn_tuple
  introduce_typ_abs_fn_sum

thm word_abs

lemma int_bounds_to_nat_boundsF: "(n::int) < numeral B \<Longrightarrow> 0 \<le> n \<Longrightarrow> nat n < numeral B"
  by (simp add: nat_less_iff)

lemma int_bounds_one_to_nat: "(n::int) < 1 \<Longrightarrow> 0 \<le> n \<Longrightarrow> nat n = 0"
  by (simp add: nat_less_iff)

lemma id_map_prod_unfold: "id = map_prod id id"
  by (simp add: prod.map_id0)

lemma id_tuple_unfold: "id = (\<lambda>(x, y). (id x, id y))"
  by simp

end
