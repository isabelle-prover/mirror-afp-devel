(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory WordAbs
imports "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "word_abs.c"
autocorres
  [ (* signed_word_abs is implicit; these are the functions that would be abstracted: *)
    (*signed_word_abs =
        S_add_S S_sub_S S_mul_S S_div_S S_mod_S neg_S
        S_and_S S_or_S S_xor_S not_S
        U_shiftl_U_abs_S U_shiftr_U_abs_S U_shiftl_S_abs_S U_shiftr_S_abs_S
        S_shiftl_U_abs_S S_shiftr_U_abs_S S_shiftl_S_abs_S S_shiftr_S_abs_S
        U_shiftl_U_abs_US U_shiftr_U_abs_US U_shiftl_S_abs_US U_shiftr_S_abs_US
        S_shiftl_U_abs_US S_shiftr_U_abs_US S_shiftl_S_abs_US S_shiftr_S_abs_US
  ,*) no_signed_word_abs =
        U_shiftl_U_no_abs U_shiftr_U_no_abs U_shiftl_S_no_abs U_shiftr_S_no_abs
        S_shiftl_U_no_abs S_shiftr_U_no_abs S_shiftl_S_no_abs S_shiftr_S_no_abs
        U_shiftl_U_abs_U U_shiftr_U_abs_U U_shiftl_S_abs_U U_shiftr_S_abs_U
        S_shiftl_U_abs_U S_shiftr_U_abs_U S_shiftl_S_abs_U S_shiftr_S_abs_U
  , unsigned_word_abs =
        ver366
        U_add_U U_sub_U U_mul_U U_div_U U_mod_U neg_U
        U_and_U U_or_U U_xor_U not_U
        U_shiftl_U_abs_U U_shiftr_U_abs_U U_shiftl_S_abs_U U_shiftr_S_abs_U
        S_shiftl_U_abs_U S_shiftr_U_abs_U S_shiftl_S_abs_U S_shiftr_S_abs_U
        U_shiftl_U_abs_US U_shiftr_U_abs_US U_shiftl_S_abs_US U_shiftr_S_abs_US
        S_shiftl_U_abs_US S_shiftr_U_abs_US S_shiftl_S_abs_US S_shiftr_S_abs_US
  , ts_rules = nondet
] "word_abs.c"

context word_abs_all_impl begin


lemma "(ver366' 0) \<bullet> s \<lbrace> \<lambda>r _. r = Result 0\<rbrace>"
  unfolding ver366'_def
  by (runs_to_vcg)


lemma "(ver366' UINT_MAX) \<bullet> s \<lbrace>\<lambda>r _. r = Result (UINT_MAX - 1)\<rbrace>"
  unfolding ver366'_def
  by (runs_to_vcg)

section \<open>Arithmetic ops\<close>
thm S_add_S'_def S_sub_S'_def S_mul_S'_def S_div_S'_def S_mod_S'_def neg_S'_def
    U_add_U'_def U_sub_U'_def U_mul_U'_def U_div_U'_def U_mod_U'_def neg_U'_def

lemma "x + y < INT_MIN \<or> x + y > INT_MAX \<Longrightarrow> \<not> (succeeds (S_add_S' (x::int) (y::int)) s)"
  unfolding S_add_S'_def runs_to_def_old
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def INT_MIN_def INT_MAX_def)

lemma "INT_MIN \<le> x + y \<Longrightarrow> x + y \<le> INT_MAX \<Longrightarrow> P s \<Longrightarrow>
         S_add_S' (x::int) (y::int) \<bullet> s
       \<lbrace>\<lambda>r s. r = Result (x + y) \<and> P s\<rbrace>"
  unfolding S_add_S'_def 
  by (runs_to_vcg \<open>simp add: INT_MIN_def INT_MAX_def\<close>)

lemma "x - y < INT_MIN \<or> x - y > INT_MAX \<Longrightarrow> \<not> succeeds (S_sub_S' (x::int) (y::int)) s"
  unfolding S_sub_S'_def runs_to_def_old
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def INT_MIN_def INT_MAX_def)

lemma "INT_MIN \<le> x - y \<Longrightarrow> x - y \<le> INT_MAX \<Longrightarrow> P s \<Longrightarrow>
         S_sub_S' (x::int) (y::int) \<bullet> s
       \<lbrace>\<lambda>r s. r = Result (x - y) \<and> P s\<rbrace>"
  unfolding S_sub_S'_def
  by (runs_to_vcg \<open>simp add: INT_MIN_def INT_MAX_def\<close>)

lemma "x * y < INT_MIN \<or> x * y > INT_MAX \<Longrightarrow> \<not> succeeds (S_mul_S' (x::int) (y::int)) s"
  unfolding S_mul_S'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def INT_MIN_def INT_MAX_def)

lemma "INT_MIN \<le> x * y \<Longrightarrow> x * y \<le> INT_MAX \<Longrightarrow> P s \<Longrightarrow>
         S_mul_S' (x::int) (y::int) \<bullet> s
       \<lbrace>\<lambda>r s. r = Result (x * y) \<and> P s\<rbrace>"
  unfolding S_mul_S'_def
  by (runs_to_vcg \<open>simp add: INT_MIN_def INT_MAX_def\<close>)


lemma "y = 0 \<or> x sdiv y < INT_MIN \<or> x sdiv y > INT_MAX \<Longrightarrow> \<not> succeeds (S_div_S' (x::int) (y::int)) s"
  unfolding S_div_S'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def INT_MIN_def INT_MAX_def)

lemma "y \<noteq> 0 \<and> INT_MIN \<le> x sdiv y \<Longrightarrow> x sdiv y \<le> INT_MAX \<Longrightarrow> P s \<Longrightarrow>
         S_div_S' (x::int) (y::int) \<bullet> s
       \<lbrace>\<lambda>r s. r = Result (x sdiv y) \<and> P s\<rbrace>"
  unfolding S_div_S'_def
  by (runs_to_vcg \<open>simp add: INT_MIN_def INT_MAX_def\<close>)

lemma "y = 0 \<or> x smod y < INT_MIN \<or> x smod y > INT_MAX \<Longrightarrow> \<not> succeeds (S_mod_S' (x::int) (y::int)) s"
  unfolding S_mod_S'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def INT_MIN_def INT_MAX_def)

lemma "y \<noteq> 0 \<and> INT_MIN \<le> x smod y \<Longrightarrow> x smod y \<le> INT_MAX \<Longrightarrow> P s \<Longrightarrow>
         S_mod_S' (x::int) (y::int) \<bullet> s
       \<lbrace>\<lambda>r s. r = Result (x smod y) \<and> P s\<rbrace>"
  unfolding S_mod_S'_def
  by (runs_to_vcg \<open>simp add: INT_MIN_def INT_MAX_def\<close>)

lemma "x \<le> INT_MIN \<or> x > -INT_MIN \<Longrightarrow> \<not> succeeds (neg_S' (x::int)) s"
  unfolding neg_S'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def INT_MIN_def INT_MAX_def)

lemma "INT_MIN < x \<Longrightarrow> x \<le> -INT_MIN \<Longrightarrow> P s \<Longrightarrow> 
  neg_S' (x::int) \<bullet> s \<lbrace>\<lambda>r s. r = Result (-x) \<and> P s\<rbrace>"
  unfolding neg_S'_def
  by (runs_to_vcg \<open>simp add: INT_MIN_def INT_MAX_def\<close>)

lemma "x + y > UINT_MAX \<Longrightarrow> \<not> succeeds (U_add_U' (x::nat) (y::nat)) s"
  unfolding U_add_U'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def UINT_MAX_def)

lemma "x + y \<le> UINT_MAX \<Longrightarrow> P s \<Longrightarrow>
         U_add_U' (x::nat) (y::nat) \<bullet> s
       \<lbrace>\<lambda>r s. r = Result (x + y) \<and> P s\<rbrace>"
  unfolding U_add_U'_def
  by (runs_to_vcg \<open>simp add: UINT_MAX_def\<close>)

lemma "x < y \<Longrightarrow> \<not> succeeds (U_sub_U' (x::nat) (y::nat)) s"
  unfolding U_sub_U'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "x \<ge> y \<Longrightarrow> P s \<Longrightarrow>
         U_sub_U' (x::nat) (y::nat) \<bullet> s
       \<lbrace>\<lambda>r s. r = Result (x - y) \<and> P s\<rbrace>"
  unfolding U_sub_U'_def
  by (runs_to_vcg)

lemma "x * y > UINT_MAX \<Longrightarrow> \<not> succeeds (U_mul_U' (x::nat) (y::nat)) s"
  unfolding U_mul_U'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "x * y \<le> UINT_MAX \<Longrightarrow> P s \<Longrightarrow>
         U_mul_U' (x::nat) (y::nat) \<bullet> s
       \<lbrace>\<lambda>r s. r = Result (x * y) \<and> P s\<rbrace>"
  unfolding U_mul_U'_def
  by (runs_to_vcg \<open>simp add: UINT_MAX_def\<close>)

lemma "y = 0 \<Longrightarrow> \<not> succeeds (U_div_U' (x::nat) (y::nat)) s"
  unfolding U_div_U'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "y \<noteq> 0 \<Longrightarrow> P s \<Longrightarrow>
         U_div_U' (x::nat) (y::nat) \<bullet> s
       \<lbrace>\<lambda>r s. r = Result (x div y) \<and> P s\<rbrace>"
  unfolding U_div_U'_def
  by (runs_to_vcg \<open>simp add: UINT_MAX_def\<close>)

lemma "y = 0 \<Longrightarrow> \<not> succeeds (U_mod_U' (x::nat) (y::nat)) s"
  unfolding U_mod_U'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "y \<noteq> 0 \<Longrightarrow> P s \<Longrightarrow>
         U_mod_U' (x::nat) (y::nat) \<bullet> s
       \<lbrace>\<lambda>r s. r = Result (x mod y) \<and> P s\<rbrace>"
  unfolding U_mod_U'_def
  by (runs_to_vcg \<open>simp add: UINT_MAX_def\<close>)

lemma "P s \<Longrightarrow> neg_U' (x::nat) \<bullet> s \<lbrace>\<lambda>r s. r = Result (if x = 0 then 0 else Suc UINT_MAX - x) \<and> P s\<rbrace>"
  unfolding neg_U'_def 
  by (runs_to_vcg \<open>simp add: UINT_MAX_def\<close>)

section \<open>Bitwise ops\<close>

thm S_and_S'_def S_or_S'_def S_xor_S'_def not_S'_def
    U_and_U'_def U_or_U'_def U_xor_U'_def not_U'_def

lemma "P s \<Longrightarrow> S_and_S' (x::int) (y::int) \<bullet> s \<lbrace>\<lambda>r s. r = Result (x AND y) \<and> P s\<rbrace>"
  unfolding S_and_S'_def by runs_to_vcg

lemma "P s \<Longrightarrow> S_or_S' (x::int) (y::int) \<bullet> s \<lbrace>\<lambda>r s. r = Result (x OR y) \<and> P s\<rbrace>"
  unfolding S_or_S'_def by runs_to_vcg

lemma "P s \<Longrightarrow> S_xor_S' (x::int) (y::int) \<bullet> s \<lbrace>\<lambda>r s. r = Result (x XOR y) \<and> P s\<rbrace>"
  unfolding S_xor_S'_def by runs_to_vcg

lemma "P s \<Longrightarrow> not_S' (x::int) \<bullet> s \<lbrace>\<lambda>r s. r = Result (NOT x) \<and> P s\<rbrace>"
  unfolding not_S'_def by runs_to_vcg

lemma "P s \<Longrightarrow> U_and_U' (x::nat) (y::nat) \<bullet> s \<lbrace>\<lambda>r s. r = Result (x AND y) \<and> P s\<rbrace>"
  unfolding U_and_U'_def by runs_to_vcg

lemma "P s \<Longrightarrow> U_or_U' (x::nat) (y::nat) \<bullet> s \<lbrace>\<lambda>r s. r = Result (x OR y) \<and> P s\<rbrace>"
  unfolding U_or_U'_def by runs_to_vcg

lemma "P s \<Longrightarrow> U_xor_U' (x::nat) (y::nat) \<bullet> s \<lbrace>\<lambda>r s. r = Result (x XOR y) \<and> P s\<rbrace>"
  unfolding U_xor_U'_def by runs_to_vcg

lemma "P s \<Longrightarrow> not_U' (x::nat) \<bullet> s \<lbrace>\<lambda>r s. r = Result (UINT_MAX - x) \<and> P s\<rbrace>"
  unfolding not_U'_def by runs_to_vcg

section \<open>Left shifts\<close>

thm U_shiftl_U_abs_US'_def U_shiftr_U_abs_US'_def U_shiftl_S_abs_US'_def U_shiftr_S_abs_US'_def
    S_shiftl_U_abs_US'_def S_shiftr_U_abs_US'_def S_shiftl_S_abs_US'_def S_shiftr_S_abs_US'_def
thm U_shiftl_U_abs_U'_def U_shiftr_U_abs_U'_def U_shiftl_S_abs_U'_def U_shiftr_S_abs_U'_def
    S_shiftl_U_abs_U'_def S_shiftr_U_abs_U'_def S_shiftl_S_abs_U'_def S_shiftr_S_abs_U'_def
thm U_shiftl_U_abs_S'_def U_shiftr_U_abs_S'_def U_shiftl_S_abs_S'_def U_shiftr_S_abs_S'_def
    S_shiftl_U_abs_S'_def S_shiftr_U_abs_S'_def S_shiftl_S_abs_S'_def S_shiftr_S_abs_S'_def
thm U_shiftl_U_no_abs'_def U_shiftr_U_no_abs'_def U_shiftl_S_no_abs'_def U_shiftr_S_no_abs'_def
    S_shiftl_U_no_abs'_def S_shiftr_U_no_abs'_def S_shiftl_S_no_abs'_def S_shiftr_S_no_abs'_def

subsection \<open>@{text U_shiftl_U}\<close>

lemma "n \<ge> 32 \<Longrightarrow> \<not> succeeds (U_shiftl_U_abs_US' (x :: nat) (n :: nat)) s"
  unfolding U_shiftl_U_abs_US'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n < 32 \<Longrightarrow> x << n \<le> UINT_MAX \<Longrightarrow>
         U_shiftl_U_abs_US' (x::nat) (n::nat) \<bullet> s
       \<lbrace>\<lambda>r s. r = Result (x << n)\<rbrace>"
  unfolding U_shiftl_U_abs_US'_def
  by (runs_to_vcg \<open>simp add: UINT_MAX_def\<close>)

lemma "n \<ge> 32 \<Longrightarrow> \<not> succeeds (U_shiftl_U_abs_U' (x :: nat) (n :: nat)) s"
  unfolding U_shiftl_U_abs_U'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n < 32 \<Longrightarrow> x << n \<le> UINT_MAX \<Longrightarrow>
         U_shiftl_U_abs_U' (x::nat) (n::nat) \<bullet> s
       \<lbrace>\<lambda>r s. r = Result (x << n)\<rbrace>"
  unfolding U_shiftl_U_abs_U'_def
  by (runs_to_vcg \<open>simp add: UINT_MAX_def\<close>)

lemma "n \<ge> 32 \<Longrightarrow> \<not> succeeds (U_shiftl_U_abs_S' (x :: word32) (n :: word32)) s"
  unfolding U_shiftl_U_abs_S'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n < 32 \<Longrightarrow>
         U_shiftl_U_abs_S' (x::word32) (n::word32) \<bullet> s
       \<lbrace>\<lambda>r s. r = Result (x << unat n)\<rbrace>"
  unfolding U_shiftl_U_abs_S'_def
  by (runs_to_vcg \<open>simp add: UINT_MAX_def\<close>)

lemma "n \<ge> 32 \<Longrightarrow> \<not> succeeds (U_shiftl_U_no_abs' (x :: word32) (n :: word32)) s"
  unfolding U_shiftl_U_no_abs'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n < 32 \<Longrightarrow>
         U_shiftl_U_no_abs' (x::word32) (n::word32) \<bullet> s
       \<lbrace>\<lambda>r s. r = Result (x << unat n)\<rbrace>"
  unfolding U_shiftl_U_no_abs'_def by runs_to_vcg

subsection \<open>@{text U_shiftl_S}\<close>

lemma "n < 0 \<Longrightarrow> \<not> succeeds (U_shiftl_S_abs_US' (x :: nat) (n :: int)) s"
  unfolding U_shiftl_S_abs_US'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n \<ge> 32 \<Longrightarrow> \<not> succeeds (U_shiftl_S_abs_US' (x :: nat) (n :: int)) s"
  unfolding U_shiftl_S_abs_US'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "x << nat n > UINT_MAX \<Longrightarrow> \<not> succeeds (U_shiftl_S_abs_US' (x :: nat) (n :: int)) s"
  unfolding U_shiftl_S_abs_US'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "0 \<le> n \<Longrightarrow> n < 32 \<Longrightarrow> x << nat n \<le> UINT_MAX \<Longrightarrow>
         U_shiftl_S_abs_US' (x::nat) (n::int) \<bullet> s
       \<lbrace>\<lambda>r s. r = Result (x << nat n)\<rbrace>"
  unfolding U_shiftl_S_abs_US'_def
  by (runs_to_vcg \<open>simp add: UINT_MAX_def\<close>)

lemma "n <s 0 \<Longrightarrow> \<not> succeeds (U_shiftl_S_abs_U' (x :: nat) (n :: sword32)) s"
  unfolding  U_shiftl_S_abs_U'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "32 <=s n \<Longrightarrow> \<not> succeeds (U_shiftl_S_abs_U' (x :: nat) (n :: sword32)) s"
  unfolding  U_shiftl_S_abs_U'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "x << unat n > UINT_MAX \<Longrightarrow> \<not> succeeds (U_shiftl_S_abs_U' (x :: nat) (n :: sword32)) s"
  unfolding  U_shiftl_S_abs_U'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def
      word_sless_alt word_sle_def nat_sint)

lemma "0 <=s n \<Longrightarrow> n <s 32 \<Longrightarrow> x << unat n \<le> UINT_MAX \<Longrightarrow>
         U_shiftl_S_abs_U' (x::nat) (n::sword32) \<bullet> s
       \<lbrace>\<lambda>r s. r = Result (x << unat n)\<rbrace>"
  unfolding  U_shiftl_S_abs_U'_def
  by (runs_to_vcg \<open>simp add: UINT_MAX_def  nat_sint word_sle_def word_sless_alt\<close>)

lemma "n < 0 \<Longrightarrow> \<not> succeeds (U_shiftl_S_abs_S' (x :: word32) (n :: int)) s"
  unfolding U_shiftl_S_abs_S'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n \<ge> 32 \<Longrightarrow> \<not> succeeds (U_shiftl_S_abs_S' (x :: word32) (n :: int)) s"
  unfolding U_shiftl_S_abs_S'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "0 \<le> n \<Longrightarrow> n < 32 \<Longrightarrow>
         U_shiftl_S_abs_S' (x::word32) (n::int) \<bullet> s
       \<lbrace>\<lambda>r s. r = Result (x << nat n)\<rbrace>"
  unfolding U_shiftl_S_abs_S'_def
  supply unsigned_of_int [simp del]
  by (runs_to_vcg \<open>simp add: UINT_MAX_def unat_of_int\<close>)

lemma "n <s 0 \<Longrightarrow> \<not> succeeds (U_shiftl_S_no_abs' (x :: word32) (n :: sword32)) s"
  unfolding U_shiftl_S_no_abs'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def word_sle_def word_sless_alt)

lemma "32 <=s n \<Longrightarrow> \<not> succeeds (U_shiftl_S_no_abs' (x :: word32) (n :: sword32)) s"
  unfolding U_shiftl_S_no_abs'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def word_sle_def word_sless_alt)

lemma "0 <=s n \<Longrightarrow> n <s 32 \<Longrightarrow>
         U_shiftl_S_no_abs' (x :: word32) (n :: sword32) \<bullet> s
       \<lbrace>\<lambda>r s. r = Result (x << unat n)\<rbrace>"
  unfolding U_shiftl_S_no_abs'_def by (runs_to_vcg \<open>simp add: UINT_MAX_def\<close>)

subsection \<open>@{text S_shiftl_U}\<close>

lemma "x < 0 \<Longrightarrow> \<not> succeeds (S_shiftl_U_abs_US' (x :: int) (n :: nat)) s"
  unfolding S_shiftl_U_abs_US'_def   
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n \<ge> 32 \<Longrightarrow> \<not> succeeds (S_shiftl_U_abs_US' (x :: int) (n :: nat)) s"
  unfolding S_shiftl_U_abs_US'_def   
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "x << nat (int n) > INT_MAX \<Longrightarrow> \<not> succeeds (S_shiftl_U_abs_US' (x :: int) (n :: nat)) s"
  unfolding S_shiftl_U_abs_US'_def   
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n < 32 \<Longrightarrow> 0 \<le> x \<Longrightarrow> x << nat (int n) \<le> INT_MAX \<Longrightarrow>
         S_shiftl_U_abs_US' (x::int) (n::nat) \<bullet> s
       \<lbrace>\<lambda>r s. r = Result (x << nat (int n))\<rbrace>"
  unfolding S_shiftl_U_abs_US'_def
  by (runs_to_vcg 
      \<open>simp add: INT_MAX_def shiftl_int_def flip: nat_mult_distrib nat_power_eq nat_numeral\<close>)

lemma "x <s 0 \<Longrightarrow> \<not> succeeds (S_shiftl_U_abs_U' (x :: sword32) (n :: nat)) s"
  unfolding S_shiftl_U_abs_U'_def   
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def word_sle_def word_sless_alt)

lemma "n \<ge> 32 \<Longrightarrow> \<not> succeeds (S_shiftl_U_abs_U' (x :: sword32) (n :: nat)) s"
  unfolding S_shiftl_U_abs_U'_def   
  apply (auto simp add: succeeds_def run_bind run_guard top_post_state_def word_sle_def word_sless_alt)
  oops \<comment> \<open>C parser issue: Jira VER-509\<close>
  thm S_shiftl_U_abs_U'_def
  thm int_unat_nonneg

lemma uint_sint_nonneg:
  "0 <=s (x :: 'a::len signed word) \<Longrightarrow> uint x = sint x"
  by (simp add: int_unat word_sle_msb_le sint_eq_uint)

lemma "sint x << n > INT_MAX \<Longrightarrow> \<not> succeeds (S_shiftl_U_abs_U' (x :: sword32) (n :: nat)) s"
  unfolding S_shiftl_U_abs_U'_def   
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def 
      shiftl_int_def INT_MAX_def nat_int_comparison(2) uint_sint_nonneg)

lemma "n < 32 \<Longrightarrow> 0 <=s x \<Longrightarrow> sint x << nat (int n) \<le> INT_MAX \<Longrightarrow>
         S_shiftl_U_abs_U' (x::sword32) (n::nat) \<bullet> s
       \<lbrace>\<lambda>r s. r = Result (x << nat (int n))\<rbrace>"
  unfolding  S_shiftl_U_abs_U'_def
  by (runs_to_vcg \<open>simp add: INT_MAX_def shiftl_int_def
                   nat_int_comparison(2) uint_sint_nonneg\<close>)

lemma "x < 0 \<Longrightarrow> \<not> succeeds (S_shiftl_U_abs_S' (x :: int) (n :: word32)) s"
  unfolding S_shiftl_U_abs_S'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n \<ge> 32 \<Longrightarrow> \<not> succeeds (S_shiftl_U_abs_S' (x :: int) (n :: word32)) s"
 unfolding S_shiftl_U_abs_S'_def
 by (auto simp add: succeeds_def run_bind run_guard top_post_state_def word_le_nat_alt)

lemma "x << unat n > INT_MAX \<Longrightarrow> \<not> succeeds (S_shiftl_U_abs_S' (x :: int) (n :: word32)) s"
  unfolding S_shiftl_U_abs_S'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def INT_MAX_def)

lemma "n < 32 \<Longrightarrow> 0 \<le> x \<Longrightarrow> x << unat n \<le> INT_MAX \<Longrightarrow>
         S_shiftl_U_abs_S' (x::int) (n::word32) \<bullet> s
       \<lbrace>\<lambda>r s. r = Result (x << unat n)\<rbrace>"
  unfolding S_shiftl_U_abs_S'_def 
  supply unsigned_of_nat [simp del] unsigned_of_nat [simp del]
  apply (runs_to_vcg)
  apply (simp_all add: INT_MAX_def shiftl_int_def
                      word_less_nat_alt)
  apply (simp flip: nat_mult_distrib nat_power_eq nat_numeral)
  done

lemma "x <s 0 \<Longrightarrow> \<not> succeeds (S_shiftl_U_no_abs' (x :: sword32) (n :: word32)) s"
  unfolding S_shiftl_U_no_abs'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def word_le_nat_alt)

lemma "n \<ge> 32 \<Longrightarrow> \<not> succeeds (S_shiftl_U_no_abs' (x :: sword32) (n :: word32)) s"
  unfolding S_shiftl_U_no_abs'_def
  apply (auto simp add: succeeds_def run_bind run_guard top_post_state_def)
  oops \<comment> \<open>C parser issue: Jira VER-509\<close>

lemma "sint x << unat n > INT_MAX \<Longrightarrow> \<not> succeeds (S_shiftl_U_no_abs' (x :: sword32) (n :: word32)) s"
  unfolding S_shiftl_U_no_abs'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def shiftl_int_def INT_MAX_def
                     nat_int_comparison(2) uint_sint_nonneg)

lemma "n < 32 \<Longrightarrow> 0 <=s x == sint x << unat n \<le> INT_MAX \<Longrightarrow>
         S_shiftl_U_no_abs' (x::sword32) (n::word32) \<bullet> s
       \<lbrace>\<lambda>r s. r = Result (x << unat n)\<rbrace>"
  unfolding S_shiftl_U_no_abs'_def
  apply (runs_to_vcg )
  apply (simp_all add:  INT_MAX_def shiftl_int_def
                   nat_int_comparison(2) uint_sint_nonneg )
   apply (smt (verit) Word.sint_0 Word_Lib_Sumo.word_sle_def not_exp_less_eq_0_int 
      uint_sint_nonneg zero_le_mult_iff)+
  done

subsection \<open>@{text S_shiftl_S}\<close>

lemma "x < 0 \<Longrightarrow> \<not> succeeds (S_shiftl_S_abs_US' (x :: int) (n :: int)) s"
  unfolding S_shiftl_S_abs_US'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n < 0 \<Longrightarrow> \<not> succeeds (S_shiftl_S_abs_US' (x :: int) (n :: int)) s"
  unfolding S_shiftl_S_abs_US'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "x << nat n > INT_MAX \<Longrightarrow> \<not> succeeds (S_shiftl_S_abs_US' (x :: int) (n :: int)) s"
  unfolding S_shiftl_S_abs_US'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n \<ge> 32 \<Longrightarrow> \<not> succeeds (S_shiftl_S_abs_US' (x :: int) (n :: int)) s"
  unfolding S_shiftl_S_abs_US'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "0 \<le> n \<Longrightarrow> n < 32 \<Longrightarrow> 0 \<le> x \<Longrightarrow> x << nat n \<le> INT_MAX \<Longrightarrow>
         S_shiftl_S_abs_US' (x::int) (n::int) \<bullet> s
       \<lbrace>\<lambda>r s. r = Result (x << nat n)\<rbrace>"
  supply unsigned_of_nat [simp del] unsigned_of_int [simp del]
  unfolding S_shiftl_S_abs_US'_def
  apply runs_to_vcg
  apply (simp_all add: INT_MAX_def shiftl_int_def)
  apply (simp flip: nat_mult_distrib nat_power_eq nat_numeral)
  done

lemma "x <s 0 \<Longrightarrow> \<not> succeeds (S_shiftl_S_abs_U' (x :: sword32) (n :: sword32)) s"
  unfolding S_shiftl_S_abs_U'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n <s 0 \<Longrightarrow> \<not> succeeds (S_shiftl_S_abs_U' (x :: sword32) (n :: sword32)) s"
  unfolding S_shiftl_S_abs_U'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "32 <=s n \<Longrightarrow> \<not> succeeds (S_shiftl_S_abs_U' (x :: sword32) (n :: sword32)) s"
  unfolding S_shiftl_S_abs_U'_def
  apply (auto simp add: succeeds_def run_bind run_guard top_post_state_def)
  oops \<comment> \<open>C parser issue: Jira VER-509\<close>

lemma "sint x << unat n > INT_MAX \<Longrightarrow> \<not> succeeds (S_shiftl_S_abs_U' (x :: sword32) (n :: sword32)) s"
  unfolding S_shiftl_S_abs_U'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def shiftl_int_def INT_MAX_def
                     nat_int_comparison(2) uint_sint_nonneg)

lemma "0 <=s n \<Longrightarrow> n <s 32 \<Longrightarrow> 0 <=s x \<Longrightarrow> sint x << unat n \<le> INT_MAX \<Longrightarrow>
         S_shiftl_S_abs_U' (x::sword32) (n::sword32) \<bullet> s
       \<lbrace>\<lambda>r s. r = Result (x << unat n)\<rbrace>"
  unfolding S_shiftl_S_abs_U'_def
  by (runs_to_vcg \<open>simp add: INT_MAX_def shiftl_int_def
                   nat_int_comparison(2) uint_sint_nonneg\<close>)
 
lemma "x < 0 \<Longrightarrow> \<not> succeeds (S_shiftl_S_abs_S' (x :: int) (n :: int)) s"
  unfolding S_shiftl_S_abs_S'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n < 0 \<Longrightarrow> \<not> succeeds (S_shiftl_S_abs_S' (x :: int) (n :: int)) s"
  unfolding S_shiftl_S_abs_S'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n \<ge> 32 \<Longrightarrow> \<not> succeeds (S_shiftl_S_abs_S' (x :: int) (n :: int)) s"
  unfolding S_shiftl_S_abs_S'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "x << nat n > INT_MAX \<Longrightarrow> \<not> succeeds (S_shiftl_S_abs_S' (x :: int) (n :: int)) s"
  unfolding S_shiftl_S_abs_S'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "0 \<le> n \<Longrightarrow> n < 32 \<Longrightarrow> 0 \<le> x \<and> x << n \<le> INT_MAX \<Longrightarrow>
         S_shiftl_S_abs_S' (x::int) (int n) \<bullet> s
       \<lbrace>\<lambda>r s. r = Result (x << nat (int n))\<rbrace>"
  supply unsigned_of_nat [simp del] unsigned_of_int [simp del]
  unfolding S_shiftl_S_abs_S'_def
  apply (runs_to_vcg)
  apply (simp_all add: INT_MAX_def shiftl_int_def)
  apply (simp flip: nat_mult_distrib nat_power_eq nat_numeral)
  done

lemma "x <s 0 \<Longrightarrow> \<not> succeeds (S_shiftl_S_no_abs' (x :: sword32) (n :: sword32)) s"
  unfolding S_shiftl_S_no_abs'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n <s 0 \<Longrightarrow> \<not> succeeds (S_shiftl_S_no_abs' (x :: sword32) (n :: sword32)) s"
  unfolding S_shiftl_S_no_abs'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "32 <=s n \<Longrightarrow> \<not> succeeds (S_shiftl_S_no_abs' (x :: sword32) (n :: sword32)) s"
  unfolding S_shiftl_S_no_abs'_def
  apply (auto simp add: succeeds_def run_bind run_guard top_post_state_def)
  oops \<comment> \<open>C parser issue: Jira VER-509\<close>

lemma "sint x << unat n > INT_MAX \<Longrightarrow> \<not> succeeds (S_shiftl_S_no_abs' (x :: sword32) (n :: sword32)) s"
  unfolding S_shiftl_S_no_abs'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def shiftl_int_def INT_MAX_def
                     nat_int_comparison(2) uint_sint_nonneg)

lemma "0 <=s n \<Longrightarrow> n <s 32 \<Longrightarrow> 0 <=s x \<Longrightarrow> sint x << unat n \<le> INT_MAX \<Longrightarrow>
         S_shiftl_S_no_abs' (x::sword32) (n::sword32) \<bullet> s
       \<lbrace>\<lambda>r s. r = Result (x << unat n)\<rbrace>"
  unfolding S_shiftl_S_no_abs'_def
  by (runs_to_vcg \<open>simp add: INT_MAX_def shiftl_int_def
                   nat_int_comparison(2) uint_sint_nonneg\<close>)

section \<open>Right shifts\<close>

subsection \<open>@{text U_shiftr_U}\<close>

lemma "n \<ge> 32 \<Longrightarrow> \<not> succeeds (U_shiftr_U_abs_US' (x :: nat) (n :: nat)) s"
  unfolding U_shiftr_U_abs_US'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n < 32 \<Longrightarrow> U_shiftr_U_abs_US' (x::nat) (n::nat) \<bullet> s \<lbrace>\<lambda>r s. r = Result (x >> n)\<rbrace>"
  unfolding U_shiftr_U_abs_US'_def by runs_to_vcg

lemma "n \<ge> 32 \<Longrightarrow> \<not> succeeds (U_shiftr_U_abs_U' (x :: nat) (n :: nat)) s"
  unfolding U_shiftr_U_abs_U'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n < 32 \<Longrightarrow> U_shiftr_U_abs_U' (x::nat) (n::nat) \<bullet> s \<lbrace>\<lambda>r s. r = Result (x >> n)\<rbrace>"
  unfolding U_shiftr_U_abs_U'_def by runs_to_vcg

lemma "n \<ge> 32 \<Longrightarrow> \<not> succeeds (U_shiftr_U_abs_S' (x :: word32) (n :: word32)) s"
  unfolding U_shiftr_U_abs_S'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n < 32 \<Longrightarrow> U_shiftr_U_abs_S' (x::word32) (n::word32) \<bullet> s \<lbrace>\<lambda>r s. r = Result (x >> unat n)\<rbrace>"
  unfolding U_shiftr_U_abs_S'_def by runs_to_vcg

lemma "n \<ge> 32 \<Longrightarrow> \<not> succeeds (U_shiftr_U_no_abs' (x :: word32) (n :: word32)) s"
  unfolding U_shiftr_U_no_abs'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n < 32 \<Longrightarrow> U_shiftr_U_no_abs' (x::word32) (n::word32) \<bullet> s \<lbrace>\<lambda>r s. r = Result (x >> unat n)\<rbrace>"
  unfolding U_shiftr_U_no_abs'_def by runs_to_vcg

subsection \<open>@{text U_shiftr_S}\<close>

lemma "n < 0 \<Longrightarrow> \<not> succeeds (U_shiftr_S_abs_US' (x :: nat) (n :: int)) s"
  unfolding U_shiftr_S_abs_US'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n \<ge> 32 \<Longrightarrow> \<not> succeeds (U_shiftr_S_abs_US' (x :: nat) (n :: int)) s"
  unfolding U_shiftr_S_abs_US'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "0 \<le> n \<Longrightarrow> n < 32 \<Longrightarrow> U_shiftr_S_abs_US' (x::nat) (n::int) \<bullet> s \<lbrace>\<lambda>r s. r = Result (x >> nat n)\<rbrace>"
  unfolding U_shiftr_S_abs_US'_def by runs_to_vcg

lemma "n <s 0 \<Longrightarrow> \<not> succeeds (U_shiftr_S_abs_U' (x :: nat) (n :: sword32)) s"
  unfolding U_shiftr_S_abs_U'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "32 <=s n \<Longrightarrow> \<not> succeeds (U_shiftr_S_abs_U' (x :: nat) (n :: sword32)) s"
  unfolding U_shiftr_S_abs_U'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "0 <=s n \<Longrightarrow> n <s 32 \<Longrightarrow> U_shiftr_S_abs_U' (x::nat) (n::sword32) \<bullet> s \<lbrace>\<lambda>r s. r = Result (x >> unat n)\<rbrace>"
  unfolding U_shiftr_S_abs_U'_def by (runs_to_vcg \<open>simp add: nat_sint word_sle_def word_sless_alt\<close>)

lemma "n < 0 \<Longrightarrow> \<not> succeeds (U_shiftr_S_abs_S' (x :: word32) (n :: int)) s"
  unfolding U_shiftr_S_abs_S'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n \<ge> 32 \<Longrightarrow> \<not> succeeds (U_shiftr_S_abs_S' (x :: word32) (n :: int)) s"
  unfolding U_shiftr_S_abs_S'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "0 \<le> n \<Longrightarrow> n < 32 \<Longrightarrow> U_shiftr_S_abs_S' (x::word32) (n::int) \<bullet> s \<lbrace>\<lambda>r s. r = Result (x >> nat n)\<rbrace>"
  unfolding U_shiftr_S_abs_S'_def by (runs_to_vcg)

lemma "n <s 0 \<Longrightarrow> \<not> succeeds (U_shiftr_S_no_abs' (x :: word32) (n :: sword32)) s"
  unfolding U_shiftr_S_no_abs'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "32 <=s n \<Longrightarrow> \<not> succeeds (U_shiftr_S_no_abs' (x :: word32) (n :: sword32)) s"
  unfolding U_shiftr_S_no_abs'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "0 <=s n \<Longrightarrow> n <s 32 \<Longrightarrow> 
  U_shiftr_S_no_abs' (x :: word32) (n :: sword32) \<bullet> s \<lbrace>\<lambda>r s. r = Result (x >> unat n)\<rbrace>"
  unfolding U_shiftr_S_no_abs'_def by runs_to_vcg

subsection \<open>@{text S_shiftr_U}\<close>

lemma "x < 0 \<Longrightarrow> \<not> succeeds (S_shiftr_U_abs_US' (x :: int) (n :: nat)) s"
  unfolding S_shiftr_U_abs_US'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n \<ge> 32 \<Longrightarrow> \<not> succeeds (S_shiftr_U_abs_US' (x :: int) (n :: nat)) s"
  unfolding S_shiftr_U_abs_US'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n < 32 \<Longrightarrow> 0 \<le> x \<Longrightarrow> S_shiftr_U_abs_US' (x::int) (n::nat) \<bullet> s \<lbrace>\<lambda>r s. r = Result (x >> nat (int n))\<rbrace>"
  unfolding S_shiftr_U_abs_US'_def by runs_to_vcg

lemma "x <s 0 \<Longrightarrow> \<not> succeeds (S_shiftr_U_abs_U' (x :: sword32) (n :: nat)) s"
  unfolding S_shiftr_U_abs_U'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n \<ge> 32 \<Longrightarrow> \<not> succeeds (S_shiftr_U_abs_U' (x :: sword32) (n :: nat)) s"
  unfolding S_shiftr_U_abs_U'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n < 32 \<Longrightarrow> 0 <=s x \<Longrightarrow> S_shiftr_U_abs_U' (x::sword32) (n::nat) \<bullet> s \<lbrace>\<lambda>r s. r = Result (x >> nat (int n))\<rbrace>"
  unfolding S_shiftr_U_abs_U'_def by runs_to_vcg

lemma "x < 0 \<Longrightarrow> \<not> succeeds (S_shiftr_U_abs_S' (x :: int) (n :: word32)) s"
  unfolding S_shiftr_U_abs_S'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n \<ge> 32 \<Longrightarrow> \<not> succeeds (S_shiftr_U_abs_S' (x :: int) (n :: word32)) s"
  unfolding S_shiftr_U_abs_S'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n < 32 \<Longrightarrow> 0 \<le> x \<Longrightarrow> 
  S_shiftr_U_abs_S' (x::int) (n::word32) \<bullet> s \<lbrace>\<lambda>r s. r = Result (x >> unat n)\<rbrace>"
  unfolding S_shiftr_U_abs_S'_def by runs_to_vcg

lemma "x <s 0 \<Longrightarrow> \<not> succeeds (S_shiftr_U_no_abs' (x :: sword32) (n :: word32)) s"
  unfolding S_shiftr_U_no_abs'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n \<ge> 32 \<Longrightarrow> \<not> succeeds (S_shiftr_U_no_abs' (x :: sword32) (n :: word32)) s"
  unfolding S_shiftr_U_no_abs'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n < 32 \<Longrightarrow> 0 <=s x \<Longrightarrow> 
  S_shiftr_U_no_abs' (x::sword32) (n::word32) \<bullet> s \<lbrace>\<lambda>r s. r = Result (x >> unat n)\<rbrace>"
  unfolding S_shiftr_U_no_abs'_def by runs_to_vcg

subsection \<open>@{text S_shiftr_S}\<close>

lemma "x < 0 \<Longrightarrow> \<not> succeeds (S_shiftr_S_abs_US' (x :: int) (n :: int)) s"
  unfolding S_shiftr_S_abs_US'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n < 0 \<Longrightarrow> \<not> succeeds (S_shiftr_S_abs_US' (x :: int) (n :: int)) s"
  unfolding S_shiftr_S_abs_US'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n \<ge> 32 \<Longrightarrow> \<not> succeeds (S_shiftr_S_abs_US' (x :: int) (n :: int)) s"
  unfolding S_shiftr_S_abs_US'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "0 \<le> n \<Longrightarrow> n < 32 \<Longrightarrow> 0 \<le> x \<Longrightarrow> 
  S_shiftr_S_abs_US' (x::int) (n::int) \<bullet> s \<lbrace>\<lambda>r s. r = Result (x >> nat n)\<rbrace>"
  unfolding S_shiftr_S_abs_US'_def by runs_to_vcg

lemma "x <s 0 \<Longrightarrow> \<not> succeeds (S_shiftr_S_abs_U' (x :: sword32) (n :: sword32)) s"
  unfolding S_shiftr_S_abs_U'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n <s 0 \<Longrightarrow> \<not> succeeds (S_shiftr_S_abs_U' (x :: sword32) (n :: sword32)) s"
  unfolding S_shiftr_S_abs_U'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "32 <=s n \<Longrightarrow> \<not> succeeds (S_shiftr_S_abs_U' (x :: sword32) (n :: sword32)) s"
  unfolding S_shiftr_S_abs_U'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "0 <=s n \<Longrightarrow> n <s 32 \<Longrightarrow> 0 <=s x \<Longrightarrow>
         S_shiftr_S_abs_U' (x::sword32) (n::sword32) \<bullet> s
       \<lbrace>\<lambda>r s. r = Result (x >> unat n)\<rbrace>"
  unfolding S_shiftr_S_abs_U'_def by runs_to_vcg

lemma "x < 0 \<Longrightarrow> \<not> succeeds (S_shiftr_S_abs_S' (x :: int) (n :: int)) s"
  unfolding S_shiftr_S_abs_S'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n < 0 \<Longrightarrow> \<not> succeeds (S_shiftr_S_abs_S' (x :: int) (n :: int)) s"
  unfolding S_shiftr_S_abs_S'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n \<ge> 32 \<Longrightarrow> \<not> succeeds (S_shiftr_S_abs_S' (x :: int) (n :: int)) s"
  unfolding S_shiftr_S_abs_S'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "0 \<le> n \<Longrightarrow> n < 32 \<Longrightarrow> 0 \<le> x \<Longrightarrow>
         S_shiftr_S_abs_S' (x::int) (n::int) \<bullet> s
       \<lbrace>\<lambda>r s. r = Result (x >> nat n)\<rbrace>"
  unfolding S_shiftr_S_abs_S'_def by runs_to_vcg

lemma "x <s 0 \<Longrightarrow> \<not> succeeds (S_shiftr_S_no_abs' (x :: sword32) (n :: sword32)) s"
  unfolding S_shiftr_S_no_abs'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "n <s 0 \<Longrightarrow> \<not> succeeds (S_shiftr_S_no_abs' (x :: sword32) (n :: sword32)) s"
  unfolding S_shiftr_S_no_abs'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "32 <=s n \<Longrightarrow> \<not> succeeds (S_shiftr_S_no_abs' (x :: sword32) (n :: sword32)) s"
  unfolding S_shiftr_S_no_abs'_def
  by (auto simp add: succeeds_def run_bind run_guard top_post_state_def)

lemma "0 <=s n \<Longrightarrow> n <s 32 \<Longrightarrow> 0 <=s x \<Longrightarrow>
         S_shiftr_S_no_abs' (x::sword32) (n::sword32) \<bullet> s
       \<lbrace>\<lambda>r s. r = Result (x >> unat n)\<rbrace>"
  unfolding S_shiftr_S_no_abs'_def by runs_to_vcg

end

end
