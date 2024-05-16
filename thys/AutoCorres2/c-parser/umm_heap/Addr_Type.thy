(*
 * Copyright (c) 2024 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Addr_Type
  imports 
    "ARM/Addr_Type_ARM"
    "ARM64/Addr_Type_ARM64"
    "ARM_HYP/Addr_Type_ARM_HYP"
    "RISCV64/Addr_Type_RISCV64"
    "X64/Addr_Type_X64"
begin

typ addr_bitsize
term array_outer_max_size_exponent
type_synonym addr = "addr_bitsize word"

declare addr_align_def[simp]
declare addr_bitsize_def[simp]

definition addr_card :: nat where
  "addr_card \<equiv> card (UNIV::addr set)"

lemma addr_card:
  "addr_card = 2^addr_bitsize"
  by (simp add: addr_card_def card_word)

lemma len_of_addr_card:
  "2 ^ len_of TYPE(addr_bitsize) = addr_card"
  by (simp add: addr_card)

lemma of_nat_addr_card [simp]:
  "of_nat addr_card = (0::addr)"
  by (simp add: addr_card)

end