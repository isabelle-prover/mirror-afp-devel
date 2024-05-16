(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* License: BSD, terms see file ./LICENSE *)

theory Addr_Type_ARM_HYP
  imports 
    Target_Architecture
    WordSetup
begin

if_architecture_context (ARM_HYP)
begin
type_synonym addr_bitsize = "32"

definition addr_bitsize :: nat where "addr_bitsize \<equiv> 32"
definition addr_align :: nat where "addr_align \<equiv> 2"

abbreviation (input) "array_outer_max_size_exponent \<equiv> 19::nat"
abbreviation (input) "array_outer_max_count_exponent \<equiv> 13::nat"
abbreviation (input) "array_inner_max_size_exponent \<equiv> 6::nat"

abbreviation "word_bits \<equiv> Machine_Word_32_Basics.word_bits"
abbreviation "word_size \<equiv> Machine_Word_32_Basics.word_size"
abbreviation "word_size_bits \<equiv> Machine_Word_32_Basics.word_size_bits"
type_synonym char_c = "8 word"
end

end
