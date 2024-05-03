(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)


theory Addr_Type_ARM64
  imports 
    Target_Architecture 
    WordSetup
begin

if_architecture_context (ARM64)
begin
type_synonym addr_bitsize = "64"

definition addr_bitsize :: nat where "addr_bitsize \<equiv> 64"
definition addr_align :: nat where "addr_align \<equiv> 3"

abbreviation (input) "array_outer_max_size_exponent \<equiv> 26::nat"
abbreviation (input) "array_outer_max_count_exponent \<equiv> 20::nat"
abbreviation (input) "array_inner_max_size_exponent \<equiv> 6::nat"

abbreviation "word_bits \<equiv> Machine_Word_64_Basics.word_bits"
abbreviation "word_size \<equiv> Machine_Word_64_Basics.word_size"
abbreviation "word_size_bits \<equiv> Machine_Word_64_Basics.word_size_bits"
type_synonym char_c = "8 signed word"
end

end
