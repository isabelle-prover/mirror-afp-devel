(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Word_Mem_Encoding_ARM_HYP
  imports "../Vanilla32_Preliminaries"
begin

if_architecture_context (ARM_HYP)
begin
(* Little-endian encoding *)
definition
  word_tag :: "'a::len8 word itself \<Rightarrow> 'a word xtyp_info"
where
  "word_tag (w::'a::len8 word itself) \<equiv> 
    TypDesc (len_exp TYPE('a)) (TypScalar (len_of TYPE('a) div 8) (len_exp TYPE('a)) 
              \<lparr>field_access = \<lambda>v bs. (rev o word_rsplit) v, 
               field_update = \<lambda>bs v. (word_rcat (rev (take (len_of TYPE('a) div 8) bs))::'a::len8 word),
               field_sz = (len_of TYPE('a) div 8)\<rparr>)  
    (''word'' @  nat_to_bin_string (len_of TYPE('a)) )"
end

end
