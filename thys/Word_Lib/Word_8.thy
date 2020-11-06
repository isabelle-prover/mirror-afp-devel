(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section "Words of Length 8"

theory Word_8
imports
  Word_Lemmas
  Word_Syntax
begin

type_synonym word8 = "8 word"
lemma len8: "len_of (x :: 8 itself) = 8" by simp

end
