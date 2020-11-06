(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section "Words of Length 16"

theory Word_16
imports
  Word_Lemmas
  Word_Syntax
begin

type_synonym word16 = "16 word"
lemma len16: "len_of (x :: 16 itself) = 16" by simp

end
