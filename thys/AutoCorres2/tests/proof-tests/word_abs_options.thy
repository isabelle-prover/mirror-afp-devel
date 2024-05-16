(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory word_abs_options imports "AutoCorres2_Main.AutoCorres_Main" begin

install_C_file "word_abs_options.c"

autocorres [
  ts_rules = nondet,
  unsigned_word_abs = usum2, no_signed_word_abs = isum1
  ] "word_abs_options.c"

context word_abs_options_all_impl begin

lemma "isum1' (a :: sword32) (b :: sword32) \<bullet> s ?\<lbrace> \<lambda>r _. r = Result (a + b) \<rbrace>"
  unfolding isum1'_def
  apply runs_to_vcg
  done

lemma "isum2' (a :: int) (b :: int) \<bullet> s ?\<lbrace> \<lambda>r _. r = Result (a + b) \<rbrace>"
  unfolding isum2'_def
  apply runs_to_vcg
  done

lemma "usum1' (a :: word32) (b :: word32) \<bullet> s ?\<lbrace> \<lambda>r _. r = Result (a + b) \<rbrace>"
  unfolding usum1'_def
  apply runs_to_vcg
  done

lemma "usum2' (a :: nat) (b :: nat) \<bullet> s ?\<lbrace> \<lambda>r _. r = Result (a + b) \<rbrace>"
  unfolding usum2'_def
  apply runs_to_vcg
  done

end

end
