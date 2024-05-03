(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)
theory SignedWordAbsHeap
imports
  AutoCorres2_Main.AutoCorres_Main
begin

text \<open>
  Regression test for signed word abs on the lifted heap.
  Jira issue ID: VER-1112

  For the gory details, see the comment for the function
  WordAbstract.mk_sword_heap_get_rule.
\<close>

install_C_file "signed_word_abs_heap.c"

autocorres [
    ts_rules=nondet,
    unsigned_word_abs=foo bar
  ]
  "signed_word_abs_heap.c"

context signed_word_abs_heap_all_impl begin
text \<open>
  Previously, lifted word heap accesses would always be translated to
  unsigned @{type nat}s, instead of signed @{typ int}s where appropriate.
\<close>
thm foo'_def bar'_def

lemma bar_123_456:
  "heap_w32 s p = 123 \<Longrightarrow> ptr_valid (heap_typing s) p \<Longrightarrow>
   bar' (ptr_coerce p) 456 \<bullet> s
   \<lbrace>\<lambda>r s. r = Result 579 \<and> heap_w32 s p = 579\<rbrace>"
  unfolding bar'_def
  by (runs_to_vcg \<open>simp add: fun_upd_apply INT_MAX_def\<close>)


text \<open>
  Previously, this was unprovable.
\<close>
lemma bar_n123_456:
  " heap_w32 s p = -123 \<Longrightarrow> ptr_valid (heap_typing s) p \<Longrightarrow>
   bar' (ptr_coerce p) 456 \<bullet> s
   \<lbrace>\<lambda>r s. r = Result 333 \<and> heap_w32 s p = 333\<rbrace>"
  unfolding bar'_def
  by (runs_to_vcg \<open>simp add: fun_upd_apply INT_MAX_def\<close>)

end

end
