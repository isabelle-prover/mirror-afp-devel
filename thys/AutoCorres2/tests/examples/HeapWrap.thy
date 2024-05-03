(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Simple test cases for heap_abs_syntax feature.
 * JIRA issue ID: VER-356
 *)
theory HeapWrap
imports "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "heap_wrap.c"
autocorres [heap_abs_syntax] "heap_wrap.c"

context heap_wrap_all_impl begin
thm f1'_def f2'_def f3'_def f4'_def f5'_def f6'_def f7'_def f8'_def
end

context heap_wrap_simpl
begin

(* overloaded syntax is not scalable *)
term "s[p\<rightarrow>right := s[q]\<rightarrow>left][q]\<rightarrow>right = s[r] +\<^sub>p uint (s[t]\<rightarrow>x) \<and>
      s[p\<rightarrow>right := s[q]\<rightarrow>left] = s[q\<rightarrow>left := s[p]\<rightarrow>right] \<and>
      s[t]\<rightarrow>p = s[q]\<rightarrow>p \<and>
      s[ptr_coerce (s[p]\<rightarrow>p) :: 32 word ptr] = ucast (s[q]\<rightarrow>x)"

end

end
