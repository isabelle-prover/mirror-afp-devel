(*
 * Copyright (c) 2024 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory fnptr_no_heap_abs
imports AutoCorres2_Main.AutoCorres_Main
begin

declare [[allow_underscore_idents=true]]
declare [[c_parser_feedback_level= -1]]

install_C_file "fnptr_no_heap_abs.c"



init-autocorres [ignore_addressable_fields_error, 
    no_heap_abs = obj1_f1 obj2_f1 obj1_f2 obj1_f3] "fnptr_no_heap_abs.c"

autocorres [
    scope_depth=0, single_threaded,
    scope=obj1_f1 obj1_f2 obj1_f3, 
    (*no_heap_abs = obj1_f1 obj2_f1 obj1_f2 obj1_f3,*)
    ts_force nondet = obj1_f1 obj2_f1 obj1_f2 obj1_f3
  ] "fnptr_no_heap_abs.c"

autocorres [
    scope_depth=0, 
    scope=f1,
    ts_force nondet = f1
  ] "fnptr_no_heap_abs.c"

context fnptr_no_heap_abs_all_corres
begin
thm ts_def
end
end