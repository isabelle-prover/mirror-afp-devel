(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
 * Simple test for skip_heap_abs.
 *)
theory skip_heap_abs imports "AutoCorres2_Main.AutoCorres_Main" begin

install_C_file "skip_heap_abs.c"

ML_val \<open>
get_raw_interpretation_data (Context.Proof @{context})
\<close>
autocorres [skip_heap_abs] "skip_heap_abs.c"

ML_val \<open>
get_raw_interpretation_data (Context.Proof @{context})
\<close>

(* There should be no heap lift phase. *)

context skip_heap_abs_simpl 
begin
ML \<open>
val fn_infos = the (Symtab.lookup (AutoCorresData.FunctionInfo.get (Context.Proof @{context})) "skip_heap_abs");
assert (is_none (FunctionInfo.Phasetab.lookup fn_infos FunctionInfo.HL)) "skip_heap_abs failed";
\<close>
end

end
