(*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory anonymous_nested_struct
  imports 
    AutoCorres2_Main.AutoCorres_Main
begin

declare [[ML_print_depth=1000]]

install_C_file "anonymous_nested_struct.c"

ML_val \<open>
val senv =  ProgramAnalysis.get_senv (the (CalculateState.get_csenv @{theory} "anonymous_nested_struct.c")) 
val clang_record_infos =  ProgramAnalysis.get_clang_record_infos (the (CalculateState.get_csenv @{theory} "anonymous_nested_struct.c")) 
val union_variants =  ProgramAnalysis.get_union_variants (the (CalculateState.get_csenv @{theory} "anonymous_nested_struct.c")) 
\<close>

context anonymous_nested_struct_global_addresses
begin
thm main1_body_def
thm foo1_body_def
thm foo2_body_def
thm bar_body_def
end

ML_val \<open>
val VV =  ProgramAnalysis.get_union_variants (the (CalculateState.get_csenv @{theory} "anonymous_nested_struct.c")) 
\<close>

ML_val \<open>
val record_info = RecursiveRecordPackage.get_info @{theory}
\<close>

ML_val \<open>
val AA = ProgramAnalysis.get_addressed_types (the (CalculateState.get_csenv @{theory} "anonymous_nested_struct.c")) 
        |> Absyn.CTypeTab.dest
\<close>


init-autocorres [ignore_addressable_fields_error] "anonymous_nested_struct.c"
autocorres [] "anonymous_nested_struct.c"

lemma actual_offsets:
  "bar' \<equiv> 2"\<comment> \<open>this should be \<open>2\<close>\<close>
  "foo1' \<equiv> 0"
  "foo2' \<equiv> 4"
  by (simp_all add: ts_def)

end