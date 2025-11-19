(*
 * Copyright (c) 2023 Apple Inc. All rights reserved. 
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)


(* FIXME 

Remove the corres_admissible_mcont rules, unused.
*)



theory fnptr_enum0
  imports AutoCorres2_Main.AutoCorres_Main
begin


declare [[ML_print_depth =1000, c_parser_feedback_level=0]]
install_C_file "fnptr_enum0.c"

thm foo1_body_def
thm foo2_body_def
thm worker_body_def

text \<open>\<close>
context fnptr_enum0_global_addresses
begin
thm fun_ptr_map_of_default_eqs
end

context fnptr_enum0_global_addresses
begin
thm fun_ptr_map_of_default_eqs
end

ML_val \<open>
val call_info = ProgramAnalysis.get_callgraph (the (CalculateState.get_csenv @{theory} "fnptr_enum0.c"))
val referenced = ProgramAnalysis.get_referenced_funs (the (CalculateState.get_csenv @{theory} "fnptr_enum0.c"))
val potential_method_callees = ProgramAnalysis.potential_method_callees  (the (CalculateState.get_csenv @{theory} "fnptr_enum0.c"))
val method_caller = ProgramAnalysis.method_callers  (the (CalculateState.get_csenv @{theory} "fnptr_enum0.c"))
val method_caller' = ProgramAnalysis.method_callers_via_fun_ptr_param (the (CalculateState.get_csenv @{theory} "fnptr_enum0.c")) 
val fun_ptr_caller = ProgramAnalysis.callers_via_fun_ptr_param (the (CalculateState.get_csenv @{theory} "fnptr_enum0.c")) 
val fun_ptr_callees_call_select = ProgramAnalysis.get_fun_ptr_callees (the (CalculateState.get_csenv @{theory} "fnptr_enum0.c")) "call_select" 
val fun_ptr_calls_call_select = ProgramAnalysis.get_fun_ptr_calls (the (CalculateState.get_csenv @{theory} "fnptr_enum0.c")) "call_select" 
val funs_with_fun_ptr_calls = ProgramAnalysis.functions_with_fun_ptr_calls (the (CalculateState.get_csenv @{theory} "fnptr_enum0.c"))
val functions_with_local_fun_ptr_calls = ProgramAnalysis.functions_with_local_fun_ptr_calls (the (CalculateState.get_csenv @{theory} "fnptr_enum0.c"))
val method_types = ProgramAnalysis.method_types  (the (CalculateState.get_csenv @{theory} "fnptr_enum0.c"))

val all_method_callers =  ProgramAnalysis.get_final_callers (the (CalculateState.get_csenv @{theory} "fnptr_enum0.c")) method_caller
val addressed_funs = ProgramAnalysis.get_all_addressed_funs (the (CalculateState.get_csenv @{theory} "fnptr_enum0.c"))

val fninfo = ProgramAnalysis.get_fninfo  (the (CalculateState.get_csenv @{theory} "fnptr_enum0.c"))
val fun_ptr_params = ProgramAnalysis.get_fun_ptr_params  (the (CalculateState.get_csenv @{theory} "fnptr_enum0.c"))
val callers_via_local_fun_ptr_param = ProgramAnalysis.callers_via_local_fun_ptr_param (the (CalculateState.get_csenv @{theory} "fnptr_enum0.c"))

val fun_ptr_parmas_worker = Symtab.lookup (ProgramAnalysis.get_fun_ptr_params  (the (CalculateState.get_csenv @{theory} "fnptr_enum0.c"))) "worker"
val mc_worker = ProgramAnalysis.method_callers_via_fun_ptr_param_of (the (CalculateState.get_csenv @{theory} "fnptr_enum0.c")) "worker"
val c_worker = ProgramAnalysis.callers_via_fun_ptr_param_of (the (CalculateState.get_csenv @{theory} "fnptr_enum0.c")) "worker"

\<close>

init-autocorres [single_threaded,in_out_parameters = worker (), ts_force_known_functions = option] "fnptr_enum0.c"

thm corres_admissible
thm gfp_lub_fun gfp_le_fun

autocorres[in_out_globals = call_get_obj glob_handler1 glob_handler2, single_threaded] "fnptr_enum0.c"

thm ts_def
thm \<P>_defs
thm final_defs
context fnptr_enum0_global_addresses
begin

thm fun_ptr_simps
thm fun_ptr_undefined_simps
thm ac_corres
thm ts_def
end

end

