(*
 * Copyright (c) 2024 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory fnptr_groups
  imports 
    (*  AutoCorres2.CTranslation *)
    AutoCorres2_Main.AutoCorres_Main
  keywords
    "named_bindings" :: thy_decl
begin

install_C_file "fnptr_groups.c"

thm call_object_disp_local_body_def
thm call_obj1_body_def
thm 
  global_const_defs 
  global_const_array_selectors 
  global_const_non_array_selectors 
  global_const_selectors

context fnptr_groups_global_addresses
begin
thm fun_ptr_simps
thm fun_ptr_undefined_simps
thm fun_ptr_distinct
thm fun_ptr_map_of_default_eqs
thm fun_ptr_map_of_default_fallthrough_eqs
end

ML \<open>
C_Files.get_main @{theory}
\<close>
declare [[ML_print_depth = 1000]]
ML \<open>
val call_info = ProgramAnalysis.get_callgraph (the (CalculateState.get_csenv @{theory} "fnptr_groups.c")) |> Symtab.dest 
  |> map (apsnd Binaryset.listItems)

val fun_ptr_params = ProgramAnalysis.get_fun_ptr_params (the (CalculateState.get_csenv @{theory} "fnptr_groups.c"))
val functions_used_as_fun_ptr_params = ProgramAnalysis.get_functions_used_as_fun_ptr_params  (the (CalculateState.get_csenv @{theory} "fnptr_groups.c"))
val fun_ptr_calls = ProgramAnalysis.get_fun_ptr_calls  (the (CalculateState.get_csenv @{theory} "fnptr_groups.c"))
val addressed = ProgramAnalysis.get_addressed  (the (CalculateState.get_csenv @{theory} "fnptr_groups.c"))
val addressed_types = ProgramAnalysis.get_addressed_types (the (CalculateState.get_csenv @{theory} "fnptr_groups.c"));
val vars = ProgramAnalysis.get_vars  (the (CalculateState.get_csenv @{theory} "fnptr_groups.c"))
val method_approx = ProgramAnalysis.get_method_approx (the (CalculateState.get_csenv @{theory} "fnptr_groups.c"))
 |> Expr.CTypeSelectorsTab.dest |> map (apsnd Binaryset.listItems)
\<close>
ML \<open>
val approx_globals = ProgramAnalysis.approx_globals'  (the (CalculateState.get_csenv @{theory} "fnptr_groups.c"))
val method_approx = ProgramAnalysis.get_method_approx (the (CalculateState.get_csenv @{theory} "fnptr_groups.c"))
 |> Expr.CTypeSelectorsTab.dest |> map (apsnd Binaryset.listItems)
\<close>
ML \<open>
val senv = ProgramAnalysis.get_senv  (the (CalculateState.get_csenv @{theory} "fnptr_groups.c"))
  

\<close>
ML \<open>
val XX = ProgramAnalysis.approx_global_fun_ptrs_from_ty (the (CalculateState.get_csenv @{theory} "fnptr_groups.c"))
  (CType.StructTy "object_C", [Expr.Field "a_binop_C"])
\<close>

thm inc_body_def
thm call_unop_body_def
thm call_binop_body_def
thm call_obj_body_def
thm call_select_body_def

ML_val \<open>
val inc_info = fun_ptr_calls "inc"
val unop_info = fun_ptr_calls "call_unop"
\<close>


ML_val \<open>
val glob_binop_calls = fun_ptr_calls "glob_binop"
\<close>
ML_val \<open>
val glob_binop_calls = fun_ptr_calls "call_binop_disp1"
\<close>

ML_val \<open>
val select_calls = fun_ptr_calls "select"
\<close>

thm call_select_body_def
ML_val \<open>
val call_select_calls = fun_ptr_calls "call_select"
\<close>
ML_val \<open>
ProgramAnalysis.get_cliques (the (CalculateState.get_csenv @{theory} "fnptr_groups.c"))
\<close>

ML \<open>
val all_funs = ProgramAnalysis.get_functions  (the (CalculateState.get_csenv @{theory} "fnptr_groups.c"))
\<close>

declare [[ML_print_depth=10000]]
init-autocorres [single_threaded,
    in_out_parameters = inc_ptr_value(n:"in_out") and dec_ptr_value(n:"in_out")
     and add_ptr_value(n:"in_out", m: "in_out") and minus_ptr_value(n:"in_out", m: "in_out"),
    in_out_globals = call_unop_ptr_value glob_binop call_binop_disp1 add minus crazy call_obj call_binop
      call_object_disp_local
      call_select call_binop_param call_binop_param_from_obj call_binop_param1 call_binop_ptr
] "fnptr_groups.c"


autocorres [ts_force nondet = add] "fnptr_groups.c"

thm ts.call_binop_ptr'_def
thm call_binop_ptr'_def
thm ts.add'_def
thm add'_def
thm polish
thm global_const_defs
thm global_const_array_selectors
thm global_const_non_array_selectors
thm global_const_selectors
thm unchanged_typing
thm runs_to_vcg
thm top_fun_def
thm map_of_default.simps
thm ts_def
thm \<P>_defs
thm final_defs

context fnptr_groups_global_addresses
begin
thm l2_corres
thm l2_def
thm io_def
thm ts_def
thm fun_ptr_simps
thm fun_ptr_undefined_simps
thm fun_ptr_guards
thm fun_ptr_undefined_simps
thm fun_ptr_map_of_default_eqs
thm fun_ptr_map_of_default_fallthrough_eqs

end
end