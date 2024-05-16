(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)
theory pointers_to_locals0 imports  "AutoCorres2.CTranslation" 
begin



declare [[c_parser_feedback_level=10, ML_print_depth=1000, 
hoare_trace=0, hoare_use_call_tr'=false]]


install_C_file "pointers_to_locals0.c"


context call_inc_impl
begin
thm call_inc_body_def
end

context call_inc_array_impl
begin
thm call_inc_array_body_def
end

context call_inc_global_array_impl
begin
thm call_inc_global_array_body_def
end
context call_inc_buffer_impl
begin
thm call_inc_buffer_body_def
end

context call_inc_buffer_ptr_impl
begin
thm call_inc_buffer_ptr_body_def
end
thm c_guard_def
context call_inc_array_ptr_impl
begin
thm call_inc_array_ptr_body_def
end

context even_odd_impl
begin
thm even_body_def
thm odd_body_def
end

ML \<open>
val addressed = CalculateState.get_csenv @{theory} "pointers_to_locals0.c" |> Option.map ProgramAnalysis.get_addressed
\<close>
context call_inc_first_impl
begin
thm call_inc_first_body_def
end

end