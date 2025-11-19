(*
 * Copyright (c) 2024 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory fnptr_io
  imports 
    AutoCorres2_Main.AutoCorres_Main
begin

install_C_file "fnptr_io.c"

thm f_body_def
ML_val \<open>
Proof_Context.get_thm @{context} "f_body_def"
\<close>
context fnptr_io_global_addresses
begin
thm fun_ptr_simps
thm f_body_def
ML_val \<open>
Proof_Context.get_thm @{context} "f_body_def"
\<close>
end
declare [[c_parser_feedback_level=2]]
autocorres [phase=L1, single_threaded,
  in_out_parameters           = inc(x:"in_out") and call_glob(x:"in_out") (*,
  method_in_out_fun_ptr_specs = object_t.op("in_out")*)
] "fnptr_io.c"

autocorres [phase=WA,
  in_out_parameters           = inc(x:"in_out") and call_glob(x:"in_out") (*,
  method_in_out_fun_ptr_specs = object_t.op("in_out")*)
] "fnptr_io.c"

declare [[single_threaded, c_parser_feedback_level=2]]
autocorres [phase=TS, single_threaded,
  in_out_parameters           = inc(x:"in_out") and call_glob(x:"in_out") (*,
  method_in_out_fun_ptr_specs = object_t.op("in_out")*)
] "fnptr_io.c"


context fnptr_io_global_addresses begin

thm ts_def
thm final_defs

end

end