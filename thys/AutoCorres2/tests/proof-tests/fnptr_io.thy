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

autocorres [
  in_out_parameters           = inc(x:"in_out"),
  method_in_out_fun_ptr_specs = object_t.op("in_out")
] "fnptr_io.c"

context ts_definition_f begin

lemma "f' \<equiv> \<P>_option_unsigned_char___unsigned_char__unsigned_char (op_C (objects.[0])) 0"
  by (rule f'_def)

end

end