(*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)


theory In_Out_Parameters_No_HL imports "AutoCorres2_Main.AutoCorres_Main" 
begin

install_C_file "in_out_parameters_no_hl.c"

init-autocorres [skip_heap_abs, 
    in_out_parameters = 
    get_fst(q:in_out),
    in_out_globals = main
   ]"in_out_parameters_no_hl.c"

autocorres  [] "in_out_parameters_no_hl.c"

context ts_definition_main
begin
thm ts_def
end

end