(*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)


theory In_Out_Parameters_Slow imports "AutoCorres2_Main.AutoCorres_Main" 
begin

install_C_file "in_out_parameters_slow.c"

init-autocorres [ in_out_parameters = 
    inc(y:in_out) and
    inc2(y:in_out, z:in_out)
   ]"in_out_parameters_slow.c"

autocorres  [] "in_out_parameters_slow.c"

context in_out_parameters_slow_all_corres
begin
thm io_corres
thm ts_def
end

end