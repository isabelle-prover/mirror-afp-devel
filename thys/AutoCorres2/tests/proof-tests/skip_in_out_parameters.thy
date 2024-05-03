(*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)
theory skip_in_out_parameters imports "AutoCorres2_Main.AutoCorres_Main" 
begin





install_C_file "skip_in_out_parameters.c"


autocorres "skip_in_out_parameters.c"

context ts_definition_inc
begin
thm ts_def
end

context ts_definition_call_inc_ptr
begin
thm ts_def
end

end