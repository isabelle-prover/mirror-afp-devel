(*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory function_pointer_array_decay
  imports 
    AutoCorres2_Main.AutoCorres_Main
begin

install_C_file "function_pointer_array_decay.c"

context function_pointer_array_decay_global_addresses
begin
thm unique_test_body_def

end

autocorres [] "function_pointer_array_decay.c"

context function_pointer_array_decay_all_corres
begin
thm ts_def
end


end