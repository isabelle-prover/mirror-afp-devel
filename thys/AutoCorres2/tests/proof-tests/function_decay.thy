(*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory function_decay
  imports 
    AutoCorres2_Main.AutoCorres_Main
begin

install_C_file "function_decay.c"

context function_decay_global_addresses
begin
thm select_body_def select1_body_def main_body_def

end



autocorres [single_threaded, scope = select select1] "function_decay.c"

context ts_definition_select
begin
thm ts_def
end
context ts_definition_select1
begin
thm ts_def
end

(* FIXME: autocorres fails here:
autocorres [phase=L1, scope = main] "function_decay.c"
*)

end