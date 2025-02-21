(*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory anonymous_nested_struct
  imports 
    AutoCorres2_Main.AutoCorres_Main
begin

install_C_file "anonymous_nested_struct.c"

context anonymous_nested_struct_global_addresses
begin
thm main_body_def

end

autocorres [] "anonymous_nested_struct.c"

context anonymous_nested_struct_all_corres
begin
thm ts_def
end


end