(*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory flexible_array_member
  imports 
    AutoCorres2_Main.AutoCorres_Main
begin

install_C_file "flexible_array_member.c"

context flexible_array_member_global_addresses
begin
thm get_body_def

end



autocorres [] "flexible_array_member.c"

context flexible_array_member_all_corres
begin
thm ts_def
end

end