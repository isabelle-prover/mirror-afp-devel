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

thm get_body_def


autocorres [] "flexible_array_member.c"

thm ts_def

end