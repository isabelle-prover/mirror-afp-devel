(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory buffer
imports "AutoCorres2_Main.AutoCorres_Main"
begin


install_C_file "buffer.c"

thm set_2_body_def

thm get_bytes_body_def

autocorres "buffer.c"


thm l2_def
thm hl_def

end
