(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)
theory globals imports "AutoCorres2_Main.AutoCorres_Main" 
begin

install_C_file "globals.c"


autocorres "globals.c"
context globals_all_corres
begin
thm ts_def
thm l2_def
end

end
