(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Global_Structs
imports "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "global_structs.c"

autocorres [ts_rules = nondet] "global_structs.c"


context global_structs_all_corres begin

thm s1_access_body_def
thm s2_access_body_def

thm s1_access'_def
thm s2_access'_def
end

end
