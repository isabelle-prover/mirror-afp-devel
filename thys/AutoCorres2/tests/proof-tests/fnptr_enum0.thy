(*
 * Copyright (c) 2023 Apple Inc. All rights reserved. 
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory fnptr_enum0
imports AutoCorres2_Main.AutoCorres_Main
begin

install_C_file "fnptr_enum0.c"

autocorres [ts_force nondet = worker]"fnptr_enum0.c"

context fnptr_enum0_all_corres
begin
thm ts_def
end

end

