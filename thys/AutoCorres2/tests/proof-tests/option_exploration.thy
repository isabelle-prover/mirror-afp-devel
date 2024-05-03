(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory option_exploration imports
  "AutoCorres2_Main.AutoCorres_Main"
begin


install_C_file "option_exploration.c"



autocorres [phase=TS,trace_opt,scope=fac, skip_word_abs, skip_heap_abs,
    ts_force nondet = fac, single_threaded] "option_exploration.c"

context ts_definition_fac
begin
thm fac'.simps
end

end