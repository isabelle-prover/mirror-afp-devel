(*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory statement_expression
 (*  imports "AutoCorres2.CTranslation" *)
  imports "AutoCorres2_Main.AutoCorres_Main" 
begin


install_C_file "statement_expression.c"

init-autocorres [(*skip_heap_abs*)] "statement_expression.c"

autocorres "statement_expression.c"
thm final_defs

end
