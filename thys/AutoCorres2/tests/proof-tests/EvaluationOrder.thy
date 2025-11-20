(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory EvaluationOrder
imports "AutoCorres2_Main.AutoCorres_Main"
begin

install_C_file "evaluation_order.c"

autocorres [ts_rules = nondet] "evaluation_order.c"

thm bitwise_or_body_def
thm same_body_def
thm call_same_body_def

thm bitwise_or'_def
thm call_same'_def

end
