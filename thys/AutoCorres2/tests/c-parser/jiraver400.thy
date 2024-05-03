(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver400
  imports "AutoCorres2.CTranslation"
begin

declare [[c_parser_feedback_level=2]]
install_C_file "jiraver400.c" [machinety=bool,roots=[h,indep1]]

context jiraver400_simpl
begin

  thm f_body_def
  thm indep1_body_def

end

end
