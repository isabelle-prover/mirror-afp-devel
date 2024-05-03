(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver307
  imports "AutoCorres2.CTranslation"
begin

include_C_file "jira ver307.h" for "jira ver307.c"
install_C_file "jira ver307.c"

context "jira ver307_simpl"
begin

thm f_body_def

end

end
