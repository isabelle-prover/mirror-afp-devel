(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory populate_globals
imports "AutoCorres2.CTranslation"
begin


declare [[globals_all_addressed=true,populate_globals=true]]
install_C_file "globsall_addressed.c"

context globsall_addressed_simpl
begin
  thm f_body_def

  term wannabe_constant
  thm wannabe_constant_def

  term "glob1_'::32 signed word ptr"
end

end
