(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver313
  imports "AutoCorres2.CTranslation"
begin

declare [[calculate_modifies_proofs = false, c_parser_feedback_level=2 ]]

install_C_file "jiraver313.c" [memsafe]

term f_body
context jiraver313_global_addresses
begin
term f_body
term foo
end

thm f_body_def
thm g_body_def

end
