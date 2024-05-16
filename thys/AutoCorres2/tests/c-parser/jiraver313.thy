(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver313
  imports "AutoCorres2.CTranslation"
begin

declare [[calculate_modifies_proofs = false ]]

install_C_file "jiraver313.c" [memsafe]

context jiraver313_global_addresses
begin
term foo
end

context jiraver313_simpl
begin
thm f_body_def
thm g_body_def

end

end
