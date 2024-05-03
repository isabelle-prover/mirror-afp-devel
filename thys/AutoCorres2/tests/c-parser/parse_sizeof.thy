(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory parse_sizeof
imports "AutoCorres2.CTranslation"
begin

install_C_file "parse_sizeof.c"

context parse_sizeof_simpl
begin
thm f_body_def
(* notice how repulsive the above is *)
thm g_body_def
end

end
