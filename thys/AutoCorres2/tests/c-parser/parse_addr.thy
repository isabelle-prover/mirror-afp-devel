(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory parse_addr
imports "AutoCorres2.CTranslation"
begin

install_C_file "parse_addr.c"

context parse_addr_global_addresses
begin
thm c_def
end

context parse_addr_simpl
begin
thm f_body_def
thm f2_body_def
thm g_body_def
thm h_body_def
thm c_def
end

end
