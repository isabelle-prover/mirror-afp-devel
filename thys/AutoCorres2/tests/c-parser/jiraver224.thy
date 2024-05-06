(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver224
imports "AutoCorres2.CTranslation"
begin

include_C_file "includes/accentéd1.h" for "jiraver224.c"
include_C_file "includes/accented大学.h" for "jiraver224.c"
include_C_file "includes/accentedだいがく.h" for "jiraver224.c"
install_C_file "jiraver224.c"

context jiraver224_simpl
begin

thm g_body_def
thm h_body_def

end

end
