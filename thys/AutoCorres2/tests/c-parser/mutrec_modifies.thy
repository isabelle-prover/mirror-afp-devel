(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory mutrec_modifies
imports "AutoCorres2.CTranslation"
begin

install_C_file "mutrec_modifies.c"

context mutrec_modifies_simpl
begin

thm f_modifies
thm g_modifies
thm atop_modifies
thm h_modifies
thm fact_modifies

thm rec1_modifies
thm rec2_modifies
thm rec3_modifies
thm rec4_modifies

end

end
