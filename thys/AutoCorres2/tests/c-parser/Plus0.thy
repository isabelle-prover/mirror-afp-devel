(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)


theory Plus0
imports
  AutoCorres2.CTranslation
begin
declare [[quick_and_dirty=false,sorry_modifies_proofs=false,show_hyps=false, show_types=false, ML_print_depth=1000]]

declare [[hoare_trace=0]]
install_C_file "plus0.c"


context plus0_simpl
begin
thm main_body_def
thm plus_body_def


end

end
