(*
 * Copyright (c) 2025 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory side_effect_assignment
  imports 
    AutoCorres2_Main.AutoCorres_Main
begin

install_C_file "side_effect_assignment.c"

context side_effect_assignment_global_addresses
begin
thm arr_upd_body_def main_body_def main1_body_def main2_body_def main3_body_def
thm loop1_body_def loop2_body_def

end

autocorres [] "side_effect_assignment.c"

context side_effect_assignment_all_corres
begin
thm ts_def
end


end