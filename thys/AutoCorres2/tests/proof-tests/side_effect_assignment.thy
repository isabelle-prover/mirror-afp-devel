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

thm ptr_fun_body_def
thm multi_assign_body_def
thm zero_loop_post_body_def
thm zero_loop_pre_body_def
thm for_pre_body_def
thm while_log_and_body_def
thm do_write1_body_def thm do_write_body_def
thm commas_body_def
context side_effect_assignment_global_addresses
begin
thm arr_upd_body_def main4_body_def main1_body_def main2_body_def main3_body_def
thm loop1_body_def loop2_body_def

end

autocorres [] "side_effect_assignment.c"

thm ts_def

end