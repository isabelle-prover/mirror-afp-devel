(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory goto
imports  "AutoCorres2_Main.AutoCorres_Main"
begin

declare  [[c_parser_feedback_level=11, ML_print_depth=1000]]

install_C_file "goto.c" 


context goto_simpl
begin
thm no_goto_proc_body_def 
thm no_goto_proc_body_def [simplified creturn_def]
thm goto_proc1_body_def
thm goto_proc_body_def
thm goto_proc_body_def [simplified cgoto_def ccatchgoto_def ccatchreturn_def]
thm while_ret_or_break_or_continue_or_goto_body_def
thm while_ret_or_break_or_continue_or_goto_body_def 
 [simplified cbreak_def creturn_def cgoto_def ccatchbrk_def ccatchgoto_def ccatchreturn_def]
end

declare [[verbose=0, ML_print_depth=1000]]
autocorres [single_threaded] goto.c

context goto_all_corres
begin

thm l2_while_ret_or_break_or_continue'_def
thm l1_no_goto_proc'_def
thm l2_no_goto_proc'_def
thm wa_no_goto_proc'_def
thm no_goto_proc'_def
thm goto_proc1'_def
thm goto_proc'_def
thm while_ret_or_break_or_continue'_def
thm while_ret_or_break_or_continue_or_goto'_def
end

end
