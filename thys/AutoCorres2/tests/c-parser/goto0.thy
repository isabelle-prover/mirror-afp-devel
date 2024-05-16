(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory goto0
imports "AutoCorres2.CTranslation"
begin

declare  [[c_parser_feedback_level=11, ML_print_depth=1000]]

install_C_file "goto0.c" 


context goto0_simpl
begin
thm no_goto_proc_body_def
thm goto_proc1_body_def
thm goto_proc_body_def


end

end
