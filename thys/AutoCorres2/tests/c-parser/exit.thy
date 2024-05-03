(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory exit
imports "AutoCorres2.CTranslation"
begin

declare  [[c_parser_feedback_level=11, ML_print_depth=1000]]

install_C_file "exit.c" 


context exit_simpl
begin
thm main_body_def
thm odd_body_def


end

end
