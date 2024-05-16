(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory init_static
  imports AutoCorres2.CTranslation
begin

declare [[verbose=4, c_parser_feedback_level=4]]
install_C_file "init_static.c"

context init_static_simpl
begin
thm b_def
thm a_def
thm f'z_def
thm f'y_def
thm f'x_def
thm f_body_def
thm g_body_def
thm c_def
thm arr_def
end
end
