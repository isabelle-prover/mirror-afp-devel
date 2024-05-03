(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory static
  imports AutoCorres2.CTranslation
begin

install_C_file "static.c"


print_record globals

context static_simpl
begin
thm foo1'n_def
thm foo1_body_def
thm foo2_body_def
thm inc_body_def
thm n_def
thm glob_body_def
thm g'i_def
thm g_body_def
thm f_body_def
end

end
