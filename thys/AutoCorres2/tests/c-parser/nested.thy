(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory nested
  imports AutoCorres2.CTranslation
begin

install_C_file "nested.c"

thm heap_update_def
context nested_simpl
begin
thm foo_body_def
end

end
