(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)


theory memcopy
  imports AutoCorres2.CTranslation
begin

declare [[verbose=4, c_parser_feedback_level=4]]
install_C_file "memcopy.c"

context memcopy_simpl
begin
thm memcpy_u8_body_def
thm memcpy_void_body_def
end
end
