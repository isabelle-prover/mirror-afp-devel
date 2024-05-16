(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory buffer
imports "AutoCorres2_Main.AutoCorres_Main"
begin


install_C_file "buffer.c"

context set_2_impl begin
thm set_2_body_def
end

context get_bytes_impl begin
thm get_bytes_body_def
end

autocorres "buffer.c"

context l2_definition_get_head
begin
thm l2_def
end

context hl_definition_get_head
begin
thm hl_def
end

context l2_definition_set_head
begin
thm l2_def
end

context hl_definition_set_head
begin
thm hl_def
end

context l2_definition_set_2
begin
thm l2_def
end

context hl_definition_set_2
begin
thm hl_def
end


context l2_definition_get_2
begin
thm l2_def
end

context hl_definition_get_2
begin
thm hl_def
end


end
