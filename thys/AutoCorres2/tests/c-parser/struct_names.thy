(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory struct_names
imports "AutoCorres2.CTranslation"
begin

install_C_file "struct_names.c"

context struct_names_global_addresses
begin

term "x_C.x_C :: 32 signed word[1] \<Rightarrow> y_C ptr \<Rightarrow> x_C"
term "x_C.y_C :: x_C \<Rightarrow> 32 signed word[1]"
term "y_C.x_C :: y_C \<Rightarrow> 32 signed word[2]"
term "y_C.y_C :: 32 signed word[2] \<Rightarrow> x_C ptr \<Rightarrow> y_C"

end

end