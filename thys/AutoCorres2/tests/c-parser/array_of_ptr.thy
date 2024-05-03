(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory array_of_ptr
imports "AutoCorres2.CTranslation"
begin

install_C_file "array_of_ptr.c"

print_locale! array_of_ptr_global_addresses
context array_of_ptr_global_addresses
begin
term "a::32 signed word ptr[4]"
thm a_def
end
end
