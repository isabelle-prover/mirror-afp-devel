(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver434
  imports "AutoCorres2.CTranslation"

begin

install_C_file "jiraver434.c"

typ "seL4_UserContext_C"
context jiraver434_simpl
begin


ML \<open>
val records = RecursiveRecordPackage.get_info @{theory}
fun defined_struct T = Symtab.defined records (fst (dest_Type T))

val _ = @{assert} (defined_struct @{typ seL4_UserContext_C})
val _ = @{assert} (defined_struct @{typ foo_C})
val _ = @{assert} (defined_struct @{typ AnonStruct1'})
\<close>


end (* context *)

end
