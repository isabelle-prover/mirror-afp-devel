(*
 * Copyright (c) 2023 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Skip_Asm
imports "AutoCorres2.CTranslation"
begin

install_C_file "skip_asm.c" [skip_asm]


thm asm_stmts_body_def \<comment> \<open>no \<^const>\<open>asm_spec\<close> should be in the body\<close>


end
