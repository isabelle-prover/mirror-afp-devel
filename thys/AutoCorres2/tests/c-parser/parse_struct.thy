(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory parse_struct
imports "AutoCorres2.CTranslation"
begin

install_C_file "parse_struct.c"

(* mem_type instances proved automatically.  If you remove the additional
   theorems from the simp add: list below, you see that the LHS of the goal
   turns into sizeof TYPE(struct1), demonstrating that the mem_type's axiom
   "len" is applied.  Thus, struct1 is really a mem_type. *)

lemma
  "length bs = size_of TYPE(struct1_C) \<Longrightarrow> length (to_bytes (x::struct1_C) bs) = 12"
  by (simp)



thm typ_tag_defs
thm allinclusive_C_tag_def
thm allinclusive_C_typ_info

context parse_struct_simpl
begin
thm mkall_body_def
end

(* fold congruences proved in creation of these records help us
   by reducing the doubling of syntax on the lhs *)
lemma "s \<lparr> c1_C := c1_C s + 2 \<rparr> = c1_C_update (\<lambda>x. x + 2) s"
  apply (simp cong: charpair_C_fold_congs)
  done

end
